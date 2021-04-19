From iris.proofmode Require Import tactics.
From iris.algebra Require Import vector list.
From lrust.typing Require Export type.
From lrust.typing Require Import own programs cont.
Set Default Proof Using "Type".

Section fn.
  Context `{!typeG Σ} {A : Type} {n : nat}.

  Record fn_params := FP {
    fp_E_explicit : lft → elctx;
    fp_tys : vec type n;
    fp_ty : type
  }.

  Definition fn_params_dist n' fp1 fp2 : Prop :=
    Forall2 (dist n') fp1.(fp_tys) fp2.(fp_tys) ∧ fp1.(fp_ty) ≡{n'}≡ fp2.(fp_ty) ∧
    pointwise_relation lft eq fp1.(fp_E_explicit) fp2.(fp_E_explicit).

  Definition fp_E (fp : fn_params) ϝ :=
    fp.(fp_E_explicit) ϝ ++ tyl_E fp.(fp_tys) ++ tyl_outlives_E fp.(fp_tys) ϝ ++
                       fp.(fp_ty).(ty_E) ++ ty_outlives_E fp.(fp_ty) ϝ.

  Global Instance fp_E_ne n':
    Proper (fn_params_dist n' ==> eq ==> eq) fp_E.
  Proof. unfold fp_E. intros ?? EQ ??->. by destruct EQ as (-> & -> & ->). Qed.

  (* The other alternative for defining the fn type would be to state
     that the value applied to its parameters is a typed body whose type
     is the return type.
     That would be slightly simpler, but, unfortunately, we are no longer
     able to prove that this is contractive. *)
  Program Definition fn (fp : A → fn_params) : type :=
    {| (* FIXME : The definition of ty_lfts is less restrictive than the one
          used in Rust. In Rust, the type of parameters are taken into account
          for well-formedness, and all the liftime constrains relating a
          generalized liftime are ignored. For simplicity, we ignore all of
          them, but this is not very faithful. *)
       st_lfts := []; st_E := [];

       st_own tid vl := tc_opaque (∃ fb kb xb e H,
         ⌜vl = [@RecV fb (kb::xb) e H]⌝ ∗ ⌜length xb = n⌝ ∗
         ▷ ∀ (x : A) (ϝ : lft) (k : val) (xl : vec val (length xb)),
            □ typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
                         [k◁cont([ϝ ⊑ₗ []], λ v : vec _ 1, [(v!!!0%fin:val) ◁ box (fp x).(fp_ty)])]
                         (zip_with (TCtx_hasty ∘ of_val) xl
                                   (box <$> (vec_to_list (fp x).(fp_tys))))
                         (subst_v (fb::kb::xb) (RecV fb (kb::xb) e:::k:::xl) e))%I |}.
  Next Obligation.
    iIntros (fp tid vl) "H". iDestruct "H" as (fb kb xb e ?) "[% _]". by subst.
  Qed.
  Next Obligation.
    unfold tc_opaque. apply _.
  Qed.

  Global Instance fn_send fp : Send (fn fp).
  Proof. iIntros (tid1 tid2 vl). done. Qed.

  Global Instance fn_type_contractive E (Tl : A → type → vec type n) T :
    (∀ x, TypeListNonExpansive (Tl x)) →
    (∀ x, TypeNonExpansive (T x)) →
    TypeContractive (λ ty, fn (λ x, FP (E x) (Tl x ty) (T x ty))).
  Proof.
    intros HTl HT.
    assert (∀ n' ty1 ty2, ty1.(ty_size) = ty2.(ty_size) → (⊢ ty_lft ty1 ≡ₗ ty_lft ty2) →
             elctx_interp ty1.(ty_E) ≡ elctx_interp ty2.(ty_E) →
             (∀ depth tid vl, dist_later n' (ty1.(ty_own) depth tid vl) (ty2.(ty_own) depth tid vl)) →
             (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{n'}≡ ty2.(ty_shr) κ tid l) →
             ∀ vl,
               (fn (λ x, FP (E x) (Tl x ty1) (T x ty1))).(ty_own) 0 xH vl ≡{n'}≡
               (fn (λ x, FP (E x) (Tl x ty2) (T x ty2))).(ty_own) 0 xH vl) as Hown.
    { rewrite /fn /fp_E /typed_body /=.
      intros n' ty1 ty2 Hsz Hl HE Ho Hs vl. do 14 (f_contractive || f_equiv).
      intros x. destruct (HTl x) as (Tl' & EQTl & HTl').
      do 12 (f_contractive || f_equiv); [|do 3 f_equiv].
      + apply equiv_dist.
        rewrite /fp_E /= !elctx_interp_app !EQTl /tyl_E /tyl_outlives_E.
        clear Tl HTl EQTl. (do 2 f_equiv); [|f_equiv; [|f_equiv]].
        * induction HTl' as [|T' Tl' HT' _ IH]=>//=.
          rewrite !elctx_interp_app IH type_lft_morphism_elctx_interp_proper //.
        * induction HTl' as [|T' Tl' HT' _ IH]=>//=.
          rewrite !elctx_interp_app IH !elctx_interp_ty_outlives_E
                  lft_incl_equiv_proper_r //.
          by iApply type_lft_morphism_lft_equiv_proper.
        * apply type_lft_morphism_elctx_interp_proper=>//. apply _.
        * rewrite !elctx_interp_ty_outlives_E.
          apply lft_incl_equiv_proper_r.
          by iApply type_lft_morphism_lft_equiv_proper.
      + rewrite !cctx_interp_singleton /=. do 5 f_equiv.
        rewrite !tctx_interp_singleton /tctx_elt_interp.
        do 6 f_equiv. apply box_type_contractive.
        * by apply HT.
        * by iApply type_lft_morphism_lft_equiv_proper.
        * apply type_lft_morphism_elctx_interp_proper=>//. apply _.
        * intros. by apply dist_dist_later, HT.
        * intros. by apply dist_S, HT.
      + rewrite /tctx_interp !big_sepL_zip_with /=. do 2 f_equiv. intros k v.
        rewrite !EQTl !list_lookup_fmap /tctx_elt_interp.
        destruct (Tl' !! k) as [T'|] eqn:EQT'; [simpl|done].
        eapply Forall_lookup in HTl'; [|done].
        f_equiv; intros [[]|]; f_equiv; intros [|]; try by rewrite ?right_absorb.
        simpl. do 4 f_equiv.
        * do 3 f_equiv. by eapply HTl'.
        * by f_equiv; apply HTl'. }
    split.
    - eapply type_lft_morphism_const=>? //=. apply lft_equiv_refl.
    - done.
    - intros. by apply Hown.
    - intros. simpl. do 4 (f_contractive || f_equiv). by eapply Hown.
  Qed.

  Global Instance fn_ne n' :
    Proper (pointwise_relation A (fn_params_dist n') ==> dist n') fn.
  Proof.
    intros x y Hxy. apply ty_of_st_ne. split=>/=; [done..|].
    intros _ _ vs. unfold typed_body, tctx_interp.
    do 30 (apply Hxy || eapply fp_E_ne || f_equiv || done).
    - rewrite !cctx_interp_singleton /=. do 5 f_equiv.
      rewrite !tctx_interp_singleton /tctx_elt_interp.
      repeat (apply Hxy || f_equiv).
    - rewrite /tctx_interp !big_sepL_zip_with /=. do 4 f_equiv.
      cut (∀ n tid p i, Proper (dist n ==> dist n)
        (λ (l : list type),
            match l !! i with
            | Some ty => tctx_elt_interp tid (p ◁ ty) | None => emp
            end)%I).
      { intros Hprop. apply Hprop, (list_fmap_ne _ _ _), Hxy. }
      clear. intros n tid p i x y. rewrite list_dist_lookup=>/(_ i).
      case _ : (x !! i)=>[tyx|]; case  _ : (y !! i)=>[tyy|];
      inversion_clear 1; [solve_proper|done].
  Qed.
End fn.

Arguments fn_params {_ _} _.

(* We use recursive notation for binders as well, to allow patterns
   like '(a, b) to be used. In practice, only one binder is ever used,
   but using recursive binders is the only way to make Coq accept
   patterns. *)
(* FIXME : because of a bug in Coq, such patterns only work for
   printing. Once on 8.6pl1, this should work.  *)
Notation "'fn(∀' x .. x' ',' E ';' T1 ',' .. ',' TN ')' '→' R" :=
  (fn (λ x, (.. (λ x',
      FP E%EL (Vector.cons T1%T .. (Vector.cons TN%T Vector.nil) ..) R%T)..)))
  (at level 99, R at level 200, x binder, x' binder,
   format "'fn(∀'  x .. x' ','  E ';'  T1 ','  .. ','  TN ')'  '→'  R") : lrust_type_scope.
Notation "'fn(∀' x .. x' ',' E ')' '→' R" :=
  (fn (λ x, (.. (λ x', FP E%EL Vector.nil R%T)..)))
  (at level 99, R at level 200, x binder, x' binder,
   format "'fn(∀'  x .. x' ','  E ')'  '→'  R") : lrust_type_scope.
Notation "'fn(' E ';' T1 ',' .. ',' TN ')' '→' R" :=
  (fn (λ _:(), FP E%EL (Vector.cons T1%T .. (Vector.cons TN%T Vector.nil) ..) R%T))
  (at level 99, R at level 200,
   format "'fn(' E ';'  T1 ','  .. ','  TN ')'  '→'  R") : lrust_type_scope.
Notation "'fn(' E ')' '→' R" :=
  (fn (λ _:(), FP E%EL Vector.nil R%T))
  (at level 99, R at level 200,
   format "'fn(' E ')'  '→'  R") : lrust_type_scope.

Instance elctx_empty : Empty (lft → elctx) := λ ϝ, [].

Section typing.
  Context `{!typeG Σ}.

  Lemma fn_subtype {A n} E0 L0 (fp fp' : A → fn_params n) :
    (∀ x ϝ, let EE := E0 ++ fp_E (fp' x) ϝ in
            elctx_sat EE L0 (fp_E (fp x) ϝ) ∧
            Forall2 (subtype EE L0) (fp' x).(fp_tys) (fp x).(fp_tys) ∧
            subtype EE L0 (fp x).(fp_ty) (fp' x).(fp_ty)) →
    subtype E0 L0 (fn fp) (fn fp').
  Proof.
    intros Hcons. apply subtype_simple_type=>//= qL. iIntros "HL0".
    (* We massage things so that we can throw away HL0 before going under the box. *)
    iAssert (∀ x ϝ, let EE := E0 ++ fp_E (fp' x) ϝ in □ (elctx_interp EE -∗
                 elctx_interp (fp_E (fp x) ϝ) ∗
                 ([∗ list] tys ∈ (zip (fp' x).(fp_tys) (fp x).(fp_tys)), type_incl (tys.1) (tys.2)) ∗
                 type_incl (fp x).(fp_ty) (fp' x).(fp_ty)))%I as "#Hcons".
    { iIntros (x ϝ). destruct (Hcons x ϝ) as (HE &Htys &Hty). clear Hcons.
      iDestruct (HE with "HL0") as "#HE".
      iDestruct (subtype_Forall2_llctx with "HL0") as "#Htys"; first done.
      iDestruct (Hty with "HL0") as "#Hty".
      iClear "∗". iIntros "!> #HEE".
      iSplit; last iSplit.
      - by iApply "HE".
      - by iApply "Htys".
      - by iApply "Hty". }
    iClear (Hcons) "∗". iIntros "!> #HE0". iSplit.
    - iApply lft_incl_refl.
    - iIntros (_ vl) "Hf". iDestruct "Hf" as (fb kb xb e ?) "[-> [<- #Hf]]".
      iExists fb, kb, xb, e, _. iSplit; [done|]. iSplit; [done|]. iNext.
      rewrite /typed_body. iIntros (x ϝ k xl) "!> * #LFT #TIME #HE' Htl HL HC HT".
      iDestruct ("Hcons" with "[$]") as "#(HE & Htys & Hty)".
      iApply ("Hf" with "LFT TIME HE Htl HL [HC] [HT]").
      + unfold cctx_interp. iIntros (elt) "Helt".
        iDestruct "Helt" as %->%elem_of_list_singleton. iIntros (ret) "Htl HL HT".
        unfold cctx_elt_interp.
        iApply ("HC" $! (_ ◁cont(_, _)) with "[%] Htl HL [> -]").
        { by apply elem_of_list_singleton. }
        rewrite /tctx_interp !big_sepL_singleton /=.
        iDestruct "HT" as (v depth) "(Hdepth & HP & Hown)".
        iExists v, depth. iFrame "HP Hdepth".
        iDestruct (box_type_incl with "[$Hty]") as "(_ & _ & #Hincl & _)".
          by iApply "Hincl".
      + iClear "Hf". rewrite /tctx_interp
           -{2}(fst_zip (fp x).(fp_tys) (fp' x).(fp_tys)) ?vec_to_list_length //
           -{2}(snd_zip (fp x).(fp_tys) (fp' x).(fp_tys)) ?vec_to_list_length //
           !zip_with_fmap_r !(zip_with_zip (λ _ _, (_ ∘ _) _ _)) !big_sepL_fmap.
        iApply (big_sepL_impl with "HT"). iIntros "!>".
        iIntros (i [p [ty1' ty2']]) "#Hzip H /=".
        iDestruct "H" as (v depth) "(? & Hdepth & Hown)". iExists v, depth. iFrame.
        rewrite !lookup_zip_with.
        iDestruct "Hzip" as %(? & ? & ([? ?] & (? & Hty'1 &
          (? & Hty'2 & [=->->])%bind_Some)%bind_Some & [=->->->])%bind_Some)%bind_Some.
        iDestruct (big_sepL_lookup with "Htys") as "#Hty'".
        { rewrite lookup_zip_with /=. erewrite Hty'2. simpl. by erewrite Hty'1. }
        iDestruct (box_type_incl with "[$Hty']") as "(_ & _ & #Hincl & _)".
        by iApply "Hincl".
  Qed.

  (* We cannot show a Proper instance because it is necessary to prove
     [elctx_sat] afer the coercion.
     See: https://github.com/rust-lang/rust/issues/25860. *)

  Lemma fn_subtype_specialize {A B n} (σ : A → B) E0 L0 fp :
    subtype E0 L0 (fn (n:=n) fp) (fn (fp ∘ σ)).
  Proof.
    apply subtype_simple_type. iIntros (qL) "/= _ !> _". iSplit.
    - iApply lft_incl_refl.
    - iIntros (_ vl) "Hf". iDestruct "Hf" as (fb kb xb e ?) "[-> [<- #Hf]]".
      iExists fb, kb, xb, e, _. iSplit; [done|]. iSplit; [done|].
      rewrite /typed_body. iNext. iIntros "*". iApply "Hf".
  Qed.

  (* In principle, proving this hard-coded to an empty L would be sufficient --
     but then we would have to require elctx_sat as an Iris assumption. *)
  Lemma type_call_iris' E L (κs : list lft) {A} x (ps : list path) qκs qL tid
        p (k : expr) (fp : A → fn_params (length ps)) :
    (∀ ϝ, elctx_sat (((λ κ, ϝ ⊑ₑ κ) <$> κs) ++ E) L (fp_E (fp x) ϝ)) →
    AsVal k →
    lft_ctx -∗ time_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗ llctx_interp L qL -∗
    qκs.[lft_intersect_list κs] -∗
    tctx_elt_interp tid (p ◁ fn fp) -∗
    ([∗ list] y ∈ zip_with TCtx_hasty ps (box <$> vec_to_list (fp x).(fp_tys)),
                   tctx_elt_interp tid y) -∗
    (∀ ret depth,
        na_own tid ⊤ -∗ llctx_interp L qL -∗ qκs.[lft_intersect_list κs] -∗
        ⧖depth -∗ (box (fp x).(fp_ty)).(ty_own) depth tid [ret] -∗
        WP k [of_val ret] {{ _, cont_postcondition }}) -∗
    WP (call: p ps → k) {{ _, cont_postcondition }}.
  Proof.
    iIntros (HE [k' <-]) "#LFT #TIME #HE Htl HL Hκs Hf Hargs Hk".
    wp_apply (wp_hasty with "Hf"). iIntros (depth v) "Hdepth % Hf".
    iApply (wp_app_vec _ _ (_::_) ((λ v, ⌜v = (λ: ["_r"], (#☠ ;; #☠) ;; k' ["_r"])%V⌝):::
               vmap (λ ty (v : val), tctx_elt_interp tid (v ◁ box ty)) (fp x).(fp_tys))%I
            with "[Hargs]").
    - rewrite /=. iSplitR "Hargs".
      { simpl. iApply wp_value. by unlock. }
      remember (fp_tys (fp x)) as tys. clear dependent k' p HE fp x.
      iInduction ps as [|p ps] "IH" forall (tys); first by simpl.
      simpl in tys. inv_vec tys=>ty tys. simpl.
      iDestruct "Hargs" as "[HT Hargs]". iSplitL "HT".
      + iApply (wp_hasty with "HT"). iIntros (??) "???".
        rewrite tctx_hasty_val. auto.
      + iApply "IH". done.
    - simpl. change (@length expr ps) with (length ps).
      iIntros (vl'). inv_vec vl'=>kv vl; csimpl.
      iIntros "[-> Hvl]". iDestruct "Hf" as (fb kb xb e ?) "[EQ [EQl #Hf]]".
      iDestruct "EQ" as %[=->]. iDestruct "EQl" as %EQl.
      revert vl fp HE. rewrite /= -EQl=>vl fp HE. wp_rec.
      iMod (lft_create with "LFT") as (ϝ) "[Htk #Hinh]"; first done.
      iSpecialize ("Hf" $! x ϝ _ vl). iDestruct (HE ϝ with "HL") as "#HE'".
      iMod (bor_create _ ϝ with "LFT Hκs") as "[Hκs HκsI]"; first done.
      iDestruct (frac_bor_lft_incl with "LFT [>Hκs]") as "#Hκs".
      { iApply (bor_fracture with "LFT"); first done. by rewrite Qp_mul_1_r. }
      iApply ("Hf" with "LFT TIME [] Htl [Htk] [Hk HκsI HL]").
      + iApply "HE'". iIntros "{$# Hf Hinh HE' LFT TIME HE %}".
        iInduction κs as [|κ κs] "IH"=> //=. iSplitL.
        { iApply lft_incl_trans; first done. iApply lft_intersect_incl_l. }
        iApply "IH". iModIntro. iApply lft_incl_trans; first done.
        iApply lft_intersect_incl_r.
      + iSplitL; last done. iExists ϝ. iSplit; first by rewrite /= left_id.
        iFrame "#∗".
      + iIntros (y) "IN". iDestruct "IN" as %->%elem_of_list_singleton.
        iIntros (args) "Htl [Hϝ _] [Hret _]". inv_vec args=>r.
        iDestruct "Hϝ" as  (κ') "(EQ & Htk & _)". iDestruct "EQ" as %EQ.
        rewrite /= left_id in EQ. subst κ'. simpl. wp_rec. wp_bind Endlft.
        iSpecialize ("Hinh" with "Htk"). iClear "Hκs".
        iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); first done.
        iApply (wp_step_fupd with "Hinh"); [set_solver-..|]. wp_seq.
        iIntros "#Htok !>". wp_seq. iMod ("HκsI" with "Htok") as ">Hκs".
        rewrite tctx_hasty_val. iDestruct "Hret" as (?) "[#? Hret]".
        by iApply ("Hk" with "Htl HL Hκs").
      + rewrite /tctx_interp vec_to_list_map !zip_with_fmap_r
                (zip_with_zip (λ v ty, (v, _))) zip_with_zip !big_sepL_fmap.
        iApply (big_sepL_mono' with "Hvl"); last done. by iIntros (i [v ty']).
  Qed.

  Lemma type_call_iris E (κs : list lft) {A} x (ps : list path) qκs tid
        f (k : expr) (fp : A → fn_params (length ps)) :
    (∀ ϝ, elctx_sat (((λ κ, ϝ ⊑ₑ κ) <$> κs) ++ E) [] (fp_E (fp x) ϝ)) →
    AsVal k →
    lft_ctx -∗ time_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
    qκs.[lft_intersect_list κs] -∗
    (fn fp).(ty_own) 0 tid [f] -∗
    ([∗ list] y ∈ zip_with TCtx_hasty ps (box <$> vec_to_list (fp x).(fp_tys)),
                   tctx_elt_interp tid y) -∗
    (∀ ret depth, na_own tid ⊤ -∗ qκs.[lft_intersect_list κs] -∗
             ⧖depth -∗ (box (fp x).(fp_ty)).(ty_own) depth tid [ret] -∗
             WP k [of_val ret] {{ _, cont_postcondition }}) -∗
    WP (call: f ps → k) {{ _, cont_postcondition }}.
  Proof.
    iIntros (HE Hk') "#LFT #TIME #HE Htl Hκs Hf Hargs Hk".
    iMod persistent_time_receipt_0 as "#?".
    iApply (type_call_iris' with "LFT TIME HE Htl [] Hκs [Hf] Hargs [Hk]"); [done|..].
    - instantiate (1 := 1%Qp). by rewrite /llctx_interp.
    - rewrite tctx_hasty_val. auto.
    - iIntros "* Htl _". iApply "Hk". done.
  Qed.

  Lemma type_call' E L (κs : list lft) T p (ps : list path)
                   {A} (fp : A → fn_params (length ps)) (k : val) x :
    Forall (lctx_lft_alive E L) κs →
    (∀ ϝ, elctx_sat (((λ κ, ϝ ⊑ₑ κ) <$> κs) ++ E) L (fp_E (fp x) ϝ)) →
    ⊢ typed_body E L [k ◁cont(L, λ v : vec _ 1, ((v!!!0%fin:val) ◁ box (fp x).(fp_ty)) :: T)]
               ((p ◁ fn fp) ::
                zip_with TCtx_hasty ps (box <$> vec_to_list (fp x).(fp_tys)) ++
                T)
               (call: p ps → k).
  Proof.
    iIntros (Hκs HE tid) "#LFT #TIME #HE Htl HL HC (Hf & Hargs & HT)".
    iMod (lctx_lft_alive_tok_list _ _ κs with "HE HL") as (q) "(Hκs & HL & Hclose)"; [done..|].
    iApply (type_call_iris' with "LFT TIME HE Htl HL Hκs Hf Hargs"); [done|].
    iIntros (r depth) "Htl HL Hκs Hdepth Hret". iMod ("Hclose" with "Hκs HL") as "HL".
    iSpecialize ("HC" with "[]"); first by (iPureIntro; apply elem_of_list_singleton).
    iApply ("HC" $! [#r] with "Htl HL").
    rewrite tctx_interp_cons tctx_hasty_val. auto with iFrame.
  Qed.

  (* Specialized type_call':  Adapted for use by solve_typing; fixed "list of
     alive lifetimes" to be the local ones. *)
  Lemma type_call {A} x E L C T T' T'' p (ps : list path)
                        (fp : A → fn_params (length ps)) k :
    p ◁ fn fp ∈ T →
    Forall (lctx_lft_alive E L) (L.*1) →
    (∀ ϝ, elctx_sat (((λ κ, ϝ ⊑ₑ κ) <$> (L.*1)) ++ E) L (fp_E (fp x) ϝ)) →
    tctx_extract E L (zip_with TCtx_hasty ps
                                   (box <$> vec_to_list (fp x).(fp_tys))) T T' →
    k ◁cont(L, T'') ∈ C →
    (∀ ret : val, tctx_incl E L ((ret ◁ box (fp x).(fp_ty))::T') (T'' [# ret])) →
    ⊢ typed_body E L C T (call: p ps → k).
  Proof.
    intros Hfn HL HE HTT' HC HT'T''.
    rewrite -typed_body_mono /flip; last done; first by eapply type_call'.
    - etrans. eapply (incl_cctx_incl _ [_]); first by intros ? ->%elem_of_list_singleton.
      apply cctx_incl_cons; first done. intros args. by inv_vec args.
    - etrans; last by apply (tctx_incl_frame_l [_]).
      apply copy_elem_of_tctx_incl; last done. apply _.
  Qed.

  Lemma type_letcall {A} x E L C T T' p (ps : list path)
                        (fp : A → fn_params (length ps)) b e :
    Closed (b :b: []) e → Closed [] p → Forall (Closed []) ps →
    p ◁ fn fp ∈ T →
    Forall (lctx_lft_alive E L) (L.*1) →
    (∀ ϝ, elctx_sat (((λ κ, ϝ ⊑ₑ κ) <$> (L.*1)) ++ E) L (fp_E (fp x) ϝ)) →
    tctx_extract E L (zip_with TCtx_hasty ps
                                   (box <$> vec_to_list (fp x).(fp_tys))) T T' →
    (∀ ret : val, typed_body E L C ((ret ◁ box (fp x).(fp_ty))::T') (subst' b ret e)) -∗
    typed_body E L C T (letcall: b := p ps in e).
  Proof.
    iIntros (?? Hpsc ????) "He".
    iApply (type_cont_norec [_] _ (λ r, ((r!!!0%fin:val) ◁ box (fp x).(fp_ty)) :: T')).
    - (* TODO : make [solve_closed] work here. *)
      eapply is_closed_weaken; first done. set_solver+.
    - (* TODO : make [solve_closed] work here. *)
      rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl=>//.
        intros. eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - iIntros (k).
      (* TODO : make [simpl_subst] work here. *)
      change (subst' "_k" k (p ((λ: ["_r"], (#☠ ;; #☠) ;; "_k" ["_r"])%E :: ps))) with
             ((subst "_k" k p) ((λ: ["_r"], (#☠ ;; #☠) ;; k ["_r"])%E :: map (subst "_k" k) ps)).
      rewrite is_closed_nil_subst //.
      assert (map (subst "_k" k) ps = ps) as ->.
      { clear -Hpsc. induction Hpsc=>//=. rewrite is_closed_nil_subst //. congruence. }
      iApply type_call; try done. constructor. done.
    - simpl. iIntros (k ret). inv_vec ret=>ret. rewrite /subst_v /=.
      rewrite ->(is_closed_subst []); last set_solver+; last first.
      { apply subst'_is_closed; last done. apply is_closed_of_val. }
      (iApply typed_body_mono; last by iApply "He"); [|done..].
      apply incl_cctx_incl. set_solver+.
  Qed.

  Lemma type_rec {A} E L fb (argsb : list binder) ef e n
        (fp : A → fn_params n) T `{!CopyC T, !SendC T, !Closed _ e} :
    IntoVal ef (funrec: fb argsb := e) →
    n = length argsb →
    □ (∀ x ϝ (f : val) k (args : vec val (length argsb)),
          typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
                     [k ◁cont([ϝ ⊑ₗ []], λ v : vec _ 1, [(v!!!0%fin:val) ◁ box (fp x).(fp_ty)])]
                     ((f ◁ fn fp) ::
                        zip_with (TCtx_hasty ∘ of_val) args
                                 (box <$> vec_to_list (fp x).(fp_tys)) ++ T)
                     (subst_v (fb :: BNamed "return" :: argsb) (f ::: k ::: args) e)) -∗
    typed_instr_ty E L T ef (fn fp).
  Proof.
    iIntros (<- ->) "#Hbody /=". iIntros (tid) "#LFT #TIME _ $ $ #HT".
    iMod persistent_time_receipt_0 as "#?". iApply wp_value.
    rewrite tctx_interp_singleton. iLöb as "IH". iExists _, 0%nat.
    iSplit; [done|]. iSplit; [by rewrite /= decide_left|].
    iExists fb, _, argsb, e, _. iSplit. done. iSplit. done. iNext.
    iIntros (x ϝ k args) "!>". iIntros (tid') "_ _ HE Htl HL HC HT'".
    iApply ("Hbody" with "LFT TIME HE Htl HL HC").
    rewrite tctx_interp_cons tctx_interp_app. iFrame "HT' IH".
    by iApply sendc_change_tid.
  Qed.

  Lemma type_fn {A} E L (argsb : list binder) ef e n
        (fp : A → fn_params n) T `{!CopyC T, !SendC T, !Closed _ e} :
    IntoVal ef (funrec: <> argsb := e) →
    n = length argsb →
    □ (∀ x ϝ k (args : vec val (length argsb)),
        typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
                   [k ◁cont([ϝ ⊑ₗ []], λ v : vec _ 1, [(v!!!0%fin:val) ◁ box (fp x).(fp_ty)])]
                   (zip_with (TCtx_hasty ∘ of_val) args
                             (box <$> vec_to_list (fp x).(fp_tys)) ++ T)
                   (subst_v (BNamed "return" :: argsb) (k ::: args) e)) -∗
    typed_instr_ty E L T ef (fn fp).
  Proof.
    iIntros (??) "#He". iApply type_rec; try done. iIntros "!> *".
    iApply typed_body_mono; last iApply "He"; try done.
    eapply contains_tctx_incl. by constructor.
  Qed.
End typing.

Global Hint Resolve fn_subtype : lrust_typing.
