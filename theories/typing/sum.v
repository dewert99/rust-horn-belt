From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.bi Require Import fractional.
From lrust.util Require Import types.
From lrust.typing Require Export (** lft_contexts *) type.
Set Default Proof Using "Type".

Section sum.
  Context `{!typeG Σ}.

  (* We define the actual empty type as being the empty sum, so that it is
     convertible to it---and in particular, we can pattern-match on it
     (as in, pattern-match in the language of lambda-rust, not in Coq). *)
  Program Definition emp0 : type Empty_set :=
    {| pt_size := 1;  pt_own _ _ _ := False%I; |}.
  Next Obligation. by iIntros. Qed.
  Global Instance emp0_send: Send emp0. Proof. done. Qed.

  Notation hnthe := (hnth emp0).

  Implicit Type (i: nat) (vl: list val).

  Definition is_pad {As} i (tyl: typel As) vl : iProp Σ :=
    ⌜((hnthe tyl i).(ty_size) + length vl)%nat = max_hlist_with (λ _, ty_size) tyl⌝.

  Lemma split_sum_mt {As} (tyl: typel As) vπ d l tid q :
    (l ↦∗{q}: λ vl, ∃i vπ' vl' vl'', ⌜vπ = xinj i ∘ vπ'⌝ ∗
      ⌜vl = #i :: vl' ++ vl''⌝ ∗ ⌜length vl = S (max_hlist_with (λ _, ty_size) tyl)⌝ ∗
      (hnthe tyl i).(ty_own) (vπ',d) tid vl')%I ⊣⊢
    ∃i vπ', ⌜vπ = xinj i ∘ vπ'⌝ ∗
      (l ↦{q} #i ∗ (l +ₗ S (hnthe tyl i).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
      (l +ₗ 1) ↦∗{q}: (hnthe tyl i).(ty_own) (vπ',d) tid.
  Proof. iSplit.
    - iDestruct 1 as (vl) "[Mt Own]".
      iDestruct "Own" as (i vπ' vl' vl'' ->->[=]) "Own". iExists i, vπ'.
      iSplit; [done|]. iDestruct (ty_size_eq with "Own") as "%Eq'".
      iDestruct (heap_mapsto_vec_cons with "Mt") as "[$ Mt]".
      iDestruct (heap_mapsto_vec_app with "Mt") as "[Mt Mt']".
      iSplitL "Mt'".
      + iExists vl''. rewrite (shift_loc_assoc_nat _ 1) Eq'. iFrame. iPureIntro.
        by rewrite -Eq' -app_length.
      + iExists vl'. by iFrame.
    - iDestruct 1 as (i vπ' ->) "[[Mt Mt'']Own]".
      iDestruct "Own" as (vl') "[Mt' Own]". iDestruct "Mt''" as (vl'') "[Mt'' %]".
      iDestruct (ty_size_eq with "Own") as "%Eq". iExists (#i :: vl' ++ vl'').
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app (shift_loc_assoc_nat _ 1) Eq.
      iFrame "Mt Mt' Mt''". iExists i, vπ', vl', vl''. do 2 (iSplit; [done|]).
      iFrame "Own". iPureIntro. simpl. f_equal. by rewrite app_length Eq.
  Qed.

  Local Lemma ty_lfts_incl {As} (tyl: typel As) i :
    ⊢ tyl_lft tyl ⊑ ty_lft (hnthe tyl i).
  Proof.
    elim: tyl i=> /=[|?? ty tyl IH] [|j];
      [by iApply lft_incl_refl|by iApply lft_incl_refl| |];
      rewrite lft_intersect_list_app; [by iApply lft_intersect_incl_l|].
    iApply lft_incl_trans; by [iApply lft_intersect_incl_r|iApply IH].
  Qed.

  Program Definition sum {As} (tyl: typel As) := {|
    ty_size := S (max_hlist_with (λ _, ty_size) tyl);
    ty_lfts := tyl_lfts tyl;  ty_E := tyl_E tyl;
    ty_own vπd tid vl := (∃i vπ' vl' vl'', ⌜vπd.1 = xinj i ∘ vπ'⌝ ∗
      ⌜vl = #i :: vl' ++ vl''⌝ ∗ ⌜length vl = S (max_hlist_with (λ _, ty_size) tyl)⌝ ∗
      (hnthe tyl i).(ty_own) (vπ',vπd.2) tid vl')%I;
    ty_shr vπd κ tid l := (∃i vπ', ⌜vπd.1 = xinj i ∘ vπ'⌝ ∗
      &frac{κ} (λ q, l ↦{q} #i ∗
        (l +ₗ S (hnthe tyl i).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
      (hnthe tyl i).(ty_shr) (vπ',vπd.2) κ tid (l +ₗ 1))%I
  |}.
  Next Obligation. move=> *. by iDestruct 1 as (???????) "?". Qed.
  Next Obligation.
    move=> */=. iDestruct 1 as (i vπ' vl' vl'' ->->->) "?".
    iExists i, vπ', vl', vl''. do 3 (iSplit; [done|]). by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iDestruct 1 as (i vπ' ->) "[??]". iExists i, vπ'.
    do 2 (iSplit; [done|]). by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "In". iDestruct 1 as (i vπ' ->) "[??]". iExists i, vπ'.
    iSplit; [done|]. iSplit;
      by [iApply (frac_bor_shorten with "In")|iApply (ty_shr_lft_mono with "In")].
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #? Bor Tok". rewrite split_sum_mt.
    iMod (bor_exists with "LFT Bor") as (i) "Bor"; [done|].
    iMod (bor_exists_tok with "LFT Bor Tok") as (vπ') "[Bor Tok]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor Tok") as "[>->[Bor Tok]]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Mt Bor]"; [done|].
    iMod (ty_share with "LFT [] Bor Tok") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_incl]. }
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[Shr $]".
    iMod (bor_fracture (λ q, _ ↦{q} _ ∗ _ ↦∗{q}: _)%I with "LFT Mt") as "?"; [done|].
    iModIntro. iExists i, vπ'. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #?". iDestruct 1 as (i vπ' vl' vl'' ->->->) "Own".
    iIntros "Tok". iMod (ty_own_proph with "LFT [] Own Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply ty_lfts_incl]. } iModIntro.
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q' ?) "[PTok Close]".
    iModIntro. iExists ξs, q'. iSplit. { iPureIntro. by apply proph_dep_constr. }
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[?$]".
    iModIntro. iExists i, vπ', vl', vl''. by do 3 (iSplit; [done|]).
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #In #?". iDestruct 1 as (i vπ' ->) "[Bor Shr]".
    iIntros "Tok". iMod (ty_shr_proph with "LFT In [] Shr Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply ty_lfts_incl]. } iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q' ?) "[PTok Close]".
    iModIntro. iExists ξs, q'. iSplit. { iPureIntro. by apply proph_dep_constr. }
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[?$]".
    iModIntro. iExists i, vπ'. by do 2 (iSplit; [done|]).
  Qed.

  Global Instance sum_ne {As} : NonExpansive (@sum As).
  Proof.
    move=> n tyl tyl' Eqv.
    have EqSize: max_hlist_with (λ _, ty_size) tyl = max_hlist_with (λ _, ty_size) tyl'.
    { elim: Eqv=> /=[|>Eqv ? ->]; [done|]. f_equiv. apply Eqv. }
    split=>/=.
    - by rewrite EqSize.
    - elim: Eqv=> /=[|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - elim: Eqv=> /=[|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - move=> *. rewrite EqSize. do 12 f_equiv. by apply @hnth_ne.
    - move=> *. rewrite /is_pad EqSize.
      repeat ((by apply @hnth_ne) || eapply ty_size_ne || f_equiv).
  Qed.

(*
  Lemma product_lft_morphism Tl:
    Forall TypeLftMorphism Tl →
    TypeLftMorphism (λ ty, sum ((λ T, T ty) <$> Tl)).
  Proof.
    intros HTl.
    assert (let s ty := sum ((λ T, T ty) <$> Tl) in
        (∃ α βs E, (∀ ty, ⊢ ty_lft (s ty) ≡ₗ α ⊓ ty_lft ty) ∧
            (∀ ty, elctx_interp (s ty).(ty_E) ⊣⊢
                   elctx_interp E ∗ elctx_interp ty.(ty_E) ∗
                   [∗ list] β ∈ βs, β ⊑ ty_lft ty)) ∨
        (∃ α E, (∀ ty, ⊢ ty_lft (s ty) ≡ₗ α) ∧
                (∀ ty, elctx_interp (s ty).(ty_E) ⊣⊢ elctx_interp E)))
      as [(?&?&?&?&?)|(?&?&?&?)]; [|by eleft|by eright].
    simpl. induction HTl as [|T Tl HT HTl [(α & βs & E & Hα & HE)|(α & E & Hα & HE)]]=>/=.
    - right. exists static, []. split=>_ //. iApply lft_equiv_refl.
    - setoid_rewrite lft_intersect_list_app.
      destruct HT as [α' βs' E' Hα' HE'|α' E' Hα' HE'].
      + left. exists (α' ⊓ α), (βs' ++ βs), (E' ++ E). split.
        * intros ty. iApply lft_equiv_trans.
          { iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα]. }
          rewrite -!assoc (comm (⊓) (ty_lft ty) (α ⊓ _)) -!assoc.
          repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
          iApply lft_intersect_equiv_idemp.
        * intros ty.
          rewrite /tyl_E /= !elctx_interp_app HE' HE big_sepL_app -!assoc.
          iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
      + left. exists (α' ⊓ α), βs, (E' ++ E). split.
        * intros ty. rewrite -assoc.
          iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
        * intros ty.
          by rewrite /tyl_E /= !elctx_interp_app HE' HE -!assoc.
    - setoid_rewrite lft_intersect_list_app.
      destruct HT as [α' βs' E' Hα' HE'|α' E' Hα' HE'].
      + left. exists (α' ⊓ α), βs', (E' ++ E). split.
        * intros ty. rewrite -!assoc (comm (⊓) α (ty_lft ty)) !assoc.
          iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
        * intros ty. rewrite /tyl_E /= !elctx_interp_app HE' HE -!assoc.
          iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
      + right. exists (α' ⊓ α), (E' ++ E). split.
        * intros. iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
        * intros. by rewrite /tyl_E /= !elctx_interp_app HE HE'.
  Qed.

  Global Instance sum_type_ne Tl:
    TypeListNonExpansive Tl → TypeNonExpansive (sum ∘ Tl).
  Proof.
    intros (Tl' & HTlTl' & HTl').
    eapply type_ne_ext; last first.
    { intros ty. by rewrite /= HTlTl'. }
    clear Tl HTlTl'.
    assert (Hsz0 : ∀ ty1 ty2, ty_size ty1 = ty_size ty2 →
      max_list_with ty_size ((λ T, T ty1) <$> Tl') =
      max_list_with ty_size ((λ T, T ty2) <$> Tl')).
    { intros ty1 ty2 Hsz.
      induction HTl' as [|T Tl' HT HTl' IH]=>//=. rewrite IH. f_equal. by apply HT. }
    split.
    - apply product_lft_morphism. eapply Forall_impl; [done|]. apply _.
    - intros. simpl. f_equiv. auto.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs depth tid vl /=. f_equiv=>i. do 6 f_equiv.
      + do 3 f_equiv. by apply Hsz0.
      + rewrite !nth_lookup !list_lookup_fmap.
        rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
        destruct (Tl' !! i)=>//=. by apply HTl'.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l /=. f_equiv=>i.
      rewrite /is_pad !nth_lookup !list_lookup_fmap.
      rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
      destruct (Tl' !! i); [|by rewrite !right_absorb]. simpl.
      repeat ((by apply HTl') || (by apply Hsz0) || f_equiv).
  Qed.

  (* TODO : get rid of this duplication *)
  Global Instance sum_type_ne_cont Tl:
    TypeListContractive Tl → TypeContractive (sum ∘ Tl).
  Proof.
    intros (Tl' & HTlTl' & HTl').
    eapply type_contractive_ext; last first.
    { intros ty. by rewrite /= HTlTl'. }
    clear Tl HTlTl'.
    assert (Hsz0 : ∀ ty1 ty2,
      max_list_with ty_size ((λ T, T ty1) <$> Tl') =
      max_list_with ty_size ((λ T, T ty2) <$> Tl')).
    { intros ty1 ty2.
      induction HTl' as [|T Tl' HT HTl' IH]=>//=. rewrite IH. f_equal. by apply HT. }
    split.
    - apply product_lft_morphism. eapply Forall_impl; [done|]. apply _.
    - intros. simpl. f_equiv. auto.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs depth tid vl /=. f_equiv=>i. do 6 f_equiv.
      + do 3 f_equiv. by apply Hsz0.
      + rewrite !nth_lookup !list_lookup_fmap.
        rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
        destruct (Tl' !! i)=>//=. by apply HTl'.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l /=. f_equiv=>i.
      rewrite /is_pad !nth_lookup !list_lookup_fmap.
      rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
      destruct (Tl' !! i); [|by rewrite !right_absorb]. simpl.
      repeat ((by apply HTl') || (by apply Hsz0) || f_equiv).
  Qed.

  Global Instance sum_mono E L :
    Proper (Forall2 (subtype E L) ==> subtype E L) sum.
  Proof.
    iIntros (tyl1 tyl2 Htyl qL) "HL".
    iAssert (□ (lft_contexts.elctx_interp E -∗ ⌜max_list_with ty_size tyl1 = max_list_with ty_size tyl2⌝))%I with "[#]" as "#Hleq".
    { iInduction Htyl as [|???? Hsub] "IH".
      { iClear "∗". iIntros "!> _". done. }
      iDestruct (Hsub with "HL") as "#Hsub". iDestruct ("IH" with "HL") as "{IH} #IH".
      iModIntro. iIntros "#HE". iDestruct ("Hsub" with "HE") as "(% & _ & _)".
      iDestruct ("IH" with "HE") as %IH. iPureIntro. simpl. inversion_clear IH. by f_equal. }
    iDestruct (subtype_Forall2_llctx with "HL") as "#Htyl"; first done.
    iClear "HL". iIntros "!> #HE".
    iDestruct ("Hleq" with "HE") as %Hleq. iSpecialize ("Htyl" with "HE"). iClear "Hleq HE".
    iAssert (∀ i, type_incl (nth i tyl1 emp0) (nth i tyl2 emp0))%I with "[#]" as "#Hty".
      { iIntros (i). edestruct (nth_lookup_or_length tyl1 i) as [Hl1|Hl]; last first.
        { rewrite nth_overflow // nth_overflow; first by iApply type_incl_refl.
          by erewrite <-Forall2_length. }
        edestruct @Forall2_lookup_l as (ty2 & Hl2 & _); [done..|].
        iDestruct (big_sepL_lookup with "Htyl") as "Hty".
        { rewrite lookup_zip_with. erewrite Hl1. simpl.
          rewrite Hl2 /=. done. }
        rewrite (nth_lookup_Some tyl2 _ _ ty2) //. }
    apply Forall2_length in Htyl.
    clear -Hleq Htyl. iSplit; [|iSplit; [|iSplit]].
    - simpl. by rewrite Hleq.
    - iClear (Hleq) "Hty".
      iInduction tyl1 as [|ty1 tyl1 IH] "IH" forall (tyl2 Htyl);
           destruct tyl2 as [|ty2 tyl2]=>//=.
      + iApply lft_incl_refl.
      + iDestruct "Htyl" as "[Hty Htyl]".
        rewrite !lft_intersect_list_app.
        iApply lft_intersect_mono; [|by iApply "IH"; auto].
        iDestruct "Hty" as "(_ & $ & _ & _)".
    - iModIntro. iIntros (depth tid vl) "H". iDestruct "H" as (i vl' vl'') "(-> & % & Hown)".
      iExists i, vl', vl''. iSplit; first done.
      iSplit; first by rewrite -Hleq.
      iDestruct ("Hty" $! i) as "(_ & _ & #Htyi & _)". by iApply "Htyi".
    - iModIntro. iIntros (κ tid l) "H". iDestruct "H" as (i) "(Hmt & Hshr)".
      iExists i. iSplitR "Hshr".
      + rewrite /is_pad -Hleq. iDestruct ("Hty" $! i) as "(Hlen & _)".
        iDestruct "Hlen" as %<-. done.
      + iDestruct ("Hty" $! i) as "(_ & _ & _ & #Htyi)". by iApply "Htyi".
  Qed.
  Lemma sum_mono' E L tyl1 tyl2 :
    Forall2 (subtype E L) tyl1 tyl2 → subtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_mono. Qed.
  Global Instance sum_proper E L :
    Proper (Forall2 (eqtype E L) ==> eqtype E L) sum.
  Proof.
    intros tyl1 tyl2 Heq; split; eapply sum_mono; [|rewrite -Forall2_flip];
      (eapply Forall2_impl; [done|by intros ?? []]).
  Qed.
  Lemma sum_proper' E L tyl1 tyl2 :
    Forall2 (eqtype E L) tyl1 tyl2 → eqtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_proper. Qed.

  Lemma nth_empty {A : Type} i (d : A) :
    nth i [] d = d.
  Proof. by destruct i. Qed.
*)

  Global Instance sum_copy {As} (tyl: _ As) : ListCopy tyl → Copy (sum tyl).
  Proof.
    move=> ?. have Copy: ∀i, Copy (hnthe tyl i).
    { move=> *. apply (HForall_hnth (λ A, @Copy _ _ A)); by [apply _|]. }
    split; [apply _|]. move=>/= ????? l ?? SubF. iIntros "#LFT".
    iDestruct 1 as (i vπd ->) "[Bor Shr]". iIntros "Na [Tok Tok']".
    iMod (frac_bor_acc with "LFT Bor Tok") as (q) "[>[Idx Pad] Close]";
    [solve_ndisj|]. iDestruct "Pad" as (vl') "[Pad %]".
    iMod (copy_shr_acc with "LFT Shr Na Tok'") as
      (q' vl) "[Na[Mt[#Own Close']]]"; first done.
    { rewrite <-SubF, <-union_subseteq_r. apply shr_locsE_subseteq. lia. }
    iDestruct (na_own_acc with "Na") as "[$ Close'']".
    { apply difference_mono_l.
      trans (shr_locsE (l +ₗ 1) (max_hlist_with (λ _, ty_size) tyl)).
      { apply shr_locsE_subseteq. lia. } { set_solver+. } }
    move: (Qp_lower_bound q q')=> [q''[?[?[->->]]]].
    iExists q'', (#i :: vl ++ vl').
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_app shift_loc_assoc
      -Nat.add_1_l Nat2Z.inj_add.
    iDestruct "Idx" as "[$ Idx]". iDestruct "Mt" as "[$ Mt]".
    iDestruct (ty_size_eq with "Own") as ">%Eq". rewrite Eq.
    iDestruct "Pad" as "[$ Pad]". iSplitR.
    { iIntros "!>!>". iExists i, vπd, vl, vl'. do 2 (iSplit; [done|]).
      iFrame "Own". rewrite /= app_length Eq. iPureIntro. by f_equal. }
    iIntros "!> Na [Idx'[Mt' Pad']]". iDestruct ("Close''" with "Na") as "Na".
    iMod ("Close'" with "Na [$Mt $Mt']") as "[$$]". iApply "Close".
    iFrame "Idx Idx'". iExists vl'. by iFrame.
  Qed.

  Global Instance sum_send {As} (tyl: _ As) : ListSend tyl → Send (sum tyl).
  Proof. move=> Send ?*/=. do 11 f_equiv. by eapply HForall_hnth in Send. Qed.

  Global Instance sum_sync {As} (tyl: _ As) : ListSync tyl → Sync (sum tyl).
  Proof. move=> Sync ?*/=. do 6 f_equiv. by eapply HForall_hnth in Sync. Qed.

  Definition emp_type: type (xsum ^[]) := sum +[].
  Global Instance emp_type_empty : Empty (type (xsum ^[])) := emp_type.

End sum.

(*
(* Σ is commonly used for the current functor. So it cannot be defined
   as Π for products. We stick to the following form. *)
Notation "Σ[ ty1 ; .. ; tyn ]" :=
  (sum (cons ty1%T (..(cons tyn%T nil)..))) : lrust_type_scope.

Global Hint Resolve sum_mono' sum_proper' : lrust_typing.
*)
