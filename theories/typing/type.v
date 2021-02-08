From iris.algebra Require Import numbers list lib.excl_auth.
From iris.base_logic.lib Require Export na_invariants.
From lrust.lang Require Export proofmode notation.
From lrust.lifetime Require Export frac_borrow.
From lrust.typing Require Export base.
From lrust.typing Require Import lft_contexts.
Set Default Proof Using "Type".

Class typeG Σ := TypeG {
  type_heapG :> lrustG Σ;
  type_lftG :> lftG Σ;
  type_na_invG :> na_invG Σ;
  type_frac_borrowG :> frac_borG Σ;
  type_excl_auth_inG :> inG Σ (excl_authR natO)
}.

Definition lftE : coPset := ↑lftN.
Definition lrustN := nroot .@ "lrust".
Definition shrN  := lrustN .@ "shr".

Definition thread_id := na_inv_pool_name.

Record type `{!typeG Σ} :=
  { ty_size : nat;
    ty_lfts : list lft;
    ty_E : elctx;
    ty_own : nat → thread_id → list val → iProp Σ;
    ty_shr : lft → thread_id → loc → iProp Σ;

    ty_shr_persistent κ tid l : Persistent (ty_shr κ tid l);

    ty_size_eq depth tid vl : ty_own depth tid vl -∗ ⌜length vl = ty_size⌝;
    ty_own_depth_mono depth1 depth2 tid vl :
      (depth1 ≤ depth2)%nat → ty_own depth1 tid vl -∗ ty_own depth2 tid vl;
    (* The mask for starting the sharing does /not/ include the
       namespace N, for allowing more flexibility for the user of
       this type (typically for the [own] type). AFAIK, there is no
       fundamental reason for this.
       This should not be harmful, since sharing typically creates
       invariants, which does not need the mask.  Moreover, it is
       more consistent with thread-local tokens, which we do not
       give any.

       The lifetime token is needed (a) to make the definition of simple types
       nicer (they would otherwise require a "∨ □|=>[†κ]"), and (b) so that
       we can have emp == sum [].
     *)
    ty_share E depth κ l tid q : lftE ⊆ E →
      lft_ctx -∗ κ ⊑ lft_intersect_list ty_lfts -∗
      &{κ} (l ↦∗: ty_own depth tid) -∗ q.[κ]
       ={E}=∗ |={E}▷=>^depth |={E}=> ty_shr κ tid l ∗ q.[κ];
    ty_shr_mono κ κ' tid l :
      κ' ⊑ κ -∗ ty_shr κ tid l -∗ ty_shr κ' tid l
  }.
Existing Instance ty_shr_persistent.
Instance: Params (@ty_size) 2 := {}.
Instance: Params (@ty_lfts) 2 := {}.
Instance: Params (@ty_E) 2 := {}.
Instance: Params (@ty_own) 2 := {}.
Instance: Params (@ty_shr) 2 := {}.

Arguments ty_own {_ _} !_ _ _ _ / : simpl nomatch.

Notation ty_lft ty := (lft_intersect_list ty.(ty_lfts)).

Lemma ty_own_mt_depth_mono `{!typeG Σ} ty depth1 depth2 tid l :
  (depth1 ≤ depth2)%nat →
  l ↦∗: ty.(ty_own) depth1 tid -∗ l ↦∗: ty.(ty_own) depth2 tid.
Proof.
  iIntros (?) "H". iDestruct "H" as (vl) "[??]".
  iExists vl. iFrame. by iApply ty_own_depth_mono.
Qed.

Definition ty_outlives_E `{!typeG Σ} ty (κ : lft) : elctx :=
  (λ α, κ ⊑ₑ α) <$> ty.(ty_lfts).

Lemma ty_outlives_E_elctx_sat `{!typeG Σ} E L ty α β :
  ty_outlives_E ty β ⊆+ E →
  lctx_lft_incl E L α β →
  elctx_sat E L (ty_outlives_E ty α).
Proof.
  unfold ty_outlives_E. induction ty.(ty_lfts) as [|κ l IH]=>/= Hsub Hαβ.
  - solve_typing.
  - apply elctx_sat_lft_incl.
    + etrans; first done. eapply lctx_lft_incl_external, elem_of_submseteq, Hsub.
      set_solver.
    + apply IH, Hαβ. etrans; last done. by apply submseteq_cons.
Qed.

Lemma elctx_interp_ty_outlives_E `{!typeG Σ} ty α :
  elctx_interp (ty_outlives_E ty α) ⊣⊢ α ⊑ ty.(ty_lft).
Proof.
  rewrite /ty_outlives_E /elctx_interp /elctx_elt_interp big_sepL_fmap /=.
  induction ty.(ty_lfts) as [|κ l IH].
  - iSplit; [|by auto]. iIntros "_". iApply lft_incl_static.
  - rewrite /= IH. iSplit.
    + iDestruct 1 as "#[??]". by iApply lft_incl_glb.
    + iIntros "#?". iSplit; (iApply lft_incl_trans; [done|]);
         [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
Qed.

Definition tyl_lfts `{!typeG Σ} tyl : list lft := concat (ty_lfts <$> tyl).
Definition tyl_E `{!typeG Σ} tyl : elctx := concat (ty_E <$> tyl).
Definition tyl_outlives_E `{!typeG Σ} tyl (κ : lft) : elctx :=
  concat ((λ ty, ty_outlives_E ty κ) <$> tyl).

Lemma tyl_outlives_E_elctx_sat `{!typeG Σ} E L tyl α β :
  tyl_outlives_E tyl β ⊆+ E →
  lctx_lft_incl E L α β →
  elctx_sat E L (tyl_outlives_E tyl α).
Proof.
  induction tyl as [|?? IH]=>/=.
  - solve_typing.
  - intros. apply elctx_sat_app.
    + eapply ty_outlives_E_elctx_sat; [|done].
      etrans; [|done]. by apply submseteq_inserts_r.
    + apply IH; [|done]. etrans; [|done]. by apply submseteq_inserts_l.
Qed.

Record simple_type `{!typeG Σ} :=
  { st_lfts : list lft;
    st_E : elctx;
    st_own : thread_id → list val → iProp Σ;
    st_size_eq tid vl : st_own tid vl -∗ ⌜length vl = 1%nat⌝;
    st_own_persistent tid vl : Persistent (st_own tid vl) }.
Existing Instance st_own_persistent.
Instance: Params (@st_lfts) 2 := {}.
Instance: Params (@st_E) 2 := {}.
Instance: Params (@st_own) 2 := {}.

Program Definition ty_of_st `{!typeG Σ} (st : simple_type) : type :=
  {| ty_size := 1;
     ty_lfts := st.(st_lfts); ty_E := st.(st_E);
     ty_own _ := st.(st_own);
     (* [st.(st_own) tid vl] needs to be outside of the fractured
         borrow, otherwise I do not know how to prove the shr part of
         [subtype_shr_mono]. *)
     ty_shr κ tid l :=
       (∃ vl, &frac{κ} (λ q, l ↦∗{q} vl) ∗ ▷ st.(st_own) tid vl)%I
  |}.
Next Obligation. intros. apply st_size_eq. Qed.
Next Obligation. auto. Qed.
Next Obligation.
  iIntros (?? st E depth κ l tid ??) "#LFT _ Hmt Hκ !>".
  iApply step_fupdN_intro=>//. iIntros "!>".
  iMod (bor_exists with "LFT Hmt") as (vl) "Hmt"; first solve_ndisj.
  iMod (bor_sep with "LFT Hmt") as "[Hmt Hown]"; first solve_ndisj.
  iMod (bor_persistent with "LFT Hown Hκ") as "[Hown $]"; first solve_ndisj.
  iMod (bor_fracture with "LFT [Hmt]") as "Hfrac"; by eauto with iFrame.
Qed.
Next Obligation.
  iIntros (?? st κ κ' tid l)  "#Hord H".
  iDestruct "H" as (vl) "[#Hf #Hown]".
  iExists vl. iFrame "Hown". by iApply (frac_bor_shorten with "Hord").
Qed.

Coercion ty_of_st : simple_type >-> type.

Declare Scope lrust_type_scope.
Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(* OFE and COFE structures on types and simple types. *)
Section ofe.
  Context `{!typeG Σ}.

  Inductive type_equiv' (ty1 ty2 : type) : Prop :=
    Type_equiv :
      ty1.(ty_size) = ty2.(ty_size) →
      ty1.(ty_lfts) = ty2.(ty_lfts) →
      ty1.(ty_E) = ty2.(ty_E) →
      (∀ depth tid vs, ty1.(ty_own) depth tid vs ≡ ty2.(ty_own) depth tid vs) →
      (∀ κ tid l, ty1.(ty_shr) κ tid l ≡ ty2.(ty_shr) κ tid l) →
      type_equiv' ty1 ty2.
  Instance type_equiv : Equiv type := type_equiv'.
  Inductive type_dist' (n : nat) (ty1 ty2 : type) : Prop :=
    Type_dist :
      ty1.(ty_size) = ty2.(ty_size) →
      ty1.(ty_lfts) = ty2.(ty_lfts) →
      ty1.(ty_E) = ty2.(ty_E) →
      (∀ depth tid vs, ty1.(ty_own) depth tid vs ≡{n}≡ ty2.(ty_own) depth tid vs) →
      (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{n}≡ ty2.(ty_shr) κ tid l) →
      type_dist' n ty1 ty2.
  Instance type_dist : Dist type := type_dist'.

  Let T := prodO (prodO (prodO (prodO
    natO (listO lftO)) (listO (prodO lftO lftO)))
    (nat -d> thread_id -d> list val -d> iPropO Σ))
    (lft -d> thread_id -d> loc -d> iPropO Σ).
  Let P (x : T) : Prop :=
    (∀ κ tid l, Persistent (x.2 κ tid l)) ∧
    (∀ depth tid vl, x.1.2 depth tid vl -∗ ⌜length vl = x.1.1.1.1⌝) ∧
    (∀ depth1 depth2 tid vl,
        (depth1 ≤ depth2)%nat → x.1.2 depth1 tid vl -∗ x.1.2 depth2 tid vl) ∧
    (∀ E depth κ l tid q, lftE ⊆ E →
      lft_ctx -∗ κ ⊑ lft_intersect_list x.1.1.1.2 -∗
      &{κ} (l ↦∗: λ vs, x.1.2 depth tid vs) -∗
      q.[κ] ={E}=∗ |={E}▷=>^depth |={E}=> x.2 κ tid l ∗ q.[κ]) ∧
    (∀ κ κ' tid l, κ' ⊑ κ -∗ x.2 κ tid l -∗ x.2 κ' tid l).

  Definition type_unpack (ty : type) : T :=
    (ty.(ty_size), ty.(ty_lfts), ty.(ty_E), ty.(ty_own), ty.(ty_shr)).

  Definition type_ofe_mixin : OfeMixin type.
  Proof.
    apply (iso_ofe_mixin type_unpack); unfold type_unpack; split.
    - by destruct 1 as [-> -> -> ??].
    - intros [[[[??] ?] ?] ?]. by constructor; try apply leibniz_equiv.
    - by destruct 1 as [-> -> -> ??].
    - intros [[[[??] ?] ?] ?]. by constructor=>//;
      eapply leibniz_equiv,  (discrete_iff _ _).
  Qed.
  Canonical Structure typeO : ofeT := OfeT type type_ofe_mixin.

  Global Instance ty_size_ne n : Proper (dist n ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_size_proper : Proper ((≡) ==> eq) ty_size.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_lfts_ne n : Proper (dist n ==> eq) ty_lfts.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_lfts_proper : Proper ((≡) ==> eq) ty_lfts.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_E_ne n : Proper (dist n ==> eq) ty_E.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_E_proper : Proper ((≡) ==> eq) ty_E.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance ty_outlives_E_ne n : Proper (dist n ==> eq ==> eq) ty_outlives_E.
  Proof. intros ?? [_ EQ _ _ _]. by rewrite /ty_outlives_E EQ. Qed.
  Global Instance ty_outlives_E_proper : Proper ((≡) ==> eq ==> eq) ty_outlives_E.
  Proof. intros ?? [_ EQ _ _ _]. by rewrite /ty_outlives_E EQ. Qed.
  Global Instance tyl_E_ne n : Proper (dist n ==> eq) tyl_E.
  Proof.
    intros ?? EQ. unfold tyl_E.
    induction EQ as [|???? EQ _ IH]=>//=. by rewrite EQ IH.
  Qed.
  Global Instance tyl_E_proper : Proper ((≡) ==> eq) tyl_E.
  Proof.
    intros ?? EQ. unfold tyl_E.
    induction EQ as [|???? EQ _ IH]=>//=. by rewrite EQ IH.
  Qed.
  Global Instance tyl_outlives_E_ne n : Proper (dist n ==> eq ==> eq) tyl_outlives_E.
  Proof.
    intros ?? EQ ?? ->. unfold tyl_outlives_E.
    induction EQ as [|???? EQ _ IH]=>//=. by rewrite EQ IH.
  Qed.
  Global Instance tyl_outlives_E_proper : Proper ((≡) ==> eq ==> eq) tyl_outlives_E.
  Proof.
    intros ?? EQ ?? ->. unfold tyl_outlives_E.
    induction EQ as [|???? EQ _ IH]=>//=. by rewrite EQ IH.
  Qed.
  Global Instance ty_own_ne n:
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) ty_own.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_proper :
    Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) ty_own.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_ne n :
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_proper :
    Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) ty_shr.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.

  Inductive st_equiv' (ty1 ty2 : simple_type) : Prop :=
    St_equiv :
      ty1.(ty_lfts) = ty2.(ty_lfts) →
      ty1.(ty_E) = ty2.(ty_E) →
      (∀ depth tid vs, ty1.(ty_own) depth tid vs ≡ ty2.(ty_own) depth tid vs) →
      st_equiv' ty1 ty2.
  Instance st_equiv : Equiv simple_type := st_equiv'.
  Inductive st_dist' (n : nat) (ty1 ty2 : simple_type) : Prop :=
    St_dist :
      ty1.(ty_lfts) = ty2.(ty_lfts) →
      ty1.(ty_E) = ty2.(ty_E) →
      (∀ depth tid vs, ty1.(ty_own) depth tid vs ≡{n}≡ (ty2.(ty_own) depth tid vs)) →
      st_dist' n ty1 ty2.
  Instance st_dist : Dist simple_type := st_dist'.

  Definition st_ofe_mixin : OfeMixin simple_type.
  Proof.
    apply (iso_ofe_mixin ty_of_st); split=>EQ.
    - split=>//=; try apply EQ. intros ???. destruct EQ as [_ _ EQ].
      repeat eapply (EQ 0%nat) || f_equiv.
    - split; apply EQ.
    - split=>//=; try apply EQ. intros ???. destruct EQ as [_ _ EQ].
      repeat eapply (EQ 0%nat) || f_equiv.
    - split; apply EQ.
  Qed.
  Canonical Structure stO : ofeT := OfeT simple_type st_ofe_mixin.

  Global Instance st_own_ne n :
    Proper (dist n ==> eq ==> eq ==> dist n) st_own.
  Proof. intros ?? [_ _ EQ] ??-> ??->. apply (EQ 0%nat). Qed.
  Global Instance st_own_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) st_own.
  Proof. intros ?? [_ _ EQ] ??-> ??->. apply (EQ 0%nat). Qed.

  Global Instance ty_of_st_ne : NonExpansive ty_of_st.
  Proof.
    intros n ?? EQ. split=>//=; try apply EQ.
    intros ???. repeat apply EQ || f_equiv.
  Qed.
  Global Instance ty_of_st_proper : Proper ((≡) ==> (≡)) ty_of_st.
  Proof. apply (ne_proper _). Qed.
End ofe.

Ltac solve_ne_type :=
  constructor;
  solve_proper_core ltac:(fun _ => ((eapply ty_size_ne || eapply ty_lfts_ne ||
                                     eapply ty_E_ne || eapply ty_outlives_E_ne) ;
                                    try reflexivity) || f_equiv).

(** Type-nonexpansive and Type-contractive functions. *)
Inductive TypeLftMorphism `{!typeG Σ} (T : type → type) : Prop :=
| type_lft_morphism_add α βs E :
    (∀ ty, ⊢ (T ty).(ty_lft) ≡ₗ α ⊓ ty.(ty_lft)) →
    (∀ ty, elctx_interp (T ty).(ty_E) ⊣⊢
           elctx_interp E ∗ elctx_interp ty.(ty_E) ∗
           [∗ list] β ∈ βs, β ⊑ ty.(ty_lft)) →
    TypeLftMorphism T
| type_lft_morphism_const α E :
    (∀ ty, ⊢ (T ty).(ty_lft) ≡ₗ α) →
    (∀ ty, elctx_interp (T ty).(ty_E) ⊣⊢ elctx_interp E) →
    TypeLftMorphism T.
Existing Class TypeLftMorphism.

Section type_lft_morphism.
Context `{!typeG Σ}.

Global Instance type_lft_morphism_compose T U :
  TypeLftMorphism T → TypeLftMorphism U → TypeLftMorphism (T ∘ U).
Proof.
  destruct 1 as [αT βsT ET HTα HTE|αT ET HTα HTE], 1 as [αU βsU EU HUα HUE|αU EU HUα HUE].
  - apply (type_lft_morphism_add _ (αT ⊓ αU) (βsT ++ βsU)
                                 (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βsT)))=>ty.
    + iApply lft_equiv_trans. iApply HTα. rewrite -assoc.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app big_sepL_app -!assoc.
      setoid_rewrite (lft_incl_equiv_proper_r _ _ _ (HUα _)). iSplit.
      * iIntros "($ & $ & $ & $ & H)". rewrite /elctx_interp big_sepL_fmap.
        iSplit; iApply (big_sepL_impl with "H"); iIntros "!# * _ #H";
        (iApply lft_incl_trans; [done|]);
        [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
      * iIntros "($ & $ & H1 & $ & H2 & $)".
        rewrite /elctx_interp big_sepL_fmap. iCombine "H1 H2" as "H".
        rewrite -big_sepL_sep. iApply (big_sepL_impl with "H"); iIntros "!# * _ #[??]".
        by iApply lft_incl_glb.
  - apply (type_lft_morphism_const _ (αT ⊓ αU) (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βsT)))=>ty.
    + iApply lft_equiv_trans. iApply HTα.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app /elctx_interp big_sepL_fmap.
      do 5 f_equiv. by apply lft_incl_equiv_proper_r.
  - apply (type_lft_morphism_const _ αT ET)=>//=.
  - apply (type_lft_morphism_const _ αT ET)=>//=.
Qed.

Lemma type_lft_morphism_lft_equiv_proper T {HT:TypeLftMorphism T} ty1 ty2 :
  ty1.(ty_lft) ≡ₗ ty2.(ty_lft) -∗ (T ty1).(ty_lft) ≡ₗ (T ty2).(ty_lft).
Proof.
  iIntros "#?". destruct HT as [α βs E Hα HE|α E Hα HE].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|].
    iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|done].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_refl.
Qed.

Lemma type_lft_morphism_elctx_interp_proper T {HT:TypeLftMorphism T} ty1 ty2 :
  elctx_interp ty1.(ty_E) ≡ elctx_interp ty2.(ty_E) →
  (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
  elctx_interp (T ty1).(ty_E) ≡ elctx_interp (T ty2).(ty_E).
Proof.
  intros HE12 Hl. destruct HT as [α βs E Hα HE|α E Hα HE].
  - rewrite !HE HE12. do 5 f_equiv. by apply lft_incl_equiv_proper_r.
  - by rewrite !HE.
Qed.

Lemma type_lft_morphism_ext T U :
  TypeLftMorphism T →
  (∀ ty, T ty = U ty) →
  TypeLftMorphism U.
Proof. by intros [] HTU; [eleft|eright]; intros; rewrite -HTU. Qed.
End type_lft_morphism.

Class TypeContractive `{!typeG Σ} (T : type -> type): Prop := {
  type_contractive_type_lft_morphism : TypeLftMorphism T;

  type_contractive_ty_size ty1 ty2 : (T ty1).(ty_size) = (T ty2).(ty_size);

  type_contractive_ty_own n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀ depth tid vl, dist_later n (ty1.(ty_own) depth tid vl) (ty2.(ty_own) depth tid vl)) →
    (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{n}≡ ty2.(ty_shr) κ tid l) →
    (∀ depth tid vl, (T ty1).(ty_own) depth tid vl ≡{n}≡ (T ty2).(ty_own) depth tid vl);

  type_contractive_ty_shr n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀ depth tid vl, match n with S (S n) =>
        ty1.(ty_own) depth tid vl ≡{n}≡ ty2.(ty_own) depth tid vl | _ => True end) →
    (∀ κ tid l, dist_later n (ty1.(ty_shr) κ tid l) (ty2.(ty_shr) κ tid l)) →
    (∀ κ tid l, (T ty1).(ty_shr) κ tid l ≡{n}≡ (T ty2).(ty_shr) κ tid l);
}.

Class TypeNonExpansive `{!typeG Σ} (T : type -> type): Prop := {
  type_non_expansive_type_lft_morphism :> TypeLftMorphism T;

  type_non_expansive_ty_size ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) → (T ty1).(ty_size) = (T ty2).(ty_size);

  type_non_expansive_ty_own n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀ depth tid vl, ty1.(ty_own) depth tid vl ≡{n}≡ ty2.(ty_own) depth tid vl) →
    (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{S n}≡ ty2.(ty_shr) κ tid l) →
    (∀ depth tid vl, (T ty1).(ty_own) depth tid vl ≡{n}≡ (T ty2).(ty_own) depth tid vl);

  type_non_expansive_ty_shr n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀ depth tid vl, dist_later n (ty1.(ty_own) depth tid vl) (ty2.(ty_own) depth tid vl)) →
    (∀ κ tid l, ty1.(ty_shr) κ tid l ≡{n}≡ ty2.(ty_shr) κ tid l) →
    (∀ κ tid l, (T ty1).(ty_shr) κ tid l ≡{n}≡ (T ty2).(ty_shr) κ tid l);
}.


Class TypeNonExpansiveList `{!typeG Σ} (T : list type → type): Prop := {
  type_list_non_expansive_ne (Tl : list (type → type)) :
    Forall TypeNonExpansive Tl →
    TypeNonExpansive (λ ty, T ((λ T, T ty) <$> Tl));
  type_list_non_expansive_cont (Tl : list (type → type)) :
    Forall TypeContractive Tl →
    TypeContractive (λ ty, T ((λ T, T ty) <$> Tl))
}.

Class TypeListNonExpansive `{!typeG Σ} (T : type → list type): Prop :=
  type_list_non_expansive : ∃ Tl,
    (∀ ty, T ty = (λ T, T ty) <$> Tl) ∧
    Forall TypeNonExpansive Tl.

Class TypeListContractive `{!typeG Σ} (T : type → list type): Prop :=
  type_list_contractive : ∃ Tl,
    (∀ ty, T ty = (λ T, T ty) <$> Tl) ∧
    Forall TypeContractive Tl.

Section type_contractive.
  Context `{!typeG Σ}.

  Lemma type_ne_ext T U :
    TypeNonExpansive T →
    (∀ ty, T ty = U ty) →
    TypeNonExpansive U.
  Proof.
    by intros [] HTU; split; intros; rewrite -?HTU; eauto using type_lft_morphism_ext.
  Qed.

  Lemma type_contractive_ext T U :
    TypeContractive T →
    (∀ ty, T ty = U ty) →
    TypeContractive U.
  Proof.
    by intros [] HTU; split; intros; rewrite -?HTU; eauto using type_lft_morphism_ext.
  Qed.

  (* Show some more relationships between properties. *)
  Global Instance type_contractive_type_ne T :
    TypeContractive T → TypeNonExpansive T.
  Proof.
    intros HT. split.
    - apply HT.
    - intros. apply HT.
    - intros. apply HT; eauto using dist_dist_later, dist_S.
    - intros [|[|n]] ????? Hown **; apply HT; eauto using dist_dist_later.
      intros. apply dist_S, Hown.
  Qed.

  Lemma type_ne_ne_compose T1 T2 :
    TypeNonExpansive T1 → TypeNonExpansive T2 → TypeNonExpansive (T1 ∘ T2).
  Proof.
    intros HT1 HT2. split; intros.
    - apply _.
    - by apply HT1, HT2.
    - apply HT1; try by apply HT2.
      + by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
    - apply HT1; try by destruct n=>//; apply HT2.
      + by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
  Qed.

  Lemma type_contractive_compose_right T1 T2 :
    TypeContractive T1 → TypeNonExpansive T2 → TypeContractive (T1 ∘ T2).
  Proof.
    intros HT1 HT2. split; intros.
    - apply _.
    - apply HT1.
    - apply HT1; try by destruct n=>//; apply HT2.
      + by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
    - apply HT1; try by destruct n as [|[|n]]=>//; apply HT2.
      + by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
  Qed.

  Lemma type_contractive_compose_left T1 T2 :
    TypeNonExpansive T1 → TypeContractive T2 → TypeContractive (T1 ∘ T2).
  Proof.
    intros HT1 HT2. split; intros.
    - apply _.
    - apply HT1, HT2.
    - apply HT1; try by apply HT2.
      + by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
    - apply HT1; try by destruct n=>//; apply HT2.
      + by iApply type_lft_morphism_lft_equiv_proper.
      + apply type_lft_morphism_elctx_interp_proper=>//. apply _.
  Qed.

  Global Instance const_type_contractive ty :
    TypeContractive (λ _, ty).
  Proof. split; intros=>//. eright=>_. iApply lft_equiv_refl. done. Qed.

  Global Instance id_type_non_expansive :
    TypeNonExpansive id.
  Proof.
    split; intros=>//. apply (type_lft_morphism_add _ static [] []).
    - intros. rewrite left_id. apply lft_equiv_refl.
    - intros. by rewrite /elctx_interp /= left_id right_id.
  Qed.

  Global Instance type_list_non_expansive_nil :
    TypeListNonExpansive (λ _, []).
  Proof. exists []. auto. Qed.

  Global Instance type_list_contractive_nil :
    TypeListContractive (λ _, []).
  Proof. exists []. auto. Qed.

  Global Instance type_list_non_expansive_cons T Tl :
    TypeNonExpansive T → TypeListNonExpansive Tl →
    TypeListNonExpansive (λ ty, T ty :: Tl ty).
  Proof.
    intros ? [Tl' [EQ HTl']]. exists (T :: Tl'). split.
    - intros. by rewrite EQ.
    - by constructor.
  Qed.

  Global Instance type_list_contractive_cons T Tl :
    TypeContractive T → TypeListContractive Tl →
    TypeListContractive (λ ty, T ty :: Tl ty).
  Proof.
    intros ? [Tl' [EQ HTl']]. exists (T :: Tl'). split.
    - intros. by rewrite EQ.
    - by constructor.
  Qed.
End type_contractive.

Fixpoint shr_locsE (l : loc) (n : nat) : coPset :=
  match n with
  | 0%nat => ∅
  | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1%nat) n
  end.

Class Copy `{!typeG Σ} (t : type) := {
  copy_persistent depth tid vl : Persistent (t.(ty_own) depth tid vl);
  copy_shr_acc depth κ tid E F l q :
    lftE ∪ ↑shrN ⊆ E → shr_locsE l (t.(ty_size) + 1) ⊆ F →
    lft_ctx -∗ t.(ty_shr) κ tid l -∗ na_own tid F -∗ q.[κ] ={E}=∗
       ∃ q' vl, na_own tid (F ∖ shr_locsE l t.(ty_size)) ∗
         l ↦∗{q'} vl ∗ ▷t.(ty_own) depth tid vl ∗
      (na_own tid (F ∖ shr_locsE l t.(ty_size)) -∗ l ↦∗{q'} vl
       ={E}=∗ na_own tid F ∗ q.[κ])
}.
Existing Instances copy_persistent.
Instance: Params (@Copy) 2 := {}.

Class LstCopy `{!typeG Σ} (tys : list type) := lst_copy : Forall Copy tys.
Instance: Params (@LstCopy) 2 := {}.
Global Instance lst_copy_nil `{!typeG Σ} : LstCopy [] := List.Forall_nil _.
Global Instance lst_copy_cons `{!typeG Σ} ty tys :
  Copy ty → LstCopy tys → LstCopy (ty :: tys) := List.Forall_cons _ _ _.

Class Send `{!typeG Σ} (t : type) :=
  send_change_tid depth tid1 tid2 vl :
    t.(ty_own) depth tid1 vl -∗ t.(ty_own) depth tid2 vl.
Instance: Params (@Send) 2 := {}.

Class LstSend `{!typeG Σ} (tys : list type) := lst_send : Forall Send tys.
Instance: Params (@LstSend) 2 := {}.
Global Instance lst_send_nil `{!typeG Σ} : LstSend [] := List.Forall_nil _.
Global Instance lst_send_cons `{!typeG Σ} ty tys :
  Send ty → LstSend tys → LstSend (ty :: tys) := List.Forall_cons _ _ _.

Class Sync `{!typeG Σ} (t : type) :=
  sync_change_tid κ tid1 tid2 l : t.(ty_shr) κ tid1 l -∗ t.(ty_shr) κ tid2 l.
Instance: Params (@Sync) 2 := {}.

Class LstSync `{!typeG Σ} (tys : list type) := lst_sync : Forall Sync tys.
Instance: Params (@LstSync) 2 := {}.
Global Instance lst_sync_nil `{!typeG Σ} : LstSync [] := List.Forall_nil _.
Global Instance lst_sync_cons `{!typeG Σ} ty tys :
  Sync ty → LstSync tys → LstSync (ty :: tys) := List.Forall_cons _ _ _.

Section type.
  Context `{!typeG Σ}.

  (** Copy types *)
  Lemma shr_locsE_shift l n m :
    shr_locsE l (n + m) = shr_locsE l n ∪ shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n; intros l.
    - rewrite shift_loc_0. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /= IHn shift_loc_assoc.
      set_solver+.
  Qed.

  Lemma shr_locsE_disj l n m :
    shr_locsE l n ## shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n; intros l.
    - simpl. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /=.
      apply disjoint_union_l. split; last (rewrite -shift_loc_assoc; exact: IHn).
      clear IHn. revert n; induction m; intros n; simpl; first set_solver+.
      rewrite shift_loc_assoc. apply disjoint_union_r. split.
      + apply ndot_ne_disjoint. destruct l. intros [=]. lia.
      + rewrite -Z.add_assoc. move:(IHm (n + 1)%nat). rewrite Nat2Z.inj_add //.
  Qed.

  Lemma shr_locsE_shrN l n :
    shr_locsE l n ⊆ ↑shrN.
  Proof.
    revert l; induction n=>l /=; first by set_solver+.
    apply union_least; last by auto. solve_ndisj.
  Qed.

  Lemma shr_locsE_subseteq l n m :
    (n ≤ m)%nat → shr_locsE l n ⊆ shr_locsE l m.
  Proof.
    induction 1; first done. etrans; first done.
    rewrite -Nat.add_1_l [(_ + _)%nat]comm_L shr_locsE_shift. set_solver+.
  Qed.

  Lemma shr_locsE_split_tok l n m tid :
    na_own tid (shr_locsE l (n + m)) ⊣⊢
      na_own tid (shr_locsE l n) ∗ na_own tid (shr_locsE (l +ₗ n) m).
  Proof.
    rewrite shr_locsE_shift na_own_union //. apply shr_locsE_disj.
  Qed.

  Global Instance copy_equiv : Proper (equiv ==> impl) Copy.
  Proof.
    intros ty1 ty2 [EQsz%leibniz_equiv EQlfts EQE EQown EQshr] Hty1. split.
    - intros. rewrite -EQown. apply _.
    - intros *. rewrite -EQsz -EQshr. setoid_rewrite <-EQown.
      apply copy_shr_acc.
  Qed.

  Global Program Instance ty_of_st_copy st : Copy (ty_of_st st).
  Next Obligation.
    iIntros (st depth κ tid E ? l q ? HF) "#LFT #Hshr Htok Hlft /=".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
    iDestruct "Hshr" as (vl) "[Hf Hown]".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[>Hmt Hclose]"; first solve_ndisj.
    iModIntro. iExists _, _. iFrame "Hmt Hown". iIntros "Htok2".
    iDestruct ("Htok" with "Htok2") as "$". iIntros "Hmt". by iApply "Hclose".
  Qed.

  (** Send and Sync types *)
  Global Instance send_equiv : Proper (equiv ==> impl) Send.
  Proof.
    intros ty1 ty2 [EQsz%leibniz_equiv EQlfts EQE EQown EQshr] Hty1.
    rewrite /Send=>????. rewrite -!EQown. auto.
  Qed.

  Global Instance sync_equiv : Proper (equiv ==> impl) Sync.
  Proof.
    intros ty1 ty2 [EQsz%leibniz_equiv EQlfts EQE EQown EQshr] Hty1.
    rewrite /Send=>????. rewrite -!EQshr. auto.
  Qed.

  Global Instance ty_of_st_sync st : Send (ty_of_st st) → Sync (ty_of_st st).
  Proof.
    iIntros (Hsend κ tid1 tid2 l) "/=". iDestruct 1 as (vl) "[Hm Hown]".
    iExists vl. iFrame "Hm". iNext. by iApply (Hsend 0%nat).
  Qed.

  Lemma send_change_tid' t depth tid1 tid2 vl :
    Send t → t.(ty_own) depth tid1 vl ≡ t.(ty_own) depth tid2 vl.
  Proof.
    intros ?. apply: anti_symm; apply send_change_tid.
  Qed.

  Lemma sync_change_tid' t κ tid1 tid2 l :
    Sync t → t.(ty_shr) κ tid1 l ≡ t.(ty_shr) κ tid2 l.
  Proof.
    intros ?. apply: anti_symm; apply sync_change_tid.
  Qed.
End type.

Definition type_incl `{!typeG Σ} (ty1 ty2 : type) : iProp Σ :=
    (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
     (ty2.(ty_lft) ⊑ ty1.(ty_lft)) ∗
     (□ ∀ depth tid vl, ty1.(ty_own) depth tid vl -∗ ty2.(ty_own) depth tid vl) ∗
     (□ ∀ κ tid l, ty1.(ty_shr) κ tid l -∗ ty2.(ty_shr) κ tid l))%I.
Instance: Params (@type_incl) 2 := {}.

Definition subtype `{!typeG Σ} (E : elctx) (L : llctx) (ty1 ty2 : type) : Prop :=
  ∀ qL, llctx_interp L qL -∗ □ (elctx_interp E -∗ type_incl ty1 ty2).
Instance: Params (@subtype) 4 := {}.

(* TODO: The prelude should have a symmetric closure. *)
Definition eqtype `{!typeG Σ} (E : elctx) (L : llctx) (ty1 ty2 : type) : Prop :=
  subtype E L ty1 ty2 ∧ subtype E L ty2 ty1.
Instance: Params (@eqtype) 4 := {}.

Section subtyping.
  Context `{!typeG Σ}.

  Global Instance type_incl_ne : NonExpansive2 type_incl.
  Proof.
    intros n ?? [EQsz1%leibniz_equiv EQown1 EQshr1] ?? [EQsz2%leibniz_equiv EQown2 EQshr2].
    rewrite /type_incl. repeat ((by auto) || f_equiv).
  Qed.

  Global Instance type_incl_persistent ty1 ty2 : Persistent (type_incl ty1 ty2) := _.

  Lemma type_incl_refl ty : ⊢ type_incl ty ty.
  Proof. iSplit; [done|iSplit; [iApply lft_incl_refl|iSplit]]; auto. Qed.

  Lemma type_incl_trans ty1 ty2 ty3 :
    type_incl ty1 ty2 -∗ type_incl ty2 ty3 -∗ type_incl ty1 ty3.
  Proof.
    iIntros "(% & #Hl12 & #Ho12 & #Hs12) (% & #Hl23 & #Ho23 & #Hs23)".
    iSplit; first (iPureIntro; etrans; done).
    iSplit; [|iSplit].
    - iApply lft_incl_trans. iApply "Hl23". iApply "Hl12".
    - iIntros "!# %%% ?". iApply "Ho23". iApply "Ho12". done.
    - iIntros "!# %%% ?". iApply "Hs23". iApply "Hs12". done.
  Qed.

  Lemma subtype_refl E L ty : subtype E L ty ty.
  Proof. iIntros (?) "_ !# _". iApply type_incl_refl. Qed.
  Global Instance subtype_preorder E L : PreOrder (subtype E L).
  Proof.
    split; first by intros ?; apply subtype_refl.
    intros ty1 ty2 ty3 H12 H23. iIntros (?) "HL".
    iDestruct (H12 with "HL") as "#H12". iDestruct (H23 with "HL") as "#H23".
    iIntros "!# #HE".
    iDestruct ("H12" with "HE") as "H12'". iDestruct ("H23" with "HE") as "H23'".
    by iApply type_incl_trans.
  Qed.

  Lemma subtype_Forall2_llctx E L tys1 tys2 qL :
    Forall2 (subtype E L) tys1 tys2 →
    llctx_interp L qL -∗ □ (elctx_interp E -∗
           [∗ list] tys ∈ (zip tys1 tys2), type_incl (tys.1) (tys.2)).
  Proof.
    iIntros (Htys) "HL".
    iAssert ([∗ list] tys ∈ zip tys1 tys2,
             □ (elctx_interp E -∗ type_incl (tys.1) (tys.2)))%I as "#Htys".
    { iApply big_sepL_forall. iIntros (k [ty1 ty2] Hlookup).
      move:Htys => /Forall2_Forall /Forall_forall=>Htys.
      iDestruct (Htys (ty1, ty2) with "HL") as "H"; [|done].
      exact: elem_of_list_lookup_2. }
    iIntros "!# #HE". iApply (big_sepL_impl with "[$Htys]").
    iIntros "!# * % #Hincl". by iApply "Hincl".
  Qed.

  Lemma equiv_subtype E L ty1 ty2 : ty1 ≡ ty2 → subtype E L ty1 ty2.
  Proof.
    unfold subtype, type_incl=>EQ qL. iIntros "_ !# _".
    iSplit; [by iPureIntro; apply EQ|]. iSplit; [by rewrite EQ; iApply lft_incl_refl|].
    iSplit; iIntros "!# *"; rewrite EQ; iIntros "$".
  Qed.

  Lemma eqtype_unfold E L ty1 ty2 :
    eqtype E L ty1 ty2 ↔
    (∀ qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
      (ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) ∗
      (□ ∀ depth tid vl, ty1.(ty_own) depth tid vl ↔ ty2.(ty_own) depth tid vl) ∗
      (□ ∀ κ tid l, ty1.(ty_shr) κ tid l ↔ ty2.(ty_shr) κ tid l)))).
  Proof.
    split.
    - iIntros ([EQ1 EQ2] qL) "HL".
      iDestruct (EQ1 with "HL") as "#EQ1". iDestruct (EQ2 with "HL") as "#EQ2".
      iIntros "!# #HE".
      iDestruct ("EQ1" with "HE") as "($ & $ & #Ho1 & #Hs1)".
      iDestruct ("EQ2" with "HE") as "(_ & $ & #Ho2 & #Hs2)".
      iSplit; iIntros "!# *"; iSplit; iIntros "?".
      * by iApply "Ho1".
      * by iApply "Ho2".
      * by iApply "Hs1".
      * by iApply "Hs2".
    - intros EQ. split; iIntros (qL) "HL";
      iDestruct (EQ with "HL") as "#EQ"; iIntros "!# #HE";
      iDestruct ("EQ" with "HE") as "(% & [??] & #Ho & #Hs)";
      (iSplit; [done|iSplit; [done|iSplit]]); iIntros "!# * ?".
      + by iApply "Ho".
      + by iApply "Hs".
      + by iApply "Ho".
      + by iApply "Hs".
  Qed.

  Lemma eqtype_refl E L ty : eqtype E L ty ty.
  Proof. by split. Qed.

  Lemma equiv_eqtype E L ty1 ty2 : ty1 ≡ ty2 → eqtype E L ty1 ty2.
  Proof. by split; apply equiv_subtype. Qed.

  Global Instance subtype_proper E L :
    Proper (eqtype E L ==> eqtype E L ==> iff) (subtype E L).
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance eqtype_equivalence E L : Equivalence (eqtype E L).
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma type_incl_simple_type (st1 st2 : simple_type) :
    ty_lft st2 ⊑ ty_lft st1 -∗
    □ (∀ tid vl, st1.(st_own) tid vl -∗ st2.(st_own) tid vl) -∗
    type_incl st1 st2.
  Proof.
    iIntros "#Hl #Ho". iSplit; [done|]. iSplit; [done|]. iSplit; iModIntro.
    - iIntros. by iApply "Ho".
    - iIntros (???) "/=". iDestruct 1 as (vl) "[Hf Hown]". iExists vl.
      iFrame "Hf". by iApply "Ho".
  Qed.

  Lemma subtype_simple_type E L (st1 st2 : simple_type) :
    (∀ qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
       (st2.(ty_lft) ⊑ st1.(ty_lft)) ∗
       (∀ tid vl, st1.(st_own) tid vl -∗ st2.(st_own) tid vl))) →
    subtype E L st1 st2.
  Proof.
    intros Hst. iIntros (qL) "HL". iDestruct (Hst with "HL") as "#Hst".
    iIntros "!# #HE". iDestruct ("Hst" with "HE") as "[??]".
    by iApply type_incl_simple_type.
  Qed.

  Lemma subtype_weaken E1 E2 L1 L2 ty1 ty2 :
    E1 ⊆+ E2 → L1 ⊆+ L2 →
    subtype E1 L1 ty1 ty2 → subtype E2 L2 ty1 ty2.
  Proof.
    iIntros (HE12 ? Hsub qL) "HL". iDestruct (Hsub with "[HL]") as "#Hsub".
    { rewrite /llctx_interp. by iApply big_sepL_submseteq. }
    iClear "∗". iIntros "!# #HE". iApply "Hsub".
    rewrite /elctx_interp. by iApply big_sepL_submseteq.
  Qed.
End subtyping.

Section type_util.
  Context `{!typeG Σ}.

  Lemma heap_mapsto_ty_own l ty depth tid :
    l ↦∗: ty.(ty_own) depth tid ⊣⊢
      ∃ (vl : vec val ty.(ty_size)), l ↦∗ vl ∗ ty.(ty_own) depth tid vl.
  Proof.
    iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[Hl Hown]".
      iDestruct (ty_size_eq with "Hown") as %<-.
      iExists (list_to_vec vl). rewrite vec_to_list_to_vec. iFrame.
    - iIntros "H". iDestruct "H" as (vl) "[Hl Hown]". eauto with iFrame.
  Qed.
End type_util.

Hint Resolve ty_outlives_E_elctx_sat tyl_outlives_E_elctx_sat : lrust_typing.
Hint Resolve subtype_refl eqtype_refl : lrust_typing.
Hint Opaque subtype eqtype : lrust_typing.
