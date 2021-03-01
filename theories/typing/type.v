From iris.algebra Require Import numbers list.
From iris.base_logic Require Export na_invariants.
From lrust.lang Require Export proofmode notation.
From lrust.prophecy Require Export prophecy.
From lrust.lifetime Require Export frac_borrow.
From lrust.typing Require Export base lft_contexts uniq_cmra.
Set Default Proof Using "Type".

Class typeG Σ := TypeG {
  type_lrustG:> lrustG Σ;
  type_prophG:> prophG Σ;
  type_uniqG:> uniqG Σ;
  type_lftG:> lftG Σ;
  type_na_invG:> na_invG Σ;
  type_frac_borG:> frac_borG Σ;
}.

Definition lrustN := nroot .@ "lrust".
Definition shrN := lrustN .@ "shr".

Definition thread_id := na_inv_pool_name.

Implicit Type d: nat.

Record type `{!typeG Σ} A :=
  { ty_size: nat; ty_lfts: list lft; ty_E: elctx;
    ty_own: pval_depth A → thread_id → list val → iProp Σ;
    ty_shr : pval_depth A → lft → thread_id → loc → iProp Σ;

    ty_shr_persistent vπd κ tid l : Persistent (ty_shr vπd κ tid l);

    ty_size_eq vπd tid vl : ty_own vπd tid vl -∗ ⌜length vl = ty_size⌝;
    ty_own_depth_mono d d' vπ tid vl :
      d ≤ d' → ty_own (vπ,d) tid vl -∗ ty_own (vπ,d') tid vl;
    ty_shr_depth_mono d d' vπ κ tid l :
      d ≤ d' → ty_shr (vπ,d) κ tid l -∗ ty_shr (vπ,d') κ tid l;
    ty_shr_lft_mono κ κ' vπd tid l :
      κ' ⊑ κ -∗ ty_shr vπd κ tid l -∗ ty_shr vπd κ' tid l;

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
    ty_share E vπ d κ l tid q : ↑lftN ⊆ E → lft_ctx -∗
      κ ⊑ lft_intersect_list ty_lfts -∗ &{κ} (l ↦∗: ty_own (vπ,d) tid) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=> ty_shr (vπ,d) κ tid l ∗ q.[κ];

    ty_own_proph E vπ d tid vl κ q : ↑lftN ⊆ E → lft_ctx -∗
      κ ⊑ lft_intersect_list ty_lfts -∗ ty_own (vπ,d) tid vl -∗ q.[κ]
      ={E}▷=∗^d ∃ξs q', ⌜vπ ./ ξs⌝ ∗ q':+[ξs] ∗
        (q':+[ξs] ={E}=∗ ty_own (vπ,d) tid vl ∗ q.[κ]);
    ty_shr_proph E vπ d κ tid l κ' q : ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗
      κ' ⊑ lft_intersect_list ty_lfts -∗ ty_shr (vπ,d) κ tid l -∗ q.[κ']
      ={E}▷=∗^(S d) ∃ξs q', ⌜vπ ./ ξs⌝ ∗ q':+[ξs] ∗
        (q':+[ξs] ={E}=∗ ty_shr (vπ,d) κ tid l ∗ q.[κ']);
  }.
Existing Instance ty_shr_persistent.

Instance: Params (@ty_size) 2 := {}.
Instance: Params (@ty_lfts) 2 := {}.
Instance: Params (@ty_E) 2 := {}.
Instance: Params (@ty_own) 2 := {}.
Instance: Params (@ty_shr) 2 := {}.

Arguments ty_size {_ _ _} _ / : simpl nomatch.
Arguments ty_lfts {_ _ _} _ / : simpl nomatch.
Arguments ty_E {_ _ _} _ / : simpl nomatch.
Arguments ty_own {_ _ _} _ _ _ _ / : simpl nomatch.
Arguments ty_shr {_ _ _} _ _ _ _ _ / : simpl nomatch.

Notation ty_lft ty := (lft_intersect_list ty.(ty_lfts)).

Lemma ty_own_mt_depth_mono `{!typeG Σ} {A} (ty: _ A) d d' vπ tid l :
  d ≤ d' → l ↦∗: ty.(ty_own) (vπ,d) tid -∗ l ↦∗: ty.(ty_own) (vπ,d') tid.
Proof.
  iIntros (Le) "Own". iDestruct "Own" as (vl) "[Mt ?]". iExists vl.
  iSplitL "Mt"; [done|]. iApply ty_own_depth_mono; by [apply Le|].
Qed.

Definition ty_outlives_E `{!typeG Σ} {A} (ty: _ A) (κ: lft) : elctx :=
  (λ α, κ ⊑ₑ α) <$> ty.(ty_lfts).

Lemma ty_outlives_E_elctx_sat `{!typeG Σ} {A} E L (ty: _ A) α β :
  ty_outlives_E ty β ⊆+ E →
  lctx_lft_incl E L α β →
  elctx_sat E L (ty_outlives_E ty α).
Proof.
  rewrite /ty_outlives_E. elim ty.(ty_lfts); [by solve_typing|].
  move=> ?? IH Sub Incl. apply elctx_sat_lft_incl.
  - etrans; [by apply Incl|].
    eapply lctx_lft_incl_external, elem_of_submseteq, Sub. set_solver.
  - apply IH, Incl. etrans; [|by apply Sub]. by apply submseteq_cons.
Qed.

Lemma elctx_interp_ty_outlives_E `{!typeG Σ} {A} (ty: _ A) α :
  elctx_interp (ty_outlives_E ty α) ⊣⊢ α ⊑ ty.(ty_lft).
Proof.
  rewrite /ty_outlives_E /elctx_interp /elctx_elt_interp big_sepL_fmap /=.
  elim ty.(ty_lfts)=> /= [|κ l ->].
  { iSplit; iIntros "_"; [|done]. iApply lft_incl_static. } iSplit.
  - iDestruct 1 as "#[??]". by iApply lft_incl_glb.
  - iIntros "#Incl". iSplit; (iApply lft_incl_trans; [iApply "Incl"|]);
      [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
Qed.

(*
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
*)

Record simple_type `{!typeG Σ} A :=
  { st_size: nat; st_lfts: list lft; st_E: elctx;
    st_own: pval_depth A → thread_id → list val → iProp Σ;
    st_size_eq vπd tid vl : st_own vπd tid vl -∗ ⌜length vl = st_size⌝;
    st_own_persistent vπd tid vl : Persistent (st_own vπd tid vl);
    st_own_depth_mono d d' vπ tid vl :
      d ≤ d' → st_own (vπ,d) tid vl -∗ st_own (vπ,d') tid vl;
    st_own_proph E vπ d tid vl κ q : ↑lftN ⊆ E → lft_ctx -∗
      κ ⊑ lft_intersect_list st_lfts -∗ st_own (vπ,d) tid vl -∗ q.[κ]
      ={E}▷=∗^d ∃ξs q', ⌜vπ ./ ξs⌝ ∗ q':+[ξs] ∗
        (q':+[ξs] ={E}=∗ st_own (vπ,d) tid vl ∗ q.[κ]); }.
Existing Instance st_own_persistent.
Instance: Params (@st_size) 2 := {}.
Instance: Params (@st_lfts) 2 := {}.
Instance: Params (@st_E) 2 := {}.
Instance: Params (@st_own) 2 := {}.
Arguments st_size {_ _ _} _ / : simpl nomatch.
Arguments st_lfts {_ _ _} _ / : simpl nomatch.
Arguments st_E {_ _ _} _ / : simpl nomatch.
Arguments st_own {_ _ _} _ _ _ _ / : simpl nomatch.

Program Definition ty_of_st `{!typeG Σ} {A} (st: simple_type A) : type A :=
  {| ty_size := st.(st_size); ty_lfts := st.(st_lfts); ty_E := st.(st_E);
     ty_own := st.(st_own);
     ty_shr vπd κ tid l :=
       (∃ vl, &frac{κ} (λ q, l ↦∗{q} vl) ∗ ▷ st.(st_own) vπd tid vl)%I
  |}.
Next Obligation. move=> >. apply st_size_eq. Qed.
Next Obligation. move=> >. by apply st_own_depth_mono. Qed.
Next Obligation.
  move=> > Le. iDestruct 1 as (vl) "[??]". iExists vl. iSplit; [done|].
  iApply st_own_depth_mono; by [apply Le|].
Qed.
Next Obligation.
  move=> >. iIntros "Incl". iDestruct 1 as (vl) "[??]". iExists vl.
  iSplit; [|done]. by iApply (frac_bor_shorten with "Incl").
Qed.
Next Obligation.
  move=> *. iIntros "#LFT ? Bor Tok". 
  iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
  iMod (bor_sep with "LFT Bor") as "[Bor Own]"; [done|].
  iMod (bor_persistent with "LFT Own Tok") as "[Own Tok]"; [done|].
  iMod (bor_fracture (λ q, _ ↦∗{q} _)%I with "LFT Bor") as "Hfrac"; [done|].

  iModIntro.
  iApply step_fupdN_intro; [done|]. iNext.
  iSplitR "Tok"; [|done]. iExists vl. iModIntro. by iSplit.
Qed.
Next Obligation. move=> >. apply st_own_proph. Qed.
Next Obligation.
  move=> *. iIntros "#LFT _ #Incl". iDestruct 1 as (vl) "[Bor Own]".
  iIntros "Tok". simpl. iModIntro. iNext. iModIntro.
  iDestruct (st_own_proph with "LFT Incl Own Tok") as "Upd"; [done|].
  iApply (step_fupdN_wand with "Upd"). iDestruct 1 as (ξs q' ?) "[Tok Upd]".
  iExists ξs, q'. iSplit; [done|]. iSplitL "Tok"; [done|]. iIntros "Tok".
  iMod ("Upd" with "Tok") as "[??]". iModIntro. iSplit; [|done]. iExists vl.
  by iSplit.
Qed.

Coercion ty_of_st : simple_type >-> type.

Declare Scope lrust_type_scope.
Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(* OFE and COFE structures on types and simple types. *)
Section ofe.
  Context `{!typeG Σ}.

  Inductive type_equiv' {A} (ty1 ty2: type A) : Prop :=
    Type_equiv :
      ty1.(ty_size) = ty2.(ty_size) →
      ty1.(ty_lfts) = ty2.(ty_lfts) →
      ty1.(ty_E) = ty2.(ty_E) →
      (∀vπd tid vs, ty1.(ty_own) vπd tid vs ≡ ty2.(ty_own) vπd tid vs) →
      (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡ ty2.(ty_shr) vπd κ tid l) →
      type_equiv' ty1 ty2.
  Instance type_equiv {A} : Equiv (type A) := type_equiv'.
  Inductive type_dist' {A} (n: nat) (ty1 ty2: type A) : Prop :=
    Type_dist :
      ty1.(ty_size) = ty2.(ty_size) →
      ty1.(ty_lfts) = ty2.(ty_lfts) →
      ty1.(ty_E) = ty2.(ty_E) →
      (∀vπd tid vs, ty1.(ty_own) vπd tid vs ≡{n}≡ ty2.(ty_own) vπd tid vs) →
      (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{n}≡ ty2.(ty_shr) vπd κ tid l) →
      type_dist' n ty1 ty2.
  Instance type_dist {A} : Dist (type A) := type_dist'.

  Let T A := prodO (prodO (prodO (prodO
    natO (listO lftO)) (listO (prodO lftO lftO)))
    (pval_depth A -d> thread_id -d> list val -d> iPropO Σ))
    (pval_depth A -d> lft -d> thread_id -d> loc -d> iPropO Σ).

  Definition type_unpack {A} (ty: type A) : T A :=
    (ty.(ty_size), ty.(ty_lfts), ty.(ty_E), ty.(ty_own), ty.(ty_shr)).

  Definition type_ofe_mixin {A} : OfeMixin (type A).
  Proof.
    apply (iso_ofe_mixin type_unpack);
    (rewrite /type_unpack; split; [by move=> [-> -> -> ??]|]);
    move=> [[[[??]?]?]?]; simpl in *; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure typeO {A} : ofe := Ofe (type A) type_ofe_mixin.

  Global Instance ty_size_ne {A} n : Proper (dist n ==> (=)) (@ty_size _ _ A).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_size_proper {A} : Proper ((≡) ==> (=)) (@ty_size _ _ A).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_lfts_ne {A} n : Proper (dist n ==> (=)) (@ty_lfts _ _ A).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_lfts_proper {A} : Proper ((≡) ==> (=)) (@ty_lfts _ _ A).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_E_ne {A} n : Proper (dist n ==> (=)) (@ty_E _ _ A).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_E_proper {A} : Proper ((≡) ==> (=)) (@ty_E _ _ A).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_outlives_E_ne {A} n :
    Proper (dist n ==> (=) ==> (=)) (@ty_outlives_E _ _ A).
  Proof. move=> ?? [_ Eqv _ _ _]. by rewrite /ty_outlives_E Eqv. Qed.
  Global Instance ty_outlives_E_proper {A} :
    Proper ((≡) ==> (=) ==> (=)) (@ty_outlives_E _ _ A).
  Proof. move=> ?? [_ Eqv _ _ _]. by rewrite /ty_outlives_E Eqv. Qed.
(*
  Global Instance tyl_E_ne {A} n : Proper (dist n ==> (=)) (@tyl_E _ _ A).
  Proof.
    move=> ?? Eqv. unfold tyl_E.
    induction Eqv as [|???? Eqv _ IH]=>//=. by rewrite Eqv IH.
  Qed.
  Global Instance tyl_E_proper {A} : Proper ((≡) ==> (=)) (@tyl_E _ _ A).
  Proof.
    move=> ?? Eqv. unfold tyl_E.
    induction Eqv as [|???? Eqv _ IH]=>//=. by rewrite Eqv IH.
  Qed.
  Global Instance tyl_outlives_E_ne {A} n :
    Proper (dist n ==> (=) ==> (=)) (@tyl_outlives_E _ _ A).
  Proof.
    move=> ?? Eqv ?? ->. unfold tyl_outlives_E.
    induction Eqv as [|???? Eqv _ IH]=>//=. by rewrite Eqv IH.
  Qed.
  Global Instance tyl_outlives_E_proper {A} :
    Proper ((≡) ==> (=) ==> (=)) (@tyl_outlives_E _ _ A).
  Proof.
    move=> ?? Eqv ?? ->. unfold tyl_outlives_E.
    induction Eqv as [|???? Eqv _ IH]=>//=. by rewrite Eqv IH.
  Qed.
*)
  Global Instance ty_own_ne {A} n:
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (@ty_own _ _ A).
  Proof. move=> ?? Eqv ??-> ??-> ??->. apply Eqv. Qed.
  Global Instance ty_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) (@ty_own _ _ A).
  Proof. move=> ?? Eqv ??-> ??-> ??->. apply Eqv. Qed.
  Global Instance ty_shr_ne {A} n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (@ty_shr _ _ A).
  Proof. move=> ?? Eqv ??-> ??-> ??-> ??->. apply Eqv. Qed.
  Global Instance ty_shr_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (@ty_shr _ _ A).
  Proof. move=> ?? Eqv ??-> ??-> ??-> ??->. apply Eqv. Qed.

  Inductive st_equiv' {A} (st1 st2: simple_type A) : Prop :=
    St_equiv :
      st1.(ty_size) = st2.(ty_size) →
      st1.(ty_lfts) = st2.(ty_lfts) →
      st1.(ty_E) = st2.(ty_E) →
      (∀vπd tid vl, st1.(ty_own) vπd tid vl ≡ st2.(ty_own) vπd tid vl) →
      st_equiv' st1 st2.
  Instance st_equiv {A} : Equiv (simple_type A) := st_equiv'.
  Inductive st_dist' {A} (n: nat) (st1 st2: simple_type A) : Prop :=
    St_dist :
      st1.(ty_size) = st2.(ty_size) →
      st1.(ty_lfts) = st2.(ty_lfts) →
      st1.(ty_E) = st2.(ty_E) →
      (∀vπd tid vl, st1.(ty_own) vπd tid vl ≡{n}≡ (st2.(ty_own) vπd tid vl)) →
      st_dist' n st1 st2.
  Instance st_dist {A} : Dist (simple_type A) := st_dist'.

  Definition st_ofe_mixin {A} : OfeMixin (simple_type A).
  Proof.
    apply (iso_ofe_mixin ty_of_st); (split=> Eqv; split; try by apply Eqv);
    move=> > /=; f_equiv; f_equiv; by move: Eqv=> [_ _ _ /= ->].
  Qed.
  Canonical Structure stO {A} : ofe := Ofe (simple_type A) st_ofe_mixin.

  Global Instance st_own_ne n {A} :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (@st_own _ _ A).
  Proof. move=> ?? Eqv ??-> ??-> ??->. apply Eqv. Qed.
  Global Instance st_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) (@st_own _ _ A).
  Proof. move=> ?? Eqv ??-> ??-> ??->. apply Eqv. Qed.

  Global Instance ty_of_st_ne {A} : NonExpansive (@ty_of_st _ _ A).
  Proof.
    move=> ??? Eqv. split; try apply Eqv. move=> > /=. f_equiv. f_equiv.
    by rewrite Eqv.
  Qed.
  Global Instance ty_of_st_proper {A} : Proper ((≡) ==> (≡)) (@ty_of_st _ _ A).
  Proof. apply (ne_proper _). Qed.
End ofe.

Ltac solve_ne_type :=
  constructor;
  solve_proper_core ltac:(fun _ => ((eapply ty_size_ne || eapply ty_lfts_ne ||
                                     eapply ty_E_ne || eapply ty_outlives_E_ne) ;
                                    try reflexivity) || f_equiv).

(** Type-nonexpansive and Type-contractive functions. *)
Inductive TypeLftMorphism `{!typeG Σ} {A B} (T : type A → type B) : Prop :=
| type_lft_morphism_add α βs E :
    (∀ty, ⊢ (T ty).(ty_lft) ≡ₗ α ⊓ ty.(ty_lft)) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢
           elctx_interp E ∗ elctx_interp ty.(ty_E) ∗
           [∗ list] β ∈ βs, β ⊑ ty.(ty_lft)) →
    TypeLftMorphism T
| type_lft_morphism_const α E :
    (∀ty, ⊢ (T ty).(ty_lft) ≡ₗ α) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢ elctx_interp E) →
    TypeLftMorphism T.
Existing Class TypeLftMorphism.

Section type_lft_morphism.
Context `{!typeG Σ}.

Global Instance type_lft_morphism_compose {A B C} (T: _ B → _ C) (U: _ A → _ B):
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

Lemma type_lft_morphism_lft_equiv_proper {A B} (T: _ A → _ B)
  {HT: TypeLftMorphism T} ty1 ty2 :
  ty1.(ty_lft) ≡ₗ ty2.(ty_lft) -∗ (T ty1).(ty_lft) ≡ₗ (T ty2).(ty_lft).
Proof.
  iIntros "#?". destruct HT as [α βs E Hα HE|α E Hα HE].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|].
    iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|done].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_refl.
Qed.

Lemma type_lft_morphism_elctx_interp_proper {A B} (T: _ A → _ B)
  {HT: TypeLftMorphism T} ty1 ty2 :
  elctx_interp ty1.(ty_E) ≡ elctx_interp ty2.(ty_E) →
  (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
  elctx_interp (T ty1).(ty_E) ≡ elctx_interp (T ty2).(ty_E).
Proof.
  intros HE12 Hl. destruct HT as [α βs E Hα HE|α E Hα HE].
  - rewrite !HE HE12. do 5 f_equiv. by apply lft_incl_equiv_proper_r.
  - by rewrite !HE.
Qed.

Lemma type_lft_morphism_ext {A B} (T U: _ A → _ B) :
  TypeLftMorphism T → (∀ty, T ty = U ty) → TypeLftMorphism U.
Proof. by intros [] HTU; [eleft|eright]; intros; rewrite -HTU. Qed.
End type_lft_morphism.

Class TypeContractive `{!typeG Σ} {A B} (T: type A -> type B): Prop := {
  type_contractive_type_lft_morphism : TypeLftMorphism T;

  type_contractive_ty_size ty1 ty2 : (T ty1).(ty_size) = (T ty2).(ty_size);

  type_contractive_ty_own n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl,
      dist_later n (ty1.(ty_own) vπd tid vl) (ty2.(ty_own) vπd tid vl)) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{n}≡ ty2.(ty_shr) vπd κ tid l) →
    (∀vπd tid vl,
      (T ty1).(ty_own) vπd tid vl ≡{n}≡ (T ty2).(ty_own) vπd tid vl);

  type_contractive_ty_shr n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl, match n with S (S n) =>
      ty1.(ty_own) vπd tid vl ≡{n}≡ ty2.(ty_own) vπd tid vl | _ => True end) →
    (∀vπd κ tid l,
      dist_later n (ty1.(ty_shr) vπd κ tid l) (ty2.(ty_shr) vπd κ tid l)) →
    (∀vπd κ tid l,
      (T ty1).(ty_shr) vπd κ tid l ≡{n}≡ (T ty2).(ty_shr) vπd κ tid l);
}.

Class TypeNonExpansive `{!typeG Σ} {A B} (T : type A -> type B): Prop := {
  type_non_expansive_type_lft_morphism :> TypeLftMorphism T;

  type_non_expansive_ty_size ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) → (T ty1).(ty_size) = (T ty2).(ty_size);

  type_non_expansive_ty_own n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl, ty1.(ty_own) vπd tid vl ≡{n}≡ ty2.(ty_own) vπd tid vl) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{S n}≡ ty2.(ty_shr) vπd κ tid l) →
    (∀vπd tid vl,
      (T ty1).(ty_own) vπd tid vl ≡{n}≡ (T ty2).(ty_own) vπd tid vl);

  type_non_expansive_ty_shr n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl,
      dist_later n (ty1.(ty_own) vπd tid vl) (ty2.(ty_own) vπd tid vl)) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{n}≡ ty2.(ty_shr) vπd κ tid l) →
    (∀vπd κ tid l,
      (T ty1).(ty_shr) vπd κ tid l ≡{n}≡ (T ty2).(ty_shr) vπd κ tid l);
}.

(*
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
    (∀ty, T ty = (λ T, T ty) <$> Tl) ∧
    Forall TypeNonExpansive Tl.

Class TypeListContractive `{!typeG Σ} (T : type → list type): Prop :=
  type_list_contractive : ∃ Tl,
    (∀ty, T ty = (λ T, T ty) <$> Tl) ∧
    Forall TypeContractive Tl.
*)

Section type_contractive.
  Context `{!typeG Σ}.

  Lemma type_ne_ext {A B} (T U: _ A → _ B) :
    TypeNonExpansive T → (∀ty, T ty = U ty) → TypeNonExpansive U.
  Proof.
    by intros [] HTU; split; intros; rewrite -?HTU;
    eauto using type_lft_morphism_ext.
  Qed.

  Lemma type_contractive_ext {A B} (T U: _ A → _ B) :
    TypeContractive T → (∀ty, T ty = U ty) → TypeContractive U.
  Proof.
    by intros [] HTU; split; intros; rewrite -?HTU;
    eauto using type_lft_morphism_ext.
  Qed.

  (* Show some more relationships between properties. *)
  Global Instance type_contractive_type_ne {A B} (T: _ A → _ B) :
    TypeContractive T → TypeNonExpansive T.
  Proof.
    intros HT. split.
    - apply HT.
    - intros. apply HT.
    - intros. apply HT; eauto using dist_dist_later, dist_S.
    - intros [|[|n]] ????? Hown **; apply HT; eauto using dist_dist_later.
      intros. apply dist_S, Hown.
  Qed.

  Lemma type_ne_ne_compose {A B C} (T1: _ B → _ C) (T2: _ A → _ B) :
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

  Lemma type_contractive_compose_right {A B C} (T1: _ B → _ C) (T2: _ A → _ B) :
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

  Lemma type_contractive_compose_left {A B C} (T1: _ B → _ C) (T2: _ A → _ B) :
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

  Global Instance const_type_contractive {A B} (ty: _ B) :
    TypeContractive (λ (_: _ A), ty).
  Proof. split; intros=>//. eright=>_. iApply lft_equiv_refl. done. Qed.

  Global Instance id_type_non_expansive {A} :
    TypeNonExpansive (id: _ A → _ A).
  Proof.
    split; intros=>//. apply (type_lft_morphism_add _ static [] []).
    - intros. rewrite left_id. apply lft_equiv_refl.
    - intros. by rewrite /elctx_interp /= left_id right_id.
  Qed.

(*
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
*)
End type_contractive.

Fixpoint shr_locsE (l: loc) (n: nat) : coPset :=
  match n with
  | 0%nat => ∅
  | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1%nat) n
  end.

Class Copy `{!typeG Σ} {A} (ty: type A) := {
  copy_persistent vπd tid vl : Persistent (ty.(ty_own) vπd tid vl);
  copy_shr_acc vπd κ tid E F l q :
    ↑lftN ∪ ↑shrN ⊆ E → shr_locsE l (ty.(ty_size) + 1) ⊆ F →
    lft_ctx -∗ ty.(ty_shr) vπd κ tid l -∗ na_own tid F -∗ q.[κ] ={E}=∗
       ∃ q' vl, na_own tid (F ∖ shr_locsE l ty.(ty_size)) ∗
         l ↦∗{q'} vl ∗ ▷ty.(ty_own) vπd tid vl ∗
      (na_own tid (F ∖ shr_locsE l ty.(ty_size)) -∗ l ↦∗{q'} vl
       ={E}=∗ na_own tid F ∗ q.[κ])
}.
Existing Instances copy_persistent.
Instance: Params (@Copy) 2 := {}.

(*
Class LstCopy `{!typeG Σ} (tys : list type) := lst_copy : Forall Copy tys.
Instance: Params (@LstCopy) 2 := {}.
Global Instance lst_copy_nil `{!typeG Σ} : LstCopy [] := List.Forall_nil _.
Global Instance lst_copy_cons `{!typeG Σ} ty tys :
  Copy ty → LstCopy tys → LstCopy (ty :: tys) := List.Forall_cons _ _ _.
*)

Class Send `{!typeG Σ} {A} (ty: type A) :=
  send_change_tid tid1 tid2 vπd vl :
    ty.(ty_own) vπd tid1 vl -∗ ty.(ty_own) vπd tid2 vl.
Instance: Params (@Send) 2 := {}.

(*
Class LstSend `{!typeG Σ} (tys : list type) := lst_send : Forall Send tys.
Instance: Params (@LstSend) 2 := {}.
Global Instance lst_send_nil `{!typeG Σ} : LstSend [] := List.Forall_nil _.
Global Instance lst_send_cons `{!typeG Σ} ty tys :
  Send ty → LstSend tys → LstSend (ty :: tys) := List.Forall_cons _ _ _.
*)

Class Sync `{!typeG Σ} {A} (ty: type A) :=
  sync_change_tid tid1 tid2 vπd κ l :
    ty.(ty_shr) vπd κ tid1 l -∗ ty.(ty_shr) vπd κ tid2 l.
Instance: Params (@Sync) 2 := {}.

(*
Class LstSync `{!typeG Σ} (tys : list type) := lst_sync : Forall Sync tys.
Instance: Params (@LstSync) 2 := {}.
Global Instance lst_sync_nil `{!typeG Σ} : LstSync [] := List.Forall_nil _.
Global Instance lst_sync_cons `{!typeG Σ} ty tys :
  Sync ty → LstSync tys → LstSync (ty :: tys) := List.Forall_cons _ _ _.
*)

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

  Global Instance copy_equiv {A} : Proper (equiv ==> impl) (@Copy _ _ A).
  Proof.
    intros ty1 ty2 [EQsz%leibniz_equiv EQlfts EQE EQown EQshr] Hty1. split.
    - intros. rewrite -EQown. apply _.
    - intros *. rewrite -EQsz -EQshr. setoid_rewrite <-EQown.
      apply copy_shr_acc.
  Qed.

  Global Program Instance ty_of_st_copy {A} (st: _ A) : Copy (ty_of_st st).
  Next Obligation.
    move=> *. iIntros "#LFT #Hshr Htok Hlft /=".
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
    iDestruct "Hshr" as (vl) "[Hf Hown]".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[>Hmt Hclose]"; first solve_ndisj.
    iModIntro. iExists _, _. iFrame "Hmt Hown". iIntros "Htok2".
    iDestruct ("Htok" with "Htok2") as "$". iIntros "Hmt". by iApply "Hclose".
  Qed.

  (** Send and Sync types *)
  Global Instance send_equiv {A} : Proper (equiv ==> impl) (@Send _ _ A).
  Proof.
    move=> ?? [_ _ _ Eqv _] ?. rewrite /Send=> *. by rewrite -!Eqv.
  Qed.

  Global Instance sync_equiv {A} : Proper (equiv ==> impl) (@Sync _ _ A).
  Proof.
    move=> ?? [_ _ _ _ Eqv] ?. rewrite /Sync=> *. by rewrite -!Eqv.
  Qed.

  Global Instance ty_of_st_sync {A} (st: _ A) :
    Send (ty_of_st st) → Sync (ty_of_st st).
  Proof.
    move=> Hsend >. iDestruct 1 as (vl) "[Hm Hown]".
    iExists vl. iFrame "Hm". iNext. by iApply Hsend.
  Qed.

  Lemma send_change_tid' {A} (ty: _ A) vπd tid1 tid2 vl :
    Send ty → ty.(ty_own) vπd tid1 vl ≡ ty.(ty_own) vπd tid2 vl.
  Proof.
    intros ?. apply: anti_symm; apply send_change_tid.
  Qed.

  Lemma sync_change_tid' {A} (ty: _ A) vπd κ tid1 tid2 l :
    Sync ty → ty.(ty_shr) vπd κ tid1 l ≡ ty.(ty_shr) vπd κ tid2 l.
  Proof.
    intros ?. apply: anti_symm; apply sync_change_tid.
  Qed.
End type.

Definition type_incl `{!typeG Σ} {A} (ty1 ty2: type A) : iProp Σ :=
    (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
     (ty2.(ty_lft) ⊑ ty1.(ty_lft)) ∗
     (□ ∀vπd tid vl, ty1.(ty_own) vπd tid vl -∗ ty2.(ty_own) vπd tid vl) ∗
     (□ ∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l -∗ ty2.(ty_shr) vπd κ tid l))%I.
Instance: Params (@type_incl) 2 := {}.

Definition subtype `{!typeG Σ} {A} E L (ty1 ty2: type A) : Prop :=
  ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗ type_incl ty1 ty2).
Instance: Params (@subtype) 4 := {}.

(* TODO: The prelude should have a symmetric closure. *)
Definition eqtype `{!typeG Σ} {A} E L (ty1 ty2: type A) : Prop :=
  subtype E L ty1 ty2 ∧ subtype E L ty2 ty1.
Instance: Params (@eqtype) 4 := {}.

Section subtyping.
  Context `{!typeG Σ}.

  Global Instance type_incl_ne {A} : NonExpansive2 (@type_incl _ _ A).
  Proof.
    intros n ?? [EQsz1%leibniz_equiv EQown1 EQshr1] ??
      [EQsz2%leibniz_equiv EQown2 EQshr2].
    rewrite /type_incl. repeat ((by auto) || f_equiv).
  Qed.

  Global Instance type_incl_persistent {A} (ty1 ty2: _ A) :
    Persistent (type_incl ty1 ty2) := _.

  Lemma type_incl_refl {A} (ty: _ A) : ⊢ type_incl ty ty.
  Proof. iSplit; [done|iSplit; [iApply lft_incl_refl|iSplit]]; auto. Qed.

  Lemma type_incl_trans {A} (ty1 ty2 ty3: _ A) :
    type_incl ty1 ty2 -∗ type_incl ty2 ty3 -∗ type_incl ty1 ty3.
  Proof.
    iIntros "(% & #Hl12 & #Ho12 & #Hs12) (% & #Hl23 & #Ho23 & #Hs23)".
    iSplit; first (iPureIntro; etrans; done).
    iSplit; [|iSplit].
    - iApply lft_incl_trans. iApply "Hl23". iApply "Hl12".
    - iIntros "!# %%% ?". iApply "Ho23". iApply "Ho12". done.
    - iIntros "!# %%%% ?". iApply "Hs23". iApply "Hs12". done.
  Qed.

  Lemma subtype_refl {A} E L (ty: _ A) : subtype E L ty ty.
  Proof. iIntros (?) "_ !# _". iApply type_incl_refl. Qed.
  Global Instance subtype_preorder {A} E L : PreOrder (@subtype _ _ A E L).
  Proof.
    split; first by intros ?; apply subtype_refl.
    intros ty1 ty2 ty3 H12 H23. iIntros (?) "HL".
    iDestruct (H12 with "HL") as "#H12". iDestruct (H23 with "HL") as "#H23".
    iIntros "!# #HE". iDestruct ("H12" with "HE") as "H12'".
    iDestruct ("H23" with "HE") as "H23'". by iApply type_incl_trans.
  Qed.

(*
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
*)

  Lemma equiv_subtype {A} E L (ty1 ty2: _ A) : ty1 ≡ ty2 → subtype E L ty1 ty2.
  Proof.
    unfold subtype, type_incl=>EQ qL. iIntros "_ !# _".
    iSplit; [by iPureIntro; apply EQ|].
    iSplit; [by rewrite EQ; iApply lft_incl_refl|].
    iSplit; iIntros "!# *"; rewrite EQ; iIntros "$".
  Qed.

  Lemma eqtype_unfold {A} E L (ty1 ty2: _ A) :
    eqtype E L ty1 ty2 ↔
    (∀ qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      (⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗
      (ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) ∗
      (□ ∀vπd tid vl, ty1.(ty_own) vπd tid vl ↔ ty2.(ty_own) vπd tid vl) ∗
      (□ ∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ↔ ty2.(ty_shr) vπd κ tid l)))).
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

  Lemma eqtype_refl {A} E L (ty: _ A) : eqtype E L ty ty.
  Proof. by split. Qed.

  Lemma equiv_eqtype {A} E L (ty1 ty2: _ A) : ty1 ≡ ty2 → eqtype E L ty1 ty2.
  Proof. by split; apply equiv_subtype. Qed.

  Global Instance subtype_proper {A} E L :
    Proper (eqtype E L ==> eqtype E L ==> iff) (@subtype _ _ A E L).
  Proof. intros ??[] ??[]. split; intros; by etrans; [|etrans]. Qed.

  Global Instance eqtype_equivalence {A} E L : Equivalence (@eqtype _ _ A E L).
  Proof.
    split.
    - by split.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; etrans; (apply H1 || apply H2).
  Qed.

  Lemma type_incl_simple_type {A} (st1 st2: simple_type A) :
    ty_size st1 = ty_size st2 → ty_lft st2 ⊑ ty_lft st1 -∗
    □ (∀vπd tid vl, st1.(st_own) vπd tid vl -∗ st2.(st_own) vπd tid vl) -∗
    type_incl st1 st2.
  Proof.
    move=> ?. iIntros "#Hl #Ho". iSplit; [done|]. iSplit; [done|].
    iSplit; iModIntro.
    - iIntros. by iApply "Ho".
    - iIntros (???) "/=". iDestruct 1 as (vl) "[Hf Hown]". iExists vl.
      iFrame "Hf". by iApply "Ho".
  Qed.

  Lemma subtype_simple_type {A} E L (st1 st2: simple_type A) :
    (∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜ty_size st1 = ty_size st2⌝ ∗ st2.(ty_lft) ⊑ st1.(ty_lft) ∗
      (∀vπd tid vl, st1.(st_own) vπd tid vl -∗ st2.(st_own) vπd tid vl))) →
    subtype E L st1 st2.
  Proof.
    intros Hst. iIntros (qL) "HL". iDestruct (Hst with "HL") as "#Hst".
    iIntros "!# #HE". iDestruct ("Hst" with "HE") as (?) "[??]".
    by iApply type_incl_simple_type.
  Qed.

  Lemma subtype_weaken {A} E1 E2 L1 L2 (ty1 ty2: _ A) :
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

  Lemma heap_mapsto_ty_own {A} l (ty: _ A) vπd tid :
    l ↦∗: ty.(ty_own) vπd tid ⊣⊢
      ∃(vl : vec val ty.(ty_size)), l ↦∗ vl ∗ ty.(ty_own) vπd tid vl.
  Proof.
    iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[Hl Hown]".
      iDestruct (ty_size_eq with "Hown") as %<-.
      iExists (list_to_vec vl). rewrite vec_to_list_to_vec. iFrame.
    - iIntros "H". iDestruct "H" as (vl) "[Hl Hown]". eauto with iFrame.
  Qed.
End type_util.

Global Hint Resolve ty_outlives_E_elctx_sat (* tyl_outlives_E_elctx_sat *)
  : lrust_typing.
Global Hint Resolve subtype_refl eqtype_refl : lrust_typing.
Global Hint Opaque subtype eqtype : lrust_typing.
