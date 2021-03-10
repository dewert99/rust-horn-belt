From iris.algebra Require Import numbers list.
From iris.base_logic Require Export na_invariants.
From lrust.util Require Import point_free types.
From lrust.prophecy Require Export prophecy.
From lrust.lifetime Require Export frac_borrow.
From lrust.lang Require Export proofmode notation.
From lrust.typing Require Export base lft_contexts uniq_cmra.
Set Default Proof Using "Type".
Open Scope nat.

Class typeG Σ := TypeG {
  type_lrustG:> lrustG Σ;  type_prophG:> prophG Σ;  type_uniqG:> uniqG Σ;
  type_lftG:> lftG Σ;  type_na_invG:> na_invG Σ;  type_frac_borG:> frac_borG Σ;
}.

Definition lrustN := nroot .@ "lrust".
Definition shrN := lrustN .@ "shr".

Definition thread_id := na_inv_pool_name.

(** * Type *)

Record type `{!typeG Σ} A := {
  ty_size: nat;  ty_lfts: list lft;  ty_E: elctx;
  ty_own: pval_depth A → thread_id → list val → iProp Σ;
  ty_shr: pval_depth A → lft → thread_id → loc → iProp Σ;

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
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξs q', ⌜vπ ./ ξs⌝ ∗
      q':+[ξs] ∗ (q':+[ξs] ={E}=∗ ty_own (vπ,d) tid vl ∗ q.[κ]);
  ty_shr_proph E vπ d κ tid l κ' q : ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗
    κ' ⊑ lft_intersect_list ty_lfts -∗ ty_shr (vπ,d) κ tid l -∗ q.[κ']
    ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξs q', ⌜vπ ./ ξs⌝ ∗
      q':+[ξs] ∗ (q':+[ξs] ={E}=∗ ty_shr (vπ,d) κ tid l ∗ q.[κ']);
}.
Existing Instance ty_shr_persistent.

Instance: Params (@ty_size) 3 := {}. Instance: Params (@ty_lfts) 3 := {}.
Instance: Params (@ty_E) 3 := {}.
Instance: Params (@ty_own) 3 := {}. Instance: Params (@ty_shr) 3 := {}.

Arguments ty_size {_ _ _} _ / : simpl nomatch.
Arguments ty_lfts {_ _ _} _ / : simpl nomatch.
Arguments ty_E {_ _ _} _ / : simpl nomatch.
Arguments ty_own {_ _ _} _ _ _ _ / : simpl nomatch.
Arguments ty_shr {_ _ _} _ _ _ _ _ / : simpl nomatch.

Notation ty_lft ty := (lft_intersect_list ty.(ty_lfts)).
Notation typel := (hlist type).

Lemma ty_own_mt_depth_mono `{!typeG Σ} {A} (ty: _ A) d d' vπ tid l :
  d ≤ d' → l ↦∗: ty.(ty_own) (vπ,d) tid -∗ l ↦∗: ty.(ty_own) (vπ,d') tid.
Proof.
  iIntros (Le). iDestruct 1 as (vl) "[??]". iExists vl. iFrame.
  iApply ty_own_depth_mono; by [apply Le|].
Qed.

Definition ty_outlives_E `{!typeG Σ} {A} (ty: _ A) (κ: lft) : elctx :=
  (λ α, κ ⊑ₑ α) <$> ty.(ty_lfts).

Lemma ty_outlives_E_elctx_sat `{!typeG Σ} {A} E L (ty: _ A) α β :
  ty_outlives_E ty β ⊆+ E → lctx_lft_incl E L α β →
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
  elim ty.(ty_lfts)=> /=[|κ l ->].
  { iSplit; iIntros "_"; [|done]. iApply lft_incl_static. } iSplit.
  - iDestruct 1 as "#[??]". by iApply lft_incl_glb.
  - iIntros "#Incl". iSplit; (iApply lft_incl_trans; [iApply "Incl"|]);
      [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
Qed.

Definition tyl_lfts `{!typeG Σ} {As} (tyl: typel As) : list lft :=
  concat ((λ _, ty_lfts) +<$> tyl).
Definition tyl_E `{!typeG Σ} {As} (tyl: typel As) : elctx :=
  concat ((λ _, ty_E) +<$> tyl).
Definition tyl_outlives_E `{!typeG Σ} {As} (tyl: typel As) κ : elctx :=
  concat ((λ _ ty, ty_outlives_E ty κ) +<$> tyl).

Lemma tyl_outlives_E_elctx_sat `{!typeG Σ} {As} E L (tyl: typel As) α β :
  tyl_outlives_E tyl β ⊆+ E → lctx_lft_incl E L α β →
  elctx_sat E L (tyl_outlives_E tyl α).
Proof.
  elim tyl=> [|> IH]; [solve_typing|]=> Outlv Incl. apply elctx_sat_app.
  - eapply ty_outlives_E_elctx_sat; [|by apply Incl]. etrans; [|by apply Outlv].
    by apply submseteq_inserts_r.
  - apply IH; [|done]. etrans; [|by apply Outlv]. by apply submseteq_inserts_l.
Qed.

Declare Scope lrust_type_scope.
Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(** Simple Type *)

Record simple_type `{!typeG Σ} A := {
  st_size: nat;  st_lfts: list lft;  st_E: elctx;
  st_own: pval_depth A → thread_id → list val → iProp Σ;
  st_own_persistent vπd tid vl : Persistent (st_own vπd tid vl);
  st_size_eq vπd tid vl : st_own vπd tid vl -∗ ⌜length vl = st_size⌝;
  st_own_depth_mono d d' vπ tid vl :
    d ≤ d' → st_own (vπ,d) tid vl -∗ st_own (vπ,d') tid vl;
  st_own_proph E vπ d tid vl κ q : ↑lftN ⊆ E → lft_ctx -∗
    κ ⊑ lft_intersect_list st_lfts -∗ st_own (vπ,d) tid vl -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξs q', ⌜vπ ./ ξs⌝ ∗
      q':+[ξs] ∗ (q':+[ξs] ={E}=∗ st_own (vπ,d) tid vl ∗ q.[κ]);
}.
Existing Instance st_own_persistent.
Instance: Params (@st_size) 3 := {}. Instance: Params (@st_lfts) 3 := {}.
Instance: Params (@st_E) 3 := {}. Instance: Params (@st_own) 3 := {}.
Arguments st_size {_ _ _} _ / : simpl nomatch.
Arguments st_lfts {_ _ _} _ / : simpl nomatch.
Arguments st_E {_ _ _} _ / : simpl nomatch.
Arguments st_own {_ _ _} _ _ _ _ / : simpl nomatch.

Program Definition ty_of_st `{!typeG Σ} {A} (st: simple_type A) : type A := {|
  ty_size := st.(st_size);  ty_lfts := st.(st_lfts);  ty_E := st.(st_E);
  ty_own := st.(st_own);
  ty_shr vπd κ tid l := (∃vl, &frac{κ} (λ q, l ↦∗{q} vl) ∗ ▷ st.(st_own) vπd tid vl)%I;
|}.
Next Obligation. move=> >. apply st_size_eq. Qed.
Next Obligation. move=> >. by apply st_own_depth_mono. Qed.
Next Obligation.
  move=> > Le. iDestruct 1 as (vl) "[??]". iExists vl. iFrame.
  iApply st_own_depth_mono; by [apply Le|].
Qed.
Next Obligation.
  move=> >. iIntros "Incl". iDestruct 1 as (vl) "[??]". iExists vl. iFrame.
  by iApply (frac_bor_shorten with "Incl").
Qed.
Next Obligation.
  move=> *. iIntros "#LFT ? Bor Tok".
  iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
  iMod (bor_sep with "LFT Bor") as "[Bor Own]"; [done|].
  iMod (bor_persistent with "LFT Own Tok") as "[??]"; [done|].
  iMod (bor_fracture (λ q, _ ↦∗{q} vl)%I with "LFT Bor") as "?"; [done|]. iModIntro.
  iApply step_fupdN_intro; [done|]. iNext. iModIntro. iFrame. iExists vl. iFrame.
Qed.
Next Obligation. move=> >. apply st_own_proph. Qed.
Next Obligation.
  move=> *. iIntros "#LFT _ Incl". iDestruct 1 as (vl) "[? Own]". iIntros "Tok !>!>".
  iDestruct (st_own_proph with "LFT Incl Own Tok") as "> Upd"; [done|].
  iModIntro. iApply (step_fupdN_wand with "Upd"). iDestruct 1 as "> Upd".
  iDestruct "Upd" as (ξs q' ?) "[Ptoks Upd]". iModIntro. iExists ξs, q'.
  iSplit; [done|]. iFrame "Ptoks". iIntros "Tok".
  iMod ("Upd" with "Tok") as "[? $]". iModIntro. iExists vl. iFrame.
Qed.

Coercion ty_of_st: simple_type >-> type.

(** Plain Type *)

Record plain_type `{!typeG Σ} A := {
  pt_size: nat;  pt_lfts: list lft;  pt_E: elctx;
  pt_own: A → thread_id → list val → iProp Σ;
  pt_own_persistent v tid vl : Persistent (pt_own v tid vl);
  pt_size_eq v tid vl : pt_own v tid vl -∗ ⌜length vl = pt_size⌝;
}.
Existing Instance pt_own_persistent.
Instance: Params (@pt_size) 3 := {}. Instance: Params (@pt_lfts) 3 := {}.
Instance: Params (@pt_E) 3 := {}. Instance: Params (@pt_own) 3 := {}.
Arguments pt_size {_ _ _} _ / : simpl nomatch.
Arguments pt_lfts {_ _ _} _ / : simpl nomatch.
Arguments pt_E {_ _ _} _ / : simpl nomatch.
Arguments pt_own {_ _ _} _ _ _ _ / : simpl nomatch.

Program Definition st_of_pt `{!typeG Σ} {A} (pt: plain_type A) : simple_type A := {|
  st_size := pt.(pt_size);  st_lfts := pt.(pt_lfts);  st_E := pt.(pt_E);
  st_own vπd tid vl := (∃v, ⌜vπd.1 = const v⌝ ∗ pt.(pt_own) v tid vl)%I;
|}.
Next Obligation. move=> >. iDestruct 1 as (? _) "?". by iApply pt_size_eq. Qed.
Next Obligation. done. Qed.
Next Obligation.
  move=> * /=. iIntros "_ _". iDestruct 1 as (?->) "?". iIntros "Ptok !>".
  iApply step_fupdN_intro; [done|]. iIntros "!>!>". iExists [], 1%Qp.
  iSplit; [done|]. iSplit; [by rewrite /proph_toks|]. iIntros "_ !>".
  iFrame "Ptok". iExists v. by iSplit.
Qed.

Coercion st_of_pt: plain_type >-> simple_type.

(** * OFE Structures on Types *)

Section ofe.
  Context `{!typeG Σ}.

  (**  Type *)

  Inductive type_equiv' {A} (ty1 ty2: type A) : Prop := TypeEquiv:
    ty1.(ty_size) = ty2.(ty_size) → ty1.(ty_lfts) = ty2.(ty_lfts) →
    ty1.(ty_E) = ty2.(ty_E) →
    (∀vπd tid vs, ty1.(ty_own) vπd tid vs ≡ ty2.(ty_own) vπd tid vs) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡ ty2.(ty_shr) vπd κ tid l) →
    type_equiv' ty1 ty2.
  Global Instance type_equiv {A} : Equiv (type A) := type_equiv'.
  Inductive type_dist' {A} (n: nat) (ty1 ty2: type A) : Prop := TypeDist:
    ty1.(ty_size) = ty2.(ty_size) → ty1.(ty_lfts) = ty2.(ty_lfts) →
    ty1.(ty_E) = ty2.(ty_E) →
    (∀vπd tid vs, ty1.(ty_own) vπd tid vs ≡{n}≡ ty2.(ty_own) vπd tid vs) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{n}≡ ty2.(ty_shr) vπd κ tid l) →
    type_dist' n ty1 ty2.
  Global Instance type_dist {A} : Dist (type A) := type_dist'.

  Definition type_unpack {A} (ty: type A)
    : prodO (prodO (prodO (prodO natO (listO lftO)) (listO (prodO lftO lftO)))
      (pval_depth A -d> thread_id -d> list val -d> iPropO Σ))
      (pval_depth A -d> lft -d> thread_id -d> loc -d> iPropO Σ) :=
    (ty.(ty_size), ty.(ty_lfts), ty.(ty_E), ty.(ty_own), ty.(ty_shr)).

  Definition type_ofe_mixin {A} : OfeMixin (type A).
  Proof.
    apply (iso_ofe_mixin type_unpack);
    (rewrite /type_unpack; split; [by move=> [->->->??]|]);
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
  Proof. rewrite /ty_outlives_E. by move=> ?? [_ -> _ _ _]. Qed.
  Global Instance ty_outlives_E_proper {A} :
    Proper ((≡) ==> (=) ==> (=)) (@ty_outlives_E _ _ A).
  Proof. rewrite /ty_outlives_E. by move=> ?? [_ -> _ _ _]. Qed.

  Global Instance hlist_dist_type {As} : Dist (typel As) := @hlist_dist (@typeO) _.

  Global Instance tyl_E_ne {As} n : Proper (dist n ==> (=)) (@tyl_E _ _ As).
  Proof. move=> ??. rewrite /tyl_E. by elim=> /=[|> ->_->]. Qed.
  Global Instance tyl_E_proper {As} : Proper ((≡) ==> (=)) (@tyl_E _ _ As).
  Proof. move=> ??. rewrite /tyl_E. by elim=> /=[|> ->_->]. Qed.
  Global Instance tyl_outlives_E_ne {As} n :
    Proper (dist n ==> (=) ==> (=)) (@tyl_outlives_E _ _ As).
  Proof.
    move=> ?? Eqv ??->. rewrite /tyl_outlives_E. by elim Eqv=> /=[|> ->_->].
  Qed.
  Global Instance tyl_outlives_E_proper {A} :
    Proper ((≡) ==> (=) ==> (=)) (@tyl_outlives_E _ _ A).
  Proof.
    move=> ?? Eqv ??->. rewrite /tyl_outlives_E. by elim Eqv=> /=[|> ->_->].
  Qed.

  Global Instance ty_own_ne {A} n:
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (@ty_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.
  Global Instance ty_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) (@ty_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_ne {A} n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (@ty_shr _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (@ty_shr _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.

  (** Simple Type *)

  Inductive simple_type_equiv' {A} (st1 st2: simple_type A) : Prop := SimpleTypeEquiv:
    st1.(st_size) = st2.(st_size) → st1.(st_lfts) = st2.(st_lfts) →
    st1.(st_E) = st2.(st_E) →
    (∀vπd tid vl, st1.(st_own) vπd tid vl ≡ st2.(st_own) vπd tid vl) →
    simple_type_equiv' st1 st2.
  Global Instance simple_type_equiv {A} : Equiv (simple_type A) := simple_type_equiv'.
  Inductive simple_type_dist' {A} (n: nat) (st1 st2: simple_type A) : Prop :=
    SimpleTypeDist:
    st1.(st_size) = st2.(st_size) → st1.(st_lfts) = st2.(st_lfts) →
    st1.(st_E) = st2.(st_E) →
    (∀vπd tid vl, st1.(st_own) vπd tid vl ≡{n}≡ (st2.(st_own) vπd tid vl)) →
    simple_type_dist' n st1 st2.
  Global Instance simple_type_dist {A} : Dist (simple_type A) := simple_type_dist'.

  Definition simple_type_ofe_mixin {A} : OfeMixin (simple_type A).
  Proof.
    apply (iso_ofe_mixin ty_of_st); (split=> Eqv; split; try by apply Eqv);
    move=> > /=; f_equiv; f_equiv; by move: Eqv=> [_ _ _ ->].
  Qed.
  Canonical Structure simple_typeO {A} : ofe := Ofe (simple_type A) simple_type_ofe_mixin.

  Global Instance st_own_ne n {A} :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (@st_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.
  Global Instance st_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) (@st_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.

  Global Instance ty_of_st_ne {A} : NonExpansive (@ty_of_st _ _ A).
  Proof.
    move=> ??? Eqv. split; try apply Eqv. move=> > /=. do 2 f_equiv.
    by rewrite Eqv.
  Qed.
  Global Instance ty_of_st_proper {A} : Proper ((≡) ==> (≡)) (@ty_of_st _ _ A).
  Proof. apply (ne_proper _). Qed.

  (** Plain Type *)

  Inductive plain_type_equiv' {A} (pt1 pt2: plain_type A) : Prop := PlainTypeEquiv:
    pt1.(pt_size) = pt2.(pt_size) → pt1.(pt_lfts) = pt2.(pt_lfts) →
    pt1.(pt_E) = pt2.(pt_E) →
    (∀v tid vl, pt1.(pt_own) v tid vl ≡ pt2.(pt_own) v tid vl) →
    plain_type_equiv' pt1 pt2.
  Global Instance plain_type_equiv {A} : Equiv (plain_type A) := plain_type_equiv'.
  Inductive plain_type_dist' {A} (n: nat) (pt1 pt2: plain_type A) : Prop :=
    PlainTypeDist:
    pt1.(pt_size) = pt2.(pt_size) → pt1.(pt_lfts) = pt2.(pt_lfts) →
    pt1.(pt_E) = pt2.(pt_E) →
    (∀v tid vl, pt1.(pt_own) v tid vl ≡{n}≡ (pt2.(pt_own) v tid vl)) →
    plain_type_dist' n pt1 pt2.
  Global Instance plain_type_dist {A} : Dist (plain_type A) := plain_type_dist'.

  Definition plain_type_unpack {A} (pt: plain_type A)
    : prodO (prodO (prodO natO (listO lftO)) (listO (prodO lftO lftO)))
      (A -d> thread_id -d> list val -d> iPropO Σ) :=
    (pt.(pt_size), pt.(pt_lfts), pt.(pt_E), pt.(pt_own)).

  Definition plain_type_ofe_mixin {A} : OfeMixin (plain_type A).
  Proof.
    apply (iso_ofe_mixin plain_type_unpack);
    (rewrite /plain_type_unpack; split; [by move=> [->->->?]|]);
    move=> [[[??]?]?]; simpl in *; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure plain_typeO {A} : ofe := Ofe (plain_type A) plain_type_ofe_mixin.

  Global Instance pt_own_ne n {A} :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (@pt_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.
  Global Instance pt_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) (@pt_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.

  Global Instance st_of_pt_ne {A} : NonExpansive (@st_of_pt _ _ A).
  Proof.
    move=> ??? Eqv. split; try apply Eqv. move=> > /=. do 2 f_equiv.
    by rewrite Eqv.
  Qed.
  Global Instance st_of_pt_proper {A} : Proper ((≡) ==> (≡)) (@st_of_pt _ _ A).
  Proof. apply (ne_proper _). Qed.

End ofe.

Ltac solve_ne_type :=
  constructor;
  solve_proper_core ltac:(fun _ => ((eapply ty_size_ne || eapply ty_lfts_ne ||
                                     eapply ty_E_ne || eapply ty_outlives_E_ne);
                                    try reflexivity) || f_equiv).

(** * Nonexpansiveness/Contractiveness of Type Morphisms *)

Inductive TypeLftMorphism `{!typeG Σ} {A B} (T: type A → type B) : Prop :=
| type_lft_morphism_add α βs E :
    (∀ty, ⊢ (T ty).(ty_lft) ≡ₗ α ⊓ ty.(ty_lft)) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢
      elctx_interp E ∗ elctx_interp ty.(ty_E) ∗ [∗ list] β ∈ βs, β ⊑ ty.(ty_lft)) →
    TypeLftMorphism T
| type_lft_morphism_const α E :
    (∀ty, ⊢ (T ty).(ty_lft) ≡ₗ α) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢ elctx_interp E) →
    TypeLftMorphism T.
Existing Class TypeLftMorphism.

Section type_lft_morphism.
Context `{!typeG Σ}.

Global Instance type_lft_morphism_compose {A B C} (T: _ B → _ C) (U: _ A → _ B) :
  TypeLftMorphism T → TypeLftMorphism U → TypeLftMorphism (T ∘ U).
Proof.
  destruct 1 as [αT βsT ET HTα HTE|αT ET HTα HTE],
           1 as [αU βsU EU HUα HUE|αU EU HUα HUE].
  - apply (type_lft_morphism_add _ (αT ⊓ αU) (βsT ++ βsU)
                                 (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βsT)))=>ty.
    + iApply lft_equiv_trans. iApply HTα. rewrite -assoc.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app big_sepL_app -!assoc.
      setoid_rewrite (lft_incl_equiv_proper_r _ _ _ (HUα _)). iSplit.
      * iIntros "($ & $ & $ & $ & H)". rewrite /elctx_interp big_sepL_fmap.
        iSplit; iApply (big_sepL_impl with "H"); iIntros "!> * _ #H";
        (iApply lft_incl_trans; [done|]);
        [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
      * iIntros "($ & $ & H1 & $ & H2 & $)".
        rewrite /elctx_interp big_sepL_fmap. iCombine "H1 H2" as "H".
        rewrite -big_sepL_sep. iApply (big_sepL_impl with "H").
        iIntros "!> * _ #[??]". by iApply lft_incl_glb.
  - apply (type_lft_morphism_const _ (αT ⊓ αU)
            (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βsT)))=>ty.
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
  elctx_interp ty1.(ty_E) ≡ elctx_interp ty2.(ty_E) → (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
  elctx_interp (T ty1).(ty_E) ≡ elctx_interp (T ty2).(ty_E).
Proof.
  intros HE12 Hl. destruct HT as [α βs E Hα HE|α E Hα HE]; [|by rewrite !HE].
  rewrite !HE HE12. do 5 f_equiv. by apply lft_incl_equiv_proper_r.
Qed.

Lemma type_lft_morphism_ext {A B} (T U: _ A → _ B) :
  TypeLftMorphism T → (∀ty, T ty = U ty) → TypeLftMorphism U.
Proof. by intros [] HTU; [eleft|eright]; intros; rewrite -HTU. Qed.

End type_lft_morphism.

Class TypeContractive `{!typeG Σ} {A B} (T: type A -> type B) : Prop := {
  type_contractive_type_lft_morphism : TypeLftMorphism T;

  type_contractive_ty_size ty1 ty2 : (T ty1).(ty_size) = (T ty2).(ty_size);

  type_contractive_ty_own n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) → (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl, dist_later n (ty1.(ty_own) vπd tid vl) (ty2.(ty_own) vπd tid vl)) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{n}≡ ty2.(ty_shr) vπd κ tid l) →
    (∀vπd tid vl, (T ty1).(ty_own) vπd tid vl ≡{n}≡ (T ty2).(ty_own) vπd tid vl);

  type_contractive_ty_shr n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) → (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl, match n with S (S n) =>
      ty1.(ty_own) vπd tid vl ≡{n}≡ ty2.(ty_own) vπd tid vl | _ => True end) →
    (∀vπd κ tid l, dist_later n (ty1.(ty_shr) vπd κ tid l) (ty2.(ty_shr) vπd κ tid l)) →
    (∀vπd κ tid l, (T ty1).(ty_shr) vπd κ tid l ≡{n}≡ (T ty2).(ty_shr) vπd κ tid l);
}.

Class TypeNonExpansive `{!typeG Σ} {A B} (T: type A -> type B) : Prop := {
  type_non_expansive_type_lft_morphism :> TypeLftMorphism T;

  type_non_expansive_ty_size ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) → (T ty1).(ty_size) = (T ty2).(ty_size);

  type_non_expansive_ty_own n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl, ty1.(ty_own) vπd tid vl ≡{n}≡ ty2.(ty_own) vπd tid vl) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{S n}≡ ty2.(ty_shr) vπd κ tid l) →
    (∀vπd tid vl, (T ty1).(ty_own) vπd tid vl ≡{n}≡ (T ty2).(ty_own) vπd tid vl);

  type_non_expansive_ty_shr n ty1 ty2 :
    ty1.(ty_size) = ty2.(ty_size) →
    (⊢ ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) →
    elctx_interp (ty1.(ty_E)) ≡ elctx_interp (ty2.(ty_E)) →
    (∀vπd tid vl,
      dist_later n (ty1.(ty_own) vπd tid vl) (ty2.(ty_own) vπd tid vl)) →
    (∀vπd κ tid l, ty1.(ty_shr) vπd κ tid l ≡{n}≡ ty2.(ty_shr) vπd κ tid l) →
    (∀vπd κ tid l, (T ty1).(ty_shr) vπd κ tid l ≡{n}≡ (T ty2).(ty_shr) vπd κ tid l);
}.

Class TypeListNonExpansive `{!typeG Σ} {A Bs} (T: type A → typel Bs) : Prop :=
  type_list_non_expansive: ∃Tl,
    (∀ty, T ty = (λ B (T': type A → type B), T' ty) +<$>+ Tl) ∧
    HForall (λ _, TypeNonExpansive) Tl.

Class TypeListContractive `{!typeG Σ} {A Bs} (T: type A → typel Bs) : Prop :=
  type_list_contractive: ∃Tl,
    (∀ty, T ty = (λ B (T': type A → type B), T' ty) +<$>+ Tl) ∧
    HForall (λ _, TypeContractive) Tl.

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

  Global Instance const_type_contractive {A B} (ty: _ B) : TypeContractive (λ _: _ A, ty).
  Proof. split; intros=>//. eright=>_. iApply lft_equiv_refl. done. Qed.

  Global Instance id_type_non_expansive {A} : TypeNonExpansive (id: _ A → _ A).
  Proof.
    split; intros=>//. apply (type_lft_morphism_add _ static [] []).
    - intros. rewrite left_id. apply lft_equiv_refl.
    - intros. by rewrite /elctx_interp /= left_id right_id.
  Qed.

  Global Instance type_list_non_expansive_nil {A} : TypeListNonExpansive (λ _: _ A, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.

  Global Instance type_list_contractive_nil {A} : TypeListContractive (λ _: _ A, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.

  Global Instance type_list_non_expansive_cons {A B Bs} (T: _ A → _ B) (Tl: _ A → _ Bs) :
    TypeNonExpansive T → TypeListNonExpansive Tl →
    TypeListNonExpansive (λ ty, T ty +:: Tl ty).
  Proof.
    move=> ? [Tl' [Eq ?]]. exists (T +:: Tl'). split; [|by constructor] => ?.
    by rewrite Eq.
  Qed.

  Global Instance type_list_contractive_cons {A B Bs} (T: _ A → _ B) (Tl: _ A → _ Bs) :
    TypeContractive T → TypeListContractive Tl →
    TypeListContractive (λ ty, T ty +:: Tl ty).
  Proof.
    move=> ? [Tl' [Eq ?]]. exists (T +:: Tl'). split; [|by constructor] => ?.
    by rewrite Eq.
  Qed.

End type_contractive.

(** * Traits *)

Fixpoint shr_locsE (l: loc) (n: nat) : coPset :=
  match n with 0 => ∅ | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1) n end.

Class Copy `{!typeG Σ} {A} (ty: type A) := {
  copy_persistent vπd tid vl : Persistent (ty.(ty_own) vπd tid vl);
  copy_shr_acc vπd κ tid E F l q :
    ↑lftN ∪ ↑shrN ⊆ E → shr_locsE l (S ty.(ty_size)) ⊆ F →
    lft_ctx -∗ ty.(ty_shr) vπd κ tid l -∗ na_own tid F -∗ q.[κ] ={E}=∗ ∃q' vl,
      na_own tid (F ∖ shr_locsE l ty.(ty_size)) ∗
      l ↦∗{q'} vl ∗ ▷ty.(ty_own) vπd tid vl ∗
      (na_own tid (F ∖ shr_locsE l ty.(ty_size)) -∗ l ↦∗{q'} vl
        ={E}=∗ na_own tid F ∗ q.[κ])
}.
Existing Instances copy_persistent.
Instance: Params (@Copy) 3 := {}.

Class ListCopy `{!typeG Σ} {As} (tyl: typel As) := list_copy: HForall (λ _, Copy) tyl.
Instance: Params (@ListCopy) 3 := {}.
Global Instance list_copy_nil `{!typeG Σ} : ListCopy +[].
Proof. constructor. Qed.
Global Instance list_copy_cons `{!typeG Σ} {A As} (ty: _ A) (tyl: _ As) :
  Copy ty → ListCopy tyl → ListCopy (ty +:: tyl).
Proof. by constructor. Qed.

Class Send `{!typeG Σ} {A} (ty: type A) :=
  send_change_tid tid1 tid2 vπd vl :
    ty.(ty_own) vπd tid1 vl -∗ ty.(ty_own) vπd tid2 vl.
Instance: Params (@Send) 3 := {}.

Class ListSend `{!typeG Σ} {As} (tyl: typel As) := list_send: HForall (λ _, Send) tyl.
Instance: Params (@ListSend) 3 := {}.
Global Instance list_send_nil `{!typeG Σ} : ListSend +[].
Proof. constructor. Qed.
Global Instance list_send_cons `{!typeG Σ} {A As} (ty: _ A) (tyl: _ As) :
  Send ty → ListSend tyl → ListSend (ty +:: tyl).
Proof. by constructor. Qed.

Class Sync `{!typeG Σ} {A} (ty: type A) :=
  sync_change_tid tid1 tid2 vπd κ l :
    ty.(ty_shr) vπd κ tid1 l -∗ ty.(ty_shr) vπd κ tid2 l.
Instance: Params (@Sync) 3 := {}.

Class ListSync `{!typeG Σ} {As} (tyl: typel As) := list_sync : HForall (λ _, Sync) tyl.
Instance: Params (@ListSync) 3 := {}.
Global Instance list_sync_nil `{!typeG Σ} : ListSync +[].
Proof. constructor. Qed.
Global Instance list_sync_cons `{!typeG Σ} {A As} (ty: _ A) (tyl: _ As) :
  Sync ty → ListSync tyl → ListSync (ty +:: tyl).
Proof. by constructor. Qed.

Section type.
  Context `{!typeG Σ}.

  (** Lemmas on Copy *)

  Lemma shr_locsE_shift l n m :
    shr_locsE l (n + m) = shr_locsE l n ∪ shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n; intros l.
    - rewrite shift_loc_0. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /= IHn shift_loc_assoc. set_solver+.
  Qed.

  Lemma shr_locsE_disj l n m :
    shr_locsE l n ## shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n; intros l.
    - simpl. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /=.
      apply disjoint_union_l. split; [|rewrite -shift_loc_assoc; exact: IHn].
      clear IHn. revert n; induction m; intros n; simpl; first set_solver+.
      rewrite shift_loc_assoc. apply disjoint_union_r. split.
      + apply ndot_ne_disjoint. destruct l. intros [=]. lia.
      + rewrite -Z.add_assoc. move:(IHm (n + 1)). rewrite Nat2Z.inj_add //.
  Qed.

  Lemma shr_locsE_shrN l n : shr_locsE l n ⊆ ↑shrN.
  Proof.
    revert l; induction n=>l /=; first by set_solver+.
    apply union_least; last by auto. solve_ndisj.
  Qed.

  Lemma shr_locsE_subseteq l n m : n ≤ m → shr_locsE l n ⊆ shr_locsE l m.
  Proof.
    induction 1; first done. etrans; first done.
    rewrite -Nat.add_1_l [(_ + _)]comm_L shr_locsE_shift. set_solver+.
  Qed.

  Lemma shr_locsE_split_tok l n m tid :
    na_own tid (shr_locsE l (n + m)) ⊣⊢
    na_own tid (shr_locsE l n) ∗ na_own tid (shr_locsE (l +ₗ n) m).
  Proof. rewrite shr_locsE_shift na_own_union //. apply shr_locsE_disj. Qed.

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
    iDestruct (na_own_acc with "Htok") as "[$ Htok]"; [solve_ndisj|].
    iDestruct "Hshr" as (?) "[Hf Hown]".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (?) "[>Hmt Hclose]"; [solve_ndisj|].
    iModIntro. iExists _, _. iFrame "Hmt Hown". iIntros "Htok2".
    iDestruct ("Htok" with "Htok2") as "$". iIntros "Hmt". by iApply "Hclose".
  Qed.

  (** Lemmas on Send and Sync *)

  Global Instance send_equiv {A} : Proper (equiv ==> impl) (@Send _ _ A).
  Proof. move=> ?? [_ _ _ Eqv _] ?. rewrite /Send=> *. by rewrite -!Eqv. Qed.

  Global Instance sync_equiv {A} : Proper (equiv ==> impl) (@Sync _ _ A).
  Proof. move=> ?? [_ _ _ _ Eqv] ?. rewrite /Sync=> *. by rewrite -!Eqv. Qed.

  Global Instance ty_of_st_sync {A} (st: _ A) : Send (ty_of_st st) → Sync (ty_of_st st).
  Proof.
    move=> Hsend >. iDestruct 1 as (vl) "[Hm Hown]".
    iExists vl. iFrame "Hm". iNext. by iApply Hsend.
  Qed.

  Lemma send_change_tid' {A} (ty: _ A) vπd tid1 tid2 vl :
    Send ty → ty.(ty_own) vπd tid1 vl ≡ ty.(ty_own) vπd tid2 vl.
  Proof. move=> ?. apply: anti_symm; apply send_change_tid. Qed.

  Lemma sync_change_tid' {A} (ty: _ A) vπd κ tid1 tid2 l :
    Sync ty → ty.(ty_shr) vπd κ tid1 l ≡ ty.(ty_shr) vπd κ tid2 l.
  Proof. move=> ?. apply: anti_symm; apply sync_change_tid. Qed.

End type.

(** * Subtyping *)

Definition type_incl `{!typeG Σ} {A B} (f: A → B) (ty1: type A) (ty2: type B) : iProp Σ :=
  ⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗ (ty2.(ty_lft) ⊑ ty1.(ty_lft)) ∗
  (□ ∀vπ d tid vl, ty1.(ty_own) (vπ,d) tid vl -∗ ty2.(ty_own) (f∘vπ,d) tid vl) ∗
  (□ ∀vπ d κ tid l, ty1.(ty_shr) (vπ,d) κ tid l -∗ ty2.(ty_shr) (f∘vπ,d) κ tid l).
Instance: Params (@type_incl) 4 := {}.

Definition subtype `{!typeG Σ} {A B} E L (f: A → B) (ty1: type A) (ty2: type B) : Prop :=
  ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗ type_incl f ty1 ty2).
Instance: Params (@subtype) 6 := {}.

Definition eqtype `{!typeG Σ} {A B} E L (f: A → B) (g: B → A) (ty1: type A) (ty2: type B)
  : Prop := subtype E L f ty1 ty2 ∧ subtype E L g ty2 ty1.
Instance: Params (@eqtype) 6 := {}.

Section subtyping.
  Context `{!typeG Σ}.

  (** Subtyping *)

  Global Instance type_incl_ne {A B} (f: A → B) : NonExpansive2 (type_incl f).
  Proof.
    rewrite /type_incl.
    move=> ???[->->_ EqvOwn EqvShr]??[->->_ EqvOwn' EqvShr']. do 4 f_equiv.
    - do 8 f_equiv. by rewrite EqvOwn EqvOwn'.
    - do 10 f_equiv. by rewrite EqvShr EqvShr'.
  Qed.

  Global Instance type_incl_persistent {A B} (f: A → B) ty1 ty2 :
    Persistent (type_incl f ty1 ty2) := _.

  Lemma type_incl_refl {A} (ty: _ A) : ⊢ type_incl id ty ty.
  Proof. iSplit; [done|]. iSplit; [by iApply lft_incl_refl|]. iSplit; auto. Qed.

  Lemma type_incl_trans {A B C} (f: A → B) (g: B → C) ty1 ty2 ty3 :
    type_incl f ty1 ty2 -∗ type_incl g ty2 ty3 -∗ type_incl (g ∘ f) ty1 ty3.
  Proof.
    iIntros "(% & #Lft & #Own & #Shr) (% & #Lft' & #Own' & #Shr')".
    iSplit. { iPureIntro. by etrans. } iSplit; [|iSplit].
    - iApply lft_incl_trans; [iApply "Lft'"|iApply "Lft"].
    - iIntros (????) "!>?". iApply "Own'". by iApply "Own".
    - iIntros (?????) "!>?". iApply "Shr'". by iApply "Shr".
  Qed.

  Lemma subtype_refl {A} E L (ty: _ A) : subtype E L id ty ty.
  Proof. iIntros (?) "_ !> _". iApply type_incl_refl. Qed.

  Lemma subtype_trans {A B C} E L (f: A → B) (g: B → C) ty1 ty2 ty3 :
    subtype E L f ty1 ty2 → subtype E L g ty2 ty3 → subtype E L (g ∘ f) ty1 ty3.
  Proof.
    move=> Sub Sub'. iIntros (?) "L". iDestruct (Sub with "L") as "#Wand".
    iDestruct (Sub' with "L") as "#Wand'". iIntros "!> #E".
    iDestruct ("Wand" with "E") as "Incl". iDestruct ("Wand'" with "E") as "Incl'".
    iApply (type_incl_trans with "Incl Incl'").
  Qed.

  Lemma subtype_weaken {A B} E1 E2 L1 L2 (f: A → B) ty1 ty2 :
    E1 ⊆+ E2 → L1 ⊆+ L2 →
    subtype E1 L1 f ty1 ty2 → subtype E2 L2 f ty1 ty2.
  Proof.
    iIntros (HE12 ? Hsub ?) "HL". iDestruct (Hsub with "[HL]") as "#Hsub".
    { rewrite /llctx_interp. by iApply big_sepL_submseteq. }
    iClear "∗". iIntros "!> #HE". iApply "Hsub".
    rewrite /elctx_interp. by iApply big_sepL_submseteq.
  Qed.

(* This lemma is not supported.
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

  (** Type Equivalence *)

  Lemma equiv_subtype {A} E L ty1 ty2 : ty1 ≡ ty2 → subtype E L (@id A) ty1 ty2.
  Proof.
    move=> Eqv ?. iIntros "_ !> _". iSplit. { iPureIntro. apply Eqv. }
    iSplit. { rewrite Eqv. iApply lft_incl_refl. }
    iSplit; iIntros "!> *"; rewrite Eqv; iIntros "$".
  Qed.

  Lemma eqtype_unfold {A B} E L (f: A → B) g ty1 ty2 : g ∘ f = id → f ∘ g = id →
    eqtype E L f g ty1 ty2 ↔
    ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜ty1.(ty_size) = ty2.(ty_size)⌝ ∗ (ty1.(ty_lft) ≡ₗ ty2.(ty_lft)) ∗
      (□ ∀vπ d tid vl, ty1.(ty_own) (vπ,d) tid vl ↔ ty2.(ty_own) (f∘vπ,d) tid vl) ∗
      (□ ∀vπ d κ tid l, ty1.(ty_shr) (vπ,d) κ tid l ↔ ty2.(ty_shr) (f∘vπ,d) κ tid l)).
  Proof.
    move=> Eq_gf Eq_fg. split.
    - iIntros ([EQ1 EQ2] ?) "HL".
      iDestruct (EQ1 with "HL") as "#EQ1". iDestruct (EQ2 with "HL") as "#EQ2".
      iIntros "!> #HE".
      iDestruct ("EQ1" with "HE") as "($ & $ & #Ho1 & #Hs1)".
      iDestruct ("EQ2" with "HE") as "(_ & $ & #Ho2 & #Hs2)".
      iSplit; iIntros "!> *"; iSplit; iIntros "Own";
      [by iApply "Ho1"| |by iApply "Hs1"|];
      [iDestruct ("Ho2" with "Own") as "?"|iDestruct ("Hs2" with "Own") as "?"];
      by rewrite compose_assoc Eq_gf.
    - intros EQ. split; iIntros (?) "HL";
      iDestruct (EQ with "HL") as "#EQ"; iIntros "!> #HE";
      iDestruct ("EQ" with "HE") as "(% & [??] & #Ho & #Hs)";
      (iSplit; [done|]; iSplit; [done|]; iSplit); iIntros "!> * Own";
      [by iApply "Ho"|by iApply "Hs"| |]; [iApply "Ho"|iApply "Hs"];
      by rewrite compose_assoc Eq_fg.
  Qed.

  Lemma eqtype_refl {A} E L (ty: _ A) : eqtype E L id id ty ty.
  Proof. split; apply subtype_refl. Qed.

  Lemma equiv_eqtype {A} E L (ty1 ty2: _ A) : ty1 ≡ ty2 → eqtype E L id id ty1 ty2.
  Proof. by split; apply equiv_subtype. Qed.

  Global Instance subtype_proper {A B} E L (f: A → B) :
    Proper (eqtype E L id id ==> eqtype E L id id ==> (↔)) (subtype E L f).
  Proof.
    move=> ??[Sub1 Sub1']??[Sub2 Sub2']. split; move=> ?;
    eapply (subtype_trans _ _ id f); [by apply Sub1'| |by apply Sub1|];
    eapply (subtype_trans _ _ f id); [|by apply Sub2| |by apply Sub2']; done.
  Qed.

  Lemma eqtype_symm {A B} E L (f: A → B) g ty ty' :
    eqtype E L f g ty ty' → eqtype E L g f ty' ty.
  Proof. move=> [??]. by split. Qed.

  Lemma eqtype_trans {A B C} E L (f: A → B) f' (g: B → C) g' ty1 ty2 ty3 :
    eqtype E L f f' ty1 ty2 → eqtype E L g g' ty2 ty3 →
    eqtype E L (g ∘ f) (f' ∘ g') ty1 ty3.
  Proof.
    move=> [Sub1 Sub1'] [??].
    split; eapply subtype_trans; [apply Sub1| | |apply Sub1']; done.
  Qed.

  (** Simple Type *)

  Lemma type_incl_simple_type {A B} (f: A → B) st1 st2 :
    st1.(st_size) = st2.(st_size) → st2.(ty_lft) ⊑ st1.(ty_lft) -∗
    □ (∀vπ d tid vl, st1.(st_own) (vπ,d) tid vl -∗ st2.(st_own) (f∘vπ,d) tid vl) -∗
    type_incl f st1 st2.
  Proof.
    move=> ?. iIntros "#Hl #Ho". iSplit; [done|]. iSplit; [done|].
    iSplit; iModIntro.
    - iIntros. by iApply "Ho".
    - iIntros (???) "/=". iDestruct 1 as (vl) "[Hf Hown]". iExists vl.
      iFrame "Hf". by iApply "Ho".
  Qed.

  Lemma subtype_simple_type {A B} E L (f: A → B) st1 st2 :
    (∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜st1.(st_size) = st2.(st_size)⌝ ∗ st2.(ty_lft) ⊑ st1.(ty_lft) ∗
      (∀vπ d tid vl, st1.(st_own) (vπ,d) tid vl -∗ st2.(st_own) (f∘vπ,d) tid vl))) →
    subtype E L f st1 st2.
  Proof.
    intros Hst. iIntros (?) "HL". iDestruct (Hst with "HL") as "#Hst".
    iIntros "!> #HE". iDestruct ("Hst" with "HE") as (?) "[??]".
    by iApply type_incl_simple_type.
  Qed.

  (** Plain Type *)

  Lemma type_incl_plain_type {A B} (f: A → B) pt1 pt2 :
    pt1.(pt_size) = pt2.(pt_size) → pt2.(ty_lft) ⊑ pt1.(ty_lft) -∗
    □ (∀v tid vl, pt1.(pt_own) v tid vl -∗ pt2.(pt_own) (f v) tid vl) -∗
    type_incl f pt1 pt2.
  Proof.
    move=> ?. iIntros "#Hl #Ho". iSplit; [done|]. iSplit; [done|].
    iSplit; iModIntro =>/=.
    - iDestruct 1 as (v ->) "?". iExists (f v). iSplit; [done|]. by iApply "Ho".
    - iIntros (???). iDestruct 1 as (vl) "[Hf Hown]". iExists vl.
      iFrame "Hf". iNext. iDestruct "Hown" as (v ->) "?". iExists (f v).
      iSplit; [done|]. by iApply "Ho".
  Qed.

  Lemma subtype_plain_type {A B} E L (f: A → B) pt1 pt2 :
    (∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜pt1.(pt_size) = pt2.(pt_size)⌝ ∗ pt2.(ty_lft) ⊑ pt1.(ty_lft) ∗
      (∀v tid vl, pt1.(pt_own) v tid vl -∗ pt2.(pt_own) (f v) tid vl))) →
    subtype E L f pt1 pt2.
  Proof.
    intros Hst. iIntros (?) "HL". iDestruct (Hst with "HL") as "#Hst".
    iIntros "!> #HE". iDestruct ("Hst" with "HE") as (?) "[??]".
    by iApply type_incl_plain_type.
  Qed.

End subtyping.

Section type_util.
  Context `{!typeG Σ}.

  Lemma heap_mapsto_ty_own {A} l (ty: _ A) vπd tid :
    l ↦∗: ty.(ty_own) vπd tid ⊣⊢
    ∃vl: vec val ty.(ty_size), l ↦∗ vl ∗ ty.(ty_own) vπd tid vl.
  Proof.
    iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[Hl Hown]".
      iDestruct (ty_size_eq with "Hown") as %<-.
      iExists (list_to_vec vl). rewrite vec_to_list_to_vec. iFrame.
    - iIntros "H". iDestruct "H" as (?) "[Hl Hown]". eauto with iFrame.
  Qed.
End type_util.

Global Hint Resolve ty_outlives_E_elctx_sat tyl_outlives_E_elctx_sat : lrust_typing.
Global Hint Resolve subtype_refl eqtype_refl : lrust_typing.
Global Hint Opaque subtype eqtype : lrust_typing.
