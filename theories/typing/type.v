From iris.algebra Require Import numbers list.
From iris.base_logic Require Export na_invariants.
From lrust.util Require Export basic update types.
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
  ty_own: (proph_asn → A) → nat → thread_id → list val → iProp Σ;
  ty_shr: (proph_asn → A) → nat → lft → thread_id → loc → iProp Σ;

  ty_shr_persistent vπ d κ tid l : Persistent (ty_shr vπ d κ tid l);

  ty_size_eq vπ d tid vl : ty_own vπ d tid vl -∗ ⌜length vl = ty_size⌝;
  ty_own_depth_mono d d' vπ tid vl :
    d ≤ d' → ty_own vπ d tid vl -∗ ty_own vπ d' tid vl;
  ty_shr_depth_mono d d' vπ κ tid l :
    d ≤ d' → ty_shr vπ d κ tid l -∗ ty_shr vπ d' κ tid l;
  ty_shr_lft_mono κ κ' vπ d tid l :
    κ' ⊑ κ -∗ ty_shr vπ d κ tid l -∗ ty_shr vπ d κ' tid l;

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
    κ ⊑ lft_intersect_list ty_lfts -∗ &{κ} (l ↦∗: ty_own vπ d tid) -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ty_shr vπ d κ tid l ∗ q.[κ];

  ty_own_proph E vπ d tid vl κ q : ↑lftN ⊆ E → lft_ctx -∗
    κ ⊑ lft_intersect_list ty_lfts -∗ ty_own vπ d tid vl -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξs q', ⌜vπ ./ ξs⌝ ∗
      q':+[ξs] ∗ (q':+[ξs] ={E}=∗ ty_own vπ d tid vl ∗ q.[κ]);
  ty_shr_proph E vπ d κ tid l κ' q : ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗
    κ' ⊑ lft_intersect_list ty_lfts -∗ ty_shr vπ d κ tid l -∗ q.[κ']
    ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξs q', ⌜vπ ./ ξs⌝ ∗
      q':+[ξs] ∗ (q':+[ξs] ={E}=∗ ty_shr vπ d κ tid l ∗ q.[κ']);
}.
Existing Instance ty_shr_persistent.
Instance: Params (@ty_size) 3 := {}.  Instance: Params (@ty_lfts) 3 := {}.
Instance: Params (@ty_E) 3 := {}.
Instance: Params (@ty_own) 3 := {}.  Instance: Params (@ty_shr) 3 := {}.
Arguments ty_size {_ _ _} _ / : simpl nomatch.
Arguments ty_lfts {_ _ _} _ / : simpl nomatch.
Arguments ty_E {_ _ _} _ / : simpl nomatch.
Arguments ty_own {_ _ _} _ _ _ _ / : simpl nomatch.
Arguments ty_shr {_ _ _} _ _ _ _ _ / : simpl nomatch.

Notation ty_lft ty := (lft_intersect_list ty.(ty_lfts)).

Notation typel := (hlist type).

Lemma ty_own_mt_depth_mono `{!typeG Σ} {A} (ty: _ A) d d' vπ tid l :
  d ≤ d' → l ↦∗: ty.(ty_own) vπ d tid -∗ l ↦∗: ty.(ty_own) vπ d' tid.
Proof.
  iIntros (Le) "[%vl[Mt ?]]". iExists vl. iFrame "Mt".
  iApply ty_own_depth_mono; by [apply Le|].
Qed.

Definition ty_outlives_E `{!typeG Σ} {A} (ty: _ A) (κ: lft) : elctx :=
  (λ α, κ ⊑ₑ α) <$> ty.(ty_lfts).

Lemma ty_outlives_E_elctx_sat `{!typeG Σ} {A} E L (ty: _ A) α β :
  ty_outlives_E ty β ⊆+ E → lctx_lft_incl E L α β →
  elctx_sat E L (ty_outlives_E ty α).
Proof.
  rewrite /ty_outlives_E. elim ty.(ty_lfts)=> [|?? IH]; [by solve_typing|].
  move=> Sub Incl. apply elctx_sat_lft_incl.
  - etrans; [by apply Incl|].
    eapply lctx_lft_incl_external, elem_of_submseteq, Sub. set_solver.
  - apply IH, Incl. etrans; [|by apply Sub]. by apply submseteq_cons.
Qed.

Lemma elctx_interp_ty_outlives_E `{!typeG Σ} {A} (ty: _ A) α :
  elctx_interp (ty_outlives_E ty α) ⊣⊢ α ⊑ ty.(ty_lft).
Proof.
  rewrite /ty_outlives_E /elctx_interp /elctx_elt_interp big_sepL_fmap /=.
  elim ty.(ty_lfts)=>/= [|κ l ->].
  { iSplit; iIntros "_"; [|done]. iApply lft_incl_static. } iSplit.
  - iIntros "#[??]". by iApply lft_incl_glb.
  - iIntros "#Incl". iSplit; (iApply lft_incl_trans; [iApply "Incl"|]);
      [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
Qed.

Notation tyl_lfts tyl := (concat ((λ _, ty_lfts) +c<$> tyl)).
Notation tyl_lft tyl := (lft_intersect_list (tyl_lfts tyl)).
Notation tyl_E tyl := (concat ((λ _, ty_E) +c<$> tyl)).
Notation tyl_outlives_E tyl κ := (concat ((λ _ ty, ty_outlives_E ty κ) +c<$> tyl)).

Lemma tyl_outlives_E_elctx_sat `{!typeG Σ} {As} E L (tyl: typel As) α β :
  tyl_outlives_E tyl β ⊆+ E → lctx_lft_incl E L α β →
  elctx_sat E L (tyl_outlives_E tyl α).
Proof.
  elim tyl; [solve_typing|]=> > IH Outlv Incl. apply elctx_sat_app.
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
  st_own: (proph_asn → A) → nat → thread_id → list val → iProp Σ;
  st_own_persistent vπ d tid vl : Persistent (st_own vπ d tid vl);
  st_size_eq vπ d tid vl : st_own vπ d tid vl -∗ ⌜length vl = st_size⌝;
  st_own_depth_mono d d' vπ tid vl :
    d ≤ d' → st_own vπ d tid vl -∗ st_own vπ d' tid vl;
  st_own_proph E vπ d tid vl κ q : ↑lftN ⊆ E → lft_ctx -∗
    κ ⊑ lft_intersect_list st_lfts -∗ st_own vπ d tid vl -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξs q', ⌜vπ ./ ξs⌝ ∗
      q':+[ξs] ∗ (q':+[ξs] ={E}=∗ st_own vπ d tid vl ∗ q.[κ]);
}.
Existing Instance st_own_persistent.
Instance: Params (@st_size) 3 := {}.  Instance: Params (@st_lfts) 3 := {}.
Instance: Params (@st_E) 3 := {}.  Instance: Params (@st_own) 3 := {}.
Arguments st_size {_ _ _} _ / : simpl nomatch.
Arguments st_lfts {_ _ _} _ / : simpl nomatch.
Arguments st_E {_ _ _} _ / : simpl nomatch.
Arguments st_own {_ _ _} _ _ _ _ / : simpl nomatch.

Program Definition ty_of_st `{!typeG Σ} {A} (st: simple_type A) : type A := {|
  ty_size := st.(st_size);  ty_lfts := st.(st_lfts);  ty_E := st.(st_E);
  ty_own := st.(st_own);
  ty_shr vπ d κ tid l := ∃vl, &frac{κ} (λ q, l ↦∗{q} vl) ∗ ▷ st.(st_own) vπ d tid vl;
|}%I.
Next Obligation. move=> >. apply st_size_eq. Qed.
Next Obligation. move=> >. by apply st_own_depth_mono. Qed.
Next Obligation.
  move=> > Le. iIntros "[%vl[Bor ?]]". iExists vl. iFrame "Bor".
  iApply st_own_depth_mono; by [apply Le|].
Qed.
Next Obligation.
  move=> >. iIntros "Incl [%vl[? Own]]". iExists vl. iFrame "Own".
  by iApply (frac_bor_shorten with "Incl").
Qed.
Next Obligation.
  move=> *. iIntros "#LFT ? Bor Tok".
  iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
  iMod (bor_sep with "LFT Bor") as "[Bor Own]"; [done|].
  iMod (bor_persistent with "LFT Own Tok") as "[? Tok]"; [done|].
  iMod (bor_fracture (λ q, _ ↦∗{q} vl)%I with "LFT Bor") as "?"; [done|]. iModIntro.
  iApply step_fupdN_intro; [done|]. iIntros "!>!>". iFrame "Tok". iExists vl. iFrame.
Qed.
Next Obligation. move=> >. apply st_own_proph. Qed.
Next Obligation.
  move=> *. iIntros "#LFT _ Incl [%vl[? Own]]". iIntros "Tok !>!>".
  iMod (st_own_proph with "LFT Incl Own Tok") as "Upd"; [done|].
  iModIntro. iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q' ?) "[Ptoks Upd]".
  iModIntro. iExists ξs, q'. iSplit; [done|]. iFrame "Ptoks". iIntros "Tok".
  iMod ("Upd" with "Tok") as "[?$]". iModIntro. iExists vl. iFrame.
Qed.

Coercion ty_of_st: simple_type >-> type.

(** Plain Type *)

Record plain_type `{!typeG Σ} A := {
  pt_size: nat;  pt_own: A → thread_id → list val → iProp Σ;
  pt_own_persistent v tid vl : Persistent (pt_own v tid vl);
  pt_size_eq v tid vl : pt_own v tid vl -∗ ⌜length vl = pt_size⌝;
}.
Existing Instance pt_own_persistent.
Instance: Params (@pt_size) 3 := {}.  Instance: Params (@pt_own) 3 := {}.
Arguments pt_size {_ _ _} _ / : simpl nomatch.
Arguments pt_own {_ _ _} _ _ _ _ / : simpl nomatch.

Program Definition st_of_pt `{!typeG Σ} {A} (pt: plain_type A) : simple_type A := {|
  st_size := pt.(pt_size);  st_lfts := [];  st_E := [];
  st_own vπ d tid vl := ∃v, ⌜vπ = const v⌝ ∗ pt.(pt_own) v tid vl;
|}%I.
Next Obligation. move=> >. iIntros "[%[_?]]". by iApply pt_size_eq. Qed.
Next Obligation. done. Qed.
Next Obligation.
  move=> * /=. iIntros "_ _[%[->?]]". iIntros "Ptok !>".
  iApply step_fupdN_intro; [done|]. iIntros "!>!>". iExists [], 1%Qp.
  do 2 (iSplit; [done|]). iIntros "_!>". iFrame "Ptok". iExists v. by iSplit.
Qed.

Coercion st_of_pt: plain_type >-> simple_type.

(** * OFE Structures on Types *)

Section ofe.
  Context `{!typeG Σ}.

  (**  Type *)

  Inductive type_equiv' {A} (ty ty': type A) : Prop := TypeEquiv:
    ty.(ty_size) = ty'.(ty_size) → ty.(ty_lfts) = ty'.(ty_lfts) → ty.(ty_E) = ty'.(ty_E) →
    (∀vπ d tid vs, ty.(ty_own) vπ d tid vs ≡ ty'.(ty_own) vπ d tid vs) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡ ty'.(ty_shr) vπ d κ tid l) →
    type_equiv' ty ty'.
  Global Instance type_equiv {A} : Equiv (type A) := type_equiv'.
  Inductive type_dist' {A} (n: nat) (ty ty': type A) : Prop := TypeDist:
    ty.(ty_size) = ty'.(ty_size) → ty.(ty_lfts) = ty'.(ty_lfts) → ty.(ty_E) = ty'.(ty_E) →
    (∀vπ d tid vs, ty.(ty_own) vπ d tid vs ≡{n}≡ ty'.(ty_own) vπ d tid vs) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{n}≡ ty'.(ty_shr) vπ d κ tid l) →
    type_dist' n ty ty'.
  Global Instance type_dist {A} : Dist (type A) := type_dist'.

  Definition type_unpack {A} (ty: type A)
    : prodO (prodO (prodO (prodO natO (listO lftO)) (listO (prodO lftO lftO)))
      ((proph_asn → A) -d> nat -d> thread_id -d> list val -d> iPropO Σ))
      ((proph_asn → A) -d> nat -d> lft -d> thread_id -d> loc -d> iPropO Σ) :=
    (ty.(ty_size), ty.(ty_lfts), ty.(ty_E), ty.(ty_own), ty.(ty_shr)).

  Definition type_ofe_mixin {A} : OfeMixin (type A).
  Proof.
    apply (iso_ofe_mixin type_unpack);
    (rewrite /type_unpack; split; [by move=> [->->->??]|]);
    move=> [[[[??]?]?]?]; simpl in *; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure typeO A : ofe := Ofe (type A) type_ofe_mixin.

  Global Instance typel_equiv {As} : Equiv (typel As) := @hlist_equiv type _ _.
  Global Instance typel_dist {As} : Dist (typel As) := @hlist_dist typeO _.

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

  Global Instance ty_own_ne {A} n:
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (@ty_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (@ty_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_ne {A} n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (@ty_shr _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (@ty_shr _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->??->. apply Eqv. Qed.

  (** Simple Type *)

  Inductive simple_type_equiv' {A} (st st': simple_type A) : Prop := SimpleTypeEquiv:
    st.(st_size) = st'.(st_size) → st.(st_lfts) = st'.(st_lfts) → st.(st_E) = st'.(st_E) →
    (∀vπ d tid vl, st.(st_own) vπ d tid vl ≡ st'.(st_own) vπ d tid vl) →
    simple_type_equiv' st st'.
  Global Instance simple_type_equiv {A} : Equiv (simple_type A) := simple_type_equiv'.
  Inductive simple_type_dist' {A} (n: nat) (st st': simple_type A) : Prop :=
    SimpleTypeDist:
    st.(st_size) = st'.(st_size) → st.(st_lfts) = st'.(st_lfts) → st.(st_E) = st'.(st_E) →
    (∀vπ d tid vl, st.(st_own) vπ d tid vl ≡{n}≡ (st'.(st_own) vπ d tid vl)) →
    simple_type_dist' n st st'.
  Global Instance simple_type_dist {A} : Dist (simple_type A) := simple_type_dist'.

  Definition simple_type_ofe_mixin {A} : OfeMixin (simple_type A).
  Proof.
    apply (iso_ofe_mixin ty_of_st); (split=> Eqv; split; try by apply Eqv);
    move=> > /=; f_equiv; f_equiv; by move: Eqv=> [_ _ _ ->].
  Qed.
  Canonical Structure simple_typeO A : ofe := Ofe (simple_type A) simple_type_ofe_mixin.

  Global Instance st_own_ne n {A} :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (@st_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance st_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (@st_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.

  Global Instance ty_of_st_ne {A} : NonExpansive (@ty_of_st _ _ A).
  Proof.
    move=> ??? Eqv. split; try apply Eqv. move=> > /=. do 2 f_equiv.
    by rewrite Eqv.
  Qed.
  Global Instance ty_of_st_proper {A} : Proper ((≡) ==> (≡)) (@ty_of_st _ _ A).
  Proof. apply (ne_proper _). Qed.

  (** Plain Type *)

  Inductive plain_type_equiv' {A} (pt pt': plain_type A) : Prop := PlainTypeEquiv:
    pt.(pt_size) = pt'.(pt_size) →
    (∀v tid vl, pt.(pt_own) v tid vl ≡ pt'.(pt_own) v tid vl) →
    plain_type_equiv' pt pt'.
  Global Instance plain_type_equiv {A} : Equiv (plain_type A) := plain_type_equiv'.
  Inductive plain_type_dist' {A} (n: nat) (pt pt': plain_type A) : Prop := PlainTypeDist:
    pt.(pt_size) = pt'.(pt_size) →
    (∀v tid vl, pt.(pt_own) v tid vl ≡{n}≡ (pt'.(pt_own) v tid vl)) →
    plain_type_dist' n pt pt'.
  Global Instance plain_type_dist {A} : Dist (plain_type A) := plain_type_dist'.

  Definition plain_type_unpack {A} (pt: plain_type A)
    : prodO natO (A -d> thread_id -d> list val -d> iPropO Σ) :=
    (pt.(pt_size), pt.(pt_own)).

  Definition plain_type_ofe_mixin {A} : OfeMixin (plain_type A).
  Proof.
    apply (iso_ofe_mixin plain_type_unpack);
    (rewrite /plain_type_unpack; split; [by move=> [->?]|]);
    move=> [??]; simpl in *; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure plain_typeO A : ofe := Ofe (plain_type A) plain_type_ofe_mixin.

  Global Instance pt_own_ne n {A} :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) (@pt_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.
  Global Instance pt_own_proper {A} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) (@pt_own _ _ A).
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.

  Global Instance st_of_pt_ne {A} : NonExpansive (@st_of_pt _ _ A).
  Proof.
    move=> ??? [? Eqv]. split=>//= *. do 3 f_equiv. by rewrite Eqv.
  Qed.
  Global Instance st_of_pt_proper {A} : Proper ((≡) ==> (≡)) (@st_of_pt _ _ A).
  Proof. apply (ne_proper _). Qed.

End ofe.

Ltac solve_ne_type :=
  constructor;
  solve_proper_core ltac:(fun _ => (
    (eapply ty_size_ne || eapply ty_lfts_ne || eapply ty_E_ne ||
     eapply ty_outlives_E_ne || eapply ty_own_ne || eapply ty_shr_ne); try reflexivity
  ) || f_equiv).

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

Global Instance type_lft_morphism_compose {A B C} (T: _ → _ C) (U: _ A → _ B) :
  TypeLftMorphism T → TypeLftMorphism U → TypeLftMorphism (T ∘ U).
Proof.
  case=> [αT βst ET HTα HTE|αT ET HTα HTE]; case=> [αU βsU EU HUα HUE|αU EU HUα HUE].
  - apply (type_lft_morphism_add _ (αT ⊓ αU) (βst ++ βsU)
                                 (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βst)))=>ty.
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
            (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βst)))=>ty.
    + iApply lft_equiv_trans. iApply HTα.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app /elctx_interp big_sepL_fmap.
      do 5 f_equiv. by apply lft_incl_equiv_proper_r.
  - apply (type_lft_morphism_const _ αT ET)=>//=.
  - apply (type_lft_morphism_const _ αT ET)=>//=.
Qed.

Lemma type_lft_morphism_lft_equiv_proper {A B} (T: _ A → _ B)
  {HT: TypeLftMorphism T} ty ty' :
  ty.(ty_lft) ≡ₗ ty'.(ty_lft) -∗ (T ty).(ty_lft) ≡ₗ (T ty').(ty_lft).
Proof.
  iIntros "#?". case HT=> [α βs E Hα HE|α E Hα HE].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|].
    iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|done].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_refl.
Qed.

Lemma type_lft_morphism_elctx_interp_proper {A B} (T: _ A → _ B)
  {HT: TypeLftMorphism T} ty ty' :
  elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
  elctx_interp (T ty).(ty_E) ≡ elctx_interp (T ty').(ty_E).
Proof.
  move=> EqvE EqvLft. move: HT=> [|] > ? HE; [|by rewrite !HE].
  rewrite !HE EqvE. do 5 f_equiv. by apply lft_incl_equiv_proper_r.
Qed.

End type_lft_morphism.

Class TypeNonExpansive `{!typeG Σ} {A B} (T: type A → type B) : Prop := {
  type_non_expansive_type_lft_morphism:> TypeLftMorphism T;
  type_non_expansive_ty_size ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (T ty).(ty_size) = (T ty').(ty_size);
  type_non_expansive_ty_own n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp (ty.(ty_E)) ≡ elctx_interp (ty'.(ty_E)) →
    (∀vπ d tid vl, ty.(ty_own) vπ d tid vl ≡{n}≡ ty'.(ty_own) vπ d tid vl) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{S n}≡ ty'.(ty_shr) vπ d κ tid l) →
    (∀vπ d tid vl, (T ty).(ty_own) vπ d tid vl ≡{n}≡ (T ty').(ty_own) vπ d tid vl);
  type_non_expansive_ty_shr n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp (ty.(ty_E)) ≡ elctx_interp (ty'.(ty_E)) →
    (∀vπ d tid vl,
      dist_later n (ty.(ty_own) vπ d tid vl) (ty'.(ty_own) vπ d tid vl)) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{n}≡ ty'.(ty_shr) vπ d κ tid l) →
    (∀vπ d κ tid l, (T ty).(ty_shr) vπ d κ tid l ≡{n}≡ (T ty').(ty_shr) vπ d κ tid l);
}.

Class TypeContractive `{!typeG Σ} {A B} (T: type A → type B) : Prop := {
  type_contractive_type_lft_morphism:> TypeLftMorphism T;
  type_contractive_ty_size ty ty' : (T ty).(ty_size) = (T ty').(ty_size);
  type_contractive_ty_own n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp (ty.(ty_E)) ≡ elctx_interp (ty'.(ty_E)) →
    (∀vπ d tid vl, dist_later n (ty.(ty_own) vπ d tid vl) (ty'.(ty_own) vπ d tid vl)) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{n}≡ ty'.(ty_shr) vπ d κ tid l) →
    (∀vπ d tid vl, (T ty).(ty_own) vπ d tid vl ≡{n}≡ (T ty').(ty_own) vπ d tid vl);
  type_contractive_ty_shr n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp (ty.(ty_E)) ≡ elctx_interp (ty'.(ty_E)) →
    (∀vπ d tid vl, match n with S (S n) =>
      ty.(ty_own) vπ d tid vl ≡{n}≡ ty'.(ty_own) vπ d tid vl | _ => True end) →
    (∀vπ d κ tid l, dist_later n (ty.(ty_shr) vπ d κ tid l) (ty'.(ty_shr) vπ d κ tid l)) →
    (∀vπ d κ tid l, (T ty).(ty_shr) vπ d κ tid l ≡{n}≡ (T ty').(ty_shr) vπ d κ tid l);
}.

Class ListTypeNonExpansive `{!typeG Σ} {A Bs} (T: type A → typel Bs) : Prop :=
  type_list_non_expansive: ∃Tl, T = (Tl +$.) ∧ HForall (λ _, TypeNonExpansive) Tl.

Class ListTypeContractive `{!typeG Σ} {A Bs} (T: type A → typel Bs) : Prop :=
  type_list_contractive: ∃Tl, T = (Tl +$.) ∧ HForall (λ _, TypeContractive) Tl.

Section type_contractive.
  Context `{!typeG Σ}.

  Global Instance type_contractive_type_ne {A B} (T: _ A → _ B) :
    TypeContractive T → TypeNonExpansive T.
  Proof.
    move=> HT. split; [by apply _|move=> *; by apply HT| |].
    - move=> *. apply HT=>// *; by [apply dist_dist_later|apply dist_S].
    - move=> n *. apply HT=>// *; [|by apply dist_dist_later].
      case n as [|[|]]=>//. simpl in *. by apply dist_S.
  Qed.

  Global Instance type_ne_ne_compose {A B C} (T: _ B → _ C) (T': _ A → _ B) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT, HT'| |];
    (move=> n *; apply HT; (try by apply HT');
      first (by iApply type_lft_morphism_lft_equiv_proper);
      first (apply type_lft_morphism_elctx_interp_proper=>//; apply _)).
    move=> *. case n as [|]=>//. by apply HT'.
  Qed.

  Global Instance type_contractive_compose_right {A B C} (T: _ B → _ C) (T': _ A → _ B) :
    TypeContractive T → TypeNonExpansive T' → TypeContractive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT| |];
    (move=> n *; apply HT; (try by apply HT');
      first (by iApply type_lft_morphism_lft_equiv_proper);
      first (apply type_lft_morphism_elctx_interp_proper=>//; apply _));
    move=> *; case n as [|[|]]=>//; by apply HT'.
  Qed.

  Global Instance type_contractive_compose_left {A B C} (T: _ B → _ C) (T': _ A → _) :
    TypeNonExpansive T → TypeContractive T' → TypeContractive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT, HT'| |];
    (move=> n *; apply HT; (try by apply HT');
      first (by iApply type_lft_morphism_lft_equiv_proper);
      first (apply type_lft_morphism_elctx_interp_proper=>//; apply _));
    move=> *; case n as [|]=>//; by apply HT'.
  Qed.

  Global Instance const_type_contractive {A B} (ty: _ A) : TypeContractive (λ _: _ B, ty).
  Proof. split; move=>// *. eright=> _; by [iApply lft_equiv_refl|]. Qed.

  Global Instance id_type_non_expansive {A} : TypeNonExpansive (id: _ A → _ A).
  Proof.
    split=>// *. apply (type_lft_morphism_add _ static [] [])=>/= ?.
    - rewrite left_id. apply lft_equiv_refl.
    - by rewrite /elctx_interp /= left_id right_id.
  Qed.

  Global Instance type_list_non_expansive_nil {A} : ListTypeNonExpansive (λ _: _ A, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.
  Global Instance type_list_contractive_nil {A} : ListTypeContractive (λ _: _ A, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.
  Global Instance type_list_non_expansive_cons {A B Bs} (T: _ A → _ B) (T': _ → _ Bs) :
    TypeNonExpansive T → ListTypeNonExpansive T' →
    ListTypeNonExpansive (λ ty, T ty +:: T' ty).
  Proof. move=> ? [Tl[->?]]. exists (T +:: Tl). split; by [|constructor]. Qed.
  Global Instance type_list_contractive_cons {A B Bs} (T: _ A → _ B) (T': _ → _ Bs) :
    TypeContractive T → ListTypeContractive T' →
    ListTypeContractive (λ ty, T ty +:: T' ty).
  Proof. move=> ? [Tl[->?]]. exists (T +:: Tl). split; by [|constructor]. Qed.

End type_contractive.

(** * Traits *)

Fixpoint shr_locsE (l: loc) (n: nat) : coPset :=
  match n with 0 => ∅ | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1) n end.

Class Copy `{!typeG Σ} {A} (ty: type A) := {
  copy_persistent vπ d tid vl : Persistent (ty.(ty_own) vπ d tid vl);
  copy_shr_acc vπ d κ tid E F l q :
    ↑lftN ∪ ↑shrN ⊆ E → shr_locsE l (ty.(ty_size) + 1) ⊆ F →
    lft_ctx -∗ ty.(ty_shr) vπ d κ tid l -∗ na_own tid F -∗ q.[κ] ={E}=∗ ∃q' vl,
      na_own tid (F ∖ shr_locsE l ty.(ty_size)) ∗
      l ↦∗{q'} vl ∗ ▷ty.(ty_own) vπ d tid vl ∗
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
  send_change_tid tid tid' vπ d vl :
    ty.(ty_own) vπ d tid vl ⊣⊢ ty.(ty_own) vπ d tid' vl.
Instance: Params (@Send) 3 := {}.

Class ListSend `{!typeG Σ} {As} (tyl: typel As) := list_send: HForall (λ _, Send) tyl.
Instance: Params (@ListSend) 3 := {}.
Global Instance list_send_nil `{!typeG Σ} : ListSend +[].
Proof. constructor. Qed.
Global Instance list_send_cons `{!typeG Σ} {A As} (ty: _ A) (tyl: _ As) :
  Send ty → ListSend tyl → ListSend (ty +:: tyl).
Proof. by constructor. Qed.

Class Sync `{!typeG Σ} {A} (ty: type A) :=
  sync_change_tid tid tid' vπ d κ l :
    ty.(ty_shr) vπ d κ tid l ⊣⊢ ty.(ty_shr) vπ d κ tid' l.
Instance: Params (@Sync) 3 := {}.

Class ListSync `{!typeG Σ} {As} (tyl: typel As) := list_sync: HForall (λ _, Sync) tyl.
Instance: Params (@ListSync) 3 := {}.
Global Instance list_sync_nil `{!typeG Σ} : ListSync +[].
Proof. constructor. Qed.
Global Instance list_sync_cons `{!typeG Σ} {A As} (ty: _ A) (tyl: _ As) :
  Sync ty → ListSync tyl → ListSync (ty +:: tyl).
Proof. by constructor. Qed.

Section traits.
  Context `{!typeG Σ}.

  (** Lemmas on Copy *)

  Lemma shr_locsE_shift l n m :
    shr_locsE l (n + m) = shr_locsE l n ∪ shr_locsE (l +ₗ n) m.
  Proof.
    move: l. elim n=> [|? IH]=> l /=.
    - rewrite shift_loc_0 /=. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add IH shift_loc_assoc. set_solver+.
  Qed.

  Lemma shr_locsE_disj l n m : shr_locsE l n ## shr_locsE (l +ₗ n) m.
  Proof.
    move: l. elim: n; [set_solver+|]=> n IHn l /=.
    rewrite -Nat.add_1_l Nat2Z.inj_add. apply disjoint_union_l.
    split; [|rewrite -shift_loc_assoc; by exact: IHn].
    clear IHn. move: n. elim m; [set_solver+|]=> ? IHm n.
    rewrite/= shift_loc_assoc. apply disjoint_union_r. split.
    - apply ndot_ne_disjoint. case l=> * [=]. lia.
    - rewrite -Z.add_assoc. move: (IHm (n + 1)). by rewrite Nat2Z.inj_add.
  Qed.

  Lemma shr_locsE_shrN l n : shr_locsE l n ⊆ ↑shrN.
  Proof.
    move: l. elim n; [set_solver+|]=>/= *. apply union_least; [solve_ndisj|done].
  Qed.

  Lemma shr_locsE_subseteq l n m : n ≤ m → shr_locsE l n ⊆ shr_locsE l m.
  Proof.
    elim; [done|]=> > ? In. etrans; [by apply In|].
    rewrite -Nat.add_1_r shr_locsE_shift. set_solver+.
  Qed.

  Lemma shr_locsE_split_tok l n m tid :
    na_own tid (shr_locsE l (n + m)) ⊣⊢
    na_own tid (shr_locsE l n) ∗ na_own tid (shr_locsE (l +ₗ n) m).
  Proof. rewrite shr_locsE_shift na_own_union; by [|apply shr_locsE_disj]. Qed.

  Global Instance copy_equiv {A} : Proper ((≡) ==> impl) (@Copy _ _ A).
  Proof.
    move=> ty ty' [EqSz _ _ EqOwn EqShr] ?. split=> >.
    - rewrite -EqOwn. apply _.
    - rewrite -EqSz -EqShr. setoid_rewrite <-EqOwn. apply copy_shr_acc.
  Qed.

  Global Program Instance simple_type_copy {A} (st: simple_type A) : Copy st.
  Next Obligation.
    move=> *. iIntros "#LFT #[%vl[Bor Own]] Na Tok".
    iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [solve_ndisj|].
    iMod (frac_bor_acc with "LFT Bor Tok") as (q) "[>Mt Close]"; [solve_ndisj|].
    iModIntro. iExists q, vl. iFrame "Mt Own". iIntros "Na".
    iDestruct ("ToNa" with "Na") as "$". iIntros "?". by iApply "Close".
  Qed.

  (** Lemmas on Send and Sync *)

  Global Instance send_equiv {A} : Proper (equiv ==> impl) (@Send _ _ A).
  Proof. move=> ?? [_ _ _ Eqv _] ?. rewrite /Send=> *. by rewrite -!Eqv. Qed.

  Global Instance sync_equiv {A} : Proper (equiv ==> impl) (@Sync _ _ A).
  Proof. move=> ?? [_ _ _ _ Eqv] ?. rewrite /Sync=> *. by rewrite -!Eqv. Qed.

  Global Instance simple_type_sync {A} (st: simple_type A) : Send st → Sync st.
  Proof. move=> Eq >/=. by setoid_rewrite Eq at 1. Qed.

End traits.

(** * Subtyping *)

Definition type_incl `{!typeG Σ} {A B} (f: A → B) (ty: type A) (ty': type B) : iProp Σ :=
  ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ (ty'.(ty_lft) ⊑ ty.(ty_lft)) ∗
  (□ ∀vπ d tid vl, ty.(ty_own) vπ d tid vl -∗ ty'.(ty_own) (f ∘ vπ) d tid vl) ∗
  (□ ∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l -∗ ty'.(ty_shr) (f ∘ vπ) d κ tid l).
Instance: Params (@type_incl) 4 := {}.

Definition subtype `{!typeG Σ} {A B} E L (f: A → B) (ty: type A) (ty': type B) : Prop :=
  ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗ type_incl f ty ty').
Instance: Params (@subtype) 6 := {}.

Definition eqtype `{!typeG Σ} {A B} E L (f: A → B) (g: B → A) (ty: type A) (ty': type B)
  : Prop := subtype E L f ty ty' ∧ subtype E L g ty' ty.
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

  Global Instance type_incl_persistent {A B} (f: A → B) ty ty' :
    Persistent (type_incl f ty ty') := _.

  Lemma type_incl_refl {A} (ty: _ A) : ⊢ type_incl id ty ty.
  Proof.
    iSplit; [done|]. iSplit; [by iApply lft_incl_refl|]. iSplit; iModIntro; by iIntros.
  Qed.

  Lemma type_incl_trans {A B C} (f: A → B) (g: B → C) ty ty' ty'' :
    type_incl f ty ty' -∗ type_incl g ty' ty'' -∗ type_incl (g ∘ f) ty ty''.
  Proof.
    iIntros "[%[#InLft[#InOwn #InShr]]] [%[#InLft'[#InOwn' #InShr']]]".
    iSplit. { iPureIntro. by etrans. } iSplit; [|iSplit].
    - iApply lft_incl_trans; [iApply "InLft'"|iApply "InLft"].
    - iIntros "!>*?". iApply "InOwn'". by iApply "InOwn".
    - iIntros "!>*?". iApply "InShr'". by iApply "InShr".
  Qed.

  Global Instance subtype_refl {E L A} : Reflexive (subtype E L (@id A)).
  Proof. move=> ??. iIntros "_!>_". iApply type_incl_refl. Qed.

  Lemma subtype_trans {A B C} E L (f: A → B) (g: B → C) ty ty' ty'' :
    subtype E L f ty ty' → subtype E L g ty' ty'' → subtype E L (g ∘ f) ty ty''.
  Proof.
    move=> Sub Sub'. iIntros (?) "L". iDestruct (Sub with "L") as "#Incl".
    iDestruct (Sub' with "L") as "#Incl'". iIntros "!> #E".
    iApply type_incl_trans; by [iApply "Incl"|iApply "Incl'"].
  Qed.

  Lemma subtype_weaken {A B} E E' L L' (f: A → B) ty ty' :
    E ⊆+ E' → L ⊆+ L' → subtype E L f ty ty' → subtype E' L' f ty ty'.
  Proof.
    move=> ?? Sub. iIntros (?) "L".
    iDestruct (Sub with "[L]") as "#Incl"; [by iApply big_sepL_submseteq|].
    iIntros "!> #E". iApply "Incl". by iApply big_sepL_submseteq.
  Qed.

  Definition subtypel {As Bs} E L (tyl: typel As) (tyl': typel Bs)
    (fl: plist2 (→) As Bs) : Prop :=
    HForallZip (λ _ _ ty ty' f, subtype E L f ty ty') tyl tyl' fl.
  Definition eqtypel {As Bs} E L (tyl: typel As) (tyl': typel Bs)
    (fl: plist2 (→) As Bs) (gl: plist2 (→) Bs As) : Prop :=
    HForallZip (λ _ _ ty ty' '(f, g), eqtype E L f g ty ty') tyl tyl'
      (p2zip fl (p2flip gl)).

  Lemma subtypel_llctx_nth {C As Bs} E L (ty: _ C) (tyl: _ As) (tyl': _ Bs) fl qL :
    subtypel E L tyl tyl' fl → llctx_interp L qL -∗ □ (elctx_interp E -∗
      ∀i, type_incl (p2nth id fl i) (hnth ty tyl i) (hnth ty tyl' i)).
  Proof.
    elim=>/= [|>Sub _ IH]. { iIntros "_!>_" (?). iApply type_incl_refl. } iIntros "L".
    iDestruct (Sub with "L") as "#Sub". iDestruct (IH with "L") as "#IH".
    iIntros "!> #E" (i). iDestruct ("Sub" with "E") as "Sub'".
    iDestruct ("IH" with "E") as "IH'". by case i=> [|j].
  Qed.

  Lemma subtypel_llctx_bigsep {As Bs} E L (tyl: _ As) (tyl': _ Bs) fl qL :
    subtypel E L tyl tyl' fl → llctx_interp L qL -∗ □ (elctx_interp E -∗
      [∗ hlist] ty; ty';- f ∈ tyl; tyl';- fl, type_incl f ty ty').
  Proof.
    elim=>/= [|>Sub _ IH]; [by iIntros "_!>_"|]. iIntros "L".
    iDestruct (Sub with "L") as "#Sub". iDestruct (IH with "L") as "#IH".
    iIntros "!> #E". iDestruct ("Sub" with "E") as "$". iDestruct ("IH" with "E") as "$".
  Qed.

  (** Type Equivalence *)

  Lemma equiv_subtype {A} E L (ty ty': _ A) : ty ≡ ty' → subtype E L id ty ty'.
  Proof.
    move=> Eqv ?. iIntros "_!>_". iSplit. { iPureIntro. apply Eqv. }
    iSplit. { rewrite Eqv. iApply lft_incl_refl. }
    iSplit; iIntros "!>*"; rewrite Eqv; iIntros "$".
  Qed.

  Lemma eqtype_unfold {A B} E L f g `{@Iso A B f g} ty ty' :
    eqtype E L f g ty ty' ↔
    ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ ty.(ty_lft) ≡ₗ ty'.(ty_lft) ∗
      (□ ∀vπ d tid vl, ty.(ty_own) vπ d tid vl ↔ ty'.(ty_own) (f ∘ vπ) d tid vl) ∗
      (□ ∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ↔ ty'.(ty_shr) (f ∘ vπ) d κ tid l)).
  Proof. split.
    - iIntros ([Sub Sub'] ?) "L". iDestruct (Sub with "L") as "#Sub".
      iDestruct (Sub' with "L") as "#Sub'". iIntros "!> #E".
      iDestruct ("Sub" with "E") as "[$[$[InOwn InShr]]]".
      iDestruct ("Sub'" with "E") as "[_[$[InOwn' InShr']]]".
      iSplit; iIntros "!>*"; iSplit; iIntros "Res";
      [by iApply "InOwn"| |by iApply "InShr"|];
      [iDestruct ("InOwn'" with "Res") as "?"|iDestruct ("InShr'" with "Res") as "?"];
      by rewrite compose_assoc semi_iso.
    - move=> Eqt. split; iIntros (?) "L";
      iDestruct (Eqt with "L") as "#Eqt"; iIntros "!> #E";
      iDestruct ("Eqt" with "E") as (?) "[[??][EqOwn EqShr]]";
      do 2 (iSplit; [done|]); iSplit; iIntros "!>* X";
      [by iApply "EqOwn"|by iApply "EqShr"| |]; [iApply "EqOwn"|iApply "EqShr"];
      by rewrite compose_assoc semi_iso.
  Qed.

  Lemma eqtype_id_unfold {A} E L (ty ty': _ A) :
    eqtype E L id id ty ty' ↔
    ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ ty.(ty_lft) ≡ₗ ty'.(ty_lft) ∗
      (□ ∀vπ d tid vl, ty.(ty_own) vπ d tid vl ↔ ty'.(ty_own) vπ d tid vl) ∗
      (□ ∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ↔ ty'.(ty_shr) vπ d κ tid l)).
  Proof. by rewrite eqtype_unfold. Qed.

  Global Instance eqtype_refl {E L A} : Reflexive (eqtype E L (@id A) id).
  Proof. done. Qed.

  Lemma equiv_eqtype {A} E L (ty ty': _ A) : ty ≡ ty' → eqtype E L id id ty ty'.
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

  Lemma eqtype_trans {A B C} E L (f: A → B) f' (g: B → C) g' ty ty' ty'' :
    eqtype E L f f' ty ty' → eqtype E L g g' ty' ty'' →
    eqtype E L (g ∘ f) (f' ∘ g') ty ty''.
  Proof.
    move=> [Sub1 Sub1'] [??].
    split; eapply subtype_trans; [apply Sub1| | |apply Sub1']; done.
  Qed.

  (** Simple Type *)

  Lemma type_incl_simple_type {A B} (f: A → B) st st' :
    st.(st_size) = st'.(st_size) → st'.(ty_lft) ⊑ st.(ty_lft) -∗
    □ (∀vπ d tid vl, st.(st_own) vπ d tid vl -∗ st'.(st_own) (f ∘ vπ) d tid vl) -∗
    type_incl f st st'.
  Proof.
    move=> ?. iIntros "#InLft #InOwn". do 2 (iSplit; [done|]).
    iSplit; iIntros "!>*"; [by iApply "InOwn"|]. iIntros "[%vl[Bor Own]]".
    iExists vl. iFrame "Bor". by iApply "InOwn".
  Qed.

  Lemma subtype_simple_type {A B} E L (f: A → B) st st' :
    (∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜st.(st_size) = st'.(st_size)⌝ ∗ st'.(ty_lft) ⊑ st.(ty_lft) ∗
      (∀vπ d tid vl, st.(st_own) vπ d tid vl -∗ st'.(st_own) (f ∘ vπ) d tid vl))) →
    subtype E L f st st'.
  Proof.
    move=> Sub. iIntros (?) "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iDestruct ("Incl" with "E") as (?) "[??]".
    by iApply type_incl_simple_type.
  Qed.

  (** Plain Type *)

  Lemma type_incl_plain_type {A B} (f: A → B) pt pt' :
    pt.(pt_size) = pt'.(pt_size) → pt'.(ty_lft) ⊑ pt.(ty_lft) -∗
    □ (∀v tid vl, pt.(pt_own) v tid vl -∗ pt'.(pt_own) (f v) tid vl) -∗
    type_incl f pt pt'.
  Proof.
    move=> ?. iIntros "#InLft #InOwn". do 2 (iSplit; [done|]). iSplit; iIntros "!>*/=".
    - iIntros "[%v[->?]]". iExists (f v). iSplit; [done|]. by iApply "InOwn".
    - iIntros "[%vl[Bor Own]]". iExists vl. iFrame "Bor". iNext.
      iDestruct "Own" as (v->) "?". iExists (f v). iSplit; [done|]. by iApply "InOwn".
  Qed.

  Lemma subtype_plain_type {A B} E L (f: A → B) pt pt' :
    (∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜pt.(pt_size) = pt'.(pt_size)⌝ ∗ pt'.(ty_lft) ⊑ pt.(ty_lft) ∗
      (∀v tid vl, pt.(pt_own) v tid vl -∗ pt'.(pt_own) (f v) tid vl))) →
    subtype E L f pt pt'.
  Proof.
    move=> Sub. iIntros (?) "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> #E". iDestruct ("Sub" with "E") as (?) "[??]".
    by iApply type_incl_plain_type.
  Qed.

End subtyping.

(** * Utility *)

Section type_util.
  Context `{!typeG Σ}.

  Lemma heap_mapsto_ty_own {A} l (ty: _ A) vπ d tid :
    l ↦∗: ty.(ty_own) vπ d tid ⊣⊢
    ∃vl: vec val ty.(ty_size), l ↦∗ vl ∗ ty.(ty_own) vπ d tid vl.
  Proof.
    iSplit; iIntros "[%vl[? Own]]"; [|iExists vl; by iFrame].
    iDestruct (ty_size_eq with "Own") as %<-. iExists (list_to_vec vl).
    rewrite vec_to_list_to_vec. iFrame.
  Qed.

  Definition by_succ (d: nat) (Φ: nat → iProp Σ) : iProp Σ :=
    match d with S d' => Φ d' | _ => False end.
  Lemma by_succ_ex d Φ : by_succ d Φ ⊣⊢ ∃d', ⌜d = S d'⌝ ∗ Φ d'.
  Proof.
    iSplit; [|by iIntros "[%[->$]]"]. iIntros. case d; [done|]=> d'.
    iExists d'. by iFrame.
  Qed.
  Global Instance by_succ_proper :
    Proper ((=) ==> pointwise_relation _ (⊣⊢) ==> (⊣⊢)) by_succ.
  Proof. move=> ??->?? Eq. rewrite !by_succ_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_succ_ne n :
    Proper ((=) ==> pointwise_relation _ (dist n) ==> (dist n)) by_succ.
  Proof. move=> ??->?? Eq. rewrite !by_succ_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_succ_mono :
    Proper ((=) ==> pointwise_relation _ (⊢) ==> (⊢)) by_succ.
  Proof. move=> ??->?? In. rewrite !by_succ_ex. by setoid_rewrite In. Qed.
  Global Instance by_succ_persistent d Φ :
    (∀d', Persistent (Φ d')) → Persistent (by_succ d Φ).
  Proof. case d; apply _. Qed.

  Definition by_just_loc (vl: list val) (Φ: loc → iProp Σ) : iProp Σ :=
    match vl with [ #(LitLoc l)] => Φ l | _ => False end.
  Lemma by_just_loc_ex vl Φ : by_just_loc vl Φ ⊣⊢ ∃l: loc, ⌜vl = [ #l]⌝ ∗ Φ l.
  Proof.
    iSplit; [|by iIntros "[%[->$]]"]. iIntros. case vl=> [|[[|l|?]|?][|??]]//.
    iExists l. by iFrame.
  Qed.
  Global Instance by_just_loc_proper :
    Proper ((=) ==> pointwise_relation _ (⊣⊢) ==> (⊣⊢)) by_just_loc.
  Proof. move=> ??->?? Eq. rewrite !by_just_loc_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_just_loc_ne n :
    Proper ((=) ==> pointwise_relation _ (dist n) ==> (dist n)) by_just_loc.
  Proof. move=> ??->?? Eq. rewrite !by_just_loc_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_just_loc_mono :
    Proper ((=) ==> pointwise_relation _ (⊢) ==> (⊢)) by_just_loc.
  Proof. move=> ??->?? In. rewrite !by_just_loc_ex. by setoid_rewrite In. Qed.
  Global Instance by_just_loc_persistent vl Φ :
    (∀l, Persistent (Φ l)) → Persistent (by_just_loc vl Φ).
  Proof. rewrite by_just_loc_ex. apply _. Qed.

End type_util.

Notation "[S d' := d ] P" := (by_succ d (λ d', P)) (at level 200,
  right associativity, format "[S  d'  :=  d ]  P") : bi_scope.

Notation "[loc[ l ] := vl ] P" := (by_just_loc vl (λ l, P)) (at level 200,
  right associativity, format "[loc[ l ]  :=  vl ]  P") : bi_scope.

Global Hint Resolve ty_outlives_E_elctx_sat tyl_outlives_E_elctx_sat : lrust_typing.
Global Hint Resolve subtype_refl eqtype_refl : lrust_typing.
Global Hint Opaque subtype eqtype : lrust_typing.
