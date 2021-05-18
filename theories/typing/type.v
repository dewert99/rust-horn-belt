From iris.algebra Require Import numbers list.
From iris.base_logic Require Export na_invariants.
From lrust.util Require Export basic vector update fancy_lists.
From lrust.prophecy Require Export prophecy.
From lrust.lifetime Require Export frac_borrow.
From lrust.lang Require Export proofmode notation.
From lrust.typing Require Export base lft_contexts uniq_cmra.
Set Default Proof Using "Type".
Open Scope nat_scope.

Implicit Type (𝔄 𝔅 ℭ: syn_type) (𝔄l 𝔅l: syn_typel).

Class typeG Σ := TypeG {
  type_lrustG:> lrustG Σ;  type_prophG:> prophG Σ;  type_uniqG:> uniqG Σ;
  type_lftG:> lftG Σ;  type_na_invG:> na_invG Σ;  type_frac_borG:> frac_borG Σ;
}.

Definition lrustN := nroot .@ "lrust".
Definition shrN := lrustN .@ "shr".

Definition thread_id := na_inv_pool_name.

(** * Type *)

Record type `{!typeG Σ} 𝔄 := {
  ty_size: nat;  ty_lfts: list lft;  ty_E: elctx;
  ty_own: proph 𝔄 → nat → thread_id → list val → iProp Σ;
  ty_shr: proph 𝔄 → nat → lft → thread_id → loc → iProp Σ;

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
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜vπ ./ ξl⌝ ∗
      q':+[ξl] ∗ (q':+[ξl] ={E}=∗ ty_own vπ d tid vl ∗ q.[κ]);
  ty_shr_proph E vπ d κ tid l κ' q : ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗
    κ' ⊑ lft_intersect_list ty_lfts -∗ ty_shr vπ d κ tid l -∗ q.[κ']
    ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜vπ ./ ξl⌝ ∗
      q':+[ξl] ∗ (q':+[ξl] ={E}=∗ ty_shr vπ d κ tid l ∗ q.[κ']);
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
Arguments ty_size_eq {_ _ _}. Arguments ty_own_depth_mono {_ _ _}.
Arguments ty_shr_depth_mono {_ _ _}. Arguments ty_shr_lft_mono {_ _ _}.
Arguments ty_share {_ _ _}.
Arguments ty_own_proph {_ _ _}. Arguments ty_shr_proph {_ _ _}.

Notation ty_lft ty := (lft_intersect_list ty.(ty_lfts)).

Notation typel := (hlist type).

Lemma ty_own_mt_depth_mono `{!typeG Σ} {𝔄} (ty: _ 𝔄) d d' vπ tid l :
  d ≤ d' → l ↦∗: ty.(ty_own) vπ d tid -∗ l ↦∗: ty.(ty_own) vπ d' tid.
Proof.
  iIntros (Le) "[%vl[↦ ?]]". iExists vl. iFrame "↦".
  iApply ty_own_depth_mono; by [apply Le|].
Qed.

Definition ty_outlv_E `{!typeG Σ} {𝔄} (ty: _ 𝔄) (κ: lft) : elctx :=
  (λ α, κ ⊑ₑ α) <$> ty.(ty_lfts).

Lemma ty_outlv_E_elctx_sat `{!typeG Σ} {𝔄} E L (ty: _ 𝔄) α β :
  ty_outlv_E ty β ⊆+ E → lctx_lft_incl E L α β →
  elctx_sat E L (ty_outlv_E ty α).
Proof.
  rewrite /ty_outlv_E. elim ty.(ty_lfts)=> [|?? IH]; [by solve_typing|].
  move=> Sub Incl. apply elctx_sat_lft_incl.
  - etrans; [by apply Incl|].
    eapply lctx_lft_incl_external, elem_of_submseteq, Sub. set_solver.
  - apply IH, Incl. etrans; [|by apply Sub]. by apply submseteq_cons.
Qed.

Lemma elctx_interp_ty_outlv_E `{!typeG Σ} {𝔄} (ty: _ 𝔄) α :
  elctx_interp (ty_outlv_E ty α) ⊣⊢ α ⊑ ty.(ty_lft).
Proof.
  rewrite /ty_outlv_E /elctx_elt_interp big_sepL_fmap /=.
  elim ty.(ty_lfts)=>/= [|κ l ->].
  { iSplit; iIntros "_"; [|done]. iApply lft_incl_static. } iSplit.
  - iIntros "#[??]". by iApply lft_incl_glb.
  - iIntros "#Incl". iSplit; (iApply lft_incl_trans; [iApply "Incl"|]);
      [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
Qed.

Definition tyl_lfts `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) : list lft :=
  concat ((λ _, ty_lfts) +c<$> tyl).
Definition tyl_lft `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) : lft :=
  lft_intersect_list (tyl_lfts tyl).
Definition tyl_E `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) : elctx :=
  concat ((λ _, ty_E) +c<$> tyl).
Definition tyl_outlv_E `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) (κ: lft) : elctx :=
  concat ((λ _ ty, ty_outlv_E ty κ) +c<$> tyl).

Lemma tyl_outlv_E_elctx_sat `{!typeG Σ} {𝔄l} E L (tyl: typel 𝔄l) α β :
  tyl_outlv_E tyl β ⊆+ E → lctx_lft_incl E L α β →
  elctx_sat E L (tyl_outlv_E tyl α).
Proof.
  elim tyl; [solve_typing|]=> > IH Outlv Incl. apply elctx_sat_app.
  - eapply ty_outlv_E_elctx_sat; [|by apply Incl]. etrans; [|by apply Outlv].
    by apply submseteq_inserts_r.
  - apply IH; [|done]. etrans; [|by apply Outlv]. by apply submseteq_inserts_l.
Qed.

Declare Scope lrust_type_scope.
Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(** Simple Type *)

Record simple_type `{!typeG Σ} 𝔄 := {
  st_size: nat;  st_lfts: list lft;  st_E: elctx;
  st_own: proph 𝔄 → nat → thread_id → list val → iProp Σ;
  st_own_persistent vπ d tid vl : Persistent (st_own vπ d tid vl);
  st_size_eq vπ d tid vl : st_own vπ d tid vl -∗ ⌜length vl = st_size⌝;
  st_own_depth_mono d d' vπ tid vl :
    d ≤ d' → st_own vπ d tid vl -∗ st_own vπ d' tid vl;
  st_own_proph E vπ d tid vl κ q : ↑lftN ⊆ E → lft_ctx -∗
    κ ⊑ lft_intersect_list st_lfts -∗ st_own vπ d tid vl -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜vπ ./ ξl⌝ ∗
      q':+[ξl] ∗ (q':+[ξl] ={E}=∗ st_own vπ d tid vl ∗ q.[κ]);
}.
Existing Instance st_own_persistent.
Instance: Params (@st_size) 3 := {}.  Instance: Params (@st_lfts) 3 := {}.
Instance: Params (@st_E) 3 := {}.  Instance: Params (@st_own) 3 := {}.
Arguments st_size {_ _ _} _ / : simpl nomatch.
Arguments st_lfts {_ _ _} _ / : simpl nomatch.
Arguments st_E {_ _ _} _ / : simpl nomatch.
Arguments st_own {_ _ _} _ _ _ _ / : simpl nomatch.

Program Definition ty_of_st `{!typeG Σ} {𝔄} (st: simple_type 𝔄) : type 𝔄 := {|
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
  move=> >. iIntros "Incl [%vl[? st]]". iExists vl. iFrame "st".
  by iApply (frac_bor_shorten with "Incl").
Qed.
Next Obligation.
  move=> *. iIntros "#LFT ? Bor κ".
  iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
  iMod (bor_sep with "LFT Bor") as "[Bor st]"; [done|].
  iMod (bor_persistent with "LFT st κ") as "[? $]"; [done|].
  iMod (bor_fracture (λ q, _ ↦∗{q} vl)%I with "LFT Bor") as "?"; [done|].
  iApply step_fupdN_full_intro. iIntros "!>!>". iExists vl. iFrame.
Qed.
Next Obligation. move=> >. apply st_own_proph. Qed.
Next Obligation.
  move=> *. iIntros "#LFT _ Incl [%vl[? st]]". iIntros "κ !>!>".
  iMod (st_own_proph with "LFT Incl st κ") as "Upd"; [done|].
  iModIntro. iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q' ?) "[ξl Tost]".
  iModIntro. iExists ξl, q'. iSplit; [done|]. iFrame "ξl". iIntros "κ".
  iMod ("Tost" with "κ") as "[?$]". iModIntro. iExists vl. iFrame.
Qed.

Coercion ty_of_st: simple_type >-> type.

(** Plain Type *)

Record plain_type `{!typeG Σ} 𝔄 := {
  pt_size: nat;  pt_own: 𝔄 → thread_id → list val → iProp Σ;
  pt_own_persistent v tid vl : Persistent (pt_own v tid vl);
  pt_size_eq v tid vl : pt_own v tid vl -∗ ⌜length vl = pt_size⌝;
}.
Existing Instance pt_own_persistent.
Instance: Params (@pt_size) 3 := {}.  Instance: Params (@pt_own) 3 := {}.
Arguments pt_size {_ _ _} _ / : simpl nomatch.
Arguments pt_own {_ _ _} _ _ _ _ / : simpl nomatch.

Program Definition st_of_pt `{!typeG Σ} {𝔄} (pt: plain_type 𝔄) : simple_type 𝔄 := {|
  st_size := pt.(pt_size);  st_lfts := [];  st_E := [];
  st_own vπ d tid vl := ∃v, ⌜vπ = const v⌝ ∗ pt.(pt_own) v tid vl;
|}%I.
Next Obligation. move=> >. iIntros "[%[_?]]". by iApply pt_size_eq. Qed.
Next Obligation. done. Qed.
Next Obligation.
  move=> * /=. iIntros "_ _[%[->?]]". iIntros "$ !>".
  iApply step_fupdN_full_intro. iModIntro. iExists [], 1%Qp.
  do 2 (iSplit; [done|]). iIntros "_!>". iExists v. by iSplit.
Qed.

Coercion st_of_pt: plain_type >-> simple_type.

(** * OFE Structures on Types *)

Section ofe.
  Context `{!typeG Σ}.

  (**  Type *)

  Inductive type_equiv' {𝔄} (ty ty': type 𝔄) : Prop := TypeEquiv:
    ty.(ty_size) = ty'.(ty_size) → ty.(ty_lfts) = ty'.(ty_lfts) → ty.(ty_E) = ty'.(ty_E) →
    (∀vπ d tid vs, ty.(ty_own) vπ d tid vs ≡ ty'.(ty_own) vπ d tid vs) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡ ty'.(ty_shr) vπ d κ tid l) →
    type_equiv' ty ty'.
  Global Instance type_equiv {𝔄} : Equiv (type 𝔄) := type_equiv'.
  Inductive type_dist' {𝔄} (n: nat) (ty ty': type 𝔄) : Prop := TypeDist:
    ty.(ty_size) = ty'.(ty_size) → ty.(ty_lfts) = ty'.(ty_lfts) → ty.(ty_E) = ty'.(ty_E) →
    (∀vπ d tid vs, ty.(ty_own) vπ d tid vs ≡{n}≡ ty'.(ty_own) vπ d tid vs) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{n}≡ ty'.(ty_shr) vπ d κ tid l) →
    type_dist' n ty ty'.
  Global Instance type_dist {𝔄} : Dist (type 𝔄) := type_dist'.

  Definition type_unpack {𝔄} (ty: type 𝔄)
    : prodO (prodO (prodO (prodO natO (listO lftO)) (listO (prodO lftO lftO)))
      (proph 𝔄 -d> nat -d> thread_id -d> list val -d> iPropO Σ))
      (proph 𝔄 -d> nat -d> lft -d> thread_id -d> loc -d> iPropO Σ) :=
    (ty.(ty_size), ty.(ty_lfts), ty.(ty_E), ty.(ty_own), ty.(ty_shr)).

  Definition type_ofe_mixin {𝔄} : OfeMixin (type 𝔄).
  Proof.
    apply (iso_ofe_mixin type_unpack);
    (rewrite /type_unpack; split; [by move=> [->->->??]|]);
    move=> [[[[??]?]?]?]; simpl in *; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure typeO 𝔄 : ofe := Ofe (type 𝔄) type_ofe_mixin.

  Global Instance typel_equiv {𝔄l} : Equiv (typel 𝔄l) := ofe_equiv (hlistO typeO _).
  Global Instance typel_dist {𝔄l} : Dist (typel 𝔄l) := ofe_dist (hlistO typeO _).

  Global Instance ty_size_ne {𝔄} n : Proper ((≡{n}@{_ 𝔄}≡) ==> (=)) ty_size.
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_size_proper {𝔄} : Proper ((≡@{_ 𝔄}) ==> (=)) ty_size.
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_lfts_ne {𝔄} n : Proper ((≡{n}@{_ 𝔄}≡) ==> (=)) ty_lfts.
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_lfts_proper {𝔄} : Proper ((≡@{_ 𝔄}) ==> (=)) ty_lfts.
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_E_ne {𝔄} n : Proper ((≡{n}@{_ 𝔄}≡) ==> (=)) ty_E.
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_E_proper {𝔄} : Proper ((≡@{_ 𝔄}) ==> (=)) ty_E.
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_outlv_E_ne {𝔄} n :
    Proper ((≡{n}@{_ 𝔄}≡) ==> (=) ==> (=)) ty_outlv_E.
  Proof. rewrite /ty_outlv_E. by move=> ?? [_ -> _ _ _]. Qed.
  Global Instance ty_outlv_E_proper {𝔄} :
    Proper ((≡@{_ 𝔄}) ==> (=) ==> (=)) ty_outlv_E.
  Proof. rewrite /ty_outlv_E. by move=> ?? [_ -> _ _ _]. Qed.

  Global Instance tyl_lfts_ne {𝔄l} n : Proper ((≡{n}@{_ 𝔄l}≡) ==> (=)) tyl_lfts.
  Proof.
    rewrite /tyl_lfts /dist=> tyl tyl' Eq. f_equal.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_lfts_proper {𝔄l} : Proper ((≡@{_ 𝔄l}) ==> (=)) tyl_lfts.
  Proof.
    rewrite /tyl_lfts /equiv=> tyl tyl' Eq. f_equal.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_lft_ne {𝔄l} n : Proper ((≡{n}@{_ 𝔄l}≡) ==> (=)) tyl_lft.
  Proof. rewrite /tyl_lft. by move=> ??->. Qed.
  Global Instance tyl_lft_proper {𝔄l} : Proper ((≡@{_ 𝔄l}) ==> (=)) tyl_lft.
  Proof. rewrite /tyl_lft. by move=> ??->. Qed.
  Global Instance tyl_E_ne {𝔄l} n : Proper ((≡{n}@{_ 𝔄l}≡) ==> (=)) tyl_E.
  Proof.
    rewrite /tyl_E /dist=> tyl tyl' Eq.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_E_proper {𝔄l} : Proper ((≡@{_ 𝔄l}) ==> (=)) tyl_E.
  Proof.
    rewrite /tyl_E /equiv=> tyl tyl' Eq.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_outlv_E_ne {𝔄l} n :
    Proper ((≡{n}@{_ 𝔄l}≡) ==> (=) ==> (=)) tyl_outlv_E.
  Proof.
    rewrite /tyl_outlv_E /dist=> tyl tyl' Eq ??->.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_outlv_E_proper {𝔄l} :
    Proper ((≡@{_ 𝔄l}) ==> (=) ==> (=)) tyl_outlv_E.
  Proof.
    rewrite /tyl_outlv_E /equiv=> tyl tyl' Eq ??->.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.

  Global Instance ty_own_ne {𝔄} n:
    Proper ((≡{n}@{_ 𝔄}≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡{n}≡)) ty_own.
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_own_proper {𝔄} :
    Proper ((≡@{_ 𝔄}) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) ty_own.
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_ne {𝔄} n :
    Proper ((≡{n}@{_ 𝔄}≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡{n}≡)) ty_shr.
  Proof. move=> ?? Eqv ??->??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_proper {𝔄} :
    Proper ((≡@{_ 𝔄}) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) ty_shr.
  Proof. move=> ?? Eqv ??->??->??->??->??->. apply Eqv. Qed.

  (** Simple Type *)

  Inductive simple_type_equiv' {𝔄} (st st': simple_type 𝔄) : Prop := SimpleTypeEquiv:
    st.(st_size) = st'.(st_size) → st.(st_lfts) = st'.(st_lfts) → st.(st_E) = st'.(st_E) →
    (∀vπ d tid vl, st.(st_own) vπ d tid vl ≡ st'.(st_own) vπ d tid vl) →
    simple_type_equiv' st st'.
  Global Instance simple_type_equiv {𝔄} : Equiv (simple_type 𝔄) := simple_type_equiv'.
  Inductive simple_type_dist' {𝔄} (n: nat) (st st': simple_type 𝔄) : Prop :=
    SimpleTypeDist:
    st.(st_size) = st'.(st_size) → st.(st_lfts) = st'.(st_lfts) → st.(st_E) = st'.(st_E) →
    (∀vπ d tid vl, st.(st_own) vπ d tid vl ≡{n}≡ (st'.(st_own) vπ d tid vl)) →
    simple_type_dist' n st st'.
  Global Instance simple_type_dist {𝔄} : Dist (simple_type 𝔄) := simple_type_dist'.

  Definition simple_type_ofe_mixin {𝔄} : OfeMixin (simple_type 𝔄).
  Proof.
    apply (iso_ofe_mixin ty_of_st); (split=> Eqv; split; try by apply Eqv);
    move=> > /=; f_equiv; f_equiv; by move: Eqv=> [_ _ _ ->].
  Qed.
  Canonical Structure simple_typeO 𝔄 : ofe := Ofe (simple_type 𝔄) simple_type_ofe_mixin.

  Global Instance st_own_ne n {𝔄} :
    Proper ((≡{n}@{_ 𝔄}≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡{n}≡)) st_own.
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance st_own_proper {𝔄} :
    Proper ((≡@{_ 𝔄}) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) st_own.
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.

  Global Instance ty_of_st_ne {𝔄} : NonExpansive (@ty_of_st _ _ 𝔄).
  Proof.
    move=> ??? Eqv. split; try apply Eqv. move=> > /=. do 2 f_equiv.
    by rewrite Eqv.
  Qed.
  Global Instance ty_of_st_proper {𝔄} : Proper ((≡@{_ 𝔄}) ==> (≡)) ty_of_st.
  Proof. apply (ne_proper _). Qed.

  (** Plain Type *)

  Inductive plain_type_equiv' {𝔄} (pt pt': plain_type 𝔄) : Prop := PlainTypeEquiv:
    pt.(pt_size) = pt'.(pt_size) →
    (∀v tid vl, pt.(pt_own) v tid vl ≡ pt'.(pt_own) v tid vl) →
    plain_type_equiv' pt pt'.
  Global Instance plain_type_equiv {𝔄} : Equiv (plain_type 𝔄) := plain_type_equiv'.
  Inductive plain_type_dist' {𝔄} (n: nat) (pt pt': plain_type 𝔄) : Prop := PlainTypeDist:
    pt.(pt_size) = pt'.(pt_size) →
    (∀v tid vl, pt.(pt_own) v tid vl ≡{n}≡ (pt'.(pt_own) v tid vl)) →
    plain_type_dist' n pt pt'.
  Global Instance plain_type_dist {𝔄} : Dist (plain_type 𝔄) := plain_type_dist'.

  Definition plain_type_unpack {𝔄} (pt: plain_type 𝔄)
    : prodO natO (𝔄 -d> thread_id -d> list val -d> iPropO Σ) :=
    (pt.(pt_size), pt.(pt_own)).

  Definition plain_type_ofe_mixin {𝔄} : OfeMixin (plain_type 𝔄).
  Proof.
    apply (iso_ofe_mixin plain_type_unpack);
    (rewrite /plain_type_unpack; split; [by move=> [->?]|]);
    move=> [??]; simpl in *; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure plain_typeO 𝔄 : ofe := Ofe (plain_type 𝔄) plain_type_ofe_mixin.

  Global Instance pt_own_ne n {𝔄} :
    Proper ((≡{n}@{_ 𝔄}≡) ==> (=) ==> (=) ==> (=) ==> (≡{n}≡)) pt_own.
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.
  Global Instance pt_own_proper {𝔄} :
    Proper ((≡@{_ 𝔄}) ==> (=) ==> (=) ==> (=) ==> (≡)) pt_own.
  Proof. move=> ?? Eqv ??->??->??->. apply Eqv. Qed.

  Global Instance st_of_pt_ne {𝔄} : NonExpansive (@st_of_pt _ _ 𝔄).
  Proof.
    move=> ??? [? Eqv]. split=>//= *. do 3 f_equiv. by rewrite Eqv.
  Qed.
  Global Instance st_of_pt_proper {𝔄} : Proper ((≡@{_ 𝔄}) ==> (≡)) st_of_pt.
  Proof. apply (ne_proper _). Qed.

End ofe.

Ltac solve_ne_type :=
  constructor;
  solve_proper_core ltac:(fun _ => (
    (eapply ty_size_ne || eapply ty_lfts_ne || eapply ty_E_ne ||
     eapply ty_outlv_E_ne || eapply ty_own_ne || eapply ty_shr_ne); try reflexivity
  ) || f_equiv).

(** * Nonexpansiveness/Contractiveness of Type Morphisms *)

Inductive TypeLftMorphism `{!typeG Σ} {𝔄 𝔅} (T: type 𝔄 → type 𝔅) : Prop :=
| type_lft_morph_add α βs E :
    (∀ty, ⊢ (T ty).(ty_lft) ≡ₗ α ⊓ ty.(ty_lft)) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢
      elctx_interp E ∗ elctx_interp ty.(ty_E) ∗ [∗ list] β ∈ βs, β ⊑ ty.(ty_lft)) →
    TypeLftMorphism T
| type_lft_morph_const α E :
    (∀ty, ⊢ (T ty).(ty_lft) ≡ₗ α) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢ elctx_interp E) →
    TypeLftMorphism T.
Existing Class TypeLftMorphism.

Section type_lft_morph.
Context `{!typeG Σ}.

Lemma type_lft_morph_id_like {𝔄 𝔅} (T: _ 𝔄 → _ 𝔅) :
  (∀ty, (T ty).(ty_lfts) = ty.(ty_lfts)) → (∀ty, (T ty).(ty_E) = ty.(ty_E)) →
  TypeLftMorphism T.
Proof.
  move=> EqLfts EqE. apply (type_lft_morph_add _ static [] [])=> ?.
  + rewrite left_id EqLfts. apply lft_equiv_refl.
  + by rewrite/= left_id right_id EqE.
Qed.

Lemma type_lft_morph_add_one {𝔄 𝔅} κ (T: _ 𝔄 → _ 𝔅) :
  (∀ty, (T ty).(ty_lfts) = κ :: ty.(ty_lfts)) →
  (∀ty, (T ty).(ty_E) = ty.(ty_E) ++ ty_outlv_E ty κ) →
  TypeLftMorphism T.
Proof.
  move=> EqLfts EqE. apply (type_lft_morph_add _ κ [κ] [])=> ?.
  + rewrite EqLfts. apply lft_equiv_refl.
  + by rewrite EqE elctx_interp_app elctx_interp_ty_outlv_E /= left_id right_id.
Qed.

Global Instance type_lft_morph_compose {𝔄 𝔅 ℭ} (T: _ → _ ℭ) (U: _ 𝔄 → _ 𝔅) :
  TypeLftMorphism T → TypeLftMorphism U → TypeLftMorphism (T ∘ U).
Proof.
  case=> [αT βst ET HTα HTE|αT ET HTα HTE]; case=> [αU βsU EU HUα HUE|αU EU HUα HUE].
  - apply (type_lft_morph_add _ (αT ⊓ αU) (βst ++ βsU)
                                 (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βst)))=>ty.
    + iApply lft_equiv_trans. iApply HTα. rewrite -assoc.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app big_sepL_app -!assoc.
      setoid_rewrite (lft_incl_equiv_proper_r _ _ _ (HUα _)). iSplit.
      * iIntros "($ & $ & $ & $ & H)". rewrite big_sepL_fmap.
        iSplit; iApply (big_sepL_impl with "H"); iIntros "!> * _ #H";
        (iApply lft_incl_trans; [done|]);
        [iApply lft_intersect_incl_l|iApply lft_intersect_incl_r].
      * iIntros "($ & $ & H1 & $ & H2 & $)".
        rewrite big_sepL_fmap. iCombine "H1 H2" as "H".
        rewrite -big_sepL_sep. iApply (big_sepL_impl with "H").
        iIntros "!> * _ #[??]". by iApply lft_incl_glb.
  - apply (type_lft_morph_const _ (αT ⊓ αU)
            (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βst)))=>ty.
    + iApply lft_equiv_trans. iApply HTα.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app big_sepL_fmap.
      do 5 f_equiv. by apply lft_incl_equiv_proper_r.
  - apply (type_lft_morph_const _ αT ET)=>//=.
  - apply (type_lft_morph_const _ αT ET)=>//=.
Qed.

Lemma type_lft_morph_lft_equiv_proper {𝔄 𝔅} (T: _ 𝔄 → _ 𝔅)
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

Lemma type_lft_morph_elctx_interp_proper {𝔄 𝔅} (T: _ 𝔄 → _ 𝔅)
  {HT: TypeLftMorphism T} ty ty' :
  elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
  elctx_interp (T ty).(ty_E) ≡ elctx_interp (T ty').(ty_E).
Proof.
  move=> EqvE EqvLft. move: HT=> [|] > ? HE; [|by rewrite !HE].
  rewrite !HE EqvE. do 5 f_equiv. by apply lft_incl_equiv_proper_r.
Qed.

End type_lft_morph.

Class TypeNonExpansive `{!typeG Σ} {𝔄 𝔅} (T: type 𝔄 → type 𝔅) : Prop := {
  type_ne_type_lft_morph:> TypeLftMorphism T;
  type_ne_ty_size ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (T ty).(ty_size) = (T ty').(ty_size);
  type_ne_ty_own n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d tid vl, ty.(ty_own) vπ d tid vl ≡{n}≡ ty'.(ty_own) vπ d tid vl) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{S n}≡ ty'.(ty_shr) vπ d κ tid l) →
    (∀vπ d tid vl, (T ty).(ty_own) vπ d tid vl ≡{n}≡ (T ty').(ty_own) vπ d tid vl);
  type_ne_ty_shr n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d tid vl,
      dist_later n (ty.(ty_own) vπ d tid vl) (ty'.(ty_own) vπ d tid vl)) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{n}≡ ty'.(ty_shr) vπ d κ tid l) →
    (∀vπ d κ tid l, (T ty).(ty_shr) vπ d κ tid l ≡{n}≡ (T ty').(ty_shr) vπ d κ tid l);
}.

Class TypeContractive `{!typeG Σ} {𝔄 𝔅} (T: type 𝔄 → type 𝔅) : Prop := {
  type_contr_type_lft_morph:> TypeLftMorphism T;
  type_contr_ty_size ty ty' : (T ty).(ty_size) = (T ty').(ty_size);
  type_contr_ty_own n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d tid vl, dist_later n (ty.(ty_own) vπ d tid vl) (ty'.(ty_own) vπ d tid vl)) →
    (∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ≡{n}≡ ty'.(ty_shr) vπ d κ tid l) →
    (∀vπ d tid vl, (T ty).(ty_own) vπ d tid vl ≡{n}≡ (T ty').(ty_own) vπ d tid vl);
  type_contr_ty_shr n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty.(ty_lft) ≡ₗ ty'.(ty_lft)) →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d tid vl, match n with S (S n) =>
      ty.(ty_own) vπ d tid vl ≡{n}≡ ty'.(ty_own) vπ d tid vl | _ => True end) →
    (∀vπ d κ tid l, dist_later n (ty.(ty_shr) vπ d κ tid l) (ty'.(ty_shr) vπ d κ tid l)) →
    (∀vπ d κ tid l, (T ty).(ty_shr) vπ d κ tid l ≡{n}≡ (T ty').(ty_shr) vπ d κ tid l);
}.

Class ListTypeNonExpansive `{!typeG Σ} {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) : Prop :=
  type_list_non_expansive: ∃Tl, T = (Tl +$.) ∧ TCHForall (λ _, TypeNonExpansive) Tl.

Class ListTypeContractive `{!typeG Σ} {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) : Prop :=
  type_list_contractive: ∃Tl, T = (Tl +$.) ∧ TCHForall (λ _, TypeContractive) Tl.

Section type_contr.
  Context `{!typeG Σ}.

  Global Instance type_contr_type_ne {𝔄 𝔅} (T: _ 𝔄 → _ 𝔅) :
    TypeContractive T → TypeNonExpansive T.
  Proof.
    move=> HT. split; [by apply _|move=> *; by apply HT| |].
    - move=> *. apply HT=>// *; by [apply dist_dist_later|apply dist_S].
    - move=> n *. apply HT=>// *; [|by apply dist_dist_later].
      case n as [|[|]]=>//. simpl in *. by apply dist_S.
  Qed.

  Global Instance type_ne_ne_compose {𝔄 𝔅 ℭ} (T: _ 𝔅 → _ ℭ) (T': _ 𝔄 → _ 𝔅) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT, HT'| |];
    (move=> n *; apply HT; try (by apply HT');
      first (by iApply type_lft_morph_lft_equiv_proper);
      first (apply type_lft_morph_elctx_interp_proper=>//; apply _)).
    move=> *. case n as [|]=>//. by apply HT'.
  Qed.

  Global Instance type_contr_compose_right {𝔄 𝔅 ℭ} (T: _ 𝔅 → _ ℭ) (T': _ 𝔄 → _ 𝔅) :
    TypeContractive T → TypeNonExpansive T' → TypeContractive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT| |];
    (move=> n *; apply HT; try (by apply HT');
      first (by iApply type_lft_morph_lft_equiv_proper);
      first (apply type_lft_morph_elctx_interp_proper=>//; apply _));
    move=> *; case n as [|[|]]=>//; by apply HT'.
  Qed.

  Global Instance type_contr_compose_left {𝔄 𝔅 ℭ} (T: _ 𝔅 → _ ℭ) (T': _ 𝔄 → _) :
    TypeNonExpansive T → TypeContractive T' → TypeContractive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT, HT'| |];
    (move=> n *; apply HT; try (by apply HT');
      first (by iApply type_lft_morph_lft_equiv_proper);
      first (apply type_lft_morph_elctx_interp_proper=>//; apply _));
    move=> *; case n as [|]=>//; by apply HT'.
  Qed.

  Global Instance const_type_contr {𝔄 𝔅} (ty: _ 𝔄) : TypeContractive (λ _: _ 𝔅, ty).
  Proof. split; move=>// *. eright=> _; by [iApply lft_equiv_refl|]. Qed.

  Global Instance id_type_ne {𝔄} : TypeNonExpansive (id: _ 𝔄 → _ 𝔄).
  Proof. split=>//. by apply type_lft_morph_id_like. Qed.

  Global Instance type_list_non_expansive_nil {𝔄} : ListTypeNonExpansive (λ _: _ 𝔄, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.
  Global Instance type_list_contractive_nil {𝔄} : ListTypeContractive (λ _: _ 𝔄, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.
  Global Instance type_list_non_expansive_cons {𝔄 𝔅 𝔅l} (T: _ 𝔄 → _ 𝔅) (T': _ → _ 𝔅l) :
    TypeNonExpansive T → ListTypeNonExpansive T' →
    ListTypeNonExpansive (λ ty, T ty +:: T' ty).
  Proof. move=> ? [Tl[->?]]. exists (T +:: Tl). split; by [|constructor]. Qed.
  Global Instance type_list_contractive_cons {𝔄 𝔅 𝔅l} (T: _ 𝔄 → _ 𝔅) (T': _ → _ 𝔅l) :
    TypeContractive T → ListTypeContractive T' →
    ListTypeContractive (λ ty, T ty +:: T' ty).
  Proof. move=> ? [Tl[->?]]. exists (T +:: Tl). split; by [|constructor]. Qed.

End type_contr.

(** * Traits *)

Fixpoint shr_locsE (l: loc) (n: nat) : coPset :=
  match n with 0 => ∅ | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1) n end.

Class Copy `{!typeG Σ} {𝔄} (ty: type 𝔄) := {
  copy_persistent vπ d tid vl : Persistent (ty.(ty_own) vπ d tid vl);
  copy_shr_acc vπ d κ tid E F l q :
    ↑lftN ∪ ↑shrN ⊆ E → shr_locsE l (ty.(ty_size) + 1) ⊆ F →
    lft_ctx -∗ ty.(ty_shr) vπ d κ tid l -∗ na_own tid F -∗ q.[κ] ={E}=∗ ∃q' vl,
      na_own tid (F ∖ shr_locsE l ty.(ty_size)) ∗
      l ↦∗{q'} vl ∗ ▷ ty.(ty_own) vπ d tid vl ∗
      (na_own tid (F ∖ shr_locsE l ty.(ty_size)) -∗ l ↦∗{q'} vl
        ={E}=∗ na_own tid F ∗ q.[κ])
}.
Existing Instances copy_persistent.
Instance: Params (@Copy) 3 := {}.

Notation ListCopy := (TCHForall (λ 𝔄, @Copy _ _ 𝔄)).

Class Send `{!typeG Σ} {𝔄} (ty: type 𝔄) :=
  send_change_tid tid tid' vπ d vl :
    ty.(ty_own) vπ d tid vl ⊣⊢ ty.(ty_own) vπ d tid' vl.
Instance: Params (@Send) 3 := {}.

Notation ListSend := (TCHForall (λ 𝔄, @Send _ _ 𝔄)).

Class Sync `{!typeG Σ} {𝔄} (ty: type 𝔄) :=
  sync_change_tid tid tid' vπ d κ l :
    ty.(ty_shr) vπ d κ tid l ⊣⊢ ty.(ty_shr) vπ d κ tid' l.
Instance: Params (@Sync) 3 := {}.

Notation ListSync := (TCHForall (λ 𝔄, @Sync _ _ 𝔄)).

Class JustLoc `{!typeG Σ} {𝔄} (ty: type 𝔄) : Prop := just_loc:
  ∀vπ d tid vl, ty.(ty_own) vπ d tid vl -∗ ⌜∃l: loc, vl = [ #l]⌝.

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

  Global Instance copy_equiv {𝔄} : Proper ((≡@{_ 𝔄}) ==> impl) Copy.
  Proof.
    move=> ty ty' [EqSz _ _ EqOwn EqShr] ?. split=> >.
    - rewrite -EqOwn. apply _.
    - rewrite -EqSz -EqShr. setoid_rewrite <-EqOwn. apply copy_shr_acc.
  Qed.

  Global Program Instance simple_type_copy {𝔄} (st: simple_type 𝔄) : Copy st.
  Next Obligation.
    move=> *. iIntros "#LFT #[%vl[Bor st]] Na κ".
    iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [solve_ndisj|].
    iMod (frac_bor_acc with "LFT Bor κ") as (q) "[>↦ Toκ]"; [solve_ndisj|].
    iModIntro. iExists q, vl. iFrame "↦ st". iIntros "Na".
    iDestruct ("ToNa" with "Na") as "$". iIntros "?". by iApply "Toκ".
  Qed.

  (** Lemmas on Send and Sync *)

  Global Instance send_equiv {𝔄} : Proper ((≡@{_ 𝔄}) ==> impl) Send.
  Proof. move=> ?? [_ _ _ Eqv _] ?. rewrite /Send=> *. by rewrite -!Eqv. Qed.

  Global Instance sync_equiv {𝔄} : Proper ((≡@{_ 𝔄}) ==> impl) Sync.
  Proof. move=> ?? [_ _ _ _ Eqv] ?. rewrite /Sync=> *. by rewrite -!Eqv. Qed.

  Global Instance simple_type_sync {𝔄} (st: simple_type 𝔄) : Send st → Sync st.
  Proof. move=> Eq >/=. by setoid_rewrite Eq at 1. Qed.

End traits.

(** * Leak *)

Definition leak `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (ty: type 𝔄) (Φ: 𝔄 → Prop)
  : Prop := ∀F q vπ d tid vl, ↑lftN ∪ ↑prophN ⊆ F →
    lft_ctx -∗ proph_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ty.(ty_own) vπ d tid vl ={F}=∗ |={F}▷=>^d |={F}=> ⟨π, Φ (vπ π)⟩ ∗ llctx_interp L q.
Instance: Params (@leak) 3 := {}.

Definition leakl `{!typeG Σ} {𝔄l} (E: elctx) (L: llctx) (tyl: typel 𝔄l)
  (Φl: plist (λ 𝔄, 𝔄 → Prop) 𝔄l) : Prop :=
  HForall_1 (λ _, leak E L) tyl Φl.

Section leak.
  Context `{!typeG Σ}.

  Lemma leak_just {𝔄} (ty: _ 𝔄) E L : leak E L ty (const True).
  Proof.
    move=> > ?. iIntros "_ _ _ $ _!>". iApply step_fupdN_full_intro.
    by iApply proph_obs_true.
  Qed.

  Lemma leak_impl {𝔄} (ty: _ 𝔄) E L (Φ Φ': _ → Prop) :
    leak E L ty Φ → (∀a, Φ a → Φ' a) → leak E L ty Φ'.
  Proof.
    move=> Lk Imp > ?. iIntros "LFT PROPH E L ty".
    iMod (Lk with "LFT PROPH E L ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). iIntros "!> >[? $] !>".
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma leakl_nil E L : leakl E L +[] -[].
  Proof. constructor. Qed.
  Lemma leakl_cons {𝔄 𝔄l} E L (ty: _ 𝔄) (tyl: _ 𝔄l) Φ Φl :
    leak E L ty Φ → leakl E L tyl Φl → leakl E L (ty +:: tyl) (Φ -:: Φl).
  Proof. by constructor. Qed.

End leak.

(** * Subtyping *)

Definition type_incl `{!typeG Σ} {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 → 𝔅)
  : iProp Σ :=
  ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ (ty'.(ty_lft) ⊑ ty.(ty_lft)) ∗
  (□ ∀vπ d tid vl, ty.(ty_own) vπ d tid vl -∗ ty'.(ty_own) (f ∘ vπ) d tid vl) ∗
  (□ ∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l -∗ ty'.(ty_shr) (f ∘ vπ) d κ tid l).
Instance: Params (@type_incl) 4 := {}.

Definition subtype `{!typeG Σ} {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 → 𝔅)
  : Prop := ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗ type_incl ty ty' f).
Instance: Params (@subtype) 6 := {}.

Definition eqtype `{!typeG Σ} {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅)
  (f: 𝔄 → 𝔅) (g: 𝔅 → 𝔄) : Prop := subtype E L ty ty' f ∧ subtype E L ty' ty g.
Instance: Params (@eqtype) 6 := {}.

Definition subtype_id `{!typeG Σ} {𝔄} E L (ty ty': type 𝔄) : Prop
  := subtype E L ty ty' id.
Definition eqtype_id `{!typeG Σ} {𝔄} E L (ty ty': type 𝔄) : Prop
  := eqtype E L ty ty' id id.

Definition subtypel `{!typeG Σ} {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l)
  (fl: plist2 (λ 𝔄 𝔅, 𝔄 → 𝔅) 𝔄l 𝔅l) : Prop :=
  HForall2_1 (λ _ _ ty ty' f, subtype E L ty ty' f) tyl tyl' fl.
Definition eqtypel `{!typeG Σ} {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l)
  (fl: plist2 (λ 𝔄 𝔅, 𝔄 → 𝔅) 𝔄l 𝔅l) (gl: plist2 (λ 𝔄 𝔅, 𝔄 → 𝔅) 𝔅l 𝔄l) : Prop :=
  HForall2_2flip (λ _ _ ty ty' f g, eqtype E L ty ty' f g) tyl tyl' fl gl.

Section subtyping.
  Context `{!typeG Σ}.

  (** Subtyping *)

  Lemma eqtype_unfold {𝔄 𝔅} E L f g `{!@Iso 𝔄 𝔅 f g} ty ty' :
    eqtype E L ty ty' f g ↔
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

  Lemma eqtype_id_unfold {𝔄} E L (ty ty': _ 𝔄) :
    eqtype E L ty ty' id id ↔
    ∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ ty.(ty_lft) ≡ₗ ty'.(ty_lft) ∗
      (□ ∀vπ d tid vl, ty.(ty_own) vπ d tid vl ↔ ty'.(ty_own) vπ d tid vl) ∗
      (□ ∀vπ d κ tid l, ty.(ty_shr) vπ d κ tid l ↔ ty'.(ty_shr) vπ d κ tid l)).
  Proof. by rewrite eqtype_unfold. Qed.

  Global Instance type_incl_ne {𝔄 𝔅} n :
    Proper ((≡{n}@{_ 𝔄}≡) ==> (≡{n}@{_ 𝔅}≡) ==> (=) ==> (≡{n}≡)) type_incl.
  Proof.
    rewrite /type_incl.
    move=> ??[->->_ EqvOwn EqvShr]??[->->_ EqvOwn' EqvShr']??->. do 4 f_equiv.
    - do 8 f_equiv. by rewrite EqvOwn EqvOwn'.
    - do 10 f_equiv. by rewrite EqvShr EqvShr'.
  Qed.

  Global Instance type_incl_persistent {𝔄 𝔅} ty ty' (f: 𝔄 → 𝔅) :
    Persistent (type_incl ty ty' f) := _.

  Lemma type_incl_refl {𝔄} (ty: _ 𝔄) : ⊢ type_incl ty ty id.
  Proof.
    iSplit; [done|]. iSplit; [by iApply lft_incl_refl|]. iSplit; iModIntro; by iIntros.
  Qed.

  Lemma type_incl_trans {𝔄 𝔅 ℭ} (f: 𝔄 → 𝔅) (g: _ → ℭ) ty ty' ty'' :
    type_incl ty ty' f -∗ type_incl ty' ty'' g -∗ type_incl ty ty'' (g ∘ f).
  Proof.
    iIntros "[%[#InLft[#InOwn #InShr]]] [%[#InLft'[#InOwn' #InShr']]]".
    iSplit. { iPureIntro. by etrans. } iSplit; [|iSplit].
    - iApply lft_incl_trans; [iApply "InLft'"|iApply "InLft"].
    - iIntros "!>*?". iApply "InOwn'". by iApply "InOwn".
    - iIntros "!>*?". iApply "InShr'". by iApply "InShr".
  Qed.

  Lemma equiv_subtype {𝔄} (ty ty': _ 𝔄) E L : ty ≡ ty' → subtype E L ty ty' id.
  Proof.
    move=> Eqv ?. iIntros "_!>_". iSplit. { iPureIntro. apply Eqv. }
    iSplit. { rewrite Eqv. iApply lft_incl_refl. }
    iSplit; iIntros "!>*"; rewrite Eqv; iIntros "$".
  Qed.

  Lemma equiv_eqtype {𝔄} (ty ty': _ 𝔄) E L : ty ≡ ty' → eqtype E L ty ty' id id.
  Proof. by split; apply equiv_subtype. Qed.

  Lemma subtype_refl {E L 𝔄} (ty: _ 𝔄) : subtype E L ty ty id.
  Proof. move=> ?. by apply equiv_subtype. Qed.

  Lemma eqtype_refl {E L 𝔄} (ty: _ 𝔄) : eqtype E L ty ty id id.
  Proof. split; apply subtype_refl. Qed.

  Lemma eqtype_symm {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L ty' ty g f.
  Proof. move=> [??]. by split. Qed.

  Lemma subtype_trans {𝔄 𝔅 ℭ} (f: 𝔄 → 𝔅) (g: _ → ℭ) ty ty' ty'' E L :
    subtype E L ty ty' f → subtype E L ty' ty'' g → subtype E L ty ty'' (g ∘ f).
  Proof.
    move=> Sub Sub' ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iDestruct (Sub' with "L") as "#Incl'". iIntros "!> #E".
    iApply type_incl_trans; by [iApply "Incl"|iApply "Incl'"].
  Qed.

  Lemma eqtype_trans {𝔄 𝔅 ℭ} (f: 𝔄 → 𝔅) f' (g: _ → ℭ) g' ty ty' ty'' E L :
    eqtype E L ty ty' f f' → eqtype E L ty' ty'' g g' →
    eqtype E L ty ty'' (g ∘ f) (f' ∘ g').
  Proof.
    move=> [Sub1 Sub1'] [??]. split; eapply subtype_trans;
    [apply Sub1| | |apply Sub1']; done.
  Qed.

  Lemma subtype_weaken {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E E' L L' :
    E ⊆+ E' → L ⊆+ L' → subtype E L ty ty' f → subtype E' L' ty ty' f.
  Proof.
    move=> ?? Sub ?. iIntros "L".
    iDestruct (Sub with "[L]") as "#Incl"; [by iApply big_sepL_submseteq|].
    iIntros "!> #E". iApply "Incl". by iApply big_sepL_submseteq.
  Qed.

  Lemma subtype_eq {𝔄 𝔅} (f g: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → f = g → subtype E L ty ty' g.
  Proof. by move=> ? <-. Qed.

  Lemma eqtype_eq {𝔄 𝔅} (f f': 𝔄 → 𝔅) g g' ty ty' E L :
    eqtype E L ty ty' f g → f = f' → g = g' → eqtype E L ty ty' f' g'.
  Proof. by move=> ? <-<-. Qed.

  Global Instance subtype_proper {𝔄 𝔅} E L :
    Proper (eqtype_id E L ==> eqtype_id E L ==> (=@{𝔄 → 𝔅}) ==> (↔)) (subtype E L).
  Proof.
    move=> ??[Sub1 Sub1']??[Sub2 Sub2']??->. split; move=> ?;
    eapply (subtype_trans id _); [by apply Sub1'| |by apply Sub1|];
    eapply (subtype_trans _ id); [|by apply Sub2| |by apply Sub2']; done.
  Qed.

  (** List *)

  Lemma subtypel_nil E L : subtypel E L +[] +[] -[].
  Proof. constructor. Qed.

  Lemma eqtypel_nil E L : eqtypel E L +[] +[] -[] -[].
  Proof. constructor. Qed.

  Lemma subtypel_cons {𝔄 𝔅 𝔄l 𝔅l} (f: 𝔄 → 𝔅) (fl: _ 𝔄l 𝔅l) ty ty' tyl tyl' E L :
    subtype E L ty ty' f → subtypel E L tyl tyl' fl →
    subtypel E L (ty +:: tyl) (ty' +:: tyl') (f -:: fl).
  Proof. by constructor. Qed.

  Lemma eqtypel_cons {𝔄 𝔅 𝔄l 𝔅l} (f: 𝔄 → 𝔅) g (fl: _ 𝔄l 𝔅l) gl ty ty' tyl tyl' E L :
    eqtype E L ty ty' f g → eqtypel E L tyl tyl' fl gl →
    eqtypel E L (ty +:: tyl) (ty' +:: tyl') (f -:: fl) (g -:: gl).
  Proof. by constructor. Qed.

  Lemma eqtypel_subtypel {𝔄l 𝔅l} (fl: _ 𝔄l 𝔅l) gl tyl tyl' E L :
    eqtypel E L tyl tyl' fl gl →
    subtypel E L tyl tyl' fl ∧ subtypel E L tyl' tyl gl.
  Proof.
    elim; [split; by constructor|]=>/= > [??] _ [??]; split; by constructor.
  Qed.

  Lemma subtypel_llctx_nth {ℭ 𝔄l 𝔅l} (ty: _ ℭ) (tyl: _ 𝔄l) (tyl': _ 𝔅l) fl q E L :
    subtypel E L tyl tyl' fl →
    llctx_interp L q -∗ □ (elctx_interp E -∗ ∀i,
      type_incl (hnth ty tyl i) (hnth ty tyl' i) (p2nth id fl i)).
  Proof.
    elim=> [|>Sub _ IH]. { iIntros "_!>_/=" (?). iApply type_incl_refl. }
    iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iDestruct (IH with "L") as "#IH". iIntros "!> #E" (i).
    iSpecialize ("Sub" with "E"). iSpecialize ("IH" with "E"). by case i.
  Qed.

  (** Simple Type *)

  Lemma type_incl_simple_type {𝔄 𝔅} (f: 𝔄 → 𝔅) st st' :
    st.(st_size) = st'.(st_size) → st'.(ty_lft) ⊑ st.(ty_lft) -∗
    □ (∀vπ d tid vl, st.(st_own) vπ d tid vl -∗ st'.(st_own) (f ∘ vπ) d tid vl) -∗
    type_incl st st' f.
  Proof.
    move=> ?. iIntros "#InLft #InOwn". do 2 (iSplit; [done|]).
    iSplit; iIntros "!>*"; [by iApply "InOwn"|]. iIntros "[%vl[Bor ?]]".
    iExists vl. iFrame "Bor". by iApply "InOwn".
  Qed.

  Lemma subtype_simple_type {𝔄 𝔅} E L (f: 𝔄 → 𝔅) st st' :
    (∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜st.(st_size) = st'.(st_size)⌝ ∗ st'.(ty_lft) ⊑ st.(ty_lft) ∗
      (∀vπ d tid vl, st.(st_own) vπ d tid vl -∗ st'.(st_own) (f ∘ vπ) d tid vl))) →
    subtype E L st st' f.
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iDestruct ("Incl" with "E") as (?) "[??]".
    by iApply type_incl_simple_type.
  Qed.

  (** Plain Type *)

  Lemma type_incl_plain_type {𝔄 𝔅} (f: 𝔄 → 𝔅) pt pt' :
    pt.(pt_size) = pt'.(pt_size) → pt'.(ty_lft) ⊑ pt.(ty_lft) -∗
    □ (∀v tid vl, pt.(pt_own) v tid vl -∗ pt'.(pt_own) (f v) tid vl) -∗
    type_incl pt pt' f.
  Proof.
    move=> ?. iIntros "#InLft #InOwn". do 2 (iSplit; [done|]). iSplit; iIntros "!>*/=".
    - iIntros "[%v[->?]]". iExists (f v). iSplit; [done|]. by iApply "InOwn".
    - iIntros "[%vl[Bor pt]]". iExists vl. iFrame "Bor". iNext.
      iDestruct "pt" as (v->) "?". iExists (f v). iSplit; [done|]. by iApply "InOwn".
  Qed.

  Lemma subtype_plain_type {𝔄 𝔅} E L (f: 𝔄 → 𝔅) pt pt' :
    (∀qL, llctx_interp L qL -∗ □ (elctx_interp E -∗
      ⌜pt.(pt_size) = pt'.(pt_size)⌝ ∗ pt'.(ty_lft) ⊑ pt.(ty_lft) ∗
      (∀v tid vl, pt.(pt_own) v tid vl -∗ pt'.(pt_own) (f v) tid vl))) →
    subtype E L pt pt' f.
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> #E". iDestruct ("Sub" with "E") as (?) "[??]".
    by iApply type_incl_plain_type.
  Qed.

  (** Leak *)

  Lemma leak_subtype {𝔄 𝔅} E L ty ty' (f: 𝔄 → 𝔅) Φ :
    subtype E L ty ty' f → leak E L ty' Φ → leak E L ty (Φ ∘ f).
  Proof.
    iIntros (Sub Lk) "* LFT PROPH E L ty". iDestruct (Sub with "L") as "#Sub".
    iDestruct ("Sub" with "E") as "#(_&_& #InOwn &_)".
    iDestruct ("InOwn" with "ty") as "ty'". by iApply (Lk with "LFT PROPH E L ty'").
  Qed.

End subtyping.

(** * Utility *)

Section type_util.
  Context `{!typeG Σ}.

  Lemma heap_mapsto_ty_own {𝔄} l (ty: _ 𝔄) vπ d tid :
    l ↦∗: ty.(ty_own) vπ d tid ⊣⊢
    ∃vl: vec val ty.(ty_size), l ↦∗ vl ∗ ty.(ty_own) vπ d tid vl.
  Proof.
    iSplit; iIntros "[%vl[? ty]]"; [|iExists vl; by iFrame].
    iDestruct (ty_size_eq with "ty") as %<-. iExists (list_to_vec vl).
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
    Proper ((=) ==> pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) by_succ.
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
    Proper ((=) ==> pointwise_relation _ (≡{n}≡) ==> (≡{n}≡)) by_just_loc.
  Proof. move=> ??->?? Eq. rewrite !by_just_loc_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_just_loc_mono :
    Proper ((=) ==> pointwise_relation _ (⊢) ==> (⊢)) by_just_loc.
  Proof. move=> ??->?? In. rewrite !by_just_loc_ex. by setoid_rewrite In. Qed.
  Global Instance by_just_loc_persistent vl Φ :
    (∀l, Persistent (Φ l)) → Persistent (by_just_loc vl Φ).
  Proof. rewrite by_just_loc_ex. apply _. Qed.

End type_util.

Notation "[S( d' ) := d ] P" := (by_succ d (λ d', P)) (at level 200,
  right associativity, format "[S( d' )  :=  d ]  P") : bi_scope.

Notation "[loc[ l ] := vl ] P" := (by_just_loc vl (λ l, P)) (at level 200,
  right associativity, format "[loc[ l ]  :=  vl ]  P") : bi_scope.

Global Hint Resolve ty_outlv_E_elctx_sat tyl_outlv_E_elctx_sat : lrust_typing.
Global Hint Resolve leakl_nil subtype_refl eqtype_refl subtypel_nil eqtypel_nil
  : lrust_typing.
(* We use [Hint Extern] instead of [Hint Resolve] here, because
  [into_plistc_cons], [leakl_cons], [subtypel_cons] and [eqtypel_cons]
  work with [apply] but not with [simple apply] *)
Global Hint Extern 0 (IntoPlistc _ _) => apply into_plistc_cons : lrust_typing.
Global Hint Extern 0 (leakl _ _ _ _) => apply leakl_cons : lrust_typing.
Global Hint Extern 0 (subtypel _ _ _ _ _) => apply subtypel_cons : lrust_typing.
Global Hint Extern 0 (eqtypel _ _ _ _ _ _) => apply eqtypel_cons : lrust_typing.
Global Hint Opaque leak subtype eqtype : lrust_typing.
