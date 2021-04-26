From iris.algebra Require Import auth cmra functions gmap frac_agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lrust.util Require Import discrete_fun.
From lrust.prophecy Require Import prophecy.

Implicit Type 𝔄 𝔅: syn_type.

Section basic.
Context `{!invG Σ, !prophG Σ}.

(** * Camera for Unique Borrowing *)

Local Definition uniq_itemR 𝔄 := frac_agreeR (leibnizO (proph 𝔄 * nat)).
Local Definition uniq_gmapUR 𝔄 := gmapUR positive (uniq_itemR 𝔄).
Local Definition uniq_smryUR := discrete_funUR uniq_gmapUR.
Definition uniqUR := authUR uniq_smryUR.

Implicit Type S: uniq_smryUR.

Local Definition item {𝔄} q (vπd: proph 𝔄 * nat) : uniq_itemR 𝔄 :=
  @to_frac_agree (leibnizO _) q vπd.
Local Definition line ξ q vπd : uniq_smryUR :=
  .{[ξ.(pv_ty) := {[ξ.(pv_bd).1 := item q vπd]}]}.
Local Definition add_line ξ q vπd S : uniq_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_bd).1 := item q vπd]> (S ξ.(pv_ty))]> S.

Definition uniqΣ := #[GFunctor uniqUR].
Class uniqPreG Σ := UniqPreG { uniq_preG_inG:> inG Σ uniqUR }.
Class uniqG Σ := UniqG { uniq_inG:> uniqPreG Σ; uniq_name: gname }.
Instance subG_uniqPreG {Σ'} : subG uniqΣ Σ' → uniqPreG Σ'.
Proof. solve_inG. Qed.

Definition uniqN := nroot .@ "uniq".

End basic.

(** * Iris Propositions *)

Section defs.
Context `{!invG Σ, !prophG Σ, uniqG Σ}.

(** Unique Reference Context *)
Definition uniq_inv: iProp Σ := ∃S, own uniq_name (● S).
Definition uniq_ctx: iProp Σ := inv uniqN uniq_inv.

Local Definition own_line ξ q vπd := own uniq_name (◯ line ξ q vπd).

(** Value Observer *)
Definition val_obs ξ vπd : iProp Σ := own_line ξ (1/2) vπd.

(** Prophecy Control *)
Local Definition val_obs2 ξ vπd : iProp Σ := own_line ξ 1 vπd.
Definition proph_ctrl ξ vπd : iProp Σ :=
  (val_obs ξ vπd ∗ 1:[ξ]) ∨ ((∃vπd', val_obs2 ξ vπd') ∗ (.$ ξ) :== vπd.1).

End defs.

Notation ".VO[ ξ ]" := (val_obs ξ) (at level 5, format ".VO[ ξ ]") : bi_scope.
Local Notation ".VO2[ ξ ]" := (val_obs2 ξ)
  (at level 5, format ".VO2[ ξ ]") : bi_scope.
Notation ".PC[ ξ ]" := (proph_ctrl ξ)
  (at level 5, format ".PC[ ξ ]") : bi_scope.


(** * Lemmas *)

Section lemmas.
Context `{!invG Σ, !prophG Σ, uniqG Σ}.

Global Instance uniq_ctx_persistent : Persistent uniq_ctx := _.
Global Instance val_obs_timeless ξ vπd : Timeless (.VO[ξ] vπd) := _.

Local Lemma own_line_agree ξ q q' vπd vπd' :
  own_line ξ q vπd -∗ own_line ξ q' vπd' -∗ ⌜(q + q' ≤ 1)%Qp ∧ vπd = vπd'⌝.
Proof.
  iIntros "Own Own'". iDestruct (own_valid_2 with "Own Own'") as %Val.
  iPureIntro. move: Val.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid.
  by move/frac_agree_op_valid.
Qed.

Local Lemma vo_vo2 ξ vπd : .VO[ξ] vπd ∗ .VO[ξ] vπd ⊣⊢ .VO2[ξ] vπd.
Proof.
  by rewrite -own_op -auth_frag_op discrete_fun_singleton_op singleton_op /item
    -frac_agree_op Qp_half_half.
Qed.

Local Lemma vo_pc ξ vπd vπd' :
  .VO[ξ] vπd -∗ .PC[ξ] vπd' -∗ ⌜vπd = vπd'⌝ ∗ .VO2[ξ] vπd ∗ 1:[ξ].
Proof.
  iIntros "Vo [[Vo' ?]|[[% Vo2] _]]";
  [|by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[_->]. iSplit; [done|].
  rewrite -vo_vo2. iFrame.
Qed.

(** Initialization *)

Lemma uniq_init `{!uniqPreG Σ} E :
  ↑uniqN ⊆ E → ⊢ |={E}=> ∃ _: uniqG Σ, uniq_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "Auth"; [by apply auth_auth_valid|].
  set IUniqG := UniqG Σ _ γ. iExists IUniqG.
  iMod (inv_alloc _ _ uniq_inv with "[Auth]") as "?"; by [iExists ε|].
Qed.

Lemma prval_to_inh {𝔄} (vπ: proph 𝔄) : inhabited 𝔄.
Proof. move: proph_asn_inhabited=> [π]. exists. apply (vπ π). Qed.

Definition prval_to_prvar {𝔄} vπ i := PrVar 𝔄 (i, (prval_to_inh vπ)).

Lemma uniq_intro {𝔄} E (vπ: _ → 𝔄) d :
  ↑prophN ∪ ↑uniqN ⊆ E → proph_ctx -∗ uniq_ctx ={E}=∗
    ∃i, let ξ := prval_to_prvar vπ i in .VO[ξ] (vπ,d) ∗ .PC[ξ] (vπ,d).
Proof.
  iIntros (?) "PROPH ?". iInv uniqN as (S) "> Auth". set I := dom (gset _) (S 𝔄).
  iMod (proph_intro _ I with "PROPH") as (i NIn) "Tok"; [by solve_ndisj|].
  move: NIn=> /not_elem_of_dom ?.
  set ξ := prval_to_prvar vπ i. set S' := add_line ξ 1 (vπ,d) S.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ 1 (vπ,d)) with "Auth") as "[? Vo2]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitR "Vo2 Tok"; [by iExists S'|]. iModIntro. iExists i.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_strip_later ξ vπd vπd' :
  ▷ .VO[ξ] vπd -∗ ▷ .PC[ξ] vπd' -∗ ◇ (⌜vπd = vπd'⌝ ∗ (.VO[ξ] vπd ∗ .PC[ξ] vπd')).
Proof.
  iIntros "> Vo [> [Vo' ?]|[>[% Vo2] _]]";
  [|by iDestruct (own_line_agree with "Vo Vo2") as %[? _]].
  iDestruct (own_line_agree with "Vo Vo'") as %[_ ->]. iModIntro.
  iSplit; [done|]. iSplitL "Vo"; [done|]. iLeft. by iSplitL "Vo'".
Qed.

Lemma uniq_agree ξ vπd vπd' : .VO[ξ] vπd -∗ .PC[ξ] vπd' -∗ ⌜vπd = vπd'⌝.
Proof.
  iIntros "Vo Pc". by iDestruct (vo_pc with "Vo Pc") as (->) "?".
Qed.

Lemma uniq_proph_tok ξ vπd vπd' :
  .VO[ξ] vπd -∗ .PC[ξ] vπd' -∗ .VO[ξ] vπd ∗ 1:[ξ] ∗ (1:[ξ] -∗ .PC[ξ] vπd').
Proof.
  iIntros "Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->) "[Vo2 $]".
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iIntros "?". iLeft. iFrame.
Qed.

Lemma uniq_update E ξ vπd vπd' vπd'' : ↑uniqN ⊆ E →
  uniq_ctx -∗ .VO[ξ] vπd -∗ .PC[ξ] vπd' ={E}=∗ .VO[ξ] vπd'' ∗ .PC[ξ] vπd''.
Proof.
  iIntros (?) "? Vo Pc". iDestruct (vo_pc with "Vo Pc") as (->) "[Vo2 Tok]".
  iInv uniqN as (S) "> Auth". set S' := add_line ξ 1 vπd'' S.
  iMod (own_update_2 _ _ _ (●S' ⋅ ◯line ξ 1 vπd'') with "Auth Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2 Tok"; [by iExists S'|]. iModIntro.
  iDestruct (vo_vo2 with "Vo2") as "[$?]". iLeft. iFrame.
Qed.

Lemma uniq_resolve E ξ vπ d vπd' ζs q : ↑prophN ⊆ E → vπ ./ ζs →
  proph_ctx -∗ .VO[ξ] (vπ,d) -∗ .PC[ξ] vπd' -∗ q:+[ζs] ={E}=∗
    ⟨π, π ξ = vπ π⟩ ∗ .PC[ξ] (vπ,d) ∗ q:+[ζs].
Proof.
  iIntros (??) "PROPH Vo Pc Ptoks". iDestruct (vo_pc with "Vo Pc") as (<-) "[? Tok]".
  iMod (proph_resolve with "PROPH Tok Ptoks") as "[#? $]"; [done|done|].
  iModIntro. iSplitR; [done|]. iRight. iSplitL; [by iExists (vπ,d)|].
  by iApply proph_eqz_obs.
Qed.

Lemma uniq_preresolve E ξ u vπ d vπd' ζs q : ↑prophN ⊆ E → u ./ ζs →
  proph_ctx -∗ .VO[ξ] (vπ,d) -∗ .PC[ξ] vπd' -∗ q:+[ζs] ={E}=∗
    ⟨π, π ξ = u π⟩ ∗ q:+[ζs] ∗ (∀vπ' d', u :== vπ' -∗ .PC[ξ] (vπ',d')).
Proof.
  iIntros (??) "PROPH Vo Pc Ptoks". iDestruct (vo_pc with "Vo Pc") as (<-) "[? Tok]".
  iMod (proph_resolve with "PROPH Tok Ptoks") as "[#Obs $]"; [done|done|].
  iModIntro. iSplitR; [done|]. iIntros (??) "Eqz". iRight.
  iSplitR "Eqz"; [by iExists (vπ,d)|].
  by iDestruct (proph_eqz_modify with "Obs Eqz") as "?".
Qed.

Lemma proph_ctrl_eqz ξ vπ d : proph_ctx -∗ .PC[ξ] (vπ,d) -∗ (.$ ξ) :== vπ.
Proof. iIntros "#? [[_ ?]|[_ ?]]"; by [iApply proph_eqz_token|]. Qed.

End lemmas.

Global Opaque uniq_ctx val_obs proph_ctrl.
