From iris.algebra Require Import auth cmra functions gmap frac_agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lrust.util Require Import discrete_fun.
From lrust.prophecy Require Import prophecy.
From lrust.typing Require Import base.

Implicit Type (Ap: ptType) (q: Qp).

(** * Camera for Unique Borrowing *)

Local Definition uniq_itemR Ap := frac_agreeR (leibnizO (pval_depth Ap)).
Local Definition uniq_gmapUR Ap := gmapUR positive (uniq_itemR Ap).
Local Definition uniq_smryUR := discrete_funUR uniq_gmapUR.
Definition uniqUR := authUR uniq_smryUR.

Implicit Type S: uniq_smryUR.

Local Definition item {Ap} q (vπd: pval_depth Ap) : uniq_itemR Ap :=
  @to_frac_agree (leibnizO _) q vπd.
Local Definition line ξ q vπd : uniq_smryUR :=
  .{[ξ.(pv_ty) := {[ξ.(pv_id) := item q vπd]}]}.
Local Definition add_line ξ q vπd S : uniq_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := item q vπd]> (S ξ.(pv_ty))]> S.

Definition uniqΣ := #[GFunctor uniqUR].
Class uniqPreG Σ := UniqPreG { uniq_preG_inG:> inG Σ uniqUR }.
Class uniqG Σ := UniqG { uniq_inG:> uniqPreG Σ; uniq_name : gname }.
Instance subG_uniqPreG {Σ} : subG uniqΣ Σ → uniqPreG Σ.
Proof. solve_inG. Qed.

Definition uniqN := nroot .@ "uniq".

(** * Iris Propositions *)

Section defs.
Context `{!invG Σ, !prophG Σ, !uniqG Σ}.

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
Context `{!invG Σ, !prophG Σ, !uniqG Σ}.

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

Local Lemma vo_pc ξ vπd :
  .VO[ξ] vπd -∗ .PC[ξ] vπd -∗ .VO2[ξ] vπd ∗ 1:[ξ].
Proof.
  iIntros "Vo". iDestruct 1 as "[[??]|[ExVo2 _]]"; last first.
  { iDestruct "ExVo2" as (?) "Vo2".
    by iDestruct (own_line_agree with "Vo Vo2") as %[? _]. }
  rewrite -vo_vo2. iFrame.
Qed.

(** Instances *)

Global Instance uniq_ctx_persistent : Persistent uniq_ctx := _.

Global Instance val_obs_timeless ξ vπd : Timeless (.VO[ξ] vπd) := _.

(** Initialization *)

Lemma uniq_init `{!uniqPreG Σ} E :
  ↑uniqN ⊆ E → ⊢ |={E}=> ∃ _: uniqG Σ, uniq_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "Auth"; [by apply auth_auth_valid|].
  set IUniqG := UniqG Σ _ γ. iExists IUniqG.
  iMod (inv_alloc _ _ uniq_inv with "[Auth]") as "?"; by [iExists ε|].
Qed.

Definition pval_to_pt {A} (vπ: proph_asn → A) := PtType A (vπ inhabitant).

Lemma uniq_intro {A} E (vπ: _ → A) d :
  ↑prophN ∪ ↑uniqN ⊆ E → proph_ctx -∗ uniq_ctx ={E}=∗
    ∃i, let ξ := PVar (pval_to_pt vπ) i in .VO[ξ] (vπ,d) ∗ .PC[ξ] (vπ,d).
Proof.
  iIntros (?) "PROPH ?". iInv uniqN as (S) "> Auth".
  set Ap := pval_to_pt vπ. set I := dom (gset _) (S Ap).
  iMod (proph_intro _ I with "PROPH") as (i NIn) "Tok"; [by solve_ndisj|].
  move: NIn=> /not_elem_of_dom ?. set ξ := PVar Ap i.
  set S' := add_line ξ 1 (vπ,d) S.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ 1 (vπ,d)) with "Auth") as "[? Vo2]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitR "Vo2 Tok"; [by iExists S'|]. iModIntro. iExists i.
  iDestruct (vo_vo2 with "Vo2") as "[Vo Vo']". iFrame "Vo". iLeft. iFrame.
Qed.

Lemma uniq_agree ξ vπd vπd' :
  .VO[ξ] vπd -∗ ▷ .PC[ξ] vπd' -∗ ◇ (⌜vπd = vπd'⌝ ∗ (.VO[ξ] vπd ∗ .PC[ξ] vπd)).
Proof.
  iIntros "Vo". iDestruct 1 as "[> [Vo' ?]|[> ExVo2 _]]"; last first.
  { iDestruct "ExVo2" as (?) "Vo2".
    by iDestruct (own_line_agree with "Vo Vo2") as %[? _]. }
  iDestruct (own_line_agree with "Vo Vo'") as %[_ ->]. iModIntro.
  iSplit; [done|]. iFrame "Vo". iLeft. iFrame.
Qed.

Lemma uniq_proph_tok ξ vπd :
  .VO[ξ] vπd -∗ .PC[ξ] vπd -∗ .VO[ξ] vπd ∗ 1:[ξ] ∗ (1:[ξ] -∗ .PC[ξ] vπd).
Proof.
  iIntros "Vo Pc".
  iDestruct (vo_pc with "Vo Pc") as "[Vo2 $]".
  iDestruct (vo_vo2 with "Vo2") as "[$ ?]". iIntros "?". iLeft. iFrame.
Qed.

Lemma uniq_update E ξ vπd vπd' : ↑uniqN ⊆ E →
  uniq_ctx -∗ .VO[ξ] vπd -∗ .PC[ξ] vπd ={E}=∗ .VO[ξ] vπd' ∗ .PC[ξ] vπd'.
Proof.
  iIntros (?) "? Vo Pc". iDestruct (vo_pc with "Vo Pc") as "[Vo2 Tok]".
  iInv uniqN as (S) "> Auth". set S' := add_line ξ 1 vπd' S.
  iMod (own_update_2 _ _ _ (●S' ⋅ ◯line ξ 1 vπd') with "Auth Vo2") as "[? Vo2]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitR "Vo2 Tok"; [by iExists S'|]. iModIntro.
  iDestruct (vo_vo2 with "Vo2") as "[$ ?]". iLeft. iFrame.
Qed.

Lemma uniq_resolve E ξ vπ d ζs q : ↑prophN ⊆ E → vπ ./ ζs →
  proph_ctx -∗ .VO[ξ] (vπ,d) -∗ .PC[ξ] (vπ,d) -∗ q:+[ζs] ={E}=∗
    ⟨π, π ξ = vπ π⟩ ∗ .PC[ξ] (vπ,d) ∗ q:+[ζs].
Proof.
  iIntros (??) "PROPH Vo Pc Ptoks".
  iDestruct (vo_pc with "Vo Pc") as "[? Tok]".
  iMod (proph_resolve with "PROPH Tok Ptoks") as "[#? $]"; [done|done|].
  iModIntro. iSplitR; [done|]. iRight. iSplitL; [by iExists (vπ,d)|].
  by iApply proph_obs_eqz.
Qed.

Lemma uniq_preresolve E ξ u vπ d ζs q : ↑prophN ⊆ E → u ./ ζs →
  proph_ctx -∗ .VO[ξ] (vπ,d) -∗ .PC[ξ] (vπ,d) -∗ q:+[ζs] ={E}=∗
    ⟨π, π ξ = u π⟩ ∗ q:+[ζs] ∗ (∀vπ' d', u :== vπ' -∗ .PC[ξ] (vπ',d')).
Proof.
  iIntros (??) "PROPH Vo Pc Ptoks".
  iDestruct (vo_pc with "Vo Pc") as "[? Tok]".
  iMod (proph_resolve with "PROPH Tok Ptoks") as "[#Obs $]"; [done|done|].
  iModIntro. iSplitR; [done|]. iIntros (??) "Eqz". iRight.
  iSplitR "Eqz"; [by iExists (vπ,d)|].
  by iDestruct (proph_eqz_modify with "Obs Eqz") as "?".
Qed.

Lemma proph_ctrl_eqz ξ vπ d : proph_ctx -∗ .PC[ξ] (vπ,d) -∗ (.$ ξ) :== vπ.
Proof.
  iIntros "#?". iDestruct 1 as "[[_ ?]|[_ ?]]"; by [iApply proph_token_eqz|].
Qed.

End lemmas.
