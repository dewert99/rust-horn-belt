From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lrust.util Require Import basic.

(** * Utility for Multi-Step-Taking Updates *)

Lemma step_fupdN_nmono `{!invG Σ} E m n (P: iProp Σ) :
  m ≤ n → (|={E}▷=>^m P) ={E}▷=∗^n P.
Proof. generalize n.
  elim m=> /=[|m']. { iIntros (? _) "?". by iApply step_fupdN_intro. }
  move=> IH ? /succ_le [n'[->Le]]/=. iIntros "?". by iApply IH.
Qed.
