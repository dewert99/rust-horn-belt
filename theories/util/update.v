From iris.bi Require Import updates.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * Utility for Multi-Step-Taking Updates *)

Section lemmas.
Context `{BiFUpd PROP}.
Implicit Type P Q: PROP.

Lemma step_fupdN_nmono E m n P : m ≤ n → (|={E}▷=>^m P) -∗ (|={E}▷=>^n P).
Proof.
  move: n. elim m=> /=[|m']. { iIntros (? _) "?". by iApply step_fupdN_intro. }
  move=> IH ? /succ_le [n'[->Le]]/=. iIntros "?". by iApply IH.
Qed.

Lemma step_fupdN_combine n E P Q :
  (|={E}▷=>^n P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^n (P ∗ Q)).
Proof.
  elim n=> /=[|?]; [iIntros; by iFrame|]. iIntros (IH) ">UpdP >UpdQ !>!>".
  by iMod (IH with "UpdP UpdQ") as "?".
Qed.

End lemmas.
