From iris.bi Require Import updates.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * Utility for Multi-Step-Taking Updates *)

Section lemmas.
Context `{!BiFUpd PROP}.
Implicit Type P Q: PROP.

Global Instance step_fupdN_proper E n : Proper ((⊣⊢) ==> (⊣⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_ne E n m : Proper (dist m ==> dist m) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.
Global Instance step_fupdN_mono E n : Proper ((⊢) ==> (⊢)) (λ P, |={E}▷=>^n P)%I.
Proof. by elim n; [apply _|]=>/= *??->. Qed.

Lemma step_fupdN_full_intro E n P : P ={E}▷=∗^n P.
Proof. iIntros "?". by iApply step_fupdN_intro. Qed.

Lemma step_fupdN_nmono m n P E : m ≤ n → (|={E}▷=>^m P) -∗ (|={E}▷=>^n P).
Proof.
  move: n. elim m=>/= [|?]; [iIntros; by iApply step_fupdN_full_intro|].
  move=> IH ? /succ_le [?[->Le]]/=. iIntros "?". by iApply IH.
Qed.

Lemma step_fupdN_combine n P Q E :
  (|={E}▷=>^n P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^n (P ∗ Q)).
Proof.
  elim n=>/= [|?]; [iIntros; by iFrame|]. iIntros (IH) ">UpdP >UpdQ !>!>".
  by iMod (IH with "UpdP UpdQ").
Qed.

Lemma step_fupdN_combine_max m n P Q E :
  (|={E}▷=>^m P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^(m `max` n) (P ∗ Q)).
Proof.
  set l := m `max` n. rewrite (step_fupdN_nmono _ l P); [|lia].
  rewrite (step_fupdN_nmono _ l Q); [|lia]. apply step_fupdN_combine.
Qed.

Lemma step_fupdN_with_emp n P E :
  (|={E}=> |={E}▷=>^n |={E}=> P) -∗ (|={E, ∅}=> |={∅}▷=>^n |={∅, E}=> P).
Proof.
  elim: n=> /=[|n IH].
  - iIntros ">>Upd". iApply fupd_mask_intro_subseteq; [set_solver|done].
  - iIntros ">>Upd". iApply fupd_mask_intro; [set_solver|].
    iIntros "Close !>!>". iDestruct (IH with "Upd") as "?". by iMod "Close".
Qed.

End lemmas.
