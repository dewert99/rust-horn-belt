From iris.bi Require Import updates.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

(** * Utility for Multi-Step-Taking Updates *)

Section lemmas.
Context `{!BiFUpd PROP}.
Implicit Type P Q R: PROP.

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

Global Instance step_fupdN_from_sep n P Q E :
  FromSep (|={E}▷=>^n (P ∗ Q)) (|={E}▷=>^n P) (|={E}▷=>^n Q).
Proof.
  rewrite /FromSep. iIntros "[P Q]". iApply (step_fupdN_combine with "P Q").
Qed.

Lemma step_fupdN_combine_max m n P Q E :
  (|={E}▷=>^m P) -∗ (|={E}▷=>^n Q) -∗ (|={E}▷=>^(m `max` n) (P ∗ Q)).
Proof.
  set l := m `max` n. rewrite (step_fupdN_nmono _ l P); [|lia].
  rewrite (step_fupdN_nmono _ l Q); [|lia]. apply step_fupdN_combine.
Qed.

Global Instance step_fupdN_from_sep_max m n P Q E :
  FromSep (|={E}▷=>^(m `max` n) (P ∗ Q)) (|={E}▷=>^m P) (|={E}▷=>^n Q) | 100.
Proof.
  rewrite /FromSep. iIntros "[P Q]". iApply (step_fupdN_combine_max with "P Q").
Qed.

Lemma step_fupdN_with_emp n P E :
  (|={E}=> |={E}▷=>^n |={E}=> P) -∗ (|={E, ∅}=> |={∅}▷=>^n |={∅, E}=> P).
Proof.
  elim: n=> /=[|n IH].
  - iIntros ">>Upd". iApply fupd_mask_intro_subseteq; [set_solver|done].
  - iIntros ">>Upd". iApply fupd_mask_intro; [set_solver|].
    iIntros "ToE !>!>". iDestruct (IH with "Upd") as "?". by iMod "ToE".
Qed.

Lemma step_fupdN_add E n m P :
  (|={E}▷=>^(n + m) P) ⊣⊢ (|={E}▷=>^n |={E}▷=>^m P).
Proof. 
  induction n as [|n IH]; [done| rewrite /= IH //].
Qed.

Lemma step_fupdN_chain E n m P Q R :
(P -∗ |={E}▷=>^n Q) →
(Q -∗ |={E}▷=>^m R) →
P -∗ |={E}▷=>^(n + m) R.
Proof.
  iIntros (PQ QR) "P".
  iDestruct (PQ with "P") as "Q".
  iApply step_fupdN_add.
  by iApply step_fupdN_mono.
Qed.

Lemma step_fupdN_fupd_mask_mono E₁ E₂ n P: 
  E₁ ⊆ E₂ → (|={E₁}▷=>^n |={E₁}=> P) -∗ (|={E₂}▷=>^n |={E₂}=> P).
  iIntros (Hsub).
  induction n as [|n IH].
  - by iApply fupd_mask_mono.
  - iIntros "H /=". 
    iApply fupd_mask_mono; [done|]. iApply IH.
    iMod "H". iModIntro.
    by iApply fupd_mask_mono; [done|].
Qed. 

Lemma fupd_step_fupdN_fupd_mask_mono E₁ E₂ n P: 
  E₁ ⊆ E₂ →
  (|={E₁}=> |={E₁}▷=>^n |={E₁}=> P) -∗ (|={E₂}=> |={E₂}▷=>^n |={E₂}=> P).
Proof.
  iIntros (Hsub) "Hstep".
  iApply fupd_mask_mono; [done|].
  by iApply step_fupdN_fupd_mask_mono; [done|].
Qed.

End lemmas.
