From iris.algebra Require Import lib.mono_nat numbers.
From iris.base_logic Require Import lib.own.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".
Import uPred.

Class timeG Σ := TimeG {
  time_mono_nat_inG :> inG Σ mono_natR;
  time_nat_inG :> inG Σ (authR natUR);
  time_global_name : gname;
  time_persist_name : gname;
  time_cumul_name : gname;
}.

Class timePreG Σ := TimePreG {
  time_preG_mono_nat_inG :> inG Σ mono_natR;
  time_preG_nat_inG :> inG Σ (authR natUR);
}.

Definition timeΣ : gFunctors :=
  #[GFunctor (constRF mono_natR); GFunctor (constRF (authR natUR))].
Instance subG_timePreG Σ : subG timeΣ Σ → timePreG Σ.
Proof. solve_inG. Qed.

Definition timeN : namespace := nroot .@ "lft_usr" .@ "time".

Section definitions.
  Context `{!timeG Σ}.

  (** persistent time receipt *)
  Definition persist_time_rcpt (n : nat) :=
    own time_persist_name (mono_nat_lb n).
  (** cumulative time receipt *)
  Definition cumul_time_rcpt (n : nat) :=
    own time_cumul_name (◯ n).
  (** invariant *)
  Definition time_ctx `{!invG Σ} :=
    inv timeN (∃ n m,
       own time_global_name (mono_nat_lb (n + m)) ∗
       own time_cumul_name (● n) ∗
       own time_persist_name (mono_nat_auth 1 m)).
  (** authority *)
  Definition time_interp (n: nat) : iProp Σ :=
    own time_global_name (mono_nat_auth 1 n).

End definitions.

Typeclasses Opaque persist_time_rcpt cumul_time_rcpt.
Instance: Params (@persist_time_rcpt) 2 := {}.
Instance: Params (@cumul_time_rcpt) 2 := {}.

Notation "⧖ n" := (persist_time_rcpt n)
  (at level 1, format "⧖ n") : bi_scope.
Notation "⧗ n" := (cumul_time_rcpt n)
  (at level 1, format "⧗ n") : bi_scope.

Section time.
  Context `{!timeG Σ}.
  Implicit Types P Q : iProp Σ.

  Global Instance persist_time_rcpt_timeless n : Timeless (⧖n).
  Proof. unfold persist_time_rcpt. apply _. Qed.
  Global Instance persist_time_rcpt_persistent n : Persistent (⧖n).
  Proof. unfold persist_time_rcpt. apply _. Qed.
  Global Instance cumul_time_rcpt_timeless n : Timeless (⧗n).
  Proof. unfold cumul_time_rcpt. apply _. Qed.

  Lemma time_interp_step n :
    time_interp n ==∗ time_interp (S n).
  Proof. eapply own_update, mono_nat_update. lia. Qed.

  Lemma persist_time_rcpt_mono n m :
    (n ≤ m)%nat → ⧖m -∗ ⧖n.
  Proof.
    intros ?. unfold persist_time_rcpt. by apply own_mono, mono_nat_lb_mono.
  Qed.
  Lemma cumul_time_rcpt_mono n m :
    (n ≤ m)%nat → ⧗m -∗ ⧗n.
  Proof.
    intros ?. unfold cumul_time_rcpt.
    by apply own_mono, auth_frag_mono, nat_included.
  Qed.

  Lemma persist_time_rcpt_sep n m : ⧖(n `max` m) ⊣⊢ ⧖n ∗ ⧖m.
  Proof. by rewrite /persist_time_rcpt -mono_nat_lb_op own_op. Qed.
  Lemma cumul_time_rcpt_sep n m : ⧗(n + m) ⊣⊢ ⧗n ∗ ⧗m.
  Proof. by rewrite /cumul_time_rcpt -nat_op auth_frag_op own_op. Qed.

  Global Instance persist_time_rcpt_from_sep n m : FromSep ⧖(n `max` m) ⧖n ⧖m.
  Proof. rewrite /FromSep. by rewrite persist_time_rcpt_sep. Qed.
  Global Instance persist_time_rcpt_into_sep n m : IntoSep ⧖(n `max` m) ⧖n ⧖m.
  Proof. rewrite /IntoSep. by rewrite persist_time_rcpt_sep. Qed.
  Global Instance cumul_time_rcpt_from_sep n m : FromSep ⧗(n + m) ⧗n ⧗m.
  Proof. rewrite /FromSep. by rewrite cumul_time_rcpt_sep. Qed.
  Global Instance cumul_time_rcpt_into_sep n m : IntoSep ⧗(n + m) ⧗n ⧗m.
  Proof. rewrite /IntoSep. by rewrite cumul_time_rcpt_sep. Qed.

  Lemma persist_time_rcpt_0 : ⊢ |==> ⧖0.
  Proof. rewrite /persist_time_rcpt. apply own_unit. Qed.
  Lemma cumul_time_rcpt_0 : ⊢ |==> ⧗0.
  Proof. rewrite /cumul_time_rcpt. apply own_unit. Qed.

  Lemma cumul_persist_time_rcpts `{!invG Σ} E n m :
    ↑timeN ⊆ E → time_ctx -∗ ⧗n -∗ ⧖m ={E}=∗ ⧖(n + m).
  Proof.
    iIntros (?) "#TIME Hn #Hm".
    unfold persist_time_rcpt, cumul_time_rcpt.
    iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm')".
    iDestruct (own_valid_2 with "Hn' Hn")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iDestruct (own_valid_2 with "Hm' Hm") as %?%mono_nat_both_valid.
    iMod (own_update_2 with "Hn' Hn") as "Hnn'".
    { apply (auth_update_dealloc _ _ (n'-n)%nat), nat_local_update.
      rewrite -plus_n_O. lia. }
    iMod (own_update with "Hm'") as "Hm'n".
    { apply (mono_nat_update (m'+n)%nat); lia. }
    iDestruct (own_mono _ _ (mono_nat_lb _) with "Hm'n") as "#$".
    { rewrite <-mono_nat_included. apply mono_nat_lb_mono. lia. }
    iModIntro; iSplitL; [|done]. iExists _, _. iFrame.
    rewrite (_:(n'+m')%nat = ((n'-n) + (m'+n))%nat); [done|lia].
  Qed.

  Lemma step_cumul_time_rcpt `{!invG Σ} E n :
    ↑timeN ⊆ E →
    time_ctx -∗ time_interp n ={E, E∖↑timeN}=∗ time_interp n ∗
    (time_interp (S n) ={E∖↑timeN, E}=∗ time_interp (S n) ∗ ⧗1).
  Proof.
    iIntros (?) "#TIME Hn". iInv "TIME" as (n' m') ">(Hglob & Hn' & Hm')" "Hclose".
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iModIntro. iFrame. iIntros "HSn". unfold cumul_time_rcpt.
    iMod (own_update with "Hn'") as "[HSn' $]".
    { apply auth_update_alloc, nat_local_update. by rewrite -plus_n_O. }
    iDestruct (own_mono _ _ (mono_nat_lb _) with "HSn") as "#H'Sn".
    { apply mono_nat_included. }
    iFrame. iApply "Hclose". iExists _, _. iFrame.
    iApply (own_mono with "H'Sn"). apply mono_nat_lb_mono. lia.
  Qed.

  Lemma time_rcpt_le `{!invG Σ} E n m m' :
    ↑timeN ⊆ E →
    time_ctx -∗ time_interp n -∗ ⧖m -∗ ⧗m' ={E}=∗ ⌜m+m' ≤ n⌝%nat ∗ ⧗m'.
  Proof.
    iIntros (?) "#TIME Hn Hm Hm'". iInv "TIME" as (m'0 m0) ">(Hglob & Hm'0 & Hm0)".
    iDestruct (own_valid_2 with "Hn Hglob") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm0 Hm") as %?%mono_nat_both_valid.
    iDestruct (own_valid_2 with "Hm'0 Hm'")
      as %[?%nat_included _]%auth_both_valid_discrete.
    iModIntro. iFrame. iSplitL; auto with iFrame lia.
  Qed.
End time.

Lemma time_init `{!invG Σ, !timePreG Σ} E : ↑timeN ⊆ E →
  ⊢ |={E}=> ∃ _ : timeG Σ, time_ctx ∗ time_interp 0.
Proof.
  intros ?.
  iMod (own_alloc (mono_nat_auth 1 0 ⋅ mono_nat_lb 0)) as (time_global_name) "[??]";
    [by apply mono_nat_both_valid|].
  iMod (own_alloc (mono_nat_auth 1 0)) as (time_persist_name) "?";
    [by apply mono_nat_auth_valid|].
  iMod (own_alloc (● 0%nat)) as (time_cumul_name) "?"; [by apply auth_auth_valid|].
  iExists (TimeG _ _ _ time_global_name time_persist_name time_cumul_name).
  iFrame. iApply inv_alloc. iExists 0%nat, 0%nat. iFrame.
Qed.
