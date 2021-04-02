Require Import FunctionalExtensionality Equality.
From iris.proofmode Require Import tactics.
From lrust.util Require Import types.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Fixpoint uninit_shr n κ l := (match n with 0 => True |
    S m => (∃v, &frac{κ} (λ q, l ↦{q} v)) ∗ uninit_shr m κ (l +ₗ 1) end)%I.

  Lemma upd_uninit_shr E vl n κ l : ↑lftN ⊆ E →
    length vl = n → lft_ctx -∗ &{κ} (l ↦∗ vl) ={E}=∗ uninit_shr n κ l.
  Proof.
    move=> ?. move: vl l. elim n; [by iIntros|]=> ? IH [|v?]; [done|]=> > [=?].
    rewrite heap_mapsto_vec_cons. iIntros "#LFT Bor".
    iMod (bor_sep with "LFT Bor") as "[Head Tail]"; [done|].
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT Head") as "Head"; [done|].
    iMod (IH with "LFT Tail") as "$"; [done|]. iModIntro. iExists v. iFrame.
  Qed.

  Program Definition uninit n : type unit := {|
    ty_size := n;  ty_lfts := [];  ty_E := [];  ty_own _ _ vl := ⌜length vl = n⌝;
    ty_shr _ κ _ l := uninit_shr n κ l;
  |}%I.
  Next Obligation.
    move=>/= n _ ? _. elim n; [apply _|]=>/= *. apply bi.sep_persistent; apply _.
  Qed.
  Next Obligation. by iIntros. Qed. Next Obligation. by iIntros. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation.
    move=>/= n ? ? _ _. elim n; [by iIntros|]=> ? IH ?. iIntros "#? [One ?]".
    iDestruct "One" as (v) "#?". iSplit.
    { iExists v. by iApply frac_bor_shorten. } by iApply IH.
  Qed.
  Next Obligation.
    move=>/= *. iIntros "#LFT #In Bor Tok".
    iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor Bor']"; [done|].
    iMod (bor_persistent with "LFT Bor' Tok") as "[>% ?]"; [done|].
    iApply step_fupdN_intro; [done|].
    by iMod (upd_uninit_shr with "LFT Bor") as "$".
  Qed.
  Next Obligation.
    iIntros. iApply step_fupdN_intro; [done|]. iIntros "!>!>!>".
    iExists [], 1%Qp. iSplit. { iPureIntro. apply proph_dep_unit. }
    iSplit; [done|]. iIntros "_ !>". by iSplit.
  Qed.
  Next Obligation.
    iIntros. iApply step_fupdN_intro; [done|]. iIntros "!>!>!>!>!>".
    iExists [], 1%Qp. iSplit. { iPureIntro. apply proph_dep_unit. }
    iSplit; [done|]. iIntros "_ !>". iFrame.
  Qed.

  Global Instance uninit_copy n : Copy (uninit n).
  Proof.
    split; [apply _|]=> ????? l q ? /=. move: l q. elim n=> [|? IH].
    - move=> *. iIntros "_ _ Na $ !>". iExists 1%Qp, []. rewrite heap_mapsto_vec_nil.
      iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [solve_ndisj|].
      do 2 (iSplit; [done|]). iIntros "Na". by iDestruct ("ToNa" with "Na") as "$".
    - move=> ?? HF.
      iIntros "#LFT [Bor Shr] Na [Tok Tok']". iDestruct "Bor" as (v) "Bor".
      iMod (frac_bor_acc with "LFT Bor Tok") as (q) "[>Mt Close]"; [solve_ndisj|].
      iMod (IH with "LFT Shr Na Tok'") as (q' vl) "[Na[Mt'[>%Eq Close']]]".
      { move: HF. rewrite -Nat.add_1_l -Nat.add_assoc shr_locsE_shift. set_solver+. }
      iDestruct (na_own_acc with "Na") as "[$ ToNa]".
      { rewrite -Nat.add_1_l shr_locsE_shift. set_solver+. }
      case (Qp_lower_bound q q')=> [q''[?[?[->->]]]]. iModIntro. iExists q'', (v :: vl).
      rewrite heap_mapsto_vec_cons. iDestruct "Mt" as "[$ Mtr]".
      iDestruct "Mt'" as "[$ Mtr']". iSplit. { iPureIntro. by rewrite /= Eq. }
      iIntros "Na [Mt Mt']". iDestruct ("ToNa" with "Na") as "Na".
      iMod ("Close" with "[$Mt $Mtr]") as "$".
      by iMod ("Close'" with "Na [$Mt' $Mtr']") as "[$$]".
  Qed.

  Global Instance uninit_send n : Send (uninit n). Proof. done. Qed.
  Global Instance uninit_sync n : Sync (uninit n). Proof. done. Qed.

End uninit.
