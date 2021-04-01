Require Import FunctionalExtensionality Equality.
From iris.proofmode Require Import tactics.
From lrust.util Require Import types.
From lrust.typing Require Import product.
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
    iMod (bor_persistent with "LFT Bor' Tok") as "[>%Eq Tok]"; [done|].
    iApply step_fupdN_intro; [done|]. iIntros "!>!>".
    iMod (upd_uninit_shr with "LFT Bor") as "$"; done.
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

  Lemma list_sep_length {A} (xl: list A) m n :
    length xl = m + n → ∃yl zl, xl = yl ++ zl ∧ length yl = m ∧ length zl = n.
  Proof.
    move: xl. elim m; [by exists [], xl|]=> ? IH [|x xl]; [done|]=> [=Eq].
    case (IH xl Eq)=> [yl[zl[->[??]]]]. exists (x :: yl), zl.
    split; [done|]. split; [|done]=>/=. by f_equal.
  Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L (const ((), ())) (const ()) (uninit (m + n)) (uninit m * uninit n).
  Proof.
    apply eqtype_unfold. { split; extensionality x; by [case x=> [[][]]|case x]. }
    iIntros (?) "_!>_ /=". iSplit; [done|]. iSplit; [by iApply lft_equiv_refl|].
    iSplit; iIntros "!> *".
    - iSplit.
      + iIntros (Eq). move: Eq=> /list_sep_length[wl[wl'[->[??]]]]. by iExists wl, wl'.
      + iDestruct 1 as (??->?) "%". rewrite app_length. iPureIntro. by f_equal.
    - iInduction m as [|m] "IH" forall (l)=>/=.
      { rewrite left_id shift_loc_0. by iApply (bi.iff_refl True%I). }
      rewrite -Nat.add_1_l -shift_loc_assoc_nat. iSplit.
      + iDestruct 1 as "[$?]". by iApply "IH".
      + iDestruct 1 as "[[$?]?]". iApply "IH". iFrame.
  Qed.

End uninit.
