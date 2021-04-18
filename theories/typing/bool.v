From lrust.typing Require Export type.
From lrust.typing Require Import programs.
From lrust.util Require Import types.

(* From lrust.util Require Import types. *)

Set Default Proof Using "Type".

Implicit Type b: bool.

Section bool.
  Context `{!typeG Σ}.

  Program Definition bool_ty: type bool :=
    {| pt_size := 1;  pt_own b _ vl := ⌜vl = [ #b]⌝; |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance bool_send: Send bool_ty. Proof. done. Qed.

  Lemma type_bool_instr b : typed_val #b bool_ty (λ post _, post -[b]).
  Proof.
    iIntros (?????) "_ _ _ $$ _ ?". iMod persistent_time_receipt_0 as "#H0".
    iApply wp_value. iExists -[const b]. iFrame.
    rewrite tctx_interp_singleton tctx_hasty_val' //.
    iExists 0%nat. iFrame "H0". by iExists b.
  Qed.

  Lemma type_bool {As} b E L C (T: _ As) x e pre:
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ bool_ty +:: T) (subst' x v e) pre) -∗
    typed_body E L C T (let: x := #b in e) (λ p, pre (b -:: p)).
  Proof.
    iIntros. iApply typed_body_impl; last first.
    { iApply type_let; by [apply type_bool_instr|solve_typing| |]. } done.
  Qed.

  Lemma type_if {As} E L C (T : tctx As) e1 e2 p pre1 pre2:
    typed_body E L C T e1 pre1 -∗ typed_body E L C T e2 pre2 -∗
    typed_body E L C (p ◁ bool_ty +:: T) (if: p then e1 else e2)
      (λ '(b -:: vl), if b then pre1 vl else pre2 vl).
  Proof.
    iIntros "He1 He2". iIntros (tid [bπ vπl]). rewrite tctx_interp_cons.
    iIntros "#LFT #TIME #HE Htl HL HC [Hp HT] Hv". wp_bind p.
    iApply (wp_hasty with "Hp"). iIntros (??) "_".
    iDestruct 1 as (b->) "%Eq". move: Eq=> [=->]. wp_case. case b.
    - by iApply ("He1" with "LFT TIME HE Htl HL HC HT").
    - by iApply ("He2" with "LFT TIME HE Htl HL HC HT").
  Qed.

End bool.
