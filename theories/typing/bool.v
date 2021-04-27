From lrust.typing Require Export type.
From lrust.typing Require Import programs.

Set Default Proof Using "Type".

Implicit Type b: boolₛ.

Section bool.
  Context `{!typeG Σ}.

  Program Definition bool_ty: type boolₛ :=
    {| pt_size := 1;  pt_own b _ vl := ⌜vl = [ #b]⌝; |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance bool_send: Send bool_ty. Proof. done. Qed.

  Lemma type_bool_instr b : typed_val #b bool_ty (λ post, post b).
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ Obs". iMod persist_time_rcpt_0 as "Time".
    iApply wp_value. iExists -[const b]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "Time". by iExists b.
  Qed.

  Lemma type_bool {Al} b E L C (T: _ Al) x e tr:
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ bool_ty +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := #b in e) (λ al, tr (b -:: al)).
  Proof. iIntros. iApply type_let; by [apply type_bool_instr|solve_typing]. Qed.

  Lemma type_if {Al Bl} p (T: _ Al) (T': _ Bl) e1 e2 pre1 pre2 tr E L C :
    tctx_extract_ctx E L +[p ◁ bool_ty] T T' tr →
    typed_body E L C T' e1 pre1 -∗ typed_body E L C T' e2 pre2 -∗
    typed_body E L C T (if: p then e1 else e2)
      (tr (λ '(b -:: vl), if b then pre1 vl else pre2 vl)).
  Proof.
    iIntros (?) "e1 e2". iApply typed_body_tctx_incl; [done|]. iIntros (?[??]).
    iIntros "#LFT #TIME #PROPH #UNIQ #E Na L C [p T] Obs". wp_bind p.
    iApply (wp_hasty with "p"). iIntros (?? _) "_".
    iDestruct 1 as ([|]->) "%Eq"; move: Eq=> [=->]; wp_case.
    - by iApply ("e1" with "LFT TIME PROPH UNIQ E Na L C T").
    - by iApply ("e2" with "LFT TIME PROPH UNIQ E Na L C T").
  Qed.

End bool.
