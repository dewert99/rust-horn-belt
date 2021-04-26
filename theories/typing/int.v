From lrust.typing Require Export type.
From lrust.typing Require Import bool programs.
Set Default Proof Using "Type".
Open Scope Z_scope.

Implicit Type z: Z.

Section int.
  Context `{!typeG Σ}.

  Program Definition int: type Z :=
    {| pt_size := 1;  pt_own z _ vl := ⌜vl = [ #z]⌝; |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance int_send: Send int. Proof. done. Qed.

  Lemma bool_ty_to_int E L : subtype E L Z_of_bool bool_ty int.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. by iIntros.
  Qed.

  Lemma type_int_instr z : typed_val #z int (λ post, post z).
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ Obs". iMod persist_time_rcpt_0 as "time".
    iApply wp_value. iExists -[const z]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "time". by iExists z.
  Qed.

  Lemma type_int {Al} z E L C (T: _ Al) x e tr :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ int +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := #z in e) (λ al, tr (z -:: al)).
  Proof. iIntros. iApply type_let; by [apply type_int_instr|solve_typing]. Qed.

  Lemma type_plus_instr E L p1 p2 :
    ⊢ typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 + p2) int
      (λ post '(-[z; z']), post (z + z')).
  Proof.
    iIntros (??(?&?&[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros (? d _) "time". iIntros ((z &->&[=->])).
    wp_apply (wp_hasty with "p2"). iIntros (?? _) "_". iIntros ((z' &->&[=->])).
    wp_op. iExists -[const (z + z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "time". by iExists (z + z').
  Qed.

  Lemma type_plus {Al Bl} E L C (T: _ Al) (T': _ Bl) p1 p2 x e tr pre :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' tr →
    (∀v: val, typed_body E L C (v ◁ int +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := p1 + p2 in e)
      (tr (λ '(z -:: z' -:: bl), pre (z + z' -:: bl))).
  Proof.
    iIntros. iApply type_let; [iApply type_plus_instr|solve_typing| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

  Lemma type_minus_instr E L p1 p2 :
    ⊢ typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 - p2) int
      (λ post '(-[z; z']), post (z - z')).
  Proof.
    iIntros (??(?&?&[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros (? d _) "time". iIntros ((z &->&[=->])).
    wp_apply (wp_hasty with "p2"). iIntros (?? _) "_". iIntros ((z' &->&[=->])).
    wp_op. iExists -[const (z - z')]. iFrame "Obs". rewrite right_id
    tctx_hasty_val'; [|done]. iExists d. iFrame "time". by iExists (z - z').
  Qed.

  Lemma type_minus {Al Bl} E L C (T: _ Al) (T': _ Bl) p1 p2 x e tr pre :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' tr →
    (∀v: val, typed_body E L C (v ◁ int +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := p1 - p2 in e)
      (tr (λ '(z -:: z' -:: bl), pre (z - z' -:: bl))).
  Proof.
    iIntros. iApply type_let; [iApply type_minus_instr|solve_typing| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

  Lemma type_le_instr E L p1 p2 :
    ⊢ typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 ≤ p2) bool_ty
      (λ post '(-[z; z']), post (bool_decide (z ≤ z'))).
  Proof.
    iIntros (??(?&?&[])) "_ _ _ _ _ $$ (p1 & p2 &_) Obs".
    wp_apply (wp_hasty with "p1"). iIntros (? d _) "time". iIntros ((z &->&[=->])).
    wp_apply (wp_hasty with "p2"). iIntros (?? _) "_". iIntros ((z' &->&[=->])).
    wp_op. iExists -[const (bool_decide (z <= z'))]. iFrame "Obs".
    rewrite right_id tctx_hasty_val'; [|done]. iExists d.
    iFrame "time". by iExists (bool_decide (z <= z')).
  Qed.

  Lemma type_le {Al Bl} E L C (T: _ Al) (T': _ Bl) p1 p2 x e tr pre :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p1 ◁ int; p2 ◁ int] T T' tr →
    (∀v: val, typed_body E L C (v ◁ bool_ty +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := p1 ≤ p2 in e)
      (tr (λ '(z -:: z' -:: bl), pre (bool_decide (z ≤ z') -:: bl))).
  Proof.
    iIntros. iApply type_let; [iApply type_le_instr|solve_typing| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

End int.
