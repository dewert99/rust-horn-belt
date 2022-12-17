From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Section ptr.
  Context `{!typeG Σ}.

  Program Definition ptr: type locₛ :=
    {| pt_size := 1;  pt_own (l: locₛ) _ vl := ⌜vl = [ #(LitLoc l)]⌝; |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance ptr_send: Send ptr.
  Proof. done. Qed.

  Lemma ptr_resolve E L : resolve E L ptr (const True).
  Proof. apply resolve_just. Qed.


  Lemma type_ptr_instr (l: loc) : typed_val #l ptr l.
  Proof.
    iIntros (?????) "_ _ _ _ _ $$ _ Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_value. iExists -[const l]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_hasty_val'; [|done]. iExists 0%nat. iFrame "⧖". by iExists l.
  Qed.

  Lemma type_ptr {𝔄l 𝔅} (l: loc) (T: tctx 𝔄l) x e tr E L (C: cctx 𝔅) :
    Closed (x :b: []) e →
    (∀v: val, typed_body E L C (v ◁ ptr +:: T) (subst' x v e) tr) -∗
    typed_body E L C T (let: x := #l in e) (λ post al, tr post (l -:: al)).
  Proof. iIntros. iApply type_let; [apply type_ptr_instr|solve_typing|done..]. Qed.
End ptr.

Global Hint Resolve ptr_resolve : lrust_typing.
