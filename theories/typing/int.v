From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
(* From lrust.typing Require Import bool programs. *)
Set Default Proof Using "Type".

Section int.
  Context `{!typeG Σ}.

  Program Definition int: type Z := {|
    pt_size := 1;  pt_own (n: Z) _ vl := ⌜vl = [ #n]⌝;
  |}%I.
  Next Obligation. move=> *. by iIntros (->). Qed.

  Global Instance int_send: Send int.
  Proof. done. Qed.
End int.

(*
Section typing.
  Context `{!typeG Σ}.

  Lemma type_int_instr (z : Z) : typed_val #z int.
  Proof.
    iIntros (E L tid) "_ _ _ $ $ _". iMod persistent_time_receipt_0 as "#H0".
    iApply wp_value. rewrite tctx_interp_singleton tctx_hasty_val' //. auto.
  Qed.

  Lemma type_int (z : Z) E L C T x e :
    Closed (x :b: []) e →
    (∀ (v : val), typed_body E L C ((v ◁ int) :: T) (subst' x v e)) -∗
    typed_body E L C T (let: x := #z in e).
  Proof. iIntros. iApply type_let; [apply type_int_instr|solve_typing|done]. Qed.

  Lemma type_plus_instr E L p1 p2 :
    ⊢ typed_instruction_ty E L [p1 ◁ int; p2 ◁ int] (p1 + p2) int.
  Proof.
    iIntros (tid) "_ _ _ $ $ [Hp1 [Hp2 _]]". iMod persistent_time_receipt_0 as "#H0".
    wp_apply (wp_hasty with "Hp1"). iIntros (? [[]|]) "_ _ H1"; try done.
    wp_apply (wp_hasty with "Hp2"). iIntros (? [[]|]) "_ _ H2"; try done.
    wp_op. rewrite tctx_interp_singleton tctx_hasty_val' //. auto.
  Qed.

  Lemma type_plus E L C T T' p1 p2 x e :
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p1 ◁ int; p2 ◁ int] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ int) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := p1 + p2 in e).
  Proof. iIntros. iApply type_let; [iApply type_plus_instr|solve_typing|done]. Qed.

  Lemma type_minus_instr E L p1 p2 :
    ⊢ typed_instruction_ty E L [p1 ◁ int; p2 ◁ int] (p1 - p2) int.
  Proof.
    iIntros (tid) "_ _ _ $ $ [Hp1 [Hp2 _]]". iMod persistent_time_receipt_0 as "#H0".
    wp_apply (wp_hasty with "Hp1"). iIntros (? [[]|]) "_ _ H1"; try done.
    wp_apply (wp_hasty with "Hp2"). iIntros (? [[]|]) "_ _ H2"; try done.
    wp_op. rewrite tctx_interp_singleton tctx_hasty_val' //. auto.
  Qed.

  Lemma type_minus E L C T T' p1 p2 x e :
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p1 ◁ int; p2 ◁ int] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ int) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := p1 - p2 in e).
  Proof. iIntros. iApply type_let; [apply type_minus_instr|solve_typing|done]. Qed.

  Lemma type_le_instr E L p1 p2 :
    ⊢ typed_instruction_ty E L [p1 ◁ int; p2 ◁ int] (p1 ≤ p2) bool.
  Proof.
    iIntros (tid) "_ _ _ $ $ [Hp1 [Hp2 _]]". iMod persistent_time_receipt_0 as "#H0".
    wp_apply (wp_hasty with "Hp1"). iIntros (? [[]|]) "_ _ H1"; try done.
    wp_apply (wp_hasty with "Hp2"). iIntros (? [[]|]) "_ _ H2"; try done.
    wp_op; case_bool_decide; rewrite tctx_interp_singleton tctx_hasty_val' //; auto.
  Qed.

  Lemma type_le E L C T T' p1 p2 x e :
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p1 ◁ int; p2 ◁ int] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ bool) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := p1 ≤ p2 in e).
  Proof. iIntros. iApply type_let; [apply type_le_instr|solve_typing|done]. Qed.
End typing.
*)
