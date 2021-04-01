From iris.proofmode Require Import tactics.
From lrust.util Require Import types.
From lrust.typing Require Import mod_ty product.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit1 : type unit :=
    {| pt_size := 1;  pt_own _ _ vl := ⌜length vl = 1⌝%I |}.
  Next Obligation. by iIntros. Qed.
  Global Instance uninit1_send : Send uninit1. Proof. done. Qed.

  Definition uninit n : type unit := <{const ()}> (Π (hrepeat uninit1 n)).

End uninit.
