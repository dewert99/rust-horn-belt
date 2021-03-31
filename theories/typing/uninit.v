Require Import FunctionalExtensionality.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit1 : type unit :=
    {| pt_size := 1;  pt_own _ _ vl := ⌜length vl = 1⌝%I |}.
  Next Obligation. by iIntros. Qed.
  Global Instance uninit1_send : Send uninit1. Proof. done. Qed.

End uninit.
