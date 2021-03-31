Require Import FunctionalExtensionality.
From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit (n: nat) : type unit :=
    {| pt_size := n;  pt_own _ _ vl := ⌜length vl = n⌝%I |}.
  Next Obligation. by iIntros. Qed.
  Global Instance uninit_send n : Send (uninit n). Proof. done. Qed.

End uninit.
