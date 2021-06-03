From lrust.typing Require Export type.
From lrust.typing Require Import product.
Set Default Proof Using "Type".

Section uninit.
  Context `{!typeG Σ}.

  Program Definition uninit n : type () :=
    {| pt_size := n; pt_own _ _ vl := ⌜length vl = n⌝ |}%I.
  Next Obligation. done. Qed.
End uninit.

Notation "↯" := uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uninit_send n : Send (↯ n).
  Proof. done. Qed.
  Global Instance uninit_sync n : Sync (↯ n).
  Proof. done. Qed.

  Lemma uninit_leak n E L : leak E L (↯ n) (const True).
  Proof. apply leak_just. Qed.

  (* TODO: Prove this after the model update *)
  Lemma uninit_unit E L :
    eqtype E L (↯ 0) (()) (const ()) (const ()).
  Admitted.

  (* TODO: Prove this after the model update *)
  Lemma uninit_plus_prod E L m n :
    eqtype E L (↯ (m + n)) (↯ m * ↯ n) (const ((), ())) (const ()).
  Admitted.
End typing.

Global Hint Resolve uninit_leak : lrust_typing.
