Require Import ssreflect ProofIrrelevance.

Ltac proof_subst x y :=
  (have ?: x = y by apply proof_irrelevance); subst x.
