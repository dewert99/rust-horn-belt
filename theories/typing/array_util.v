From lrust.typing Require Export type.
Set Default Proof Using "Type".

Notation "l +ₗ[ ty ] i" := (l%L +ₗ Z.of_nat (i%nat * ty.(ty_size))%nat)
  (format "l  +ₗ[ ty ]  i", at level 50, left associativity) : loc_scope.
