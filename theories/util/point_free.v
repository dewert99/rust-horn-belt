Require Import ssreflect.
From stdpp Require Import prelude.

(** * Utility for Point-Free Style *)

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Global Infix "⊛" := (s_comb) (left associativity, at level 50).

Lemma surjective_pairing_fun {A B C} (f: A → B * C) :
  pointwise_relation _ (=) f (pair ∘ (fst ∘ f) ⊛ (snd ∘ f)).
Proof. move=> ?. by rewrite /s_comb /compose -surjective_pairing. Qed.
