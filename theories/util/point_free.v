Require Import ssreflect.
From stdpp Require Import prelude.

(** * Utility for Point-Free Style *)

Lemma compose_assoc {A B C D} (f: A → B) (g: B → C) (h: C → D) :
h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. by rewrite /compose. Qed.

Infix "=ₚ" := (pointwise_relation _ (=)) (at level 70).
Notation "(=ₚ)" := (pointwise_relation _ (=)) (only parsing).

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).

Lemma surjective_pairing_fun {A B C} (f: A → B * C) :
  f =ₚ (pair ∘ (fst ∘ f) ⊛ (snd ∘ f)).
Proof. move=> ?. by rewrite /s_comb /compose -surjective_pairing. Qed.
