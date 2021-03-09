Require Import ssreflect FunctionalExtensionality.
From stdpp Require Import prelude.

(** * Utility for Point-Free Style *)

Lemma compose_assoc {A B C D} (f: A → B) (g: B → C) (h: C → D) :
  h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. by rewrite /compose. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).

Lemma surjective_pairing_fun {A B C} (f: A → B * C) :
  f = (pair ∘ (fst ∘ f) ⊛ (snd ∘ f)).
Proof. extensionality x. by rewrite /s_comb /compose -surjective_pairing. Qed.
