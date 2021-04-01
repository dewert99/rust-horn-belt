Require Import ssreflect FunctionalExtensionality.
From stdpp Require Import prelude.

(** * Utility for Natural Numbers *)

Lemma succ_le m n : S m ≤ n → ∃n', n = S n' ∧ m ≤ n'.
Proof. move: n=> [|n'] => Le; [by inversion Le|exists n'; lia]. Qed.

(** * Utility for Point-Free Style *)

Lemma compose_assoc {A B C D} (f: A → B) (g: B → C) (h: C → D) :
  h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. done. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).

Lemma surjective_pairing_fun {A B C} (f: A → B * C) :
  f = (pair ∘ (fst ∘ f) ⊛ (snd ∘ f)).
Proof. extensionality x. by rewrite /s_comb /compose -surjective_pairing. Qed.

Definition pair_map {A B A' B'} (f: A → A') (g: B → B') xy := (f xy.1, g xy.2).

Class SemiIso {A B} (f: A → B) (g: B → A) := semi_iso: g ∘ f = id.
Class Iso {A B} (f: A → B) (g: B → A) := iso: g ∘ f = id ∧ f ∘ g = id.
Global Instance Iso_Split `{@Iso A B f g} : SemiIso f g. Proof. apply iso. Qed.
Global Instance Iso_Split' `{@Iso A B f g} : SemiIso g f. Proof. apply iso. Qed.
Global Instance Iso_id {A} : Iso (@id A) id. Proof. done. Qed.
Global Instance Iso_flip `{@Iso A B f g} : Iso g f | 100. Proof. split; apply iso. Qed.

Definition pair_assoc {A B C} '((x, (y, z))) : (A * B) * C := ((x, y), z).
Definition pair_assoc' {A B C} '(((x, y), z)) : A * (B * C) := (x, (y, z)).
Global Instance pair_assoc_iso {A B C} : Iso (@pair_assoc A B C) pair_assoc'.
Proof. split; extensionality xyz; by [case xyz=> [?[??]]|case xyz=> [[??]?]]. Qed.

Definition pair_left_id {A} '(((), x)) : A := x.
Definition pair_left_id' {A} (x: A) := ((), x).
Global Instance pair_left_id_iso {A} : Iso (@pair_left_id A) pair_left_id'.
Proof. split; extensionality x; by [case x=> [[]?]|]. Qed.

Definition pair_right_id {A} '((x, ())) : A := x.
Definition pair_right_id' {A} (x: A) := (x, ()).
Global Instance pair_right_id_iso {A} : Iso (@pair_right_id A) pair_right_id'.
Proof. split; extensionality x; by [case x=> [?[]]|]. Qed.

Definition absurd {A} (x: Empty_set) : A := match x with end.
