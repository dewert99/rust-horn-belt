Require Import ssreflect FunctionalExtensionality.
From stdpp Require Import prelude.

(** * Utility for Natural Numbers *)

Lemma succ_le m n : S m ≤ n → ∃n', n = S n' ∧ m ≤ n'.
Proof. move: n=> [|n]=> Le; [|exists n]; lia. Qed.

(** * Utility for Lists *)

Lemma list_sep_length {A} (xl: list A) m n :
  length xl = m + n → ∃yl zl, xl = yl ++ zl ∧ length yl = m ∧ length zl = n.
Proof.
  move: xl. elim m; [by exists [], xl|]=> ? IH [|x xl]; [done|]=> [=Eq].
  case (IH xl Eq)=> [yl[zl[->[??]]]]. exists (x :: yl), zl.
  split; [done|]. split; [|done]=>/=. by f_equal.
Qed.

(** * Utility for Point-Free Style *)

Ltac fun_ext := apply functional_extensionality.

Class SemiIso {A B} (f: A → B) (g: B → A) := semi_iso: g ∘ f = id.

Class Iso {A B} (f: A → B) (g: B → A) := { iso:> SemiIso f g; iso':> SemiIso g f }.

Global Instance iso_id {A} : Iso (@id A) id. Proof. done. Qed.

Global Instance semi_iso_inj `{@SemiIso A B f g} : Inj (=) (=) f | 100.
Proof.
  move=> x y Eq. have [<-<-]: (g ∘ f) x = x ∧ (g ∘ f) y = y.
  { by rewrite semi_iso. } by rewrite /= Eq.
Qed.

Lemma compose_assoc {A B C D} (f: A → B) g (h: C → D) : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. done. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).

Lemma surjective_pairing_fun {A B C} (f: A → B * C) : f = (pair ∘ (fst ∘ f) ⊛ (snd ∘ f)).
Proof. fun_ext=> ?. by rewrite /s_comb /compose -surjective_pairing. Qed.

Definition prod_assoc {A B C} '((x, (y, z))) : (A * B) * C := ((x, y), z).
Definition prod_assoc' {A B C} '(((x, y), z)) : A * (B * C) := (x, (y, z)).
Global Instance prod_assoc_iso {A B C} : Iso (@prod_assoc A B C) prod_assoc'.
Proof. split; fun_ext; by [case=> [?[??]]|case=> [[??]?]]. Qed.

Definition prod_left_id {A} '(((), x)) : A := x.
Definition prod_left_id' {A} (x: A) := ((), x).
Global Instance prod_left_id_iso {A} : Iso (@prod_left_id A) prod_left_id'.
Proof. split; fun_ext; by [case=> [[]?]|]. Qed.

Definition prod_right_id {A} '((x, ())) : A := x.
Definition prod_right_id' {A} (x: A) := (x, ()).
Global Instance prod_right_id_iso {A} : Iso (@prod_right_id A) prod_right_id'.
Proof. split; fun_ext; by [case=> [?[]]|]. Qed.

(* * Utility for Singleton Types *)

Class Unique A := { unique: A; eq_unique: ∀x: A, x = unique }.

Program Global Instance unit_unique: Unique () := {| unique := () |}.
Next Obligation. by move=> []. Qed.

Program Global Instance prod_unique `{Unique A, Unique B}
  : Unique (A * B) := {| unique := (unique, unique) |}.
Next Obligation. move=> ????. case=> [??]; f_equal; apply eq_unique. Qed.

Program Global Instance fun_unique {B} `{Unique A}
  : Unique (B → A) := {| unique := const unique |}.
Next Obligation. move=> *. fun_ext=>/= ?. apply eq_unique. Qed.

Global Instance unique_iso `{Unique A, Unique B} : @Iso A B unique unique.
Proof. split; fun_ext=>/= ?; symmetry; apply eq_unique. Qed.

(** * Utility for Empty_set *)

Global Instance Empty_set_empty: Empty Type := Empty_set.
Definition absurd {A} (x: ∅) : A := match x with end.
