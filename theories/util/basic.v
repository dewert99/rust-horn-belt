Require Import ssreflect FunctionalExtensionality.
From stdpp Require Import prelude.
From iris.algebra Require Import ofe monoid.
From iris.proofmode Require Import tactics.

(** * Utility for Natural Numbers *)

Lemma succ_le m n : S m ≤ n ↔ ∃n', n = S n' ∧ m ≤ n'.
Proof. split; [|case; lia]. move: n=> [|n']; [|exists n']; lia. Qed.

(** * Utility for Point-Free Style *)

Ltac fun_ext := apply functional_extensionality.

Class SemiIso {A B} (f: A → B) (g: B → A) := semi_iso: g ∘ f = id.

Class Iso {A B} (f: A → B) (g: B → A) :=
  { iso_semi_iso:> SemiIso f g; iso_semi_iso':> SemiIso g f }.

Global Instance iso_id {A} : Iso (@id A) id. Proof. done. Qed.

Global Instance semi_iso_inj `{!@SemiIso A B f g} : Inj (=) (=) f | 100.
Proof.
  move=> x y Eq. have [<-<-]: (g ∘ f) x = x ∧ (g ∘ f) y = y by rewrite semi_iso.
  by rewrite /= Eq.
Qed.

Lemma compose_assoc {A B C D} (f: A → B) g (h: C → D) : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. done. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).
Global Arguments s_comb {_ _ _} _ _ _ / : assert.
Typeclasses Transparent s_comb.

Lemma surjective_pairing_fun {A B C} (f: A → B * C) : f = pair ∘ (fst ∘ f) ⊛ (snd ∘ f).
Proof. fun_ext=> ?/=. by rewrite -surjective_pairing. Qed.

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

Definition option_to_sum {A} (o: option A) : () + A :=
  match o with None => inl () | Some x => inr x end.
Definition sum_to_option {A} (s: () + A) : option A :=
  match s with inl _ => None | inr x => Some x end.
Global Instance option_sum_iso {A} : Iso (@option_to_sum A) sum_to_option.
Proof. split; fun_ext; case=>//; by case. Qed.

Definition list_to_option {A} (xl: list A) : option (A * list A) :=
  match xl with [] => None | x :: xl' => Some (x, xl') end.
Definition option_to_list {A} (o: option (A * list A)) : list A :=
  match o with None => [] | Some (x, xl') => x :: xl' end.
Global Instance list_option_iso {A} : Iso (@list_to_option A) option_to_list.
Proof. split; fun_ext; case=>//; by case. Qed.

(* * Utility for Singleton Types *)

Class Unique A := { unique: A; eq_unique: ∀x: A, x = unique }.

Program Global Instance unit_unique: Unique () := {| unique := () |}.
Next Obligation. by case. Qed.

Program Global Instance prod_unique `{!Unique A, Unique B}
  : Unique (A * B) := {| unique := (unique, unique) |}.
Next Obligation. move=> ????. case=> *; f_equal; apply eq_unique. Qed.

Program Global Instance fun_unique {B} `{!Unique A}
  : Unique (B → A) := {| unique := const unique |}.
Next Obligation. move=> *. fun_ext=>/= ?. apply eq_unique. Qed.

Global Instance unique_iso `{!Unique A, Unique B} : @Iso A B unique unique.
Proof. split; fun_ext=>/= ?; symmetry; apply eq_unique. Qed.

(** * Utility for voidness *)

Global Instance Empty_set_empty: Empty Type := Empty_set.

Class Void A := absurd: ∀{B}, A → B.

Global Instance Empty_set_void: Void ∅. Proof. by move. Qed.

Global Instance fun_void `{!Inhabited A, Void B} : Void (A → B).
Proof. move=> ? /(.$ inhabitant) ?. by apply absurd. Qed.

Program Global Instance void_fun_unique {B} `{!Void A}
  : Unique (A → B) := {| unique := absurd |}.
Next Obligation. move=> *. fun_ext=> ?. by apply absurd. Qed.

Global Instance void_iso `{!Void A, Void B} : Iso absurd absurd.
Proof. split; fun_ext=> ?; by apply absurd. Qed.

(** * OFE *)

Notation "(≡{ n }≡)" := (dist n) (only parsing).
Notation "(≡{ n }≡@{ A } )" := (@dist A _ n) (only parsing).

(** * Monoid *)

Global Instance and_monoid: Monoid and := {| monoid_unit := True |}.

(** * Iris *)

Notation big_sepL := (big_opL bi_sep) (only parsing).

Class IntoFromSep {PROP: bi} (P Q Q': PROP) :=
  { into_from_sep_into:> IntoSep P Q Q'; into_from_sep_from:> FromSep P Q Q' }.
Lemma get_into_from_sep {PROP: bi} (P Q Q': PROP) : P ⊣⊢ Q ∗ Q' → IntoFromSep P Q Q'.
Proof. move=> Eq. split; [rewrite /IntoSep|rewrite /FromSep]; by rewrite Eq. Qed.

(* Applicative Functors *)

Class Ap (M : Type → Type) := ap : ∀ {A B}, M (A → B) → M A → M B.

Infix "<*>" := ap (at level 61, left associativity).

(* Reader Monad  *)

Global Instance reader_fmap R : FMap ((→) R) := λ _ _ f a r, f (a r).
Global Instance reader_ap R : Ap ((→) R) := λ _ _ f a r, f r (a r).
Global Instance reader_mret R : MRet ((→) R) := λ _ a _, a.
Global Instance reader_mbind R : MBind ((→) R) := λ _ _ f a r, f (a r) r.
Global Instance reader_mjoin R : MJoin ((→) R) := λ _ j r, j r r.

Lemma reader_fmap_ret R A B (f : A → B) (a : A) : f <$> (@mret ((→) R) _ _ a) = @mret ((→) R) _ _ (f a).
by rewrite /mret /reader_mret /fmap /reader_fmap.
Qed.