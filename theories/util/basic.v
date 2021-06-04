Require Export Equality FunctionalExtensionality.
From iris.algebra Require Import ofe.
From iris.proofmode Require Import tactics.

(** * Utility for Point-Free Style *)

Ltac fun_ext := apply functional_extensionality.

Class SemiIso {A B} (f: A → B) (g: B → A) := semi_iso: g ∘ f = id.

Lemma semi_iso' {A B} f g `{!@SemiIso A B f g} x : g (f x) = x.
Proof. have ->: g (f x) = (g ∘ f) x by done. by rewrite semi_iso. Qed.

Class Iso {A B} (f: A → B) (g: B → A) :=
  { iso_semi_iso_l :> SemiIso f g; iso_semi_iso_r :> SemiIso g f }.

Global Instance iso_id {A} : Iso (@id A) id.
Proof. done. Qed.

Global Instance semi_iso_inj `{!@SemiIso A B f g} : Inj (=) (=) f | 100.
Proof. move=> ?? /(f_equal g). by rewrite !semi_iso'. Qed.

Lemma compose_assoc {A B C D} (f: A → B) g (h: C → D) : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. done. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).
Global Arguments s_comb {_ _ _} _ _ _ / : assert.
Typeclasses Transparent s_comb.

(** * Utility for voidness *)

Global Instance Empty_set_empty: Empty Set := Empty_set.
Global Instance Empty_set_empty': Empty Type := Empty_set.

Class Void A := absurd: ∀{B}, A → B.

Global Instance Empty_set_void: Void ∅.
Proof. by move. Qed.
Global Instance False_void: Void False.
Proof. by move. Qed.

Global Instance fun_void `{!Inhabited A, !Void B} : Void (A → B).
Proof. move=> ? /(.$ inhabitant) ?. by apply absurd. Qed.

Global Instance void_iso `{!Void A, !Void B} : Iso absurd absurd.
Proof. split; fun_ext=> ?; by apply absurd. Qed.

(** * Utility for Iris *)

Notation big_sepL := (big_opL bi_sep) (only parsing).

(** * Utility for Natural Numbers *)

Lemma succ_le m n : S m ≤ n ↔ ∃n', n = S n' ∧ m ≤ n'.
Proof. split; [|case; lia]. move: n=> [|n']; [|exists n']; lia. Qed.

Global Instance eq_nat_sym : Symmetric eq_nat.
Proof. move=> ??. by rewrite !eq_nat_is_eq. Qed.

(** * Utility for Booleans *)

Lemma negb_andb b c : negb (b && c) = negb b || negb c.
Proof. by case b; case c. Qed.
Lemma negb_orb b c : negb (b || c) = negb b && negb c.
Proof. by case b; case c. Qed.
Lemma negb_negb_orb b c : negb (negb b || c) = b && negb c.
Proof. by case b; case c. Qed.

(** * Utility for Pairs *)

Lemma surjective_pairing_fun {A B C} (f: A → B * C) : f = pair ∘ (fst ∘ f) ⊛ (snd ∘ f).
Proof. fun_ext=> ?/=. by rewrite -surjective_pairing. Qed.

Definition prod_assoc {A B C} '(x, (y, z)) : (A * B) * C := ((x, y), z).
Definition prod_assoc' {A B C} '((x, y), z) : A * (B * C) := (x, (y, z)).
Global Instance prod_assoc_iso {A B C} : Iso (@prod_assoc A B C) prod_assoc'.
Proof. split; fun_ext; by [case=> [?[??]]|case=> [[??]?]]. Qed.

Definition prod_left_id {A} '((), x) : A := x.
Definition prod_left_id' {A} (x: A) := ((), x).
Global Instance prod_left_id_iso {A} : Iso (@prod_left_id A) prod_left_id'.
Proof. split; fun_ext; by [case=> [[]?]|]. Qed.

Definition prod_right_id {A} '(x, ()) : A := x.
Definition prod_right_id' {A} (x: A) := (x, ()).
Global Instance prod_right_id_iso {A} : Iso (@prod_right_id A) prod_right_id'.
Proof. split; fun_ext; by [case=> [?[]]|]. Qed.

(** * Utility for Lists *)

(** List.nth with better pattern matching *)
Fixpoint lnth {A} (d: A) (xl: list A) (i: nat) : A :=
  match xl with
  | [] => d
  | x :: xl' => match i with 0 => x | S j => lnth d xl' j end
  end.
Notation lnthe := (lnth ∅).

Lemma lnth_default {A} D (As : list A) i :
  length As <= i → D = lnth D As i.
Proof.
  generalize dependent As.
  induction i; destruct As; simpl; intros; auto with lia.
Qed.

Definition lapply {A B} (fl: list (B → A)) (x: B) : list A := map (.$ x) fl.

(** Fixpoint version of List.Forall *)
Fixpoint lforall {A} (Φ: A → Prop) (xl: list A) : Prop :=
  match xl with [] => True | x :: xl' => Φ x ∧ lforall Φ xl' end.

Section forall2b. Context {A B} (f: A → B → bool).
Fixpoint forall2b (xl: list A) (yl: list B) :=
  match xl, yl with
  | [], [] => true
  | x :: xl', y :: yl' => f x y && forall2b xl' yl'
  | _, _ => false
  end.
End forall2b.

Definition list_to_option {A} (xl: list A) : option (A * list A) :=
  match xl with [] => None | x :: xl' => Some (x, xl') end.
Definition option_to_list {A} (o: option (A * list A)) : list A :=
  match o with None => [] | Some (x, xl') => x :: xl' end.
Global Instance list_option_iso {A} : Iso (@list_to_option A) option_to_list.
Proof. split; fun_ext; case=>//; by case. Qed.
