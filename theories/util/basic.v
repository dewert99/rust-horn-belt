Require Export Equality FunctionalExtensionality.
From iris.prelude Require Import prelude.
From iris.algebra Require Import ofe monoid.
From iris.proofmode Require Import tactics.

(** * Utility for Natural Numbers *)

Lemma succ_le m n : S m ≤ n ↔ ∃n', n = S n' ∧ m ≤ n'.
Proof. split; [|case; lia]. move: n=> [|n']; [|exists n']; lia. Qed.

Global Instance eq_nat_sym : Symmetric eq_nat.
Proof. move=> ??. by rewrite !eq_nat_is_eq. Qed.

(** * Utility for Vectors *)

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.

(** * Utility for Lists *)

(** List.nth with better pattern matching *)
Fixpoint lnth {A} (d: A) (xl: list A) (i: nat) : A := match xl with
  [] => d | x :: xl' => match i with 0 => x | S j => lnth d xl' j end end.

Notation lnthe := (lnth ∅).

(** * Utility for Point-Free Style *)

Ltac fun_ext := apply functional_extensionality.

Class SemiIso {A B} (f: A → B) (g: B → A) := semi_iso: g ∘ f = id.

Class Iso {A B} (f: A → B) (g: B → A) :=
  { iso_semi_iso:> SemiIso f g; iso_semi_iso':> SemiIso g f }.

Global Instance iso_id {A} : Iso (@id A) id. Proof. done. Qed.

Global Instance semi_iso_inj `{!@SemiIso A B f g} : Inj (=) (=) f | 100.
Proof.
  move=> x y Eq. have [<-<-]: (g ∘ f) x = x ∧ (g ∘ f) y = y by rewrite semi_iso.
  by rewrite/= Eq.
Qed.

Lemma compose_assoc {A B C D} (f: A → B) g (h: C → D) : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. done. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).
Global Arguments s_comb {_ _ _} _ _ _ / : assert.
Typeclasses Transparent s_comb.

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

Program Global Instance prod_unique `{!Unique A, !Unique B}
  : Unique (A * B) := {| unique := (unique, unique) |}.
Next Obligation. move=> ????. case=> *; f_equal; apply eq_unique. Qed.

Program Global Instance fun_unique {B} `{!Unique A}
  : Unique (B → A) := {| unique := const unique |}.
Next Obligation. move=> *. fun_ext=>/= ?. apply eq_unique. Qed.

Global Instance unique_iso `{!Unique A, !Unique B} : @Iso A B unique unique.
Proof. split; fun_ext=>/= ?; symmetry; apply eq_unique. Qed.

(** * Utility for voidness *)

Global Instance Empty_set_empty: Empty Set := Empty_set.
Global Instance Empty_set_empty': Empty Type := Empty_set.

Class Void A := absurd: ∀{B}, A → B.

Global Instance Empty_set_void: Void ∅. Proof. by move. Qed.
Global Instance False_void: Void False. Proof. by move. Qed.

Global Instance fun_void `{!Inhabited A, !Void B} : Void (A → B).
Proof. move=> ? /(.$ inhabitant) ?. by apply absurd. Qed.

Program Global Instance void_fun_unique {B} `{!Void A}
  : Unique (A → B) := {| unique := absurd |}.
Next Obligation. move=> *. fun_ext=> ?. by apply absurd. Qed.

Global Instance void_iso `{!Void A, !Void B} : Iso absurd absurd.
Proof. split; fun_ext=> ?; by apply absurd. Qed.

(** * OFE *)

Notation "(≡{ n }≡)" := (dist n) (only parsing).
Notation "(≡{ n }@{ A }≡)" := (@dist A _ n) (only parsing).

(** * Iris *)

Notation big_sepL := (big_opL bi_sep) (only parsing).

Lemma big_sepL_forall' `{!BiAffine PROP} {A} (Φ: A → PROP) l :
  (∀x, Persistent (Φ x)) →
  ([∗ list] x ∈ l, Φ x) ⊣⊢ ∀x, ⌜x ∈ l⌝ → Φ x.
Proof.
  move=> ?. elim l. { iSplit; [|by iIntros]. iIntros "_" (? In). inversion In. }
  move=>/= ?? ->. setoid_rewrite elem_of_cons. iSplit.
  - iIntros "[? To]" (?[->|?]); by [|iApply "To"].
  - iIntros "To". iSplit; [|iIntros (??)]; iApply "To"; by [iLeft|iRight].
Qed.
