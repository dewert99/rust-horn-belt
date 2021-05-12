Require Export Equality FunctionalExtensionality.
From iris.prelude Require Import prelude.
From iris.algebra Require Import ofe monoid.
From iris.proofmode Require Import tactics.

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

(** * Utility for Lists *)

(** List.nth with better pattern matching *)
Fixpoint lnth {A} (d: A) (xl: list A) (i: nat) : A := match xl with
  [] => d | x :: xl' => match i with 0 => x | S j => lnth d xl' j end end.
Notation lnthe := (lnth ∅).

(** Fixpoint version of List.Forall *)
Fixpoint lforall {A} (Φ: A → Prop) (xl: list A) : Prop :=
  match xl with [] => True | x :: xl' => Φ x ∧ lforall Φ xl' end.

Section forall2b. Context {A B} (f: A → B → bool).
Fixpoint forall2b (xl: list A) (yl: list B) := match xl, yl with [], [] => true
  | x :: xl', y :: yl' => f x y && forall2b xl' yl' | _, _ => false end.
End forall2b.

(** * Utility for Vectors *)

Notation vhd := Vector.hd.
Notation vtl := Vector.tl.
Notation vzip := (vzip_with pair).
Notation vsepat := Vector.splitat.

Fixpoint vfunsep {A B n} : (B → vec A n) → vec (B → A) n :=
  match n with 0 => λ _, [#] | S _ => λ f, (vhd ∘ f) ::: vfunsep (vtl ∘ f) end.

Definition vapply {A B n} (fl: vec (B → A) n) (x: B) : vec A n := vmap (.$ x) fl.

Lemma surjective_vcons {A n} (xl: vec A (S n)) : xl = vhd xl ::: vtl xl.
Proof. by inv_vec xl. Qed.

Lemma vsepat_app {A m n} (xl: _ A (m + n)) :
  xl = (vsepat m xl).1 +++ (vsepat m xl).2.
Proof.
  induction m; [done|]=>/=.
  by rewrite [vsepat _ _]surjective_pairing /= -IHm -surjective_vcons.
Qed.
Lemma vapp_ex {A m n} (xl: _ A (m + n)) : ∃yl zl, xl = yl +++ zl.
Proof. eexists _, _. apply vsepat_app. Qed.

Lemma vzip_with_app {A B C m n} (f: A → B → C) (xl: _ m) (xl': _ n) yl yl' :
  vzip_with f (xl +++ xl') (yl +++ yl') = vzip_with f xl yl +++ vzip_with f xl' yl'.
Proof. induction xl; inv_vec yl; [done|]=>/= ??. by rewrite IHxl. Qed.

(** * Utility for Point-Free Style *)

Ltac fun_ext := apply functional_extensionality.

Class SemiIso {A B} (f: A → B) (g: B → A) := semi_iso: g ∘ f = id.

Lemma semi_iso' {A B} f g `{!@SemiIso A B f g} x : g (f x) = x.
Proof. have ->: g (f x) = (g ∘ f) x by done. by rewrite semi_iso. Qed.

Class Iso {A B} (f: A → B) (g: B → A) :=
  { iso_semi_iso_l :> SemiIso f g; iso_semi_iso_r :> SemiIso g f }.

Global Instance iso_id {A} : Iso (@id A) id. Proof. done. Qed.

Global Instance semi_iso_inj `{!@SemiIso A B f g} : Inj (=) (=) f | 100.
Proof. move=> ?? /(f_equal g). by rewrite !semi_iso'. Qed.

Lemma compose_assoc {A B C D} (f: A → B) g (h: C → D) : h ∘ (g ∘ f) = (h ∘ g) ∘ f.
Proof. done. Qed.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Infix "⊛" := s_comb (left associativity, at level 50).
Global Arguments s_comb {_ _ _} _ _ _ / : assert.
Typeclasses Transparent s_comb.

Lemma surjective_pairing_fun {A B C} (f: A → B * C) : f = pair ∘ (fst ∘ f) ⊛ (snd ∘ f).
Proof. fun_ext=> ?/=. by rewrite -surjective_pairing. Qed.

Lemma surjective_vcons_fun {A B n} (f: B → vec A (S n)) :
  f = (λ a, vcons a) ∘ (vhd ∘ f) ⊛ (vtl ∘ f).
Proof. fun_ext=>/= ?. by rewrite -surjective_vcons. Qed.

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

Global Instance vapp_vsepat_iso {A} m n : Iso (curry vapp) (@vsepat A m n).
Proof. split; fun_ext.
  - move=> [xl ?]. by elim xl; [done|]=>/= ???->.
  - move=>/= ?. rewrite [vsepat _ _]surjective_pairing /=. induction m; [done|]=>/=.
    by rewrite [vsepat _ _]surjective_pairing /= IHm -surjective_vcons.
Qed.

Global Instance vapply_vfunsep_iso {A B n} : Iso vapply (@vfunsep A B n).
Proof.
  split; fun_ext; [by elim; [done|]=>/= ???->|]. move=> f. fun_ext=>/= x.
  induction n=>/=; [|rewrite IHn /=]; move: (f x)=> xl; by inv_vec xl.
Qed.

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
