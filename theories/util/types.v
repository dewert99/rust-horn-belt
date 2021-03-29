Require Import Equality FunctionalExtensionality.
From iris.algebra Require Import monoid ofe.
From iris.base_logic Require Import iprop.
From iris.proofmode Require Import tactics.

(** * List of Types *)
(** We avoid using [list Type] because that can cause universe inconsistency *)

Inductive Types := tnil: Types | tcons: Type → Types → Types.
Implicit Type (A B C D: Type) (As Bs: Types).

Notation "^[ ]" := tnil (at level 5, format "^[ ]").
Infix "^::" := tcons (at level 60, right associativity).
Notation "^[ A ; .. ; B ]" := (A ^:: .. (B ^:: ^[]) ..)
  (at level 5, format "^[ A ;  .. ;  B ]").

Fixpoint tapp As Bs :=
  match As with ^[] => Bs | A ^:: As' => A ^:: tapp As' Bs end.
Infix "^++" := tapp (at level 60, right associativity).

Fixpoint tnth B As (i: nat) := match As with
  ^[] => B | A ^:: As' => match i with 0 => A | S j => tnth B As' j end end.

(** * Heterogeneous List *)

Inductive hlist (F: Type → Type) : Types → Type :=
| hnil: hlist F ^[]
| hcons {A As} : F A → hlist F As → hlist F (A ^:: As).
Notation "+[ ]" := (hnil _) (at level 1, format "+[ ]").
Notation "+[ ]@{ F }" := (hnil F) (at level 1, only parsing).
Infix "+::" := (hcons _) (at level 60, right associativity).
Infix "+::@{ F }" := (hcons F) (at level 60, right associativity, only parsing).
Notation "+[ x ; .. ; z ]" := (x +:: .. (z +:: +[]) ..)
  (at level 1, format "+[ x ;  .. ;  z ]").
Notation "+[ x ; .. ; z ]@{ F }" := (x +:: .. (z +:: +[]@{F}) ..)
  (at level 1, only parsing).

Fixpoint happ {F As Bs} (xl: hlist F As) (yl: hlist F Bs)
  : hlist F (As ^++ Bs) :=
  match xl with +[] => yl | x +:: xl' => x +:: happ xl' yl end.
Infix "+++" := happ (at level 60, right associativity).

Fixpoint hmap {F B As} (f: ∀A, F A → B) (xl: hlist F As) : list B :=
  match xl with +[] => [] | x +:: xl' => f _ x :: hmap f xl' end.
Infix "+<$>" := hmap (at level 61, left associativity).

Fixpoint hhmap {F G As} (f: ∀A, F A → G A) (xl: hlist F As) : hlist G As :=
  match xl with +[] => +[] | x +:: xl' => f _ x +:: hhmap f xl' end.
Infix "+<$>+" := hhmap (at level 61, left associativity).

Fixpoint hnth {F As B} (y: F B) (xl: hlist F As) (i: nat) : F (tnth B As i) :=
  match xl with +[] => y | x +:: xl' =>
    match i with 0 => x | S j => hnth y xl' j end end.

Fixpoint max_hlist_with {F As} (f: ∀A, F A → nat) (xl: hlist F As) : nat :=
  match xl with +[] => 0 | x +:: xl' => f _ x `max` max_hlist_with f xl' end.

Inductive HForall {F} (Φ: ∀A, F A → Prop) : ∀{As: Types}, hlist F As → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {A As} (x: _ A) (xl: _ As) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Lemma HForall_nth {F As B} (Φ: ∀A, F A → Prop) (y: _ B) (xl: _ As) i :
  Φ _ y → HForall Φ xl → Φ _ (hnth y xl i).
Proof.
  move=> ? All. move: i. elim: All=> /=[|> ?? IH]; [by move=> ?|]. by case=> [|?].
Qed.

Inductive HForall2 {F G} (Φ: ∀A, F A → G A → Prop)
  : ∀{As}, hlist F As → hlist G As → Prop :=
| HForall2_nil: HForall2 Φ +[] +[]
| HForall2_cons {A As} (x: _ A) (y: _ A) (xl: _ As) (yl: _ As) :
    Φ _ x y → HForall2 Φ xl yl → HForall2 Φ (x +:: xl) (y +:: yl).

Lemma HForall2_nth {F G B As} (Φ: ∀A, F A → G A → Prop) (x y: _ B) (xl yl: _ As) i :
  Φ _ x y → HForall2 Φ xl yl → Φ _ (hnth x xl i) (hnth y yl i).
Proof.
  move=> ? All. move: i. elim: All=> /=[|> ?? IH]; [by move=> ?|]. by case=> [|?].
Qed.

(** * List-like Product *)

Inductive nil_unit := nil_tt: nil_unit.
Inductive cons_prod A B := cons_pair: A → B → cons_prod A B.
Arguments cons_pair {_ _} _ _.

Notation ":1" := nil_unit (at level 1) : type_scope.
Infix ":*" := cons_prod (at level 60, right associativity) : type_scope.
Notation "-[ ]" := nil_tt (at level 1, format "-[ ]").
Infix "-::" := cons_pair (at level 60, right associativity).
Notation "-[ a ; .. ; z ]" := (a -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ a ;  .. ;  z ]").

Fixpoint plist (F: Type → Type) As : Type :=
  match As with ^[] => :1 | A ^:: As' => F A :* plist F As' end.

Fixpoint papp {F As Bs} (xl: plist F As) (yl: plist F Bs) : plist F (As ^++ Bs) :=
  match As, xl with ^[], -[] => yl | A ^:: As', x -:: xl' => x -:: papp xl' yl end.
Infix "-++" := papp (at level 60, right associativity).

Fixpoint hlist_to_plist {F As} (xl: hlist F As) : plist F As :=
  match xl with +[] => -[] | x +:: xl' => x -:: hlist_to_plist xl' end.

Fixpoint plist2 (F: Type → Type → Type) As Bs : Type :=
  match As, Bs with ^[], ^[] => :1 |
    A ^:: As', B ^:: Bs' => F A B :* plist2 F As' Bs' | _, _ => Empty_set end.

Fixpoint p2flip {F As Bs} : plist2 F As Bs → plist2 (flip F) Bs As :=
  match As, Bs with ^[], ^[] => id
  | _ ^:: _, _ ^:: _ => λ xl, let: x -:: xl' := xl in x -:: p2flip xl'
  | _, _ => λ xl, match xl with end end.

Fixpoint pp2map {F G As Bs} (f: ∀A B, F A B → G A B) : plist2 F As Bs → plist2 G As Bs :=
  match As, Bs with ^[], ^[] => id
  | _ ^:: _, _ ^:: _ => λ xl, let: x -:: xl' := xl in f _ _ x -:: pp2map f xl'
  | _, _ => λ xl, match xl with end end.
Infix "-2<$>-" := pp2map (at level 61, left associativity).

Fixpoint p2nth {F As Bs C D} (y: F C D) :
  plist2 F As Bs → ∀i, F (tnth C As i) (tnth D Bs i) :=
  match As, Bs with ^[], ^[] => λ _ _, y
  | _ ^:: _, _ ^:: _ => λ xl i,
      let: x -:: xl' := xl in match i with 0 => x | S j => p2nth y xl' j end
  | _, _ => λ xl _, match xl with end end.

Inductive HForallZip {F G H} (Φ: ∀A B, F A → G B → H A B → Prop)
  : ∀{As Bs}, hlist F As → hlist G Bs → plist2 H As Bs → Prop :=
| HForallZip_nil: HForallZip Φ +[] +[] -[]
| HForallZip_cons {A B As Bs} (x: _ A) (y: _ B) z (xl: _ As) (yl: _ Bs) zl :
    Φ _ _ x y z → HForallZip Φ xl yl zl →
    HForallZip Φ (x +:: xl) (y +:: yl) (z -:: zl).

Lemma HForallZip_nth {F G H C D As Bs} (Φ: ∀A B, F A → G B → H A B → Prop)
  (x: _ C) (y: _ D) z (xl: _ As) (yl: _ Bs) zl i :
  Φ _ _ x y z → HForallZip Φ xl yl zl → Φ _ _ (hnth x xl i) (hnth y yl i) (p2nth z zl i).
Proof.
  move=> ? All. move: i. elim: All=> /=[|> ?? IH]; [by move=> ?|]. by case=> [|?].
Qed.

Lemma HForallZip_flip {F G H As Bs}
  (Φ: ∀A B, F A → G B → H A B → Prop) (xl: _ As) (yl: _ Bs) zl :
  HForallZip Φ xl yl zl →
  HForallZip (λ _ _ y x z, Φ _ _ x y z) yl xl (p2flip zl).
Proof.
  elim=> /=[|*]; [constructor|]. by apply (@HForallZip_cons _ _ (flip H)).
Qed.

Lemma HForallZip_impl {F G H H' As Bs}
  (Φ: ∀A B, F A → G B → H A B → Prop) (Ψ: ∀A B, F A → G B → H' A B → Prop)
  (f: ∀A B, H A B → H' A B) (xl: _ As) (yl: _ Bs) zl :
  (∀A B (x: _ A) (y: _ B) z, Φ _ _ x y z → Ψ _ _ x y (f _ _ z)) →
  HForallZip Φ xl yl zl → HForallZip Ψ xl yl (f -2<$>- zl).
Proof.
  move=> Imp. elim=> /=[|> ???]; [constructor|]. constructor; by [apply Imp|].
Qed.

(** * Sum *)

Inductive xsum As : Type := xinj (i: nat) : tnth Empty_set As i → xsum As.
Arguments xinj {_} _ _.

Global Instance xinj_inj {As} i : Inj (=) (=) (@xinj As i).
Proof. move=> ?? Eq. by dependent destruction Eq. Qed.

Definition xsum_map {As Bs} (fl: plist2 (→) As Bs) (xl: xsum As) : xsum Bs :=
  match xl with xinj i x => xinj i (p2nth id fl i x) end.

(** * Setoid *)

Section setoid.
Context {F: Type → Type} `{∀A, Equiv (F A)}.

Global Instance hlist_equiv {As} : Equiv (hlist F As) := HForall2 (λ _, (≡)).

Global Instance hnth_proper {As B} :
  Proper ((≡) ==> (≡) ==> forall_relation (λ _, (≡))) (@hnth F As B).
Proof. move=> ???????. by apply (HForall2_nth _). Qed.

End setoid.

(** * Ofe *)

Section ofe.
Context {F: Type → ofe}.

Global Instance hlist_dist {As} : Dist (hlist F As) :=
  λ n, HForall2 (λ _, dist n).
Global Instance hcons_ne {A As} : NonExpansive2 (@hcons F A As).
Proof. move=> ???????. by constructor. Qed.

Global Instance hnth_ne {As B} n :
Proper ((dist n) ==> (dist n) ==> forall_relation (λ _, dist n)) (@hnth F As B).
Proof. move=> ???????. by apply (HForall2_nth (λ A, ofe_dist (F A) n)). Qed.

End ofe.

(** * Iris *)

Fixpoint big_sepHL {Σ F As} (Φ: ∀A, F A → iProp Σ) (xl: hlist F As) : iProp Σ :=
  match xl with +[] => True | x +:: xl' => Φ _ x ∗ big_sepHL Φ xl' end.
Notation "[∗ hlist] x ∈ xl , P" := (big_sepHL (λ _ x, P) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
    format "[∗  hlist]  x  ∈  xl ,  P") : bi_scope.

Fixpoint big_sepHLZip {Σ F G H As Bs} (Φ: ∀A B, F A → G B → H A B → iProp Σ)
  (xl: hlist F As) (yl: hlist G Bs) (zl: plist2 H As Bs) : iProp Σ :=
  match xl, yl, zl with +[], +[], -[] => True |
    x +:: xl', y +:: yl', z -:: zl' => Φ _ _ x y z ∗ big_sepHLZip Φ xl' yl' zl' |
    _, _, _ => False end.
Notation "[∗ hlist] x ; y ;- z ∈ xl ; yl ;- zl , P" :=
  (big_sepHLZip (λ _ _ x y z, P) xl yl zl)
  (at level 200, xl, yl, zl at level 10, x, y, z at level 1, right associativity,
    format "[∗  hlist]  x ;  y ;-  z  ∈  xl ;  yl ;-  zl ,  P") : bi_scope.
