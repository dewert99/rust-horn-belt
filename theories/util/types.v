From stdpp Require Import prelude.
From iris.algebra Require Import monoid ofe.
From iris.base_logic Require Export iprop.

(** * List of Types *)
(** We avoid using [list Type] because that can cause universe inconsistency *)

Inductive Types := tnil: Types | tcons: Type → Types → Types.
Implicit Type As: Types.

Notation "^[ ]" := tnil (at level 5, format "^[ ]").
Infix "^::" := tcons (at level 60, right associativity).
Notation "^[ A ; .. ; B ]" := (A ^:: .. (B ^:: ^[]) ..)
  (at level 5, format "^[ A ;  .. ;  B ]").

Fixpoint tapp As Bs :=
  match As with ^[] => Bs | A ^:: As' => A ^:: tapp As' Bs end.
Infix "^++" := tapp (at level 60, right associativity).

(** * Heterogeneous List *)

Inductive hlist F : Types → Type :=
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

Inductive HForall {F} (Φ: ∀A, F A → Prop) : ∀{As: Types}, hlist F As → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {A As} (x: _ A) (xl: _ As) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Inductive HForall2 {F G} (Φ: ∀A, F A → G A → Prop)
  : ∀{As}, hlist F As → hlist G As → Prop :=
| HForall2_nil: HForall2 Φ +[] +[]
| HForall2_cons {A As} (x: _ A) (y: _ A) (xl: _ As) (yl: _ As) :
    Φ _ x y → HForall2 Φ xl yl → HForall2 Φ (x +:: xl) (y +:: yl).

Fixpoint big_sepHL {Σ F As} (Φ: ∀A, F A → iProp Σ) (xl: hlist F As) : iProp Σ :=
  match xl with +[] => True | x +:: xl' => Φ _ x ∗ big_sepHL Φ xl' end.
Notation "'[∗' 'hlist]' x ∈ xl , P" := (big_sepHL (λ _ x, P) xl)
  (at level 200, xl at level 10, x at level 1, right associativity,
   format "[∗  hlist]  x  ∈  xl ,  P") : bi_scope.

Inductive hlist2 F : Types → Types → Type :=
| hnil2: hlist2 F ^[] ^[]
| hcons2 {A B As Bs} : F A B → hlist2 F As Bs → hlist2 F (A ^:: As) (B ^:: Bs).
Notation "+2[ ]" := (hnil2 _) (at level 1, format "+2[ ]").
Notation "+2[ ]@{ F }" := (hnil2 F) (at level 1, only parsing).
Infix "+2::" := (hcons2 _) (at level 60, right associativity).
Infix "+2::@{ F }" := (hcons2 F) (at level 60, right associativity, only parsing).
Notation "+2[ x ; .. ; z ]" := (x +2:: .. (z +2:: +2[]) ..)
  (at level 1, format "+2[ x ;  .. ;  z ]").
Notation "+2[ x ; .. ; z ]@{ F }" := (x +2:: .. (z +2:: +2[]@{F}) ..)
  (at level 1, only parsing).

Inductive HForall3 {F G H} (Φ: ∀A B, F A B → G A → H B → Prop)
  : ∀{As Bs}, hlist2 F As Bs → hlist G As → hlist H Bs → Prop :=
| HForall3_nil: HForall3 Φ +2[] +[] +[]
| HForall3_cons {A B As Bs} (x: _ A B) y z (xl: _ As Bs) yl zl :
    Φ _ _ x y z → HForall3 Φ xl yl zl →
    HForall3 Φ (x +2:: xl) (y +:: yl) (z +:: zl).

Section setoid.
Context {F: Type → Type} `{∀A, Equiv (F A)}.

Global Instance hlist_equiv {As} : Equiv (hlist F As) := HForall2 (λ _, (≡)).

End setoid.

Section ofe.
Context {F: Type → ofe}.

Global Instance hlist_dist {As} : Dist (hlist F As) :=
  λ n, HForall2 (λ _, dist n).
Global Instance hcons_ne {A As} : NonExpansive2 (@hcons F A As).
Proof. move=> ???????. by apply HForall2_cons. Qed.

End ofe.

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

Fixpoint flist F As : Type :=
  match As with ^[] => :1 | A ^:: As' => F A :* flist F As' end.
Fixpoint app_flist {F As Bs} (xl: flist F As) (yl: flist F Bs)
  : flist F (As ^++ Bs) := match As, xl with
  | ^[], -[] => yl | A ^:: As', x -:: xl' => x -:: app_flist xl' yl end.
Infix "-++" := app_flist (at level 60, right associativity).
