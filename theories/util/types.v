From stdpp Require Import prelude.
From iris.algebra Require Import ofe.

(** * List of Types *)
(** We avoid using [list Type] because that can cause universe inconsistency *)

Inductive Types := tnil: Types | tcons: Type → Types → Types.
Implicit Type As: Types.

Notation "^[ ]" := (tnil) (at level 5, format "^[ ]").
Infix "^::" := (tcons) (at level 60, right associativity).
Notation "^[ A ; .. ; B ]" := (A ^:: .. (B ^:: ^[]) ..)
  (at level 5, format "^[ A ;  .. ;  B ]").

Fixpoint app_Types As Bs :=
  match As with ^[] => Bs | A ^:: As' => A ^:: app_Types As' Bs end.
Infix "^++" := (app_Types) (at level 60, right associativity).

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
Infix "+++" := (happ) (at level 60, right associativity).

Fixpoint hmap {F B As} (f: ∀A, F A → B) (xl: hlist F As) : list B :=
  match xl with +[] => [] | x +:: xl' => f _ x :: hmap f xl' end.
Infix "+<$>" := (hmap) (at level 61, left associativity).

Fixpoint hhmap {F G As} (f: ∀A, F A → G A) (xl: hlist F As) : hlist G As :=
  match xl with +[] => +[] | x +:: xl' => f _ x +:: hhmap f xl' end.
Infix "+<$>+" := (hhmap) (at level 61, left associativity).

Inductive HForall {F} (Φ: ∀A, F A → Prop) : ∀{As: Types}, hlist F As → Prop :=
| HForall_nil: HForall Φ +[]
| HForall_cons {A As} (x: _ A) (xl: _ As) :
    Φ _ x → HForall Φ xl → HForall Φ (x +:: xl).

Inductive HForall2 {F G} (Φ: ∀A, F A → G A → Prop)
  : ∀{As: Types}, hlist F As → hlist G As → Prop :=
| HForall2_nil: HForall2 Φ +[] +[]
| HForall2_cons {A As} (x: _ A) (y: _ A) (xl: _ As) (yl: _ As) :
    Φ _ x y → HForall2 Φ xl yl → HForall2 Φ (x +:: xl) (y +:: yl).

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

Notation ":1" := (nil_unit) (at level 1) : type_scope.
Infix ":*" := (cons_prod) (at level 60, right associativity) : type_scope.
Notation "-[ ]" := (nil_tt) (at level 1, format "-[ ]").
Infix "-::" := (cons_pair) (at level 60, right associativity).
Notation "-[ a ; .. ; z ]" := (a -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ a ;  .. ;  z ]").

Fixpoint flist F As : Type :=
  match As with ^[] => :1 | A ^:: As' => F A :* flist F As' end.
Fixpoint app_flist {F As Bs} (xl: flist F As) (yl: flist F Bs)
  : flist F (As ^++ Bs) := match As, xl with
  | ^[], -[] => yl | A ^:: As', x -:: xl' => x -:: app_flist xl' yl end.
Infix "-++" := (app_flist) (at level 60, right associativity).
