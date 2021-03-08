From stdpp Require Import prelude.

(** * List of Types *)
(** We avoid using [list Type] because that can cause universe inconsistency *)

Inductive Types := NilTypes: Types | ConsTypes: Type → Types → Types.
Implicit Type As Bs: Types.

Notation "^[ ]" := (NilTypes) (at level 5, format "^[ ]").
Infix "^::" := (ConsTypes) (at level 60, right associativity).
Notation "^[ A ; .. ; B ]" := (A ^:: .. (B ^:: ^[]) ..)
  (at level 5, format "^[ A ;  .. ;  B ]").

(** * Heterogeneous List *)

Inductive hlist (F: Type → Type) : Types → Type :=
| NilHlist: hlist F ^[]
| ConsHlist {A As} : F A → hlist F As → hlist F (A ^:: As).

Notation "+[ ]" := (NilHlist _) (at level 1, format "+[ ]").
Notation "+[ ]@{ F }" := (NilHlist F) (at level 1, only parsing).
Infix "+::" := (ConsHlist _) (at level 60, right associativity).
Infix "+::@{ F }" := (ConsHlist F)
  (at level 60, right associativity, only parsing).
Notation "+[ a ; .. ; z ]" := (a +:: .. (z +:: +[]) ..)
  (at level 1, format "+[ a ;  .. ;  z ]").
Notation "+[ a ; .. ; z ]@{ F }" := (a +:: .. (z +:: +[]@{F}) ..)
  (at level 1, only parsing).

(** * List-like Product *)

Inductive nil_unit := NilTt: nil_unit.
Inductive cons_prod A B := ConsPair: A → B → cons_prod A B.
Arguments ConsPair {_ _} _ _.

Notation ":1" := (nil_unit) (at level 1).
Infix ":*" := (cons_prod) (at level 39, right associativity).
Notation "-[ ]" := (NilTt) (at level 1, format "-[ ]").
Infix "-::" := (ConsPair) (at level 60, right associativity).
Notation "-[ a ; .. ; z ]" := (a -:: .. (z -:: -[]) ..)
  (at level 1, format "-[ a ;  .. ;  z ]").

Fixpoint flist As : Type := match As with
| ^[] => :1
| A ^:: As => A :* flist As
end.
