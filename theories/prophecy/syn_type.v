Require Import ssreflect.
From stdpp Require Import prelude.
From lrust.util Require Import fancy_lists.
Set Default Proof Using "Type".

(** * Syntax for Coq type *)

Inductive syn_type0 := Zₛ | boolₛ | unitₛ | Propₛ.
Inductive syn_type1 := optionₛ' | listₛ'.
Inductive syn_type2 := prodₛ' | sumₛ' | funₛ'.
Inductive syn_typex := xprodₛ' | xsumₛ'.

Instance syn_type0_eq_dec: EqDecision syn_type0. Proof. solve_decision. Qed.
Instance syn_type1_eq_dec: EqDecision syn_type1. Proof. solve_decision. Qed.
Instance syn_type2_eq_dec: EqDecision syn_type2. Proof. solve_decision. Qed.
Instance syn_typex_eq_dec: EqDecision syn_typex. Proof. solve_decision. Qed.

Inductive syn_type :=
| SynType0:> syn_type0 → syn_type
| SynType1: syn_type1 → syn_type → syn_type
| SynType2: syn_type2 → syn_type → syn_type → syn_type
| SynTypex: syn_typex → list syn_type → syn_type.

Implicit Type 𝔄 𝔅: syn_type.

Local Notation all2 f := (fix all2 xl yl := match xl, yl with | [], [] => true
  | x :: xl', y :: yl' => f x y && all2 xl' yl' | _, _ => false end).

Fixpoint syn_type_beq (𝔄 𝔅: syn_type) : bool :=
  match 𝔄, 𝔅 with
  | SynType0 a, SynType0 b => bool_decide (a = b)
  | SynType1 f 𝔄, SynType1 g 𝔅 => bool_decide (f = g) && syn_type_beq 𝔄 𝔅
  | SynType2 f 𝔄 𝔄', SynType2 g 𝔅 𝔅' =>
      bool_decide (f = g) && syn_type_beq 𝔄 𝔅 && syn_type_beq 𝔄' 𝔅'
  | SynTypex f 𝔄l, SynTypex g 𝔅l => bool_decide (f = g) && all2 syn_type_beq 𝔄l 𝔅l
  | _, _ => false
  end.

Lemma syn_type_eq_correct (𝔄 𝔅: syn_type) : syn_type_beq 𝔄 𝔅 ↔ 𝔄 = 𝔅.
Proof.
  move: 𝔄 𝔅. fix FIX 1. move=> [?|??|???|? 𝔄l] [?|??|???|? 𝔅l]//=;
  rewrite ?andb_True bool_decide_spec ?FIX.
  - split; by [move=> ->|move=> [=]].
  - split; by [move=> [->->]|move=> [=]].
  - split; [by move=> [[->->]->]|by move=> [=]].
  - suff ->: ∀𝔄l 𝔅l, all2 syn_type_beq 𝔄l 𝔅l ↔ 𝔄l = 𝔅l.
    { split; by [move=> [->->]|move=> [=]]. }
    elim=> [|?? IH][|??]//. rewrite andb_True FIX IH.
    split; by [move=> [->->]|move=> [=]].
Qed.
Instance syn_type_beq_dec: EqDecision syn_type.
Proof.
  refine (λ 𝔄 𝔅, cast_if (decide (syn_type_beq 𝔄 𝔅)));
  by rewrite -syn_type_eq_correct.
Qed.

Declare Scope syn_type_scope.
Bind Scope syn_type_scope with syn_type.
Delimit Scope syn_type_scope with TYPE.
Notation optionₛ := (SynType1 optionₛ'). Notation listₛ := (SynType1 listₛ').
Notation prodₛ := (SynType2 prodₛ'). Notation sumₛ := (SynType2 sumₛ').
Notation funₛ := (SynType2 funₛ').
Infix "*" := prodₛ : syn_type_scope. Infix "+" := sumₛ : syn_type_scope.
Infix "→" := funₛ : syn_type_scope.
Notation xprodₛ := (SynTypex xprodₛ'). Notation xsumₛ := (SynTypex xsumₛ').
Notation "Π!" := xprodₛ : syn_type_scope. Notation "Σ!" := xsumₛ : syn_type_scope.

Local Notation tmap' f := (fix tmap' xl :=
  match xl with [] => ^[] | x :: xl' => f x ^:: tmap' xl' end).

Fixpoint of_syn_type (𝔄: syn_type) : Type := match 𝔄 with
| Zₛ => Z | boolₛ => bool | unitₛ => unit | Propₛ => Prop
| optionₛ 𝔄 => option (of_syn_type 𝔄) | listₛ 𝔄 => list (of_syn_type 𝔄)
| prodₛ 𝔄 𝔅 => of_syn_type 𝔄 * of_syn_type 𝔅
| sumₛ 𝔄 𝔅 => of_syn_type 𝔄 + of_syn_type 𝔅
| funₛ 𝔄 𝔅 => of_syn_type 𝔄 → of_syn_type 𝔅
| xprodₛ 𝔄l => Π! (tmap' of_syn_type 𝔄l)
| xsumₛ 𝔄l => Σ! (tmap' of_syn_type 𝔄l)
end.
Coercion of_syn_type: syn_type >-> Sortclass.
