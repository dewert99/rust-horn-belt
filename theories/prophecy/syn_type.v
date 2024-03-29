From iris.prelude Require Import prelude.
From stdpp Require Import gmap.
From lrust.util Require Import basic vector fancy_lists.
From lrust.lang Require lang.
Set Default Proof Using "Type".

(** * Syntax for Coq type *)

Inductive syn_type := Zₛ | boolₛ | unitₛ | Propₛ | locₛ
| optionₛ (_: syn_type) | listₛ (_: syn_type) | vecₛ (_: syn_type) (_: nat)
| prodₛ (_ _: syn_type) | sumₛ (_ _: syn_type) | funₛ (_ _: syn_type)
| xprodₛ (_: list syn_type) | xsumₛ (_: list syn_type) | ghostₛ (_: nat) (_: syn_type).

Notation syn_typel := (list syn_type).
Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Declare Scope syn_type_scope.
Bind Scope syn_type_scope with syn_type.
Delimit Scope syn_type_scope with ST.
Notation "()" := unitₛ : syn_type_scope.
Infix "*" := prodₛ : syn_type_scope. Infix "+" := sumₛ : syn_type_scope.
Infix "→" := funₛ : syn_type_scope.
Notation "Π!" := xprodₛ : syn_type_scope. Notation "Σ!" := xsumₛ : syn_type_scope.
(* We use the following notation because
  [psum of_syn_type []] is equal to [Empty_set] *)
Notation Empty_setₛ := (xsumₛ []).

Global Instance Empty_setₛ_empty: Empty syn_type := Empty_setₛ.

Fixpoint ghost_level (𝔄: syn_type) : nat :=
  match 𝔄 with
  | Zₛ | boolₛ | unitₛ | Propₛ | locₛ => 0
  | optionₛ 𝔄₀ => ghost_level 𝔄₀ | listₛ 𝔄₀ => ghost_level 𝔄₀
  | vecₛ 𝔄₀ n => ghost_level 𝔄₀
  | prodₛ 𝔄₀ 𝔄₁ => ghost_level 𝔄₀ `max` ghost_level 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => ghost_level 𝔄₀ `max` ghost_level 𝔄₁
  | funₛ 𝔄₀ 𝔄₁ => ghost_level 𝔄₀ `max` ghost_level 𝔄₁
  | xprodₛ 𝔄l => foldr max 0 (ghost_level <$> 𝔄l)
  | xsumₛ 𝔄l => foldr max 0 (ghost_level <$> 𝔄l)
  | ghostₛ level 𝔄 => level + ghost_level 𝔄
  end.

Fixpoint of_syn_type (𝔄: syn_type): Type :=
  match 𝔄 with
  | Zₛ => Z | boolₛ => bool | unitₛ => () | Propₛ => Prop | locₛ => lang.loc
  | optionₛ 𝔄₀ => option (of_syn_type 𝔄₀) | listₛ 𝔄₀ => list (of_syn_type 𝔄₀)
  | vecₛ 𝔄₀ n => vec (of_syn_type 𝔄₀) n
  | prodₛ 𝔄₀ 𝔄₁ => of_syn_type 𝔄₀ * of_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => of_syn_type 𝔄₀ + of_syn_type 𝔄₁
  | funₛ 𝔄₀ 𝔄₁ => of_syn_type 𝔄₀ → of_syn_type 𝔄₁
  | xprodₛ 𝔄l => plist of_syn_type 𝔄l
  | xsumₛ 𝔄l => psum of_syn_type 𝔄l
  | ghostₛ _ 𝔄 => of_syn_type 𝔄
  end.
Coercion of_syn_type: syn_type >-> Sortclass.

(** Decidable Equality *)

Fixpoint syn_type_beq 𝔄 𝔅 : bool :=
  match 𝔄, 𝔅 with
  | Zₛ, Zₛ | boolₛ, boolₛ | (), () | Propₛ, Propₛ | locₛ, locₛ => true
  | optionₛ 𝔄₀, optionₛ 𝔅₀ | listₛ 𝔄₀, listₛ 𝔅₀ => syn_type_beq 𝔄₀ 𝔅₀
  | vecₛ 𝔄₀ n, vecₛ 𝔅₀ m => syn_type_beq 𝔄₀ 𝔅₀ && bool_decide (n = m)
  | 𝔄₀ * 𝔄₁, 𝔅₀ * 𝔅₁ | 𝔄₀ + 𝔄₁, 𝔅₀ + 𝔅₁ | 𝔄₀ → 𝔄₁, 𝔅₀ → 𝔅₁
    => syn_type_beq 𝔄₀ 𝔅₀ && syn_type_beq 𝔄₁ 𝔅₁
  | Π! 𝔄l, Π! 𝔅l | Σ! 𝔄l, Σ! 𝔅l => forall2b syn_type_beq 𝔄l 𝔅l
  | ghostₛ l 𝔄₀, ghostₛ l' 𝔅₀ => syn_type_beq 𝔄₀ 𝔅₀ && bool_decide (l = l')
  | _, _ => false
  end%ST.

Lemma syn_type_eq_correct 𝔄 𝔅 : syn_type_beq 𝔄 𝔅 ↔ 𝔄 = 𝔅.
Proof.
  move: 𝔄 𝔅. fix FIX 1.
  have FIXl: ∀𝔄l 𝔅l, forall2b syn_type_beq 𝔄l 𝔅l ↔ 𝔄l = 𝔅l.
  { elim=> [|?? IH][|??]//. rewrite andb_True FIX IH.
    split; by [move=> [->->]|move=> [=]]. }
  move=> 𝔄 𝔅. case 𝔄; case 𝔅=>//= *;
  rewrite ?andb_True ?FIX ?FIXl ?bool_decide_spec;
  try (by split; [move=> ->|move=> [=]]);
  by split; [move=> [->->]|move=> [=]].
Qed.
Global Instance syn_type_beq_dec: EqDecision syn_type.
Proof.
  refine (λ 𝔄 𝔅, cast_if (decide (syn_type_beq 𝔄 𝔅)));
  by rewrite -syn_type_eq_correct.
Qed.

(** Decidable Inhabitedness *)

Fixpoint inh_syn_type 𝔄 : bool :=
  match 𝔄 with
  | vecₛ 𝔄₀ n => bool_decide (n = 0) || inh_syn_type 𝔄₀
  | prodₛ 𝔄₀ 𝔄₁ => inh_syn_type 𝔄₀ && inh_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => inh_syn_type 𝔄₀ || inh_syn_type 𝔄₁
  | funₛ 𝔄₀ 𝔄₁ => negb (inh_syn_type 𝔄₀) || inh_syn_type 𝔄₁
  | xprodₛ 𝔄l => forallb inh_syn_type 𝔄l
  | xsumₛ 𝔄l => existsb inh_syn_type 𝔄l
  | ghostₛ _ 𝔄 => inh_syn_type 𝔄
  | _ => true
  end.

Local Lemma of_just_and_neg_inh_syn_type {𝔄} :
  (inh_syn_type 𝔄 → 𝔄) * (negb (inh_syn_type 𝔄) → 𝔄 → ∅).
Proof.
  move: 𝔄. fix FIX 1. move=> 𝔄. split.
  - case: 𝔄=>//=; try by (move=> *; exact inhabitant).
    + move=> ? n. case Eq: (bool_decide (n = 0))=>/=.
      * move: Eq=> /bool_decide_eq_true ->?. exact [#].
      * move=> ?. by apply (vreplicate n), FIX.
    + move=> ?? /andb_True[??]. constructor; by apply FIX.
    + move=> 𝔄?. case Eq: (inh_syn_type 𝔄)=>/= H.
      * apply inl, FIX. by rewrite Eq.
      * by apply inr, FIX.
    + move=> 𝔄?. case Eq: (inh_syn_type 𝔄)=>/= ??; [by apply FIX|].
      apply (@absurd ∅ _). eapply FIX; [|done]. by rewrite Eq.
    + elim; [move=> ?; exact -[]|]=> ?? IH /andb_True [??].
      split; by [apply FIX|apply IH].
    + elim; [done|]=>/= 𝔄 ? IH. case Eq: (inh_syn_type 𝔄)=>/= H.
      * left. apply FIX. by rewrite Eq.
      * right. by apply IH.
    + move=> ? 𝔄?. destruct (FIX 𝔄) as [to_res _]. apply to_res. done.
  - case: 𝔄=>//=.
    + move=> ?[|?]; rewrite negb_orb=> /andb_True[/negb_True/bool_decide_spec ??] v;
      [lia|]. by eapply FIX, vhd.
    + move=> 𝔄?. rewrite negb_andb.
      case Eq: (inh_syn_type 𝔄)=>/= ?[a?]; [by eapply FIX|].
      eapply FIX; [|apply a]. by rewrite Eq.
    + move=> ??. by rewrite negb_orb=> /andb_True[??] [a|b];
      eapply FIX; [|apply a| |apply b].
    + move=> ??. rewrite negb_negb_orb=> /andb_True[??] f. eapply FIX; [done|].
      by apply f, FIX.
    + elim; [done|]=> 𝔄 ? IH. rewrite negb_andb. case Eq: (inh_syn_type 𝔄)
      =>/= ?[??]; [by apply IH|]. eapply FIX; [|done]. by rewrite Eq.
    + elim; [move=> ?; by apply absurd|]=> ?? IH.
      rewrite negb_orb=> /andb_True[??] [?|?]; by [eapply FIX|apply IH].
    + move=> ? 𝔄?. destruct (FIX 𝔄) as [_ to_res]. apply to_res. done.
Qed.
Lemma of_inh_syn_type {𝔄} : inh_syn_type 𝔄 → 𝔄.
Proof. apply of_just_and_neg_inh_syn_type. Qed.
Lemma of_neg_inh_syn_type {𝔄} : negb (inh_syn_type 𝔄) → 𝔄 → ∅.
Proof. apply of_just_and_neg_inh_syn_type. Qed.
Lemma to_inh_syn_type {𝔄} (x: 𝔄) : inh_syn_type 𝔄.
Proof.
  case Eq: (inh_syn_type 𝔄); [done|]. apply (absurd (A:=∅)).
  eapply of_neg_inh_syn_type; [|done]. by rewrite Eq.
Qed.
Lemma to_neg_inh_syn_type {𝔄} (f: 𝔄 → ∅) : negb (inh_syn_type 𝔄).
Proof.
  case Eq: (inh_syn_type 𝔄); [|done].
  apply (absurd (A:=∅)), f, of_inh_syn_type. by rewrite Eq.
Qed.

Definition syn_typei: Type := {𝔄 | inh_syn_type 𝔄}.
Implicit Type 𝔄i 𝔅i: syn_typei.

Definition of_syn_typei 𝔄i : Type := `𝔄i.
Coercion of_syn_typei: syn_typei >-> Sortclass.

Global Instance syn_typei_inhabited 𝔄i : Inhabited 𝔄i.
Proof. apply populate. case 𝔄i=> ??. by apply of_inh_syn_type. Qed.
