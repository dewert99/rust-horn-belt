Require Import ssreflect.
From stdpp Require Import prelude.
From lrust.util Require Import basic fancy_lists.
Set Default Proof Using "Type".

(** * Syntax for Coq type *)

Inductive syn_type := Zₛ | boolₛ | unitₛ | empty_setₛ | Propₛ
| optionₛ (_: syn_type) | listₛ (_: syn_type)
| prodₛ (_ _: syn_type) | sumₛ (_ _: syn_type) | funₛ (_ _: syn_type)
| xprodₛ (_: list syn_type) | xsumₛ (_: list syn_type).

Implicit Type 𝔄 𝔅: syn_type.

Local Notation all2 f := (fix all2 xl yl := match xl, yl with [], [] => true
  | x :: xl', y :: yl' => f x y && all2 xl' yl' | _, _ => false end).

Fixpoint syn_type_beq (𝔄 𝔅: syn_type) : bool := match 𝔄, 𝔅 with
  | Zₛ, Zₛ | boolₛ, boolₛ | unitₛ, unitₛ | empty_setₛ, empty_setₛ | Propₛ, Propₛ => true
  | optionₛ 𝔄₀, optionₛ 𝔅₀ | listₛ 𝔄₀, listₛ 𝔅₀ => syn_type_beq 𝔄₀ 𝔅₀
  | prodₛ 𝔄₀ 𝔄₁, prodₛ 𝔅₀ 𝔅₁ | sumₛ 𝔄₀ 𝔄₁, sumₛ 𝔅₀ 𝔅₁ | funₛ 𝔄₀ 𝔄₁, funₛ 𝔅₀ 𝔅₁
    => syn_type_beq 𝔄₀ 𝔅₀ && syn_type_beq 𝔄₁ 𝔅₁
  | xprodₛ 𝔄l, xprodₛ 𝔅l | xsumₛ 𝔄l, xsumₛ 𝔅l => all2 syn_type_beq 𝔄l 𝔅l
  | _, _ => false
  end.

Lemma syn_type_eq_correct (𝔄 𝔅: syn_type) : syn_type_beq 𝔄 𝔅 ↔ 𝔄 = 𝔅.
Proof.
  move: 𝔄 𝔅. fix FIX 1.
  have FIXl: ∀𝔄l 𝔅l, all2 syn_type_beq 𝔄l 𝔅l ↔ 𝔄l = 𝔅l.
  { elim=> [|?? IH][|??]//. rewrite andb_True FIX IH.
    split; by [move=> [->->]|move=> [=]]. }
  move=> [|||||?|?|??|??|??|?|?] [|||||?|?|??|??|??|?|?]//=;
  rewrite ?andb_True ?FIX ?FIXl; try (by split; [move=> ->|move=> [=]]);
  by split; [move=> [->->]|move=> [=]].
Qed.
Instance syn_type_beq_dec: EqDecision syn_type.
Proof.
  refine (λ 𝔄 𝔅, cast_if (decide (syn_type_beq 𝔄 𝔅)));
  by rewrite -syn_type_eq_correct.
Qed.

Declare Scope syn_type_scope.
Bind Scope syn_type_scope with syn_type.
Delimit Scope syn_type_scope with TYPE.
Infix "*" := prodₛ : syn_type_scope. Infix "+" := sumₛ : syn_type_scope.
Infix "→" := funₛ : syn_type_scope.
Notation "Π!" := xprodₛ : syn_type_scope. Notation "Σ!" := xsumₛ : syn_type_scope.

Local Notation tmap' f := (fix tmap' xl :=
  match xl with [] => ^[] | x :: xl' => f x ^:: tmap' xl' end).

Fixpoint of_syn_type (𝔄: syn_type) : Type := match 𝔄 with
  | Zₛ => Z | boolₛ => bool | unitₛ => unit | empty_setₛ => ∅ | Propₛ => Prop
  | optionₛ 𝔄₀ => option (of_syn_type 𝔄₀) | listₛ 𝔄₀ => list (of_syn_type 𝔄₀)
  | prodₛ 𝔄₀ 𝔄₁ => of_syn_type 𝔄₀ * of_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => of_syn_type 𝔄₀ + of_syn_type 𝔄₁
  | funₛ 𝔄₀ 𝔄₁ => of_syn_type 𝔄₀ → of_syn_type 𝔄₁
  | xprodₛ 𝔄l => Π! (tmap' of_syn_type 𝔄l)
  | xsumₛ 𝔄l => Σ! (tmap' of_syn_type 𝔄l)
  end.
Coercion of_syn_type: syn_type >-> Sortclass.

Local Notation all f := (fix all xl := match xl with
  [] => true | x :: xl' => f x && all xl' end).
Local Notation some f := (fix all xl := match xl with
  [] => false | x :: xl' => f x || all xl' end).

Fixpoint inh_syn_type (𝔄: syn_type) : bool := match 𝔄 with
  | prodₛ 𝔄₀ 𝔄₁ => inh_syn_type 𝔄₀ && inh_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => inh_syn_type 𝔄₀ || inh_syn_type 𝔄₁
  | funₛ 𝔄₀ 𝔄₁ => negb (inh_syn_type 𝔄₀) || inh_syn_type 𝔄₁
  | xprodₛ 𝔄l => all inh_syn_type 𝔄l | xsumₛ 𝔄l => some inh_syn_type 𝔄l
  | empty_setₛ => false | _ => true
  end.

Lemma negb_andb b c : negb (b && c) = negb b || negb c.
Proof. by case b; case c. Qed.
Lemma negb_orb b c : negb (b || c) = negb b && negb c.
Proof. by case b; case c. Qed.
Lemma negb_negb_orb b c : negb (negb b || c) = b && negb c.
Proof. by case b; case c. Qed.

Lemma of_just_and_neg_inh_syn_type {𝔄: syn_type} :
  (inh_syn_type 𝔄 → 𝔄) * (negb (inh_syn_type 𝔄) → 𝔄 → ∅).
Proof.
  move: 𝔄. fix FIX 1. move=> 𝔄. split.
  - case: 𝔄=>//= [|||?|?|??|𝔄?|𝔄?|𝔄l|𝔄l]=> H;
    [exact 0|exact true|exact True|exact None|exact []| | | | |].
    + move: H=> /andb_True[??]. constructor; by apply FIX.
    + move: H. case Eq: (inh_syn_type 𝔄); rewrite/= -/inh_syn_type=> H.
      { apply inl, FIX. by rewrite Eq. } { by apply inr, FIX. }
    + move: H. case Eq: (inh_syn_type 𝔄)=>/= ??; [by apply FIX|].
      suff E: Empty_set by done. eapply FIX; [|done]. by rewrite Eq.
    + move: H. elim 𝔄l; [move=> ?; exact -[]|]=> ?? IH /andb_True [??].
      split; by [apply FIX|apply IH].
    + move: H. elim 𝔄l; [done|]=> 𝔄 ? IH.
      case Eq: (inh_syn_type 𝔄); rewrite/= -/inh_syn_type=> H.
      { apply xinhd, FIX. by rewrite Eq. } { by apply xintl, IH. }
  - case: 𝔄=>//= [𝔄?|𝔄?|𝔄?|𝔄l|𝔄l].
    + rewrite negb_andb. case Eq: (inh_syn_type 𝔄)=>/= ?[a?]; [by eapply FIX|].
      eapply FIX; [|apply a]. by rewrite Eq.
    + rewrite negb_orb=> /andb_True[??] [x|x]; eapply FIX; [|apply x| |apply x]=>//.
    + rewrite negb_negb_orb=> /andb_True[??] f. eapply FIX; [done|]. by apply f, FIX.
    + elim 𝔄l; [done|]=> 𝔄 ? IH. rewrite negb_andb. case Eq: (inh_syn_type 𝔄)
      =>/= ?[??]; [by apply IH|]. eapply FIX; [|done]. by rewrite Eq.
    + elim 𝔄l; [move=> ?; by apply absurd|]=> ?? IH. rewrite negb_orb
      => /andb_True[??] /xsum_cons_to_sum[?|?]; by [eapply FIX|apply IH].
Qed.
Lemma of_inh_syn_type {𝔄: syn_type} : inh_syn_type 𝔄 → 𝔄.
Proof. apply of_just_and_neg_inh_syn_type. Qed.
Lemma of_neg_inh_syn_type {𝔄: syn_type} : negb (inh_syn_type 𝔄) → 𝔄 → ∅.
Proof. apply of_just_and_neg_inh_syn_type. Qed.

Lemma to_inh_syn_type {𝔄: syn_type} (x: 𝔄) : inh_syn_type 𝔄.
Proof.
  move: 𝔄 x. fix FIX 1. case=>//= [??|??|𝔄?|𝔄l|𝔄l].
  - move=> [??]. rewrite andb_True. by split; apply FIX.
  - move=> [?|?]; rewrite orb_True; [left|right]; by apply FIX.
  - move=> f. case Eq: (inh_syn_type 𝔄); [|done].
    apply FIX, f, of_inh_syn_type. by rewrite Eq.
  - elim 𝔄l; [done|]=>/= ?? IH [??]. rewrite andb_True. split; by [apply FIX|apply IH].
  - elim 𝔄l; [by apply absurd|]=> ?? IH /xsum_cons_to_sum[?|?];
    rewrite orb_True; [left|right]; by [eapply FIX|apply IH].
Qed.

Definition syn_typei: Type := { 𝔄 | inh_syn_type 𝔄 }.
Definition of_syn_typei (𝔄i: syn_typei) : Type := `𝔄i.
Coercion of_syn_typei: syn_typei >-> Sortclass.

Lemma syn_typei_eq (𝔄i 𝔅i: syn_typei) : 𝔄i = 𝔅i ↔ `𝔄i = `𝔅i.
Proof. apply (sig_eq_pi _). Qed.

Global Instance syn_typei_inhabited (𝔄i: syn_typei) : Inhabited 𝔄i.
Proof. apply populate. case 𝔄i=>??. by apply of_inh_syn_type. Qed.
