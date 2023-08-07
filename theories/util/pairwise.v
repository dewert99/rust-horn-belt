From stdpp Require Import list sorting.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.

Notation PairWise := Sorted.StronglySorted.

Lemma PairWise_cons {T} R (x: T) (l: list T): PairWise R (x :: l) ↔ Forall (R x) l ∧ PairWise R l.
Proof. split. intros. inversion_clear H. done. intros [??]. constructor; done. Qed.

Lemma PairWise_nil {T} R : PairWise R ([]: list T) ↔ True.
Proof. split; intros. done. constructor. Qed.

Lemma PairWise_app {T} R (l: list T) (l': list T): PairWise R (l ++ l') ↔ PairWise R l ∧ Forall (λ x, Forall (R x) l') l ∧ PairWise R l'.
Proof. 
  induction l; simpl. rewrite PairWise_nil Forall_nil. intuition.
  rewrite 2! PairWise_cons IHl Forall_app Forall_cons. intuition.
Qed.

Lemma PairWise_fmap {T U} (f: T → U) R (l: list T): PairWise R (f<$>l) ↔ PairWise (λ x1 x2, R (f x1) (f x2)) l.
Proof. 
  induction l; simpl. rewrite 2! PairWise_nil. done. 
  rewrite 2! PairWise_cons IHl Forall_fmap. done.
Qed.

Global Instance PairWise_mono {T} : Proper ((pointwise_relation T (pointwise_relation T impl)) ==> (=) ==> impl) (@PairWise T).
Proof.
  intros R R' H ? l->. induction l. rewrite 2! PairWise_nil. done.
  rewrite 2! PairWise_cons. f_equiv; [|done]. intros H'. eapply Forall_impl. exact H'. intros ??. apply H. done.
Qed.

Global Instance PairWise_proper {T} : Proper ((pointwise_relation T (pointwise_relation T (↔))) ==> (=) ==> (↔)) (@PairWise T).
Proof.
  intros R R' H ? l->. split; (eassert (impl _ _); [|done]). rewrite H. done. rewrite -H. done.
Qed.

Lemma PairWise_and {T} (l: list T) R1 R2: PairWise (λ x y, R1 x y ∧ R2 x y) l ↔ PairWise R1 l ∧ PairWise R2 l.
Proof. 
  induction l. rewrite 3! PairWise_nil. done.
  rewrite 3! PairWise_cons Forall_and IHl. intuition.
Qed.

Lemma forall_pairs_alt {T} R (l: list T): Forall (λ x, Forall (R x) l) l ↔ PairWise R l ∧ Forall (λ x, R x x) l ∧ PairWise (flip R) l.
Proof. 
  induction l; simpl. rewrite 2! Forall_nil 2! PairWise_nil. done. 
  rewrite 2! PairWise_cons 3! Forall_cons. setoid_rewrite Forall_cons. rewrite Forall_and IHl. intuition.
Qed.

Lemma forall_pairs_alt' {T} (R: relation T) `{!Reflexive R} `{!Symmetric R} (l: list T): Forall (λ x, Forall (R x) l) l ↔ PairWise R l.
Proof. 
  rewrite forall_pairs_alt. intuition. apply Forall_true=>?. reflexivity. f_exact H. done.
Qed.

Lemma elem_of_alt {T} (a: T) (l: list T): a ∈ l ↔ Exists (λ y, a = y) l.
Proof. 
  induction l. rewrite Exists_nil elem_of_nil. done.
  rewrite Exists_cons elem_of_cons IHl. done.
Qed.

Lemma not_elem_of_alt {T} (a: T) (l: list T): a ∉ l ↔ Forall (λ y, a ≠ y) l.
Proof. 
  induction l. rewrite Forall_nil elem_of_nil. split. done. intros ??. done.
  rewrite Forall_cons not_elem_of_cons IHl. done.
Qed.

Lemma PairWise_NoDup {T} (l: list T): PairWise (≠) l ↔ NoDup l.
Proof. 
  induction l. rewrite PairWise_nil NoDup_nil. done. 
  rewrite PairWise_cons NoDup_cons IHl not_elem_of_alt. done.
Qed.