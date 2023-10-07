Require Export stdpp.list.
Require Import stdpp.fin_maps.

Section filter.

Lemma list_filter_True {A} (l: list A) : (filter (const True) l) = l.
Proof. induction l. done. rewrite filter_cons_True, IHl; done. Qed.

Lemma list_filter_False {A} (l: list A) : (filter (const False) l) = [].
Proof. induction l. done. rewrite filter_cons_False, IHl. done. intuition. Qed.

Lemma filter_sublist {A} P `{!∀ x : A, Decision (P x)} (l: list A) :
  filter P l `sublist_of` l.
Proof.
  induction l as [|x l IHl]; [done|]. rewrite filter_cons.
  destruct (decide (P x));
    [by apply sublist_skip|by apply sublist_cons].
Qed.

Lemma list_filter_fmap {A B} P `{!∀ x : A, Decision (P x)} (l: list B) (f: B → A): 
  filter P (f <$> l) = f <$> (filter (P∘f) l).
Proof.
  induction l as [|x l IHl]; [done|]. rewrite fmap_cons, 2! filter_cons. simpl.
  destruct (decide (P (f x))); rewrite IHl; done.
Qed.

Lemma list_filter_iff' {A} (P1 P2 : A → Prop)
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} (l : list A) :
  Forall (λ x, P1 x ↔ P2 x) l →
  filter P1 l = filter P2 l.
Proof.
  intros HPiff. induction l as [|a l IH]; [done|]. inversion_clear HPiff.
  destruct (decide (P1 a)).
  - rewrite !filter_cons_True by naive_solver. by rewrite IH.
  - rewrite !filter_cons_False by naive_solver. by rewrite IH.
Qed.

Lemma list_filter_True' {A} P `{!∀ x : A, Decision (P x)} (l: list A) : 
  Forall P l → (filter P l) = l.
Proof. intros. erewrite list_filter_iff'. apply list_filter_True. eapply Forall_impl. done. simpl. intuition. Qed.

Lemma delete_list_to_map `{FinMap K M} {A} (k: K) (l: list (K * A)) : 
  (base.delete k (list_to_map (M:=M A) l)) = (list_to_map (filter (λ '(k', _), k ≠ k') l)).
Proof.
  induction l as [|[k' x] l IHl]; simpl. apply delete_empty. rewrite filter_cons. destruct (decide (k ≠ k')).
  simpl. rewrite <- IHl, delete_insert_ne; done.  destruct (decide (k = k')) as [->|?].
  rewrite <- IHl, delete_insert_delete; done. done.
Qed.
End filter.

Section index.
  Definition find_idx {A} P `{∀ x, Decision (P x)} : list A → nat :=
    fix go l :=
    match l with
    | [] => 0
    | x :: l => if decide (P x) then 0 else S (go l)
    end.
  

  Lemma find_idx_alt {A} P `{∀ x, Decision (P x)} (l: list A):
    find_idx P l = match list_find P l with | Some x => x.1 | None => length l end.
  Proof. 
    induction l; simpl. done. destruct (decide (P a)); simpl. done. 
    rewrite IHl. destruct (list_find P l); done.
  Qed.

  Lemma list_find_ext {A} P `{∀ x, Decision (P x)} (Q : A → Prop) `{∀ x, Decision (Q x)} l :
    (∀ x, P x ↔ Q x) →
    find_idx P l = find_idx Q l.
  Proof. intros. rewrite 2! find_idx_alt. erewrite list_find_ext. done. done.  Qed.

  Lemma find_idx_spec' {A} P `{∀ x, Decision (P x)} (l: list A) (i: nat):
  find_idx P l = i ↔
    (i = length l ∨ ∃ x, l !! i = Some x ∧ P x) ∧ ∀ j y, l !! j = Some y → j < i → ¬P y.
  Proof.
    rewrite find_idx_alt. remember (list_find P l) as x. symmetry in Heqx. remember Heqx as eq. clear Heqeq. destruct x as [[??]|].
    rewrite list_find_Some in Heqx. destruct Heqx as (?&?&?). split. intros <-. split. right. exists a. done. done.
    intros ([|[?[??]]]&?). exfalso; eapply H4. exact H0. rewrite H3. eapply lookup_lt_Some. done. done.
    assert (list_find P l = Some (i, x)). rewrite list_find_Some. done.
    rewrite eq in H6. injection H6. done.
    rewrite list_find_None, Forall_forall in Heqx. split. intros. split. left. done. intros. apply Heqx. eapply elem_of_list_lookup_2. done.
    intros ([|[?[??]]]&?). done. assert (list_find P l = Some (i, x)). rewrite list_find_Some. done.
    rewrite eq in H3. done.
  Qed.

  Lemma find_idx_spec {A} P `{∀ x, Decision (P x)} (l: list A):
    (find_idx P l = length l ∨ ∃ x, l !! find_idx P l = Some x ∧ P x) ∧ ∀ j y, l !! j = Some y → j < find_idx P l  → ¬P y.
  Proof.
    remember (find_idx P l) as f. symmetry in Heqf. rewrite find_idx_spec' in Heqf. done.
  Qed.

  Lemma find_idx_Some {A} P `{∀ x, Decision (P x)} (l: list A) (x: A):
    l !! find_idx P l = Some x → P x.
  Proof.
    destruct (find_idx_spec P l) as [[|[?[??]]]?].
    rewrite H0. intros. apply lookup_lt_Some in H2. lia. 
    rewrite H0. intros [= ->]. done.
  Qed.

  Lemma find_idx_fmap {A B} P `{∀ x, Decision (P x)} (l: list B) (f: B → A): find_idx P (f<$>l) = find_idx (P ∘ f) l.
  Proof.
    rewrite 2! find_idx_alt, list_find_fmap. remember (list_find (P ∘ f) l) as x. destruct x. done. rewrite fmap_length. done.
  Qed.

  Lemma find_idx_delete {K A} `{EqDecision K} `{FinMap K M} (l: list (K*A)) (k: K) (a: A):
    ((list_to_map l): M A) !! k = Some a → <[k:=a]>(list_to_map (base.delete (find_idx (λ x, x.1 = k) l) l): M A) = (list_to_map l) ∧ l !! (find_idx (λ x, x.1 = k) l) = Some (k, a).
  Proof.
    induction l as [|[??]]; simpl. rewrite lookup_empty. done.
    destruct (decide (k0 = k)) as [->|?]; simpl. rewrite lookup_insert. intros [= ->]. done.
    intros ?. rewrite lookup_insert_ne in H7; [|done]. destruct (IHl H7) as (<-&<-). rewrite <- insert_commute; done.
  Qed.

  Lemma find_idx_delete' {K A} `{EqDecision K} `{FinMap K M} (l: list (K*A)) (k: K) (a: A):
    NoDup l.*1 → ((list_to_map l): M A) !! k = Some a → (list_to_map (base.delete (find_idx (λ x, x.1 = k) l) l): M A) = (base.delete k (list_to_map l)) ∧ l !! (find_idx (λ x, x.1 = k) l) = Some (k, a).
  Proof.
    intros no_dup is_some. destruct (find_idx_delete l k a is_some) as [<- is_some2]. intuition.
    rewrite delete_insert. done.
    apply not_elem_of_list_to_map_1. clear is_some is_some2. induction l; simpl. apply not_elem_of_nil. 
    inversion_clear no_dup. destruct (decide (a0.1 = k)) as [<-|]; simpl. done.
    apply not_elem_of_cons. split. done. apply IHl. done.
  Qed.
End index.