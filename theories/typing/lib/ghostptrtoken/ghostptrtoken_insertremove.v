From lrust.typing Require Export type always_true.
From lrust.typing Require Import uniq_util typing ptr logic_fn.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken_basic ghostseq_basic permdata_basic.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_insertremove.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_insert {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "b"] :=
      Skip;;
      delete [ #1; "t"];;
      return: ["b"].

  Lemma ghostptrtoken_insert_type {𝔄} (ty: type 𝔄) :
   (ty.(ty_size) > 0) → typed_val (ghostptrtoken_insert ty) (fn<α>(∅; &uniq{α} (ghostptrtoken_ty ty), box ty) → ptr)
      (λ post '-[(al, al'); a], forall ptr, (list_to_gmap al') = <[ptr:=a]>(list_to_gmap al) → (list_to_gmap al) !! ptr = None → post ptr).
  Proof.
    intros ?. eapply type_fn; [apply _|]=> α ??[l[l2[]]]. simpl_subst. via_tr_impl.
    iApply ghost_read_delete; [done|]. iIntros. iApply typed_body_tctx_incl.
    eapply ghost_update; [done|solve_typing|]. 
    eapply tctx_incl_trans. eapply (tctx_incl_frame_l _ _ +[_]). eapply tctx_incl_trans. eapply permdata_from_box. eapply tctx_incl_swap.
    simpl. eapply (tctx_incl_frame_r +[_; _] +[_] +[_]). eapply seq_cons. done.
    iApply type_jump; [solve_typing|solve_extract|].
    apply resolve_tctx_cons_hasty. eapply uniq_resolve'; [eapply always_true_ghostptrtoken_nodup'; lia|solve_typing]. apply resolve_tctx_nil.
    move=>post [[tc tf][v []]]Impl l' [eq nodup]/=. rewrite eq in Impl. apply Impl. done.
    apply not_elem_of_list_to_map_1. inversion_clear nodup. done.
  Qed.

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

  Lemma find_idx_spec' {A} P `{∀ x, Decision (P x)} (l: list A) (i: nat):
  find_idx P l = i ↔
    (i = length l ∨ ∃ x, l !! i = Some x ∧ P x) ∧ ∀ j y, l !! j = Some y → j < i → ¬P y.
  Proof.
    rewrite find_idx_alt. remember (list_find P l) as x. symmetry in Heqx. remember Heqx as eq. clear Heqeq. destruct x as [[??]|].
    rewrite list_find_Some in Heqx. destruct Heqx as (?&?&?). split.  move=>/=<-. split. right. exists a. done. done.
    intros ([|[?[??]]]&?). exfalso; eapply H4. exact H0. rewrite H3. eapply lookup_lt_Some. done. done.
    assert (list_find P l = Some (i, x)). rewrite list_find_Some. done.
    rewrite eq in H6. injection H6. done.
    rewrite list_find_None Forall_forall in Heqx. split. intros. split. left. done. intros. apply Heqx. eapply elem_of_list_lookup_2. done.
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
    rewrite 2! find_idx_alt list_find_fmap. remember (list_find (P ∘ f) l) as x. destruct x. done. rewrite fmap_length. done.
  Qed.

  Lemma find_idx_delete {K A} `{EqDecision K} `{FinMap K M} (l: list (K*A)) (k: K) (a: A):
    ((list_to_map l): M A) !! k = Some a → <[k:=a]>(list_to_map (base.delete (find_idx (λ x, x.1 = k) l) l): M A) = (list_to_map l) ∧ l !! (find_idx (λ x, x.1 = k) l) = Some (k, a).
  Proof.
    induction l as [|[??]]; simpl. rewrite lookup_empty. done.
    destruct (decide (k0 = k)) as [->|?]; simpl. rewrite lookup_insert. intros [= ->]. done.
    intros ?. rewrite lookup_insert_ne in H7; [|done]. destruct (IHl H7) as (<-&<-). rewrite -insert_commute; done.
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

  Lemma find_logic {𝔄 𝔄'} (ty: type (𝔄*𝔄')) (ty': plain_type 𝔄) `{!EqDecision 𝔄} :
    (∀ vπ ξl, ty_proph ty vπ ξl → ∃ (x: 𝔄) (vπ': proph 𝔄'), vπ = (λ π, (x, vπ' π))) → logic_fn +[ghostseq.ghostseq_ty ty; (ty': type 𝔄)] int (λ '-[l; k], find_idx (λ (x: (𝔄*𝔄')) , x.1 = k) l).
  Proof. intros ? (?&?&[]) ((?&?&?&->&->&?)&(?&?&->)&[]). exists [].
    revert x1 H0. simpl. induction x0 as [|fst rest]; intros; destruct x1; inversion_clear H0. exists 0%Z. done.
    destruct (H _ _ H1) as (fst'&?&->).  simpl. destruct (decide (fst' = x2)). exists 0%Z. done.
    destruct (IHrest x1 H2) as (res&eq). exists (Z.succ res). fun_ext=>π/=. specialize (equal_f eq π)=>/=<-. lia.
  Qed.


  Definition ghostptrtoken_remove {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "ptr"] :=
      Skip;;
      delete [ #1; "t"];;
      Skip;;
      (Skip;;Skip);;
      (Skip;;Skip);;
      return: ["ptr"].

  (* Rust's GhostPtrToken::remove *)
  Lemma ghostptrtoken_remove_type {𝔄} (ty: type 𝔄) :
    (ty.(ty_size) > 0) → typed_val (ghostptrtoken_remove ty) (fn<α>(∅; &uniq{α} (ghostptrtoken_ty ty), ptr) → box ty)
      (λ post '-[(al, al'); p], exists(a: 𝔄), ((list_to_gmap al) !! p = Some a) ∧ (((list_to_gmap al') = (base.delete p (list_to_gmap al))) → post a)).
  Proof.
    intros ??. eapply type_fn; [apply _|]=> α ??[l[l2[]]]. simpl_subst. via_tr_impl.
    iApply ghost_read_delete; [done|]. iIntros.
    iApply type_resolve'. eapply resolve_unblock_tctx_cons_keep_and_learn. eapply always_true_uniq. apply always_true_ghostptrtoken_nodup'. lia. solve_typing. solve_typing.
    iApply ghost_new; [solve_typing|].
    iApply typed_body_tctx_incl. eapply tctx_incl_trans. eapply tctx_incl_tail. apply tctx_incl_swap. apply tctx_incl_swap.
    iApply ghost_new; [solve_typing|].
    iApply typed_body_tctx_incl. eapply tctx_incl_trans. eapply tctx_incl_tail. eapply tctx_incl_trans. apply tctx_incl_swap. eapply tctx_incl_tail. apply tctx_incl_swap.
    eapply tctx_incl_trans. eapply (tctx_incl_frame_r +[_; _]). eapply tctx_incl_trans. eapply tctx_incl_tail. eapply (logic_fn_ghost_tctx_incl' [_] _ +[]). apply uniq_curr_logic_fn.
    eapply tctx_incl_trans. apply tctx_incl_swap. eapply (logic_fn_ghost_tctx_incl' [_; _] _ +[_]).
    apply find_logic. intros ??(?&?&->&?). eexists _, _. done. eapply tctx_incl_trans. eapply tctx_incl_swap.
    eapply ghost_update; [done|solve_typing|]. 
    eapply tctx_incl_trans. eapply (tctx_incl_frame_r +[_; _]). eapply seq_remove. done. eapply tctx_incl_tail. eapply tctx_incl_trans. eapply tctx_incl_swap. eapply permdata_to_box. 
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
    rewrite /trans_upper /trans_tail. move=>post [[tc tf][l' []]] [v [lookup Impl]] no_dup/=.
    eexists _, _. split. done. simpl in no_dup. destruct (find_idx_delete' _ _ _ no_dup lookup) as (?&->). split. done. split. done.
    intros. apply Impl. rewrite H1 -H0. done.
  Qed.
    
End ghostptrtoken_insertremove.
