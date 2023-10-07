From lrust.typing Require Export type always_true.
From lrust.typing Require Import uniq_util typing ptr lib_ghost_fn.
From lrust.util Require Import list.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken_basic ghostseq_basic permdata_basic.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section find_logic.
  Context `{!typeG Σ}.

  Lemma find_ghost_fn {𝔄 𝔄'} (ty: type 𝔄) (ty': type 𝔄') (f: 𝔄' → 𝔄 → Prop) `{!RelDecision f} :
    (ghost_fn (ty' → ty → bool_ty) (λ x y, (bool_decide (f x y)))) → ghost_fn (ty' → ghostseq.ghostseq_ty ty → int) (λ k, find_idx (f k)).
  Proof. 
    fold of_syn_type. intros F. refine (λ k, _)%GB. eapply seq_ind_ghost_fn.
    intros ? find. fold of_syn_type. refine (λ hd tl,  _)%GB.  erewrite functional_extensionality. 
    refine (((ite_ghost_fn $ ((F $ k) $ hd)) $ %(0: Zₛ)) $ _)%GB. eapply succ_ghost_fn. eapply (find $ tl)%GB.
    intros ?. simpl. rewrite /bool_decide /decide. destruct (decide_rel f (o x) (o0 x)); done.  eapply (%(0: Zₛ))%GB.
  Qed.

  Lemma find_permdata_ghost_fn {𝔄} {ty: type 𝔄} :
    ghost_fn (ptr → ghostptrtoken_ty ty → int) (λ k, find_idx (λ x , (x.1 = k))).
  Proof.
    fold of_syn_type. eapply (find_ghost_fn (permdata_ty ty) ptr). eapply plain_arg_ghost_fn=>l.
    intros ??(?&?&->&?). erewrite functional_extensionality. eapply (% ((bool_decide (x = l)): boolₛ))%GB. done.
  Qed.
End find_logic.

Section ghostptrtoken_borrow.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_borrow {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "p"] :=
      Skip;;
      delete [ #1; "t"];;
      (Skip;;Skip);;
      (Skip;;Skip);;
      return: ["p"].
  Opaque ghost_fn_proph.

  (* Rust's GhostPtrToken::borrow_mut *)
  Lemma ghostptrtoken_borrow_type {𝔄} (ty: type 𝔄):
    typed_val (ghostptrtoken_borrow ty) (fn<α>(∅; &shr{α} (ghostptrtoken_ty ty), ptr) → &shr{α} ty)
      (λ post '-[l; ptr], exists v, (list_to_gmap l) !! ptr = Some(v) ∧ post (v)).
  Proof.
    fold of_syn_type. eapply type_fn; [apply _|]=> ???[ol[pl[]]]. simpl_subst. via_tr_impl.
    iApply ghost_read_delete. done. iIntros (?).
    iApply ghost_new; [solve_typing|].
    iApply typed_body_tctx_incl. eapply tctx_incl_trans. eapply tctx_incl_tail. apply tctx_incl_swap. apply tctx_incl_swap.
    iApply ghost_new; [solve_typing|].
    iApply typed_body_tctx_incl. eapply tctx_incl_trans. eapply tctx_incl_swap. eapply tctx_incl_trans. eapply tctx_incl_tail. 
    eapply tctx_incl_trans. eapply (tctx_incl_frame_r +[_; _]).  eapply (logic_fn_ghost_tctx_incl' [_; _] _ +[_] int  (λ '-[x; y], _)).
    apply (λ ptr token, ((find_permdata_ghost_fn $ (box_deref_ghost_fn $ ptr)) $ (shr_deref_ghost_fn $ token)))%GB. 
    eapply tctx_incl_trans. eapply tctx_incl_swap. apply seq_shr_index. done. eapply permdata_shr.
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
    rewrite /trans_upper /trans_tail. move=>post [s[l []]][v [lookup ?]]. simpl.
    eexists _, _. destruct (find_idx_delete _ _ _ lookup). intuition. rewrite H0. done. done.
  Qed.
End ghostptrtoken_borrow.

Section ghostptrtoken_insertremove.
  Context `{!typeG Σ}.

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
    eapply tctx_incl_trans. eapply (tctx_incl_frame_r +[_; _]). eapply (logic_fn_ghost_tctx_incl' [_; _] _ +[_] int  (λ '-[x; y], _)).
    refine (λ ptr token, _)%GB. erewrite functional_extensionality. apply ((find_permdata_ghost_fn $ (box_deref_ghost_fn $ ptr)) $ (uniq_curr_ghost_fn $ token))%GB. intros x. simpl. remember (o x). remember (o0 x). done.
    eapply tctx_incl_trans. eapply tctx_incl_swap.
    eapply ghost_update; [done|solve_typing|]. 
    eapply tctx_incl_trans. eapply (tctx_incl_frame_r +[_; _]). eapply seq_remove. done. eapply tctx_incl_tail. eapply tctx_incl_trans. eapply tctx_incl_swap. eapply permdata_to_box. 
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
    rewrite /trans_upper /trans_tail. move=>post [[tc tf][l' []]] [v [lookup Impl]] no_dup/=.
    eexists _, _. split. done. simpl in no_dup. destruct (find_idx_delete' _ _ _ no_dup lookup) as (?&?). split. done. split. done.
    intros. apply Impl. rewrite H2 -H0. done.
  Qed.
    
End ghostptrtoken_insertremove.
