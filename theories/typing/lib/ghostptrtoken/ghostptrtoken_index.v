From lrust.typing Require Export type always_true.
From lrust.typing Require Import uniq_util typing ptr logic_fn.
From lrust.util Require Import list.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken_basic ghostseq_basic permdata_basic.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section find_logic.
  Context `{!typeG Σ}.
  Lemma find_logic {𝔄 𝔄'} (ty: type (𝔄*𝔄')) (ty': plain_type 𝔄) `{!EqDecision 𝔄} :
    (∀ vπ ξl, ty_proph ty vπ ξl → ∃ (x: 𝔄) (vπ': proph 𝔄'), vπ = (λ π, (x, vπ' π))) → logic_fn +[ghostseq.ghostseq_ty ty; (ty': type 𝔄)] int (λ '-[l; k], find_idx (λ (x: (𝔄*𝔄')) , x.1 = k) l).
  Proof. intros ? (?&?&[]) ((?&?&?&->&->&?)&(?&?&->)&[]). exists [].
    revert x1 H0. simpl. induction x0 as [|fst rest]; intros; destruct x1; inversion_clear H0. exists 0%Z. done.
    destruct (H _ _ H1) as (fst'&?&->).  simpl. destruct (decide (fst' = x2)). exists 0%Z. done.
    destruct (IHrest x1 H2) as (res&eq). exists (Z.succ res). fun_ext=>π/=. specialize (equal_f eq π)=>/=<-. lia.
  Qed.

  Lemma find_permdata_logic {𝔄} (ty: type 𝔄) :
    logic_fn +[ghostptrtoken_ty ty; ptr] int (λ '-[l; k], find_idx (λ x , x.1 = k) l).
  Proof. apply find_logic. intros ??(?&?&->&?). eexists _, _. done. Qed.
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
    eapply tctx_incl_trans. eapply (tctx_incl_frame_r +[_; _]). eapply tctx_incl_trans. eapply tctx_incl_tail. eapply (logic_fn_ghost_tctx_incl' [_] _ +[]). apply shr_deref_logic_fn.
    eapply tctx_incl_trans. apply tctx_incl_swap. eapply (logic_fn_ghost_tctx_incl' [_; _] _ +[_]).
    apply find_permdata_logic. eapply tctx_incl_trans. eapply tctx_incl_swap. apply seq_shr_index. done. eapply permdata_shr.
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
