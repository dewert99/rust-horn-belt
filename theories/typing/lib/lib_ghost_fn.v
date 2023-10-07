From lrust.util Require Export pairwise.
From lrust.typing Require Export type ghost_fn.
From lrust.typing Require Import array_util typing always_true option.
From lrust.typing.lib Require Import option maybe_uninit list ghostptrtoken.ghostseq.
From stdpp Require Import numbers.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section lib_ghost_fn.
  Context `{!typeG Σ}.

  Lemma none_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (option_ty ty) None. 
  Proof. 
    epose ((mod_create_ghost_fn $ (xsum_inj_ghost_fun _ $ _))%GB: ghost_fn_proph (option_ty ty) _).
    Unshelve. 3:{exact 0%fin. } 3:{ exact unit_create_ghost_fn. } done. 
  Qed.

  Lemma some_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (ty → option_ty ty) Some. 
  Proof. 
    eapply (λ x, _)%GB. Unshelve. epose (((mod_create_ghost_fn $ (xsum_inj_ghost_fun _ $ _)))%GB: ghost_fn_proph (option_ty ty) _).
    Unshelve. 3:{exact 1%fin. } 3:{ exact x. } done. 
  Qed.

  Lemma option_destruct_ghost_fn {𝔄 𝔅} {ty: type 𝔄} {tyr: type 𝔅} fπ: 
    (ghost_fn_proph tyr (λ π, fπ π None)) → (ghost_fn_proph (ty → tyr) (λ π x, fπ π (Some x))) → (ghost_fn_proph ((option_ty ty) → tyr) fπ).
  Proof. 
    intros Nf Sf. eapply mod_destruct_ghost_fn. eapply xsum_destruct_ghost_fn. intros i.
    inv_fin i. exact (unit_destruct_ghost_fn Nf). intros. inv_fin i. exact Sf. intros. inv_fin i.
  Qed.

  Lemma maybe_uninit_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (? ty → option_ty ty) id.
  Proof. intros ??[(->&->)|(?&->&?)]. apply none_ghost_fn. eapply (some_ghost_fn $ _). done. Qed.

  Program Definition id_proph {𝔄} (vπ: proph 𝔄): type 𝔄 := {|
    st_size := 0;  st_lfts :=[];  st_E := [];
    st_proph vπ' ξl := vπ' = vπ /\ vπ' ./[𝔄] ξl;
    st_own vπ d tid vl := False
  |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. move=> /= ????[??]. done. Qed.

  Lemma seq_ind_ghost_fn {𝔄 𝔅} {ty : type 𝔄} {tyr: ghost_fn_type 𝔅} {fπ} :
  (forall (ty': (type (listₛ 𝔄))), (ghost_fn_proph (ty' → tyr) fπ → ghost_fn_proph (ty → ty' → tyr) (λ π x l, (fπ π (x :: l)))))
   → (ghost_fn_proph tyr (λ π, fπ π [])) → ghost_fn_proph ((ghostseq_ty ty) → tyr) fπ.
  Proof. 
    fold of_syn_type. intros ????(?&?&->&->&?). revert x0 H1. induction x; intros. apply H0.
    inversion_clear H1. eapply ((H _ (λ l, _) $ _) $ _). done. Unshelve. 2:{eapply id_proph. exact (lapply x). }
    split. reflexivity. simpl. eapply ty_proph_weaken_big_sepL'. done.
    intros ? [-> ?]. eapply IHx. done.
  Qed.

  Lemma nil_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (ghostseq_ty ty) [].
  Proof. eexists [], [], []. split. done. split. fun_ext=>π. done. apply Forall2_nil. Qed.

  Lemma cons_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (ty → ghostseq_ty ty → ghostseq_ty ty) cons.
  Proof. intros ?????(?&?&->&->&?). eexists _, (_ :: _), (_ :: _). intuition. constructor; done. Qed.

  Lemma seq_take_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (int → ghostseq_ty ty → ghostseq_ty ty) (λ n, (take (Z.to_nat n))).
  Proof. 
    intros ??(?&->)??(?&?&->&->&?). simpl. eexists _, _, _.
    split. done. split. fun_ext=>π. rewrite /lapply -fmap_take. done. apply Forall2_take. done.
  Qed.

  Lemma seq_drop_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (int → ghostseq_ty ty → ghostseq_ty ty) (λ n, (drop (Z.to_nat n))).
  Proof. 
    intros ??(?&->)??(?&?&->&->&?). simpl. eexists _, _, _.
    split. done. split. fun_ext=>π. rewrite /lapply -fmap_drop. done. apply Forall2_drop. done.
  Qed.

  Lemma seq_lookup_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (int → ghostseq_ty ty → option_ty ty) (λ i, lookup (Z.to_nat i)).
  Proof. 
    intros ??(?&->)??(?&?&->&->&?). rewrite Forall2_lookup in H. specialize (H (Z.to_nat x)).
    erewrite functional_extensionality; [|intros; rewrite /lapply list_lookup_fmap; simpl; reflexivity].
    destruct (x0 !! Z.to_nat x). inversion_clear H. eapply (ghost_fn_app some_ghost_fn). eexists _. done. apply none_ghost_fn.
  Qed.

End lib_ghost_fn.

Notation "`None`" := none_ghost_fn: ghost_fn_builder_scope.
Notation "( `Some` x )" := (some_ghost_fn $ x)%GB: ghost_fn_builder_scope.
Notation "[ ]" := nil_ghost_fn: ghost_fn_builder_scope.
Notation cons_ghost_fn2 x y :=  ((cons_ghost_fn $ x) $ y).
Notation "x :: y" := (ghost_fn_app (ghost_fn_app cons_ghost_fn x) y)  (at level 60, right associativity): ghost_fn_builder_scope.

Section lib_ghost_fn.
  Opaque ghost_fn_proph.
  Context `{!typeG Σ}.
  
  Definition singleton_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (ty → ghostseq_ty ty) (λ x, [x]) 
    := (λ x, x :: [])%GB.

  Lemma app_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (ghostseq_ty ty → ghostseq_ty ty → ghostseq_ty ty) (++).
  Proof. 
    apply seq_ind_ghost_fn. intros ? app. 
    eapply (λ hd tl oth, (hd :: ((app $ tl) $ oth)))%GB.
    eapply (λ oth, oth)%GB.
  Qed.

  Lemma seq_length_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (ghostseq_ty ty → int) length.
  Proof. 
    apply seq_ind_ghost_fn. intros ? len. refine (λ x l, _)%GB. apply succ_ghost_fn.  eapply (len $ l)%GB. eapply plain_ret_ghost_fn.
  Qed.


  Lemma list_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (list_ty ty → ghostseq_ty ty) id.
  Proof. 
    apply fix_ind_ghost_fn=>? f. apply mod_destruct_ghost_fn. apply xsum_destruct_ghost_fn.
    intros i. inv_fin i. apply unit_destruct_ghost_fn. apply nil_ghost_fn.
    intros i. inv_fin i. apply pair_destruct_ghost_fn. eapply (λ x b, (x :: (box_deref_ghost_fn $ (f $ b))))%GB.
    intros i. inv_fin i.
  Qed.

End lib_ghost_fn.
