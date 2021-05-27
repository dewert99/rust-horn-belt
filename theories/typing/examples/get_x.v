From iris.proofmode Require Import tactics.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section get_x.
  Context `{!typeG Σ}.

  Definition get_x: val :=
    fn: ["p"] :=
      let: "p'" := !"p" in Share;;
      letalloc: "r" <- "p'" in
      delete [ #1; "p"];; return: ["r"].

  Lemma get_x_type :
    typed_val get_x (fn<α>(∅; &uniq{α} (int * int)) → &shr{α} int)
      (λ post '-[(zz, zz')], zz' = zz → post zz.1).
  Proof.
    move=> ??. eapply type_fn; [solve_typing|]=>/= ???[p[]]. simpl_subst. via_tr_impl.
    { iApply type_deref; [solve_extract|solve_typing|solve_typing|]. intro_subst.
      iApply type_share; [solve_extract|solve_typing|].
      (* TODO: make automation work for product split *)
      iApply (type_letalloc_1 (&shr{_} int));
        [eapply tctx_extract_split_shr_prod; solve_typing|done|]. intro_subst.
      iApply type_delete; [solve_extract|done|done|].
      iApply type_jump; [solve_typing|solve_extract|solve_typing]. }
    by move=> ?[[[??]?][]]/=.
  Qed.
End get_x.
