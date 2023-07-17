From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr zst.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken_basic heap_util ghostseq_basic.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_merge.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_merge {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "t2"] :=
      Skip;;
      delete [ #1; "t"];;
      return: [null_val].

  Lemma ghostptrtoken_merge_type {𝔄} (ty: type 𝔄) :
    (ty_size ty > 0)%Z → typed_val (ghostptrtoken_merge ty) (fn<α>(∅; &uniq{α} (ghostptrtoken_ty ty), ghostptrtoken_ty ty) → ())
      (λ post '-[(al, al'); al2], al' = al2 ++ al → NoDup al'.*1 → post ()).
  Proof.
    intros ?. eapply type_fn; [apply _|]=> α ??[l[l2[]]]. simpl_subst. via_tr_impl.
    iApply ghost_read_delete; [done|]. iIntros. iApply typed_body_tctx_incl.
    eapply ghost_update; [done|solve_typing|]. eapply tctx_incl_trans. eapply seq_fappend. unfold ghostptrtoken_ty. eapply tctx_incl_trans. eapply ghost_dummy'.
    eapply tctx_incl_swap. iApply type_jump; [solve_typing|solve_extract|].
    apply resolve_tctx_cons_hasty; [apply uniq_ghostptrtoken_resolve; [done|solve_typing]|apply resolve_tctx_nil].
    move=>post [[??][?[]]]Impl[eq?]/=. rewrite eq in Impl. by apply Impl.
  Qed.
End ghostptrtoken_merge.
