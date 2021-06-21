From lrust.typing Require Export type.
From lrust.typing Require Import uniq_array_util typing.
From lrust.typing.lib Require Import vec.vec slice.uniq_slice.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section vec_slice.
  Context `{!typeG Σ}.

  Definition vec_to_slice: val :=
    fn: ["bv"] :=
      let: "v" := !"bv" in delete [ #1; "bv"];;
      let: "r" := new [ #2] in
      "r" <- !"v";; "r" +ₗ #1 <- !("v" +ₗ #1);;
      return: ["r"].

  Lemma vec_to_uniq_slice_type {𝔄} (ty: type 𝔄) :
    typed_val vec_to_slice (fn<α>(∅; &uniq{α} (vec_ty ty)) → uniq_slice α ty)
      (λ post '-[(al, al')], length al' = length al → post (zip al al')).
  Proof.
    eapply type_fn; [apply _|]=>/= α ??[bv[]]. simpl_subst.
    iIntros (?(vπ &[])?) "#LFT #TIME #PROPH UNIQ E Na L C /=[bv _] Obs".
    rewrite tctx_hasty_val. iDestruct "bv" as ([|]) "[_ box]"=>//.
    case bv as [[|bv|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In &%&%& %ξi &>[% %Eq2]& ↦bv & Vo & Bor) †bv]".
    wp_read. wp_seq. rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦bv $†bv]"); [done|]. iIntros "_".
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Bor α") as "[big ToBor]"; [done|]. wp_seq.
    iDestruct "big" as (? d') "(#⧖ & Pc & big)". rewrite split_mt_vec.
    case d'=>// ?. iDestruct "big" as (??? aπl ->) "(↦₀ & ↦₁ & ↦₂ & ↦tys & ex & †)".
    wp_bind (new _). iApply (wp_cumulative_time_receipt with "TIME"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (?) "[†r ↦r] ⧗". wp_let.
    set ξ := PrVar _ ξi. iDestruct (uniq_agree with "Vo Pc") as %[Eq1 ->].
    have ->: vπ = λ π, (lapply aπl π, π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    rewrite !heap_mapsto_vec_cons. iDestruct "↦r" as "(↦r & ↦r' &_)".
    wp_read. wp_write. do 2 wp_op. wp_read. wp_write. do 2 wp_seq.
    iMod (uniq_intro_vec aπl with "PROPH UNIQ") as (ζil) "VoPcs"; [done|].
    iDestruct (uniq_proph_tok_vec with "VoPcs") as "[ζl VoPcs]".
    set aπζil := vzip _ _. set ζl := map _ aπζil.
    set aπl' := vmap (λ aπζi (π: proph_asn),
      π (PrVar (𝔄 ↾ prval_to_inh aπζi.1) aπζi.2): 𝔄) aπζil.
    set aaπl := vmap (λ aπζi π,
      (aπζi.1 π, π (PrVar (𝔄 ↾ prval_to_inh aπζi.1) aπζi.2): 𝔄)) aπζil.
    iMod (uniq_preresolve ξ ζl (lapply aπl') with "PROPH Vo Pc ζl")
      as "(Obs' & ζl & ToPc)"; [done|..].
    { rewrite -vec_to_list_apply. apply proph_dep_constr, proph_dep_prvars. }
    iCombine "Obs' Obs" as "#?". iSpecialize ("VoPcs" with "ζl").
    iDestruct (big_sepL_sep with "VoPcs") as "[Vos Pcs]".
    iMod ("ToBor" $! (big_sepL _ _) with "[⧗ ↦₀ ↦₁ ↦₂ ex † ToPc] [↦tys Pcs]")
      as "[Bor α]"; last first.
    - iMod ("ToL" with "α L") as "L". rewrite cctx_interp_singleton.
      iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
      iApply ("C" $! [# #_] -[lapply aaπl] with "Na L [-]").
      + rewrite/= right_id (tctx_hasty_val #_) -freeable_sz_full. iExists _.
        iFrame "⧖ †r". iNext. rewrite split_mt_uniq_slice. iFrame "In".
        iExists _, _, _, _. rewrite big_sepL_sep. by iFrame.
      + iApply proph_obs_impl; [|done]=>/= π [-> Imp].
        have ->: lapply aaπl π = zip (lapply aπl π) (lapply aπl' π).
        { clear. induction aπl; inv_vec ζil=>//= *. by f_equal. }
        apply Imp. clear. induction aπl; inv_vec ζil=>//= *. by f_equal.
    - iNext. iApply (merge_big_sepL_proph_ctrl_mt_ty_own with "[] Pcs ↦tys").
      iApply persistent_time_receipt_mono; [|done]. lia.
    - iIntros "!> big".
      iDestruct (split_big_sepL_proph_ctrl_mt_ty_own with "PROPH ⧖ big") as "big".
      iMod (bi.later_exist_except_0 with "big") as (wπl ?) "(>⧖' & Eqzs & ↦tys)".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖'") as "⧖'"; [solve_ndisj|].
      iIntros "!>!>". iExists (lapply wπl), _. iFrame "⧖'". iSplitL "Eqzs ToPc".
      { iApply "ToPc". rewrite -!vec_to_list_apply.
        iApply proph_eqz_constr. iApply (proph_eqz_prvars with "Eqzs"). }
      rewrite split_mt_vec. iExists _, _, _, _. by iFrame.
  Qed.
End vec_slice.