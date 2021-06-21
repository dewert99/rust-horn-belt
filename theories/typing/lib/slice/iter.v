From lrust.typing Require Export type.
From lrust.typing Require Import typing uniq_array_util.
From lrust.typing.lib.slice Require Import uniq_slice.
Set Default Proof Using "Type".

Implicit Type 𝔄: syn_type.

Section iter.
  Context `{!typeG Σ}.

  (** We model the unique iterator the same as the unique slice *)
  Definition iter_uniq {𝔄} (κ: lft) (ty: type 𝔄) : type (listₛ (𝔄 * 𝔄)) :=
    uniq_slice κ ty.

  Definition iter_next {𝔄} (ty: type 𝔄) : val :=
    fn: ["b"] :=
      let: "it" := !"b" in delete [ #1; "b"];;
      let: "l" := !"it" in
      "it" <- "l" +ₗ #ty.(ty_size);; "it" +ₗ #1 <- !("it" +ₗ #1) - #1;;
      letalloc: "r" <- "l" in return: ["r"].

  (* The precondition requires that is the sliced list is non-empty *)
  Lemma iter_uniq_next_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_uniq α ty)) → &uniq{α} ty)
      (λ post '-[(aal, aal')],
        ∃(aa: 𝔄 * 𝔄) aalₜ, aal = aa :: aalₜ ∧ (aal' = aalₜ → post aa)).
  Proof.
    eapply type_fn; [apply _|]. move=>/= [α β]??[b[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[b _] #Obs".
    rewrite tctx_hasty_val. iDestruct "b" as ([|]) "[#⧖' box]"=>//.
    case b as [[|b|]|]=>//=. rewrite split_mt_uniq_bor.
    iDestruct "box" as "[(#In' & %it &%& %ξi &>[% %Eq2]& >↦b & Vo & Bor) †b]".
    set ξ := PrVar _ ξi. wp_read.
    iMod (lctx_lft_alive_tok β with "E L") as (?) "(β & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor β") as "[big ToBor]"; [done|]. wp_let.
    iDestruct "big" as (??) "(#⧖ & Pc & ↦it)". rewrite split_mt_uniq_slice.
    iDestruct "↦it" as "(#In &%&%&%& big)".
    rewrite freeable_sz_full -heap_mapsto_vec_singleton.
    wp_apply (wp_delete with "[$↦b $†b]"); [done|]. iIntros "_". wp_seq.
    iDestruct "big" as (aπζil [->?]) "(↦ & ↦' & uniqs)".
    wp_read. wp_let. wp_op. wp_write. do 2 wp_op. wp_read. wp_op. wp_write.
    wp_apply wp_new; [done..|]. iIntros (r) "[†r ↦r]". wp_let.
    rewrite heap_mapsto_vec_singleton. wp_write.
    set aaπl := vmap _ _. iDestruct (uniq_agree with "Vo Pc") as %[Eq1 <-].
    have ->: vπ = λ π, (lapply aaπl π, π ξ).
    { by rewrite [vπ]surjective_pairing_fun Eq1 Eq2. }
    iMod (proph_obs_sat with "PROPH Obs") as %(?&?&?& Eq &_); [done|].
    case aπζil as [|[aπ ζi] n' aπζil']; [done|]=>/=.
    iDestruct "uniqs" as "[uniq uniqs]". rewrite shift_loc_0.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[Pc ↦ ↦' uniqs]") as "[Bor β]".
    { iNext. iExists _, _. rewrite split_mt_uniq_slice. iFrame "⧖ Pc In".
      iExists _, _, _, aπζil'. have ->: (S n' - 1)%Z = n' by lia.
      setoid_rewrite <-shift_loc_assoc_nat. by iFrame. }
    iMod ("ToL" with "β L") as "L".
    set aaπl' := vmap _ aπζil'. rewrite /uniq_own. set ζ := PrVar _ ζi.
    iApply (type_type
      +[#it ◁ &uniq{β} (iter_uniq α ty); #r ◁ box (&uniq{α} ty)]
      -[λ π, (lapply aaπl' π, π ξ); λ π, (aπ π, π ζ)]
      with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_). iSplitL "Vo Bor"; [|iSplitL; [|done]].
      + iExists _. iFrame "⧖ In'". iExists _, _. rewrite /uniq_own.
        rewrite (proof_irrel (@prval_to_inh (listₛ (_*_)) (lapply aaπl'))
          (@prval_to_inh (listₛ (_*_)) (fst ∘ vπ))).
        by iFrame.
      + iExists _. rewrite -freeable_sz_full. iFrame "⧖' †r". iNext.
        rewrite split_mt_uniq_bor. iFrame "In". iExists _, _, _. iFrame.
        iPureIntro. split; [lia|done].
    - by iApply proph_obs_impl; [|done]=>/= ?[?[?[[=<-<-]?]]].
  Qed.

  Definition iter_next_back {𝔄} (ty: type 𝔄) : val :=
    fn: ["b"] :=
      let: "it" := !"b" in delete [ #1; "b"];;
      let: "len" := !("it" +ₗ #1) - #1 in "it" +ₗ #1 <- "len";;
      letalloc: "r" <- !"it" +ₗ "len" * #ty.(ty_size) in return: ["r"].

  (* The precondition requires that is the sliced list is non-empty *)
  Lemma iter_uniq_next_back_type {𝔄} (ty: type 𝔄) :
    typed_val (iter_next_back ty)
      (fn<(α, β)>(∅; &uniq{β} (iter_uniq α ty)) → &uniq{α} ty)
      (λ post '-[(aal, aal')],
        ∃aalᵢ (aa: 𝔄 * 𝔄), aal = aalᵢ ++ [aa] ∧ (aal' = aalᵢ → post aa)).
  Proof.
  Admitted.
End iter.
