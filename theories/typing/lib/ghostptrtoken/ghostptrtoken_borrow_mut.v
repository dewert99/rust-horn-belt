From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr.
From lrust.typing.lib Require Import ghostptrtoken.ghostptrtoken.
Set Default Proof Using "Type".

Open Scope nat.

Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_insertremove.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_borrow_mut {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "b"] :=
      delete [ #1; "t"];;
      Skip;;
      return: ["b"].

  (* Rust's GhostPtrToken::borrow_mut *)
  Lemma ghostptrtoken_borrow_mut_type {𝔄} (ty: type 𝔄) (α β: lft):
    typed_val (ghostptrtoken_borrow_mut ty) (fn(∅; &uniq{α} (&uniq{β} (ghostptrtoken_ty ty)), ptr) → &uniq{β} ty)
      (λ post '-[((ol, ol'), (nl, nl')); ptr], exists v, (list_to_gmap ol) !! ptr = Some(v) ∧ (<[ptr:=v]>(list_to_gmap nl) = (list_to_gmap ol) → forall v', (ol' = (ptr,v')::nl') → post (v, v'))).
  Proof.
    fold of_syn_type. eapply type_fn; [apply _|]=> ???[ol[pl[]]]. simpl_subst.
    iIntros (?(lππ & pπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(ol & p &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "ol" as ([|dm]) "[_ ol]"=>//.
    case ol as [[|ol|]|]=>//. iDestruct "ol" as "[(%oll & >↦ol & [#LftIn uniq]) †ol]".
    case oll as [|[[|m|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "p" as ([|dx]) "[⧖p p]"=>//. case pl as [[|pl|]|]=>//=.
    iDestruct "p" as "[p' †p]".
    wp_bind (delete _). iApply (wp_cumulative_time_receipt with "TIME"); [done|]. rewrite freeable_sz_full.
    iApply ((wp_delete [ #m])with "[↦ol †ol]"); [done| by iFrame|]. 
    iNext. iIntros "_ ⧗".
    iDestruct "p'" as (?) "(↦p&(%p&->&->))". simpl.
    iDestruct "uniq" as (du ξi [? Eq2]) "[OVo OBor]".
    move: Eq2. set ξ := PrVar _ ξi => Eq2.
    iMod (lctx_lft_alive_tok β with "E L") as (?) "(β & L & ToL)"; [solve_typing..|].
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL2)"; [solve_typing..|].
    iMod (bor_acc with "LFT OBor α") as "[(%&%& #⧖u & OPc & (%vl&↦utoken&#βin&uniq')) ToOBor]"; [done|].
    wp_seq. iCombine "⧖p ⧖u" as "#⧖". simpl.
    iDestruct (uniq_agree with "OVo OPc") as %[<-<-].
    destruct vl as [|[[|l'|]|][]]; simpl; try by iDestruct "uniq'" as "[]".
    iDestruct "uniq'" as (dv ζi [? Eq3]) "[Vo Bor]".
    move: Eq3. set ζ := PrVar _ ζi => Eq3.
    iMod (bor_acc_cons with "LFT Bor β") as "[(%&%&_& Pc & ↦token) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<- <-) "[Vo Pc]".
    wp_seq.
    rewrite split_mt_token. case dv as [|dv]. done.
    simpl. iDestruct "↦token" as (aπl) "(%Eq1 & ↦l & ↦tys†)".
    remember ((list_to_gmap aπl) !! p) as vπ. symmetry in Heqvπ. destruct vπ as [vπ|]; last first.
    iMod (proph_obs_sat with "PROPH Obs") as %(πw&obs). done.
    exfalso. remember (equal_f Eq1 πw). clear Heqe.
    simpl in e. destruct (lππ πw) as [[??][??]]. simpl in e.
    destruct obs as (v&obs&_). 
    rewrite e /alapply list_to_map_fmap
    lookup_fmap Heqvπ in obs. done.
    destruct (elem_of_list_to_map_2' _ _ _ Heqvπ) as (rπ&perm&reinsert).
    unfold big_sepAL.
    iEval (rewrite perm 2! big_sepL_cons) in "↦tys†".
    iDestruct "↦tys†" as "((↦ty&↦tys)&(†&†s))".
    iMod (uniq_intro (𝔄:=listₛ (locₛ * 𝔄)) (alapply rπ) with "PROPH UNIQ") as (ζ'i) "[Vo' Pc']"; [done|].
    set ζ' := PrVar _ ζ'i. iDestruct (uniq_proph_tok with "Vo' Pc'") as "(Vo' & ζ' & Pc')".
    iMod (uniq_intro vπ with "PROPH UNIQ") as (ηi) "[RVo RPc]"; [done|].
    set η := PrVar _ ηi. iDestruct (uniq_proph_tok with "RVo RPc") as "(RVo & η & RPc)".
    rewrite 2! proph_tok_singleton.
    iDestruct (proph_tok_combine with "η ζ'") as (?) "[ηζ Toηζ]".
    iMod (uniq_preresolve ζ _ (λ π, (p, (π η)) :: (π ζ'))
    with "PROPH Vo Pc ηζ") as "(#Obs' & ηζ & ToPc)"; [done| |].
    apply proph_dep_constr2; [apply proph_dep_constr|]; apply proph_dep_one.
    iMod ((uniq_update ξ (λ π, (al_fmap _ rπ, π ζ'))) with "UNIQ OVo OPc") as "[OVo OPc]"; [done|].
    iDestruct ("Toηζ" with "ηζ") as "[η ζ']".
    (* iMod (uniq_resolve ξ with "PROPH OVo OPc ζ'") as "(Obs''&OPc&ζ')"; [done| |]; last first. *)
    iCombine "Obs' Obs" as "#?". iClear "Obs".
    iSpecialize ("Pc'" with "ζ'"). iSpecialize ("RPc" with "η").
    iMod ("ToBor" $! (_∗_)%I with "[ToPc † ⧗] [Pc' RPc ↦tys ↦l ↦ty †s]")
      as "[Bor β]"; last first.
    - iMod (bor_sep with "LFT Bor") as "(BorR&BorK)"; [done|].
    iMod ("ToOBor" with "[OPc ↦utoken βin Vo' BorK]") as "[OBor α]".
    {iNext. iExists _, _. iFrame "OPc ⧖u". iExists _. iFrame "↦utoken βin".
    iExists _, _. iSplit. iSplit. done. done.
    iFrame "Vo' BorK". }
    wp_seq.
    iMod ("ToL2" with "α L") as "L". iMod ("ToL" with "β L") as "L".
    iApply (type_type +[#m ◁ &uniq{α} (&uniq{β} (ghostptrtoken_ty ty)); #pl ◁ box (&uniq{β} ty)] -[(λ π, ((al_fmap (.$ π) rπ, π ζ'), π ξ)); (λ π, (vπ π, π η))]
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
    iSplitL "OVo OBor"; [|iSplitL; [|done]]; rewrite (tctx_hasty_val #_);
    iExists _. simpl. iFrame "⧖u". iFrame "LftIn".
    iExists du, _.
    unfold uniq_body.
    rewrite (proof_irrel (@prval_to_inh ((listₛ (locₛ * 𝔄)) * (listₛ (locₛ * 𝔄))) (λ π, (al_fmap (.$ π) rπ, π ζ'))) 
    (@prval_to_inh ((listₛ (locₛ * 𝔄)) * (listₛ (locₛ * 𝔄))) (fst ∘ lππ))).
    iFrame. done. 
    iFrame "⧖u †p". iNext. rewrite split_mt_uniq_bor. iFrame "βin". 
    iExists _, _, _. rewrite heap_mapsto_vec_singleton. iFrame "↦p RVo BorR". done.
    simpl.
    iApply proph_obs_impl; [|done] => π/=.
    move: (equal_f Eq1 π) (equal_f Eq2 π) (equal_f Eq3 π)=>/=.
    destruct (lππ π) as [[oam oam'][nam' nam]]. simpl.
    intros -><-<- (->&v&Contains&Imp) [= ->->]. rewrite /alapply list_to_map_fmap lookup_fmap_Some Heqvπ in Contains. destruct Contains as (?&<-&[=<-]).  
    apply Imp. rewrite /alapply 2! list_to_map_fmap -fmap_insert reinsert. done.
    done.
    - iNext. iSplitL "RPc ↦ty". iExists _, _. iFrame "RPc".
    iSplit. 
    iApply (persistent_time_receipt_mono with "⧖u"). lia.
    iApply (ty_own_mt_depth_mono with "↦ty"). lia.
    iExists _, _. iFrame. iSplitR.
    iApply (persistent_time_receipt_mono with "⧖"). lia.
    iExists _. iFrame. iExists _. iFrame. done.
    - iNext. iIntros "((%vπ'&%d'&>⧖d'&Pc1&↦ty)&(%mπ'&%d''&>⧖d''&Pc2&%vl&↦emp&↦tys))".
    iCombine "⧖d' ⧖d''" as "⧖d".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖d")
    as "⧖d"; [solve_ndisj|]. simpl.
    iModIntro. iNext. destruct d''. done. simpl. iDestruct "↦tys" as "(%aπl'&(->&->)&↦tys&†s)".
    iExists (λ π, ((p, (vπ' π)) :: (alapply aπl' π))), _. iFrame.
    iSplitL "Pc1 Pc2 ToPc". iApply "ToPc".
    iDestruct (proph_ctrl_eqz with "PROPH Pc1") as "Eqz1".
    iDestruct (proph_ctrl_eqz with "PROPH Pc2") as "Eqz2".
    iApply (proph_eqz_constr2 with "[Eqz1] Eqz2").
    iApply (proph_eqz_constr with "Eqz1").
    iExists _. iFrame. 
    iExists _. iSplit. iPureIntro. split. done. apply functional_extensionality. intros π.
    rewrite /alapply -/(prod_map id (.$ π) (p, vπ')) -fmap_cons. done.
    iFrame. iNext. unfold big_sepAL.
    rewrite big_sepL_cons. iSplitL "↦ty".
    iApply (ty_own_mt_depth_mono with "↦ty"). lia.
    iApply (big_sepL_mono with "↦tys"). iIntros (?[??]?) "↦ty".
    iApply (ty_own_mt_depth_mono with "↦ty"). lia.
  Qed.

End ghostptrtoken_insertremove.
