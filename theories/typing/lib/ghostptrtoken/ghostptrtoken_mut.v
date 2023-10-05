From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr always_true hints uniq_alt.
From lrust.util Require Import list.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken heap_util ghostptrtoken_basic.
Set Default Proof Using "Type".

Open Scope nat.

Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_mut.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_mut_mod {𝔄} (ll: list loc): ((listₛ (locₛ * 𝔄)) * (listₛ (locₛ * 𝔄)))%ST -> ((listₛ (locₛ * 𝔄)) * (listₛ (locₛ * 𝔄)))%ST :=
    prod_map id (filter (λ '(l, v), l ∉ ll)).

  Definition ghostptrtoken_ty_uniq_alt_base {𝔄} (ty: type 𝔄) κ vπ d tid vl :=
    (∃(ll: (list loc)) vπ', ⌜vπ = (ghostptrtoken_mut_mod ll) ∘ vπ'⌝ ∗ ([∗ list] l ∈ ll, &at{κ, lftN} (†{1}l…(ty_size ty))) ∗ ty_own (&uniq{κ} (ghostptrtoken_ty ty)) vπ' d tid vl)%I.

  Program Global Instance ghostptrtoken_ty_uniq {𝔄} (ty: type 𝔄): UniqAlt (ghostptrtoken_ty ty) := {
    ty_uniq_alt κ := 
    if (decide ((ty_size ty) > 0)%Z) 
       then ghostptrtoken_ty_uniq_alt_base ty κ
       else (ty_own (&uniq{κ} (ghostptrtoken_ty ty)));
  }.
  Next Obligation. intros. destruct (decide ((ty_size ty) > 0)%Z); [|eapply (@ty_uniq_alt_out _ _ _ (ghostptrtoken_ty ty) (base_ty_uniq _))].
    iIntros "(%&%&->&#†s&?)". iExists _, _. iFrame. iSplit. done. iSplit. iIntros (????) "?". iExists _, _. iFrame. iFrame "†s". done.
    iIntros (?????) "#LFT #PROPH κ token". rewrite ghostptrtoken_own_alt.  iDestruct "token" as (?) "(>[->->]&token)".
    iExists' aπl. iDestruct "token" as "($&owns)".
    iAssert (|={_}=>  ⌜Forall (λ '(l, _), l ∉ ll) aπl⌝  ∗ q.[κ] ∗ ▷ (big_sepL _ _))%I with "[-]" as ">(%&$&$)".
    iInduction aπl as [|[??]?] "IH". iFrame. done. simpl. iDestruct "owns" as "(own&owns)". 
    rewrite Forall_cons bi.pure_and. iMod ("IH" with "κ owns") as "($&κ&$)". iClear "IH".
    iInduction ll as [|] "IH". iFrame. iModIntro. iPureIntro. apply not_elem_of_nil. simpl. iDestruct "†s" as "(†&†s)".
    iMod (at_bor_acc_tok with "LFT † κ") as "(>†'&W)". solve_ndisj. solve_ndisj. iDestruct "own" as "[†''|>%to_false]"; [|rewrite to_false in g; lia].
    destruct (decide (l = a)) as [->|?]. iAssert (▷False)%I with "[-]" as ">[]". iNext. iApply (no_duplicate_freeable with "†' †''").
    iMod ("W" with "[†']") as "κ". iNext. done.
    rewrite not_elem_of_cons bi.pure_and. iMod ("IH" with "†s [†''] κ") as "($&κ&$)". iLeft. done. iFrame. done.
    iModIntro. iSplit; [|done]. iApply proph_obs_true=>π. simpl. eapply list_filter_True', Forall_fmap, Forall_impl. done. intros [??]. done.
  Qed.
  Next Obligation. intros. destruct (decide ((ty_size ty) > 0)%Z); [|done].
    iIntros "?". iExists [], _. simpl. iFrame. iPureIntro. fun_ext=>π. rewrite /ghostptrtoken_mut_mod /prod_map. simpl. 
    erewrite list_filter_iff, list_filter_True. destruct (vπ π). done. intros [??]. rewrite elem_of_nil. simpl. intuition.
  Qed.

  Lemma ghostptrtoken_own_uniq_alt {𝔄} (ty: type 𝔄) κ: 
    (ty_size ty > 0) → (ty_own (uniq_alt_ty κ (ghostptrtoken_ty ty))) = ghostptrtoken_ty_uniq_alt_base ty κ.
  Proof.
    replace (ty_own (uniq_alt_ty κ (_))) with (ty_uniq_alt κ); [|done]. simpl.
    intros. destruct (decide (ty.(ty_size) > 0)%Z); [|lia]. done.
  Qed.


  Definition ghostptrtoken_take_mut {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "b"] :=
      delete [ #1; "t"];;
      Skip;;
      return: ["b"].

  Lemma uniq_body_irrel {𝔄} (inhπ: proph 𝔄) (ty: type 𝔄) (vπ: proph 𝔄) (ξi: positive) (d: nat)
      (κ: lft) (tid: thread_id) (l: loc): uniq_body ty vπ ξi d κ tid l = (
    let ξ := PrVar (𝔄 ↾ prval_to_inh inhπ) ξi in
    .VO[ξ] vπ d ∗
    &{κ} (∃vπ' d', ⧖(S d') ∗ .PC[ξ, ty.(ty_proph)] vπ' d' ∗ l ↦∗: ty.(ty_own) vπ' d' tid))%I.
    Proof. erewrite (proof_irrel (prval_to_inh _) ). done. Qed. 

  Lemma pv_irrel {𝔄} (ξi: positive) (π: proph_asn) (inhπ: proph 𝔄) (inhπ': proph 𝔄): π (PrVar (𝔄 ↾ prval_to_inh inhπ) ξi) = π (PrVar (𝔄 ↾ prval_to_inh inhπ') ξi) :> 𝔄.
  Proof. erewrite (proof_irrel (prval_to_inh _) ). done. Qed. 

  (* Rust's GhostPtrToken::borrow_mut *)
  Lemma ghostptrtoken_take_mut_type {𝔄} (ty: type 𝔄) (α β: lft):
  (ty.(ty_size) > 0) →
    typed_val (ghostptrtoken_take_mut ty) (fn(∅; &uniq{α} (uniq_alt_ty β (ghostptrtoken_ty ty)), ptr) → &uniq{β} ty)
      (λ post '-[((ol, ol'), (nl, nl')); ptr], exists v, (list_to_gmap ol) !! ptr = Some(v) ∧ 
        (<[ptr:=v]>(list_to_gmap nl) = (list_to_gmap ol) →
         (list_to_gmap nl') !! ptr = None →
          forall v', ((list_to_gmap ol') = <[ptr:=v']>(list_to_gmap nl')) → post (v, v'))).
  Proof. intros ?.
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
    iMod (bor_acc with "LFT OBor α") as "[(%&%& #⧖u & OPc & (%vl&↦utoken&uniq')) ToOBor]"; [done|].
    rewrite ghostptrtoken_own_uniq_alt.
    iDestruct "uniq'" as (? lππ') "(>%EqAlt&at†s&#βin&%l'&>->&%dv&%ζi&>[% %Eq3]&[Vo Bor])".
    wp_seq. iCombine "⧖p ⧖u" as "#⧖". simpl.
    iDestruct (uniq_agree with "OVo OPc") as %[<-<-].
    move: Eq3. set ζ := PrVar _ ζi => Eq3.
    iMod (bor_acc_cons with "LFT Bor β") as "[(%&%&_& Pc & ↦token) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<- <-) "[Vo Pc]". setoid_rewrite split_mt_token.
    wp_seq. 
    iDestruct "↦token" as (aπl) "(%Eq1&↦l&↦tys†)".
    remember ((list_to_gmap aπl) !! p) as vπ. symmetry in Heqvπ. destruct vπ as [vπ|]; last first.
    iMod (proph_obs_sat with "PROPH Obs") as %(πw&obs). done.
    exfalso. move: (equal_f Eq1 πw) (equal_f EqAlt πw). simpl.
    destruct (lππ πw) as [[??][??]]. destruct (lππ' πw) as [??]. rewrite /ghostptrtoken_mut_mod. simpl.
    intros ->[= ->->].
    destruct obs as (v&obs&_). 
    rewrite /alapply list_to_map_fmap
    lookup_fmap Heqvπ in obs. done.
    destruct (elem_of_list_to_map_2' _ _ _ Heqvπ) as (rπ&perm&reinsert).
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
    iMod ((uniq_update ξ ((λ π, ghostptrtoken_mut_mod (p::ll) (al_fmap _ rπ, π ζ')))) with "UNIQ OVo OPc") as "[OVo OPc]"; [done|].
    iDestruct ("Toηζ" with "ηζ") as "[η ζ']".
    (* iMod (uniq_resolve ξ with "PROPH OVo OPc ζ'") as "(Obs''&OPc&ζ')"; [done| |]; last first. *)
    iCombine "Obs' Obs" as "#?". iClear "Obs".
    iSpecialize ("Pc'" with "ζ'"). iSpecialize ("RPc" with "η").
    iMod ("ToBor" $! (_∗_∗(† p … ty_size ty))%I with "[ToPc ⧗] [Pc' RPc ↦tys ↦l ↦ty † †s]")
      as "[Bor β]"; last first.
    - iMod (bor_sep with "LFT Bor") as "(BorR&BorK)"; [done|].
    iMod (bor_sep with "LFT BorK") as "(BorK&Bor†)"; [done|].
    iAssert (|={_}=>  ⌜p ∉ ll⌝  ∗ q'.[β] ∗ _  ∗ (big_sepL _ _))%I with "[β Bor† at†s]" as ">(%pNotIn&β&Bor†&at†s)".
    clear EqAlt. iInduction ll as [|] "IH". iFrame. iModIntro. iSplit; [|iExact "Bor†"]. iPureIntro. apply not_elem_of_nil.
    iDestruct "at†s" as "(at†'&at†s)". destruct (decide (p = a)) as [<-|?].
    iDestruct "β" as "(β&β')". iMod (bor_acc with "LFT Bor† β") as "(>†&_)". done.
    iMod (at_bor_acc_tok with "LFT at†' β'") as "(>†'&_)". done. done. iDestruct (no_duplicate_freeable with "† †'") as "[]".
    iMod ("IH" with "β Bor† at†s") as "(%&$&$&$)". iFrame. iPureIntro. apply not_elem_of_cons; done.
    iMod (bor_share_lftN with "Bor†") as "at†"; [done|].
    iMod ("ToOBor" with "[OPc ↦utoken βin Vo' BorK at†s at†]") as "[OBor α]".
    {iNext. iExists _, _. iFrame "OPc ⧖u". iExists _. iFrame "↦utoken βin".
    iExists _, _. iSplit. unfold compose. done. iFrame.
    iExists _, _. iSplit. iSplit. done. done.
    iFrame "Vo' BorK". }
    wp_seq.
    iMod ("ToL2" with "α L") as "L". iMod ("ToL" with "β L") as "L".
    iApply (type_type +[#m ◁ &uniq{α} (uniq_alt_ty β (ghostptrtoken_ty ty)); #pl ◁ box (&uniq{β} ty)] -[(λ π, (_, π ξ)); (λ π, (vπ π, π η))]
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
    iSplitL "OVo OBor"; [|iSplitL; [|done]]; rewrite (tctx_hasty_val #_);
    iExists _. simpl. iFrame "⧖u". iFrame "LftIn".
    iExists du, _.  
    erewrite uniq_body_irrel. rewrite ghostptrtoken_own_uniq_alt; [|done]. iFrame.
    iPureIntro. split. done. fun_ext=>π. simpl. erewrite pv_irrel. done.
    iFrame "⧖u †p". iNext. rewrite split_mt_uniq_bor. iFrame "βin". 
    iExists _, _, _. rewrite heap_mapsto_vec_singleton. iFrame "↦p RVo BorR". done.
    simpl. iApply proph_obs_impl; [|done] => π/=.
    move: (equal_f EqAlt π) (equal_f Eq1 π) (equal_f Eq2 π) (equal_f Eq3 π)=>/=.
    destruct (lππ π) as [??]. destruct (lππ' π) as [??]. simpl.
    move=> ->->->->/= [-> ToImp] res. 
    rewrite res /alapply 2! list_to_map_fmap reinsert lookup_fmap lookup_insert in ToImp. 
    simpl. destruct ToImp as (v&[= <-]&Imp). apply Imp. rewrite fmap_insert. done.
    apply not_elem_of_list_to_map_1. rewrite elem_of_list_fmap. 
    intros ([??]&->&[[??]%not_elem_of_cons _]%elem_of_list_filter). done.
    erewrite (list_filter_iff _ _ (π ζ')). erewrite <- list_filter_filter.
    erewrite <- (delete_list_to_map p). rewrite insert_delete_insert filter_cons.
    destruct (decide (p ∉ ll)). apply list_to_map_cons. done.  
    intros [??]. simpl. rewrite not_elem_of_cons. intuition.
    - destruct dv; [done|]. iDestruct "†" as "[$|%]"; [|lia]. iSplitL "RPc ↦ty". 
    iExists _, _. iFrame "RPc". iNext. iSplit. 
    iApply (persistent_time_receipt_mono with "⧖u"). lia.
    iApply (ty_own_mt_depth_mono with "↦ty"). lia.
    iExists _, _. iFrame. iSplitR. iNext.
    iApply (persistent_time_receipt_mono with "⧖"). lia. 
    rewrite split_mt_token. iExists _. iFrame. done. 
    - iNext. iIntros "((%vπ'&%d'&>⧖d'&Pc1&↦ty)&(%mπ'&%d''&>⧖d''&Pc2&↦tys)&†)". rewrite split_mt_token.
    iCombine "⧖d' ⧖d''" as "⧖d".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖d")
    as "⧖d"; [solve_ndisj|]. iDestruct "↦tys" as "(%aπl'&>->&$&↦tys&†s)".
    iModIntro. iNext. 
    iExists (λ π, ((p, (vπ' π)) :: (alapply aπl' π))), _. iFrame.
    iSplitL "Pc1 Pc2 ToPc". iApply "ToPc".
    iDestruct (proph_ctrl_eqz' with "PROPH Pc1") as "Eqz1".
    iDestruct (proph_ctrl_eqz' with "PROPH Pc2") as "Eqz2".
    iApply proph_eqz_mono. 2:{
      iApply (proph_eqz_constr2 with "[Eqz1] Eqz2").
      iApply (proph_eqz_constr with "Eqz1").
    } { simpl. intros ? ([|aπ aπl'']&?&->&?&?). specialize (equal_f H2 inhabitant). done.
    inversion_clear H3. destruct H4 as (?&?&->&?). eexists _, _, _, _. split. done. split.
    rewrite H2. done. split. eexists. split; [|done]. fun_ext. 
    intros. simpl. unfold prod_map. f_equal. by injection (equal_f H2 inhabitant).
    eexists _, _. done. }
    iExists ((_, _) :: _). iSplit. iPureIntro. fun_ext=>?//. iFrame. 
    rewrite big_sepL_cons. simpl. iSplitL "↦ty".
    iApply (ty_own_mt_depth_mono with "↦ty"). lia.
    iApply (big_sepL_mono with "↦tys"). iIntros (?[??]?) "↦ty". 
    destruct d''; [done|]. simpl. iNext.
    iApply (ty_own_mt_depth_mono with "↦ty"). lia.
    - done. 
  Qed.

End ghostptrtoken_mut.
