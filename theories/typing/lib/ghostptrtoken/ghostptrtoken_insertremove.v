From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr.
From lrust.typing.lib Require Import ghostptrtoken.ghostptrtoken ghostptrtoken.heap_util.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_insertremove.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_insert {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "b"] :=
      delete [ #1; "t"];;
      return: ["b"].

  (* Rust's GhostPtrToken::insert *)
  Lemma ghostptrtoken_insert_type {𝔄} (ty: type 𝔄) :
    typed_val (ghostptrtoken_insert ty) (fn<α>(∅; &uniq{α} (ghostptrtoken_ty ty), box ty) → ptr)
      (λ post '-[(al, al'); a], forall ptr, al' = (ptr,a)::al → ((ty.(ty_size) > 0) → NoDup al'.*1) → post ptr).
  Proof.
    eapply type_fn; [apply _|]=> α ??[l[x[]]]. simpl_subst.
    iIntros (?(lπ & bπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(l & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "l" as ([|dl]) "[_ l]"=>//.
    case l as [[|l|]|]=>//. iDestruct "l" as "[(%ll & >↦l & [#LftIn uniq]) †l]".
    case ll as [|[[|l'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//=.
    iDestruct "x" as "[x' †x]".
     wp_bind (delete _). rewrite freeable_sz_full.
    iApply ((wp_delete [ #l'])with "[↦l †l]"); [done| by iFrame|]. 
    iNext. iIntros.
    iDestruct "x'" as (?) "(↦x&x')".
    case dx as [|dx]=>//=. case vl as [|[[|p|]|][]]=>//=.
    iDestruct "x'" as "(x'&†x')".
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦token) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_token. case du as [|du]=>//=.
    iDestruct "↦token" as (aπl Eq1) "(↦l & ↦tys & †)".
    iCombine "⧖u ⧖x" as "#⧖". simpl.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iAssert ((l' ↦∗: (ghostptrtoken_ty ty).(ty_own) _ (S (du `max` dx)) tid))%I with "[↦l ↦tys x' † †x']" as "own".
    iExists _. iFrame. iExists ((p, bπ)::aπl). iSplit; [done|].
    rewrite freeable_sz_full. iFrame. iNext.
    unfold big_sepAL. rewrite big_sepL_cons. iSplitL "x'".
    iDestruct "x'" as (?) "(↦&own)". iExists (vl). iFrame. iApply (ty_own_depth_mono with "own"). lia.
    iApply (big_sepL_impl with "↦tys"). iModIntro. iIntros (?[??]?) "H".
    iDestruct "H" as (?) "(H1&H2)". iExists vl. iFrame. iApply (ty_own_depth_mono with "H2"). lia.
    iDestruct ((plain_entails_r (ghost_ptr_token_no_dup _ _ _ _ _)) with "own") as "(own&>%no_dup)".
    iMod ("ToBor" with "[own Pc]") as "[Bor α]".
    iDestruct (bi.later_intro with "own") as "own". 
    iNext. iExists _, _. iFrame "⧖ Pc own".
    iMod ("ToL" with "α L") as "L".
    set lπ' := λ π, ((alapply ((p, bπ)::aπl) π), π ξ).
    iApply (type_type +[#l' ◁ &uniq{α} (ghostptrtoken_ty ty); #x ◁ box ptr] -[lπ'; const p]
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplitL "Vo Bor"; [|iSplitL; [|done]]. rewrite (tctx_hasty_val #l').
      iExists _. iSplit; [done|]. 
      iSplit; [done|]. fold max. iExists _, _. rewrite /uniq_body.
      rewrite (proof_irrel (@prval_to_inh (listₛ (locₛ * 𝔄)) (fst ∘ lπ')) (@prval_to_inh (listₛ (locₛ * 𝔄))  (fst ∘ lπ))).
      iFrame. exact.
      rewrite (tctx_hasty_val #x). iExists _. iSplit; [done|].
      simpl. iFrame. iNext. iExists _. iFrame. iExists p. done.
    - iApply proph_obs_impl; [|done]=> π.
      move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (lπ π)=>/= ??->-> Imp Eq.
      apply Imp. rewrite Eq. reflexivity.
      intros. rewrite Eq. apply no_dup. done.
  Qed.

  Definition ghostptrtoken_remove {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "ptr"] :=
      delete [ #1; "t"];;
      return: ["ptr"].

  (* Rust's GhostPtrToken::re,ove *)
  Lemma ghostptrtoken_remove_type {𝔄} (ty: type 𝔄) :
    typed_val (ghostptrtoken_remove ty) (fn<α>(∅; &uniq{α} (ghostptrtoken_ty ty), ptr) → box ty)
      (λ post '-[(al, al'); p], exists(a: 𝔄), ((list_to_gmap al) !! p = Some a) ∧ ((<[p:=a]>(list_to_gmap al') = (list_to_gmap al)) → ((ty.(ty_size) > 0) → NoDup al.*1) → post a)).
  Proof.
    eapply type_fn; [apply _|]=> α ??[l[x[]]]. simpl_subst.
    iIntros (?(lπ & pπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(l & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "l" as ([|dl]) "[_ l]"=>//.
    case l as [[|l|]|]=>//. iDestruct "l" as "[(%ll & >↦l & [#LftIn uniq]) †l]".
    case ll as [|[[|l'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//=.
    iDestruct "x" as "[x' †x]".
     wp_bind (delete _). rewrite freeable_sz_full.
    iApply ((wp_delete [ #l'])with "[↦l †l]"); [done| by iFrame|]. 
    iNext. iIntros.
    iDestruct "x'" as (?) "(↦x&x')".
    iDestruct "x'" as (p) "(%pπeq& %vleq)".
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦token) ToBor]"; [done|].
    wp_seq. 
    iDestruct ((plain_entails_r (ghost_ptr_token_no_dup _ _ _ _ _)) with "↦token") as "(↦token&>%no_dup)".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_token. case du as [|du]=>//=.
    iDestruct "↦token" as (aπl Eq1) "(↦l & ↦token)".
    iCombine "⧖u ⧖x" as "#⧖". simpl.
    iMod (proph_obs_sat with "PROPH Obs") as "%ObsSat"; [done|].
    remember ((list_to_gmap aπl) !! p) as bπ. symmetry in Heqbπ. destruct bπ as [bπ|]; last first.
    destruct ObsSat. rewrite (surjective_pairing_fun lπ) in H1.
    rewrite Eq1 in H1. rewrite pπeq in H1. simpl in H1. 
    destruct H1 as (?&Contains&?).
    rewrite /alapply list_to_map_fmap lookup_fmap Heqbπ in Contains. done.
    destruct (elem_of_list_to_map_2' _ _ _ Heqbπ) as (rπ&perm&reinsert).
    unfold big_sepAL.
    iEval (rewrite perm 2! big_sepL_cons) in "↦token".
    iDestruct "↦token" as "((↦x' & ↦) & †x' & †)".
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    assert ((S du `max` dx) = S(du `max` (pred dx))); [by lia|]. rewrite H1 /=.
    iMod ("ToBor" with "[↦l ↦ † Pc]") as "[Bor α]".
    { iNext. iExists _, _. rewrite split_mt_token. iFrame "⧖ Pc".
      iExists _. iFrame. iSplit; [done|].
      iNext. iApply (big_sepL_impl with "↦"). iModIntro. iIntros (?[??]?) "H".
      iDestruct "H" as (?) "(H1&H2)". iExists _. iFrame. iApply (ty_own_depth_mono with "H2"). fold max. lia.
    }
    iMod ("ToL" with "α L") as "L".
    set lπ' := λ π, ((alapply rπ π), π ξ).
    iApply (type_type +[#l' ◁ &uniq{α} (ghostptrtoken_ty ty); #x ◁ box (box ty)] -[lπ'; bπ]
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplitL "Vo Bor"; [|iSplitL; [|done]]. rewrite (tctx_hasty_val #l').
      iExists _. iSplit; [done|]. 
      iSplit; [done|]. fold max. iExists _, _. rewrite /uniq_body.
      rewrite (proof_irrel (@prval_to_inh (listₛ (locₛ * 𝔄)) (fst ∘ lπ')) (@prval_to_inh (listₛ (locₛ * 𝔄)) (fst ∘ lπ))).
      replace (fst ∘ lπ') with (alapply rπ); [|done].
      iFrame. iPureIntro. split; [done|done].
      rewrite (tctx_hasty_val #x). iExists _. iSplit; [done|]. rewrite vleq.
      simpl. iFrame. iNext. iExists _. 
      iFrame. simpl. rewrite freeable_sz_full. iFrame. 
      iNext. iDestruct "↦x'" as (?) "(a & rest)". iExists vl0. iFrame.
      iApply ty_own_depth_mono; [|done]. lia.
    - iApply proph_obs_impl; [|done]=> π.
      move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (lπ π)=>/= ??->-> Imp Eq.
      destruct Imp as (xv&xeq&Imp).
      rewrite /alapply list_to_map_fmap lookup_fmap_Some in xeq. destruct xeq as (xπ&<-&lookup_eq).
      rewrite (equal_f pπeq)/= in lookup_eq.
      rewrite lookup_eq in Heqbπ. injection Heqbπ as ->.
      apply Imp. rewrite Eq.
      rewrite /alapply 2! list_to_map_fmap -fmap_insert. f_equal.
      rewrite (equal_f pπeq). exact. 
      intros. rewrite -Eq1. apply no_dup. done.
  Qed.
    
End ghostptrtoken_insertremove.
