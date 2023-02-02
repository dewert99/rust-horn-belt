From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr.
From lrust.typing.lib Require Import ghostptrtoken.ghostptrtoken.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_insertremove.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_merge {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "t2"] :=
      delete [ #1; "t"];;
      return: ["t2"].

  (* Rust's GhostPtrToken::merge *)
  Lemma ghostptrtoken_merge_type {𝔄} (ty: type 𝔄) :
    typed_val (ghostptrtoken_merge ty) (fn<α>(∅; &uniq{α} (ghostptrtoken_ty ty), ghostptrtoken_ty ty) → ())
      (λ post '-[(al, al'); al2], al' = al2 ++ al → post ()).
  Proof.
    eapply type_fn; [apply _|]=> α ??[l[l2[]]]. simpl_subst.
    iIntros (?(lπ & l2π &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(l & l2 &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "l" as ([|dl]) "[⧖1 l]"=>//.
    case l as [[|l|]|]=>//. iDestruct "l" as "[(%ll & >↦l & [#LftIn uniq]) †l]".
    case ll as [|[[|l'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "l2" as ([|dl2]) "[⧖2 l2]"=>//. case l2 as [[|l2|]|]=>//=.
    iDestruct "l2" as "[l2' †l2]".
    wp_bind (delete _). rewrite freeable_sz_full.
    iApply ((wp_delete [ #l']) with "[↦l †l]"); [done| by iFrame|]. 
    iNext. iIntros.
    iDestruct "l2'" as (vl2) "(↦l2&l2')".
    case dl2 as [|dl2]=>//=. iDestruct "l2'" as "(%aπl2&(->&->)&(↦2&†2))". 
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦token) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_token. case du as [|du]=>//=.
    iDestruct "↦token" as (aπl Eq1) "(↦l & ↦tys & †)".
    iDestruct (persistent_time_receipt_mono (S (S du)) with "⧖1") as "⧖1". lia.
    iCombine "⧖1 ⧖2" as "#⧖". simpl.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    unfold big_sepAL.
    iMod ("ToBor" with "[↦l ↦tys ↦2 † †2 Pc]") as "[Bor α]".
    { iNext. iExists _, _. rewrite split_mt_token. iFrame "⧖ Pc". simpl.
      iExists (aπl2++aπl). iFrame. iSplit; [done|].
      iNext. rewrite big_sepL_app. iSplitL "↦2";
      iApply (big_sepL_impl with "[$]"); iModIntro; iIntros (?[??]?) "H";
      iApply (ty_own_mt_depth_mono with "H"); lia. }
    iMod ("ToL" with "α L") as "L".
    set lπ' := λ π, ((alapply (aπl2++aπl) π), π ξ).
    iApply (type_type +[#l' ◁ &uniq{α} (ghostptrtoken_ty ty); #l2 ◁ box ()] -[lπ'; const ()]
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplitL "Vo Bor"; [|iSplitL; [|done]]. rewrite (tctx_hasty_val #l').
      iExists _. iSplit; [done|]. 
      iSplit; [done|]. fold max. iExists _, _. rewrite /uniq_body.
      rewrite (proof_irrel (@prval_to_inh (listₛ (locₛ * 𝔄)) (fst ∘ lπ')) (@prval_to_inh (listₛ (locₛ * 𝔄))  (fst ∘ lπ))).
      iFrame. exact.
      rewrite (tctx_hasty_val #l2). iExists _. iSplit; [done|].
      simpl. iFrame. iNext. iExists _. iFrame. iExists (const -[]). done.
    - iApply proph_obs_impl; [|done]=> π.
      move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (lπ π)=>/= ??->-> Imp Eq.
      apply Imp. rewrite Eq. rewrite /alapply fmap_app. reflexivity.
  Qed.
End ghostptrtoken_insertremove.
