From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr.
From lrust.typing.lib Require Import ghostptrtoken.ghostptrtoken.
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
      (λ post '-[(am, am'); a], forall ptr, am' = <[ptr:=a]>am → post ptr).
  Proof.
    eapply type_fn; [apply _|]=> α ??[m[x[]]]. simpl_subst.
    iIntros (?(mπ & bπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(m & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "m" as ([|dm]) "[_ m]"=>//.
    case m as [[|m|]|]=>//. iDestruct "m" as "[(%ml & >↦m & [#LftIn uniq]) †m]".
    case ml as [|[[|m'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//=.
    iDestruct "x" as "[x' †x]".
     wp_bind (delete _). rewrite freeable_sz_full.
    iApply ((wp_delete [ #m'])with "[↦m †m]"); [done| by iFrame|]. 
    iNext. iIntros.
    iDestruct "x'" as (?) "(↦x&x')".
    case dx as [|dx]=>//=. case vl as [|[[|l|]|][]]=>//=.
    iDestruct "x'" as "(x'&†x')".
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦token) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_token. case du as [|du]=>//=.
    iDestruct "↦token" as (aπm Eq1) "(↦l & ↦tys & †)".
    iCombine "⧖u ⧖x" as "#⧖". simpl.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[↦l ↦tys x' † †x' Pc]") as "[Bor α]".
    (* assert (aπm !! l = None). remember (aπm !! l) as a. rewrite Heqa. case a in Heqa; [|done]. *)
    { iNext. iExists _, _. rewrite split_mt_token. iFrame "⧖ Pc".
      iExists (<[l:=bπ]>aπm). iFrame. iSplit; [done|].
      iSplitL "↦tys x'".
      iNext. rewrite big_opM_insert_delete. iSplitL "x'".
      iDestruct "x'" as (?) "(↦&own)". iExists (vl). iFrame. iApply (ty_own_depth_mono with "own"). lia.
      iApply big_sepM_subseteq. apply delete_subseteq. 
      iApply (big_sepM_impl with "↦tys"). iModIntro. iIntros (???) "H".
      iDestruct "H" as (?) "(H1&H2)". iExists vl. iFrame. iApply (ty_own_depth_mono with "H2"). fold max. lia.
      rewrite big_opM_insert_delete. rewrite freeable_sz_full. iFrame "†x'".
      iApply (big_sepM_subseteq with "†"). apply delete_subseteq. }
    iMod ("ToL" with "α L") as "L".
    set mπ' := λ π, ((mapply (<[l:= bπ]>aπm) π), π ξ).
    iApply (type_type +[#m' ◁ &uniq{α} (ghostptrtoken_ty ty); #x ◁ box ptr] -[mπ'; const l]
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplitL "Vo Bor"; [|iSplitL; [|done]]. rewrite (tctx_hasty_val #m').
      iExists _. iSplit; [done|]. 
      iSplit; [done|]. fold max. iExists _, _. rewrite /uniq_body.
      rewrite (proof_irrel (@prval_to_inh (fmapₛ 𝔄) (fst ∘ mπ')) (@prval_to_inh (fmapₛ 𝔄)  (fst ∘ mπ))).
      assert ((fst ∘ mπ') = mapply (<[l:= bπ]>(aπm))). exact.
      rewrite H1. iFrame. iPureIntro. split; [done|done].
      rewrite (tctx_hasty_val #x). iExists _. iSplit; [done|].
      simpl. iFrame. iNext. iExists _. iFrame. iExists l. exact.
    - iApply proph_obs_impl; [|done]=> π.
      move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (mπ π)=>/= ??->-> Imp Eq.
      apply Imp. rewrite Eq. rewrite -fmap_insert. exact.
  Qed.

  Definition ghostptrtoken_remove {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "ptr"] :=
      delete [ #1; "t"];;
      return: ["ptr"].

  (* Rust's GhostPtrToken::remove *)
  Lemma ghostptrtoken_remove_type {𝔄} (ty: type 𝔄) :
    typed_val (ghostptrtoken_remove ty) (fn<α>(∅; &uniq{α} (ghostptrtoken_ty ty), ptr) → box ty)
      (λ post '-[(am, am'); l], exists(a: 𝔄), (am !! l = Some a) ∧ ((am' = base.delete l am) → post a)).
  Proof.
    eapply type_fn; [apply _|]=> α ??[m[x[]]]. simpl_subst.
    iIntros (?(mπ & pπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(m & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "m" as ([|dm]) "[_ m]"=>//.
    case m as [[|m|]|]=>//. iDestruct "m" as "[(%ml & >↦m & [#LftIn uniq]) †m]".
    case ml as [|[[|m'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//=.
    iDestruct "x" as "[x' †x]".
     wp_bind (delete _). rewrite freeable_sz_full.
    iApply ((wp_delete [ #m'])with "[↦m †m]"); [done| by iFrame|]. 
    iNext. iIntros.
    iDestruct "x'" as (?) "(↦x&x')".
    iDestruct "x'" as (l) "(%pπeq& %vleq)".
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦token) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_token. case du as [|du]=>//=.
    iDestruct "↦token" as (aπm Eq1) "(↦l & ↦token)".
    iCombine "⧖u ⧖x" as "#⧖". simpl.
    iMod (proph_obs_sat with "PROPH Obs") as "%ObsSat"; [done|].
    destruct ObsSat. rewrite (surjective_pairing_fun mπ) in H1.
    rewrite Eq1 in H1. rewrite pπeq in H1. simpl in H1.
    destruct H1 as (?&Contains&?).
    rewrite lookup_fmap_Some in Contains. destruct Contains as (bπ&?&Contains).
    rewrite (big_opM_delete _ aπm l); [|done].
    rewrite (big_opM_delete _ aπm l); [|done].
    iDestruct "↦token" as "((↦x' & ↦) & †x' & †)".
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    assert ((S du `max` dx) = S(du `max` (pred dx))); [by lia|]. rewrite H3 /=.
    iMod ("ToBor" with "[↦l ↦ † Pc]") as "[Bor α]".
    { iNext. iExists _, _. rewrite split_mt_token. iFrame "⧖ Pc".
      iExists _. iFrame. iSplit; [done|].
      iNext. iApply (big_sepM_impl with "↦"). iModIntro. iIntros (???) "H".
      iDestruct "H" as (?) "(H1&H2)". iExists _. iFrame. iApply (ty_own_depth_mono with "H2"). fold max. lia.
    }
    iMod ("ToL" with "α L") as "L".
    set mπ' := λ π, ((mapply (base.delete l aπm) π), π ξ).
    iApply (type_type +[#m' ◁ &uniq{α} (ghostptrtoken_ty ty); #x ◁ box (box ty)] -[mπ'; bπ]
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - iSplitL "Vo Bor"; [|iSplitL; [|done]]. rewrite (tctx_hasty_val #m').
      iExists _. iSplit; [done|]. 
      iSplit; [done|]. fold max. iExists _, _. rewrite /uniq_body.
      rewrite (proof_irrel (@prval_to_inh (fmapₛ 𝔄) (fst ∘ mπ')) (@prval_to_inh (fmapₛ 𝔄)  (fst ∘ mπ))).
      assert ((fst ∘ mπ') = mapply (base.delete l aπm)). exact.
      rewrite H4. iFrame. iPureIntro. split; [done|done].
      rewrite (tctx_hasty_val #x). iExists _. iSplit; [done|]. rewrite vleq.
      simpl. iFrame. iNext. iExists _. 
      iFrame. simpl. rewrite freeable_sz_full. iFrame. 
      iNext. iDestruct "↦x'" as (?) "(a & rest)". iExists vl0. iFrame.
      iApply ty_own_depth_mono; [|done]. lia.
    - iApply proph_obs_impl; [|done]=> π.
      move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (mπ π)=>/= ??->-> Imp Eq.
      destruct Imp as (xv&xeq&Imp).
      rewrite lookup_fmap_Some in xeq. destruct xeq as (xπ&xeq&lookup_eq).
      rewrite (equal_f pπeq)/= in lookup_eq.
      rewrite lookup_eq in Contains. injection Contains as xeqb.
      rewrite -xeqb xeq. apply Imp. rewrite Eq.
      unfold mapply. rewrite fmap_delete. f_equal.
      rewrite (equal_f pπeq). exact.
  Qed.
End ghostptrtoken_insertremove.
