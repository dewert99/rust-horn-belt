From iris.proofmode Require Import tactics.
From lrust.lang Require Import memcpy.
From lrust.typing Require Import uninit uniq_bor shr_bor own sum.
From lrust.typing Require Import lft_contexts type_context programs product.
From lrust.typing Require Import base_type.

Set Default Proof Using "Type".

Section case.
  Context `{!typeG Σ}.
  (* TODO FIX THIS *)
  Local Instance base_empty `{!typeG Σ} : Empty (type ∅) := base.

  Lemma type_case_own' {Ts 𝔅 As} E L (C : cctx 𝔅) (T : tctx Ts) p n (tyl : typel _) el el' (prel : hlist (λ _, _) _) :
    list_to_hlist el = Some el' →
    IxHForall3 (λ i ty e (prei : predl_trans' (Σ!%ST As :: Ts) 𝔅),
      (⊢ typed_body E L C ((p +ₗ #0 ◁ own_ptr n (uninit 1)) +:: (p +ₗ #1 ◁ own_ptr n ty) +::
         (p +ₗ #(S (ty.(ty_size))) ◁
            own_ptr n (uninit (max_ty_size tyl - ty_size ty))) +:: T) e
            (λ post '(_ -:: v -:: _ -:: w), prei post (pinj (D := Empty_setₛ) i v -:: w))) ∨
      (⊢ typed_body E L C ((p ◁ own_ptr n (xsum_ty tyl)) +:: T) e prei))
      tyl el' prel →
    ⊢ typed_body E L C ((p ◁ own_ptr n (xsum_ty tyl)) +:: T) (case: !p of el)
      (λ post '(v -:: w), (∀ i, hnth (D := empty) (λ _ _, False) prel i post (v -:: w)) : Prop).
  Proof.
    iIntros (elEl Hel tid [vπ vπl] postπ) "#LFT #TIME #PROPH #UNIQ #HE Hna HL HC /= [Hp HT] Hproph". wp_bind p.
    iApply (wp_hasty with "Hp").
    iIntros ([[]|] [|depth1]) "%Hv #Hdepth Hp /= //".
    iDestruct "Hp" as "[H↦ Hf]". iDestruct "H↦" as (vl) "[H↦ Hown]".
    iMod (bi.later_exist_except_0 with "Hown") as (i) "Hown".
    iMod (bi.later_exist_except_0 with "Hown") as (wπ vl' vl'') "(>(% & % & EQlen) & Hown)". subst.
    iDestruct "EQlen" as %[=EQlen]. rewrite -EQlen.
    rewrite -(Nat.add_1_l (length _)) app_length -!freeable_sz_split /=
            heap_mapsto_vec_cons heap_mapsto_vec_app.
    iDestruct "H↦" as "(H↦i & H↦vl' & H↦vl'')". iDestruct "Hf" as "(Hfi & Hfvl' & Hfvl'')".
    iAssert (⌜ i < length As ⌝)%I with "[Hown]" as "%".
    { case (decide (i < length As)) => [//| ?].
      rewrite hnth_default; [ apply lnth_default; lia | | lia].
      move => eq. destruct eq; by pose proof (wπ inhabitant). }
    eapply (IxHForall3_nth _ ∅ _ _ _ _ _ i) in Hel as Hety.
    wp_read. wp_case.
    { split; [lia|]. destruct (list_to_hlist_length el el'); [done|].
      edestruct (nth_lookup_or_length el i ltac:(done)); [|lia].
      rewrite Nat2Z.id e -(list_to_hlist_hnth_nth ∅ _ _ _ _ elEl) //. }
    destruct Hety as [Hety|Hety].
    - iApply (Hety $! tid (const () -:: _ -:: const () -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
      rewrite /= !tctx_hasty_val' /= -?Hv //=; iFrame "HT".
      + rewrite /own_ptr /=.
        iDestruct (_.(ty_size_eq) with "Hown") as "%X"; rewrite -X; clear X.
        iSplitL "H↦i Hfi"; last iSplitR "H↦vl'' Hfvl''"; iExists _; iFrame "#"; simpl.
        * rewrite shift_loc_0. iFrame. iExists [ #i]. rewrite heap_mapsto_vec_singleton.
          auto with iFrame.
        * eauto with iFrame.
        * rewrite -EQlen app_length minus_plus shift_loc_assoc_nat. eauto with iFrame.
      + iApply (proph_obs_impl with "Hproph") => π /= ? //.
    - iApply (Hety $! tid (_ -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
      rewrite /= !tctx_hasty_val' /= -?Hv //=; iFrame "HT".
      + iExists _. iFrame "#". rewrite /= -EQlen app_length -(Nat.add_1_l (_+_)) -!freeable_sz_split. iFrame.
        iExists (#i :: vl' ++ vl''). iNext. rewrite heap_mapsto_vec_cons heap_mapsto_vec_app.
        iFrame. iExists i,_, vl', vl''. rewrite /= app_length /=. auto.
      + iApply (proph_obs_impl with "Hproph") => π /= ? //.
  Qed.

  (* Lemma type_case_own E L C T T' p n tyl el :
    tctx_extract_hasty E L p (own_ptr n (sum tyl)) T T' →
    Forall2 (λ ty e,
      (⊢ typed_body E L C ((p +ₗ #0 ◁ own_ptr n (uninit 1)) :: (p +ₗ #1 ◁ own_ptr n ty) ::
         (p +ₗ #(S (ty.(ty_size))) ◁
            own_ptr n (uninit (max_list_with ty_size tyl - ty_size ty))) :: T') e) ∨
      (⊢ typed_body E L C ((p ◁ own_ptr n (sum tyl)) :: T') e))
      tyl el →
    ⊢ typed_body E L C T (case: !p of el).
  Proof. unfold tctx_extract_hasty=>->. apply type_case_own'. Qed.
  *)

  Lemma type_case_uniq' {As 𝔅 Xl} E L (C : cctx 𝔅) (T : tctx Xl) p κ tyl el el' (prel : hlist (λ _, _) _) :
    list_to_hlist el = Some el' → lctx_lft_alive E L κ →
    IxHForall3 (D := Empty_setₛ) (λ i ty e (prei : predl_trans' ((Σ! As * Σ! As)%ST :: Xl) 𝔅),
      (⊢ typed_body E L C ((p +ₗ #1 ◁ &uniq{κ}ty) +:: T) e (λ post '((v, v') -:: w), prei post ((pinj i v : Σ!%ST As, pinj i v' : Σ!%ST As) -:: w))) ∨
      (⊢ typed_body E L C ((p ◁ &uniq{κ}(xsum_ty tyl)) +:: T) e prei)) tyl el' prel →
    ⊢ typed_body E L C ((p ◁ &uniq{κ}(xsum_ty tyl)) +:: T) (case: !p of el)
      (λ post '(v -:: w), (∀ i, hnth (D := Empty_setₛ) (λ _ _, False) prel i post (v -:: w)) : Prop).
  Proof.
    iIntros (el2el' Halive Hel tid [vπ vπl] postπ) "#LFT #TIME #PROPH #UNIQ #HE Hna HL HC /= [Hp HT] Hproph". wp_bind p.
    iApply (wp_hasty with "Hp").
    iIntros ([[]|] [|depth1]) "%Hv #Hdepth /= [#? Hp] //".
    { iDestruct "Hp" as (??) "(% & ?)". lia. }
    iDestruct "Hp" as (depth2 ξid) "([% %B] & ξvo & Hp)"; set ξ := PrVar _ ξid.
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]"; [done|].
    iMod (bor_acc_cons with "LFT Hp Htok") as "[H Hclose']"; [done|].
    iMod (bi.later_exist_except_0 with "H") as (vπ' depth2') "(H↦ & #Hdepth2' & ξpc)".
    iDestruct "H↦" as (vl) "[> H↦ Hown]".
    iMod (bi.later_exist_except_0 with "Hown") as (i) "Hown".
    iMod (bi.later_exist_except_0 with "Hown") as (wπ vl' vl'') "(>(-> & -> & EQlen) & Hown)".
    iMod (uniq_strip_later with "ξvo ξpc") as "(%A & <- & ξvo & ξpc)".
    iDestruct "EQlen" as %[=EQlen].
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_app.
    iDestruct "H↦" as "(H↦i & H↦vl' & H↦vl'')".
    iAssert (⌜ i < length As ⌝)%I with "[Hown]" as "%".
    { clear -wπ. case (decide (i < length As)) => [//| ?].
      rewrite hnth_default; [ apply lnth_default; lia | | lia].
      move => eq. destruct eq; by pose proof (wπ inhabitant). }
    eapply (IxHForall3_nth _ _ _ _ _ _ _ i) in Hel as Hety.
    wp_read. wp_case.
    { split; [lia|]. destruct (list_to_hlist_length el el'); [done|].
      edestruct (nth_lookup_or_length el i ltac:(done)); [|lia].
      rewrite Nat2Z.id e -(list_to_hlist_hnth_nth ∅ _ _ _ _ el2el') //. }
    iDestruct (_.(ty_size_eq) with "Hown") as %EQlenvl'.
    destruct Hety as [Hety|Hety].
    - iMod (uniq_intro wπ depth2 with "PROPH UNIQ") as (ζid) "[ζvo ζpc]"; [done|]; set ζ := PrVar _ ζid.
      iDestruct (uniq_proph_tok with "ζvo ζpc") as "(ζvo & ζ & Toζpc)"; rewrite proph_tok_singleton.
      iMod (uniq_preresolve ξ _ (λ π, pinj i (π ζ)) with "PROPH ξvo ξpc ζ") as "(#Hproph' & ζ & ξeqz)"; first done.
      { apply proph_dep_constr, proph_dep_one. }
      iDestruct ("Toζpc" with "ζ") as "ζpc".
      iMod ("Hclose'" $! (∃ vπ' d', (l +ₗ 1) ↦∗: (hnthe tyl i).(ty_own) vπ' d' tid ∗ ⧖(S d') ∗ .PC[ζ] vπ' d')%I
        with "[ξeqz H↦i H↦vl''] [ ζpc H↦vl' Hown]") as "[Hb Htok]".
      { iIntros "!>Hown". iMod (bi.later_exist_except_0 with "Hown") as (??) "(Hown & #>Hdepth2'' & ζpc)".
        iDestruct "Hown" as (vl'2) "[H↦ Hown]". iExists _, _. iModIntro; iNext.
        iDestruct (proph_ctrl_eqz with "PROPH ζpc") as "ζeqz".
        iDestruct (proph_eqz_constr (pinj i) with "ζeqz") as "ζeqz".
        iDestruct ("ξeqz" with "ζeqz") as "ξpc".
        iFrame "# ξpc". iExists (#i::vl'2++vl'').
        iDestruct (_.(ty_size_eq) with "Hown") as %EQlenvl'2.
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app EQlenvl' EQlenvl'2.
        iFrame. iExists _, _, _, _. iFrame.
        rewrite /= -EQlen !app_length EQlenvl' EQlenvl'2 //. }
      { iNext. iExists _, _. iFrame "#∗". iExists _. iFrame. }
      iMod ("Hclose" with "Htok") as "HL".
      iApply (Hety $! _ ((λ π, (wπ π, π ζ)) -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
      + iFrame. rewrite tctx_hasty_val' /= -?Hv //.
        iExists (S depth1). iFrame "#". iSplitR.
        { iApply lft_incl_trans; [done|]. iApply ty_lfts_nth_incl. }
        rewrite (proof_irrel (_ wπ) (prval_to_inh' (λ π, (wπ π, π ζ)))).
        iExists _, ζid. by iFrame.
      + iCombine "Hproph' Hproph" as "Hproph".
        iApply (proph_obs_impl with "Hproph") => π /= [<- >].
        move: (equal_f A π) (equal_f B π).
        rewrite {4}(_ : vπ = λ π, (fst (vπ π), snd (vπ π))); last first.
        { fun_ext => π'. by destruct (vπ π'). }
        move => /= ->-> /= x //.
    - iMod ("Hclose'" with "[] [H↦i H↦vl' H↦vl'' Hown ξpc]") as "[Hb Htok]";
        [by iIntros "!>$"| |].
      { iExists _, depth2. iFrame "∗#". iExists (#i::vl'++vl'').
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app /= -EQlen.
        iFrame. iNext. iExists i, _, vl', vl''. by iFrame. }
      iMod ("Hclose" with "Htok") as "HL".
      iApply (Hety $! _ (_ -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
      + iFrame. rewrite tctx_hasty_val' ?Hv //. iExists (S depth1).
        iFrame "#". iExists _, _. auto with iFrame.
      + iApply (proph_obs_impl with "Hproph") => π /= ?; auto.
  Qed.

  (* Lemma type_case_uniq E L C T T' p κ tyl el :
    tctx_extract_hasty E L p (&uniq{κ}(sum tyl)) T T' →
    lctx_lft_alive E L κ →
    Forall2 (λ ty e,
      (⊢ typed_body E L C ((p +ₗ #1 ◁ &uniq{κ}ty) :: T') e) ∨
      (⊢ typed_body E L C ((p ◁ &uniq{κ}(sum tyl)) :: T') e)) tyl el →
    ⊢ typed_body E L C T (case: !p of el).
  Proof. unfold tctx_extract_hasty=>->. apply type_case_uniq'. Qed. *)
   (* Lemma hnth_default {A D As} {F : A → _} (d : F D) (l : hlist F As) i : *)

  Lemma type_case_shr' {Xl As 𝔅} E L (C : cctx 𝔅) (T : tctx Xl) p κ tyl el el' (prel : hlist (λ _, _) As) :
    list_to_hlist el = Some el' → lctx_lft_alive E L κ →
    IxHForall3 (λ i ty e (prei : predl_trans' (Σ!%ST As :: Xl) 𝔅),
      (⊢ typed_body E L C ((p +ₗ #1 ◁ &shr{κ}ty) +:: T) e (λ post '(vi -:: w), prei post (pinj (D := Empty_setₛ) i vi -:: w))) ∨
      (⊢ typed_body E L C ((p ◁ &shr{κ}(xsum_ty tyl)) +:: T) e prei)
    ) tyl el' prel →
    ⊢ typed_body E L C ((p ◁ &shr{κ}(xsum_ty tyl)) +:: T) (case: !p of el)
      (λ post '(v -:: w), (∀ i, hnth (D := Empty_setₛ) (λ _ _, False) prel i post (v -:: w)) : Prop).
  Proof.
    iIntros (el2el' Halive Hel tid [? ?] postπ) "#LFT #TIME #PROPH UNIQ #HE Hna HL HC /= [Hp HT] Hproph". wp_bind p.
    iApply (wp_hasty with "Hp").
    iIntros ([[]|] [|depth]) "% Hdepth Hp //".
    iDestruct "Hp" as (i vπ) "(% & #Hb & Hshr)".
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]". done.
    iMod (frac_bor_acc with "LFT Hb Htok") as (q') "[[H↦i H↦vl''] Hclose']". done.
    iAssert (⌜ i < length As ⌝)%I with "[Hshr]" as "%".
    { clear -vπ. case (decide (i < length As)) => [//| ?].
      rewrite hnth_default; [ apply lnth_default; lia | | lia].
      move => eq; destruct eq; by pose proof (vπ inhabitant). }
    eapply (IxHForall3_nth _ _ _ _ _ _ _ i) in Hel as Hety.
    wp_read. wp_case.
    { split; [lia|]. destruct (list_to_hlist_length el el'); [done|].
      edestruct (nth_lookup_or_length el i ltac:(done)); [|lia].
      rewrite Nat2Z.id e -(list_to_hlist_hnth_nth ∅ _ _ _ _ el2el') //. }
    iMod ("Hclose'" with "[$H↦i $H↦vl'']") as "Htok".
    iMod ("Hclose" with "Htok") as "HL".
    destruct Hety as [Hety|Hety]; iApply (Hety $! _ (_ -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
    - rewrite /= tctx_hasty_val' /= -?H //. iFrame.
      iExists _. by iFrame.
    - iApply (proph_obs_impl with "Hproph") => /= ??; subst; eauto.
    - rewrite /= tctx_hasty_val' /= -?H //. iFrame.
      iExists _. iFrame. iExists _, _. by iFrame "%∗".
    - iApply (proph_obs_impl with "Hproph") => /= ??; subst; eauto.
  Qed.

(*
  Lemma type_case_shr E L C T p κ tyl el prel:
    p ◁ &shr{κ}(sum tyl) ∈ T →
    lctx_lft_alive E L κ →
    Forall3 (λ ty e, ⊢ typed_body E L C ((p +ₗ #1 ◁ &shr{κ}ty) :: T) e) tyl el prel →
    ⊢ typed_body E L C T (case: !p of el).
  Proof.
    intros. rewrite ->copy_elem_of_tctx_incl; last done; last apply _.
    apply type_case_shr'; first done. eapply Forall2_impl; first done. auto.
  Qed.

  Lemma type_sum_assign_instr {E L} (i : nat) ty1 tyl ty ty2 p1 p2 :
    tyl !! i = Some ty →
    (⊢ typed_write E L ty1 (sum tyl) ty2) →
    ⊢ typed_instr E L [p1 ◁ ty1; p2 ◁ ty] (p1 <-{Σ i} p2) (λ _, [p1 ◁ ty2]).
  Proof.
    iIntros (Hty Hw tid) "#LFT #TIME #HE $ HL Hp".
    rewrite tctx_interp_cons tctx_interp_singleton.
    iDestruct "Hp" as "[Hp1 Hp2]". iDestruct (closed_hasty with "Hp1") as "%".
    iDestruct (closed_hasty with "Hp2") as "%".
    wp_apply (wp_hasty with "Hp1"). iIntros (depth1 v1) "Hdepth1". iIntros (Hv1) "Hty1".
    iDestruct "Hp2" as (v2 depth2) "(Hdepth2 & H)". iDestruct "H" as (Hv2) "Hty2".
    iCombine "Hdepth1 Hdepth2" as "Hdepth". rewrite -persist_time_rcpt_sep.
    rewrite !(ty_own_depth_mono _ _ (depth1 `max` depth2)); [|lia..].
    rewrite typed_write_eq in Hw.
    iMod (Hw with "[] LFT HE HL Hty1") as (l vl) "(H & H↦ & Hw)"=>//=.
    destruct vl as [|? vl]; iDestruct "H" as %[[= Hlen] ->].
    rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[H↦0 H↦vl]".
    wp_write. wp_bind p1. iApply (wp_wand with "[]"); first by iApply (wp_eval_path).
    iIntros (? ->). wp_op. wp_bind p2.
    iApply (wp_wand with "[]"); first by iApply (wp_eval_path). iIntros (? ->).
    iDestruct (ty_size_eq with "Hty2") as %Hlenty. destruct vl as [|? vl].
    { exfalso. revert i Hty. clear - Hlen Hlenty. induction tyl=>//= -[|i] /=.
      - intros [= ->]. simpl in *. lia.
      - apply IHtyl. simpl in *. lia. }
    rewrite heap_mapsto_vec_cons -wp_fupd.
    iApply (wp_persist_time_rcpt with "TIME Hdepth")=>//.
    iDestruct "H↦vl" as "[H↦ H↦vl]". wp_write. iIntros "#Hdepth".
    rewrite tctx_interp_singleton tctx_hasty_val' //.
    rewrite -(bi.exist_intro (S _)). iFrame "Hdepth". iApply ("Hw" with "[-] [//]").
    iNext. iExists (_::_::_). rewrite !heap_mapsto_vec_cons. iFrame.
    iExists i, [_], _. rewrite -Hlen nth_lookup Hty. auto.
  Qed.

  Lemma type_sum_assign {E L} sty tyl i ty1 ty ty1' C T T' p1 p2 e:
    Closed [] e →
    0 ≤ i →
    sty = sum tyl →
    tctx_extract E L [p1 ◁ ty1; p2 ◁ ty] T T' →
    tyl !! (Z.to_nat i) = Some ty →
    (⊢ typed_write E L ty1 sty ty1') →
    typed_body E L C ((p1 ◁ ty1') :: T') e -∗
    typed_body E L C T (p1 <-{Σ i} p2 ;; e).
  Proof.
    iIntros (??->) "* **". rewrite -(Z2Nat.id i) //.
    iApply type_seq; [by eapply type_sum_assign_instr|done|done].
  Qed.

  Lemma type_sum_unit_instr {E L} (i : nat) tyl ty1 ty2 p :
    tyl !! i = Some unit →
    (⊢ typed_write E L ty1 (sum tyl) ty2) →
    ⊢ typed_instr E L [p ◁ ty1] (p <-{Σ i} ()) (λ _, [p ◁ ty2]).
  Proof.
    iIntros (Hty Hw tid) "#LFT #TIME #HE $ HL Hp". rewrite tctx_interp_singleton.
    wp_apply (wp_hasty with "Hp"). iIntros (depth v) "Hdepth". iIntros (Hv) "Hty".
    rewrite typed_write_eq in Hw.
    iMod (Hw with "[] LFT HE HL Hty") as (l vl) "(H & H↦ & Hw)"; first done.
    simpl. destruct vl as [|? vl]; iDestruct "H" as %[[= Hlen] ->].
    rewrite heap_mapsto_vec_cons -wp_fupd. iDestruct "H↦" as "[H↦0 H↦vl]".
    iApply (wp_persist_time_rcpt with "TIME Hdepth")=>//.
    wp_write. iIntros "#Hdepth". rewrite tctx_interp_singleton tctx_hasty_val' //.
    rewrite -(bi.exist_intro (S _)). iFrame "Hdepth".
    iApply ("Hw" with "[-] Hdepth"). iModIntro. iExists (_::_).
    rewrite heap_mapsto_vec_cons. iFrame.
    iExists i, [], _. rewrite -Hlen nth_lookup Hty. auto.
  Qed.

  Lemma type_sum_unit {E L} sty tyl i ty1 ty1' C T T' p e:
    Closed [] e →
    0 ≤ i →
    sty = sum tyl →
    tctx_extract_hasty E L p ty1 T T' →
    tyl !! (Z.to_nat i) = Some unit →
    (⊢ typed_write E L ty1 sty ty1') →
    typed_body E L C ((p ◁ ty1') :: T') e -∗
    typed_body E L C T (p <-{Σ i} () ;; e).
  Proof.
    iIntros (??->) "* **". rewrite -(Z2Nat.id i) //.
    iApply type_seq; [by eapply type_sum_unit_instr|solve_typing|done].
  Qed.

  Lemma type_sum_memcpy_instr {E L} (i : nat) tyl ty1 ty1' ty2 ty2' ty p1 p2 :
    tyl !! i = Some ty →
    (⊢ typed_write E L ty1 (sum tyl) ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    ⊢ typed_instr E L [p1 ◁ ty1; p2 ◁ ty2]
               (p1 <-{ty.(ty_size),Σ i} !p2) (λ _, [p1 ◁ ty1'; p2 ◁ ty2']).
  Proof.
    iIntros (Hty Hw Hr tid) "#LFT #TIME #HE Htl [HL1 HL2] Hp".
    rewrite tctx_interp_cons tctx_interp_singleton.
    iDestruct "Hp" as "[Hp1 Hp2]". iDestruct (closed_hasty with "Hp1") as "%".
    iDestruct (closed_hasty with "Hp2") as "%". wp_apply (wp_hasty with "Hp1").
    iIntros (depth1 v1) "Hdepth1". iIntros (Hv1) "Hty1".
    iDestruct "Hp2" as (v2 depth2) "(Hdepth2 & H)". iDestruct "H" as (Hv2) "Hty2".
    iCombine "Hdepth1 Hdepth2" as "Hdepth". rewrite -persist_time_rcpt_sep.
    rewrite !(ty_own_depth_mono _ _ (depth1 `max` depth2)); [|lia..].
    rewrite typed_write_eq in Hw.
    iMod (Hw with "[] LFT HE HL1 Hty1") as (l1 vl1) "(H & H↦ & Hw)"=>//=.
    clear Hw. destruct vl1 as [|? vl1]; iDestruct "H" as %[[= Hlen] ->].
    rewrite heap_mapsto_vec_cons -wp_fupd. iDestruct "H↦" as "[H↦0 H↦vl1]". wp_write.
    wp_bind p1. iApply (wp_wand with "[]"); first by iApply (wp_eval_path). iIntros (? ->).
    wp_op. wp_bind p2. iApply (wp_wand with "[]"); first by iApply (wp_eval_path). iIntros (? ->).
    rewrite typed_read_eq in Hr.
    iMod (Hr with "[] LFT HE Htl HL2 Hty2") as (l2 vl2 q) "(% & H↦2 & Hty & Hr)"=>//=.
    clear Hr. subst. assert (ty.(ty_size) ≤ length vl1).
    { revert i Hty. rewrite Hlen. clear. induction tyl=>//= -[|i] /=.
      - intros [= ->]. lia.
      - specialize (IHtyl i). intuition lia. }
    rewrite -(take_drop (ty.(ty_size)) vl1) heap_mapsto_vec_app.
    iDestruct "H↦vl1" as "[H↦vl1 H↦pad]".
    iDestruct (ty_size_eq with "Hty") as "#>%".
    iApply (wp_persist_time_rcpt with "TIME Hdepth")=>//.
    iApply (wp_memcpy with "[$H↦vl1 $H↦2]"); [|lia|].
    { rewrite take_length. lia. }
    iNext; iIntros "[H↦vl1 H↦2] #Hdepth".
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //.
    iMod ("Hr" with "H↦2") as "($ & $ & Hty2)".
    iMod ("Hw" with "[-Hty2] Hdepth") as "[$ Hty]"; last first.
    { iSplitL "Hty"; [eauto with iFrame|]. iExists _. iFrame.
      iApply persist_time_rcpt_mono; [|done]. lia. }
    iNext. rewrite split_sum_mt /is_pad. iExists i. rewrite nth_lookup Hty. iFrame.
    iSplitL "H↦pad".
    - rewrite (shift_loc_assoc_nat _ 1) take_length Nat.min_l; last lia.
      iExists _. iFrame. rewrite /= drop_length. iPureIntro. lia.
    - iExists _. iFrame.
  Qed.

  Lemma type_sum_memcpy {E L} sty tyl i ty1 ty2 ty n ty1' ty2' C T T' p1 p2 e:
    Closed [] e →
    0 ≤ i →
    sty = sum tyl →
    tctx_extract E L [p1 ◁ ty1; p2 ◁ ty2] T T' →
    tyl !! (Z.to_nat i) = Some ty →
    (⊢ typed_write E L ty1 sty ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C ((p1 ◁ ty1') :: (p2 ◁ ty2') :: T') e -∗
    typed_body E L C T (p1 <-{n,Σ i} !p2 ;; e).
  Proof.
    iIntros (?? -> ??? Hr ?) "?". subst. rewrite -(Z2Nat.id i) //.
    by iApply type_seq; [eapply type_sum_memcpy_instr, Hr|done|done].
  Qed.

  Lemma ty_outlv_E_elctx_sat_sum E L tyl α:
    elctx_sat E L (tyl_outlv_E tyl α) →
    elctx_sat E L (ty_outlv_E (sum tyl) α).
  Proof.
    intro Hsat. eapply eq_ind; [done|]. clear Hsat.
    rewrite /tyl_outlv_E /ty_outlv_E /=.
    induction tyl as [|?? IH]=>//=. by rewrite IH fmap_app.
  Qed. *)
End case.

(* Global Hint Resolve ty_outlv_E_elctx_sat_sum : lrust_typing. *)
