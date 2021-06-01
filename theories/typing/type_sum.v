From iris.proofmode Require Import tactics.
From lrust.lang Require Import memcpy.
From lrust.typing Require Import uninit uniq_bor shr_bor own sum.
From lrust.typing Require Import lft_contexts type_context programs product.
From lrust.typing Require Import base_type.

Set Default Proof Using "Type".

Section case.
  Context `{!typeG Σ}.

  Notation hnthb := (hnth (base (𝔄:=@empty _ Empty_setₛ_empty))).

  Lemma type_case_own' {ℭ 𝔄l 𝔅l} prel E L (C : cctx ℭ) (T : tctx 𝔅l) p n (tyl : typel 𝔄l) el el' :
    list_to_hlist el = Some el' →
    HForallThree (λ _ ty e prei,
        match prei with
        | inl inner => ⊢ typed_body E L C
            ((p +ₗ #0 ◁ own_ptr n (uninit 1)) +:: (p +ₗ #1 ◁ own_ptr n ty) +::
              (p +ₗ #(S (ty.(ty_size))) ◁ own_ptr n (uninit (max_ty_size tyl - ty_size ty))) +:: T)
            e (λ post '(_ -:: a -:: _ -:: tl), inner post (a -:: tl))
        | inr outer => ⊢ typed_body E L C ((p ◁ own_ptr n (xsum_ty tyl)) +:: T) e outer
        end) tyl el' prel →
    ⊢ typed_body E L C ((p ◁ own_ptr n (xsum_ty tyl)) +:: T) (case: !p of el)
         (λ post '(v -:: w), ∀ i, match hnth (D := Empty_setₛ) (inr (λ _ _, False)) prel i with
          | inl inner => ∀ v', v = pinj i v' → inner post (v' -:: w)
          | inr outer => (∃ v', v = pinj (D := Empty_setₛ) i v') →  outer post (v -:: w)
         end)%type.
Proof.
    iIntros (elEl Hel tid [vπ vπl] postπ) "#LFT #TIME #PROPH #UNIQ #HE Hna HL HC /= [Hp HT] Hproph".
    wp_bind p. iApply (wp_hasty with "Hp").
    iIntros ([[]|] [|depth1]) "%Hv #Hdepth Hp /= //".
    iDestruct "Hp" as "[H↦ Hf]". iDestruct "H↦" as (vl) "[H↦ Hown]".
    iMod (bi.later_exist_except_0 with "Hown") as (i) "Hown".
    iMod (bi.later_exist_except_0 with "Hown")
      as (wπ vl' vl'') "(>(% & % & EQlen) & Hown)". subst.
    iDestruct "EQlen" as %[=EQlen]. rewrite -EQlen.
    rewrite -(Nat.add_1_l (length _)) app_length -!freeable_sz_split /=
            heap_mapsto_vec_cons heap_mapsto_vec_app.
    iDestruct "H↦" as "(H↦i & H↦vl' & H↦vl'')". iDestruct "Hf" as "(Hfi & Hfvl' & Hfvl'')".
    iAssert (⌜ i < length 𝔄l ⌝)%I with "[Hown]" as "%".
    { case (decide (i < length 𝔄l)) => [//| ?].
      rewrite hnth_default; [ apply lnth_default; lia | | lia].
      move => eq. destruct eq; by pose proof (wπ inhabitant). }
    eapply (HForallThree_nth_len _ (base (𝔄:=empty)) _ (inr (λ _ _, False)) _ _ _ i) in Hel as Hety; last lia.
    wp_read. wp_case.
    { split; [lia|]. destruct (list_to_hlist_length el el'); [done|].
      edestruct (nth_lookup_or_length el i ltac:(done)); [|lia].
      rewrite Nat2Z.id e. erewrite <-list_to_hlist_hnth_nth; [done|apply elEl]. }
    destruct (hnth _ prel i) eqn:EQty.
    - iApply (Hety $! tid (const () -:: _ -:: const () -:: _)
                with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
      rewrite /= !tctx_hasty_val' /= -?Hv //=; iFrame "HT".
      + rewrite /own_ptr /=.
        iDestruct (_.(ty_size_eq) with "Hown") as "%X". rewrite -X; clear X.
        iSplitL "H↦i Hfi"; last iSplitR "H↦vl'' Hfvl''"; iExists _; iFrame "#"; simpl.
        * rewrite shift_loc_0. iFrame. iExists [ #i]. rewrite heap_mapsto_vec_singleton.
          auto with iFrame.
        * eauto with iFrame.
        * rewrite -EQlen app_length minus_plus shift_loc_assoc_nat. auto 10 with iFrame.
      + iApply (proph_obs_impl with "Hproph") => π /= /(_ i).
        rewrite EQty. auto.
    - iApply (Hety $! tid (_ -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
      rewrite /= !tctx_hasty_val' /= -?Hv //=; iFrame "HT".
      + iExists _. iFrame "#".
        rewrite /= -EQlen app_length -(Nat.add_1_l (_+_)) -!freeable_sz_split. iFrame.
        iExists (#i :: vl' ++ vl''). iNext.
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app.
        iFrame. iExists i,_, vl', vl''. rewrite /= app_length /=. auto.
      + iApply (proph_obs_impl with "Hproph") => π /= /(_ i).
        rewrite EQty. eauto.
  Qed.

  Lemma type_case_own {ℭ 𝔄l 𝔅l ℭl} prel E L (C : cctx ℭ) (T : tctx 𝔅l) (T' : tctx ℭl)
                      p n (tyl : typel 𝔄l) el el' fr :
    list_to_hlist el = Some el' →
    tctx_extract_elt E L (p ◁ own_ptr n (xsum_ty tyl)) T T' fr →
    HForallThree (λ _ ty e prei,
        match prei with
        | inl inner => ⊢ typed_body E L C
            ((p +ₗ #0 ◁ own_ptr n (uninit 1)) +:: (p +ₗ #1 ◁ own_ptr n ty) +::
              (p +ₗ #(S (ty.(ty_size))) ◁ own_ptr n (uninit (max_ty_size tyl - ty_size ty))) +:: T')
            e (λ post '(_ -:: a -:: _ -:: tl), inner post (a -:: tl))
        | inr outer => ⊢ typed_body E L C ((p ◁ own_ptr n (xsum_ty tyl)) +:: T') e outer
        end) tyl el' prel →
    ⊢ typed_body E L C T (case: !p of el)
      (fr ∘ (λ post '(v -:: w), ∀ i, match hnth (D := Empty_setₛ) (inr (λ _ _, False)) prel i with
        | inl inner => ∀ v', v = pinj i v' → inner post (v' -:: w)
        | inr outer => (∃ v', v = pinj (D := Empty_setₛ) i v') → outer post (v -:: w)
        end)%type).
  Proof. intros. iApply typed_body_tctx_incl; [done|]. iApply type_case_own'; done. Qed.

  Lemma type_case_uniq' {𝔄l ℭ 𝔅l} prel E L (C : cctx ℭ) (T : tctx 𝔅l) p κ (tyl : typel 𝔄l) el el' :
    list_to_hlist el = Some el' → lctx_lft_alive E L κ →
    HForallThree
      (λ _ ty e prei, match prei with
        | inl inner => ⊢ typed_body E L C ((p +ₗ #1 ◁ &uniq{κ}ty) +:: T) e inner
        | inr outer => ⊢ typed_body E L C ((p ◁ &uniq{κ}(xsum_ty tyl)) +:: T) e outer
        end) tyl el' prel →
    ⊢ typed_body E L C ((p ◁ &uniq{κ}(xsum_ty tyl)) +:: T) (case: !p of el)
        (λ post '(v -:: tl), ∀ i, match hnth (D := Empty_setₛ) (inr (λ _ _, False)) prel i with
          | inl inner => ∀ (w w' : of_syn_type _), v = (pinj i w, pinj i w') → inner post ((w, w') -:: tl)
          | inr outer => (∃ w, v.1 = pinj (D := Empty_setₛ) i w) →  outer post (v -:: tl)
          end)%type.
  Proof.
    iIntros (el2el' Halive Hel tid [vπ vπl] postπ) "#LFT #TIME #PROPH #UNIQ #HE Hna HL HC /= [Hp HT] Hproph".
    wp_bind p. iApply (wp_hasty with "Hp").
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
    iAssert (⌜ i < length 𝔄l ⌝)%I with "[Hown]" as "%".
    { clear -wπ. case (decide (i < length 𝔄l)) => [//| ?].
      rewrite hnth_default; [ apply lnth_default; lia | | lia].
      move => eq. destruct eq; by pose proof (wπ inhabitant). }
    eapply (HForallThree_nth_len _ _ _ (inr (λ _ _, False)) _ _ _ i) in Hel as Hety; last lia.
    wp_read. wp_case.
    { split; [lia|]. destruct (list_to_hlist_length el el'); [done|].
      edestruct (nth_lookup_or_length el i ltac:(done)); [|lia].
      rewrite Nat2Z.id e. erewrite <-list_to_hlist_hnth_nth; [done|apply el2el']. }
    iDestruct (_.(ty_size_eq) with "Hown") as %EQlenvl'.
    destruct (hnth _ prel i) eqn:EQty.
    - iMod (uniq_intro wπ depth2 with "PROPH UNIQ") as (ζid) "[ζvo ζpc]"; [done|]; set ζ := PrVar _ ζid.
      iDestruct (uniq_proph_tok with "ζvo ζpc") as "(ζvo & ζ & Toζpc)"; rewrite proph_tok_singleton.
      iMod (uniq_preresolve ξ _ (λ π, pinj i (π ζ)) with "PROPH ξvo ξpc ζ")
        as "(#Hproph' & ζ & ξeqz)"; first done.
      { apply proph_dep_constr, proph_dep_one. }
      iDestruct ("Toζpc" with "ζ") as "ζpc".
      iMod ("Hclose'" $! (∃ vπ' d', (l +ₗ 1) ↦∗: (hnthb tyl i).(ty_own) vπ' d' tid ∗ ⧖(S d') ∗ .PC[ζ] vπ' d')%I
        with "[ξeqz H↦i H↦vl''] [ ζpc H↦vl' Hown]") as "[Hb Htok]".
      { iIntros "!>Hown".
        iMod (bi.later_exist_except_0 with "Hown") as (??) "(Hown & #>Hdepth2'' & ζpc)".
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
        iApply (proph_obs_impl with "Hproph") => π /= [+ /(_ i)].
        move: (equal_f A π) (equal_f B π).
        rewrite EQty {5}(_ : vπ = λ π, (fst (vπ π), snd (vπ π))); last first.
        { fun_ext => π'. by destruct (vπ π'). }
        move => /=->->->. auto.
    - iMod ("Hclose'" with "[] [H↦i H↦vl' H↦vl'' Hown ξpc]") as "[Hb Htok]";
        [by iIntros "!>$"| |].
      { iExists _, depth2. iFrame "∗#". iExists (#i::vl'++vl'').
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app /= -EQlen.
        iFrame. iNext. iExists i, _, vl', vl''. by iFrame. }
      iMod ("Hclose" with "Htok") as "HL".
      iApply (Hety $! _ (_ -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
      + iFrame. rewrite tctx_hasty_val' ?Hv //. iExists (S depth1).
        iFrame "#". iExists _, _. auto with iFrame.
      + iApply (proph_obs_impl with "Hproph") => π /= /(_ i).
        move: (equal_f A π). rewrite EQty => /= ->. eauto.
  Qed.

  Lemma type_case_uniq {ℭ 𝔄l 𝔅l ℭl} prel E L (C : cctx ℭ) (T : tctx 𝔅l) (T' : tctx ℭl)
                       p κ (tyl : typel 𝔄l) el el' fr :
    list_to_hlist el = Some el' → lctx_lft_alive E L κ →
    tctx_extract_elt E L (p ◁ &uniq{κ}(xsum_ty tyl)) T T' fr →
    lctx_lft_alive E L κ →
    HForallThree
      (λ _ ty e prei, match prei with
        | inl x => ⊢ typed_body E L C ((p +ₗ #1 ◁ &uniq{κ}ty) +:: T') e x
        | inr y => ⊢ typed_body E L C ((p ◁ &uniq{κ}(xsum_ty tyl)) +:: T') e y
        end) tyl el' prel →
    ⊢ typed_body E L C T (case: !p of el)
        (fr ∘ (λ post '(v -:: tl), ∀ i, match hnth (D := Empty_setₛ) (inr (λ _ _, False)) prel i with
        | inl inner => ∀ (w w' : of_syn_type _), v = (pinj i w, pinj i w') → inner post ((w, w') -:: tl)
        | inr outer => (∃ w, v.1 = pinj (D := Empty_setₛ) i w) →  outer post (v -:: tl)
        end)%type).
  Proof. intros. iApply typed_body_tctx_incl; [done|]. iApply type_case_uniq'; done. Qed.

  Lemma type_case_shr' {𝔅l 𝔄l ℭ} prel E L (C : cctx ℭ) (T : tctx 𝔅l) p κ (tyl : typel 𝔄l) el el' :
    list_to_hlist el = Some el' → lctx_lft_alive E L κ →
    HForallThree (λ _ ty e prei,
      match prei with
      | inl inner => ⊢ typed_body E L C ((p +ₗ #1 ◁ &shr{κ}ty) +:: T) e inner
      | inr outer => ⊢ typed_body E L C ((p ◁ &shr{κ}(xsum_ty tyl)) +:: T) e outer
      end) tyl el' prel →
    ⊢ typed_body E L C ((p ◁ &shr{κ}(xsum_ty tyl)) +:: T) (case: !p of el)
      (λ post '(v -:: w), ∀ i, match hnth (D := Empty_setₛ) (inr (λ _ _, False)) prel i with
        | inl inner => ∀ v', v = pinj i v' → inner post (v' -:: w)
        | inr outer => (∃ w, v = pinj (D := Empty_setₛ) i w) →  outer post (v -:: w)
      end)%type.
  Proof.
    iIntros (el2el' Halive Hel tid [? ?] postπ) "#LFT #TIME #PROPH UNIQ #HE Hna HL HC /= [Hp HT] Hproph". wp_bind p.
    iApply (wp_hasty with "Hp").
    iIntros ([[]|] [|depth]) "% Hdepth Hp //".
    iDestruct "Hp" as (i vπ) "(%Hvπ & #Hb & Hshr)".
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]". done.
    iMod (frac_bor_acc with "LFT Hb Htok") as (q') "[[H↦i H↦vl''] Hclose']". done.
    iAssert (⌜ i < length 𝔄l ⌝)%I with "[Hshr]" as "%".
    { clear -vπ. case (decide (i < length 𝔄l)) => [//| ?].
      rewrite hnth_default; [ apply lnth_default; lia | | lia].
      move => eq; destruct eq; by pose proof (vπ inhabitant). }
    eapply (HForallThree_nth_len _ _ _ (inr (λ _ _, False)) _ _ _ i) in Hel as Hety; last lia.
    wp_read. wp_case.
    { split; [lia|]. destruct (list_to_hlist_length el el'); [done|].
      edestruct (nth_lookup_or_length el i ltac:(done)); [|lia].
      rewrite Nat2Z.id e. erewrite <-list_to_hlist_hnth_nth; [done|apply el2el']. }
    iMod ("Hclose'" with "[$H↦i $H↦vl'']") as "Htok".
    iMod ("Hclose" with "Htok") as "HL".
    destruct (hnth _ prel i) eqn:EQty; iApply (Hety $! _ (_ -:: _) with "LFT TIME PROPH UNIQ HE Hna HL HC [-Hproph]").
    - rewrite /= tctx_hasty_val' /= -?H //. iFrame. iExists _. by iFrame.
    - iApply (proph_obs_impl with "Hproph") => /= π /(_ i); rewrite Hvπ EQty; eauto.
    - rewrite /= tctx_hasty_val' /= -?H //. iFrame.
      iExists _. iFrame. iExists _, _. by iFrame "%∗".
    - iApply (proph_obs_impl with "Hproph") => /= π /(_ i); rewrite Hvπ EQty; eauto.
  Qed.

  Lemma type_case_shr {ℭ 𝔄l 𝔅l ℭl} prel E L (C : cctx ℭ) (T : tctx 𝔅l) (T' : tctx ℭl)
                      p κ (tyl : typel 𝔄l) el el' fr :
    list_to_hlist el = Some el' → lctx_lft_alive E L κ →
    tctx_extract_elt E L (p ◁ &shr{κ}(xsum_ty tyl)) T T' fr →
    HForallThree (λ _ ty e prei,
      match prei with
      | inl inner => ⊢ typed_body E L C ((p +ₗ #1 ◁ &shr{κ}ty) +:: T') e inner
      | inr outer => ⊢ typed_body E L C ((p ◁ &shr{κ}(xsum_ty tyl)) +:: T') e outer
      end) tyl el' prel →
    ⊢ typed_body E L C T (case: !p of el)
        (fr ∘ (λ post '(v -:: w), ∀ i, match hnth (D := Empty_setₛ) (inr (λ _ _, False)) prel i with
            | inl inner => ∀ v', v = pinj i v' → inner post (v' -:: w)
            | inr outer => (∃ w, v = pinj (D := Empty_setₛ) i w) → outer post (v -:: w)
          end)%type).
  Proof. intros. iApply typed_body_tctx_incl; [done|]. iApply type_case_shr'; done. Qed.

  Lemma type_sum_assign_instr {E L 𝔄 𝔄' 𝔄l} (i : nat) (ty1: type 𝔄)
                              (tyl: typel 𝔄l) (ty2: type 𝔄') p1 p2 gt st Φ:
    typed_write E L ty1 (xsum_ty tyl) ty2 (xsum_ty tyl) gt st  →
    leak' E L (xsum_ty tyl) Φ →
    typed_instr E L +[p1 ◁ ty1; p2 ◁ hnthb tyl i] (p1 <-{Σ i} p2) (λ _, +[p1 ◁ ty2])
      (λ post '-[a; b], Φ (gt a) (post -[st a (pinj i b)])).
  Proof.
    iIntros ([Eq Hw] Lk tid postπ (? & ? & [])) "#LFT #TIME #PROPH #UNIQ #HE $ [HL HL'] (Hp1 & Hp2 & _) Hproph".
    iDestruct (closed_hasty with "Hp1") as "%". iDestruct (closed_hasty with "Hp2") as "%".
    wp_apply (wp_hasty with "Hp1"). iIntros (v1 depth1) "%Hv1 Hdepth1 Hty1".
    iDestruct "Hp2" as (v2 depth2) "(%Hv2 & Hdepth2 & Hty2)".
    iCombine "Hdepth1 Hdepth2" as "#Hdepth".
    rewrite !(ty_own_depth_mono _ _ (depth1 `max` depth2)); [|lia..].
    iMod (Hw with "LFT UNIQ HE HL Hty1") as (l ->) "(H & Hw)".
    iDestruct "H" as (vl) "(> H↦ & H)". iDestruct "H" as (?) "H".
    iMod (bi.later_exist_except_0 with "H") as (?) "H".
    iDestruct "H" as (??) "(>(% & % & H) & Leaked)".
    destruct vl as [|? vl]; iDestruct "H" as %[= Hlen].
    iAssert (▷ ty_own (Σ! tyl) _ _ tid _)%I with "[Leaked]" as "Leaked".
    { iExists i0, a, vl', _. iFrame. iPureIntro. naive_solver. }
    iDestruct (Lk (⊤ ∖ (⊤ ∖ ↑lftN ∖ ↑prophN)) with "LFT PROPH HE HL' Leaked") as "ToObs"; first set_solver.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ (⊤ ∖ ↑lftN ∖ ↑prophN)
    with "TIME Hdepth [ToObs]")=>//. { by iApply step_fupdN_with_emp. }
    rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[H↦0 H↦vl]".
    wp_write. wp_bind p1. iApply (wp_wand with "[]"); first by iApply (wp_eval_path).
    iIntros (? ->). wp_op. wp_bind p2.
    iApply (wp_wand with "[]"); first by iApply (wp_eval_path). iIntros (? ->).
    iDestruct (ty_size_eq with "Hty2") as %Hlenty. destruct vl as [|? vl].
    { exfalso. move: (Hlen) (i) Hlenty. elim tyl => //= > IH ? [|?]; eauto with lia.  }
    rewrite heap_mapsto_vec_cons -wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hdepth"); first solve_ndisj.
    iDestruct "H↦vl" as "[H↦ H↦vl]". wp_write. iIntros "#Hdepth' !> [ToObs HL']".
    iExists -[_]. rewrite tctx_hasty_val' // -(bi.exist_intro (S _)) bi.sep_assoc.
    iFrame "Hdepth'". iCombine "ToObs Hproph" as "Hproph". iSplitR "Hproph".
    - iFrame "HL'". iApply ("Hw" with "[-] [//]").
      iNext. iExists (_::_::_). rewrite !heap_mapsto_vec_cons. iFrame.
      iExists i, _, [_], _. rewrite -Hlen. auto.
    - iApply (proph_obs_impl with "Hproph") => π /= [impl ?]. by apply impl.
  Qed.

  Lemma type_sum_assign {E L 𝔅l ℭl 𝔄 𝔄' ℭ 𝔄l}
        (tyl : typel 𝔄l) i (ty1 : type 𝔄) (ty : type ℭ) (ty1' : type 𝔄')
        (C : cctx ℭ) (T : tctx 𝔅l) (T' : tctx ℭl) p1 p2 e gt st tr fr Φ:
    Closed [] e → (0 ≤ i)%nat →
    tctx_extract_ctx E L +[p1 ◁ ty1; p2 ◁ hnthb tyl i] T T' fr →
    typed_write E L ty1 (xsum_ty tyl) ty1' (xsum_ty tyl) gt st →
    leak' E L (xsum_ty tyl) Φ →
    typed_body E L C ((p1 ◁ ty1') +:: T') e tr -∗
    typed_body E L C T (p1 <-{Σ i} p2 ;; e)
      (fr ∘ (λ post '(a -:: b -:: f), Φ (gt a) (post (st a (pinj i b) -:: f))) ∘ tr).
  Proof.
    iIntros. iApply (typed_body_tctx_incl _ _  _ _ _ _ _ _ H1). via_tr_impl.
    { iApply type_seq; by [eapply type_sum_assign_instr|solve_typing]. }
    done.
  Qed.

  Lemma type_sum_unit_instr {E L 𝔄 𝔅 𝔄l} (i: nat) (tyl: typel 𝔄l) (ty1: type 𝔄)
                            (ty2: type 𝔅) p gt st eq:
    hnthb tyl i = eq_rect _ _ unit_ty _ eq →
    typed_write E L ty1 (xsum_ty tyl) ty2 (xsum_ty tyl) gt st →
    typed_instr E L +[p ◁ ty1] (p <-{Σ i} ())
    (λ _, +[p ◁ ty2]) (λ post '-[a], post -[st a (pinj i (eq_rect unitₛ _ () _ eq))]).
  Proof.
    iIntros (Hty [Eq Hw] tid postπ [vπ []]) "#LFT #TIME #PROPH #UNIQ #HE $ HL [Hp _] Hproph".
    wp_apply (wp_hasty with "Hp"). iIntros (depth v) "%Hv Hdepth Hty".
    iMod (Hw with "LFT UNIQ HE HL Hty") as (l ->) "(H & Hw)". clear Hw.
    iDestruct "H" as (vl) "(>H↦ & H)".
    iDestruct "H" as (?) "H"; iMod (bi.later_exist_except_0 with "H") as (?) "H";
      iDestruct "H" as (??) "(>(% & % & H) & _)".
    destruct vl as [|? vl]; iDestruct "H" as %[= Hlen].
    rewrite heap_mapsto_vec_cons -wp_fupd. iDestruct "H↦" as "[H↦0 H↦vl]".
    iApply (wp_persistent_time_receipt with "TIME Hdepth")=>//.
    wp_write. iIntros "#Hdepth". iExists -[_].
    rewrite right_id bi.sep_assoc tctx_hasty_val' //. iSplitR "Hproph".
    - rewrite -(bi.exist_intro (S _)). iFrame "Hdepth".
      iApply ("Hw" with "[-] Hdepth"). iModIntro. iExists (_::_).
      rewrite heap_mapsto_vec_cons. iFrame.
      iExists i, (λ _, eq_rect _ _ () _ eq), [], _. rewrite Hty -Hlen.
      iSplit; [done|]. clear Hty; destruct eq. iExists (const -[]). auto.
    - by iApply (proph_obs_impl with "Hproph").
  Qed.

  Lemma type_sum_unit {E L 𝔄 𝔄' ℭ 𝔄l 𝔅l ℭl} (tyl : typel 𝔄l) i (ty1 : type 𝔄)
                      (ty1' : type 𝔄') (C : cctx ℭ) (T : tctx 𝔅l) (T' : tctx ℭl) p e
    gt st fr tr (eq : ()%ST = lnthe 𝔄l i):
    Closed [] e → (0 ≤ i)%nat →
    tctx_extract_elt E L (p ◁ ty1) T T' fr →
    hnthb tyl i = eq_rect _ _ unit_ty _ eq →
    typed_write E L ty1 (xsum_ty tyl) ty1' (xsum_ty tyl) gt st →
    typed_body E L C ((p ◁ ty1') +:: T') e tr -∗
    typed_body E L C T (p <-{Σ i} () ;; e)
      (fr ∘ (λ post '(a -:: f), post (st a (pinj i (eq_rect unitₛ _ () _ eq)) -:: f) ) ∘ tr).
  Proof.
    iIntros (?? Incl) "* **". iApply (typed_body_tctx_incl _ _  _ _ _ _ _ _ Incl).
    via_tr_impl.
    { iApply type_seq; by [eapply type_sum_unit_instr|solve_typing]. }
    done.
  Qed.

  Lemma type_sum_memcpy_instr {E L 𝔄l 𝔄 𝔄' 𝔅 𝔅'} (i : nat) (tyl : typel 𝔄l)
    (ty1 : type 𝔄) (ty1' : type 𝔄') (ty2 : type 𝔅) (ty2' : type 𝔅') p1 p2 gt st rd wt:
    let ty := hnthb tyl i in
    typed_write E L ty1 (xsum_ty tyl) ty1' (xsum_ty tyl) gt st →
    typed_read E L ty2 ty ty2' rd wt →
    typed_instr E L +[p1 ◁ ty1; p2 ◁ ty2]
      (p1 <-{ty.(ty_size),Σ i} !p2) (λ _, +[p1 ◁ ty1'; p2 ◁ ty2'])
      (λ post '-[a; b], post -[st a (pinj i (rd b)); wt b]).
  Proof.
    iIntros (ty [Eq Hw] Hr tid postπ (vπ & wπ & [])) "#LFT #TIME #PROPH #UNIQ #HE Htl [HL1 HL2] (Hp1 & Hp2 & _) Hproph".
    iDestruct (closed_hasty with "Hp1") as "%". iDestruct (closed_hasty with "Hp2") as "%".
    wp_apply (wp_hasty with "Hp1"). iIntros (v1 depth1) "%Hv1 Hdepth1 Hty1".
    iDestruct "Hp2" as (v2 depth2) "(%Hv2 & Hdepth2 & Hty2)".
    iCombine "Hdepth1 Hdepth2" as "Hdepth".
    rewrite !(ty_own_depth_mono _ _ (depth1 `max` depth2)); [|lia..].
    iMod (Hw with "LFT UNIQ HE HL1 Hty1") as (l1 ->) "(H & Hw)".
    iDestruct "H" as (?) "(>H↦ & H)".
    iMod (bi.later_exist_except_0 with "H") as (?) "H";
    iMod (bi.later_exist_except_0 with "H") as (?) "H";
    iDestruct "H" as (??) "(>(% & % & H) & _)".
    clear Hw. destruct vl as [|? vl]; iDestruct "H" as %[= Hlen].
    rewrite heap_mapsto_vec_cons -wp_fupd. iDestruct "H↦" as "[H↦0 H↦vl1]". wp_write.
    wp_bind p1. iApply (wp_wand with "[]"); first by iApply (wp_eval_path). iIntros (? ->).
    wp_op. wp_bind p2. iApply (wp_wand with "[]"); first by iApply (wp_eval_path). iIntros (? ->).
    iMod (Hr with "LFT HE Htl HL2 Hty2") as (l2 vl2 q) "(% & H↦2 & Hty & Hr)" => //=.
    clear Hr. subst. assert (ty.(ty_size) ≤ length vl).
    { rewrite Hlen. clear. generalize dependent i. induction tyl => //= - [|i]; [lia|].
      specialize (IHtyl i). intuition lia. }
    rewrite -(take_drop (ty.(ty_size)) vl) heap_mapsto_vec_app.
    iDestruct "H↦vl1" as "[H↦vl1 H↦pad]".
    iDestruct (ty_size_eq with "Hty") as "#>%Hvl2Len".
    iApply (wp_persistent_time_receipt with "TIME Hdepth")=>//.
    iApply (wp_memcpy with "[$H↦vl1 $H↦2]"); [|lia|].
    { rewrite take_length. lia. }
    iNext; iIntros "[H↦vl1 H↦2] #Hdepth". iExists -[_; _].
    rewrite right_id !tctx_hasty_val' //.
    iMod ("Hr" with "H↦2") as "($ & $ & Hty2)".
    iMod ("Hw" with "[-Hty2 Hproph] Hdepth") as "[$ Hty]"; last first. iSplitR "Hproph".
    { iSplitL "Hty"; [eauto with iFrame|]. iExists _. iFrame.
      iApply persistent_time_receipt_mono; [|done]. lia. }
    { iApply (proph_obs_impl with "Hproph") => /= π post; apply post. }
    iNext. rewrite split_sum_mt /is_pad. iExists i, _.  iFrame.
    iSplitR; [done|iSplitL "H↦pad"].
    - rewrite (shift_loc_assoc_nat _ 1) take_length Nat.min_l; last lia.
      iExists _. iFrame. rewrite /= drop_length. iPureIntro. rewrite -Hvl2Len. lia.
    - iExists _. iFrame.
  Qed.

  Lemma type_sum_memcpy {E L 𝔄l 𝔄 𝔄' 𝔅 𝔅' ℭ 𝔅l ℭl} (tyl : typel 𝔄l) i
                        (ty1 : type 𝔄) (ty2 : type 𝔅) n (ty1' : type 𝔄')
                        (ty2' : type 𝔅') (C : cctx ℭ) (T : tctx 𝔅l) (T' : tctx ℭl) p1 p2 e
    fr tr gt st rd wt:
    let ty := hnthb tyl i in
    Closed [] e → (0 ≤ i)%nat →
    tctx_extract_ctx E L +[p1 ◁ ty1; p2 ◁ ty2] T T' fr →
    typed_write E L ty1 (xsum_ty tyl) ty1' (xsum_ty tyl) gt st →
    typed_read E L ty2 ty ty2' rd wt →
    Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C ((p1 ◁ ty1') +:: (p2 ◁ ty2') +:: T') e tr -∗
    typed_body E L C T (p1 <-{n,Σ i} !p2 ;; e)
      (fr ∘ (λ post '(a -:: b -:: f), post (st a (pinj i (rd b)) -:: wt b -:: f)) ∘ tr).
  Proof.
    iIntros (??? Incl ?? <-) "* **". iApply (typed_body_tctx_incl _ _  _ _ _ _ _ _ Incl).
    via_tr_impl.
    { iApply type_seq; by [eapply type_sum_memcpy_instr|solve_typing]. }
    done.
  Qed.

  Lemma ty_outlives_E_elctx_sat_sum {𝔄l} E L (tyl : typel 𝔄l) α:
    elctx_sat E L (tyl_outlives_E tyl α) →
    elctx_sat E L (ty_outlives_E (xsum_ty tyl) α).
  Proof.
    intro Hsat. eapply eq_ind; [done|]. clear Hsat.
    rewrite /tyl_outlives_E /ty_outlives_E /=.
    induction tyl as [|???? IH]=>//=. by rewrite IH fmap_app.
  Qed.
End case.

Global Hint Resolve ty_outlives_E_elctx_sat_sum : lrust_typing.
