From iris.algebra.lib Require Export excl_auth.
From iris.proofmode Require Import tactics.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import util lft_contexts type_context programs.
Set Default Proof Using "Type".

Section uniq_bor.
  Context `{!typeG Σ}.

  Program Definition uniq_bor (κ:lft) (ty:type) :=
    {| ty_size := 1;
       ty_lfts := κ :: ty.(ty_lfts); ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
       ty_own depth0 tid vl :=
         κ ⊑ ty.(ty_lft) ∗
         match depth0, vl return _ with
         | S depth1, [ #(LitLoc l) ] =>
           ∃ depth2 γ, ⌜depth2 ≤ depth1⌝%nat ∗ own γ (◯E depth2) ∗
             &{κ} (∃ depth2', own γ (●E depth2') ∗ ⧖S depth2' ∗
                                     l ↦∗: ty.(ty_own) depth2' tid)
         | _, _ => False
         end;
       ty_shr κ' tid l :=
         ∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗ ▷ ty.(ty_shr) κ' tid l'
    |}%I.
  Next Obligation. by iIntros (κ ty [|depth] tid [|[[]|][]]) "[_ H]". Qed.
  Next Obligation.
    intros κ ty [|depth1] [|depth2] tid [|[[]|][]] ?; try iIntros "[_ []]" || lia.
    do 8 f_equiv. lia.
  Qed.
  Next Obligation.
    move=> κ ty N depth0 κ' l tid ??/=. iIntros "#LFT #Houtlives Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as ([|[[|l'|]|][]]) "Hb"=>//;
      (iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]"; [done|]);
      destruct depth0 as [|depth1];
      try (by iMod (bor_persistent with "LFT Hb2 Htok") as "[[_ >[]] _]").
    iMod (bor_sep with "LFT Hb2") as "[_ Hb2]"; [done|].
    iMod (bor_exists with "LFT Hb2") as (depth2) "Hb2"; [done|].
    iMod (bor_exists with "LFT Hb2") as (γ) "Hb2"; [done|].
    iMod (bor_sep with "LFT Hb2") as "[Hdepth Hb2]"; [done|].
    iMod (bor_persistent with "LFT Hdepth Htok") as "[>Hdepth Htok]"; [done|].
    iDestruct "Hdepth" as %Hdepth.
    iMod (bor_sep with "LFT Hb2") as "[Hdepth2 Hb2]"; [done|].
    iMod (bor_unnest with "LFT Hb2") as "Hb2"; [done|].
    iIntros "/= !> !> !>". iMod "Hb2".
    iMod (bor_exists with "LFT Hb2") as (depth2') "Hb2"; [done|].
    iDestruct (bor_shorten κ' with "[] Hb2") as "Hb2".
    { iApply lft_incl_glb; [|iApply lft_incl_refl].
      iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    iMod (bor_sep with "LFT Hb2") as "[Hdepth2' Hb2]"; [done|].
    iMod (bor_combine with "LFT Hdepth2' Hdepth2") as "Hdepth"; [done|].
    assert (Hvalid : ∀ x : excl_authR natO, own γ x ⊣⊢ own γ x ∗ ✓x).
    { intros ?. iSplit; [|iIntros "[$ _]"]. iIntros "H".
      by iDestruct (own_valid with "H") as "#$". }
    rewrite -own_op Hvalid. iMod (bor_sep with "LFT Hdepth") as "[_ Hdepth]"; [done|].
    iMod (bor_persistent with "LFT Hdepth Htok") as "[>Hdepth Htok]"; [done|].
    iDestruct "Hdepth" as %->%excl_auth_agree_L.
    iMod (bor_sep with "LFT Hb2") as "[_ Hb2]"; [done|].
    iMod (ty_share with "LFT [] Hb2 Htok") as "Hb2"=>//.
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    (* TODO prove that step_fupdN is monotonic. *)
    iModIntro. iInduction Hdepth as [|] "IH"; last first.
    { iIntros "/= !> !> !>". iApply ("IH" with "[$] [$]"). }
    iApply (step_fupdN_wand with "Hb2"). iIntros ">[? $]".
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "Hb1"; first solve_ndisj.
    eauto with iFrame.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid l. iIntros "/= #Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]".
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]").
    by iApply (ty_shr_mono with "Hκ").
  Qed.

  Global Instance uniq_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) uniq_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2. rewrite eqtype_unfold=>Hty. iIntros (?) "HL".
    iDestruct (Hty with "HL") as "#Hty". iDestruct (Hκ with "HL") as "#Hκ".
    iIntros "!# #HE". iSplit; first done.
    iDestruct ("Hty" with "HE") as "(_ & #[Hout1 Hout2] & #Ho & #Hs)";
      [done..|clear Hty].
    iSpecialize ("Hκ" with "HE"). iSplit; [|iSplit; iModIntro].
    - by iApply lft_intersect_mono.
    - iIntros ([|] ? [|[[]|][]]) "[#? H] //". iSplitR.
      + by do 2 (iApply lft_incl_trans; [done|]).
      + iDestruct "H" as (???) "[? H]". iExists _, _. iFrame "∗ %".
        iApply (bor_shorten with "Hκ"). iApply bor_iff; last done.
        iNext. iModIntro.
        by iSplit; iIntros "H"; iDestruct "H" as (?) "(?&?&H)";
        iDestruct "H" as (?) "[??]"; iExists _; iFrame; iExists vl; iFrame; iApply "Ho".
    - iIntros (κ ??) "H". iDestruct "H" as (l') "[Hbor #Hupd]". iExists l'.
      iFrame. by iApply "Hs".
  Qed.
  Global Instance uniq_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) uniq_bor.
  Proof. intros ??????. apply uniq_mono. done. by symmetry. Qed.
  Global Instance uniq_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) uniq_bor.
  Proof. intros ??[]; split; by apply uniq_mono. Qed.

  Global Instance uniq_type_contractive κ : TypeContractive (uniq_bor κ).
  Proof.
    split.
    - apply (type_lft_morphism_add _ κ [κ] []) => ?.
      + iApply lft_equiv_refl.
      + by rewrite /= elctx_interp_app elctx_interp_ty_outlives_E
                   /elctx_interp /= left_id right_id.
    - done.
    - move=> ??? Hsz Hl HE Ho ??? vl /=. f_equiv.
      + apply equiv_dist. iDestruct Hl as "#[??]".
        iSplit; iIntros "#H"; (iApply lft_incl_trans; [iApply "H"|done]).
      + repeat (apply Ho || f_contractive || f_equiv).
    - move=> ??????? Hs ??? /=. repeat (apply Hs || f_contractive || f_equiv).
  Qed.

  Global Instance uniq_ne κ : NonExpansive (uniq_bor κ).
  Proof. solve_ne_type. Qed.

  Global Instance uniq_send κ ty :
    Send ty → Send (uniq_bor κ ty).
  Proof.
    intros Hsend [] tid1 tid2 [|[[]|][]]=>//=. do 7 f_equiv. iIntros "?".
    iApply bor_iff; last done. iNext. iModIntro. iApply bi.equiv_iff.
    do 7 f_equiv. by iSplit; iIntros "."; iApply Hsend.
  Qed.

  Global Instance uniq_sync κ ty :
    Sync ty → Sync (uniq_bor κ ty).
  Proof.
    iIntros (Hsync κ' tid1 tid2 l) "H". iDestruct "H" as (l') "[Hm #Hshr]".
    iExists l'. iFrame "Hm". by iApply Hsync.
  Qed.
End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma uniq_mono' E L κ1 κ2 ty1 ty2 :
    lctx_lft_incl E L κ2 κ1 → eqtype E L ty1 ty2 →
    subtype E L (&uniq{κ1}ty1) (&uniq{κ2}ty2).
  Proof. by intros; apply uniq_mono. Qed.
  Lemma uniq_proper' E L κ ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (&uniq{κ}ty1) (&uniq{κ}ty2).
  Proof. by intros; apply uniq_proper. Qed.

  Lemma tctx_reborrow_uniq E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [p ◁ &uniq{κ}ty] [p ◁ &uniq{κ'}ty; p ◁{κ'} &uniq{κ}ty].
  Proof.
    iIntros (Hκκ' tid ?) "#LFT HE HL H". iDestruct (Hκκ' with "HL HE") as "#Hκκ'".
    iFrame. rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|] [|depth1]) "(#Hdepth1 & % & #Hout & Hb)"; try done.
    iDestruct "Hb" as (depth2 γ Hdepth) "[H◯ Hb]".
    iMod (rebor with "LFT Hκκ' Hb") as "[Hb Hext]"; try done.
    iMod (bor_create _ κ' (∃ depth2', own γ (◯E depth2') ∗ ⧖S depth2')%I
            with "LFT [H◯]") as "[H◯ H◯†]"; [done| |].
    { iExists depth2. iFrame. iApply persistent_time_receipt_mono; [|done]. lia. }
    iMod (bor_combine with "LFT H◯ Hb") as "Hb"; [done|].
    iMod (bor_acc_atomic_cons with "LFT Hb") as "[[[>H◯ H] Hclose]|[#H† Hclose]]";
      [done| |]; last first.
    { iMod "Hclose" as "_". iSplitR.
      - iExists _, _. iFrame "# %". iSplitR; [by iApply lft_incl_trans|].
        iMod (own_alloc (◯E 0%nat)) as (γ') "?"; [by apply auth_frag_valid|].
        iExists _, _. iFrame. iSplitR; [auto with lia|]. by iApply bor_fake.
      - iMod ("H◯†" with "H†") as (depth1') ">[H◯ #Hdepth1']".
        iMod ("Hext" with "H†") as "Hb".
        iExists _. iIntros "{$%} !> _". iExists (S depth1'). iFrame "#".
        eauto with iFrame. }
    iClear (depth1 depth2 Hdepth) "Hdepth1".
    iDestruct "H" as (depth2') "(>H● & _ & Hown)".
    iDestruct "H◯" as (depth2) "[H◯ #Hdepth2]".
    iDestruct (own_valid_2 with "H● H◯") as %->%excl_auth_agree_L.
    iMod (own_alloc (●E depth2 ⋅ ◯E depth2)) as (γ') "[H●' H◯']";
      [by apply excl_auth_valid|].
    iMod ("Hclose" $! (∃ depth2', own γ' (●E depth2') ∗ ⧖S depth2' ∗
                                    l ↦∗: ty_own ty depth2' tid)%I
            with "[H◯ H●] [Hown H●']").
    { iIntros "!>". iDestruct 1 as (depth2') "(_ & #>Hdepth2' & Hown)".
      iMod (own_update_2 with "H● H◯") as "[H● H◯]"; [by apply excl_auth_update|].
      iSplitL "H◯"; iExists depth2'; auto with iFrame. }
    { iExists _. by iFrame. }
    iModIntro. iSplitR "Hext H◯†".
    - iExists _, (S _). simpl. iFrame "%#". iSplitR; [by iApply lft_incl_trans|].
      iExists _, _. by iFrame "∗%".
    - iExists _. iSplit; [done|]. iIntros "#H†".
      iMod ("Hext" with "H†") as "Hb". iMod ("H◯†" with "H†") as ">H◯".
      iDestruct "H◯" as (depth2') "[H◯ #Hdepth2']". iExists (S depth2').
      iFrame "#". iExists depth2', γ. by iFrame.
  Qed.

  Lemma tctx_extract_hasty_reborrow E L p ty ty' κ κ' T :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' →
    tctx_extract_hasty E L p (&uniq{κ'}ty) ((p ◁ &uniq{κ}ty')::T)
                       ((p ◁{κ'} &uniq{κ}ty')::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]). rewrite tctx_reborrow_uniq //.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, uniq_mono'.
  Qed.

  Lemma read_uniq E L κ ty :
    Copy ty → lctx_lft_alive E L κ → ⊢ typed_read E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    rewrite typed_read_eq. iIntros (Hcopy Halive) "!#".
    iIntros ([[]|] [|depth1] tid F qL ?) "#LFT #HE Htl HL [Hout Hown] //".
    iDestruct "Hown" as (depth2 γ) "(% & H◯ & Hown)".
    iMod (Halive with "HE HL") as (q) "[Hκ Hclose]"; first solve_ndisj.
    iMod (bor_acc with "LFT Hown Hκ") as "[H Hclose']"; first solve_ndisj.
    iDestruct "H" as (depth2') "(>H● & >#Hdepth2' & H↦)".
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". iIntros "!>".
    iExists _, _, _. iSplit; first done. iFrame "H↦ Htl Hout".
    iDestruct (own_valid_2 with "H● H◯") as %->%excl_auth_agree_L.
    iDestruct (ty_own_depth_mono with "Hown") as "$"; [lia|].
    iIntros "H↦". iMod ("Hclose'" with "[H↦ H●]") as "[Hb Htok]".
    { eauto 10 with iFrame. }
    iMod ("Hclose" with "Htok") as "$". eauto with iFrame.
  Qed.

  Lemma write_uniq E L κ ty :
    lctx_lft_alive E L κ → ⊢ typed_write E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    rewrite typed_write_eq. iIntros (Halive) "!#".
    iIntros ([[]|] [|depth1] tid F qL ?) "#LFT HE HL [Hout Hown] //".
    iDestruct "Hown" as (depth2 γ) "(% & H◯ & Hown)".
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    iMod (bor_acc with "LFT Hown Htok") as "[H Hclose']"; first solve_ndisj.
    iDestruct "H" as (depth2') "(>H● & _ & H↦)".
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iModIntro. iExists _, _. iSplit; first done.
    iFrame. iIntros "Hown #Hdepth1". iDestruct "Hown" as (vl') "[H↦ Hown]".
    iMod (own_update_2 with "H● H◯") as "[H● H◯]"; [by apply excl_auth_update|].
    iMod ("Hclose'" with "[> H↦ Hown H●]") as "[Hb Htok]".
    { iExists _. iFrame "Hdepth1". auto with iFrame. }
    iMod ("Hclose" with "Htok") as "$". auto with iFrame.
  Qed.
End typing.

Global Hint Resolve uniq_mono' uniq_proper' write_uniq read_uniq : lrust_typing.
Global Hint Resolve tctx_extract_hasty_reborrow | 10 : lrust_typing.
