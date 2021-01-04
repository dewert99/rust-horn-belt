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
       ty_own tid vl :=
         κ ⊑ ty.(ty_lft) ∗
         match vl return _ with
         | [ #(LitLoc l) ] => &{κ} (l ↦∗: ty.(ty_own) tid)
         | _ => False
         end;
       ty_shr κ' tid l :=
         ∃ l':loc, &frac{κ'}(λ q', l ↦{q'} #l') ∗
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[κ']
               ={F}[F∖↑shrN]▷=∗ ty.(ty_shr) (κ') tid l' ∗ q.[κ']
    |}%I.
  Next Obligation. by iIntros (q ty tid [|[[]|][]]) "[_ H]". Qed.
  Next Obligation.
    move=> κ ty N κ' l tid ??/=. iIntros "#LFT #Hout Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as ([|[[|l'|]|][]]) "Hb"; first solve_ndisj;
      (iMod (bor_sep with "LFT Hb") as "[Hb1 Hb]"; first solve_ndisj);
      (iMod (bor_sep with "LFT Hb") as "[Hb2 Hb3]"; first solve_ndisj);
      try (iMod (bor_persistent with "LFT Hb3 Htok") as "[>[] _]"; solve_ndisj).
    iMod (bor_persistent with "LFT Hb2 Htok") as "[#Hout' Htok]"; first solve_ndisj.
    iFrame. iExists l'. subst. rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "$"; first solve_ndisj.
    iApply delay_sharing_nested=>//. iApply lft_incl_trans; [done|].
    iApply lft_intersect_incl_l.
  Qed.
  Next Obligation.
    intros κ0 ty κ κ' tid l. iIntros "#Hκ #H".
    iDestruct "H" as (l') "[Hfb Hvs]".
    iExists l'. iSplit. by iApply (frac_bor_shorten with "[]").
    iIntros "!# * % Htok". iApply (step_fupd_mask_mono F _ (F∖↑shrN)); try solve_ndisj.
    iMod (lft_incl_acc with "Hκ Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hvs" with "[%] Htok") as "Hvs'"; first solve_ndisj. iModIntro. iNext.
    iMod "Hvs'" as "[#Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
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
    - iIntros (? [|[[]|][]]) "[#? H] //". iSplitR.
      + by do 2 (iApply lft_incl_trans; [done|]).
      + iApply (bor_shorten with "Hκ"). iApply bor_iff; last done.
        iNext. iModIntro. iSplit; iIntros "H"; iDestruct "H" as (vl) "[??]";
        iExists vl; iFrame; by iApply "Ho".
    - iIntros (κ ??) "H".
      iDestruct "H" as (l') "[Hbor #Hupd]". iExists l'. iIntros "{$Hbor}!# %%% Htok".
      iMod ("Hupd" with "[%] Htok") as "Hupd'"; try done. iModIntro. iNext.
      iMod "Hupd'" as "[H $]". by iApply "Hs".
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
    - move=> ??? Hsz Hl HE Ho ?? vl /=. f_equiv.
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
    iIntros (Hsend tid1 tid2 [|[[]|][]]) "// [$ H]".
    iApply bor_iff; last done. iNext. iModIntro. iApply bi.equiv_iff.
    do 3 f_equiv. iSplit; iIntros "."; by iApply Hsend.
  Qed.

  Global Instance uniq_sync κ ty :
    Sync ty → Sync (uniq_bor κ ty).
  Proof.
    iIntros (Hsync κ' tid1 tid2 l) "H". iDestruct "H" as (l') "[Hm #Hshr]".
    iExists l'. iFrame "Hm". iModIntro. iIntros (F q) "% Htok".
    iMod ("Hshr" with "[] Htok") as "Hfin"; first done. iClear "Hshr".
    iModIntro. iNext. iMod "Hfin" as "[Hshr $]". iApply Hsync. done.
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
    iFrame.
    rewrite tctx_interp_singleton tctx_interp_cons tctx_interp_singleton.
    iDestruct "H" as ([[]|]) "(% & #? & Hb)"; try done.
    iMod (rebor with "LFT Hκκ' Hb") as "[Hb Hext]"; try done. iModIntro.
    iSplitL "Hb".
    - iExists _. iSplit; [done|]. iSplit; [|done]. by iApply lft_incl_trans.
    - iExists _. iSplit; [done|]. iFrame "#". done.
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
    iIntros ([[]|] tid F qL ?) "#LFT #HE Htl HL [Hout Hown]"; try done.
    iMod (Halive with "HE HL") as (q) "[Hκ Hclose]"; first solve_ndisj.
    iMod (bor_acc with "LFT Hown Hκ") as "[H↦ Hclose']"; first solve_ndisj.
    iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". iIntros "!>".
    iExists _, _, _. iSplit; first done. iFrame "∗#". iIntros "H↦".
    iMod ("Hclose'" with "[H↦]") as "[$ Htok]". by iExists _; iFrame.
    by iMod ("Hclose" with "Htok") as "($ & $ & $)".
  Qed.

  Lemma write_uniq E L κ ty :
    lctx_lft_alive E L κ → ⊢ typed_write E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    rewrite typed_write_eq. iIntros (Halive) "!#".
    iIntros ([[]|] tid F qL ?) "#LFT HE HL [Hout Hown]"; try done.
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    iMod (bor_acc with "LFT Hown Htok") as "[H↦ Hclose']"; first solve_ndisj.
    iDestruct "H↦" as (vl) "[>H↦ Hown]". rewrite ty.(ty_size_eq).
    iDestruct "Hown" as ">%". iModIntro. iExists _, _. iSplit; first done.
    iFrame. iIntros "Hown". iDestruct "Hown" as (vl') "[H↦ Hown]".
    iMod ("Hclose'" with "[H↦ Hown]") as "[$ Htok]". by iExists _; iFrame.
    by iMod ("Hclose" with "Htok") as "($ & $ & $)".
  Qed.
End typing.

Hint Resolve uniq_mono' uniq_proper' write_uniq read_uniq : lrust_typing.
Hint Resolve tctx_extract_hasty_reborrow | 10 : lrust_typing.
