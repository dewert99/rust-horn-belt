From iris.algebra.lib Require Export excl_auth.
From iris.proofmode Require Import tactics.
From lrust.util Require Import basic update.
From lrust.lang Require Import heap.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_cmra.
(* From lrust.typing Require Import lft_contexts type_context programs. *)
Set Default Proof Using "Type".

Section uniq_bor.
  Context `{!typeG Σ}.

  Program Definition uniq_bor {A} (κ: lft) (ty: type A) : type (A * A) := {|
    ty_size := 1;  ty_lfts := κ :: ty.(ty_lfts);  ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    ty_own vπd tid vl := ∃d (l: loc) (ξ: proph_var' A), ⌜S d ≤ vπd.2⌝ ∗ ⌜vl = [ #l]⌝ ∗
      ⌜snd ∘ vπd.1 = (.$ ξ)⌝ ∗ .VO[ξ] (fst ∘ vπd.1, d) ∗
      &{κ} (∃vπd', l ↦∗: ty.(ty_own) vπd' tid ∗ ⧖ S vπd'.2 ∗ .PC[ξ] vπd');
    ty_shr vπd κ' tid l := ∃d (l': loc) ξ, ⌜vπd.2 = S d⌝ ∗ ⌜snd ∘ vπd.1 ./ [ξ]⌝ ∗
      &frac{κ'}(λ q', l ↦{q'} #l') ∗ &frac{κ'} (λ q, q:[ξ]) ∗
      ▷ ty.(ty_shr) (fst ∘ vπd.1, d) κ' tid l';
  |}%I.
  Next Obligation. move=> *. by iDestruct 1 as (????->) "?". Qed.
  Next Obligation.
    move=> ????[|d']*/=; iDestruct 1 as (d l ξ ?->?) "[??]"; [lia|].
    iExists d, l, ξ. iSplit; [iPureIntro; lia|]. do 2 (iSplit; [done|]). iFrame.
  Qed.
  Next Obligation.
    move=> ????[|d']*/=; iDestruct 1 as (d l ξ ->?) "[Bor [Bor' ?]]"; [lia|].
    iExists d', l, ξ. do 2 (iSplit; [done|]). iFrame "Bor Bor'".
    iApply ty_shr_depth_mono; [|done]. lia.
  Qed.
  Next Obligation.
    move=> *. iIntros "#In". iDestruct 1 as (d l ξ -> ?) "[?[??]]". iExists d, l, ξ.
    do 2 (iSplit; [done|]). do 2 (iSplit; [by iApply frac_bor_shorten|]).
    by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> A ??? vπ *. iIntros "#LFT #? Bor Tok".
    have ?: Inhabited A := populate ((vπ inhabitant).1).
    iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorMt Bor]"; [done|].
    iMod (bor_exists with "LFT Bor") as (d) "Bor"; [done|].
    iMod (bor_exists with "LFT Bor") as (l) "Bor"; [done|].
    iMod (bor_exists with "LFT Bor") as (ξ) "Bor"; [done|].
    iMod (bor_sep_persistent with "LFT Bor Tok") as "[>%Le [Bor Tok]]"; [done|].
    do 2 (iMod (bor_sep_persistent with "LFT Bor Tok") as "[>-> [Bor Tok]]"; [done|]).
    iMod (bor_sep with "LFT Bor") as "[BorVo Bor]"; [done|].
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|].
    move: Le=> /succ_le /=[d'[->Le]]. iIntros "!>!>!>".
    iMod (bor_shorten with "[] Bor") as "Bor".
    { iApply lft_incl_glb; [|iApply lft_incl_refl].
      iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorOwn Bor]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[_ BorPc]"; [done|].
    iMod (bor_combine with "LFT BorVo BorPc") as "Bor"; [done|].
    iMod (bor_acc_cons with "LFT Bor Tok") as "[[Vo Pc] Close]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-) "[Vo Pc]".
    iDestruct (uniq_proph_tok with "Vo Pc") as "[Vo [PTok PrePc]]".
    iMod ("Close" with "[Vo PrePc] PTok") as "[BorPTok Tok]".
    { iIntros "!> >PTok !>!>". iFrame "Vo". by iApply "PrePc". }
    iMod (ty_share with "LFT [] BorOwn Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iApply step_fupdN_nmono; [by apply Le|]. iApply (step_fupdN_wand with "Upd").
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT BorMt") as "BorMt"; [done|].
    iMod (bor_fracture (λ q, q:[_])%I with "LFT BorPTok") as "BorPTok"; [done|].
    iIntros "!> >[? $] !>". iExists d', l, ξ. iFrame "BorMt BorPTok". iSplit; [done|].
    iSplit; [iPureIntro; apply proph_dep_one|]. by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #?". iDestruct 1 as (d l ξ Le->Eq) "[Vo Bor]".
    move: Le=> /succ_le [?[->Le]]/=. iDestruct 1 as "[Tok Tok']".
    iMod (lft_incl_acc with "[] Tok") as (?) "[Tok PreTok]"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    iMod (bor_acc with "LFT Bor Tok") as "[Big Close']"; [done|]. iIntros "!>!>!>".
    iDestruct "Big" as (?) "[Own [#Time Pc]]". iDestruct "Own" as (vl) "[Mt Own]".
    iDestruct (uniq_agree with "Vo Pc") as "#<-".
    iDestruct (uniq_proph_tok with "Vo Pc") as "[Vo [PTok' PrePc]]".
    iMod (ty_own_proph with "LFT [] Own Tok'") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. } iModIntro.
    iApply step_fupdN_nmono; [apply Le|]. iApply (step_fupdN_wand with "Upd").
    iMod 1 as (ξs ??) "[PTok Close]". iModIntro. rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "PTok PTok'") as (q) "[PTok PrePToks]".
    iExists (ξs ++ [ξ: proph_var]), q. iSplit.
    { iPureIntro. apply proph_dep_pair; [done|]. rewrite Eq. apply proph_dep_one. }
    iFrame "PTok". iIntros "PTok". iDestruct ("PrePToks" with "PTok") as "[PTok PTok']".
    iMod ("Close" with "PTok") as "[Own $]". iDestruct ("PrePc" with "PTok'") as "Pc".
    iMod ("Close'" with "[Mt Own Pc]") as "[? Tok]".
    { iModIntro. iExists _. iFrame "Pc Time". iExists vl. iFrame. }
    iMod ("PreTok" with "Tok") as "$". iModIntro. iExists d, l, ξ.
    iSplit; [iPureIntro; lia|]. do 2 (iSplit; [done|]). iFrame.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #In #?". iDestruct 1 as (d l ξ ->?) "[?[#Bor Shr]]".
    iDestruct 1 as "[Tok Tok']". iIntros "!>!>".
    iDestruct (ty_shr_proph with "LFT In [] Shr Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. } iModIntro.
    iApply (step_fupdN_wand with "Upd"). iNext. iMod 1 as (ξs q' ?) "[PTok Close]".
    iMod (lft_incl_acc with "In Tok'") as (?) "[Tok PreTok]"; [done|].
    iMod (frac_bor_acc with "LFT Bor Tok") as (?) "[>PTok' Close']"; [done|].
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "PTok PTok'") as (q) "[PTok PrePToks]". iModIntro.
    iExists (ξs ++ [ξ]), q. iSplit; [iPureIntro; by apply proph_dep_pair|].
    iFrame "PTok". iIntros "PTok". iDestruct ("PrePToks" with "PTok") as "[PTok PTok']".
    iMod ("Close" with "PTok") as "[? $]". iMod ("Close'" with "PTok'") as "Tok".
    iMod ("PreTok" with "Tok") as "$". iModIntro. iExists d, l, ξ.
    by do 4 (iSplit; [done|]).
  Qed.

  Global Instance uniq_type_contractive {A} κ : TypeContractive (@uniq_bor A κ).
  Proof. split.
    - apply (type_lft_morphism_add _ κ [κ] [])=> ?; [by iApply lft_equiv_refl|].
      by rewrite elctx_interp_app elctx_interp_ty_outlives_E /elctx_interp
        /= left_id right_id.
    - done.
    - move=> */=. do 17 (f_contractive || f_equiv). by simpl in *.
    - move=> */=. do 11 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance uniq_ne {A} κ : NonExpansive (@uniq_bor A κ).
  Proof. solve_ne_type. Qed.

End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uniq_send {A} κ (ty: _ A) : Send ty → Send (&uniq{κ} ty).
  Proof.
    move=> Send ?*/=. do 10 f_equiv. iIntros "?". iApply bor_iff; last done.
    iApply bi.equiv_iff. do 6 f_equiv. by iSplit; iIntros "?"; iApply Send.
  Qed.

  Global Instance uniq_sync {A} κ (ty: _ A) : Sync ty → Sync (&uniq{κ} ty).
  Proof. move=> Sync ?*/=. do 11 f_equiv. iApply Sync. Qed.

  Lemma uniq_subtype {A} E L κ κ' (ty ty': _ A) :
    lctx_lft_incl E L κ' κ → eqtype E L id id ty ty' →
    subtype E L id (&uniq{κ} ty) (&uniq{κ'} ty').
  Proof.
    move=> In /eqtype_id_unfold Eqt. iIntros (?) "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In". iIntros "!> #E".
    iSplit; [done|]. iDestruct ("Eqt" with "E") as (?) "[[??] [#EqOwn #EqShr]]".
    iSpecialize ("In" with "E"). iSplit; [by iApply lft_intersect_mono|].
    iSplit; iModIntro.
    - iIntros "*". iDestruct 1 as (d' l' ξ ?->?) "[Vo Bor]". iExists d', l', ξ.
      do 3 (iSplit; [done|]). iFrame "Vo". iApply (bor_shorten with "In").
      iApply bor_iff; [|done]. iIntros "!>!>".
      iSplit; iDestruct 1 as (vπd) "[Own Misc]"; iExists vπd; iFrame "Misc";
      iDestruct "Own" as (vl) "[Mt Own]"; iExists vl; iFrame "Mt"; by iApply "EqOwn".
    - iIntros "*". iDestruct 1 as (d' l' ξ ??) "[?[??]]". iExists d', l', ξ.
      do 4 (iSplit; [done|]). by iApply "EqShr".
  Qed.
  Lemma uniq_eqtype {A} E L κ κ' (ty ty': _ A) :
    lctx_lft_eq E L κ κ' → eqtype E L id id ty ty' →
    eqtype E L id id (&uniq{κ} ty) (&uniq{κ} ty').
  Proof. move=> [??] [??]. by split; apply uniq_subtype. Qed.

(*
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
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, uniq_subtype.
  Qed.

  Lemma read_uniq E L κ ty :
    Copy ty → lctx_lft_alive E L κ → ⊢ typed_read E L (&uniq{κ}ty) ty (&uniq{κ}ty).
  Proof.
    rewrite typed_read_eq. iIntros (Hcopy Halive) "!>".
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
    rewrite typed_write_eq. iIntros (Halive) "!>".
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
*)
End typing.

Global Hint Resolve uniq_subtype uniq_eqtype (* write_uniq read_uniq *) : lrust_typing.
(*
Global Hint Resolve tctx_extract_hasty_reborrow | 10 : lrust_typing.
*)
