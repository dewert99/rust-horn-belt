From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_bor.
  Context `{!typeG Σ}.

  Definition prval_to_inh' {𝔄} (vπ: proph (𝔄 * 𝔄))
    : inh_syn_type 𝔄 := prval_to_inh (fst ∘ vπ).

  Program Definition uniq_bor {𝔄} (κ: lft) (ty: type 𝔄) : type (𝔄 * 𝔄) := {|
    ty_size := 1;  ty_lfts := κ :: ty.(ty_lfts);  ty_E := ty.(ty_E) ++ ty_outlv_E ty κ;
    ty_own vπ d tid vl := κ ⊑ ty.(ty_lft) ∗ [loc[l] := vl] ∃d' i,
      let ξ := PrVar (𝔄 ↾ prval_to_inh' vπ) i in
      ⌜S d' ≤ d ∧ snd ∘ vπ = (.$ ξ)⌝ ∗ .VO[ξ] (fst ∘ vπ) d' ∗
      &{κ} (∃vπ' d', l ↦∗: ty.(ty_own) vπ' d' tid ∗ ⧖(S d') ∗ .PC[ξ] vπ' d');
    ty_shr vπ d κ' tid l := [S d' := d] ∃(l': loc) ξ, ⌜snd ∘ vπ ./ [ξ]⌝ ∗
      &frac{κ'}(λ q', l ↦{q'} #l') ∗ &frac{κ'} (λ q, q:[ξ]) ∗
      ▷ ty.(ty_shr) (fst ∘ vπ) d' κ' tid l';
  |}%I.
  Next Obligation. move=>/= *. rewrite by_just_loc_ex. by iIntros "[_ [%[->?]]]".  Qed.
  Next Obligation. move=>/= > H. by setoid_rewrite H. Qed.
  Next Obligation.
    move=> ???[|?][|?]*/=; try (by iIntros); [lia|]. do 8 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??????[|?]*; [by iIntros|]. iIntros "#In (%l & %ξ &%&?&?&?)".
    iExists l, ξ. iSplit; [done|]. do 2 (iSplit; [by iApply frac_bor_shorten|]).
    by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> 𝔄 ??? vπ *. have ?: Inhabited 𝔄 := populate (fst (vπ inhabitant)).
    iIntros "#LFT #? Bor κ'". iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorMt Bor]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    rewrite by_just_loc_ex. iMod (bor_exists with "LFT Bor") as (l) "Bor"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ'") as "(>->& Bor & κ')"; [done|].
    iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_exists with "LFT Bor") as (i) "Bor"; [done|].
    set ξ := PrVar (𝔄 ↾ prval_to_inh' vπ) i.
    iMod (bor_sep_persistent with "LFT Bor κ'") as
    "(>%H & Bor & κ')"; [done|]. move: H=> [/succ_le [d[->Le]]->]/=.
    iMod (bor_sep with "LFT Bor") as "[BorVo Bor]"; [done|].
    iMod (bor_unnest with "LFT Bor") as "Bor"; [done|]. iIntros "!>!>!>".
    iMod (bor_shorten with "[] Bor") as "Bor".
    { iApply lft_incl_glb; [|iApply lft_incl_refl].
      iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    do 2 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_sep with "LFT Bor") as "[BorOwn Bor]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[_ BorPc]"; [done|].
    iMod (bor_combine with "LFT BorVo BorPc") as "Bor"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ'") as "[[Vo Pc] ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (->->) "[Vo Pc]".
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod ("ToBor" with "[Vo ToPc] ξ") as "[Borξ κ']".
    { iIntros "!> >ξ !>!>". iFrame "Vo". by iApply "ToPc". }
    iMod (ty_share with "LFT [] BorOwn κ'") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iApply step_fupdN_nmono; [by apply Le|]. iApply (step_fupdN_wand with "Upd").
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT BorMt") as "BorMt"; [done|].
    iMod (bor_fracture (λ q, q:[_])%I with "LFT Borξ") as "Borξ"; [done|].
    iIntros "!> >[?$] !>". iExists l, ξ. iFrame "BorMt Borξ".
    iSplit; [iPureIntro; apply proph_dep_one|]. iApply ty_shr_depth_mono; by [|lia].
  Qed.
  Next Obligation.
    move=> 𝔄 ??? vπ *. iIntros "#LFT #?". setoid_rewrite by_just_loc_ex at 1.
    iIntros "[In (%&->& Big)]". iDestruct "Big" as (d i [Le Eq]) "[Vo Bor]".
    set ξ := PrVar (𝔄 ↾ prval_to_inh' vπ) i. move: Le=> /succ_le [?[->Le]].
    iIntros "[κ1 κ1']". iMod (lft_incl_acc with "[] κ1") as (?) "[κ1 Toκ1]";
    first done. { iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    iMod (bor_acc with "LFT Bor κ1") as "[Big ToBor]"; [done|]. iIntros "!>!>!>".
    iDestruct "Big" as (??) "((%vl & ↦ & ty) & #⧖ & Pc)".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod (ty_own_proph with "LFT [] ty κ1'") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. } iModIntro.
    iApply step_fupdN_nmono; [by apply Le|]. iApply (step_fupdN_wand with "Upd").
    iMod 1 as (ζl ??) "[ζl Toty]". iModIntro. rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζl ξ") as (q) "[ζlξ Toζlξ]".
    iExists (ζl ++ [ξ]), q. iSplit.
    { iPureIntro. apply proph_dep_pair; [done|]. rewrite Eq. apply proph_dep_one. }
    iFrame "ζlξ". iIntros "ζlξ". iDestruct ("Toζlξ" with "ζlξ") as "[ζl ξ]".
    iMod ("Toty" with "ζl") as "[ty $]". iDestruct ("ToPc" with "ξ") as "Pc".
    iMod ("ToBor" with "[↦ ty Pc]") as "[Bor κ1]".
    { iModIntro. iExists (fst ∘ vπ), d. iFrame "Pc ⧖". iExists vl. iFrame. }
    iMod ("Toκ1" with "κ1") as "$". iModIntro. iFrame "In". iExists d, i.
    iFrame "Vo Bor". iPureIntro. split; [lia|done].
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|].
    iIntros "#LFT #In #? (%l & %ξ &%&?& #Bor & ty) [κ' κ'+] !>!>".
    iDestruct (ty_shr_proph with "LFT In [] ty κ'") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. } iModIntro.
    iApply (step_fupdN_wand with "Upd"). iNext. iMod 1 as (ζl q' ?) "[ζl Toty]".
    iMod (lft_incl_acc with "In κ'+") as (?) "[κ1 Toκ'+]"; [done|].
    iMod (frac_bor_acc with "LFT Bor κ1") as (?) "[>ξ Toκ1]"; [done|].
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζl [$ξ]") as (q) "[ζlξ Toζlξ]". iModIntro.
    iExists (ζl ++ [ξ]), q. iSplit; [iPureIntro; by apply proph_dep_pair|].
    iFrame "ζlξ". iIntros "ζlξ". iDestruct ("Toζlξ" with "ζlξ") as "[ζl ξ]".
    iMod ("Toty" with "ζl") as "[?$]". iMod ("Toκ1" with "ξ") as "κ1".
    iMod ("Toκ'+" with "κ1") as "$". iModIntro. iExists l, ξ. by do 3 (iSplit; [done|]).
  Qed.

  Global Instance uniq_bor_ne {𝔄} κ : NonExpansive (@uniq_bor 𝔄 κ).
  Proof. solve_ne_type. Qed.

End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uniq_type_contr {𝔄} κ : TypeContractive (@uniq_bor _ _ 𝔄 κ).
  Proof. split; [by apply (type_lft_morph_add_one κ)|done| |].
    - move=> > ? Hl * /=. f_equiv.
      + apply equiv_dist. iDestruct Hl as "#[??]".
        iSplit; iIntros "#H"; (iApply lft_incl_trans; [iApply "H"|done]).
      + do 17 (f_contractive || f_equiv). by simpl in *.
    - move=> */=. do 10 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance uniq_send {𝔄} κ (ty: _ 𝔄) : Send ty → Send (&uniq{κ} ty).
  Proof. move=> >/=. by do 18 f_equiv. Qed.

  Global Instance uniq_sync {𝔄} κ (ty: _ 𝔄) : Sync ty → Sync (&uniq{κ} ty).
  Proof. move=> >/=. by do 10 f_equiv. Qed.

  Global Instance uniq_leak {𝔄} κ (ty: _ 𝔄) :
    Leak (&uniq{κ} ty) [κ] (λ '(a, a'), a' = a).
  Proof.
    move=>/= ? vπ d ? vl ??. rewrite right_id. iIntros "#LFT PROPH [κ κ'] [In uniq]".
    case vl as [|[[]|][]]=>//. iDestruct "uniq" as (??[Le Eq]) "[Vo Bor]".
    move: Le=> /succ_le[?[->Le]]. have ?: Inhabited 𝔄 := populate (fst (vπ inhabitant)).
    iMod (bor_acc with "LFT Bor κ") as "[(%&%&(%& ↦ & ty)&⧖& Pc) ToBor]"; [solve_ndisj|].
    iIntros "/= !>!>!>". iMod (ty_own_proph with "LFT In ty κ'") as "Toξl";
    [solve_ndisj|]. iDestruct (uniq_agree with "Vo Pc") as %[<-->].
    iApply step_fupdN_nmono; [by apply Le|].
    iApply (step_fupdN_wand with "Toξl"). iIntros "!> >(%&%&%& ξl & Toty)".
    iMod (uniq_resolve with "PROPH Vo Pc ξl") as "(Obs & Pc & ξl)"; [solve_ndisj|done|].
    iMod ("Toty" with "ξl") as "[ty $]". iMod ("ToBor" with "[↦ ty ⧖ Pc]") as "[_ $]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. } iApply proph_obs_eq;
    [|done]=>/= π. move: (equal_f Eq π)=>/=. by case (vπ π)=>/= ??->.
  Qed.

  Lemma uniq_subtype {𝔄} E L κ κ' (ty ty': _ 𝔄) :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    subtype E L (&uniq{κ} ty) (&uniq{κ'} ty') id.
  Proof.
    move=> In /eqtype_id_unfold Eqt ?. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In". iIntros "!> #E".
    iSplit; [done|]. iDestruct ("Eqt" with "E") as (?) "[[??][#EqOwn #EqShr]]".
    iSpecialize ("In" with "E"). iSplit; [by iApply lft_intersect_mono|].
    iSplit; iModIntro=>/=.
    - iIntros "*". rewrite {1}by_just_loc_ex. iIntros "[#? (%&->& Big)]".
      iSplitR. { iApply lft_incl_trans; [|done]. by iApply lft_incl_trans. }
      iDestruct "Big" as (d' ξ ?) "[Vo ?]". iExists d', ξ. iSplit; [done|]. iFrame "Vo".
      iApply (bor_shorten with "In"). iApply bor_iff; [|done]. iIntros "!>!>".
      iSplit; iDestruct 1 as (vπ' d'') "[(%vl & ↦ & ?) Misc]"; iExists vπ', d'';
      iFrame "Misc"; iExists vl; iFrame "↦"; by iApply "EqOwn".
    - iIntros (?[|?]???); [by iIntros|]. iDestruct 1 as (l' ξ ?) "(?&?&?)".
      iExists l', ξ. do 3 (iSplit; [done|]). by iApply "EqShr".
  Qed.
  Lemma uniq_eqtype {𝔄} E L κ κ' (ty ty': _ 𝔄) :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' id id →
    eqtype E L (&uniq{κ} ty) (&uniq{κ} ty') id id.
  Proof. move=> [??][??]. by split; apply uniq_subtype. Qed.

  Lemma tctx_reborrow_uniq {𝔄} E L p (ty : type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L +[p ◁ &uniq{κ}ty] +[p ◁ &uniq{κ'}ty; p ◁{κ'} &uniq{κ}ty] (λ post '-[v], ∀ v', post -[(v.1, v'); (v', v.2)]).
  Proof.
    iIntros (Hκκ' tid ? [vπ []] ?) "#LFT #PROPH #UNIQ HE HL [H _] Hproph". iDestruct (Hκκ' with "HL HE") as "#Hκκ'".
    iFrame.
    iDestruct "H" as ([[]|] [|depth1] ) "(%Hp & #Hdepth1 & [#Hκ Hb])"; try done;
    iDestruct "Hb" as (depth2 ξi [? ?]) "[ξVo Hb]"; try lia.
    set ξ := PrVar _ ξi.
    iMod (rebor with "LFT Hκκ' Hb") as "[Hb Hext]"; try done.
    iMod (uniq_intro (fst ∘ vπ) with "PROPH UNIQ") as (ζi) "(ζVo & ζPc)"; [done|].
    set ζ := PrVar _ ζi.
    iMod (bor_create _ κ' (∃ vπ' d', .VO[ξ] vπ' d' ∗ ⧖(S d') ∗ .PC[ζ] vπ' d')%I
            with "LFT [ξVo ζPc]") as "[ζb ζb†]"; [done| |].
    { iExists _, _. iFrame. iApply persist_time_rcpt_mono; done. }
    iMod (bor_combine with "LFT ζb Hb") as "Hb"; [done|].
    iExists -[λ π, ((vπ π).1, π ζ); λ π, (π ζ, (vπ π).2)].
    iSplitR "Hproph"; last first.
    { iApply (proph_obs_impl with "Hproph") => /= π X. apply X. }
    iMod (bor_acc_atomic_cons with "LFT Hb") as "[[[Q P] Hclose]|[#H† Hclose]]";
      [done| |]; last first.
    { iMod "Hclose" as "_".
      iMod ("Hext" with "H†"). iMod ("ζb†" with "H†") as (??) "(> ξVo & >#Hd' & ζPc)".
      iMod (uniq_strip_later with "ζVo ζPc") as "(<- & -> & ζVo & ζPc)".
      iSplitL "ζVo".
      - iExists _, _. iFrame (Hp) "Hd'". iSplitR.
        { by iApply lft_incl_trans. }
        iExists _, ζi. iFrame. iSplitR; [done|].
        by iApply bor_fake.
      - rewrite right_id. iExists _.
        iIntros "{$%} !> _".
        iExists _, (S d'). iSplitL "ζPc"; [|iSplitR].
        + iModIntro; iNext.
          iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "X".
          iApply (proph_eqz_pair with "[X]"); [done|].
          iApply proph_eqz_eq.
        + iApply persist_time_rcpt_mono; done.
        + iFrame "Hκ". iExists _, _. by iFrame.
    }
    iMod (bi.later_exist_except_0 with "P") as (??) "(Hown & >#Hd2 & ξPc)".
    iMod (bi.later_exist_except_0 with "Q") as (??) "(ξVo & _ & ζPc)".
    iMod (uniq_strip_later with "ξVo ξPc") as "(-> & -> & ξVo & ξPc)".
    iMod (uniq_strip_later with "ζVo ζPc") as "(<- & <- & ζVo & ζPc)".
    rewrite /= right_id.
    iMod ("Hclose" $! (∃ vπ' d', l ↦∗: ty_own ty vπ' d' tid ∗ ⧖(S d') ∗ .PC[ζ] vπ' d')%I
            with "[ξVo ξPc] [ζPc Hown]").
    { iIntros "!> H". iMod (bi.later_exist_except_0 with "H") as (??) "(Hown & >#? & ζPc)".
      iMod (uniq_update with "UNIQ ξVo ξPc") as "(ξVo & ξPc)"; [solve_ndisj|].
      iSplitL "ξVo ζPc"; iExists _, _; by iFrame.
    }
    { iExists _, _. by iFrame. }
    iModIntro. iSplitR "Hext ζb†".
    - iExists _, (S _). iFrame (Hp) "Hd2". iSplitR; [by iApply lft_incl_trans|].
      iExists _, _. by iFrame "∗%".
    - iExists _. iSplit; [done|]. iIntros "#H†".
      iMod ("Hext" with "H†") as "Hb". iMod ("ζb†" with "H†") as "ζbor".
      iMod (bi.later_exist_except_0 with "ζbor") as (wπ depth2') "(> ξVo & >#Hdepth2' & ζPc)".
      iExists _, (S depth2').
      iFrame "Hdepth2' Hκ". iSplitL "ζPc".
      { iModIntro; iNext.
        iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "X".
        iApply (proph_eqz_pair _ (λ π, (wπ π, (vπ π).2)) with "[X]"); [|iApply proph_eqz_eq].
        rewrite /compose /=. by change (λ x, wπ x) with wπ.
      }
      iExists depth2', ξi.
      rewrite (proof_irrel (prval_to_inh' _) (prval_to_inh' vπ)).
      by iFrame.
  Qed.

  Lemma tctx_extract_hasty_reborrow {𝔄 As} E L p (ty : type 𝔄) (ty' : type 𝔄) κ κ' (T : tctx As):
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    tctx_extract_elt E L (p ◁ &uniq{κ'}ty) ((p ◁ &uniq{κ}ty')+::T)
                       ((p ◁{κ'} &uniq{κ}ty')+::T) (@trans_upper [_ * _]%ST [𝔄 * 𝔄; (_ * _)]%ST _ (λ post '-[v], ∀ v', post -[(id v.1, id v'); (v', v.2)])).
  Proof.
    intros. eapply tctx_incl_impl.
    - eapply (tctx_incl_frame_r +[_] +[_;_]), tctx_incl_trans.
      + by eapply tctx_reborrow_uniq.
      + by eapply subtype_tctx_incl, uniq_subtype, eqtype_symm.
    - done.
  Qed.

  Lemma read_uniq {𝔄} E L κ (ty: _ 𝔄):
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&uniq{κ} ty) ty (&uniq{κ} ty) fst id.
  Proof.
    iIntros (? Alv ?[|?][[]|]??) "#LFT E Na L [In uniq] //".
    { iDestruct "uniq" as (??[??]) "_". lia. }
    have ?: Inhabited 𝔄 := populate (fst (vπ inhabitant)).
    iDestruct "uniq" as (??[??]) "[Vo Bor]".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as
      "[(%&%&(%& >↦ & #ty)& #>⧖ & Pc) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iDestruct (ty_size_eq with "ty") as "#>%". iIntros "!>".
    iExists _, _, _. iSplit; [done|]. iFrame "↦ Na". iSplitR.
    { iApply ty_own_depth_mono; [|done]. lia. }
    iIntros "↦". iMod ("ToBor" with "[↦ Pc]") as "[? κ]".
    { iNext. iExists _, _. iFrame "Pc ⧖". iExists _. by iFrame. }
    iMod ("ToL" with "κ") as "$". iModIntro. iFrame "In". iExists _, _. by iFrame.
  Qed.

  Lemma write_uniq {𝔄} E L κ (ty: _ 𝔄):
    lctx_lft_alive E L κ →
    typed_write E L (&uniq{κ} ty) ty (&uniq{κ} ty) ty fst (λ v w, (w, v.2)).
  Proof.
    move=> Alv. split; [done|]. iIntros (vπ d[[]|]??) "#LFT #UNIQ E L [In uniq] //".
    case d=> [|?]. { iDestruct "uniq" as (??[??]) "_". lia. }
    have ?: Inhabited 𝔄 := populate (fst (vπ inhabitant)).
    iDestruct "uniq" as (??[??]) "[Vo Bor]".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as "[(%&%&(%& >↦ & ty)&_& Pc) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]". iModIntro.
    iExists _. iSplit; [done|]. iSplitL "↦ ty".
    { iNext. iExists _. iFrame "↦". iApply ty_own_depth_mono; [|done]. lia. }
    iIntros (wπ ?) "(% & >↦ & ty) #⧖ /=".
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[↦ Pc ty]") as "[Bor κ]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. }
    iMod ("ToL" with "κ") as "$". iModIntro. iFrame "In". iExists _, _.
    rewrite (proof_irrel (prval_to_inh' _) (prval_to_inh' vπ)). by iFrame.
  Qed.

End typing.

Global Hint Resolve uniq_subtype uniq_eqtype write_uniq read_uniq : lrust_typing.
Global Hint Resolve tctx_extract_hasty_reborrow | 10 : lrust_typing.
