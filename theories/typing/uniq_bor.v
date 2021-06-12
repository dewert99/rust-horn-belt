From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs mod_ty.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_bor.
  Context `{!typeG Σ}.

  Definition prval_to_inh' {𝔄} (vπ: proph (𝔄 * 𝔄))
    : inh_syn_type 𝔄 := prval_to_inh (fst ∘ vπ).

  Program Definition uniq_bor {𝔄} (κ: lft) (ty: type 𝔄) : type (𝔄 * 𝔄) := {|
    ty_size := 1;  ty_lfts := κ :: ty.(ty_lfts);  ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    ty_own vπ d tid vl := κ ⊑ ty.(ty_lft) ∗ [loc[l] := vl] ∃d' i,
      let ξ := PrVar (𝔄 ↾ prval_to_inh' vπ) i in
      ⌜(S d' ≤ d)%nat ∧ snd ∘ vπ = (.$ ξ)⌝ ∗ .VO[ξ] (fst ∘ vπ) d' ∗
      &{κ} (∃vπ' d', ⧖(S d') ∗ .PC[ξ] vπ' d' ∗ l ↦∗: ty.(ty_own) vπ' d' tid);
    ty_shr vπ d κ' tid l := [S(d') := d] ∃(l': loc) ξ, ⌜snd ∘ vπ ./ [ξ]⌝ ∗
      &frac{κ'} (λ q', l ↦{q'} #l') ∗ &frac{κ'} (λ q, q:[ξ]) ∗
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
    move=> 𝔄 ??? vπ *. have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iIntros "#LFT #? Bor κ'". iMod (bor_exists with "LFT Bor") as (vl) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
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
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (bor_sep with "LFT Bor") as "[BorPc Borty]"; [done|].
    iMod (bor_combine with "LFT BorVo BorPc") as "Bor"; [done|].
    iMod (bor_acc_cons with "LFT Bor κ'") as "[[Vo Pc] ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (->->) "[Vo Pc]".
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod ("ToBor" with "[Vo ToPc] ξ") as "[Borξ κ']".
    { iIntros "!> >ξ !>!>". iFrame "Vo". by iApply "ToPc". }
    iMod (ty_share with "LFT [] Borty κ'") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iApply step_fupdN_nmono; [by apply Le|]. iApply (step_fupdN_wand with "Upd").
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (bor_fracture (λ q, q:[_])%I with "LFT Borξ") as "Borξ"; [done|].
    iIntros "!> >[?$] !>". iExists l, ξ. iFrame "Bor↦ Borξ".
    iSplit; [iPureIntro; apply proph_dep_one|]. iApply ty_shr_depth_mono; by [|lia].
  Qed.
  Next Obligation.
    move=> 𝔄 ??? vπ *. iIntros "#LFT #?". setoid_rewrite by_just_loc_ex at 1.
    iIntros "[In (%&->& Big)]". iDestruct "Big" as (d i [Le Eq]) "[Vo Bor]".
    set ξ := PrVar (𝔄 ↾ prval_to_inh' vπ) i. move: Le=> /succ_le [?[->Le]].
    iIntros "[κ1 κ1₊]".
    iMod (lft_incl_acc with "[] κ1") as (?) "[κ1 Toκ1]"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    iMod (bor_acc with "LFT Bor κ1") as "[Big ToBor]"; [done|]. iIntros "!>!>!>".
    iDestruct "Big" as (??) "(#⧖ & Pc & %vl & ↦ & ty)".
    iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & ξ & ToPc)".
    iMod (ty_own_proph with "LFT [] ty κ1₊") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iModIntro. iApply step_fupdN_nmono; [by apply Le|].
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ζl ??) "[ζl Toty]". iModIntro.
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζl ξ") as (q) "[ζlξ Toζlξ]".
    iExists (ζl ++ [ξ]), q. iSplit.
    { iPureIntro. apply proph_dep_pair; [done|]. rewrite Eq. apply proph_dep_one. }
    iIntros "{$ζlξ}ζlξ". iDestruct ("Toζlξ" with "ζlξ") as "[ζl ξ]".
    iMod ("Toty" with "ζl") as "[ty $]". iDestruct ("ToPc" with "ξ") as "Pc".
    iMod ("ToBor" with "[Pc ↦ ty]") as "[Bor κ1]".
    { iModIntro. iExists (fst ∘ vπ), d. iFrame "Pc ⧖". iExists vl. iFrame. }
    iMod ("Toκ1" with "κ1") as "$". iModIntro. iFrame "In". iExists d, i.
    iFrame "Vo Bor". iPureIntro. split; [lia|done].
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|].
    iIntros "#LFT #In #? (%l & %ξ &%&?& #Bor & ty) [κ' κ'₊] !>!>".
    iDestruct (ty_shr_proph with "LFT In [] ty κ'") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iModIntro. iApply (step_fupdN_wand with "Upd"). iNext.
    iMod 1 as (ζl q' ?) "[ζl Toty]".
    iMod (lft_incl_acc with "In κ'₊") as (?) "[κ1 Toκ'₊]"; [done|].
    iMod (frac_bor_acc with "LFT Bor κ1") as (?) "[>ξ Toκ1]"; [done|].
    rewrite proph_tok_singleton.
    iDestruct (proph_tok_combine with "ζl [$ξ]") as (q) "[ζlξ Toζlξ]". iModIntro.
    iExists (ζl ++ [ξ]), q. iSplit; [iPureIntro; by apply proph_dep_pair|].
    iIntros "{$ζlξ}ζlξ". iDestruct ("Toζlξ" with "ζlξ") as "[ζl ξ]".
    iMod ("Toty" with "ζl") as "[?$]". iMod ("Toκ1" with "ξ") as "κ1".
    iMod ("Toκ'₊" with "κ1") as "$". iModIntro. iExists l, ξ. by do 3 (iSplit; [done|]).
  Qed.

  Global Instance uniq_bor_ne {𝔄} κ : NonExpansive (@uniq_bor 𝔄 κ).
  Proof. solve_ne_type. Qed.
End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uniq_type_contractive {𝔄} κ : TypeContractive (uniq_bor (𝔄:=𝔄) κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| |].
    - move=> > ? Hl * /=. f_equiv.
      + apply equiv_dist. iDestruct Hl as "#[??]".
        iSplit; iIntros "#H"; (iApply lft_incl_trans; [iApply "H"|done]).
      + do 18 (f_contractive || f_equiv). by simpl in *.
    - move=> */=. do 10 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance uniq_send {𝔄} κ (ty: type 𝔄) : Send ty → Send (&uniq{κ} ty).
  Proof. move=> >/=. by do 19 f_equiv. Qed.

  Global Instance uniq_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (&uniq{κ} ty).
  Proof. move=> >/=. by do 10 f_equiv. Qed.

  Global Instance uniq_just_loc {𝔄} κ (ty: type 𝔄) : JustLoc (&uniq{κ} ty).
  Proof. iIntros (???[|[[]|][]]) "[_ ?] //". by iExists _. Qed.

  Lemma uniq_leak {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ → leak E L (&uniq{κ} ty) (λ '(a, a'), a' = a).
  Proof.
    move=>/= Alv ?? vπ d ? vl ?. iIntros "#LFT PROPH E L [In uniq]".
    case vl as [|[[]|][]]=>//. iDestruct "uniq" as (??[Le Eq]) "[Vo Bor]".
    move: Le=> /succ_le[?[->Le]]/=.
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iMod (Alv with "E L") as (?) "[[κ κ₊] ToL]"; [solve_ndisj|].
    iMod (bor_acc with "LFT Bor κ") as "[(%&%& ⧖ & Pc &%& ↦ & ty) ToBor]";
      [solve_ndisj|]. iIntros "!>!>!>".
    iMod (ty_own_proph with "LFT In ty κ₊") as "Toξl"; [solve_ndisj|].
    iDestruct (uniq_agree with "Vo Pc") as %[<-->].
    iApply step_fupdN_nmono; [by apply Le|].
    iApply (step_fupdN_wand with "Toξl"). iIntros "!> >(%&%&%& ξl & Toty)".
    iMod (uniq_resolve with "PROPH Vo Pc ξl") as "(Obs & Pc & ξl)"; [solve_ndisj|done|].
    iMod ("Toty" with "ξl") as "[ty κ₊]". iMod ("ToBor" with "[⧖ Pc ↦ ty]") as "[_ κ]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. }
    iSplitL "Obs"; [|iApply "ToL"; by iFrame]. iApply proph_obs_eq; [|done]=>/= π.
    move: (equal_f Eq π)=>/=. by case (vπ π)=>/= ??->.
  Qed.

  Lemma uniq_real {𝔄 𝔅} E L κ ty (f: 𝔄 → 𝔅) :
    lctx_lft_alive E L κ → real E L ty f →
    real E L (&uniq{κ} ty) (f ∘ fst).
  Proof.
    move=> Alv [Rlo Rls]. split.
    - iIntros (????? [|[[]|][]] ?) "#LFT #E [L L₊] [$ uniq] //".
      iDestruct "uniq" as (d' ?[Le Eq]) "[Vo Bor]".
      move: Le=> /succ_le[?[-> Le]]/=.
      iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
      iMod (bor_acc with "LFT Bor κ") as "[big ToBor]"; [done|].
      iIntros "!>!>!>". iDestruct "big" as (??) "(⧖' & Pc &%& ↦ & ty)".
      iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
      iMod (Rlo with "LFT E L₊ ty") as "Upd"; [done|].
      iApply step_fupdN_nmono; [by apply Le|]. iApply (step_fupdN_wand with "Upd").
      iIntros "!> >($&$& ty)". iMod ("ToBor" with "[⧖' Pc ↦ ty]") as "[Bor κ]".
      { iNext. iExists _, _. iFrame "⧖' Pc". iExists _. iFrame. }
      iMod ("ToL" with "κ") as "$". iModIntro. iExists d', _. iFrame "Vo Bor".
      iPureIntro. split; [lia|done].
    - iIntros (???[|]????) "LFT E L uniq //".
      iDestruct "uniq" as (???) "(Bor & Bor' & ty)". iIntros "!>!>!>/=".
      iMod (Rls with "LFT E L ty") as "Upd"; [done|]. iIntros "!>!>".
      iApply (step_fupdN_wand with "Upd"). iIntros ">($&$&?)". iExists _, _. by iFrame.
  Qed.

  Lemma uniq_subtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
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
      iSplit; iDestruct 1 as (vπ' d'') "(⧖ & Pc &%vl & ↦ & ?)"; iExists vπ', d'';
      iFrame "⧖ Pc"; iExists vl; iFrame "↦"; by iApply "EqOwn".
    - iIntros (?[|?]???); [by iIntros|]. iDestruct 1 as (l' ξ ?) "(?&?&?)".
      iExists l', ξ. do 3 (iSplit; [done|]). by iApply "EqShr".
  Qed.
  Lemma uniq_eqtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' id id →
    eqtype E L (&uniq{κ} ty) (&uniq{κ} ty') id id.
  Proof. move=> [??][??]. by split; apply uniq_subtype. Qed.

  Lemma write_uniq {𝔄} E L κ (ty: type 𝔄):
    lctx_lft_alive E L κ →
    typed_write E L (&uniq{κ} ty) ty (&uniq{κ} ty) ty fst (λ v w, (w, v.2)).
  Proof.
    move=> Alv. split; [done|]. iIntros (vπ d[[]|]??) "#LFT #UNIQ E L [In uniq] //".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iDestruct "uniq" as (??[Le ?]) "[Vo Bor]". move: Le=> /succ_le[?[->?]].
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as "[(%&%&_& Pc &%& >↦ & ty) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]". iModIntro.
    iExists _. iSplit; [done|]. iSplitL "↦ ty".
    { iNext. iExists _. iFrame "↦". iApply ty_own_depth_mono; [|done]. lia. }
    iIntros (wπ ?) "(% & >↦ & ty) #⧖ /=".
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[↦ Pc ty]") as "[Bor κ]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. }
    iMod ("ToL" with "κ") as "$". iFrame "In". iExists _, _.
    rewrite (proof_irrel (prval_to_inh' _) (prval_to_inh' vπ)). by iFrame.
  Qed.

  Lemma read_uniq {𝔄} E L κ (ty: type 𝔄):
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&uniq{κ} ty) ty (&uniq{κ} ty) fst id.
  Proof.
    iIntros (? Alv vπ ?[[]|]??) "#LFT E Na L [In uniq] //".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iDestruct "uniq" as (??[Le ?]) "[Vo Bor]". case d as [|]; [lia|].
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as
      "[(%&%& #>⧖ & Pc &%& >↦ & #ty) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iDestruct (ty_size_eq with "ty") as "#>%". iIntros "!>".
    iExists _, _, _. iSplit; [done|]. iFrame "↦ Na". iSplitR.
    { iApply ty_own_depth_mono; [|done]. lia. }
    iIntros "↦". iMod ("ToBor" with "[↦ Pc]") as "[? κ]".
    { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. by iFrame. }
    iMod ("ToL" with "κ") as "$". iFrame "In". iExists _, _. by iFrame.
  Qed.

  Lemma tctx_reborrow_uniq {𝔄} E L p (ty: type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L +[p ◁ &uniq{κ} ty] +[p ◁ &uniq{κ'} ty; p ◁{κ'} &uniq{κ} ty]
      (λ post '-[(a, a')], ∀a'': 𝔄, post -[(a, a''); (a'', a')]).
  Proof.
    intros κκ'. split; [intros ??? [[??][]]; by apply forall_proper|].
    iIntros (??[vπ[]]?) "#LFT #PROPH #UNIQ E L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iDestruct (κκ' with "L E") as "#κ⊑κ'". iFrame "L".
    iDestruct "p" as ([[]|]??) "[⧖ [#In uniq]]"=>//.
    iDestruct "uniq" as (? ξi [Le Eq]) "[ξVo ξBor]". set ξ := PrVar _ ξi.
    move: Le=> /succ_le[?[->?]].
    iMod (rebor with "LFT κ⊑κ' ξBor") as "[ξBor ToξBor]"; [done|].
    iMod (uniq_intro (fst ∘ vπ) with "PROPH UNIQ") as (ζi) "(ζVo & ζPc)"; [done|].
    set ζ := PrVar _ ζi.
    iMod (bor_create _ κ' (∃vπ' d', .VO[ξ] vπ' d' ∗ ⧖(S d') ∗ .PC[ζ] vπ' d')%I
      with "LFT [⧖ ξVo ζPc]") as "[ζBor ToζBig]"; [done| |].
    { iExists _, _. iFrame "ξVo ζPc". iApply persistent_time_receipt_mono; [|done]. lia. }
    iMod (bor_combine with "LFT ξBor ζBor") as "Bor"; [done|].
    iExists -[λ π, ((vπ π).1, π ζ); λ π, (π ζ, (vπ π).2)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs") => /= π. case (vπ π)=>/= ?? All. apply All. }
    iMod (bor_acc_atomic_cons with "LFT Bor") as
      "[[[ξBig ζBig] ToBor]|[#†κ' TolftN]]"; [done| |]; last first.
    { iMod "TolftN" as "_". iMod ("ToξBor" with "†κ'").
      iMod ("ToζBig" with "†κ'") as (??) "(>ξVo & >#⧖ & ζPc)".
      iMod (uniq_strip_later with "ζVo ζPc") as (<-<-) "[ζVo ζPc]". iSplitL "ζVo".
      - iExists _, _. iFrame "⧖". iSplitR; [done|].
        iSplitR; [by iApply lft_incl_trans|]. iExists _, ζi. iFrame "ζVo".
        iSplitR; [done|]. by iApply bor_fake.
      - iModIntro. iSplitL; [|done]. iExists _. iSplit; [done|]. iIntros "_!>".
        iExists _, _. iFrame "⧖". iSplitL "ζPc"; last first.
        { iFrame "In". iExists _, _. by iFrame. }
        iNext. iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
        iApply (proph_eqz_pair with "[Eqz]"); [done|iApply proph_eqz_refl]. }
    iDestruct "ξBig" as (??) "(>#⧖ & ξPc & ↦ty)".
    iDestruct "ζBig" as (??) "(>ξVo & _ & ζPc)".
    iMod (uniq_strip_later with "ξVo ξPc") as (<-<-) "[ξVo ξPc]".
    iMod (uniq_strip_later with "ζVo ζPc") as (<-<-) "[ζVo ζPc]".
    iMod ("ToBor" $! (∃ vπ' d', ⧖(S d') ∗ .PC[ζ] vπ' d' ∗
      l ↦∗: ty.(ty_own) vπ' d' tid)%I with "[ξVo ξPc] [ζPc ↦ty]") as "ζBor".
    { iIntros "!> (%&% & #? & ζPc & ↦ty)".
      iMod (uniq_update with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [solve_ndisj|].
      iSplitL "↦ty ξPc"; iExists _, _; by iFrame. }
    { iNext. iExists _, _. by iFrame. }
    iModIntro. iSplitL "ζVo ζBor"; [|iSplitL; [|done]].
    { iExists _, _. iSplit; [done|]. iFrame "⧖".
      iSplitR; [by iApply lft_incl_trans|]. iExists _, _. by iFrame. }
    iExists _. iSplit; [done|]. iIntros "#†κ'". iMod ("ToξBor" with "†κ'") as "ξBor".
    iMod ("ToζBig" with "†κ'") as (vπ' ?) "(>ξVo & >⧖' & ζPc)". iModIntro.
    iExists _, _. iFrame "⧖' In". iSplitL "ζPc".
    - iNext. iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
      iApply (proph_eqz_pair _ (pair ∘ vπ' ⊛ (snd ∘ vπ)) with "[Eqz]");
      [done|iApply proph_eqz_refl].
    - iExists _, _. rewrite (proof_irrel (prval_to_inh' _) (prval_to_inh' vπ)).
      by iFrame.
  Qed.

  Lemma tctx_extract_hasty_reborrow {𝔄 𝔅l} (ty ty': type 𝔄) κ κ' (T: tctx 𝔅l) E L p :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    tctx_extract_elt E L (p ◁ &uniq{κ'} ty) (p ◁ &uniq{κ} ty' +:: T)
      (p ◁{κ'} &uniq{κ} ty' +:: T) (λ post '((a, a') -:: bl),
        ∀a'': 𝔄, post ((a, a'') -:: (a'', a') -:: bl)).
  Proof.
    move=> ??. eapply tctx_incl_impl.
    - apply (tctx_incl_frame_r +[_] +[_;_]).
      eapply tctx_incl_trans; [by apply tctx_reborrow_uniq|].
      by apply subtype_tctx_incl, uniq_subtype, eqtype_symm.
    - by move=>/= ?[[??]?].
    - intros ??? [[??]?]. by apply forall_proper.
  Qed.

  Lemma tctx_uniq_mod_ty_out {𝔄 𝔅 ℭl} κ f ty (T: tctx ℭl) p E L
    `{!@Inj 𝔄 𝔅 (=) (=) f} : lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} (<{f}> ty) +:: T) (p ◁ &uniq{κ} ty +:: T)
      (λ post '((b, b') -:: cl), ∀a a', b = f a → b' = f a' → post ((a, a') -:: cl)).
  Proof.
    intros Alv. split.
    { intros ?? Eq  [[??]?]. do 2 apply forall_proper=>?. split=>???; apply Eq; auto. }
    iIntros (??[vπ ?]?) "LFT #PROPH UNIQ E L /=[p T] Obs".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    have ?: Inhabited 𝔅 := populate (vπ inhabitant).1.
    iDestruct "p" as ([[]|]? Ev) "[_ [In uniq]]"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[ξVo Bor]".
    move: Eq. (set ξ := PrVar _ ξi)=> Eq.
    iMod (bor_acc_cons with "LFT Bor κ") as
      "[(%&%& >#⧖ & ξPc &%& ↦ & ty') ToBor]"; [done|].
    iMod (uniq_strip_later with "ξVo ξPc") as (<-<-) "[ξVo ξPc]".
    iMod (bi.later_exist_except_0 with "ty'") as (aπ) "[>%Eq' ty]".
    have ?: Inhabited 𝔄 := populate (aπ inhabitant).
    iMod (uniq_intro aπ with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    set ζ := PrVar _ ζi. iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ζPc)".
    iMod (uniq_preresolve ξ [ζ] (λ π, f (π ζ)) with "PROPH ξVo ξPc [$ζ]") as
    "(Obs' & [ζ _] & ToξPc)"; [done|apply proph_dep_constr, proph_dep_one|done|].
    iCombine "Obs Obs'" as "Obs". iSpecialize ("ζPc" with "ζ").
    iExists ((λ π, (aπ π, π ζ)) -:: _). iFrame "T".
    iMod ("ToBor" with "[ToξPc] [↦ ty ζPc]") as "[Bor κ]"; last first.
    - iMod ("ToL" with "κ") as "$". iModIntro. iSplitR "Obs"; last first.
      { iApply proph_obs_impl; [|done]=>/= π.
        move: (equal_f Eq π) (equal_f Eq' π)=>/=.
        case (vπ π)=>/= ??->->[Imp ?]. by apply Imp. }
      iExists _, _. iSplit; [done|]. iFrame "⧖ In". iExists _, _. by iFrame.
    - iNext. iExists _, _. iFrame "⧖ ζPc". iExists _. iFrame.
    - iIntros "!> (%&%& ⧖' & ζPc &%& ↦ & ty) !>!>". iExists _, _. iFrame "⧖'".
      iSplitR "↦ ty".
      { iApply "ToξPc". iApply proph_eqz_constr. by iApply proph_ctrl_eqz. }
      iExists _. iFrame "↦". iExists _. by iFrame.
  Qed.

  Lemma tctx_uniq_eqtype {𝔄 𝔅 ℭl} κ (f: 𝔄 → 𝔅) g ty ty' (T: tctx ℭl) p E L :
    eqtype E L ty ty' f g → SemiIso g f → lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} ty +:: T) (p ◁ &uniq{κ} ty' +:: T)
      (λ post '((a, a') -:: cl), post ((f a, f a') -:: cl)).
  Proof.
    move=> [Sub Sub'] ? Alv. split; [by move=> ???[[??]?]|].
    iIntros (??[vπ ?]?) "LFT #PROPH UNIQ E L /=[p T] Obs".
    iDestruct (Sub with "L") as "#Sub". iDestruct (Sub' with "L") as "#Sub'".
    iDestruct ("Sub" with "E") as "#(_& _ & #InOwn &_)".
    iDestruct ("Sub'" with "E") as "#(_& ? & #InOwn' &_)".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    have ?: Inhabited 𝔅 := populate (f inhabitant).
    iDestruct "p" as ([[]|]? Ev) "[_ [#In uniq]]"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[ξVo Bor]". move: Eq. (set ξ := PrVar _ ξi)=> Eq.
    iMod (bor_acc_cons with "LFT Bor κ") as
      "[(%&%& >#⧖ & ξPc &%& ↦ & ty) ToBor]"; [done|].
    iMod (uniq_strip_later with "ξVo ξPc") as (<-<-) "[ξVo ξPc]".
    iMod (uniq_intro (f ∘ fst ∘ vπ) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    set ζ := PrVar _ ζi. iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ζPc)".
    iMod (uniq_preresolve ξ [ζ] (λ π, g (π ζ)) with "PROPH ξVo ξPc [$ζ]") as
    "(Obs' & [ζ _] & ToξPc)"; [done|apply proph_dep_constr, proph_dep_one|done|].
    iCombine "Obs Obs'" as "Obs". iSpecialize ("ζPc" with "ζ").
    iExists ((λ π, (f (vπ π).1, π ζ)) -:: _). iFrame "T".
    iMod ("ToBor" with "[ToξPc] [↦ ty ζPc]") as "[Bor κ]"; last first.
    - iMod ("ToL" with "κ") as "$". iModIntro. iSplitR "Obs"; last first.
      { iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq π)=>/=.
        case (vπ π)=>/= ??->[? /(f_equal f) +]. by rewrite semi_iso'=> <-. }
      iExists _, _. iSplit; [done|]. iFrame "⧖".
      iSplit; [by iApply lft_incl_trans|]. iExists _, _. by iFrame.
    - iNext. iExists _, _. iFrame "⧖ ζPc". iExists _. iFrame "↦". by iApply "InOwn".
    - iIntros "!> (%bπ &%& ⧖' & ζPc &%& ↦ & ty) !>!>". iExists _, _. iFrame "⧖'".
      iSplitR "↦ ty".
      { iApply "ToξPc". iApply proph_eqz_constr. by iApply proph_ctrl_eqz. }
      iExists _. iFrame "↦". by iApply "InOwn'".
  Qed.

  Lemma tctx_extract_uniq_eqtype {𝔄 𝔅 ℭl} κ (f: 𝔅 → 𝔄) g ty ty' (T: tctx ℭl) p E L :
    lctx_lft_alive E L κ → eqtype E L ty' ty f g → SemiIso g f →
    tctx_extract_elt E L (p ◁ &uniq{κ} ty) (p ◁ &uniq{κ} ty' +:: T) T
      (λ post '((b, b') -:: cl), post ((f b, f b') -:: cl)).
  Proof. move=> ???. by eapply tctx_uniq_eqtype. Qed.
End typing.

Global Hint Resolve uniq_leak uniq_real uniq_subtype uniq_eqtype : lrust_typing.

(* Registering [write_uniq]/[read_uniq] to [Hint Resolve]
  doesnt't help automation in some situations,
  but the following hints let automation work *)
Global Hint Extern 0 (typed_write _ _ (&uniq{_} _) _ _ _ _ _) =>
  simple apply write_uniq : lrust_typing.
Global Hint Extern 0 (typed_read _ _ (&uniq{_} _) _ _ _ _) =>
  simple apply read_uniq : lrust_typing.

Global Hint Resolve tctx_extract_hasty_reborrow | 10 : lrust_typing.
Global Hint Resolve tctx_extract_uniq_eqtype | 5 : lrust_typing.
