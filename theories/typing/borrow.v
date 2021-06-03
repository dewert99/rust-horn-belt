From lrust.typing Require Export uniq_bor shr_bor own.
From lrust.typing Require Import lft_contexts type_context programs.
Set Default Proof Using "Type".

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{!typeG Σ}.

  Lemma tctx_borrow {𝔄} E L p n (ty: type 𝔄) κ:
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_incl E L +[p ◁ own_ptr n ty] +[p ◁ &uniq{κ} ty; p ◁{κ} own_ptr n ty]
      (λ post '-[a], ∀a': 𝔄, post -[(a, a'); a']).
  Proof.
    intros Out. split; [intros ??? [?[]]; by apply forall_proper|].
    iIntros (??[vπ[]]?) "#LFT #PROPH #UNIQ #E L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iDestruct "p" as ([[]|][|]?) "[#⧖ own]"=>//.
    iDestruct "own" as "[(%& >↦ & ty) †]". iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#?".
    iMod (uniq_intro vπ with "PROPH UNIQ") as (i) "[Vo Pc]"; [done|].
    set ξ := PrVar (𝔄 ↾ prval_to_inh vπ) i.
    iMod (bor_create ⊤ κ (∃vπ' d, _ ↦∗: ty.(ty_own) vπ' d _ ∗
      ⧖(S d) ∗ .PC[ξ] vπ' d)%I with "LFT [↦ ty Pc]") as "[Bor Toty]"; [done| |].
    { iExists _, _. iFrame "Pc ⧖". iExists _. iFrame. }
    iExists -[pair ∘ vπ ⊛ (.$ ξ); (.$ ξ)]. rewrite/= right_id. iFrame "L". iModIntro.
    iSplitR "Obs"; [|by iApply proph_obs_impl; [|done]=>/=]. iSplitL "Vo Bor".
    - iExists _, _. do 2 (iSplit; [done|]). iFrame "#". iExists _, _. by iFrame.
    - iExists _. iSplit; [done|]. iIntros "†κ". iMod ("Toty" with "†κ") as
      (??) "(↦ty & >⧖' & Pc)". iExists _, _. iFrame "⧖' ↦ty †".
      iIntros "!>!>". iDestruct (proph_ctrl_eqz with "PROPH Pc") as "$".
  Qed.

  Lemma type_share_instr {𝔄} p κ (ty : type 𝔄) E L :
    lctx_lft_alive E L κ →
    typed_instr E L +[p ◁ &uniq{κ}ty] Share (const +[p ◁ &shr{κ} ty])
      (λ post '-[(a, a')], a' = a -> post -[a]).
  Proof.
    iIntros (Hκ ?? [vπ []]) "#LFT #TIME #PROPH #UNIQ #HE $ HL [Huniq _] Hproph".
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; [done..|].
    iDestruct "Huniq" as ([[]|] [|d]) "(% & _ & [#? H]) /="; try done;
      iDestruct "H" as (? ?) "([% %Eq] & Hvo & Huniq)"; try lia.
    move: Eq. set (ξ := PrVar _ i)=> Eq.
    iMod (bor_exists_tok with "LFT Huniq Htok1") as (vπ') "[Huniq Htok1]"; first solve_ndisj.
    iMod (bor_exists_tok with "LFT Huniq Htok1") as (d'') "[Huniq Htok1]"; first solve_ndisj.
    iMod (bor_acc with "LFT Huniq Htok1") as "[(Hown & > #Hd'' & Hpc) Hclose']"; first solve_ndisj.
    iDestruct "Hown" as (?) "[H↦ Hown]".
    iDestruct (ty.(ty_own_proph) with "LFT [$] Hown [$Htok2]") as "H"; first solve_ndisj.
    wp_bind Skip.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME Hd'' [H]"); [done..| |].
    { iApply step_fupdN_with_emp.
      iApply (fupd_step_fupdN_fupd_mask_mono with "H"); done. }
    wp_seq. iDestruct 1 as (ξl q') "/= (%Hdep & Hdt & Hclose'')".
    iDestruct (uniq_agree with "Hvo Hpc") as "%Hag"; inversion Hag; subst; clear Hag.
    iMod (uniq_resolve with "PROPH Hvo Hpc Hdt") as "(Hobs & Hpc & Hdt)"; [done|done| ].
    iMod ("Hclose''" with "Hdt") as "[Hown Htok]".
    iMod ("Hclose'" with "[H↦ Hown Hpc]") as "[Huniq Htok2]".
    { iFrame "#∗". iExists _. iFrame. }
    iMod (bor_sep with "LFT Huniq") as "[Huniq _]"; first solve_ndisj.
    iDestruct (ty.(ty_share) with "LFT [$] Huniq Htok") as "Hshr"; first solve_ndisj.
    iModIntro. wp_seq.
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME Hd'' [Hshr]");
      [done..| |].
    { iApply step_fupdN_with_emp.
      iApply (fupd_step_fupdN_fupd_mask_mono with "Hshr"); done. }
    wp_seq. iIntros "[Hshr Htok1]". iMod ("Hclose" with "[$Htok1 $Htok2]") as "$".
    iExists -[_]. rewrite /= right_id. iSplitR "Hproph Hobs".
    - iExists _, _. by iFrame "# % Hshr".
    - iCombine "Hobs Hproph" as "Hobs". iApply proph_obs_impl; [|done]=>/= π.
      move: (equal_f Eq π)=>/=. case (vπ π)=>/= ??<-[<-Imp]. by apply Imp.
  Qed.

  Lemma type_share {𝔄 𝔅l ℭl 𝔇} p κ (ty: type 𝔄) (T: tctx 𝔅l) (T' : tctx ℭl)
    trx tr e E L (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ &uniq{κ} ty] T T' trx →
    lctx_lft_alive E L κ →
    typed_body E L C (p ◁ &shr{κ} ty +:: T') e tr -∗
    typed_body E L C T (Share;; e) (trx ∘ (λ post '((a, a') -:: bl),
      a' = a → tr post (a -:: bl)))%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_seq; [by eapply type_share_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.

  Lemma tctx_extract_hasty_borrow {𝔄 𝔅 As} E L p n (ty : type 𝔄) (ty' : type 𝔅) κ (T : tctx As) f:
    subtype E L ty' ty f →
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_extract_elt E L (p ◁ &uniq{κ}ty) ((p ◁ own_ptr n ty')+::T)
                       ((p ◁{κ} own_ptr n ty)+::T) (λ post '(b -:: bs), ∀ (b' : 𝔄), post ((f b, b') -:: b' -:: bs)).
  Proof.
    intros. eapply tctx_incl_impl.
    - eapply tctx_incl_trans; [by eapply subtype_tctx_incl, own_subtype|].
      eapply (tctx_incl_frame_r +[_] +[_; _]). by eapply tctx_borrow.
    - done.
    - intros ??? [??]. by apply forall_proper.
  Qed.

  Lemma type_deref_uniq_own_instr {𝔄} κ p n (ty: type 𝔄) E L :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &uniq{κ} (own_ptr n ty)]
        (!p) (&uniq{κ} ty) (λ post '-[a], post a).
  Proof.
    iIntros (Alvκ ?? [vπ []]) "#LFT #TIME #PROPH #UNIQ #E $ L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iMod (Alvκ with "E L") as (q) "[κ ToL]"; [done|]. wp_apply (wp_hasty with "p").
    iIntros ([[]|] ??) "#⧖ [#? uniq]"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[ξVo Bor]". set (ξ := PrVar _ ξi).
    iMod (bor_acc_cons with "LFT Bor κ") as "[Body ToBor]"; [done|].
    iDestruct "Body" as (?[|]) "(↦own & _ & ξPc)";
      iDestruct "↦own" as ([|[[| |]|][]]) "[>↦ own]"; try iDestruct "own" as ">[]".
    iDestruct "own" as "[ty †]". rewrite heap_mapsto_vec_singleton -wp_fupd.
    iApply wp_cumulative_time_receipt; [done|done|]. wp_read. iIntros "⧗1".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<-->].
    iMod (uniq_intro (fst ∘ vπ) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    set (ζ := PrVar _ ζi).
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    rewrite proph_tok_singleton. iMod (uniq_preresolve with "PROPH ξVo ξPc ζ")
    as "(EqObs & ζ & ToξPc)"; [done|apply (proph_dep_one ζ)|].
    iCombine "EqObs Obs" as "Obs". iDestruct ("ToζPc" with "ζ") as "ζPc".
    iMod ("ToBor" $! (∃vπ' d', (∃vl', _ ↦∗ vl' ∗ ty_own ty vπ' d' _ vl') ∗
      ⧖(S d') ∗ .PC[ζ] vπ' d')%I with "[↦ ⧗1 † ToξPc] [ty ζPc]") as "[Bor κ]".
    - iIntros "!> (%&%& ? & >⧖' & ζPc)".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗1 ⧖'") as "⧖'"; [solve_ndisj|].
      iIntros "!>!>". iDestruct ("ToξPc" with "[ζPc]") as "ξPc".
      { iApply (proph_ctrl_eqz with "PROPH ζPc"). }
      iExists _, _. iFrame "⧖' ξPc".
      iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "↦". iFrame.
    - iExists _, _. iFrame "ty ζPc". iApply persistent_time_receipt_mono; [|done]. lia.
    - iExists -[λ π, ((vπ π).1, π ζ)]. iMod ("ToL" with "κ") as "$".
      rewrite right_id tctx_hasty_val'; [|done]. iModIntro. iSplitR "Obs".
      + iExists _. iFrame "⧖". iFrame "#". iExists _, _. iFrame "ζVo Bor". iPureIntro.
        split; by [lia|].
      + iApply proph_obs_impl; [|done]=> π[<-?].
        eapply eq_ind; [done|]. move: (equal_f Eq π)=>/=. by case (vπ π)=>/= ??->.
  Qed.

  Lemma type_deref_uniq_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_uniq_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.

  Lemma type_deref_shr_own_instr {𝔅} {E L} κ p n (ty : type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &shr{κ}(own_ptr n ty)] (!p) (&shr{κ} ty) (λ post '-[a], post a).
  Proof.
    iIntros (Hκ tid ? [vπ []]) "#LFT #TIME #PROPH #UNIQ HE $ HL [Hp _] /= Hproph".
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros ([[]|] [|[|depth]]) "_ #Hd Hown /="; try done.
    iDestruct "Hown" as (l') "#[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iApply wp_fupd. wp_read. iMod ("Hclose'" with "[H↦]") as "Htok1"; first by auto.
    iExists -[_].
    iMod ("Hclose" with "[Htok1 Htok2]") as "($ & $)"; first by iFrame.
    rewrite right_id tctx_hasty_val' //. iFrame.
    iExists (S _). simpl. iFrame "Hown".
    iApply (persistent_time_receipt_mono with "Hd"); lia.
  Qed.

  Lemma type_deref_shr_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_elt E L (p ◁ &shr{κ} (own_ptr n ty)) T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e) (trx ∘ tr).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_shr_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.

  Definition tr_unnest {𝔄} (post : pred' (𝔄 * 𝔄)%ST)
                            (vs : Π!%ST[((𝔄 * 𝔄) * (𝔄 * 𝔄))%ST]) : Prop :=
    let '-[(v, v')] := vs in v.2 = v'.2 → post (v.1, v'.1).

  Lemma type_deref_uniq_uniq_instr {𝔄 E L} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &uniq{κ}(&uniq{κ'}ty)] (!p) (&uniq{κ} ty) tr_unnest.
  Proof.
    iIntros (Hκ tid ? [vπ []]) "/= #LFT #TIME #PROPH #UNIQ #HE $ HL [Hp _] Hproph".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp").
    iIntros ([[]|] [|depth1]) "% #Hdepth1 [#Hκκ' H] //=";
      iDestruct "H" as (d' ξi) "([% %vπEqξ] & ξVo & Huniq)"; first lia.
    set ξ := PrVar _ ξi.
    iAssert (κ ⊑ foldr meet static (ty_lfts ty))%I as "Hκ".
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iMod (bor_acc_cons with "LFT Huniq Htok") as "[H Hclose']"; [done|].
    iMod (bi.later_exist_except_0 with "H") as (? [|depth2]) "(Hinner & > #Hdepth2' & ξPc)";
      iDestruct "Hinner" as ([|[[]|] []]) "(>Hl & #Hκ' & H)"; (try by iDestruct "H" as ">[]");
      try (iDestruct "H" as (? ?) "(>[% %] & ?)"; lia).
    iDestruct "H" as (depth3 ωi) "(>[% %ωEq] & ωVo & Hbor)".
    set ω := PrVar _ ωi.
    iMod (uniq_strip_later with "ξVo ξPc") as "(<- & -> & ξVo & ξPc)".
    iMod (uniq_update ξ with "UNIQ ξVo ξPc") as "[ξVo ξPc]"; [done|].
    iMod ("Hclose'" $! (∃ l', l ↦ #(LitLoc l') ∗
      (∃ vπ' d', .VO[ω] vπ' d' ∗ .PC[ξ] (λ π, (vπ' π, π ω)) (S d') ∗ ⧖ (2 + d')) ∗
      &{κ'}(∃ vπ' d', l' ↦∗: ty.(ty_own) vπ' d' tid ∗ ⧖(S d') ∗ .PC[ω] vπ' d')

    )%I  with "[] [Hbor Hl ωVo ξPc]") as "[Hbor Htok]".
    { iIntros "!> H". iDestruct "H" as (l') "[>H↦ [VoPc H]]".
      iDestruct "VoPc" as (??) "(>ωVo & ? & >#?)".
      iExists _,(S d'). iFrame "#∗".
      iExists [ #l' ]. rewrite heap_mapsto_vec_singleton. iFrame "H↦".
      iExists d', ωi. rewrite (proof_irrel (prval_to_inh' (λ π, (vπ' π, π ω))) (prval_to_inh' (fst ∘ vπ))).
      by iFrame. }
    { iExists l0. rewrite heap_mapsto_vec_singleton. iFrame.
      iExists _, _. iFrame. iApply (persistent_time_receipt_mono); [|done]. lia. }
    iClear "Hdepth1 Hdepth2'". clear dependent p depth1 Hκ.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor"; [done|].
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]"; [done|].
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']"; [done|].
    iMod (bor_sep with "LFT Hbor") as "[BorVoPc Hbor]"; [done|].
    iMod (bor_unnest with "LFT Hbor") as "Hbor"; [done|].
    iApply wp_fupd. iApply wp_cumulative_time_receipt=>//. wp_read. iIntros "Ht".
    iMod "Hbor".
    iMod ("Hclose'" with "[H↦]") as "[_ Htok]"; first by auto.
    iMod (bor_combine with "LFT BorVoPc [Hbor]") as "Hbor"; [done| |].
    { iApply (bor_shorten with "[] Hbor").
      iApply lft_incl_glb; [|iApply lft_incl_refl].
      iApply lft_incl_trans; [iApply "Hκκ'" |]. iApply lft_intersect_incl_l. }
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[[VoPc Hown] Hclose']"; [done|].
    iDestruct "VoPc" as (vπ' ?) "(Hvo & Hpc & ?)".
    iMod (bi.later_exist_except_0 with "Hown") as (wπ depth3') "(Hown & >#? & Hpcω)".
    iMod (uniq_strip_later with "ξVo Hpc") as "(% & -> & ξVo & ξPc)".
    rewrite (_ : vπ' = fst ∘ (fst ∘ vπ)); last first.
    (* TODO(xavier): remove usage of fun_ext here.  *)
    { fun_ext => x /=. move: (equal_f H x) => /= y. by inversion y.  }
    iMod (uniq_strip_later with "Hvo Hpcω") as "(<- & -> & ωVo & ωPc)".
    iMod (uniq_intro (fst ∘ (fst ∘ vπ)) _ with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; first done.
    set (ζ := PrVar _ ζi).
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    iDestruct (uniq_proph_tok with "ωVo ωPc") as "(ωVo & ω & ToωPc)".
    iMod (uniq_preresolve ξ [ζ; ω] (λ π, (π ζ, π ω)) with "PROPH ξVo ξPc [$ζ $ω]") as "(Hobs & (ζ & ω &_) & Heqz)"; [done| |done|].
    { apply (proph_dep_pair [_] [_]); apply proph_dep_one. }
    iDestruct ("ToζPc" with "ζ") as "ζPc".
    iDestruct ("ToωPc" with "ω") as "ωPc".
    iMod ("Hclose'" $! (∃ vπ' d', l' ↦∗: ty.(ty_own) vπ' d' tid ∗ ⧖ (S d') ∗ .PC[ζ] vπ' d')%I
      with "[Heqz ωVo ωPc Ht] [Hown ζPc]") as "[? Htok]".
    { iIntros "!> H".
      iMod (bi.later_exist_except_0 with "H") as (? ?) "(Hinner & > #Hd' & Hpc)".
      iMod (uniq_update with "UNIQ ωVo ωPc") as "[ωVo ωPc]"; [solve_ndisj|].
      iSplitR "Hinner ωPc".
      - iExists _, d'.
        iMod (cumulative_persistent_time_receipt with "TIME Ht Hd'") as "$"; [solve_ndisj|].
        iFrame. iApply "Heqz".
        iDestruct (proph_ctrl_eqz with "PROPH Hpc") as "Eqz".
        iApply (proph_eqz_constr2 pair with "Eqz []").
        iApply proph_eqz_eq.
      - iExists _, _. by iFrame. }
    { iExists _, _. by iFrame. }
    iExists -[λ π, ((vπ π).1.1 , π ζ)]. rewrite right_id.
    iMod ("Hclose" with "Htok") as "$".
    iSplitR "Hproph Hobs".
    - iExists _, _. iFrame "#". iSplitR; [done|].
      iExists _, ζi. by iFrame.
    - iCombine "Hproph Hobs" as "?". iApply proph_obs_impl; [|done].
      move => π. move: (equal_f vπEqξ π) (equal_f ωEq π) => /=.
      destruct (vπ π) as [v v'] => /= -> ? /= [+ b]; rewrite b => /= ?; auto.
  Qed.

  Lemma type_deref_uniq_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_elt E L (p ◁ &uniq{κ} (&uniq{κ'} ty)) T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e)
      (trx ∘ (λ post '(v -:: bl),
                tr_unnest (λ v', tr post (v' -:: bl)) -[v])).
  Proof.
    iIntros. by iApply type_let; [by eapply type_deref_uniq_uniq_instr|solve_typing| |done].
  Qed.

  Lemma type_deref_shr_uniq_instr {𝔄} {E L} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L +[p ◁ &shr{κ}(&uniq{κ'}ty)] (!p) (&shr{κ}ty) (λ post '-[v], post v.1).
  Proof.
    iIntros (Hκ tid ? [vπ []]) "#LFT #TIME #PROPH #UNIQ HE $ HL [Hp _] Hproph".
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros ([[]|] [|[|depth]]) "% #Hdepth Hshr"; try done.
    iDestruct "Hshr" as (l' ξ) "(% & H↦ & Hdep & Hshr)".
    iMod (frac_bor_acc with "LFT H↦ Htok") as (q'') "[>H↦ Hclose']". done.
    iApply wp_fupd. wp_read.
    iMod ("Hclose'" with "[H↦]") as "Htok"; first by auto.
    iMod ("Hclose" with "Htok") as "$".
    iExists -[_].
    rewrite right_id tctx_hasty_val' //.
    iFrame. iExists (S depth). iFrame.
    iApply (persistent_time_receipt_mono with "Hdepth"); lia.
  Qed.

  Lemma type_deref_shr_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_elt E L (p ◁ &shr{κ} (&uniq{κ'} ty)) T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := !p in e)
      (trx ∘ (λ post '(v -:: bl), tr post (v.1 -:: bl))).
  Proof.
    iIntros. by iApply type_let; [by eapply type_deref_shr_uniq_instr|solve_typing| |done].
  Qed.
End borrow.

Global Hint Resolve tctx_extract_hasty_borrow | 10 : lrust_typing.
