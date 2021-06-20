From lrust.typing Require Import typing uniq_array_util.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_slice.
  Context `{!typeG Σ}.

  Lemma split_mt_uniq_slice {A} P Ψ Φ l' q :
    (l' ↦∗{q}: (λ vl, P ∗
      ∃(l: loc) (n d': nat) (aπξil: A n),
        ⌜vl = [ #l; #n] ∧ Ψ n aπξil d'⌝ ∗ Φ l n d' aπξil)) ⊣⊢
    P ∗ ∃(l: loc) (n d': nat) aπξil,
      ⌜Ψ n aπξil d'⌝ ∗ l' ↦{q} #l ∗ (l' +ₗ 1) ↦{q} #n ∗ Φ l n d' aπξil.
  Proof.
    iSplit.
    - iIntros "(%& ↦ &$&%&%&%&%&[->%]& Φ)". iExists _, _, _, _. iSplit; [done|].
      iFrame "Φ". rewrite !heap_mapsto_vec_cons. iDestruct "↦" as "($&$&_)".
    - iIntros "($&%&%&%&%&%& ↦ & ↦' & Φ)". iExists [_;_].
      rewrite !heap_mapsto_vec_cons heap_mapsto_vec_nil. iFrame "↦ ↦'".
      iExists _, _, _, _. by iFrame.
  Qed.

  Definition prval_pos_to_prpair {𝔄} : proph 𝔄 * positive → proph (𝔄 * 𝔄) :=
    λ '(vπ, ξi) π, (vπ π, π (PrVar (𝔄 ↾ prval_to_inh vπ) ξi): 𝔄).

  Program Definition uniq_slice {𝔄}
      (κ: lft) (ty: type 𝔄) : type (listₛ (𝔄 * 𝔄)) := {|
    ty_size := 2;  ty_lfts := κ :: ty.(ty_lfts);  ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    ty_own vπ d tid vl := κ ⊑ ty.(ty_lft) ∗
      ∃(l: loc) (n d': nat) (aπξil: vec (proph 𝔄 * positive) n),
        ⌜vl = [ #l; #n] ∧ vπ = lapply (vmap prval_pos_to_prpair aπξil)
          ∧ (S d' ≤ d)%nat⌝ ∗
        [∗ list] i ↦ aπξi ∈ aπξil, uniq_own ty aπξi.1 aπξi.2 d' κ tid (l +ₗ[ty] i);
    ty_shr vπ d κ' tid l' := [S(d') := d]
      ∃(l: loc) (n: nat) (aπl: vec (proph 𝔄) n) ξl,
        ⌜map fst ∘ vπ = lapply aπl ∧ map snd ∘ vπ ./ ξl⌝ ∗
        &frac{κ'} (λ q, l' ↦{q} #l ∗ (l' +ₗ 1) ↦{q} #n) ∗ &frac{κ'} (λ q, q:+[ξl]) ∗
        ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ' tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation. by iIntros "* (_&%&%&%&%&[->?]&_)". Qed.
  Next Obligation. move=>/= *. by do 14 f_equiv. Qed.
  Next Obligation.
    move=> ???[|?][|?]*/=; try (by iIntros); [lia|]. do 15 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??????[|?]*; [by iIntros|]. iIntros "#? (%&%&%&%&%&#?&#?& #All)".
    iExists _, _, _, _. iSplit; [done|].
    do 2 (iSplitL; [by iApply frac_bor_shorten|]). iNext. rewrite !big_sepL_forall.
    iIntros (???). iApply ty_shr_lft_mono; [done|]. by iApply "All".
  Qed.
  Next Obligation.
    iIntros (????? d) "*% #LFT #In Bor κ'". rewrite split_mt_uniq_slice.
    iMod (bor_sep with "LFT Bor") as "[_ Bor]"; [done|].
    do 3 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_exists_tok with "LFT Bor κ'") as (aπξil) "[Bor κ']"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ'") as "(>[->%] & Bor & κ')"; [done|].
    rewrite assoc. iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_fracture (λ q, _ ↦{q} _ ∗ _ ↦{q} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (ty_share_big_sepL_uniq_own with "LFT [] [] Bor κ'") as "Upd"; [done|..].
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
    iIntros "!> >(Borξl & tys &$)". set ξl := vmap _ _.
    iMod (bor_fracture (λ q, q:+[_])%I with "LFT Borξl") as "Borξl"; [done|].
    iModIntro. case d as [|]; [lia|]. iExists _, _, _, _. iFrame "Bor↦ Borξl".
    iSplit; last first.
    { iClear "#". iNext. iStopProof. do 3 f_equiv. iApply ty_shr_depth_mono. lia. }
    iPureIntro. split.
    - fun_ext=>/= ?. elim aπξil; [done|]. by move=>/= [??]??->.
    - rewrite /ξl. elim aπξil; [done|]. case=>/= [??]???.
      apply (proph_dep_constr2 _ _ _ [_]); [|done]. apply proph_dep_one.
  Qed.
  Next Obligation.
    iIntros "*% LFT #? (#? & %&%&%& %aπξil &(->&->&%)& uniqs) κ'".
    iMod (ty_own_proph_big_sepL_uniq_own with "LFT [] [] uniqs κ'") as "Upd"; [done|..].
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
    iIntros "!> >(%&%& %Dep & ζξl & Touniqs) !>". iExists _, _. iFrame "ζξl". iSplit.
    { iPureIntro. apply proph_dep_list_prod.
      - apply (proph_dep_constr vec_to_list) in Dep. eapply proph_dep_eq; [done|].
        fun_ext=>/= ?. elim aπξil; [done|]. by move=>/= [??]??->.
      - elim aπξil; [done|]. move=>/= [??]???.
        apply (proph_dep_constr2 _ _ _ [_]); [|done]. apply proph_dep_one. }
    iIntros "ζξl". iMod ("Touniqs" with "ζξl") as "[uniqs $]". iModIntro.
    iSplit; [done|]. iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????? d) "*% #LFT #In #In' big [κ' κ'₊]". case d; [done|]=> ?.
    iDestruct "big" as (????[Eq ?]) "(Bor↦ & #Borξl & tys)". iIntros "!>!>!>/=".
    iMod (ty_shr_proph_big_sepL with "LFT In [] tys κ'") as "Upd"; [done|..].
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iMod (lft_incl_acc with "In κ'₊") as (?) "[κ0 Toκ'₊]"; [done|].
    iMod (frac_bor_acc with "LFT Borξl κ0") as (?) "[>ξl Toκ0]"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%&%&%& ζl & Toshr) !>".
    iDestruct (proph_tok_combine with "ζl ξl") as (?) "[ζξl Toζξl]".
    iExists _, _. iFrame "ζξl". iSplit.
    { iPureIntro. apply proph_dep_list_prod; [|done]. rewrite Eq.
      rewrite -vec_to_list_apply. by apply proph_dep_constr. }
    iIntros "ζξl". iDestruct ("Toζξl" with "ζξl") as "[ζl ξl]".
    iMod ("Toshr" with "ζl") as "[tys $]". iMod ("Toκ0" with "ξl") as "κ0".
    iMod ("Toκ'₊" with "κ0") as "$". iModIntro. iExists _, _, _, _.
    iSplit; [done|]. by iFrame.
  Qed.

  Global Instance uniq_slice_ne {𝔄} κ : NonExpansive (@uniq_slice 𝔄 κ).
  Proof. rewrite /uniq_slice /uniq_own. solve_ne_type. Qed.
End uniq_slice.
