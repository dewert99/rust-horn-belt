From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.

Open Scope nat.

Notation "l ↦∗len n" := (l ↦∗: (λ vl, ⌜length vl = n%nat⌝))%I
  (at level 20, format "l  ↦∗len  n") : bi_scope.
Notation freeable_sz' sz l := (freeable_sz sz%nat sz%nat l).

Section vec.
  Context `{!typeG Σ}.

  Program Definition vec {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 3;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own alπ d tid vl :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜vl = [ #len; #ex; #l] ∧ alπ = vec_to_list ∘ vapply aπl⌝ ∗
        ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
        (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
        freeable_sz' ((ex + len) * ty.(ty_size)) l;
    ty_shr alπ d κ tid l' :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜alπ = (λ π, vapply aπl π)⌝ ∗ &frac{κ} (λ q, l' ↦∗{q} [ #len; #ex; #l]) ∗
        ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i);
  |}%I.
  Next Obligation.
    iIntros (???[]??) "vec //". by iDestruct "vec" as (????[-> _]) "?".
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 17 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 14 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|]. iIntros "#? (%&%&%&%&%&?& All)".
    iExists _, _, _, _. iSplit; [done|]. iSplit; [by iApply frac_bor_shorten|].
    rewrite !big_sepL_forall. iIntros "!> **".
    iApply ty_shr_lft_mono; by [|iApply "All"].
  Qed.
  Next Obligation.
    iIntros (???? d ? l' tid q ?) "#LFT #In Bor κ".
    iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    move: d=> [|d]. { by iMod (bor_persistent with "LFT Bor κ") as "[>[] _]". }
    do 2 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_exists with "LFT Bor") as (l) "Bor"; [done|].
    iMod (bor_exists_tok with "LFT Bor κ") as (aπl) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>[->->] & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_fracture (λ q', _ ↦∗{q'} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (bor_later_tok with "LFT Bor κ") as "Borκ"; [done|]. iIntros "/=!>!>!>".
    iMod "Borκ" as "[Bor κ]". iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    iAssert (|={E}=> |={E}▷=>^d |={E}=>
      ([∗ list] i ↦ aπ ∈ aπl, ty_shr ty aπ d κ tid (l +ₗ[ty] i)) ∗ q.[κ])%I
      with "[κ Bors]" as "Upd"; last first.
    { iApply (step_fupdN_wand with "Upd"). iIntros ">[?$] !>".
      iExists _, _, _, _. iSplit; [done|]. iFrame. }
    iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. by iFrame. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "Bors" as "[Bor Bors]".
    iMod (ty_share with "LFT In Bor κ") as "Toshr"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "κ₊ Bors") as "Toshrs".
    iCombine "Toshr Toshrs" as "Toshrs". iApply (step_fupdN_wand with "Toshrs").
    by iIntros "!> [>[$$] >[$$]]".
  Qed.
  Next Obligation.
    iIntros (????[|d] tid ?? q ?) "#LFT #In vec κ //=".
    iDestruct "vec" as (??? aπl[->->]) "(↦tys & ex & †)". iIntros "!>!>!>".
    iAssert (|={E}=> |={E}▷=>^d |={E}=> ∃ξl q',
      ⌜vec_to_list ∘ vapply aπl ./ ξl⌝ ∗ q':+[ξl] ∗ (q':+[ξl] ={E}=∗
        ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) ∗ q.[κ]))%I
      with "[↦tys κ]" as "To↦tys"; last first.
    { iApply (step_fupdN_wand with "To↦tys"). iIntros ">(%&%&%& ξl & To↦tys) !>".
      iExists _, _. iSplit; [done|]. iIntros "{$ξl}ξl".
      iMod ("To↦tys" with "ξl") as "[?$]". iModIntro. iExists _, _, _, _. by iFrame. }
    iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      iFrame "κ". do 2 (iSplit; [done|]). by iIntros. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "↦tys" as "[(% & ↦ & ty) ↦tys]".
    iMod (ty_own_proph with "LFT In ty κ") as "Toty"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "↦tys κ₊") as "To↦tys".
    iCombine "Toty To↦tys" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "!> [>(%&%&%& ξl & Toty) >(%&%&%& ζl & To↦tys)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iFrame "ξζl". iSplit; [iPureIntro; by apply proph_dep_constr2|].
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toty" with "ξl") as "[?$]". iMod ("To↦tys" with "ζl") as "[$$]".
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|d] κ ? l' κ' q ?) "#LFT #In #In' vec κ' //=".
    iDestruct "vec" as (?? l aπl ->) "[? tys]". iIntros "!>!>!>".
    iAssert (|={E}▷=> |={E}▷=>^d |={E}=> ∃ξl q',
      ⌜vec_to_list ∘ vapply aπl ./ ξl⌝ ∗ q':+[ξl] ∗ (q':+[ξl] ={E}=∗
        ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) ∗ q.[κ']))%I
      with "[tys κ']" as "Totys"; last first.
    { iApply (step_fupdN_wand with "Totys"). iIntros "!> >(%&%&%& ξl & Totys)!>".
      iExists _, _. iSplit; [done|]. iIntros "{$ξl}ξl".
      iMod ("Totys" with "ξl") as "[?$]". iExists _, _, _, _. by iFrame. }
    iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      iFrame "κ'". do 2 (iSplit; [done|]). by iIntros. }
    iDestruct "κ'" as "[κ' κ'₊]". iDestruct "tys" as "[ty tys]".
    iMod (ty_shr_proph with "LFT In In' ty κ'") as "Toty"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "tys κ'₊") as "Totys".
    iIntros "!>!>". iCombine "Toty Totys" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "[>(%&%&%& ξl & Toty) >(%&%&%& ζl & Totys)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iFrame "ξζl". iSplit; [iPureIntro; by apply proph_dep_constr2|].
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toty" with "ξl") as "[$$]". by iMod ("Totys" with "ζl") as "[$$]".
  Qed.

  Global Instance vec_ne {𝔄} : NonExpansive (@vec 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance vec_type_contractive 𝔄 : TypeContractive (@vec 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |].
    - move=>/= > ->*. do 19 (f_contractive || f_equiv). by simpl in *.
    - move=>/= > ->*. do 16 (f_contractive || f_equiv). by simpl in *.
  Qed.

End vec.
