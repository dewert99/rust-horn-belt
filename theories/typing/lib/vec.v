From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.

Open Scope nat.

Notation "l ↦∗len n" := (∃vl, ⌜length vl = n%nat⌝ ∗ l ↦∗ vl)%I
  (at level 20, format "l  ↦∗len  n") : bi_scope.

Section vec.
  Context `{!typeG Σ}.

  Definition freeable_sz' (sz: nat) (l: loc) : iProp Σ :=
    †{1}l…sz ∨ ⌜Z.of_nat sz = 0⌝.

  Program Definition vec {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 3;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own alπ d tid vl :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜vl = [ #len; #ex; #l] ∧ alπ = lapply aπl⌝ ∗
        ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
        (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
        freeable_sz' ((ex + len) * ty.(ty_size)) l;
    ty_shr alπ d κ tid l' :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜alπ = lapply aπl⌝ ∗ &frac{κ} (λ q, l' ↦∗{q} [ #len; #ex; #l]) ∗
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
    iIntros (???? d ? l' tid q ?) "#LFT In Bor κ".
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
    iMod "Borκ" as "[Bor κ]".
    iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _, _, _, _. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|d] tid ?? q ?) "LFT In vec κ //=".
    iDestruct "vec" as (??? aπl[->->]) "(↦tys & ex & †)". iIntros "!>!>!>".
    iMod (ty_own_proph_mt_big_sepL_v with "LFT In ↦tys κ") as "To↦tys"; [done|].
    iApply (step_fupdN_wand with "To↦tys"). iIntros "!> >(%&%&%& ξl & To↦tys) !>".
    iExists _, _. iSplit.
    { iPureIntro. rewrite lapply_vapply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("To↦tys" with "ξl") as "[?$]". iModIntro.
    iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|d] κ ? l' κ' q ?) "LFT In In' vec κ' //=".
    iDestruct "vec" as (?? l aπl ->) "[? tys]". iIntros "!>!>!>".
    iMod (ty_shr_proph_big_sepL_v with "LFT In In' tys κ'") as "Totys"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Totys").
    iIntros ">(%&%&%& ξl & Totys)!>". iExists _, _. iSplit.
    { iPureIntro. rewrite lapply_vapply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[?$]". iModIntro.
    iExists _, _, _, _. by iFrame.
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
