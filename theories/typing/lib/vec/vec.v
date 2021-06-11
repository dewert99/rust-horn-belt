From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec.
  Context `{!typeG Σ}.

  Definition freeable_sz' (sz: nat) (l: loc) : iProp Σ :=
    †{1}l…sz ∨ ⌜Z.of_nat sz = 0%Z⌝.

  Lemma split_vec_mt {𝔄} l' q d alπ Φ :
    (l' ↦∗{q}: (λ vl, [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
      ⌜vl = [ #len; #ex; #l] ∧ alπ = lapply aπl⌝ ∗ Φ d' len ex l aπl))%I ⊣⊢
    [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
      ⌜alπ = lapply aπl⌝ ∗
      l' ↦{q} #len ∗ (l' +ₗ 1) ↦{q} #ex ∗ (l' +ₗ 2) ↦{q} #l ∗ Φ d' len ex l aπl.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". case d=>// ?. iDestruct "big" as (????[->->]) "Φ".
      iExists _, _, _, _. iSplit; [done|]. iFrame "Φ".
      rewrite !heap_mapsto_vec_cons shift_loc_assoc. iDestruct "↦" as "($&$&$&_)".
    - iIntros "big". case d=>// ?. iDestruct "big" as (????->) "(↦₀ & ↦₁ & ↦₂ & ?)".
      iExists [_;_;_]. rewrite !heap_mapsto_vec_cons shift_loc_assoc heap_mapsto_vec_nil.
      iFrame "↦₀ ↦₁ ↦₂". iExists _, _, _, _. by iFrame.
  Qed.

  Program Definition vec_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 3;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own alπ d tid vl :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜vl = [ #len; #ex; #l] ∧ alπ = lapply aπl⌝ ∗
        ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
        (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
        freeable_sz' ((len + ex) * ty.(ty_size)) l;
    ty_shr alπ d κ tid l' :=
      [S(d') := d] ∃(len ex: nat) (l: loc) (aπl: vec (proph 𝔄) len),
        ⌜alπ = lapply aπl⌝ ∗
        &frac{κ} (λ q, l' ↦{q} #len ∗ (l' +ₗ 1) ↦{q} #ex ∗ (l' +ₗ 2) ↦{q} #l) ∗
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
    iIntros (???? d ? l' tid q ?) "#LFT In Bor κ". rewrite split_vec_mt. case d.
    { by iMod (bor_persistent with "LFT Bor κ") as "[>[] _]". }
    move=> ?. do 2 (iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|]).
    iMod (bor_exists with "LFT Bor") as (l) "Bor"; [done|].
    iMod (bor_exists_tok with "LFT Bor κ") as (aπl) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    do 2 rewrite assoc. iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    rewrite -assoc. iMod (bor_fracture (λ q', _ ↦{q'} _ ∗ _ ↦{q'} _ ∗ _ ↦{q'} _)%I
      with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_later_tok with "LFT Bor κ") as "Borκ"; [done|].
    iIntros "/=!>!>!>". iMod "Borκ" as "[Bor κ]".
    iMod (ty_share_big_sepL with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|d] tid ?? q ?) "LFT In vec κ //=".
    iDestruct "vec" as (??? aπl [->->]) "(↦tys & ex & †)". iIntros "!>!>!>".
    iMod (ty_own_proph_big_sepL_mt with "LFT In ↦tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _. iSplit.
    { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
    iExists _, _, _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|d] κ ? l' κ' q ?) "LFT In In' vec κ' //=".
    iDestruct "vec" as (?? l aπl ->) "[? tys]". iIntros "!>!>!>".
    iMod (ty_shr_proph_big_sepL with "LFT In In' tys κ'") as "Totys"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Totys").
    iIntros ">(%&%&%& ξl & Totys) !>". iExists _, _. iSplit.
    { iPureIntro. rewrite -vec_to_list_apply. by apply proph_dep_constr. }
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[?$]". iModIntro.
    iExists _, _, _, _. by iFrame.
  Qed.

  Global Instance vec_ty_ne {𝔄} : NonExpansive (@vec_ty 𝔄).
  Proof. solve_ne_type. Qed.
End vec.
