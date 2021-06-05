From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Notation "l ↦∗len n" := (∃vl, ⌜length vl = n%nat⌝ ∗ l ↦∗ vl)%I
  (at level 20, format "l  ↦∗len  n") : bi_scope.

Section vec.
  Context `{!typeG Σ}.

  Definition freeable_sz' (sz: nat) (l: loc) : iProp Σ :=
    †{1}l…sz ∨ ⌜Z.of_nat sz = 0⌝.

  Program Definition vec_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
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

  Global Instance vec_ty_ne {𝔄} : NonExpansive (@vec_ty 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance vec_type_contractive 𝔄 : TypeContractive (@vec_ty 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |].
    - move=>/= > ->*. do 19 (f_contractive || f_equiv). by simpl in *.
    - move=>/= > ->*. do 16 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance vec_send {𝔄} (ty: type 𝔄) : Send ty → Send (vec_ty ty).
  Proof. move=> ?>/=. by do 19 f_equiv. Qed.

  Global Instance vec_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (vec_ty ty).
  Proof. move=> ?>/=. by do 16 f_equiv. Qed.

  Lemma vec_leak {𝔄} (ty: type 𝔄) Φ E L :
    leak E L ty Φ → leak E L (vec_ty ty) (lforall Φ).
  Proof.
    iIntros (Lk ? q ?[|]???) "#LFT #PROPH #E L vec //=".
    iDestruct "vec" as (?? l aπl[->->]) "[↦tys _]". iIntros "!>!>!>".
    iInduction aπl as [|] "IH" forall (q l)=>/=.
    { iApply step_fupdN_full_intro. iFrame. by iApply proph_obs_true. }
    iDestruct "↦tys" as "[(%&_& ty) ↦tys]". iDestruct "L" as "[L L₊]".
    iMod (Lk with "LFT PROPH E L ty") as "Upd"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "L₊ ↦tys") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "!>[>[#? $] >[#? $]]". by iApply proph_obs_and.
  Qed.

  Lemma vec_leak_just {𝔄} (ty: type 𝔄) E L :
    leak E L ty (const True) → leak E L (vec_ty ty) (const True).
  Proof. move=> ?. apply leak_just. Qed.

  Lemma vec_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (vec_ty ty) (vec_ty ty') (map f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "(%EqSz & #? & #InOwn & #InShr)".
    have Eq: ∀(aπl: vec (proph 𝔄) _), map f ∘ lapply aπl = lapply (vmap (f ∘.) aπl).
    { move=> ?. elim; [done|]=> ??? IH. fun_ext=>/= ?. f_equal. apply (equal_f IH). }
    do 2 (iSplit; [done|]). iSplit; iIntros "!>" (?[|]) "* vec //=".
    - iDestruct "vec" as (?? l aπl [->->]) "(↦tys & ex & †)".
      iExists _, _, _, _. rewrite Eq EqSz. iSplit; [done|]. iFrame "ex †".
      iNext. iInduction aπl as [|] "IH" forall (l)=>/=; [done|].
      iDestruct "↦tys" as "[(%& ↦ & ty) ↦tys]". setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct ("IH" with "↦tys") as "$". iExists _. iFrame "↦". by iApply "InOwn".
    - iDestruct "vec" as (?? l' ?->) "(↦ & tys)". iExists _, _, _, _.
      rewrite Eq EqSz. iSplit; [done|]. iFrame "↦". iNext.
      iInduction aπl as [|] "IH" forall (l')=>/=; [done|].
      iDestruct "tys" as "[ty tys]". setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct ("IH" with "tys") as "$". by iApply "InShr".
  Qed.
  Lemma vec_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (vec_ty ty) (vec_ty ty') (map f) (map g).
  Proof. move=> [??]. split; by apply vec_subtype. Qed.
End vec.

Global Hint Resolve vec_leak | 5 : lrust_typing.
Global Hint Resolve vec_leak_just vec_subtype vec_eqtype : lrust_typing.
