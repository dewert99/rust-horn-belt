From lrust.typing Require Export type.
From lrust.typing Require Import zst typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section permdata.
  Context `{!typeG Σ}.

  Lemma split_mt_pdata {𝔄} (d: nat) l' vπ ty tid:
    (∃ vl, l' ↦∗ vl ∗ ∃ (l: loc) (vπ': (proph 𝔄)),
    ⌜vl = [] ∧ vπ = λ π, (l, vπ' π)⌝ ∗
    ((box ty).(ty_own) vπ' d tid [ #l])) ⊣⊢
    ∃ l (vπ': (proph 𝔄)),
      ⌜vπ = λ π, (l, vπ' π)⌝ ∗ l' ↦∗ [] ∗ ((box ty).(ty_own) vπ' d tid [ #l]).
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". iDestruct "big" as (??[->->]) "Φ".
      iExists _, _. iSplit; [done|iFrame].
    - iIntros "big". iDestruct "big" as (??->) "(↦ & ?)".
      iExists []. iFrame "↦". iExists _, _. by iFrame.
  Qed.

  (* Rust's GhostSeq<T> *)
  Program Definition permdata_ty {𝔄} (ty: type 𝔄) : type (locₛ * 𝔄) := {|
    ty_size := 0;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_proph vπ ξl := exists l (vπ': (proph 𝔄)),
      vπ = (λ π, (l, vπ' π)) /\ ty.(ty_proph) vπ' ξl;
    ty_own vπ d tid vl :=
      ∃ l (vπ': (proph 𝔄)),
        ⌜vl = [] ∧ vπ = λ π, (l, vπ' π)⌝ ∗
        ((box ty).(ty_own) vπ' d tid [ #l]);
    ty_shr vπ d κ tid _ :=
      ∃ l (vπ': (proph 𝔄)),
        ⌜vπ = λ π, (l, vπ' π)⌝ ∗
        [S(d') := d] ▷ ty.(ty_shr) vπ' d' κ tid l;
  |}%I.
  Next Obligation.
    iIntros (??????) "token //". by iDestruct "token" as (??[-> _]) "?".
  Qed.
  Next Obligation.
    Opaque box. move=> ????*/=; try (by iIntros). do 5 f_equiv.
    apply ty_own_depth_mono. lia.
    Transparent box.
  Qed.
  Next Obligation.
    move=> ??[|?][|?] */=; do 5 f_equiv. by iIntros. lia.
    f_equiv. apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*; iIntros "#? (%&%&?&shr)". done.
    iExists _, _. iSplit; [done|].
    iApply ty_shr_lft_mono; done.
  Qed.
  Next Obligation.
    iIntros (???? d) "*% #LFT In Bor κ". rewrite split_mt_pdata.
    do 2 (iMod (bor_exists_tok with "LFT Bor κ") as (?) "[Bor κ]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    destruct d; simpl. 
    iMod (bor_persistent with "LFT Bor κ") as "(>false&$)"; done.
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_later_tok with "LFT Bor κ") as "Bor"; [done|].
    iIntros "!>!>!>". iMod "Bor" as "[Bor κ]".
    iMod (ty_share with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _, _. iSplit. done. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????) "*% LFT In token κ".
    iDestruct "token" as (??[->->]) "↦tys".
    iMod (ty_own_proph (box ty) with "LFT In ↦tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _. iSplit. iExists _, _. done.
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
    iExists _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|?]) "*% *% LFT In In' (%&%&->&tys) κ'/="; [done|].
    iIntros "!>!>". iMod (ty_shr_proph with "LFT In In' tys κ'") as "Toκ'"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Toκ'").
    iIntros "!> >(%&%&%& ξl & Toκ') !>". iExists _, _. iSplit. iExists _, _. done.
    iIntros "{$ξl}ξl". by iMod ("Toκ'" with "ξl") as "$".
  Qed.
  Next Obligation.
    simpl. intros ????(?&?&->&?).
    rewrite -(left_id _ app ξl) -(Nat.max_id (ghost_level _)). apply proph_dep_prod.
    done. by eapply ty_proph_weaken.
  Qed.

  Global Instance permdata_ty_ne {𝔄} : NonExpansive (@permdata_ty 𝔄).
  Proof.
    solve_ne_type. done.
  Qed.
End permdata.
