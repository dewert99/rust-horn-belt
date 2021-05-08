From lrust.typing Require Export type.
From lrust.typing Require Import uninit.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section maybe_uninit.
  Context `{!typeG Σ}.

  Local Lemma maybe_uninit_mt {𝔄} (ty: _ 𝔄) vπ d tid l q :
    (l ↦∗{q}: λ vl, ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl)%I ⊣⊢
    ⌜vπ = const None⌝ ∗ l ↦∗{q}: (λ vl, ⌜length vl = ty.(ty_size)⌝) ∨
    ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ l ↦∗{q}: ty.(ty_own) vπ' d tid.
  Proof. iSplit.
    - iIntros "(%vl &?&[[%%]|(%vπ' &%&?)])". { iLeft. iSplit; [done|]. iExists vl.
      by iFrame. } iRight. iExists vπ'. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "[(%& %vl & ↦ &%)|(%vπ' &%& %vl & ↦ &?)]"; iExists vl; iFrame "↦";
      [by iLeft|]. iRight. iExists vπ'. by iSplit.
  Qed.

  Program Definition maybe_uninit {𝔄} (ty: type 𝔄) : type (optionₛ 𝔄) := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl :=
      ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ': proph 𝔄, ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl;
    ty_shr vπ d κ tid l :=
      ⌜vπ = const None⌝ ∨
      ∃vπ': proph 𝔄, ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_shr) vπ' d κ tid l;
  |}%I.
  Next Obligation. iIntros "* [[_$]|(%&_&?)]". by rewrite ty_size_eq. Qed.
  Next Obligation.
    move=> *. iIntros "[?|(%vπ &?&?)]"; [by iLeft|iRight]. iExists vπ.
    iSplit; [done|]. by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "[?|(%vπ &?&?)]"; [by iLeft|iRight]. iExists vπ.
    iSplit; [done|]. by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "#? [?|(%vπ &?&?)]"; [by iLeft|iRight]. iExists vπ.
    iSplit; [done|]. by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT In Bor κ". rewrite maybe_uninit_mt.
    iMod (bor_or with "LFT Bor") as "[Bor|Bor]"; first done.
    { iApply step_fupdN_full_intro.
      iMod (bor_sep_persistent with "LFT Bor κ") as "(>->&?&$)"; by [|iLeft]. }
    iMod (bor_exists_tok with "LFT Bor κ") as (vπ) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>->& Bor & κ)"; [done|].
    iMod (ty_share with "LFT In Bor κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[?$] !>". iRight.
    iExists vπ. by iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT In [[->%]|(%vπ &->& ty)] κ".
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). iIntros "_!>". iFrame "κ". by iLeft. }
    iMod (ty_own_proph with "LFT In ty κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%ξl & %q &%& ξl & Toty) !>".
    iExists ξl, q. iSplit; [iPureIntro; by apply proph_dep_constr|].
    iFrame "ξl". iIntros "ξl". iMod ("Toty" with "ξl") as "[?$]".
    iRight. iExists vπ. by iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT In In' [->|(%vπ &->& ty)] κ".
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). iIntros "_!>". iFrame "κ". by iLeft. }
    iMod (ty_shr_proph with "LFT In In' ty κ") as "Upd"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%ξl&%q&%& ξl & Toty) !>". iExists ξl, q.
    iSplit; [iPureIntro; by apply proph_dep_constr|]. iFrame "ξl". iIntros "ξl".
    iMod ("Toty" with "ξl") as "[?$]". iRight. iExists vπ. by iFrame.
  Qed.

  Global Instance maybe_uninit_ne {𝔄} : NonExpansive (@maybe_uninit 𝔄).
  Proof. solve_ne_type. Qed.

End maybe_uninit.

Notation "?" := maybe_uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance maybe_uninit_type_ne {𝔄} : TypeNonExpansive (@maybe_uninit _ _ 𝔄).
  Proof.
    constructor; [by apply type_lft_morph_id_like|done| |];
    [move=>/= > ->*|move=>/= >*]; by do 4 f_equiv.
  Qed.

  Global Instance maybe_uninit_send {𝔄} (ty: _ 𝔄) : Send ty → Send (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.
  Global Instance maybe_uninit_sync {𝔄} (ty: _ 𝔄) : Sync ty → Sync (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.

  Lemma maybe_uninit_leak {𝔄} (ty: _ 𝔄) Φ E L :
    Leak E L ty Φ → Leak E L (? ty) (λ o, ∀a: 𝔄, o = Some a → Φ a).
  Proof.
    move=> Lk > ?. iIntros "LFT PROPH E L [[-> _]|(%&->& ty)]".
    { iApply step_fupdN_full_intro. iIntros "!>!>". iFrame "L".
      iApply proph_obs_true=>/= ?? Eq. inversion Eq. }
    iMod (Lk with "LFT PROPH E L ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). iIntros "!> >[Obs $] !>".
    by iApply proph_obs_impl; [|done]=>/= ???[=<-].
  Qed.

  Lemma maybe_uninit_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (? ty) (? ty') (option_map f).
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "(%&?& #InOwn & #InShr)".
    do 2 (iSplit; [done|]). iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%vπ' &->&?)]"; [by iLeft|]. iRight. iExists (f ∘ vπ').
      iSplit; [done|]. by iApply "InOwn".
    - iIntros "[->|(%vπ' &->&?)]"; [by iLeft|]. iRight. iExists (f ∘ vπ').
      iSplit; [done|]. by iApply "InShr".
  Qed.
  Lemma maybe_uninit_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (? ty) (? ty') (option_map f) (option_map g).
  Proof. move=> [??]. split; by apply maybe_uninit_subtype. Qed.

  Lemma uninit_to_maybe_uninit {𝔄} (ty: _ 𝔄) E L :
    subtype E L (↯ ty.(ty_size)) (? ty) (const None).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_static|].
    by iSplit; iIntros "!>*%/="; iLeft.
  Qed.

  Lemma into_maybe_uninit {𝔄} (ty: _ 𝔄) E L : subtype E L ty (? ty) Some.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*?/="; iRight; iExists vπ; by iFrame.
  Qed.

  Lemma maybe_uninit_join {𝔄} (ty: _ 𝔄) E L :
    subtype E L (? (? ty)) (? ty) (option_join _).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%&->&[[->->]|(%vπ'' &->&?)])]"; [by iLeft|by iLeft|].
      iRight. iExists vπ''. by iFrame.
    - iIntros "[->|(%&->&[->|(%vπ'' &->&?)])]"; [by iLeft|by iLeft|].
      iRight. iExists vπ''. by iFrame.
  Qed.

End typing.

Global Hint Resolve maybe_uninit_leak | 10 : lrust_typing.
Global Hint Resolve maybe_uninit_subtype maybe_uninit_eqtype : lrust_typing.
