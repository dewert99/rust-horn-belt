Require Import FunctionalExtensionality Equality.
From lrust.typing Require Export type.
From lrust.typing Require Import uninit.
Set Default Proof Using "Type".

Section maybe_uninit.
  Context `{!typeG Σ}.

  Local Lemma maybe_uninit_mt {A} (ty: _ A) vπ d tid l q :
    (l ↦∗{q}: λ vl, ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl)%I ⊣⊢
    ⌜vπ = const None⌝ ∗ l ↦∗{q}: (λ vl, ⌜length vl = ty.(ty_size)⌝) ∨
    ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ l ↦∗{q}: ty.(ty_own) vπ' d tid.
  Proof. iSplit.
    - iIntros "(%vl &?&[[%%]|(%vπ' &%&?)])". { iLeft. iSplit; [done|]. iExists vl.
      by iFrame. } iRight. iExists vπ'. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "[(%& %vl & Mt &%)|(%vπ' &%& %vl & Mt &?)]"; iExists vl; iFrame "Mt";
      [by iLeft|]. iRight. iExists vπ'. by iSplit.
  Qed.

  Program Definition maybe_uninit {A} (ty: type A) : type (option A) := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl :=
      ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl;
    ty_shr vπ d κ tid l :=
      ⌜vπ = const None⌝ ∨ ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_shr) vπ' d κ tid l;
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
    move=> *. iIntros "#LFT In Bor Tok". rewrite maybe_uninit_mt.
    iMod (bor_or with "LFT Bor") as "[Bor|Bor]"; first done.
    { iApply step_fupdN_full_intro.
      iMod (bor_sep_persistent with "LFT Bor Tok") as "(>->&?&$)"; by [|iLeft]. }
    iMod (bor_exists_tok with "LFT Bor Tok") as (vπ) "[Bor Tok]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor Tok") as "(>->& Bor & Tok)"; [done|].
    iMod (ty_share with "LFT In Bor Tok") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[?$] !>". iRight.
    iExists vπ. by iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT In [[->%]|(%vπ &->& Own)] Tok".
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). iIntros "_!>". iFrame "Tok". by iLeft. }
    iMod (ty_own_proph with "LFT In Own Tok") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%ξs & %q &%& PTok & Close) !>".
    iExists ξs, q. iSplit; [iPureIntro; by apply proph_dep_constr|].
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[?$]".
    iRight. iExists vπ. by iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT In In' [->|(%vπ &->& Shr)] Tok".
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). iIntros "_!>". iFrame "Tok". by iLeft. }
    iMod (ty_shr_proph with "LFT In In' Shr Tok") as "Upd"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%ξs&%q&%& PTok & Close) !>". iExists ξs, q.
    iSplit; [iPureIntro; by apply proph_dep_constr|]. iFrame "PTok". iIntros "PTok".
    iMod ("Close" with "PTok") as "[?$]". iRight. iExists vπ. by iFrame.
  Qed.

  Global Instance maybe_uninit_ne {A} : NonExpansive (@maybe_uninit A).
  Proof. solve_ne_type. Qed.

End maybe_uninit.

Notation "?" := maybe_uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance maybe_uninit_type_ne {A} : TypeNonExpansive (@maybe_uninit _ _ A).
  Proof.
    constructor; [by apply type_lft_morphism_id_like|done| |];
    [move=>/= > ->*|move=>/= >*]; by do 4 f_equiv.
  Qed.

  Global Instance maybe_uninit_send {A} (ty: _ A) : Send ty → Send (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.
  Global Instance maybe_uninit_sync {A} (ty: _ A) : Sync ty → Sync (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.

  Lemma maybe_uninit_subtype {A B} (f: A → B) ty ty' E L :
    subtype E L f ty ty' → subtype E L (option_map f) (? ty) (? ty').
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "(%&?& #InOwn & #InShr)".
    do 2 (iSplit; [done|]). iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%vπ' &->&?)]"; [by iLeft|]. iRight. iExists (f ∘ vπ').
      iSplit; [done|]. by iApply "InOwn".
    - iIntros "[->|(%vπ' &->&?)]"; [by iLeft|]. iRight. iExists (f ∘ vπ').
      iSplit; [done|]. by iApply "InShr".
  Qed.
  Lemma maybe_uninit_eqtype {A B} (f: A → B) g ty ty' E L :
    eqtype E L f g ty ty' → eqtype E L (option_map f) (option_map g) (? ty) (? ty').
  Proof. move=> [??]. split; by apply maybe_uninit_subtype. Qed.

  Lemma uninit_to_maybe_uninit {A} (ty: _ A) E L :
    subtype E L (const None) (↯ ty.(ty_size)) (? ty).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_static|].
    by iSplit; iIntros "!>*%/="; iLeft.
  Qed.

  Lemma into_maybe_uninit {A} (ty: _ A) E L : subtype E L Some ty (? ty).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*?/="; iRight; iExists vπ; by iFrame.
  Qed.

  Lemma maybe_uninit_join {A} (ty: _ A) E L :
    subtype E L (option_join _) (? (? ty)) (? ty).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%&->&[[->->]|(%vπ'' &->&?)])]"; [by iLeft|by iLeft|].
      iRight. iExists vπ''. by iFrame.
    - iIntros "[->|(%&->&[->|(%vπ'' &->&?)])]"; [by iLeft|by iLeft|].
      iRight. iExists vπ''. by iFrame.
  Qed.

End typing.

Global Hint Resolve maybe_uninit_subtype maybe_uninit_eqtype : lrust_typing.
