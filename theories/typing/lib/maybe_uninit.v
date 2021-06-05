From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section maybe_uninit.
  Context `{!typeG Σ}.

  Local Lemma maybe_uninit_mt {𝔄} (ty: type 𝔄) vπ d tid l q :
    (l ↦∗{q}: λ vl, ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl)%I ⊣⊢
    ⌜vπ = const None⌝ ∗ l ↦∗{q}: (λ vl, ⌜length vl = ty.(ty_size)⌝) ∨
    ∃vπ', ⌜vπ = Some ∘ vπ'⌝ ∗ l ↦∗{q}: ty.(ty_own) vπ' d tid.
  Proof.
    iSplit.
    - iIntros "(%vl &?&[[%%]|(%vπ' &%&?)])".
      { iLeft. iSplit; [done|]. iExists vl. by iFrame. }
      iRight. iExists vπ'. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "[(%& %vl & ↦ &%)|(%vπ' &%& %vl & ↦ &?)]"; iExists vl;
        iFrame "↦"; [by iLeft|].
      iRight. iExists vπ'. by iSplit.
  Qed.

  Program Definition maybe_uninit {𝔄} (ty: type 𝔄) : type (optionₛ 𝔄) := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl :=
      ⌜vπ = const None ∧ length vl = ty.(ty_size)⌝ ∨
      ∃vπ': proph 𝔄, ⌜vπ = Some ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl;
    ty_shr vπ d κ tid l :=
      ⌜vπ = const None⌝ ∗ uninit_shr κ l ty.(ty_size) 0 ∨
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
    move=> ? ty *. iIntros "#? [[-> ?]|(%vπ &?&?)]"; [iLeft|iRight].
    { iSplit; [done|]. by iApply uninit_shr_shorten. }
    iExists vπ. iSplit; [done|]. by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT In Bor κ". rewrite maybe_uninit_mt.
    iMod (bor_or with "LFT Bor") as "[Bor|Bor]"; first done.
    { iApply step_fupdN_full_intro.
      iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
      iMod (bor_to_uninit_shr with "LFT Bor κ") as "[?$]"; by [|iLeft; iFrame]. }
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
    iIntros "{$ξl}ξl". iMod ("Toty" with "ξl") as "[?$]".
    iRight. iExists vπ. by iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "LFT In In' [[-> ?]|(%vπ &->& ty)] κ".
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). iIntros "_!>". iFrame "κ". iLeft. by iFrame. }
    iMod (ty_shr_proph with "LFT In In' ty κ") as "Upd"; [done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%ξl&%q&%& ξl & Toty) !>". iExists ξl, q.
    iSplit; [iPureIntro; by apply proph_dep_constr|]. iIntros "{$ξl}ξl".
    iMod ("Toty" with "ξl") as "[?$]". iRight. iExists vπ. by iFrame.
  Qed.

  Global Instance maybe_uninit_ne {𝔄} : NonExpansive (@maybe_uninit 𝔄).
  Proof. solve_ne_type. Qed.
End maybe_uninit.

Notation "?" := maybe_uninit : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance maybe_uninit_type_ne {𝔄} : TypeNonExpansive (maybe_uninit (𝔄:=𝔄)).
  Proof.
    constructor; [by apply type_lft_morphism_id_like|done| |];
    move=>/= > ->*; by do 4 f_equiv.
  Qed.

  Global Instance maybe_uninit_copy {𝔄} (ty: type 𝔄) : Copy ty → Copy (? ty).
  Proof.
    move=> ?. split; [apply _|]=> *. iIntros "LFT [[-> shr]|(%&->& ty)] Na κ".
    - iMod (uninit_shr_acc with "LFT shr κ") as (???) "[↦ Toκ]"; [solve_ndisj|].
      iModIntro. iExists _, _.
      iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [set_solver+|]. iFrame "↦".
      iSplit; [by iLeft|]. iIntros "Na". by iDestruct ("ToNa" with "Na") as "$".
    - iMod (copy_shr_acc with "LFT ty Na κ") as (??) "($& ↦ &?& Toκ)"; [done..|].
      iModIntro. iExists _, _. iFrame "↦ Toκ". iNext. iRight. iExists _. by iFrame.
  Qed.

  Global Instance maybe_uninit_send {𝔄} (ty: type 𝔄) : Send ty → Send (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.
  Global Instance maybe_uninit_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (? ty).
  Proof. move=> >/=. by do 4 f_equiv. Qed.

  Lemma maybe_uninit_leak {𝔄} (ty: type 𝔄) Φ E L :
    leak E L ty Φ →
    leak E L (? ty) (λ o, match o with None => True | Some a => Φ a end).
  Proof.
    move=> Lk > ?. iIntros "LFT PROPH E L [[-> _]|(%&->& ty)]".
    { iApply step_fupdN_full_intro. iIntros "!>!>". iFrame "L".
      by iApply proph_obs_true. }
    iMod (Lk with "LFT PROPH E L ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). by iIntros "!> >[$$]".
  Qed.

  Lemma maybe_uninit_leak_just {𝔄} (ty: type 𝔄) E L :
    leak E L ty (const True) → leak E L (? ty) (const True).
  Proof. move=> ?. apply leak_just. Qed.

  Lemma maybe_uninit_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (? ty) (? ty') (option_map f).
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "(%EqSz &?& #InOwn & #InShr)".
    do 2 (iSplit; [done|]). iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%vπ' &->&?)]"; [by iLeft|]. iRight. iExists (f ∘ vπ').
      iSplit; [done|]. by iApply "InOwn".
    - iIntros "[[-> ?]|(%vπ' &->&?)]".
      + iLeft. rewrite EqSz. by iFrame.
      + iRight. iExists (f ∘ vπ'). iSplit; [done|]. by iApply "InShr".
  Qed.
  Lemma maybe_uninit_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (? ty) (? ty') (option_map f) (option_map g).
  Proof. move=> [??]. split; by apply maybe_uninit_subtype. Qed.

  Lemma uninit_to_maybe_uninit {𝔄} (ty: type 𝔄) E L :
    subtype E L (↯ ty.(ty_size)) (? ty) (const None).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_static|].
    iSplit; iIntros "!>** /="; iLeft; by iSplit.
  Qed.

  Lemma into_maybe_uninit {𝔄} (ty: type 𝔄) E L : subtype E L ty (? ty) Some.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*?/="; iRight; iExists vπ; by iFrame.
  Qed.

  Lemma maybe_uninit_join {𝔄} (ty: type 𝔄) E L :
    subtype E L (? (? ty)) (? ty) (option_join 𝔄).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/=".
    - iIntros "[[->->]|(%&->&[[->->]|(%vπ'' &->&?)])]"; [by iLeft..|].
      iRight. iExists vπ''. by iFrame.
    - iIntros "[[->?]|(%&->&[[->?]|(%vπ'' &->&?)])]"; [iLeft; by iFrame..|].
      iRight. iExists vπ''. by iFrame.
  Qed.
End typing.

Global Hint Resolve maybe_uninit_leak | 5 : lrust_typing.
Global Hint Resolve maybe_uninit_leak_just
  maybe_uninit_subtype maybe_uninit_eqtype : lrust_typing.
