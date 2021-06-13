From lrust.util Require Import basic.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Section refined.
  Context `{!typeG Σ}.

  Lemma split_refined_mt {𝔄} Φ (ty: type 𝔄) vπ d tid l q :
    (l ↦∗{q}: λ vl, ⟨π, Φ (vπ π)⟩ ∗ ty.(ty_own) vπ d tid vl)%I ⊣⊢
    ⟨π, Φ (vπ π)⟩ ∗ l ↦∗{q}: ty.(ty_own) vπ d tid.
  Proof. iSplit; [|iIntros "[$$]"]. iIntros "(%&?&$&?)". iExists _. iFrame. Qed.

  Program Definition refined {𝔄} (Φ: pred' 𝔄) (ty: type 𝔄) :={|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl := ⟨π, Φ (vπ π)⟩ ∗ ty.(ty_own) vπ d tid vl;
    ty_shr vπ d κ tid l := ⟨π, Φ (vπ π)⟩ ∗ ty.(ty_shr) vπ d κ tid l;
  |}%I.
  Next Obligation. iIntros "* [_ ?]". by rewrite ty_size_eq. Qed.
  Next Obligation. iIntros "*% [$?]". by iApply ty_own_depth_mono. Qed.
  Next Obligation. iIntros "*% [$?]". by iApply ty_shr_depth_mono. Qed.
  Next Obligation. iIntros "* #? [$?]". by iApply ty_shr_lft_mono. Qed.
  Next Obligation.
    iIntros "*% #LFT In Bor κ". rewrite split_refined_mt.
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>$& Bor & κ)"; [done|].
    by iApply (ty_share with "LFT In Bor κ").
  Qed.
  Next Obligation.
    iIntros "*% LFT In [$ ty] κ". by iApply (ty_own_proph with "LFT In ty κ").
  Qed.
  Next Obligation.
    iIntros "*% LFT In In' [$ ty] κ". by iApply (ty_shr_proph with "LFT In In' ty κ").
  Qed.

  Global Instance refined_ne {𝔄} (Φ: 𝔄 → _) : NonExpansive (refined Φ).
  Proof. solve_ne_type. Qed.
End refined.

Notation "!{ Φ }" := (refined Φ) (format "!{ Φ }"): lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance refined_type_ne {𝔄} (Φ: 𝔄 → _) : TypeNonExpansive !{Φ}%T.
  Proof.
    split=>/= *; [by apply type_lft_morphism_id_like|done|by f_equiv..].
  Qed.

  Global Instance refined_send {𝔄} (Φ: 𝔄 → _) ty : Send ty → Send (!{Φ} ty).
  Proof. move=> ?>/=. by f_equiv. Qed.

  Global Instance refined_sync {𝔄} (Φ: 𝔄 → _) ty : Sync ty → Sync (!{Φ} ty).
  Proof. move=> ?>/=. by f_equiv. Qed.

  Lemma refined_leak {𝔄} (Φ: 𝔄 → _) ty Ψ E L :
    leak E L ty Ψ → leak E L (!{Φ} ty) Ψ.
  Proof.
    iIntros (Lk) "* LFT PROPH E L [_ ty]". by iApply (Lk with "LFT PROPH E L ty").
  Qed.

  Lemma refined_real {𝔄 𝔅} Φ (f: 𝔄 → 𝔅) ty E L :
    real E L ty f → real E L (!{Φ} ty) f.
  Proof.
    move=> [Rlo Rls]. split; iIntros "*% LFT E L [$ ty]";
    by [iApply (Rlo with "LFT E L ty")|iApply (Rls with "LFT E L ty")].
  Qed.

  Lemma refined_subtype {𝔄 𝔅} (Φ Ψ: _ → Prop) (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → (∀a, Φ a → Ψ (f a)) →
    subtype E L (!{Φ} ty) (!{Ψ} ty') f.
  Proof.
    iIntros (Sub Imp ?) "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> E". iDestruct ("Sub" with "E") as "(%&?& #InOwn & #InShr)".
    do 2 (iSplit; [done|]).
    iSplit; iIntros "!>*[??]"; iSplit; [|by iApply "InOwn"| |by iApply "InShr"];
    (iApply proph_obs_impl; [|done]=>/= ?; apply Imp).
  Qed.
  Lemma refined_eqtype {𝔄 𝔅} (Φ Ψ: _ → Prop) (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → (∀a, Φ a → Ψ (f a)) → (∀a, Ψ a → Φ (g a)) →
    eqtype E L (!{Φ} ty) (!{Ψ} ty') f g.
  Proof. move=> [??]??. split; by apply refined_subtype. Qed.

  Lemma refined_forget {𝔄} (Φ: 𝔄 → _) ty E L : subtype E L (!{Φ} ty) ty id.
  Proof.
    iIntros "% _!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>* [_$]".
  Qed.

  Lemma tctx_refined_out {𝔄 𝔅l} (Φ: 𝔄 → _) ty E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ !{Φ} ty +:: T) (p ◁ ty +:: T)
      (λ post '(a -:: bl), Φ a → post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by apply forall_proper=> ?. }
    iIntros (??[??]?) "_ _ _ _ $ /=[(%&%&%&?& Obs &?) T] Obs' !>".
    iCombine "Obs Obs'" as "Obs". iExists (_-::_). iFrame "T".
    iSplit. { iExists _, _. by iFrame. }
    iApply proph_obs_impl; [|done]=>/= ?[? Imp]. by apply Imp.
  Qed.

  Lemma tctx_refined_in {𝔄 𝔅l} (Φ: 𝔄 → _) ty E L (T: tctx 𝔅l) p :
    tctx_incl E L (p ◁ ty +:: T) (p ◁ !{Φ} ty +:: T)
      (λ post '(a -:: bl), Φ a ∧ post (a -:: bl)).
  Proof.
    split. { move=>/= ???[??]. by f_equiv. }
    iIntros (??[??]?) "_ _ _ _ $ /=[(%&%&%& ⧖ & ty) T] Obs !>".
    iExists (_-::_). iFrame "T". iSplit; last first.
    { by iApply proph_obs_impl; [|done]=>/= ?[_ ?]. }
    iExists _, _. iSplit; [done|]. iFrame "⧖ ty".
    by iApply proph_obs_impl; [|done]=>/= ?[? _].
  Qed.

  Lemma tctx_extract_refined_out {𝔄 𝔅l} (Φ: 𝔄 → _) ty E L (T: tctx 𝔅l) p :
    tctx_extract_elt E L (p ◁ ty) (p ◁ !{Φ} ty +:: T) T
      (λ post '(a -:: bl), Φ a → post (a -:: bl)).
  Proof. apply tctx_refined_out. Qed.

  Lemma tctx_extract_refined_in {𝔄 𝔅l} (Φ: 𝔄 → _) ty E L (T: tctx 𝔅l) p :
    tctx_extract_elt E L (p ◁ !{Φ} ty) (p ◁ ty +:: T) T
      (λ post '(a -:: bl), Φ a ∧ post (a -:: bl)).
  Proof. apply tctx_refined_in. Qed.
End typing.

Global Hint Resolve refined_forget | 20 : lrust_typing.
Global Hint Resolve tctx_extract_refined_out tctx_extract_refined_in | 20
  : lrust_typing.
Global Hint Resolve refined_leak refined_real refined_subtype refined_eqtype
  : lrust_typing.
