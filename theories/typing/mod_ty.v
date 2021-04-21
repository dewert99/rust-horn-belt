From lrust.util Require Import basic.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section mod_ty.
  Context `{!typeG TYPE Ty Σ}.

  Local Lemma mod_ty_mt {A B} (f: A → B) ty vπ' d tid l q :
    (l ↦∗{q}: λ vl, ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ ty.(ty_own) vπ d tid vl)%I ⊣⊢
    ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ l ↦∗{q}: ty.(ty_own) vπ d tid.
  Proof. iSplit.
    - iIntros "(%vl &?& %vπ &->&?)". iExists vπ. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "(%vπ &->& %vl & Mt &?)". iExists vl. iFrame "Mt". iExists vπ.
      by iSplit; [done|].
  Qed.

  Program Definition mod_ty {A B} (f: A → B) (ty: type A) : type B := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl := ∃vπ', ⌜vπ = f ∘ vπ'⌝ ∗ ty.(ty_own) vπ' d tid vl;
    ty_shr vπ d κ tid l := ∃vπ', ⌜vπ = f ∘ vπ'⌝ ∗ ty.(ty_shr) vπ' d κ tid l;
  |}%I.
  Next Obligation. move=> *. iIntros "[%[%?]]". by iApply ty_size_eq. Qed.
  Next Obligation.
    move=> */=. iIntros "[%vπ[->?]]". iExists vπ. iSplit; [done|].
    by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "[%vπ[->?]]". iExists vπ. iSplit; [done|].
    by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#? [%vπ[->?]]". iExists vπ. iSplit; [done|].
    by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In Bor Tok". rewrite mod_ty_mt.
    iMod (bor_exists_tok with "LFT Bor Tok") as (vπ) "[Bor Tok]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor Tok") as "(>-> & Bor & Tok)"; [done|].
    iMod (ty_share with "LFT In Bor Tok") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[Shr $] !>". iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In [%vπ[->Own]] Tok".
    iMod (ty_own_proph with "LFT In Own Tok") as "Upd"; [done|]. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q ?) "[PTok Close]".
    iModIntro. iExists ξs, q. iSplit; [iPureIntro; by apply (proph_dep_constr _)|].
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[Own $]".
    iModIntro. iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In In' [%vπ[->Shr]] Tok".
    iMod (ty_shr_proph with "LFT In In' Shr Tok") as "Upd"; [done|]. iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q ?) "[PTok Close]".
    iModIntro. iExists ξs, q. iSplit; [iPureIntro; by apply (proph_dep_constr _)|].
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[Own $]".
    iModIntro. iExists vπ. by iSplit.
  Qed.

  Global Instance mod_ty_ne {A B} (f: A → B) : NonExpansive (mod_ty f).
  Proof. solve_ne_type. Qed.

End mod_ty.

Notation "<{ f }>" := (mod_ty f) (format "<{ f }>"): lrust_type_scope.

Section typing.
  Context `{!typeG TYPE Ty Σ}.

  Global Instance mod_ty_type_ne {A B} (f: A → B) : TypeNonExpansive <{f}>%T.
  Proof.
    split=>/= *; by [apply type_lft_morphism_id_like| |do 3 f_equiv|do 3 f_equiv].
  Qed.

  Global Instance mod_ty_copy {A B} (f: A → B) ty : Copy ty → Copy (<{f}> ty).
  Proof.
    move=> [? ShrAcc]. split; [by apply _|]=> */=. iIntros "LFT [%vπ[->Shr]] Na Tok".
    iMod (ShrAcc with "LFT Shr Na Tok") as (q vl) "($& Mt &?& Close)"; [done|done|].
    iModIntro. iExists q, vl. iFrame "Mt Close". iNext. iExists vπ. by iSplit.
  Qed.

  Global Instance mod_ty_send {A B} (f: A → B) ty : Send ty → Send (<{f}> ty).
  Proof. move=> ??*/=. by do 3 f_equiv. Qed.

  Global Instance mod_ty_sync {A B} (f: A → B) ty : Sync ty → Sync (<{f}> ty).
  Proof. move=> ??*/=. by do 3 f_equiv. Qed.

  Lemma mod_ty_own {A B} g f `{@Iso A B f g} ty vπ d tid vl :
    (<{f}> ty).(ty_own) vπ d tid vl ⊣⊢ ty.(ty_own) (g ∘ vπ) d tid vl.
  Proof. iSplit=>/=.
    - iIntros "[%[->?]]". by rewrite compose_assoc semi_iso.
    - iIntros "?". iExists (g ∘ vπ). iFrame. by rewrite compose_assoc semi_iso.
  Qed.
  Lemma mod_ty_shr {A B} g f `{@Iso A B f g} ty vπ d κ tid l :
    (<{f}> ty).(ty_shr) vπ d κ tid l ⊣⊢ ty.(ty_shr) (g ∘ vπ) d κ tid l.
  Proof. iSplit=>/=.
    - iIntros "[%[->?]]". by rewrite compose_assoc semi_iso.
    - iIntros "?". iExists (g ∘ vπ). iFrame. by rewrite compose_assoc semi_iso.
  Qed.

  Lemma mod_ty_id {A} (ty: _ A) : <{id}>%T ty ≡ ty.
  Proof. split; move=>// *; by [rewrite mod_ty_own|rewrite mod_ty_shr]. Qed.

  Lemma mod_ty_compose {A B C} (f: A → B) (g: _ → C) ty :
    (<{g}> (<{f}> ty) ≡ <{g ∘ f}> ty)%T.
  Proof.
    split=>// *; (iSplit=>/=; [
      iIntros "(%&->& %vπ &->&?)"; iExists vπ; by iFrame|
      iIntros "[%vπ[->?]]"; iExists (f ∘ vπ); (iSplit; [done|]); iExists vπ; by iFrame
    ]).
  Qed.

  Lemma mod_ty_in {A B} E L (f: A → B) ty : subtype E L f ty (<{f}> ty).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>" (vπ) "*?"; iExists vπ; by iSplit.
  Qed.

  Lemma mod_ty_out {A B} E L f g `{@SemiIso A B f g} ty :
    subtype E L g (<{f}> ty) ty.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/=[%[->?]]"; by rewrite compose_assoc semi_iso.
  Qed.

  Lemma mod_ty_inout {A B} E L f g `{@SemiIso A B f g} ty :
    eqtype E L f g ty (<{f}> ty).
  Proof. by split; [apply mod_ty_in|apply mod_ty_out]. Qed.
  Lemma mod_ty_outin {A B} E L f g `{@SemiIso A B f g} ty :
    eqtype E L g f (<{f}> ty) ty.
  Proof. by apply eqtype_symm, mod_ty_inout. Qed.

  Lemma mod_ty_subtype {A B A' B'} E L h f (f': A' → B') g `{SemiIso A B f g} ty ty' :
    subtype E L h ty ty' → subtype E L (f' ∘ h ∘ g) (<{f}> ty) (<{f'}> ty').
  Proof.
    move=> ??. eapply subtype_trans; [by apply mod_ty_out|].
    eapply subtype_trans; by [|apply mod_ty_in].
  Qed.

  Lemma mod_ty_eqtype {A B A' B'} E L h h' f f' g g'
    `{SemiIso A B f g} `{SemiIso A' B' f' g'} ty ty' :
    eqtype E L h h' ty ty' →
    eqtype E L (f' ∘ h ∘ g) (f ∘ h' ∘ g') (<{f}> ty) (<{f'}> ty').
  Proof. move=> [??]. split; by apply mod_ty_subtype. Qed.

End typing.

Global Hint Resolve mod_ty_subtype mod_ty_eqtype : lrust_typing.
