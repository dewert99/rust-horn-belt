From lrust.util Require Import basic.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

Global Instance compose_inj {A B C} f `{Inj A B (=) (=) f} : @Inj (C → A) (C → B) (=) (=) (compose f).
Proof. intros ???. fun_ext. intros ?. apply (inj f). specialize (equal_f H0 x0). done. Qed.

Section mod_ty.
  Context `{!typeG Σ}.

  Class SameLevel 𝔄 𝔅 : Prop := {same_level: ghost_level 𝔅 = ghost_level 𝔄}.

  Global Instance same_level_refl 𝔄 : SameLevel 𝔄 𝔄.
  Proof. done. Qed. 

  Lemma split_mt_mod_ty {𝔄 𝔅} (f: 𝔄 → 𝔅) ty vπ' d tid l :
    (l ↦∗: λ vl, ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ ty.(ty_own) vπ d tid vl) ⊣⊢
    ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ l ↦∗: ty.(ty_own) vπ d tid.
  Proof.
    iSplit.
    - iIntros "(%vl &?& %vπ &->&?)". iExists vπ. iSplit; [done|]. iExists vl. iFrame.
    - iIntros "(%vπ &->& %vl & ↦ &?)". iExists vl. iFrame "↦". iExists vπ.
      by iSplit; [done|].
  Qed.

  Program Definition mod_ty `{SameLevel 𝔄 𝔅} (f: 𝔄 → 𝔅) (ty: type 𝔄) : type 𝔅 := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E); 
    ty_proph vπ ξl := exists vπ', vπ = f ∘ vπ' /\ ty.(ty_proph) vπ' ξl;
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
    move=> */=. iIntros "#LFT In Bor κ". rewrite split_mt_mod_ty.
    iMod (bor_exists_tok with "LFT Bor κ") as (vπ) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (ty_share with "LFT In Bor κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[? $] !>". iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In [%vπ[->ty]] κ".
    iMod (ty_own_proph with "LFT In ty κ") as "Upd"; [done|]. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q ?) "[ξl Toty]".
    iModIntro. iExists ξl, q. iSplit; [by iExists _|].
    iIntros "{$ξl}ξl". iMod ("Toty" with "ξl") as "[? $]".
    iModIntro. iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In In' [%vπ[->ty]] κ".
    iMod (ty_shr_proph with "LFT In In' ty κ") as "Upd"; [done|]. iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q ?) "[ξl Toκ]".
    iModIntro. iExists ξl, q. iSplit; [by iExists _|].
    iIntros "{$ξl}ξl". by iMod ("Toκ" with "ξl").
  Qed.
  Next Obligation. move=> /= ???????[?[->?]]. rewrite same_level. by eapply proph_dep_constr, ty_proph_weaken. Qed.

  Global Instance mod_ty_ne `{SameLevel 𝔄 𝔅} (f: 𝔄 → 𝔅) : NonExpansive (mod_ty f).
  Proof. solve_ne_type. Qed.
End mod_ty.

Notation "<{ f }>" := (mod_ty f) (format "<{ f }>"): lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma mod_ty_own' `{SameLevel 𝔄 𝔅} g f `{!@SemiIso 𝔄 𝔅 f g} ty vπ d tid vl :
    (<{f}> ty).(ty_own) vπ d tid vl ⊢ ty.(ty_own) (g ∘ vπ) d tid vl.
  Proof. iIntros "[%[->?]]". by rewrite compose_assoc semi_iso. Qed.
  Lemma mod_ty_own `{SameLevel 𝔄 𝔅} g f `{!@Iso 𝔄 𝔅 f g} ty vπ d tid vl :
    (<{f}> ty).(ty_own) vπ d tid vl ⊣⊢ ty.(ty_own) (g ∘ vπ) d tid vl.
  Proof.
    iSplit; [by iApply mod_ty_own'|]. iIntros "ty". iExists _. iFrame "ty".
    by rewrite compose_assoc semi_iso.
  Qed.

  Lemma mod_ty_shr' `{SameLevel 𝔄 𝔅} g f `{!@SemiIso 𝔄 𝔅 f g} ty vπ d κ tid l :
    (<{f}> ty).(ty_shr) vπ d κ tid l ⊢ ty.(ty_shr) (g ∘ vπ) d κ tid l.
  Proof. iIntros "[%[->?]]". by rewrite compose_assoc semi_iso. Qed.
  Lemma mod_ty_shr `{SameLevel 𝔄 𝔅} g f `{!@Iso 𝔄 𝔅 f g} ty vπ d κ tid l :
    (<{f}> ty).(ty_shr) vπ d κ tid l ⊣⊢ ty.(ty_shr) (g ∘ vπ) d κ tid l.
  Proof.
    iSplit; [by iApply mod_ty_shr'|]. iIntros "ty". iExists _. iFrame "ty".
    by rewrite compose_assoc semi_iso.
  Qed.

  Lemma mod_ty_proph' `{SameLevel 𝔄 𝔅} g f `{!@SemiIso 𝔄 𝔅 f g} ty vπ ξl :
    (<{f}> ty).(ty_proph) vπ ξl → ty.(ty_proph) (g ∘ vπ) ξl.
  Proof. intros [? [-> ?]]. by rewrite compose_assoc semi_iso. Qed.
  Lemma mod_ty_proph `{SameLevel 𝔄 𝔅} g f `{!@Iso 𝔄 𝔅 f g} ty vπ ξl :
    (<{f}> ty).(ty_proph) vπ ξl ↔ ty.(ty_proph) (g ∘ vπ) ξl.
  Proof.
    split; [apply mod_ty_proph'; apply H0|]. intros ty_p. eexists _. split; [|done].
    by rewrite compose_assoc semi_iso.
  Qed.

  Global Instance mod_ty_type_ne `{SameLevel 𝔄 𝔅} (f: 𝔄 → 𝔅) : TypeNonExpansive <{f}>%T.
  Proof.
    split; [|split|..]; simpl; intros; [|apply type_lft_morphism_id_like|do 3 f_equiv| |do 3 f_equiv|do 3 f_equiv]; try done.
    destruct H0 as (vπ'&->&?). exists [vπ'], [ξ]. intuition. eexists _. inversion_clear H1. done.
  Qed.

  Global Instance mod_ty_copy `{SameLevel 𝔄 𝔅} (f: 𝔄 → 𝔅) ty : Copy ty → Copy (<{f}> ty).
  Proof.
    move=> [? ShrAcc]. split; [by apply _|]=> */=. iIntros "LFT [%vπ[->ty]] Na κ".
    iMod (ShrAcc with "LFT ty Na κ") as (q vl) "($& ↦ &?& Toκ)"; [done|done|].
    iModIntro. iExists q, vl. iFrame "↦ Toκ". iNext. iExists vπ. by iSplit.
  Qed.

  Global Instance mod_ty_send `{SameLevel 𝔄 𝔅} (f: 𝔄 → 𝔅) ty : Send ty → Send (<{f}> ty).
  Proof. move=> ?>/=. by do 3 f_equiv. Qed.

  Global Instance mod_ty_sync `{SameLevel 𝔄 𝔅} (f: 𝔄 → 𝔅) ty : Sync ty → Sync (<{f}> ty).
  Proof. move=> ?>/=. by do 3 f_equiv. Qed.

  Lemma mod_ty_resolve' `{SameLevel 𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty Φ :
    resolve E L ty Φ → resolve E L (<{f}> ty) (λ b, ∃a, b = f a ∧ Φ a).
  Proof.
    move=> Rslv > ?. iIntros "LFT PROPH E L (%&->& ty)".
    iMod (Rslv with "LFT PROPH E L ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). iIntros "!> >[Obs $] !>".
    iApply proph_obs_impl; [|done]=>/= ??. by eexists _.
  Qed.

  Lemma mod_ty_resolve `{SameLevel 𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty Φ :
    resolve E L ty Φ → resolve E L (<{f}> ty) (Φ ∘ g).
  Proof.
    move=> ?. eapply resolve_impl; [by apply mod_ty_resolve'|]=>/=
    ?[?[/(f_equal g) + ?]]. by rewrite semi_iso'=> ->.
  Qed.

  Lemma mod_ty_resolve_just `{SameLevel 𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty :
    resolve E L ty (const True) → resolve E L (<{f}> ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma mod_ty_real `{SameLevel 𝔄 𝔅} {ℭ} E L f g `{!@Iso 𝔄 𝔅 f g} (h: _ → ℭ) ty :
    real E L ty h → real E L (<{f}> ty) (h ∘ g).
  Proof.
    move=> [Rlo Rls]. split.
    - iIntros "*% LFT E L ty". rewrite mod_ty_own.
      iMod (Rlo with "LFT E L ty") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). by iIntros "!> >($&$&$)".
    - iIntros "*% LFT E L ty". rewrite mod_ty_shr.
      iMod (Rls with "LFT E L ty") as "Upd"; [done|]. iIntros "!>!>".
      iApply (step_fupdN_wand with "Upd"). by iIntros ">($&$&$)".
  Qed.

  Lemma mod_ty_id {𝔄} (ty: type 𝔄) : <{id}>%T ty ≡ ty.
  Proof. split; move=>// *; by [rewrite mod_ty_proph|rewrite mod_ty_own|rewrite mod_ty_shr]. Qed.

  Local Instance same_level_trans 𝔄 𝔅 ℭ `{SameLevel 𝔄 𝔅} `{SameLevel 𝔅 ℭ} : SameLevel 𝔄 ℭ.
  Proof. eassert (_ = _); [|done]. transitivity (ghost_level 𝔅); apply same_level. Qed. 

  Lemma mod_ty_compose `{SameLevel 𝔄 𝔅} `{SameLevel 𝔅 ℭ} (f: 𝔄 → 𝔅) (g: 𝔅 → ℭ) ty :
    (<{g}> (<{f}> ty) ≡ <{g ∘ f}> ty)%T.
  Proof.
    split=>// *; [shelve | |]; (iSplit=>/=; [
      iIntros "(%&->& %vπ &->&?)"; iExists vπ; by iFrame|
      iIntros "[%vπ[->?]]"; iExists (f ∘ vπ); (iSplit; [done|]); iExists vπ; by iFrame
    ]).
    Unshelve. split.
    intros (?&->&?&->&?). eexists; split; [|done]. by rewrite compose_assoc.
    intros (?&->&?). eexists; split. done. eexists; split; [|done]. done.
  Qed.

  Lemma mod_ty_in `{SameLevel 𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty : subtype E L ty (<{f}> ty) f.
  Proof.
    iIntros "*_!>_". iSplit. iPureIntro. split. done.
    intros ???. exists vπ. done.
    iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>" (vπ) "*?"; iExists vπ; by iSplit.
  Qed.
  Lemma mod_ty_blocked_in `{SameLevel 𝔄 𝔅} (f: 𝔄 → 𝔅) `{Inj _ _ (=) (=) f} ty : blocked_subtype ty (<{f}> ty) f.
  Proof.
    split; [done|]. intros ?? (?&?&?). 
    apply compose_inj in H1; [|done]. by rewrite H1.
  Qed.

  Lemma mod_ty_out `{SameLevel 𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty :
    subtype E L (<{f}> ty) ty g.
  Proof.
    iIntros "*_!>_".
    iSplit. iPureIntro. split; [done|]. intros ?? (?&->&?). by rewrite compose_assoc semi_iso.
    iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/=[%[->?]]"; by rewrite compose_assoc semi_iso.
  Qed.
  Lemma mod_ty_blocked_out `{SameLevel 𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty :
    blocked_subtype (<{f}> ty) ty g.
  Proof.
    split; [apply semi_iso_inj|]. intros. exists (g ∘ vπ). by rewrite compose_assoc semi_iso.
  Qed.

  Lemma mod_ty_inout `{SameLevel 𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty :
    eqtype E L ty (<{f}> ty) f g.
  Proof. by split; [apply mod_ty_in|apply mod_ty_out]. Qed.
  Lemma mod_ty_outin `{SameLevel 𝔄 𝔅} E L f g `{!@SemiIso 𝔄 𝔅 f g} ty :
    eqtype E L (<{f}> ty) ty g f.
  Proof. by apply eqtype_symm, mod_ty_inout. Qed.
  Lemma mod_ty_blocked_inout `{SameLevel 𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty :
    blocked_eqtype ty (<{f}> ty) f g.
  Proof. by split; [apply mod_ty_blocked_in; apply semi_iso_inj |apply mod_ty_blocked_out]. Qed.
  Lemma mod_ty_blocked_outin `{SameLevel 𝔄 𝔅} f g `{!@Iso 𝔄 𝔅 f g} ty :
    blocked_eqtype (<{f}> ty) ty g f.
  Proof. by apply blocked_eqtype_symm, mod_ty_blocked_inout. Qed.

  Lemma mod_ty_subtype `{SameLevel 𝔄 𝔅} `{SameLevel 𝔄' 𝔅'} E L h
      f f' g `{!@SemiIso 𝔄 𝔅 f g} ty ty' :
    subtype E L ty ty' h → subtype E L (<{f}> ty) (<{f'}> ty') (f' ∘ h ∘ g).
  Proof.
    move=> ??. eapply subtype_trans; [by apply mod_ty_out|].
    eapply subtype_trans; by [|apply mod_ty_in].
  Qed.

  Lemma mod_ty_eqtype `{SameLevel 𝔄 𝔅} `{SameLevel 𝔄' 𝔅'} E L h h' f f' g g'
      `{!@SemiIso 𝔄 𝔅 f g} `{!@SemiIso 𝔄' 𝔅' f' g'} ty ty' :
    eqtype E L ty ty' h h' →
    eqtype E L (<{f}> ty) (<{f'}> ty') (f' ∘ h ∘ g) (f ∘ h' ∘ g').
  Proof. move=> [??]. split; apply mod_ty_subtype; try done. Qed.

  Lemma mod_ty_blocked_subtype `{SameLevel 𝔄 𝔅} `{SameLevel 𝔄' 𝔅'} h
      f f' `{Inj 𝔄' 𝔅' (=) (=) f'} g `{!@Iso 𝔄 𝔅 f g} ty ty' :
    blocked_subtype ty ty' h → blocked_subtype (<{f}> ty) (<{f'}> ty') (f' ∘ h ∘ g).
  Proof.
    move=> ?. eapply blocked_subtype_trans; [by apply mod_ty_blocked_out|].
    eapply blocked_subtype_trans; by [|apply mod_ty_blocked_in].
  Qed.

  Lemma mod_ty_blockedeqtype `{SameLevel 𝔄 𝔅} `{SameLevel 𝔄' 𝔅'} h h' f f' g g'
      `{!@Iso 𝔄 𝔅 f g} `{!@Iso 𝔄' 𝔅' f' g'} ty ty' :
    blocked_eqtype ty ty' h h' →
    blocked_eqtype (<{f}> ty) (<{f'}> ty') (f' ∘ h ∘ g) (f ∘ h' ∘ g').
  Proof. move=> [??]. split; apply mod_ty_blocked_subtype; try done; apply semi_iso_inj. Qed.
End typing.

Global Hint Resolve mod_ty_in mod_ty_out mod_ty_inout mod_ty_outin
  | 20 : lrust_typing.
Global Hint Resolve mod_ty_resolve | 5 : lrust_typing.
Global Hint Resolve mod_ty_resolve_just mod_ty_subtype mod_ty_eqtype
  : lrust_typing.
