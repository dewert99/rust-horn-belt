From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section mod_ty.
  Context `{!typeG Σ}.

  Local Lemma mod_ty_mt {A B} (f: A → B) ty vπ' d tid l q :
    (l ↦∗{q}: λ vl, ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ ty.(ty_own) (vπ,d) tid vl)%I ⊣⊢
    ∃vπ, ⌜vπ' = f ∘ vπ⌝ ∗ l ↦∗{q}: ty.(ty_own) (vπ,d) tid.
  Proof. iSplit.
    - iDestruct 1 as (vl) "[Mt Own]". iDestruct "Own" as (vπ->) "Own".
      iExists vπ. iSplit; [done|]. iExists vl. iFrame.
    - iDestruct 1 as (vπ->vl) "[Mt Own]". iExists vl. iFrame "Mt". iExists vπ.
      by iSplit; [done|].
  Qed.

  Program Definition mod_ty {A B} (f: A → B) (ty: type A) : type B := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπd tid vl := ∃vπ, ⌜vπd.1 = f ∘ vπ⌝ ∗ ty.(ty_own) (vπ,vπd.2) tid vl;
    ty_shr vπd κ tid l := ∃vπ, ⌜vπd.1 = f ∘ vπ⌝ ∗ ty.(ty_shr) (vπ,vπd.2) κ tid l;
  |}%I.
  Next Obligation. move=> *. iDestruct 1 as (??) "?". by iApply ty_size_eq. Qed.
  Next Obligation.
    move=> */=. iDestruct 1 as (vπ->) "?". iExists vπ. iSplit; [done|].
    by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iDestruct 1 as (vπ->) "?". iExists vπ. iSplit; [done|].
    by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#?". iDestruct 1 as (vπ->) "?". iExists vπ. iSplit; [done|].
    by iApply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In Bor Tok". rewrite mod_ty_mt.
    iMod (bor_exists_tok with "LFT Bor Tok") as (vπ) "[Bor Tok]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor Tok") as "[>->[Bor Tok]]"; [done|].
    iMod (ty_share with "LFT In Bor Tok") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[Shr $] !>". iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In". iDestruct 1 as (vπ->) "Own". iIntros "Tok".
    iMod (ty_own_proph with "LFT In Own Tok") as "Upd"; [done|]. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q ?) "[PTok Close]".
    iModIntro. iExists ξs, q. iSplit; [iPureIntro; by apply (proph_dep_constr _)|].
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[Own $]".
    iModIntro. iExists vπ. by iSplit.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In In'". iDestruct 1 as (vπ->) "Shr". iIntros "Tok".
    iMod (ty_shr_proph with "LFT In In' Shr Tok") as "Upd"; [done|]. iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q ?) "[PTok Close]".
    iModIntro. iExists ξs, q. iSplit; [iPureIntro; by apply (proph_dep_constr _)|].
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[Own $]".
    iModIntro. iExists vπ. by iSplit.
  Qed.

  Global Instance mod_ty_type_nonexpansive {A B} (f: A → B) : TypeNonExpansive (mod_ty f).
  Proof. split; [|done|move=> */=; by do 3 f_equiv|move=> */=; by do 3 f_equiv].
    apply (type_lft_morphism_add _ static [] [])=> ?.
    - rewrite left_id. apply lft_equiv_refl.
    - by rewrite /elctx_interp /= left_id right_id.
  Qed.

  Global Instance mod_ty_ne {A B} (f: A → B) : NonExpansive (mod_ty f).
  Proof. solve_ne_type. Qed.

End mod_ty.

Section typing.
  Context `{!typeG Σ}.

  Global Instance mod_ty_copy {A B} (f: A → B) ty : Copy ty → Copy (mod_ty f ty).
  Proof.
    move=> [? ShrAcc]. split; [by apply _|]. move=> */=. iIntros "LFT".
    iDestruct 1 as (vπ ->) "Shr". iIntros "Na Tok".
    iMod (ShrAcc with "LFT Shr Na Tok") as (q vl) "[$[Mt[? Close]]]"; [done|done|].
    iModIntro. iExists q, vl. iFrame "Mt Close". iNext. iExists vπ. by iSplit.
  Qed.

  Global Instance mod_ty_send {A B} (f: A → B) ty : Send ty → Send (mod_ty f ty).
  Proof. move=> ??*/=. by do 3 f_equiv. Qed.

  Global Instance mod_ty_sync {A B} (f: A → B) ty : Sync ty → Sync (mod_ty f ty).
  Proof. move=> ??*/=. by do 3 f_equiv. Qed.

  Lemma mod_ty_subtype_in {A B} E L (f: A → B) ty : subtype E L f ty (mod_ty f ty).
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>" (vπ) "*?"; iExists vπ; by iSplit.
  Qed.

  Lemma mod_ty_subtype_out {A B} E L (f: A → B) g ty :
    g ∘ f = id → subtype E L g (mod_ty f ty) ty.
  Proof.
    move=> Eq. iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*/="; iDestruct 1 as (vπ'->) "?"; by rewrite compose_assoc Eq.
  Qed.

  Lemma mod_ty_eqtype_inout {A B} E L (f: A → B) g ty :
    g ∘ f = id → eqtype E L f g ty (mod_ty f ty).
  Proof. move=> ?. by split; [apply mod_ty_subtype_in|apply mod_ty_subtype_out]. Qed.

  Lemma mod_ty_subtype {A B A' B'} E L h (f: A → B) (f': A' → B') g ty ty' :
    g ∘ f = id → subtype E L h ty ty' →
    subtype E L (f' ∘ h ∘ g) (mod_ty f ty) (mod_ty f' ty').
  Proof.
    move=> ??. eapply subtype_trans; [by apply mod_ty_subtype_out|].
    eapply subtype_trans; by [|apply mod_ty_subtype_in].
  Qed.

  Lemma mod_ty_eqtype {A B A' B'} E L h h' (f: A → B) (f': A' → B') g g' ty ty' :
    g ∘ f = id → g' ∘ f' = id → eqtype E L h h' ty ty' →
    eqtype E L (f' ∘ h ∘ g) (f ∘ h' ∘ g') (mod_ty f ty) (mod_ty f' ty').
  Proof. move=> ??[??]. split; by apply mod_ty_subtype. Qed.

End typing.
