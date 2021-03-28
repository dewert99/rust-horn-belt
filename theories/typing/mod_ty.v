From iris.proofmode Require Import tactics.
From lrust.util Require Import basic.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section mod_ty.
  Context `{!typeG Σ}.

  Program Definition mod_ty {A B} (f: A → B) `{!Inj (=) (=) f} (ty: type B) : type A := {|
    ty_size := ty.(ty_size);  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπd tid vl := ty.(ty_own) (f ∘ vπd.1, vπd.2) tid vl;
    ty_shr vπd κ tid l := ty.(ty_shr) (f ∘ vπd.1, vπd.2) κ tid l;
  |}%I.
  Next Obligation. move=> *. apply ty_size_eq. Qed.
  Next Obligation. move=> *. by apply ty_own_depth_mono. Qed.
  Next Obligation. move=> *. by apply ty_shr_depth_mono. Qed.
  Next Obligation. move=> *. apply ty_shr_lft_mono. Qed.
  Next Obligation.  move=> *. by apply ty_share. Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In Own Tok".
    iMod (ty_own_proph with "LFT In Own Tok") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iModIntro. iMod 1 as (ξs q ?) "[PTok Close]".
    iModIntro. iExists ξs, q. iSplit; [iPureIntro; by apply (proph_dep_destr _)|iFrame].
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT In In' Shr Tok".
    iMod (ty_shr_proph with "LFT In In' Shr Tok") as "Upd"; [done|]. iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q ?) "[PTok Close]".
    iModIntro. iExists ξs, q. iSplit; [iPureIntro; by apply (proph_dep_destr _)|iFrame].
  Qed.

  Global Instance mod_ty_type_nonexpansive `{Inj A B (=) (=) f} :
    TypeNonExpansive (mod_ty f).
  Proof. split; [|done|by move=> */=|by move=> */=].
    apply (type_lft_morphism_add _ static [] [])=> ?.
    - rewrite left_id. apply lft_equiv_refl.
    - by rewrite /elctx_interp /= left_id right_id.
  Qed.

  Global Instance mod_ty_ne `{Inj A B (=) (=) f} : NonExpansive (mod_ty f).
  Proof. solve_ne_type. Qed.

End mod_ty.

Section typing.
  Context `{!typeG Σ}.

  Global Instance mod_ty_copy `{Inj A B (=) (=) f} ty : Copy ty → Copy (mod_ty f ty).
  Proof.
    move=> [? ShrAcc]. split; [by apply _|]. move=> */=. iIntros "LFT Shr Na Tok".
    iMod (ShrAcc with "LFT Shr Na Tok") as (q vl) "[$[Mt[Own Close]]]"; [done|done|].
    iModIntro. iExists q, vl. iFrame.
  Qed.

  Global Instance mod_ty_send `{Inj A B (=) (=) f} ty : Send ty → Send (mod_ty f ty).
  Proof. by move=> ??*/=. Qed.

  Global Instance mod_ty_sync `{Inj A B (=) (=) f} ty : Sync ty → Sync (mod_ty f ty).
  Proof. by move=> ??*/=. Qed.

  Lemma mod_ty_subtype_out `{Inj A B (=) (=) f} E L ty : subtype E L f (mod_ty f ty) ty.
  Proof.
    iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; by iIntros "!>*?".
  Qed.

  Lemma mod_ty_subtype_in `{Inj A B (=) (=) f} E L g ty :
    f ∘ g = id → subtype E L g ty (mod_ty f ty).
  Proof.
    move=> Eq. iIntros "*_!>_". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit; iIntros "!>*?/="; by rewrite compose_assoc Eq.
  Qed.

  Lemma mod_ty_eqtype_inout `{Inj A B (=) (=) f} E L g ty :
    f ∘ g = id → eqtype E L g f ty (mod_ty f ty).
  Proof. move=> ?. split; [apply mod_ty_subtype_in|by apply mod_ty_subtype_out]. Qed.

  Lemma mod_ty_subtype `{Inj A B (=) (=) f, Inj A' B' (=) (=) f'} E L h g' ty ty' :
    f' ∘ g' = id → subtype E L h ty ty' →
    subtype E L (g' ∘ h ∘ f) (mod_ty f ty) (mod_ty f' ty').
  Proof.
    move=> ??. eapply subtype_trans; [by apply mod_ty_subtype_out|].
    eapply subtype_trans; by [|apply mod_ty_subtype_in].
  Qed.

  Lemma mod_ty_eqtype `{Inj A B (=) (=) f, Inj A' B' (=) (=) f'} E L h h' g g' ty ty' :
    f ∘ g = id → f' ∘ g' = id → eqtype E L h h' ty ty' →
    eqtype E L (g' ∘ h ∘ f) (g ∘ h' ∘ f') (mod_ty f ty) (mod_ty f' ty').
  Proof. move=> ??[??]. split; by apply mod_ty_subtype. Qed.

End typing.
