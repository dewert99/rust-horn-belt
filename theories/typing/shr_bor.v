From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
(* From lrust.typing Require Import lft_contexts type_context programs. *)
Set Default Proof Using "Type".

Section shr_bor.
  Context `{!typeG Σ}.

  Program Definition shr_bor {A} (κ: lft) (ty: type A) : type A := {|
    st_size := 1;  st_lfts := κ :: ty.(ty_lfts);  st_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    st_own vπd tid vl := ∃d (l: loc),
      ⌜vπd.2 = S d⌝ ∗ ⌜vl = [ #l]⌝ ∗ ty.(ty_shr) (vπd.1,d) κ tid l;
  |}%I.
  Next Obligation. move=> *. by iDestruct 1 as (???->) "_". Qed.
  Next Obligation.
    move=> ????[|d']*/=; iDestruct 1 as (d l ->->) "?"; [lia|].
    iExists d', l. do 2 (iSplit; [done|]). iApply ty_shr_depth_mono; [|done]. lia.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #?". iDestruct 1 as (??->->) "Shr". iIntros "Tok !>".
    iDestruct (ty_shr_proph with "LFT [] [] Shr Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iApply (step_fupdN_wand with "Upd"). iNext. iMod 1 as (ξs q ?) "[PTok Upd]".
    iModIntro. iExists ξs, q. iSplit; [done|]. iFrame "PTok". iIntros "PTok".
    iMod ("Upd" with "PTok") as "[Shr $]". iExists d, l. by iFrame "Shr".
  Qed.

  Global Instance shr_ne {A} κ : NonExpansive (@shr_bor A κ).
  Proof. solve_ne_type. Qed.

End shr_bor.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance shr_type_contractive {A} κ : TypeContractive (@shr_bor _ _ A κ).
  Proof. split.
    - apply (type_lft_morphism_add _ κ [κ] [])=> ?; [by apply lft_equiv_refl|].
      by rewrite elctx_interp_app elctx_interp_ty_outlives_E /elctx_interp
        /= left_id right_id.
    - done.
    - move=> */=. by do 6 f_equiv.
    - move=> */=. do 10 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance shr_send {A} κ (ty: _ A) : Sync ty → Send (&shr{κ} ty).
  Proof. move=> ??*/=. by do 6 f_equiv. Qed.

  Lemma shr_type_incl {A B} κ κ' (f: A → B) ty ty' :
    κ' ⊑ κ -∗ type_incl f ty ty' -∗ type_incl f (&shr{κ} ty) (&shr{κ'} ty').
  Proof.
    iIntros "#? [_ [#? [? #Sub]]]".
    iApply type_incl_simple_type=>/=; [done|by iApply lft_intersect_mono|].
    iIntros "!> *". iDestruct 1 as (d' l ->->) "?". iExists d', l.
    do 2 (iSplit; [done|]). iApply "Sub". by iApply ty_shr_lft_mono.
  Qed.

  Lemma shr_subtype {A B} E L κ κ' (f: A → B) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L f ty ty' →
    subtype E L f (&shr{κ} ty) (&shr{κ'} ty').
  Proof.
    move=> Lft Ty. iIntros (?) "L". iDestruct (Lft with "L") as "#Lft".
    iDestruct (Ty with "L") as "#Ty". iIntros "!> #?".
    iApply shr_type_incl; by [iApply "Lft"|iApply "Ty"].
  Qed.

  Lemma shr_eqtype {A B} E L κ κ' (f: A → B) g ty ty' :
    lctx_lft_eq E L κ κ' → eqtype E L f g ty ty' →
    eqtype E L f g (&shr{κ} ty) (&shr{κ'} ty').
  Proof. move=> [??] [??]. split; by apply shr_subtype. Qed.

(*
  Lemma tctx_reborrow_shr E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [p ◁ &shr{κ}ty] [p ◁ &shr{κ'}ty; p ◁{κ} &shr{κ}ty].
  Proof.
    iIntros (Hκκ' tid ?) "#LFT #HE HL [H _]". iDestruct (Hκκ' with "HL HE") as "#Hκκ'".
    iFrame. rewrite /tctx_interp /=. simpl.
    iDestruct "H" as ([[]|] depth) "(? & % & #Hshr)"; try done. iModIntro. iSplit.
    - iExists _, _. do 2 (iSplit; [done|]). by iApply (ty_shr_mono with "Hκκ' Hshr").
    - iSplit=> //. iExists _. auto 10.
  Qed.

  Lemma read_shr E L κ ty :
    Copy ty → lctx_lft_alive E L κ → ⊢ typed_read E L (&shr{κ}ty) ty (&shr{κ}ty).
  Proof.
    rewrite typed_read_eq. iIntros (Hcopy Halive) "!>".
    iIntros ([[]|] depth tid F qL ?) "#LFT #HE Htl HL #Hshr"; try done.
    iMod (Halive with "HE HL") as (q) "[Hκ Hclose]"; first solve_ndisj.
    iMod (copy_shr_acc with "LFT Hshr Htl Hκ")
      as (q' vl) "(Htl & H↦ & #Hown & Hcl)"; first solve_ndisj.
    { rewrite ->shr_locsE_shrN. solve_ndisj. }
    iExists _, _, _. iIntros "!> {$∗ $#}". iSplit; first done. iIntros "H↦".
    iMod ("Hcl" with "Htl H↦") as "[$ Hκ]". iApply ("Hclose" with "Hκ").
  Qed.
*)
End typing.

Global Hint Resolve shr_subtype shr_eqtype (* read_shr *) : lrust_typing.
