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
    move=> */=. iIntros "#LFT #LftIn". iDestruct 1 as (??->->) "Shr". iIntros "LftTok !>".
    iDestruct (ty_shr_proph with "LFT [] [] Shr LftTok") as "Fupd". { done. }
    { iApply lft_incl_trans; [iApply "LftIn"|iApply lft_intersect_incl_l]. }
    { iApply lft_incl_trans; [iApply "LftIn"|iApply lft_intersect_incl_r]. }
    iApply (step_fupdN_wand with "Fupd"). iIntros "!> > Upd !>".
    iDestruct "Upd" as (ξs q) "[?[ProphTok Upd]]". iExists ξs, q. iSplit; [done|].
    iFrame "ProphTok". iIntros "ProphTok". iMod ("Upd" with "ProphTok") as "[? $]".
    iModIntro. iExists d, l. by do 2 (iSplit; [done|]).
  Qed.

  Lemma shr_type_incl {A B} κ κ' (f: A → B) ty ty' :
    κ' ⊑ κ -∗ type_incl f ty ty' -∗ type_incl f (shr_bor κ ty) (shr_bor κ' ty').
  Proof.
    iIntros "#? [_ [#? [_ #Wand]]]". iApply type_incl_simple_type=>/=.
    { done. } { by iApply lft_intersect_mono. }
    iIntros "!>" (????). iDestruct 1 as (d' l) "[->[->?]]". iExists d', l.
    do 2 (iSplit; [done|]). iApply "Wand". by iApply ty_shr_lft_mono.
  Qed.

  Global Instance shr_mono {A} E L :
    Proper (flip (lctx_lft_incl E L) ==> subtype E L id ==> subtype E L id) (@shr_bor A).
  Proof.
    move=>/= ?? Lft ?? Ty. iIntros (?) "L". iDestruct (Lft with "L") as "#Lft".
    iDestruct (Ty with "L") as "#Ty". iIntros "!> #E".
    iApply shr_type_incl; by [iApply "Lft"|iApply "Ty"].
  Qed.
  Global Instance shr_mono_flip {A} E L : Proper
    (lctx_lft_incl E L ==> flip (subtype E L id) ==> flip (subtype E L id)) (@shr_bor A).
  Proof. move=> ??????. by apply shr_mono. Qed.
  Global Instance shr_proper {A} E L :
    Proper (lctx_lft_eq E L ==> eqtype E L id id ==> eqtype E L id id) (@shr_bor A).
  Proof. move=> ??[??]??[??]. by split; apply shr_mono. Qed.

  Global Instance shr_type_contractive {A} κ : TypeContractive (@shr_bor A κ).
  Proof. split.
    - apply (type_lft_morphism_add _ κ [κ] [])=> ?; [by apply lft_equiv_refl|].
      by rewrite /= elctx_interp_app elctx_interp_ty_outlives_E /elctx_interp
        /= left_id right_id.
    - done.
    - move=> */=. by do 6 f_equiv.
    - move=> */=. do 10 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance shr_ne {A} κ : NonExpansive (@shr_bor A κ).
  Proof. solve_ne_type. Qed.

  Global Instance shr_send {A} κ (ty: _ A) : Sync ty → Send (shr_bor κ ty).
  Proof.
    move=> Sync ????. iDestruct 1 as (d l ??) "?". iExists d, l.
    do 2 (iSplit; [done|]). by iApply Sync.
  Qed.
End shr_bor.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

(*
Section typing.
  Context `{!typeG Σ}.

  Lemma shr_mono' E L κ1 κ2 ty1 ty2 :
    lctx_lft_incl E L κ2 κ1 → subtype E L ty1 ty2 →
    subtype E L (&shr{κ1}ty1) (&shr{κ2}ty2).
  Proof. by intros; apply shr_mono. Qed.
  Lemma shr_proper' E L κ ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (&shr{κ}ty1) (&shr{κ}ty2).
  Proof. by intros; apply shr_proper. Qed.

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
End typing.

Global Hint Resolve shr_mono' shr_proper' read_shr : lrust_typing.
*)
