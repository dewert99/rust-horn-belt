From lrust.typing Require Export type.
(* From lrust.typing Require Import type_context programs. *)
Set Default Proof Using "Type".

Section shr_bor.
  Context `{!typeG Σ}.

  Program Definition shr_bor {A} (κ: lft) (ty: type A) : type A := {|
    st_size := 1;  st_lfts := κ :: ty.(ty_lfts);  st_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    st_own vπ d tid vl := [S d' := d] [loc[l] := vl] ty.(ty_shr) vπ d' κ tid l
  |}%I.
  Next Obligation.
    move=> ????[|?]*/=; [by iIntros|]. rewrite by_just_loc_ex. by iIntros "[%[->?]]".
  Qed.
  Next Obligation.
    move=> ???[|?][|?]*; (try by iIntros); [lia|]. rewrite/= !by_just_loc_ex.
    do 3 f_equiv. apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*/=; [by iIntros|]. rewrite {1}by_just_loc_ex.
    iIntros "#LFT #? (%&->& Shr) Tok !>/=".
    iDestruct (ty_shr_proph with "LFT [] [] Shr Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_l]. }
    { iApply lft_incl_trans; by [|iApply lft_intersect_incl_r]. }
    iApply (step_fupdN_wand with "Upd"). iNext. iMod 1 as (ξs q ?) "[PTok Upd]".
    iModIntro. iExists ξs, q. iSplit; [done|]. iFrame "PTok". iIntros "PTok".
    by iMod ("Upd" with "PTok") as "$".
  Qed.

  Global Instance shr_ne {A} κ : NonExpansive (@shr_bor A κ).
  Proof. solve_ne_type. Qed.

End shr_bor.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance shr_type_contractive {A} κ : TypeContractive (@shr_bor _ _ A κ).
  Proof. split; [by apply (type_lft_morphism_add_one κ)|done| |].
    - move=>/= *. by do 4 f_equiv.
    - move=>/= *. do 8 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance shr_send {A} κ (ty: _ A) : Sync ty → Send (&shr{κ} ty).
  Proof. move=> Eq >/=. by setoid_rewrite Eq at 1. Qed.

  Lemma shr_type_incl {A B} κ κ' (f: A → B) ty ty' :
    κ' ⊑ κ -∗ type_incl f ty ty' -∗ type_incl f (&shr{κ} ty) (&shr{κ'} ty').
  Proof.
    iIntros "#? (_ & #? & _ & #Sub)".
    iApply type_incl_simple_type=>/=; [done|by iApply lft_intersect_mono|].
    iIntros "!>" (?[|?]??); [done|]. rewrite/= by_just_loc_ex.
    iIntros "[%[->?]]". iApply "Sub". by iApply ty_shr_lft_mono.
  Qed.

  Lemma shr_subtype {A B} E L κ κ' (f: A → B) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L f ty ty' →
    subtype E L f (&shr{κ} ty) (&shr{κ'} ty').
  Proof.
    move=> Lft Ty ?. iIntros "L". iDestruct (Lft with "L") as "#Lft".
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
