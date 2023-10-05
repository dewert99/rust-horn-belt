From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr hints.
From lrust.util Require Import list.
Set Default Proof Using "Type".

Open Scope nat.

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_alt.
  Context `{!typeG Σ}.

  Class UniqAlt {𝔄} (ty: type 𝔄) := {
    ty_uniq_alt κ (vπ: (proph (𝔄 * 𝔄)%ST)) d tid vl: iProp Σ;
    ty_uniq_alt_out κ vπ d tid vl:
      (ty_uniq_alt κ vπ d tid vl) -∗
      ∃ (f: 𝔄 → 𝔄)  (vπ': (proph (𝔄 * 𝔄)%ST)), ⌜vπ = (prod_map id f) ∘ vπ'⌝ ∗ ty_own (&uniq{κ} ty) vπ' d tid vl 
      ∗ (∀vπ'' d' vl' tid', ty_own (&uniq{κ} ty) vπ'' d' tid' vl' -∗ (ty_uniq_alt κ ((prod_map id f) ∘ vπ'') d' tid' vl'))
      ∧ (∀vπ'' d' tid' vl' q, lft_ctx -∗ proph_ctx -∗ q.[κ] -∗ ▷ ty_own ty vπ'' d' tid' vl' ={↑lftN ∪ ↑prophN}=∗ ▷ ⟨π, f (vπ'' π) = vπ'' π⟩ ∗ q.[κ] ∗ ▷ ty_own ty vπ'' d' tid' vl');
    ty_uniq_alt_in κ vπ d tid vl:
      (ty_own (&uniq{κ} ty) vπ d tid vl) -∗ (ty_uniq_alt κ vπ d tid vl) 
  }.

  Program Definition base_ty_uniq {𝔄} (ty: type 𝔄): UniqAlt ty := {|
    ty_uniq_alt κ vπ d tid vl := (ty_own (&uniq{κ} ty) vπ d tid vl)
  |}.
  Next Obligation. intros.
    iIntros. iExists id, _. iFrame. iSplit. iPureIntro. fun_ext=>π. simpl. destruct (vπ π). done. iSplit. iIntros. iFrame.
    iIntros. iModIntro. iFrame. iNext. iApply proph_obs_true=>π. done.
  Qed.
  Next Obligation. intros. done. Qed.

  Program Definition uniq_alt_ty {𝔄} κ (ty: type 𝔄) `{!UniqAlt ty} : type (𝔄 * 𝔄)  := {|
    ty_size := ty_size (&uniq{κ} ty); ty_lfts := ty_lfts (&uniq{κ} ty);  ty_E := ty_E (&uniq{κ} ty);
    ty_proph := ty_proph (&uniq{κ} ty);
    ty_own := ty_uniq_alt κ;
    ty_shr := ty_shr (&uniq{κ} ty);
    ty_shr_depth_mono := ty_shr_depth_mono (&uniq{κ} ty);
    ty_shr_lft_mono := ty_shr_lft_mono (&uniq{κ} ty);
    ty_shr_proph := ty_shr_proph (&uniq{κ} ty);
    ty_proph_weaken := ty_proph_weaken (&uniq{κ} ty);
  |}%I.
  Next Obligation.
   intros. iIntros "uniq". iDestruct (ty_uniq_alt_out with "uniq") as (??->) "(uniq&_)". iApply (ty_size_eq with "uniq"). 
  Qed.
  Next Obligation.
    intros. iIntros "uniq". iDestruct (ty_uniq_alt_out with "uniq") as (??->) "(uniq&W)". iApply "W". iApply (ty_own_depth_mono (&uniq{κ} ty)). done. done.
  Qed.
  Next Obligation. 
    intros. iIntros  "#LFT #In Bor κ". iMod (bor_acc_cons with "LFT Bor κ") as "((%&?&Uniq)&ToBor)". done.
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).1.
    iDestruct (bi.later_mono _ _ (ty_uniq_alt_out _ _ _ _ _) with "Uniq") as (??) "(>->&?&W)".
    iMod ("ToBor" with "[W] [-]") as "(Bor&κ)"; [| | iMod ((ty_share (&uniq{κ} ty)) with "LFT In Bor κ") as "X"].
    2:{iNext.  iExists _. iFrame.  }
    iNext. iIntros "(%&↦&X) !> !>". iDestruct ("W" with "X") as "?". iExists _. iFrame. done.
    iModIntro. iApply (step_fupdN_wand with "X"). iIntros ">((%&->&%&%&%&?)&$) !>". iExists _, _. iSplit; [|iFrame].
    iPureIntro. unfold compose. apply proph_dep_constr. done.
  Qed.
  Next Obligation. 
    intros. iIntros  "#LFT #In Uniq κ". iDestruct (ty_uniq_alt_out with "Uniq") as (??->) "(Uniq&W&_)". iMod ((ty_own_proph (&uniq{κ} ty)) with "LFT In Uniq κ") as "X". done.
    iModIntro. iApply (step_fupdN_wand with "X"). iIntros ">(%&%&(%&%&->&%&%)&?&W2) !>".
    iExists _, _. iFrame. iSplit. iPureIntro. eexists _, _. intuition. unfold compose. apply proph_dep_constr. done.
    iIntros "X". iMod ("W2" with "X") as "(?&$)". iModIntro. iApply ("W" with "[$]").
  Qed.

  Global Instance alt_uniq_send {𝔄} κ (ty: type 𝔄) `{!UniqAlt ty} : Send ty → Send (uniq_alt_ty κ ty).
  Proof. 
    intros ??*. assert (∀ (tid tid': thread_id), ty_own (uniq_alt_ty κ ty) vπ d tid vl ⊢ ty_own (uniq_alt_ty κ ty) vπ d tid' vl) as x.
    iIntros (??) "own". iDestruct (ty_uniq_alt_out with "own") as (??->) "(uniq&W&_)". rewrite uniq_send. iApply ("W" with "uniq").
    iSplit; iApply x.
  Qed.
  Global Instance alt_uniq_sync {𝔄} κ (ty: type 𝔄) `{!UniqAlt ty} : Sync ty → Sync (&uniq{κ} ty).
  Proof. move=> ??*. apply uniq_sync. done. Qed.


  Lemma uniq_alt_ty_intro {𝔄} κ (ty: type 𝔄) `{!UniqAlt ty} E L: 
    subtype E L (&uniq{κ} ty) (uniq_alt_ty κ ty) id.
  Proof.
    iIntros (?) "_ !> E". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iSplit. iIntros "!>" (vπ ???) "?". iApply (ty_uniq_alt_in with "[$]").
    iIntros "!>" (vπ ????) "$". 
  Qed.

  Lemma uniq_alt_ty_eqv_base {𝔄} κ (ty: type 𝔄) : 
   (&uniq{κ} ty)%T ≡ (@uniq_alt_ty _ κ ty (base_ty_uniq ty)).
  Proof. done. Qed.

  Lemma uniq_alt_ty_eq_base {𝔄} κ (ty: type 𝔄) E L: 
    eqtype E L (&uniq{κ} ty) (@uniq_alt_ty _ κ ty (base_ty_uniq ty)) id id.
  Proof. apply equiv_eqtype. done. Qed.
End uniq_alt.
