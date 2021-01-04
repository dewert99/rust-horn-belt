From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section util.
  Context `{!typeG Σ}.

  (* Delayed sharing is used by various types; in particular own and uniq.
     It comes in two flavors: Borrows of "later something" and borrows of
     "borrowed something".
     TODO: Figure out a nice way to generalize that; the two proofs below are too
     similar. *)

  (* This is somewhat the general pattern here... but it doesn't seem
     easy to make this usable in Coq, with the arbitrary quantifiers
     and things.  Also, it actually works not just for borrows but for
     anything that you can split into a timeless and a persistent
     part.

  Lemma delay_borrow_step :
    lfeE ⊆ N → (∀ x, Persistent (Post x)) →
    lft_ctx -∗ &{κ} P -∗
      □ (∀ x, &{κ} P -∗ Pre x -∗ Frame x ={F1 x}[F2 x]▷=∗ Post x ∗ Frame x) ={N}=∗ 
      □ (∀ x, Pre x -∗ Frame x ={F1 x}[F2 x]▷=∗ Post x ∗ Frame x).
   *)

  Lemma delay_sharing_later N κ l ty tid :
    lftE ⊆ N →
    lft_ctx -∗ ▷ (κ ⊑ ty.(ty_lft)) -∗ &{κ}(▷ l ↦∗: ty.(ty_own) tid) ={N}=∗
       □ ∀ (F : coPset) (q : Qp),
       ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ (q).[κ] ={F}[F ∖ ↑shrN]▷=∗ ty.(ty_shr) κ tid l ∗ (q).[κ].
  Proof.
    iIntros (?) "#LFT #Hout Hbor". rewrite bor_unfold_idx.
    iDestruct "Hbor" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty κ tid l)%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok".
    iMod (inv_acc with "Hinv") as "[INV Hclose]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_later_tok with "LFT [Hbtok] Htok") as "Hdelay"; first solve_ndisj.
      { rewrite bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hdelay" as "[Hb Htok]".
      iMod (ty.(ty_share) with "LFT Hout Hb Htok") as "[#$ $]"; first solve_ndisj.
      iApply "Hclose". auto.
    - iMod fupd_intro_mask' as "Hclose'"; first solve_ndisj. iModIntro.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.

  Lemma delay_sharing_nested N κ κ' l ty tid :
    lftE ⊆ N →
    lft_ctx -∗ ▷ (κ ⊑ ty.(ty_lft)) -∗ ▷ (κ' ⊑ κ) -∗ &{κ'}(&{κ}(l ↦∗: ty_own ty tid)) ={N}=∗
       □ ∀ (F : coPset) (q : Qp),
       ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ (q).[κ'] ={F}[F ∖ ↑shrN]▷=∗ ty.(ty_shr) κ' tid l ∗ (q).[κ'].
  Proof.
    iIntros (?) "#LFT #Hout #Hincl Hbor". rewrite bor_unfold_idx.
    iDestruct "Hbor" as (i) "(#Hpb&Hpbown)".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty κ' tid l)%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok".
    iMod (inv_acc with "Hinv") as "[INV Hclose]"; first solve_ndisj.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest with "LFT [Hbtok]") as "Hb"; first solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb". iDestruct (bor_shorten with "[] Hb") as "Hb".
      { iApply (lft_incl_glb κ' κ κ' with "Hincl []"). iApply lft_incl_refl. }
      iMod (ty.(ty_share) with "LFT [Hout] Hb Htok") as "[#Hshr $]"; first solve_ndisj.
      { by iApply lft_incl_trans. }
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod fupd_intro_mask' as "Hclose'"; last iModIntro; first solve_ndisj.
      iNext. iMod "Hclose'" as "_". iMod ("Hclose" with "[]") as "_"; by eauto.
  Qed.
End util.
