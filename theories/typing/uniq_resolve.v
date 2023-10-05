From lrust.typing Require Export type.
From lrust.typing Require Import always_true typing uniq_alt.

Section uniq_resolve.
Implicit Type 𝔄 𝔅: syn_type.
Context `{!typeG Σ}.


Lemma alt_uniq_resolve' {𝔄} (P: 𝔄 → Prop) E L κ (ty: type 𝔄) `{!FlatOwn ty} `{!UniqAlt ty} :
  always_true ty P → lctx_lft_alive E L κ → resolve E L (uniq_alt_ty κ ty) (λ '(a, a'), a' = a ∧ P a).
Proof. unfold resolve.
  move=>/= always Alv ?? vπ d ? vl ?. iIntros "#LFT #PROPH #E L uniq".
  iDestruct (ty_uniq_alt_out with "uniq") as (??->) "([In uniq]&_&resolve_alt)".
  iDestruct "uniq" as (?->??[Le Eq]) "[Vo Bor]". destruct d; [lia|]. 
  iMod (Alv with "E L") as (?) "[[κ κ₊] ToL]"; [solve_ndisj|].
  iMod (bor_acc with "LFT Bor κ") as "[(%&%& ⧖ & Pc &%& ↦ & ty) ToBor]";
    [solve_ndisj|].
  iDestruct ("resolve_alt" with "LFT PROPH κ₊ ty") as "mod".
  iMod (fupd_mask_mono with "mod") as "(Obs''&κ₊&ty)"; [solve_ndisj|].
  simpl. iIntros "!>!>!>".
  iMod (lft_incl_acc with "In κ₊") as "(%&lft&toκ₊)"; [solve_ndisj|].
  iApply (fupd_mask_mono _); [|iDestruct (ty_own_flat with "LFT ty lft") as ">Upd"]; [solve_ndisj|].
  iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
  iApply (step_fupdN_wand with "[Upd]"). iApply step_fupdN_nmono; [|iApply (step_fupdN_mask_mono' with "Upd")]; [lia|solve_ndisj].
  iIntros "!> flat". iMod (fupd_mask_mono with "flat") as "flat"; [solve_ndisj|]. iDestruct (always with "flat") as "#Obs".
  iDestruct (ty_flat_proph with "flat") as "(%&%&%&ξl&Toflat)".
  iMod (uniq_resolve with "PROPH Vo Pc ξl") as "(Obs'& Pc & ξl)"; [solve_ndisj| |].
  by eapply ty_proph_weaken. iCombine "Obs'' Obs' Obs" as "Obs'".
  iDestruct ("Toflat" with "ξl") as "flat". iDestruct (ty_flat_own with "flat") as "Toty". 
  iMod (fupd_mask_mono with "Toty") as "[ty lft]"; [solve_ndisj|]. iMod ("toκ₊" with "lft") as "κ₊".
  iMod ("ToBor" with "[⧖ Pc ↦ ty]") as "[_ κ]". 
  { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. }
  iMod ("ToL" with "[$]") as "$". iModIntro.
  iApply (proph_obs_impl with "Obs'")=>/= π.
  move: (equal_f Eq π)=>/=. by case (vπ' π)=>/= ??->[?[-> ?]].
Qed.

Lemma uniq_resolve' {𝔄} (P: 𝔄 → Prop) E L κ (ty: type 𝔄) `{!FlatOwn ty} :
  always_true ty P → lctx_lft_alive E L κ → resolve E L (&uniq{κ} ty)%T (λ '(a, a'), a' = a ∧ P a).
Proof. unfold resolve. setoid_rewrite uniq_alt_ty_eqv_base. apply alt_uniq_resolve'. Qed.

Lemma alt_uniq_resolve {𝔄} E L κ (ty: type 𝔄) `{!UniqAlt ty} :
  lctx_lft_alive E L κ → resolve E L (uniq_alt_ty κ ty) (λ '(a, a'), a' = a).
Proof. 
  unfold resolve. setoid_rewrite (proph_obs_proper). eapply alt_uniq_resolve'.
  apply always_true_just'. intros π. case (vπ π)=>/=; intuition.
Qed.

(* Complete the set even though this is already defined *)
Lemma uniq_resolve_redo {𝔄} E L κ (ty: type 𝔄) :
  lctx_lft_alive E L κ → resolve E L (&uniq{κ} ty)%T (λ '(a, a'), a' = a).
Proof. unfold resolve. setoid_rewrite uniq_alt_ty_eqv_base. apply alt_uniq_resolve. Qed.

Program Global Instance flat_alt_uniq {𝔄} (ty: type 𝔄) κ `{!FlatOwn ty} `{!UniqAlt ty} : FlatOwn (uniq_alt_ty κ ty) :=  {|
    T := ((𝔄 → 𝔄) * (proph (𝔄 * 𝔄)%ST));
    ty_flat' vπ d tid q '(f, vπ') vl := ⌜vπ = (prod_map id f) ∘ vπ'⌝ ∗ (ty_flat (&uniq{κ} ty) vπ' d tid q vl)
|}%I.
Next Obligation. 
  intros. iIntros "LFT ty κ". iDestruct (ty_uniq_alt_out with "ty") as (??) "(?&ty&W&_)".
  iMod (ty_own_flat with "LFT ty κ") as "mod". iModIntro.
  iApply (step_fupdN_wand with "mod"). iIntros ">flat !>". iExists (_, _). iFrame.
  iIntros "(->&flat)". iMod (ty_flat_own with "flat") as "(own&$)". iModIntro. iApply ("W" with "own").
Qed.
Next Obligation.
  simpl. iIntros (????????[??]??) "(#Eq&flat)".
  iDestruct (ty_flat_proph with "flat") as "(%&%&(%&%&->&%&%)&ξl&ToFlat)".
  iExists _, _. iFrame "Eq". iFrame. iDestruct "Eq" as "->".
  iPureIntro. eexists _, _. intuition. eapply proph_dep_constr in H. f_exact H. by fun_ext. 
Qed.

Lemma always_true_alt_uniq {𝔄} (ty: type 𝔄) `{!FlatOwn ty} `{!UniqAlt ty} κ P: always_true ty P → always_true (uniq_alt_ty κ ty) (P ∘ fst).
Proof. 
  intros ??*. iIntros "flat".  iDestruct "flat" as ([??]) "/=((->&flat)&_)". simpl. iApply (always_true_uniq with "flat"). done.
Qed.
End uniq_resolve.