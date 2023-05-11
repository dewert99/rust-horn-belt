From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section zst.
  Context `{!typeG Σ}.

  Class ZST {𝔄} (ty: type 𝔄) :=
  zero_size : ty.(ty_size) = 0.

  Lemma zst_size_eq {𝔄} (ty: type 𝔄) `{!ZST ty} vπ d tid vl : ty.(ty_own) vπ d tid vl -∗ ⌜vl = []⌝.
  Proof. 
    iIntros "ty". iDestruct (ty_size_eq with "ty") as "%". 
    iPureIntro. apply nil_length_inv. by rewrite zero_size in H.
  Qed.

  Lemma zst_own_eqv {𝔄} (ty: type 𝔄) `{!ZST ty} aπ d tid l:
    l ↦∗: ty.(ty_own) aπ d tid ⊣⊢
    ty.(ty_own) aπ d tid [].
  Proof. 
    intros. iSplit.
    - iIntros "(%& ↦ & ty)".
      iDestruct (zst_size_eq with "ty") as "%zst". rewrite zst.
      iFrame.
    - iIntros "↦".
      iExists _. iFrame. by iApply heap_mapsto_vec_nil.
  Qed.

  Lemma tctx_elt_interp_zst' {𝔄} (ty: type 𝔄) `{!ZST ty} vπ tid p (l: loc):
    eval_path p = Some #l → tctx_elt_interp tid (p ◁ box ty) vπ ⊣⊢ ∃d, ⧖(S d) ∗ ▷ ty.(ty_own) vπ d tid [].
  Proof. 
    intros. rewrite tctx_hasty_val'; [|done]. simpl. setoid_rewrite zst_own_eqv; [|done]. iSplit.
    iIntros "X". iDestruct "X" as ([|?]) "(?&X)"; [done|].
    iExists n. iFrame. iDestruct "X" as "($&_)".
    iIntros "(%&?&?)". iExists (S d). rewrite zero_size. iFrame.
  Qed.

  Lemma tctx_elt_interp_zst {𝔄} (ty: type 𝔄) `{!ZST ty} vπ tid (l: loc):
    tctx_elt_interp tid (#l ◁ box ty) vπ ⊣⊢ ∃d, ⧖(S d) ∗ ▷ ty.(ty_own) vπ d tid [].
  Proof. 
    by rewrite tctx_elt_interp_zst'.
  Qed.

  Lemma ghost_update {𝔄 𝔄l 𝔅l} (ty: type 𝔄) `{!ZST ty} (Tin: tctx 𝔄l) (Tout: tctx 𝔅l) p κ E L tr:
    lctx_lft_alive E L κ 
    → (tctx_incl E [] (p ◁ (box ty) +:: Tin) (p ◁ (box ty) +:: Tout) tr)
    → (tctx_incl E L (p ◁ (&uniq{κ} ty) +:: Tin) (p ◁ (&uniq{κ} ty) +:: Tout) (λ post '((cur, fin) -:: rest), tr (λ '(res -:: rest), post ((res, fin) -:: rest)) (cur -:: rest))).
  Proof. intros Alv [P incl]. split. 
    intros ????. do 2 f_equiv. apply P. intros ?. f_equiv. by rewrite H.
    simpl. iIntros (??(vπ&rπ)?) "#LFT #PROPH #UNIQ #E L (ty&tyr) Obs".
    iDestruct "ty" as ([[| |]|]??) "(_&κin&ty)"; try done. 
    iDestruct "ty" as (??[? Eq]) "(Vo&Bor)"; try done.
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as "[(%&% & >⧖ & Pc & ↦ty) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iMod (incl 1%Qp _ (fst ∘ vπ -:: rπ) with "LFT PROPH UNIQ E [] [↦ty tyr ⧖] [Obs]") as ([vπ' rπ']) "(_&[↦ty tyr]&Obs')".
    by iApply big_sepL_nil. iFrame. rewrite zst_own_eqv. rewrite tctx_elt_interp_zst'; [|done]. iExists _. iFrame "⧖". iFrame.
    iApply (proph_obs_impl with "Obs"). simpl. intros. rewrite (surjective_pairing (vπ π)) in H1. exact H1.
    simpl. iExists ((λ π, (vπ' π, (vπ π).2)) -:: rπ'). iFrame.
    rewrite tctx_elt_interp_zst'; [|done]. iDestruct "↦ty" as "(%&#⧖&ty)".
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[ty Pc ⧖]") as "(Bor&κ)".
    iNext. iExists _, _. iFrame "Pc ⧖". iExists _. iFrame. by iApply heap_mapsto_vec_nil.
    iMod ("ToL" with "κ") as "$". iModIntro.
    iExists _, _. iFrame "⧖". iSplit; [done|].
    remember (proof_irrel (prval_to_inh (fst ∘ vπ)) (prval_to_inh vπ')) as Eq'.
    rewrite Eq'. rewrite Eq' in Eq.
    iExists _, _. iFrame.
    iPureIntro. split. done.
    fun_ext. simpl. intros. exact (equal_f Eq x).
  Qed.
End zst.