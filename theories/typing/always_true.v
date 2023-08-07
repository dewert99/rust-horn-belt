From lrust.typing Require Export type.
From lrust.typing Require Import typing hints.

Section always_true.
Implicit Type 𝔄 𝔅: syn_type.
Context `{!typeG Σ}.

Class FlatOwn {𝔄} (ty: type 𝔄) := {
  T: Type;
  ty_flat' vπ d tid q (t: T) vl: iProp Σ;
  ty_own_flat' vπ d tid vl q:
    lft_ctx -∗ ty_own ty vπ d tid vl -∗ q.[(ty_lft ty)]
      ={↑lftN}=∗ |={↑lftN}▷=>^d |={↑lftN}=> 
      ∃ t, ty_flat' vπ d tid q t vl ∗ (ty_flat' vπ d tid q t vl ={↑lftN}=∗ ty_own ty vπ d tid vl ∗ q.[(ty_lft ty)]);
  ty_flat_proph' vπ d tid vl q t: 
    (ty_flat' vπ d tid q vl t) -∗
        ∃ (ξl : list proph_var) (q' : Qp), 
          ⌜ty_proph ty vπ ξl⌝ ∗ q':+[ξl] ∗
          (q':+[ξl] -∗ ty_flat' vπ d tid q vl t)
}.

Global Arguments FlatOwn {_%syn_type_scope} (_%lrust_type_scope).

Definition ty_flat {𝔄} (ty: type 𝔄) `{!FlatOwn ty} vπ d tid q vl :=
  (∃ t, ty_flat' vπ d tid q t vl ∗ ⌜length vl = ty.(ty_size)⌝ ∗ (ty_flat' vπ d tid q t vl ={↑lftN}=∗ ty_own ty vπ d tid vl ∗ q.[(ty_lft ty)]))%I.

Lemma ty_own_flat {𝔄} (ty: type 𝔄) `{!FlatOwn ty} vπ d tid vl q:
  lft_ctx -∗ ty_own ty vπ d tid vl -∗ q.[(ty_lft ty)]
    ={↑lftN}=∗ |={↑lftN}▷=>^d |={↑lftN}=> ty_flat ty vπ d tid q vl.
Proof. 
  intros. unfold ty_flat. iIntros "LFT ty lft". iDestruct (ty_size_eq with "ty") as "%sz". setoid_rewrite (is_True_True sz).
  setoid_rewrite bi.True_sep. iApply (ty_own_flat' with "LFT ty lft"). typeclasses eauto.
Qed.

Lemma ty_flat_own {𝔄} (ty: type 𝔄) `{!FlatOwn ty} vπ d tid vl q :
  ty_flat ty vπ d tid q vl
    ={↑lftN}=∗ ty_own ty vπ d tid vl ∗ q.[(ty_lft ty)].
Proof. intros. iIntros "(%&flat&_&W)". iApply ("W" with "flat"). Qed.

Lemma ty_flat_proph {𝔄} (ty: type 𝔄) `{!FlatOwn ty} vπ d tid vl q: 
  (ty_flat ty vπ d tid q vl) -∗
    ∃ (ξl : list proph_var) (q' : Qp), 
      ⌜ty_proph ty vπ ξl⌝ ∗ q':+[ξl] ∗
      (q':+[ξl] -∗ ty_flat ty vπ d tid q vl).
Proof.
  intros. iIntros "(%&flat&W)". iDestruct (ty_flat_proph' with "flat") as "(%&%&?&?&W2)".
  iExists _, _. iFrame. iIntros "ξl". iExists _. iFrame. iApply ("W2" with "ξl").
Qed.

Definition always_true {𝔄} (ty: type 𝔄) `{!FlatOwn ty} (P: 𝔄 → Prop): Prop := 
  (∀ vπ d tid q vl, ty_flat ty vπ d tid q vl -∗ ⟨π , P (vπ π)⟩).

Global Instance always_true_mono {𝔄} (ty: type 𝔄) `{!FlatOwn ty} : Proper ((pointwise_relation _ impl) ==> impl) (always_true ty).
Proof. intros ?*? always ?*. iIntros. iApply proph_obs_impl; [|by iApply always]. intuition. apply H. done. Qed.

Global Instance always_true_proper {𝔄} (ty: type 𝔄) `{!FlatOwn ty} : Proper ((pointwise_relation _ iff) ==> iff) (always_true ty).
Proof. split; apply always_true_mono; intros ?; rewrite H; done. Qed.

Lemma always_true_and {𝔄} (ty: type 𝔄) `{!FlatOwn ty} P Q: (always_true ty P) ∧ (always_true ty Q) ↔ (always_true ty (λ x, P x ∧ Q x)).
Proof. 
  split. intros [HP HQ]. intros ?*. iIntros "flat". 
  iDestruct (HP with "flat") as "#?". iDestruct (HQ with "flat") as "#?".
  iApply (proph_obs_and); done.
  intros. split; f_exact H; intros ??; intuition. 
Qed.

Definition always_true_pair {𝔄} (ty: type 𝔄) `{!FlatOwn ty} (R: 𝔄 → 𝔄 → Prop): Prop := 
  (∀ vπ vπ' d d' tid q q' vl vl', ty_flat ty vπ d tid q vl -∗ ty_flat ty vπ' d' tid q' vl' -∗ ⟨π , R (vπ π) (vπ' π)⟩).

Lemma exist_pair {T U} (P: (T * U) → iProp Σ): (∃ (p: (T * U)), P p) ⊣⊢ (∃ (t: T) (u: U), P (t, u)).
Proof. iSplit. iIntros "(%&P)". destruct p. iExists _, _. done. iIntros "(%&%&P)". iExists (_, _). done. Qed.

Lemma exist_nil (P: () → iProp Σ): (∃ (n: ()), P n) ⊣⊢ P ().
Proof. iSplit. iIntros "(%&P)". destruct n. done. iIntros "P". iExists (). done. Qed.

Program Definition flat_just {𝔄} (ty: type 𝔄): FlatOwn ty := {|
  T := (list proph_var * Qp);
    ty_flat' vπ d tid q '(ξl, q') vl := 
        ⌜ty_proph ty vπ ξl⌝ ∗ q':+[ξl];
|}%I.
Next Obligation. 
  move=>/=*. iIntros "LFT ty lft". rewrite exist_pair. iDestruct (ty_own_proph with "LFT [] ty lft") as "X". 
  done. iApply lft_incl_refl. iFexact "X". do 7 f_equiv. iIntros "($&$&W) (_&X)". iRevert "X". done.
Qed.
Next Obligation.
  iIntros (?????[??]??) "(#?&?)". iExists _, _. iFrame "#". iFrame. iIntros. iFrame.
Qed.

Program Global Instance flat_uniq {𝔄} (ty: type 𝔄) κ `{!FlatOwn ty} : FlatOwn (&uniq{κ} ty) :=  {|
    T := (nat * positive);
    ty_flat' vπ d tid q '(d', ξi) vl := [loc[l] := vl][S(d) := d]
    let ξ := PrVar (𝔄 ↾ prval_to_inh (fst ∘ vπ)) ξi in
    l ↦∗: ty_flat ty (fst ∘ vπ) d' tid q ∗ ⌜d' ≤ d ∧ snd ∘ vπ = (.$ ξ)⌝
    ∗ .VO[ξ] (fst ∘ vπ) d' ∗ .PC[ξ, ty.(ty_proph)] (fst ∘ vπ) d';
|}%I.
Next Obligation. 
  intros. rewrite exist_pair. simpl. setoid_rewrite <- lft_tok_sep. iIntros "#LFT (In&(%&->&%&%&[%%]&Vo&Bor)) (κ&lft)". simpl.
  iMod (bor_acc with "LFT Bor κ") as "(Open&ToBor)". done. destruct d; [lia|]. simpl. iIntros "!>!>!>".
  iDestruct "Open" as (??) "(⧖&Pc&%&↦&ty)". iDestruct (uniq_agree with "Vo Pc") as "#(<-&<-)".
  iDestruct (ty_own_flat with "LFT ty lft") as ">flat".
  iModIntro.  iApply (step_fupdN_wand with "[-]"). iApply step_fupdN_frame_l. iDestruct (step_fupdN_nmono with "flat") as "$". lia. 
  iCombine "Vo Pc ↦ ⧖ ToBor In" as "X". iExact "X". 
  iIntros "((Vo&Pc&↦&⧖&ToBor&$)&>flat)". iModIntro. iExists _, _. iFrame. iSplitL "↦ flat". iSplit. iExists _. iFrame. iPureIntro. intuition. lia.
  iIntros "((%&↦&flat)&_&Vo&Pc)". iMod (ty_flat_own with "flat") as "(own&$)".
  iMod ("ToBor" with "[⧖ Pc ↦ own]") as "(Bor&$)". iNext. iExists _, _. iFrame. iExists _. iFrame.
  iModIntro. iExists _, _. iFrame. iPureIntro. done.
Qed.
Next Obligation.
  simpl. iIntros (???????[??]??) "(%&->&%&->&(%&?&flat)&(%&%)&Vo&Pc)". 
  iDestruct (ty_flat_proph with "flat") as "(%&%&%&ξl&ToFlat)".
  iDestruct (uniq_proph_tok with "Vo Pc") as "($&ξ&ToPc)".
  rewrite proph_tok_singleton.
  iDestruct (proph_tok_combine with "ξl ξ") as (?) "[ξl Toξl]".
  iExists _, _. iFrame. iSplit. iPureIntro. eexists _, _. intuition. rewrite H0. apply proph_dep_one.
  iIntros "ξl". iDestruct ("Toξl" with "ξl") as "(ξ&ξl)". iDestruct ("ToPc" with "ξl") as "$".
  iSplit; [|done]. iExists _. iDestruct ("ToFlat" with "ξ") as "$". done.
Qed.

Program Global Instance flat_box {𝔄} (ty: type 𝔄) `{!FlatOwn ty} : FlatOwn (box ty) := {|
    T := ();
    ty_flat' vπ d tid q '() vl := [loc[l] := vl][S(d) := d] l ↦∗: ty_flat ty vπ d tid q;
|}%I.
Next Obligation. 
  intros. rewrite exist_nil. simpl. iIntros "#LFT (%&->&%&->&(%&↦&ty)&$) lft". simpl.
  iIntros "!>!>!>". iMod (ty_own_flat with "LFT ty lft") as "?". iModIntro. 
  iApply (step_fupdN_wand with "[-]"). iApply step_fupdN_frame_l. iFrame. iExact "↦". 
  iIntros "(?&>?)". iModIntro. iSplitR "". iExists _. iFrame. 
  iIntros "(%&?&flat)". iMod (ty_flat_own with "flat") as "(?&$)". iModIntro. iNext. iExists _. iFrame.
Qed.
Next Obligation.
  simpl. iIntros (??????[]??) "(%&->&%&->&%&?&flat)". 
  iDestruct (ty_flat_proph with "flat") as "(%&%&?&ξl&ToFlat)".
  iExists _, _. iFrame. 
  iIntros "ξl". iExists _. iDestruct ("ToFlat" with "ξl") as "$". done.
Qed.

Lemma always_true_just {𝔄} (ty: type 𝔄) `{!FlatOwn ty} : always_true ty (const True).
Proof. intros ?*. iIntros "_". iApply proph_obs_true=>π. done. Qed.

Definition always_true_just' {𝔄} (ty: type 𝔄) := @always_true_just 𝔄 ty (flat_just ty).

Lemma always_true_uniq {𝔄} (ty: type 𝔄) `{!FlatOwn ty} κ P: always_true ty P → always_true (&uniq{κ} ty) (P ∘ fst).
Proof. 
  intros ??*. iIntros "flat". unfold ty_flat. iDestruct "flat" as ([??]) "/=((%&->&%&->&(%&_&flat)&_)&_)". iApply (H with "flat").
Qed.

Lemma always_true_box {𝔄} (ty: type 𝔄) `{!FlatOwn ty} P: always_true ty P → always_true (box ty) P.
Proof. 
  intros ??*. iIntros "flat". iDestruct "flat" as ([]) "/=((%&->&%&->&(%&_&flat))&_)". iApply (H with "flat").
Qed.

Lemma always_true_pair_just {𝔄} (ty: type 𝔄) `{!FlatOwn ty} : always_true_pair ty (const (const True)).
Proof. intros ?*. iIntros "_ _". iApply proph_obs_true=>π. done. Qed.

Definition always_true_pair_just' {𝔄} (ty: type 𝔄) := @always_true_pair_just 𝔄 ty (flat_just ty).

Lemma always_true_pair_uniq {𝔄} (ty: type 𝔄) `{!FlatOwn ty} κ (R: 𝔄 → 𝔄 → Prop): always_true_pair ty R → always_true_pair (&uniq{κ} ty) (λ x y, R x.1 y.1).
Proof. 
  intros ??*. iIntros "flat flat'".
  iDestruct "flat" as ([??]) "/=((%&->&%&->&(%&_&flat)&_)&_)". iDestruct "flat'" as ([??]) "/=((%&->&%&->&(%&_&flat')&_)&_)".
  iApply (H with "flat flat'").
Qed.

Lemma always_true_pair_box {𝔄} (ty: type 𝔄) `{!FlatOwn ty} (R: 𝔄 → 𝔄 → Prop): always_true_pair ty R → always_true_pair (box ty) R.
Proof. 
  intros ??*. iIntros "flat flat'".
  iDestruct "flat" as ([]) "/=((%&->&%&->&(%&_&flat))&_)". iDestruct "flat'" as ([]) "/=((%&->&%&->&(%&_&flat'))&_)".
  iApply (H with "flat flat'").
Qed.

Lemma step_fupd_mask_mono' E1 E2 (P: iProp Σ) :
  E1 ⊆ E2 → (|={E1}▷=> P) ⊢ |={E2}▷=> P.
Proof.
  intros. rewrite fupd_mask_mono; [|done]. do 2 f_equiv. apply fupd_mask_mono; done.
Qed.

Lemma step_fupdN_mask_mono' E1 E2 n (P: iProp Σ) :
  E1 ⊆ E2 → (|={E1}▷=>^n P) ⊢ |={E2}▷=>^n P.
Proof.
  intros. induction n. done. simpl. rewrite step_fupd_mask_mono'; [|done]. do 3 f_equiv. apply IHn.
Qed.

Lemma resolve_uniq_body' {𝔄} (P: 𝔄 → Prop) (ty: type 𝔄) `{!FlatOwn ty} vπ ξi d κ tid l E L q F :
  lctx_lft_alive E L κ → ↑lftN ∪ ↑prophN ⊆ F → always_true ty P →
  lft_ctx -∗ proph_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗ llctx_interp L q -∗
  uniq_body ty vπ ξi d κ tid l ={F}=∗ |={F}▷=>^(S d) |={F}=>
    ⟨π, π (PrVar (𝔄 ↾ prval_to_inh vπ) ξi) = vπ π ∧ P (vπ π)⟩ ∗ llctx_interp L q.
Proof.
  iIntros (Alv ? always) "#LFT PROPH In #E L [Vo Bor] /=".
  iMod (Alv with "E L") as (?) "[[κ κ₊] ToL]"; [solve_ndisj|].
  iMod (bor_acc with "LFT Bor κ") as "[(%&%& ⧖ & Pc &%& ↦ & ty) ToBor]";
    [solve_ndisj|]. iIntros "!>!>!>".
  iMod (lft_incl_acc with "In κ₊") as "(%&lft&toκ₊)"; [solve_ndisj|].
  iApply (fupd_mask_mono _); [|iDestruct (ty_own_flat with "LFT ty lft") as ">Upd"]; [solve_ndisj|].
  iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
  iApply (step_fupdN_wand with "[Upd]"). iApply (step_fupdN_mask_mono' with "Upd"); solve_ndisj. iIntros "!> flat".
  iMod (fupd_mask_mono with "flat") as "flat"; [solve_ndisj|]. iDestruct (always with "flat") as "#Obs".
  iDestruct (ty_flat_proph with "flat") as "(%&%&%&ξl&Toflat)".
  iMod (uniq_resolve with "PROPH Vo Pc ξl") as "(Obs'& Pc & ξl)"; [solve_ndisj| |].
  by eapply ty_proph_weaken. iCombine "Obs' Obs" as "$".
  iDestruct ("Toflat" with "ξl") as "flat". iDestruct (ty_flat_own with "flat") as "Toty". 
  iMod (fupd_mask_mono with "Toty") as "[ty lft]"; [solve_ndisj|]. iMod ("toκ₊" with "lft") as "κ₊".
  iMod ("ToBor" with "[⧖ Pc ↦ ty]") as "[_ κ]". 
  { iNext. iExists _, _. iFrame "⧖ Pc". iExists _. iFrame. }
  iApply "ToL". iFrame.
Qed.

Lemma uniq_resolve' {𝔄} (P: 𝔄 → Prop) E L κ (ty: type 𝔄) `{!FlatOwn ty} :
  always_true ty P → lctx_lft_alive E L κ → resolve E L (&uniq{κ} ty) (λ '(a, a'), a' = a ∧ P a).
Proof. unfold resolve.
  move=>/= H??? vπ ?? vl ?. iIntros "LFT PROPH E L [In uniq]".
  iDestruct "uniq" as (?->??[Le Eq]) "uniq".
  iMod (resolve_uniq_body' with "LFT PROPH In E L uniq") as "Upd"; [done..|].
  iApply step_fupdN_nmono; [done|]. iApply (step_fupdN_wand with "Upd").
  iIntros "!> >(?&$) !>". iApply proph_obs_eq; [|done]=>/= π.
  move: (equal_f Eq π)=>/=. by case (vπ π)=>/= ??->.
Qed.


  Lemma type_resolve_instr' {𝔄l 𝔅l} κ (T: tctx 𝔄l) (T': tctx 𝔅l) tr E L :
    resolve_unblock_tctx E L κ T T' tr →
    typed_instr E L T Skip (λ _, T') tr.
  Proof.
    iIntros (Rslv ???) "LFT TIME PROPH _ E $ L /= T Obs".
    iDestruct (Rslv with "LFT PROPH E L T Obs") as ">(%&%&⧖&Upd)".
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L. }
    wp_seq. iIntros "(?&?&Obs)". iModIntro. iExists _. iFrame.
  Qed.

  Lemma tctx_incl_refl_app_nil {𝔅l} E L (T: tctx 𝔅l) : tctx_incl E L T (T h++ +[]) (λ tr x, tr (x -++ (-[]: plist of_syn_type []))).
  Proof.
    induction T; simpl; eapply tctx_incl_ext.
    apply tctx_incl_refl. intros ?[]. done. apply tctx_incl_tail. done. intros ?[??]. done.
  Qed.

  Lemma type_resolve' {𝔅 𝔄l 𝔅l} E L (C: cctx 𝔅) (T': tctx 𝔄l) (T: tctx 𝔅l) e tr tr':
    Closed [] e → resolve_unblock_tctx E L inhabitant T T' tr
      → typed_body E L C T' e tr' -∗ typed_body E L C T (Skip ;; e) (tr ∘ tr').
  Proof.
    iIntros (??) "B". iApply type_seq; [by apply (type_resolve_instr' inhabitant T T')|apply tctx_incl_refl_app_nil|..]; last first.
    iApply typed_body_tctx_incl; [|done]. apply tctx_incl_resolve_lower. 
    rewrite /trans_upper. move=>??/=. rewrite papp_sepr papp_sepl. f_equiv. fun_ext=>?/=. rewrite papp_sepl. done.
  Qed.

  Definition resolve_unblock_tctx_nil' := (resolve_unblock_tctx_nil inhabitant).

  Lemma resolve_unblock_tctx_cons_keep_and_learn {𝔄 𝔅l ℭl} p (ty: type 𝔄) `{!FlatOwn ty}
      (T: tctx 𝔅l) (T': tctx ℭl) P tr κ E L :
    always_true ty P → lctx_lft_alive E L (ty_lft ty) → resolve_unblock_tctx E L κ T T' tr →
    resolve_unblock_tctx E L κ (p ◁ ty +:: T) (p ◁ ty +:: T') (λ post '(c -:: al), tr (λ bl, P c → post (c -:: bl)) al).
  Proof.
    iIntros (always_true Alv RslvU ??[vπ ?]?) "#LFT PROPH #E [L L'] /=[(%&%d'&%&#⧖'&ty) T] Obs".
    iMod (Alv with "E L") as (?) "[κ  ToL]"; [solve_ndisj|].
    iMod (RslvU with "LFT PROPH E L' T Obs") as (d vπl') "[⧖ Upd]". iDestruct (ty_own_flat with "LFT ty κ") as "Upd'".
    iMod (fupd_mask_mono with "Upd'") as "Upd'"; [done|]. iDestruct ((step_fupdN_mask_mono' _  ⊤) with "Upd'") as "Upd'"; [done|].
    iCombine "⧖ ⧖'" as "⧖". iCombine "Upd Upd'" as "Upd". iModIntro.
    iExists _, (vπ -:: vπl'). iFrame "⧖". iApply (step_fupdN_wand with "Upd").
    iIntros "(>($&$&Obs)&flat)". iMod (fupd_mask_mono with "flat") as "flat"; [done|].
    iDestruct (always_true with "flat") as "#Obs'". iCombine "Obs Obs'" as "Obs".
    iDestruct (ty_flat_own with "flat") as "Toty". iMod (fupd_mask_mono with "Toty") as "[ty κ]"; [done|].
    iMod ("ToL" with "κ") as "$". iModIntro.
    iSplit. iExists _, _. iFrame "ty ⧖'". done.
    iApply (proph_obs_impl with "Obs")=>π/=. intuition.
  Qed.

End always_true.