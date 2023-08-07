From lrust.typing Require Export type.
From lrust.typing Require Import typing.
From lrust.typing Require Export hints.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section zst.
  Context `{!typeG Σ}.

  Class ZST {𝔄} (ty: type 𝔄) :=
  zero_size : ty.(ty_size) = 0.

  Definition null_loc : loc := inhabitant.
  Definition null_val : val := #null_loc.

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

  Lemma tctx_elt_interp_zst'' {𝔄} (ty: type 𝔄) `{!ZST ty} vπ tid p:
    (tctx_elt_interp tid (p ◁ box ty) vπ) ⊣⊢ ∃(l: loc) d, ⌜eval_path p = Some #l⌝ ∧ ⧖(S d) ∗ ▷ ty.(ty_own) vπ d tid [].
  Proof. 
    iSplit. iIntros "(%&%&?&?&X)".  iDestruct "X" as (?->?[= ->]) "(?&_)". rewrite zst_own_eqv. iExists _, _. iFrame.
    iIntros "(%&%&%&?)". rewrite tctx_elt_interp_zst'. iExists _. done. done.
  Qed.

  Lemma tctx_elt_interp_zst {𝔄} (ty: type 𝔄) `{!ZST ty} vπ tid (l: loc):
    tctx_elt_interp tid (#l ◁ box ty) vπ ⊣⊢ ∃d, ⧖(S d) ∗ ▷ ty.(ty_own) vπ d tid [].
  Proof. 
    by rewrite tctx_elt_interp_zst'.
  Qed.

  Global Instance unit_zst: ZST ().
  Proof. done. Qed.

  Lemma ghost_update {𝔄 𝔄l 𝔅l} (ty: type 𝔄) `{!ZST ty} (Tin: tctx 𝔄l) (Tout: tctx 𝔅l) p p2 κ E L tr:
    lctx_lft_alive E L κ 
    → (tctx_incl E L (p ◁ (box ty) +:: Tin) (p2 ◁ (box ty) +:: Tout) tr)
    → (tctx_incl E L (p ◁ (&uniq{κ} ty) +:: Tin) (p ◁ (&uniq{κ} ty) +:: Tout) (λ post '((cur, fin) -:: rest), tr (λ '(res -:: rest), post ((res, fin) -:: rest)) (cur -:: rest))).
  Proof. intros Alv [P incl]. split. 
    intros ????. do 2 f_equiv. apply P. intros ?. f_equiv. by rewrite H.
    simpl. iIntros (??(vπ&rπ)?) "#LFT #PROPH #UNIQ #E (L&L') (ty&tyr) Obs".
    iDestruct "ty" as (???) "(_&κin&ty)". iDestruct "ty" as (?[= ->]??[? Eq]) "(Vo&Bor)".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iMod (bor_acc with "LFT Bor κ") as "[(%&% & >⧖ & Pc & ↦ty) ToBor]"; [done|].
    iMod (uniq_strip_later with "Vo Pc") as (<-<-) "[Vo Pc]".
    iMod (incl _ _ (fst ∘ vπ -:: rπ) with "LFT PROPH UNIQ E L' [↦ty tyr ⧖] [Obs]") as ([vπ' rπ']) "($&[↦ty tyr]&Obs')".
    iFrame. rewrite zst_own_eqv. rewrite tctx_elt_interp_zst'; [|done]. iExists _. iFrame "⧖". iFrame.
    iApply (proph_obs_impl with "Obs"). simpl. intros. rewrite (surjective_pairing (vπ π)) in H1. exact H1.
    simpl. iExists ((λ π, (vπ' π, (vπ π).2)) -:: rπ'). iFrame.
    rewrite tctx_elt_interp_zst''. iDestruct "↦ty" as (???) "(#⧖&ty)".
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

  Lemma ghost_dummy_instr E L:
   typed_instr E L +[] Skip (const +[#null_loc ◁ (box ())]) (λ post '-[], post -[()]).
  Proof.
    iIntros (???) "_ #TIME _ _ _ $ $ C #Obs". iMod persistent_time_receipt_0 as "⧖".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. wp_seq. iIntros "⧖".
    iExists -[const ()]. simpl. iFrame. rewrite tctx_elt_interp_zst.
    iSplit. iExists _. iFrame. iNext. iExists (const -[]). simpl. done. done.
  Qed.

  Lemma ghost_dummy {𝔅 𝔄l} E L (C: cctx 𝔅) (T: tctx 𝔄l) e tr:
    Closed [] e → typed_body E L C (#null_loc ◁ (box ()) +:: T) e tr
      -∗ typed_body E L C T (Skip;; e) (λ post x, tr post (() -:: x)).
  Proof.
    iIntros (?) "B". iApply type_seq; [apply ghost_dummy_instr|apply tctx_incl_refl| |done]. done.
  Qed.

  Lemma ghost_read {𝔄 𝔅 𝔄' 𝔅' 𝔄l} (ty: type 𝔄) (tyb: type 𝔅) (ty': type 𝔄') gt st p E L (C: cctx 𝔅') (T: tctx 𝔄l) e tr:
   tyb.(ty_size) = 1%nat → typed_read E L ty tyb ty' gt st → Closed [] e 
   → (∀ (v: val), typed_body E L C (p ◁ ty' +:: v ◁ tyb +:: T) e tr)
    -∗ typed_body E L C (p ◁ ty +:: T) (Skip;; e) (λ post '(a -:: rest), tr post (st a -:: gt a -:: rest)).
  Proof.
    iIntros (Sz read ?) "B". iIntros (?(vπ&rπ)?) "#LFT #? #? #? #E Na L C ((%&%&%&#⧖&ty)&rest) Obs".
    iMod (read with "LFT E Na L ty") as "(%&%&%&%&↦&tyb&wand)". iMod ("wand" with "↦") as "(Na&L&ty')".
    wp_seq. wp_seq. iDestruct (ty_size_eq with "tyb") as "%Len". rewrite Sz in Len. case vl as [|v'[|]]=>//. 
    iApply ("B" with "LFT [//] [//] [//] E Na L C [ty' tyb rest]").
    Unshelve. 4:{exact ((st ∘ vπ) -:: (gt ∘ vπ) -:: rπ). } 3:{exact v'. }
    iFrame. iSplitL "ty'". 
    rewrite tctx_hasty_val'; [|done]. iExists _. iFrame "⧖". done.
    rewrite tctx_hasty_val. iExists _. iFrame "⧖". done.
    done.
  Qed.

  Lemma ghost_read_delete {𝔄 𝔅' 𝔄l} (ty: type 𝔄) (v: val) E L (C: cctx 𝔅') (T: tctx 𝔄l) e tr:
   ty.(ty_size) = 1%nat → Closed [] e 
   → (∀ (v': val), typed_body E L C (v' ◁ ty +:: T) e tr)
    -∗ typed_body E L C (v ◁ (box ty) +:: T) (Skip;; delete [ #1; v];; e) tr.
  Proof.
    iIntros (Sz ?) "B". via_tr_impl. iApply ghost_read; [|apply read_own_move|]; [done|].
    iIntros. iApply type_delete; [| | |iApply "B"]. solve_extract. done. rewrite Sz. done.
    by move=>?[??]?.
  Qed.

  Local Instance box_zst_copy {𝔄} (ty: type 𝔄) `{!ZST ty} `{!Copy ty} vπ d tid vl : Persistent (ty_own (box ty) vπ d tid vl).
  Proof. eassert (_ -∗ _); [|done].
    iIntros "x". iDestruct "x" as (?->?->) "x".
    simpl. rewrite zst_own_eqv. iDestruct "x" as "(#x&_)". iModIntro. iFrame "x".
    rewrite zero_size. done.
  Qed.

  Lemma copy_ghost {𝔄} (ty: type 𝔄) `{!ZST ty} `{!Copy ty} p E L:
   tctx_incl E L +[p ◁ (box ty)] +[p ◁ (box ty); p ◁ (box ty)] (λ post '-[x], post -[x; x]).
  Proof. split. solve_proper. iIntros (??[?[]]?) "_ _ _ _ $ [ty?] Obs".
    rewrite tctx_elt_interp_zst''. iDestruct "ty" as (??) "#ty". iModIntro.
    iExists -[_; _]. iSplit. simpl. iFrame. rewrite 2! tctx_elt_interp_zst''. iSplit; iExists _, _; done.
    done.
  Qed.

  Lemma ghost_dummy' {𝔄} (ty: type 𝔄) p E L:
   tctx_incl E L +[p ◁ (box ty)] +[null_val ◁ (box ()); p ◁ (box ty)] (λ post '-[x], post -[(); x]).
  Proof. split. solve_proper. iIntros (??[?[]]?) "_ _ _ _ $ [(%&%&%&#⧖&ty)?] Obs".
    iDestruct "ty" as (?->?[=->]) "ty".
    iModIntro.
    iExists -[_; _]. iSplit. simpl. iFrame. rewrite tctx_elt_interp_zst tctx_hasty_val'; [|done]. 
    iSplit; iExists _; iFrame "⧖". iNext. iExists (const -[]). done. done.
    done.
  Qed.

  (* Local Instance bor_proper1 κ: Proper ((⊣⊢) ==> (⊢)) &{κ}%I.
  Proof. intros ???. iIntros; (iDestruct (bor_iff_proper κ x y with "[]") as "#X"; [|by iApply "X"]); 
    rewrite H; iNext; iModIntro; (iSplit; iIntros; done).
  Qed. 

  Local Instance bor_proper2 κ: Proper ((⊣⊢) ==> (⊣⊢)) &{κ}%I.
  Proof. intros ???. iSplit; iIntros; iStopProof; by f_equiv. Qed. 

  Lemma ghost_read_uniq {𝔄 𝔅 𝔄'} (ty: type 𝔄) κ (tyb: type 𝔅) `{!ZST tyb} (ty': type 𝔄') gt st p E L :
    typed_read E L ty (&uniq{κ} tyb) ty' gt st →
    typed_instr E L +[p ◁ ty] Skip (λ _, +[#null_loc ◁ (&uniq{κ} tyb); p ◁ ty'])
    (λ post '-[a], post -[gt a; st a]).
  Proof. intros. apply ghost_read; [done|done|]. 
    iIntros ([[| |]|]???) "($&ty)"; try done. iStopProof. simpl. do 5 f_equiv. unfold uniq_body. do 8 f_equiv. 
    rewrite 2! zst_own_eqv. done.
  Qed. *)
End zst.