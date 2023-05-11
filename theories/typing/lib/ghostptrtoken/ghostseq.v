From lrust.typing Require Export type.
From lrust.typing Require Import zst array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section seq.
  Context `{!typeG Σ}.

  Lemma split_mt_seq {𝔄} (d: nat) l' alπ ty tid:
    (∃ vl, l' ↦∗ vl ∗ ∃ (aπl: list (proph 𝔄)),
      ⌜vl = [] ∧ alπ = lapply aπl⌝ ∗ ([∗ list] aπ ∈ aπl, ty.(ty_own) aπ d tid [])) ⊣⊢
     ∃(aπl: list (proph 𝔄)),
      ⌜alπ = lapply aπl⌝ ∗ l' ↦∗ [] ∗ ([∗ list] aπ ∈ aπl, ty.(ty_own) aπ d tid []).
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". iDestruct "big" as (?[->->]) "Φ".
      iExists _. iSplit; [done|iFrame].
    - iIntros "big". iDestruct "big" as (?->) "(↦ & ?)".
      iExists []. iFrame "↦". iExists _. by iFrame.
  Qed.

  Lemma ty_share_big_sepL' {𝔄} (ty: type 𝔄) E aπl d κ tid l q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
    &{κ} ([∗ list] aπ ∈ aπl, ty.(ty_own) aπ d tid []) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=>
        ([∗ list] aπ ∈ aπl, ty.(ty_shr) aπ d κ tid l) ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT #In Bor κ".
    iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    iInduction aπl as [|x] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. by iFrame. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "Bors" as "[Bor Bors]".
    iMod (bor_acc with "LFT Bor κ") as "(ty&toBor)"; [done|].
    assert (▷ ty_own ty x d tid [] ⊢ ■▷⌜ZST ty⌝) as zst1.
    iIntros "ty". iApply plain. iModIntro. iDestruct (ty_size_eq with "ty") as "%".
    rewrite nil_length in H0. done.
    apply plainly_entails_l in zst1.
    iDestruct (zst1 with "ty") as "(>%zst&ty)".
    iMod ("toBor" with "ty") as "(Bor&κ)".
    setoid_rewrite <- zst_own_eqv; [|exact zst..].
    iMod (ty_share with "LFT In Bor κ") as "Toshr"; [done|].
    iMod ("IH" with "κ₊ Bors") as "Toshrs".
    iCombine "Toshr Toshrs" as "Toshrs". iApply (step_fupdN_wand with "Toshrs").
    by iIntros "!> [>[$$] >[$$]]".
    Unshelve. exact null_loc.
  Qed.

  Lemma trans_big_sepL'_mt_ty_own {𝔄} (ty: type 𝔄) aπl d tid :
    ([∗ list] aπ ∈ aπl, ty.(ty_own) aπ d tid []) ⊣⊢
    ([∗ list] aπwl ∈ (vzip (Vector.of_list aπl) (fun_to_vec (const []))), ty.(ty_own) aπwl.1 d tid aπwl.2).
  Proof.
    iSplit.
    - iIntros "↦owns". iInduction aπl as [|x] "IH"=>/=. done.
      iDestruct "↦owns" as "[$ ↦owns]".
      iDestruct ("IH" with "↦owns") as "tys".
      iFrame.
    - iIntros "↦s". iInduction aπl as [|x] "IH"; [done|].
      iDestruct "↦s" as "[$ ↦s]". iApply ("IH" with "↦s").
  Qed.

  Lemma ty_own_proph_big_sepL' {𝔄} (ty: type 𝔄) (n: nat) E aπl d tid κ q :
  ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
  ([∗ list] aπ ∈ aπl, ty.(ty_own) aπ d tid []) -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξll q', ⌜Forall2 ty.(ty_proph) aπl ξll⌝ ∗ q':+[mjoin ξll] ∗
      (q':+[mjoin ξll] ={E}=∗
        ([∗ list] aπ ∈ aπl, ty.(ty_own) aπ d tid []) ∗ q.[κ]).
  Proof.
    rewrite {1} trans_big_sepL'_mt_ty_own. iIntros (?) "LFT In tys κ".
    iMod (ty_own_proph_big_sepL with "LFT In tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&(%&->&%)& ξl & Totys) !>".
    iExists _, _. rewrite vec_to_list_to_vec in H0.
    iSplit; [done|]. iIntros "{$ξl}ξl".
    iMod ("Totys" with "ξl") as "[tys $]".
    rewrite -trans_big_sepL'_mt_ty_own. done.
  Qed.

  Lemma ty_shr_proph_big_sepL' {𝔄} (ty: type 𝔄) (n: nat) E aπl d κ tid l κ' q :
  ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
  ([∗ list] aπ ∈ aπl, ty.(ty_shr) aπ d κ tid l) -∗ q.[κ']
    ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξll q', ⌜Forall2 ty.(ty_proph) aπl ξll⌝ ∗ q':+[mjoin ξll] ∗
      (q':+[mjoin ξll] ={E}=∗ q.[κ']).
  Proof.
    iIntros (?) "#LFT #In #In' tys κ'".
    iInduction aπl as [|x] "IH" forall (q) =>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      iFrame "κ'". iSplit. done. iSplit; [done|]. by iIntros. }
    iDestruct "κ'" as "[κ' κ'₊]". iDestruct "tys" as "[ty tys]".
    iMod (ty_shr_proph with "LFT In In' ty κ'") as "Upd"; [done|].
    iMod ("IH" with "tys κ'₊") as "Upd'".
    iIntros "!>!>". iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "[>(%&%&%& ξl & Toκ') >(%&%&%& ζl & Toκ'₊)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iSplit. iPureIntro. by constructor. iFrame "ξζl". 
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toκ'" with "ξl") as "$". by iMod ("Toκ'₊" with "ζl") as "$".
  Qed.

  (* Rust's GhostSeq<T> *)
  Program Definition ghostseq_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
    ty_size := 0;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_proph alπ ξl := exists (aπl: list (proph 𝔄)) ξll,
      ξl = mjoin ξll /\ alπ = lapply aπl /\ Forall2 ty.(ty_proph) aπl ξll;
    ty_own alπ d tid vl :=
      ∃(aπl: list (proph 𝔄)),
        ⌜vl = [] ∧ alπ = lapply aπl⌝ ∗
        ([∗ list] aπ ∈ aπl, ty.(ty_own) aπ d tid []);
    ty_shr alπ d κ tid l :=
      ∃(aπl: list (proph 𝔄)),
        ⌜alπ = lapply aπl⌝ ∗
        ([∗ list] aπ ∈ aπl, ty.(ty_shr) aπ d κ tid l);
  |}%I.
  Next Obligation.
    iIntros (??????) "token //". by iDestruct "token" as (?[-> _]) "?".
  Qed.
  Next Obligation.
    move=> ????*/=; try (by iIntros). do 6 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ????*/=; try (by iIntros). do 6 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??????*. iIntros "#? (%&?& All)".
    iExists _. iSplit; [done|].
    erewrite !big_sepL_forall; [|intros ??; by apply ty_shr_persistent ..]. iIntros (???).
    iApply ty_shr_lft_mono; by [|iApply "All"].
  Qed.
  Next Obligation.
    iIntros (???? d) "*% #LFT In Bor κ". rewrite split_mt_seq.
    iMod (bor_exists_tok with "LFT Bor κ") as (?) "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (ty_share_big_sepL' with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (?????) "*% LFT In token κ/=".
    iDestruct "token" as (?[->->]) "↦tys".
    iMod (ty_own_proph_big_sepL' with "LFT In ↦tys κ") as "Upd"; [done|done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _. iSplit. iExists _, _. done.
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (?????) "*% LFT In In' token κ'/=".
    iDestruct "token" as (?->) "tys".
    iMod (ty_shr_proph_big_sepL' with "LFT In In' tys κ'") as "Toκ'"; [done|done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Toκ'").
    iIntros ">(%&%&%& ξl & Toκ') !>". iExists _, _. iSplit. iExists _, _. done.
    iIntros "{$ξl}ξl". by iMod ("Toκ'" with "ξl") as "$".
  Qed.
  Next Obligation.
    simpl. intros ????(?&?&->&->&?). 
    by eapply ty_proph_weaken_big_sepL'.
  Qed.

  Global Instance ghostptrtoken_ty_ne {𝔄} : NonExpansive (@ghostseq_ty 𝔄).
  Proof.
    solve_ne_type. done.
  Qed.
End seq.
