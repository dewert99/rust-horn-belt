From lrust.typing Require Export type.
Set Default Proof Using "Type".

Notation "l +ₗ[ ty ] i" := (l%L +ₗ Z.of_nat (i%nat * ty.(ty_size))%nat)
  (format "l  +ₗ[ ty ]  i", at level 50, left associativity) : loc_scope.

Notation "l ↦∗len n" := (∃vl, ⌜length vl = n%nat⌝ ∗ l ↦∗ vl)%I
  (at level 20, format "l  ↦∗len  n") : bi_scope.

Section array_util.
  Context `{!typeG Σ}.

  Lemma ty_share_big_sepL {𝔄} (ty: type 𝔄) E aπl d κ l tid q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty.(ty_lft) -∗
    &{κ} ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=>
        ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT #In Bor κ".
    iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. by iFrame. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "Bors" as "[Bor Bors]".
    iMod (ty_share with "LFT In Bor κ") as "Toshr"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "κ₊ Bors") as "Toshrs".
    iCombine "Toshr Toshrs" as "Toshrs". iApply (step_fupdN_wand with "Toshrs").
    by iIntros "!> [>[$$] >[$$]]".
  Qed.

  Lemma ty_own_proph_mt_big_sepL_v {𝔄} (ty: type 𝔄) n E (aπl: vec _ n) l d tid κ q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty.(ty_lft) -∗
    ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜vapply aπl ./ ξl⌝ ∗ q':+[ξl] ∗
        (q':+[ξl] ={E}=∗
          ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) ∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT #In ↦tys κ". iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      iFrame "κ". do 2 (iSplit; [done|]). by iIntros. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "↦tys" as "[(% & ↦ & ty) ↦tys]".
    iMod (ty_own_proph with "LFT In ty κ") as "Toty"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "↦tys κ₊") as "To↦tys".
    iCombine "Toty To↦tys" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "!> [>(%&%&%& ξl & Toty) >(%&%&%& ζl & To↦tys)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iFrame "ξζl". iSplit; [iPureIntro; by apply proph_dep_vcons|].
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toty" with "ξl") as "[?$]". iMod ("To↦tys" with "ζl") as "[$$]".
    iExists _. by iFrame.
  Qed.

  Lemma ty_shr_proph_big_sepL_v {𝔄} (ty: type 𝔄) n E (aπl: vec _ n) d κ tid l κ' q :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty.(ty_lft) -∗
    ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) -∗ q.[κ']
      ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜vapply aπl ./ ξl⌝ ∗ q':+[ξl] ∗
        (q':+[ξl] ={E}=∗
          ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) ∗ q.[κ']).
  Proof.
    iIntros (?) "#LFT #In #In' tys κ'". iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      iFrame "κ'". do 2 (iSplit; [done|]). by iIntros. }
    iDestruct "κ'" as "[κ' κ'₊]". iDestruct "tys" as "[ty tys]".
    iMod (ty_shr_proph with "LFT In In' ty κ'") as "Toty"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "tys κ'₊") as "Totys".
    iIntros "!>!>". iCombine "Toty Totys" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "[>(%&%&%& ξl & Toty) >(%&%&%& ζl & Totys)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iFrame "ξζl". iSplit; [iPureIntro; by apply proph_dep_vcons|].
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toty" with "ξl") as "[$$]". by iMod ("Totys" with "ζl") as "[$$]".
  Qed.

  Lemma leak_mt_big_sepL {𝔄} (ty: type 𝔄) n (aπl: vec _ n) d tid l :
    ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid)%I ⊢
    l ↦∗len (n * ty.(ty_size)).
  Proof.
    iInduction aπl as [|] "IH" forall (l)=>/=.
    { iIntros. iExists []. by rewrite heap_mapsto_vec_nil. }
    iIntros "((%& ↦ & ty) & ↦tys)". rewrite ty_size_eq. iDestruct "ty" as %Eq.
    setoid_rewrite <-shift_loc_assoc_nat. iDestruct ("IH" with "↦tys") as "(%&%& ↦')".
    iExists (_++_). rewrite app_length heap_mapsto_vec_app shift_loc_0 -{3}Eq.
    iFrame "↦ ↦'". iPureIntro. by f_equal.
  Qed.
End array_util.
