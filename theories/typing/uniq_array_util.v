From lrust.typing Require Export type array_util uniq_util.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_array_util.
  Context `{!typeG Σ}.

  Lemma ty_share_big_sepL_uniq_own {𝔄} (ty: type 𝔄) n (vπξil: vec _ n)
      d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty.(ty_lft) -∗
    &{κ'} ([∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) -∗
    q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      let ξl := vmap (λ vπξi, PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2) vπξil in
      &{κ'} 1:+[ξl] ∗
      ([∗ list] i ↦ vπ ∈ vmap fst vπξil, ty.(ty_shr) vπ d κ' tid (l +ₗ[ty] i)) ∗
      q.[κ'].
  Proof.
    iIntros (?) "#LFT #In #In' Bor κ'".
    iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    iInduction vπξil as [|] "IH" forall (q l)=>/=.
    { iApply step_fupdN_full_intro. iFrame "κ'".
      by iMod (bor_create _ _ True%I with "LFT [//]") as "[$ _]". }
    iDestruct "Bors" as "[Bor Bors]". iDestruct "κ'" as "[κ' κ'₊]".
    iMod (ty_share_uniq_own with "LFT In In' Bor κ'") as "Upd"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "κ'₊ Bors") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>(ξ &$&$) >(ξl &$&$)]".
    by iMod (bor_combine with "LFT ξ ξl") as "$".
  Qed.

  Lemma ty_own_proph_big_sepL_uniq_own {𝔄} (ty: type 𝔄) n (vπξil: vec _ n)
      d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty.(ty_lft) -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) -∗
    q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      let ξl := vmap (λ vπξi, PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2) vπξil in
      ∃ζl q', ⌜vapply (vmap fst vπξil) ./ ζl⌝ ∗ q':+[ζl ++ ξl] ∗
        (q':+[ζl ++ ξl] ={E}=∗
          ([∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) ∗
          q.[κ']).
  Proof.
    iIntros (?) "#LFT #In #In' uniqs κ'". iInduction vπξil as [|] "IH" forall (q l).
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      do 2 (iSplit; [done|]). iIntros. by iFrame. }
    iDestruct "uniqs" as "[uniq uniqs]". iDestruct "κ'" as "[κ' κ'₊]"=>/=.
    iMod (ty_own_proph_uniq_own with "LFT In In' uniq κ'") as "Upd"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "uniqs κ'₊") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>(%&%&%& [ζl ξ] & Touniq) >(%&%&%& [ζl' ξl] & Touniqs)] !>".
    iDestruct (proph_tok_combine with "ζl ζl'") as (?) "[ζζl Toζζl]".
    iDestruct (proph_tok_combine with "ξ ξl") as (?) "[ξl Toξl]".
    iDestruct (proph_tok_combine with "ζζl ξl") as (?) "[ζζξl Toζζξl]".
    iExists _, _. iFrame "ζζξl". iSplit. { iPureIntro. by apply proph_dep_vec_S. }
    iIntros "ζζξl". iDestruct ("Toζζξl" with "ζζξl") as "[ζζl ξl]".
    iDestruct ("Toζζl" with "ζζl") as "[ζl ζl']".
    iDestruct ("Toξl" with "ξl") as "[ξ ξl]".
    iMod ("Touniq" with "[$ζl $ξ]") as "[$$]".
    by iMod ("Touniqs" with "[$ζl' $ξl]") as "[$$]".
  Qed.

  Lemma leak_big_sepL_uniq_own {𝔄} (ty: type 𝔄) n (vπξil: vec _ n) d κ tid l E L q F :
    lctx_lft_alive E L κ → ↑lftN ∪ ↑prophN ⊆ F →
    lft_ctx -∗ proph_ctx -∗ κ ⊑ ty.(ty_lft) -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i))
      ={F}=∗ |={F}▷=>^(S d) |={F}=>
      let φπ π := lforall (λ vπξi,
        let ξ := PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2 in π ξ = vπξi.1 π) vπξil in
      .⟨φπ⟩ ∗ llctx_interp L q.
  Proof.
    iIntros (??) "#LFT #PROPH #In #E L uniqs". iInduction vπξil as [|] "IH" forall (q l).
    { iApply step_fupdN_full_intro. iFrame "L". by iApply proph_obs_true. }
    iDestruct "uniqs" as "[uniq uniqs]". iDestruct "L" as "[L L₊]"=>/=.
    iMod (leak_uniq_own with "LFT PROPH In E L uniq") as "Upd"; [done..|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "L₊ uniqs") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>[Obs $] >[Obs' $]]". by iCombine "Obs Obs'" as "$".
  Qed.

  Lemma real_big_sepL_uniq_own {𝔄 𝔅} (ty: type 𝔄) n (vπξil: vec _ n)
      d κ tid l E L (f: _ → 𝔅) q F :
    lctx_lft_alive E L κ → real E L ty f → ↑lftN ⊆ F →
    lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i))
      ={F}=∗ |={F}▷=>^(S d) |={F}=>
      ⌜∃v, vapply (vmap ((f ∘.) ∘ fst) vπξil) = const v⌝ ∗ llctx_interp L q ∗
      ([∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)).
  Proof.
    iIntros (???) "#LFT #E L uniqs". iInduction vπξil as [|] "IH" forall (q l).
    { iApply step_fupdN_full_intro. iIntros "!>!>". iFrame "L".
      iSplit; [|done]. by iExists [#]. }
    iDestruct "uniqs" as "[uniq uniqs]". iDestruct "L" as "[L L₊]"=>/=.
    iMod (real_uniq_own with "LFT E L uniq") as "Upd"; [done..|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "L₊ uniqs") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>([%v ->]&$&$) >([%vl %Eq]&$&$)] !%". exists (v ::: vl).
    fun_ext=>/= ?. by rewrite Eq.
  Qed.

  Lemma incl_big_sepL_uniq_own {𝔄} (ty ty': type 𝔄) vπξil d κ κ' tid l :
    κ' ⊑ κ -∗ □ (∀vπ d tid vl, ty.(ty_own) vπ d tid vl ↔ ty'.(ty_own) vπ d tid vl) -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) -∗
    [∗ list] i ↦ vπξi ∈ vπξil, uniq_own ty' vπξi.1 vπξi.2 d κ' tid (l +ₗ[ty] i).
  Proof.
    iIntros "#InLft #EqOwn uniqs". iInduction vπξil as [|] "IH" forall (l); [done|].
    iDestruct "uniqs" as "[uniq uniqs]".
    iDestruct (incl_uniq_own with "InLft EqOwn uniq") as "$"=>/=.
    setoid_rewrite <-shift_loc_assoc_nat. iDestruct ("IH" with "uniqs") as "$".
  Qed.
End uniq_array_util.
