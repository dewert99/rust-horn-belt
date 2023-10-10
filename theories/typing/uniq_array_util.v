From lrust.typing Require Export type array_util uniq_util.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_array_util.
  Context `{!typeG Σ}.

  Lemma ty_share_big_sepL_uniq_body {𝔄} (ty: type 𝔄) n (vπξil: vec _ n)
      d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    &{κ'} ([∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) -∗
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
    iMod (ty_share_uniq_body with "LFT In In' Bor κ'") as "Upd"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "κ'₊ Bors") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>(ξ &$&$) >(ξl &$&$)]".
    by iMod (bor_combine with "LFT ξ ξl") as "$".
  Qed.

  Lemma ty_own_proph_big_sepL_uniq_body {𝔄} (ty: type 𝔄) n (vπξil: vec _ n)
      d κ tid l κ' q E :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) -∗
    q.[κ'] ={E}=∗ |={E}▷=>^(S d) |={E}=>
      let ξl := vmap (λ vπξi, PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2) vπξil in
      ∃ζll q', ⌜Forall2 ty.(ty_proph) (vmap fst vπξil) ζll⌝ ∗ q':+[mjoin ζll ++ ξl] ∗
        (q':+[mjoin ζll ++ ξl] ={E}=∗
          ([∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) ∗
          q.[κ']).
  Proof.
    iIntros (?) "#LFT #In #In' uniqs κ'". iInduction vπξil as [|] "IH" forall (q l).
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp. simpl.
      do 2 (iSplit; [done|]). iIntros. by iFrame. }
    iDestruct "uniqs" as "[uniq uniqs]". iDestruct "κ'" as "[κ' κ'₊]"=>/=.
    iMod (ty_own_proph_uniq_body with "LFT In In' uniq κ'") as "Upd"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "uniqs κ'₊") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>(%&%&%& [ζl ξ] & Touniq) >(%&%&%& [ζl' ξl] & Touniqs)] !>".
    iDestruct (proph_tok_combine with "ζl ζl'") as (?) "[ζζl Toζζl]".
    iDestruct (proph_tok_combine with "ξ ξl") as (?) "[ξl Toξl]".
    iDestruct (proph_tok_combine with "ζζl ξl") as (?) "[ζζξl Toζζξl]".
    iExists (_ :: _), _. simpl. iFrame "ζζξl". iSplit. { iPureIntro. constructor; done. }
    iIntros "ζζξl". iDestruct ("Toζζξl" with "ζζξl") as "[ζζl ξl]".
    iDestruct ("Toζζl" with "ζζl") as "[ζl ζl']".
    iDestruct ("Toξl" with "ξl") as "[[ξ _] ξl]".
    iMod ("Touniq" with "[$ζl $ξ]") as "[$$]". done.
    by iMod ("Touniqs" with "[$ζl' $ξl]") as "[$$]".
  Qed.

  Lemma resolve_big_sepL_uniq_body {𝔄} (ty: type 𝔄) n (vπξil: vec _ n) d κ tid l E L q F :
    lctx_lft_alive E L κ → ↑lftN ∪ ↑prophN ⊆ F →
    lft_ctx -∗ proph_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i))
      ={F}=∗ |={F}▷=>^(S d) |={F}=>
      let φπ π := lforall (λ vπξi,
        let ξ := PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2 in π ξ = vπξi.1 π) vπξil in
      .⟨φπ⟩ ∗ llctx_interp L q.
  Proof.
    iIntros (??) "#LFT #PROPH #In #E L uniqs". iInduction vπξil as [|] "IH" forall (q l).
    { iApply step_fupdN_full_intro. iFrame "L". by iApply proph_obs_true. }
    iDestruct "uniqs" as "[uniq uniqs]". iDestruct "L" as "[L L₊]"=>/=.
    iMod (resolve_uniq_body with "LFT PROPH In E L uniq") as "Upd"; [done..|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "L₊ uniqs") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>[Obs $] >[Obs' $]]". by iCombine "Obs Obs'" as "$".
  Qed.

  Lemma real_big_sepL_uniq_body {𝔄 𝔅} (ty: type 𝔄) n (vπξil: vec _ n)
      d κ tid l E L (f: _ → 𝔅) q F :
    lctx_lft_alive E L κ → real E L ty f → ↑lftN ⊆ F →
    lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i))
      ={F}=∗ |={F}▷=>^(S d) |={F}=>
      ⌜∃v, vapply (vmap ((f ∘.) ∘ fst) vπξil) = const v⌝ ∗ llctx_interp L q ∗
      ([∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)).
  Proof.
    iIntros (???) "#LFT #E L uniqs". iInduction vπξil as [|] "IH" forall (q l).
    { iApply step_fupdN_full_intro. iIntros "!>!>". iFrame "L".
      iSplit; [|done]. by iExists [#]. }
    iDestruct "uniqs" as "[uniq uniqs]". iDestruct "L" as "[L L₊]"=>/=.
    iMod (real_uniq_body with "LFT E L uniq") as "Upd"; [done..|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "L₊ uniqs") as "Upd'".
    iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand _ _ (S _) with "Upd").
    iIntros "!> [>([%v ->]&$&$) >([%vl %Eq]&$&$)] !%". exists (v ::: vl).
    fun_ext=>/= ?. by rewrite Eq.
  Qed.

  Lemma incl_big_sepL_uniq_body {𝔄} (ty ty': type 𝔄) vπξil d κ κ' tid l :
  (∀vπ ξl, ty.(ty_proph) vπ ξl ↔ ty'.(ty_proph) vπ ξl) →
    κ' ⊑ κ -∗ □ (∀vπ d tid vl, ty.(ty_own) vπ d tid vl ↔ ty'.(ty_own) vπ d tid vl) -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty vπξi.1 vπξi.2 d κ tid (l +ₗ[ty] i)) -∗
    [∗ list] i ↦ vπξi ∈ vπξil, uniq_body ty' vπξi.1 vπξi.2 d κ' tid (l +ₗ[ty] i).
  Proof.
    iIntros (InProph) "#InLft #EqOwn uniqs". iInduction vπξil as [|] "IH" forall (l); [done|].
    iDestruct "uniqs" as "[uniq uniqs]".
    iDestruct (incl_uniq_body with "InLft EqOwn uniq") as "$"=>/=. done.
    setoid_rewrite <-shift_loc_assoc_nat. iDestruct ("IH" with "uniqs") as "$".
  Qed.

  Lemma uniq_intro_vec {𝔄 n} (vπl: vec (proph 𝔄) n) d (ty: type 𝔄) E :
    ↑prophN ∪ ↑uniqN ⊆ E → proph_ctx -∗ uniq_ctx ={E}=∗ ∃ξil,
      [∗ list] vπξi ∈ vzip vπl ξil,
        let ξ := PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2 in
        .VO[ξ] vπξi.1 d ∗ .PC[ξ, ty.(ty_proph)] vπξi.1 d.
  Proof.
    iIntros (?) "#PROPH #UNIQ". iInduction vπl as [|vπ] "IH".
    { iModIntro. by iExists [#]. }
    iMod (uniq_intro vπ with "PROPH UNIQ") as (?) "?"; [done|].
    iMod "IH" as (?) "?". iModIntro. iExists (_:::_). iFrame.
  Qed.

  Lemma uniq_proph_tok_vec {𝔄 n} (vπξil: vec (proph 𝔄 * _) n) d (P: (proph 𝔄) → _) :
    ([∗ list] vπξi ∈ vπξil,
      let ξ := PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2 in
      .VO[ξ] vπξi.1 d ∗ .PC[ξ, P] vπξi.1 d) -∗
    let ξl := map (λ vπξi, PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2) vπξil in
    1:+[ξl] ∗ (1:+[ξl] -∗ [∗ list] vπξi ∈ vπξil,
      let ξ := PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2 in
      .VO[ξ] vπξi.1 d ∗ .PC[ξ, P] vπξi.1 d).
  Proof.
    iIntros "VoPcs". iInduction vπξil as [|] "IH". { iSplitL; by [|iIntros]. }
    iDestruct "VoPcs" as "[[Vo Pc] VoPcs]"=>/=.
    iDestruct (uniq_proph_tok with "Vo Pc") as "($&$& ToPc)".
    iDestruct ("IH" with "VoPcs") as "[$ ToVoPcs]". iIntros "[ξ ξl]".
    iDestruct ("ToPc" with "ξ") as "$". iDestruct ("ToVoPcs" with "ξl") as "$".
  Qed.

  Lemma proph_dep_prvars {𝔄 n} (vπξil: vec (proph 𝔄 * _) n) :
    let ξl := map (λ vπξi, PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2) vπξil in
    let vπl' := vmap (λ vπξi (π: proph_asn),
      π (PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2): 𝔄) vπξil in
    vapply vπl' ./[𝔄] ξl.
  Proof.
    elim: vπξil; [done|]=>/= ????. apply (proph_dep_vec_S [_]); [|done].
    apply proph_dep_one.
  Qed.

  Lemma merge_big_sepL_proph_ctrl_mt_ty_own {𝔄 n}
      (vπl: vec _ n) ξil (ty: type 𝔄) d tid l:
    ⧖(S d) -∗
    ([∗ list] vπξi ∈ vzip vπl ξil,
      .PC[PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2, ty.(ty_proph)] vπξi.1 d) -∗
    ([∗ list] i ↦ vπ ∈ vπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) vπ d tid) -∗
    [∗ list] i ↦ vπξi ∈ vzip vπl ξil, ∃vπ' d', ⧖(S d') ∗
      .PC[PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2, ty.(ty_proph)] vπ' d' ∗
      (l +ₗ[ty] i) ↦∗: ty.(ty_own) vπ' d' tid.
  Proof.
    iIntros "#⧖ Pcs ↦tys". iInduction vπl as [|] "IH" forall (l); inv_vec ξil=>//= ??.
    iDestruct "Pcs" as "[Pc Pcs]". iDestruct "↦tys" as "[(%& ↦ & ty) ↦tys]".
    setoid_rewrite <-shift_loc_assoc_nat. iDestruct ("IH" with "Pcs ↦tys") as "$".
    iExists _, _. iFrame "⧖ Pc". iExists _. iFrame.
  Qed.

  Lemma split_big_sepL_proph_ctrl_mt_ty_own {𝔄 n}
      (vπξil: vec _ n) (ty: type 𝔄) dex tid l :
    proph_ctx -∗ ⧖(S dex) -∗
    ([∗ list] i ↦ vπξi ∈ vπξil, ∃vπ' d', ⧖(S d') ∗
      .PC[PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2, ty.(ty_proph)] vπ' d' ∗
      (l +ₗ[ty] i) ↦∗: ty.(ty_own) vπ' d' tid) -∗
    ∃wπl d, ⧖(S d) ∗
      ([∗ list] vπξiwπ ∈ vzip vπξil wπl,
        (.$ PrVar (𝔄 ↾ prval_to_inh vπξiwπ.1.1) vπξiwπ.1.2) :={ty.(ty_proph)}= vπξiwπ.2) ∗
      ([∗ list] i ↦ wπ ∈ wπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) wπ d tid).
  Proof.
    iIntros "#PROPH #⧖ex Pc↦tys". iInduction vπξil as [|] "IH" forall (l).
    { iExists [#], _. by iFrame "⧖ex"=>/=. }
    iDestruct "Pc↦tys" as "[(%&%& ⧖ & Pc & ↦ty) Pc↦tys]".
    iDestruct (proph_ctrl_eqz' with "PROPH Pc") as "Eqz".
    setoid_rewrite <-shift_loc_assoc_nat.
    iDestruct ("IH" with "Pc↦tys") as (??) "(⧖' & Eqzs & ↦tys)".
    iCombine "⧖ ⧖'" as "⧖". iExists (_:::_), _=>/=. iFrame "⧖ Eqz Eqzs".
    iSplitL "↦ty"; iClear "#"; iStopProof.
    - do 3 f_equiv. apply ty_own_depth_mono. lia.
    - setoid_rewrite shift_loc_assoc_nat. do 6 f_equiv. apply ty_own_depth_mono. lia.
  Qed.

  Lemma proph_eqz_prvars {𝔄 n} vπξil (wπl: vec (proph 𝔄) n) (P: (proph 𝔄) → _) :
    ([∗ list] vπξiwπ ∈ vzip vπξil wπl,
      (.$ PrVar (𝔄 ↾ prval_to_inh vπξiwπ.1.1) vπξiwπ.1.2) :={P}= vπξiwπ.2) -∗
    let vπl := vmap (λ vπξi (π: proph_asn),
      π (PrVar (𝔄 ↾ prval_to_inh vπξi.1) vπξi.2): 𝔄) vπξil in
    vapply vπl :={λ vπ ξl, exists ξll, ξl = mjoin ξll /\ Forall2 P (vfunsep vπ) ξll}= vapply wπl.
  Proof.
    iIntros "Eqzs". iInduction vπξil as [|] "IH"; inv_vec wπl=>/= *.
    { iApply proph_eqz_refl. }
    iDestruct "Eqzs" as "[Eqz Eqzs]". iDestruct ("IH" with "Eqzs") as "Eqz'".
    iApply proph_eqz_mono; [|iApply (proph_eqz_constr2 vcons' with "Eqz Eqz'")].
    intros ?(?&->&?). inversion_clear H. eexists _, _, _, _.  intuition. fun_ext=>?/=. done. done. eexists _. done.
  Qed.

  Definition eq_rect_vec {A n m} (v: vec A n) (eq: n = m) := (eq_rect _ (λ n, vec A n) v _ eq).

  Lemma eq_rect_vec_to_list {A} n m (v: vec A n) (eq: n = m): (vec_to_list (eq_rect_vec v eq)) = (vec_to_list v).
  Proof. assert (eq' := eq). revert eq. rewrite -eq'. intros ?.  rewrite (eq_pi _ _ eq eq_refl). done. Qed.

  Lemma proph_eqz_vec_to_list {𝔄 n} (vπl: (vec _ n)) (vπl': (vec _ n)) (P: (proph 𝔄) → _) :
    vapply vπl :={λ vπ ξl, exists ξll, ξl = mjoin ξll /\ Forall2 P (vfunsep vπ) ξll}= vapply vπl' -∗
    lapply vπl :={λ vπ ξl, exists aπl ξll, ξl = mjoin ξll /\ vπ = lapply aπl /\ Forall2 P aπl ξll}= lapply vπl'.
  Proof.
    iIntros "Eqz". rewrite -2! vec_to_list_apply. iApply proph_eqz_mono; [|iApply (proph_eqz_constr with "Eqz")].
    intros ? (?&?&?&?&?). eexists (vapply (eq_rect_vec (list_to_vec x) _)). rewrite H0 vec_to_list_apply semi_iso' eq_rect_vec_to_list vec_to_list_to_vec.
    intuition. eexists _. done. Unshelve. 
    erewrite <- fmap_length. rewrite vec_to_list_apply /lapply in H0. erewrite <- (equal_f H0 inhabitant).
    rewrite fmap_length vec_to_list_length. reflexivity.
  Qed.
End uniq_array_util.
