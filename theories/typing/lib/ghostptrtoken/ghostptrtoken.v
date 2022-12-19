From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section token.
  Context `{!typeG Σ}.

  Lemma split_mt_token {𝔄} d l' amπ Φ :
    (l' ↦∗: (λ vl, [S(d') := d] ∃ (aπm: gmap loc (proph 𝔄)),
      ⌜vl = [] ∧ amπ = mapply aπm⌝ ∗ Φ d' aπm)) ⊣⊢
    [S(d') := d] ∃(aπm: gmap loc (proph 𝔄)),
      ⌜amπ = mapply aπm⌝ ∗ l' ↦∗ [] ∗ Φ d' aπm.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". case d=>// ?. iDestruct "big" as (?[->->]) "Φ".
      iExists _. iSplit; [done|iFrame].
    - iIntros "big". case d=>// ?. iDestruct "big" as (?->) "(↦ & ?)".
      iExists []. iFrame "↦". iExists _. by iFrame.
  Qed.

  Lemma split_mt_token' {𝔄} l' amπ Φ :
    (l' ↦∗: (λ vl, ∃(aπm: gmap loc (proph 𝔄)),
      ⌜vl = [] ∧ amπ = mapply aπm⌝ ∗ Φ aπm)) ⊣⊢
    ∃(aπm: gmap loc (proph 𝔄)),
      ⌜amπ = mapply aπm⌝ ∗ l' ↦∗ [] ∗ Φ aπm.
  Proof.
    set Φ' := λ _: nat, Φ. have ->: Φ = Φ' 0 by done.
    by apply (split_mt_token (S _)).
  Qed.

  Lemma ty_share_big_sepM {𝔄} (ty: type 𝔄) E aπm d κ tid q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
    &{κ} ([∗ map] l ↦ aπ ∈ aπm, l ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=>
        ([∗ map] l ↦ aπ ∈ aπm, ty.(ty_shr) aπ d κ tid l) ∗ q.[κ].
  Proof.
    rewrite big_opM_map_to_list.
    rewrite big_opM_map_to_list.
    iIntros (?) "#LFT #In Bor κ".
    iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    iInduction (map_to_list aπm) as [|] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. by iFrame. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "Bors" as "[Bor Bors]".
    iMod (ty_share with "LFT In Bor κ") as "Toshr"; [done|].
    iMod ("IH" with "κ₊ Bors") as "Toshrs".
    iCombine "Toshr Toshrs" as "Toshrs". iApply (step_fupdN_wand with "Toshrs").
    by iIntros "!> [>[$$] >[$$]]".
  Qed.

  Lemma trans_big_sepM_mt_ty_own {𝔄} (ty: type 𝔄) aπm d tid :
    ([∗ map] l ↦ aπ ∈ aπm, l ↦∗: ty.(ty_own) aπ d tid) ⊣⊢
    ∃(wll: vec (list val) (length (map_to_list aπm))), ([∗ list] elt ∈ (vzip (vmap (λ x, x.1) (Vector.of_list (map_to_list aπm))) wll), elt.1 ↦∗ elt.2) ∗
      ([∗ list] aπwl ∈ vzip (vmap (λ x, x.2) (Vector.of_list (map_to_list aπm))) wll, ty.(ty_own) aπwl.1 d tid aπwl.2).
  Proof.
    rewrite big_opM_map_to_list.
    iSplit.
    - iIntros "↦owns". iInduction (map_to_list aπm) as [|] "IH"=>/=.
      { iExists [#]. iSplit; [done|done]. }
      iDestruct "↦owns" as "[(%& ↦ & ty) ↦owns]".
      iDestruct ("IH" with "↦owns") as (?) "(↦s & tys)".
      iExists (_:::_). iFrame.
    - iIntros "(%& ↦s & tys)". iInduction (map_to_list aπm) as [|] "IH"; [done|].
      inv_vec wll=>/= ??.
      iDestruct "↦s" as "[↦ ↦s]". iDestruct "tys" as "[ty tys]".
      iSplitL "↦ ty".
      { iExists _. iFrame. }
      iApply ("IH" with "↦s tys").
  Qed.

  Definition list_to_gmap {A} `{Countable K} : list (K * A) → gmap K A := list_to_map.

  Lemma remove_mapply {A B} `{Countable K} (aπm: gmap K (A → B)):
    mapply aπm = λ π, list_to_map (prod_map id (.$ π) <$> (map_to_list aπm)).
  Proof.
    apply functional_extensionality. intros.
    rewrite list_to_map_fmap. rewrite list_to_map_to_list. exact.
  Qed.

  Lemma zip_to_prod_map{A B C} (f: B → C) (l: list (A * B)):
    (zip l.*1 (f <$> l.*2)) = (prod_map id f) <$> l.
  Proof.
    rewrite zip_with_fmap_r. rewrite zip_with_fst_snd.
    congr fmap.
    intros. apply functional_extensionality. intros. destruct x.
    unfold prod_map. unfold uncurry. unfold Datatypes.uncurry. unfold fst. unfold snd. unfold id. reflexivity.
  Qed.

  Lemma ty_own_proph_big_sepM_mt {𝔄} (ty: type 𝔄) (n: nat) E aπm d tid κ q :
  ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
  ([∗ map] l ↦ aπ ∈ aπm, l ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜mapply aπm ./ ξl⌝ ∗ q':+[ξl] ∗
      (q':+[ξl] ={E}=∗
        ([∗ map] l ↦ aπ ∈ aπm, l ↦∗: ty.(ty_own) aπ d tid) ∗ q.[κ]).
  Proof.
    rewrite {1} trans_big_sepM_mt_ty_own. iIntros (?) "LFT In (%& ↦ & tys) κ".
    iMod (ty_own_proph_big_sepL with "LFT In tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _.
    apply proph_dep_constr with vec_to_list _ _  in H0. rewrite vec_to_list_apply in H0.
    rewrite vec_to_list_map in H0. rewrite vec_to_list_to_vec in H0.
    apply proph_dep_constr with (λ x, zip ((map_to_list aπm).*1) x) _ _  in H0.
    iSplit. iPureIntro.
    rewrite remove_mapply.
    apply proph_dep_constr.
    unfold compose in H0. unfold lapply in H0.
    intros π π' eqv. specialize (H0 π π' eqv).
    rewrite 2! zip_to_prod_map in H0. exact H0.
    iIntros "{$ξl}ξl".
    iMod ("Totys" with "ξl") as "[tys $]".
    rewrite trans_big_sepM_mt_ty_own.
    iModIntro. iExists _. iFrame.
  Qed.

  Lemma ty_shr_proph_big_sepM {𝔄} (ty: type 𝔄) (n: nat) E aπm d κ tid κ' q :
  ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
  ([∗ map] l ↦ aπ ∈ aπm, ty.(ty_shr) aπ d κ tid l) -∗ q.[κ']
    ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜mapply aπm ./ ξl⌝ ∗ q':+[ξl] ∗
      (q':+[ξl] ={E}=∗ q.[κ']).
  Proof.
    iIntros (?) "#LFT #In #In' tys κ'".
    rewrite big_opM_map_to_list.
    setoid_rewrite remove_mapply.
    iInduction (map_to_list aπm) as [|] "IH" forall (q).
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      iFrame "κ'". iSplit.
      iPureIntro. intros π π' eqv. rewrite 2! fmap_nil. reflexivity.
      iSplit; [done|].
      by iIntros. }
    iDestruct "κ'" as "[κ' κ'₊]". iDestruct "tys" as "[ty tys]".
    iMod (ty_shr_proph with "LFT In In' ty κ'") as "Upd"; [done|].
    iMod ("IH" with "tys κ'₊") as "Upd'".
    iIntros "!>!>". iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "[>(%&%&%& ξl & Toκ') >(%&%&%& ζl & Toκ'₊)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iFrame "ξζl". iSplit.
    iPureIntro. intros π π' eqv. 
    rewrite 2! fmap_cons. unfold list_to_gmap. unfold list_to_gmap in H1.
    rewrite 2! list_to_map_cons. congr insert. 
    apply H0. intros ξ ξin. apply eqv. apply elem_of_app. left. exact.
    apply H1. intros ξ ξin. apply eqv. apply elem_of_app. right. exact.  
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toκ'" with "ξl") as "$". by iMod ("Toκ'₊" with "ζl") as "$".
  Qed.

  (* Rust's GhostPtrToken<T> *)
  Program Definition ghostptrtoken_ty {𝔄} (ty: type 𝔄) : type (fmapₛ 𝔄) := {|
    ty_size := 0;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own amπ d tid vl :=
      [S(d') := d] ∃(aπm: gmap loc (proph 𝔄)),
        ⌜vl = [] ∧ amπ = mapply aπm⌝ ∗
        ▷ ([∗ map] l ↦ aπ ∈ aπm, (l) ↦∗: ty.(ty_own) aπ d' tid) ∗
        ([∗ map] l ↦ _ ∈ aπm, freeable_sz' ty.(ty_size) l);
    ty_shr amπ d κ tid l' :=
      [S(d') := d] ∃(aπm: gmap loc (proph 𝔄)),
        ⌜amπ = mapply aπm⌝ ∗
        ▷ [∗ map] l ↦ aπ ∈ aπm, ty.(ty_shr) aπ d' κ tid l;
  |}%I.
  Next Obligation.
    iIntros (???[]??) "token //". by iDestruct "token" as (?[-> _]) "?".
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 11 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 7 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|]. iIntros "#? (%&?& All)".
    iExists _. iSplit; [done|].
    rewrite !big_sepM_forall. iIntros "!> **".
    iApply ty_shr_lft_mono; by [|iApply "All"].
  Qed.
  Next Obligation.
    iIntros (???? d) "*% #LFT In Bor κ". rewrite split_mt_token. case d.
    { by iMod (bor_persistent with "LFT Bor κ") as "[>[] _]". }
    move=> ?. do 1 (iMod (bor_exists_tok with "LFT Bor κ") as (?) "[Bor κ]"; [done|]).
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor↦ Bor]"; [done|].
    iMod (bor_fracture (λ q', _ ↦∗{q'} _)%I with "LFT Bor↦") as "Bor↦"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_later_tok with "LFT Bor κ") as "Borκ"; [done|].
    iIntros "/=!>!>!>". iMod "Borκ" as "[Bor κ]".
    iMod (ty_share_big_sepM with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|?]) "*% LFT In token κ/="; [done|].
    iDestruct "token" as (?[->->]) "(↦tys & †)". iIntros "!>!>!>".
    iMod (ty_own_proph_big_sepM_mt with "LFT In ↦tys κ") as "Upd"; [done|done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _. iSplit; [done|].
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|?]) "*%*% LFT In In' token κ'/="; [done|].
    iDestruct "token" as (?->) "tys". iIntros "!>!>!>".
    iMod (ty_shr_proph_big_sepM with "LFT In In' tys κ'") as "Toκ'"; [done|done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Toκ'").
    iIntros ">(%&%&%& ξl & Toκ') !>". iExists _, _. iSplit; [done|].
    iIntros "{$ξl}ξl". by iMod ("Toκ'" with "ξl") as "$".
  Qed.

  Global Instance vec_ty_ne {𝔄} : NonExpansive (@ghostptrtoken_ty 𝔄).
  Proof.
    constructor.
    exact.  
    unfold ty_lfts. unfold ghostptrtoken_ty. eapply ty_lfts_ne. exact. 
    unfold ty_E. unfold ghostptrtoken_ty. eapply ty_E_ne. exact.
    unfold ty_own. unfold ghostptrtoken_ty.
    assert (ty_size x = ty_size y). eapply ty_size_ne. exact.
    rewrite H0.
    intros ????. do 13 f_equiv. apply ty_own_ne; [done|done|done|done|done].
    unfold ty_shr. unfold ghostptrtoken_ty.
    intros ?????. do 9 f_equiv.
    apply ty_shr_ne; [done|done|done|done|done|done].
  Qed.
End token.
