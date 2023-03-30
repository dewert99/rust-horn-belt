From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Notation "'[∗' 'list]' ( k , x ) ∈ l , P" := ((big_opL bi_sep (fun _ '(k, x) => P) l))%core
(at level 200, l at level 10, k, x at level 1, right associativity)
  : bi_scope.

Notation al_fmap f := (fmap (prod_map id f)).

Notation list_to_gmap := (@list_to_map loc _ (gmap loc _)).

Lemma elem_of_list_to_map_2' {K A M} `{FinMap K M} (l: list (K * A)) i x:
  ((list_to_map l): M A) !! i = Some x → ∃ r, l ≡ₚ (i, x) :: r /\ ((list_to_map l): M A) = <[i:=x]>(list_to_map r).
Proof.
  intros. induction l as [|[i' x'] r]. apply elem_of_list_to_map_2 in H7. apply elem_of_nil in H7. done.
  destruct (decide (i'=i)) as [->|?].
  rewrite list_to_map_cons lookup_insert in H7.
  injection H7 as <-. exists r. split. reflexivity. 
  rewrite list_to_map_cons. reflexivity.
  rewrite list_to_map_cons lookup_insert_ne in H7; [|done].
  destruct (IHr H7) as (r'&perm&ltm).
  exists ((i', x')::r'). split. rewrite Permutation_swap -perm. done.
  rewrite 2! list_to_map_cons ltm insert_commute.
  done. done.
Qed.

Section token.

  Context `{!typeG Σ}.

  Global Instance big_sepAL_persistent {K A} (Φ: K → A → iProp Σ) (l: list (K*A)):
    (∀ k x, Persistent (Φ k x)) → Persistent ([∗ list] (k, x) ∈ l, Φ k x).
  Proof.
    intros. apply big_sepL_persistent. intros ?[??]. done.
  Qed.

  Definition alapply {A B K} (fl: list (K*(B → A))) (x: B) := (al_fmap (.$ x) fl).

  Lemma split_mt_token {𝔄} d l' alπ Φ :
    (l' ↦∗: (λ vl, [S(d') := d] ∃ (aπl: list (loc * (proph 𝔄))),
      ⌜vl = [] ∧ alπ = alapply aπl⌝ ∗ Φ d' aπl)) ⊣⊢
    [S(d') := d] ∃(aπl: list (loc * (proph 𝔄))),
      ⌜alπ = alapply aπl⌝ ∗ l' ↦∗ [] ∗ Φ d' aπl.
  Proof.
    iSplit.
    - iIntros "(%& ↦ & big)". case d=>// ?. iDestruct "big" as (?[->->]) "Φ".
      iExists _. iSplit; [done|iFrame].
    - iIntros "big". case d=>// ?. iDestruct "big" as (?->) "(↦ & ?)".
      iExists []. iFrame "↦". iExists _. by iFrame.
  Qed.

  Lemma split_mt_token' {𝔄} l' alπ Φ :
    (l' ↦∗: (λ vl, ∃(aπl: list (loc * (proph 𝔄))),
      ⌜vl = [] ∧ alπ = alapply aπl⌝ ∗ Φ aπl)) ⊣⊢
    ∃(aπl: list (loc * (proph 𝔄))),
      ⌜alπ = alapply aπl⌝ ∗ l' ↦∗ [] ∗ Φ aπl.
  Proof.
    set Φ' := λ _: nat, Φ. have ->: Φ = Φ' 0 by done.
    by apply (split_mt_token (S _)).
  Qed.

  Lemma ty_share_big_sepAL {𝔄} (ty: type 𝔄) E aπl d κ tid q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
    &{κ} ([∗ list] (l, aπ) ∈ aπl, l ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=>
        ([∗ list] (l, aπ) ∈ aπl, ty.(ty_shr) aπ d κ tid l) ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT #In Bor κ".
    iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    iInduction aπl as [|[l x]] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. by iFrame. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "Bors" as "[Bor Bors]".
    iMod (ty_share with "LFT In Bor κ") as "Toshr"; [done|].
    iMod ("IH" with "κ₊ Bors") as "Toshrs".
    iCombine "Toshr Toshrs" as "Toshrs". iApply (step_fupdN_wand with "Toshrs").
    by iIntros "!> [>[$$] >[$$]]".
  Qed.

  Lemma trans_big_sepAL_mt_ty_own {𝔄} (ty: type 𝔄) aπl d tid :
    ([∗ list] (l, aπ) ∈ aπl, l ↦∗: ty.(ty_own) aπ d tid) ⊣⊢
    ∃(wll: vec (list val) (length aπl)), ([∗ list] elt ∈ (vzip (vmap (λ x, x.1) (Vector.of_list aπl)) wll), elt.1 ↦∗ elt.2) ∗
      ([∗ list] aπwl ∈ vzip (vmap (λ x, x.2) (Vector.of_list aπl)) wll, ty.(ty_own) aπwl.1 d tid aπwl.2).
  Proof.
    iSplit.
    - iIntros "↦owns". iInduction aπl as [|[l x]] "IH"=>/=.
      { iExists [#]. iSplit; [done|done]. }
      iDestruct "↦owns" as "[(%& ↦ & ty) ↦owns]".
      iDestruct ("IH" with "↦owns") as (?) "(↦s & tys)".
      iExists (_:::_). iFrame.
    - iIntros "(%& ↦s & tys)". iInduction aπl as [|[l x]] "IH"; [done|].
      inv_vec wll=>/= ??.
      iDestruct "↦s" as "[↦ ↦s]". iDestruct "tys" as "[ty tys]".
      iSplitL "↦ ty".
      { iExists _. iFrame. }
      iApply ("IH" with "↦s tys").
  Qed.

  (* Lemma remove_alapply {A B} `{Countable K} (aπl: gmap K (A → B)):
    alapply aπl = λ π, list_to_map (prod_map id (.$ π) <$> (map_to_list aπl)).
  Proof.
    apply functional_extensionality. intros.
    rewrite list_to_map_fmap. rewrite list_to_map_to_list. exact.
  Qed. *)

  Lemma zip_to_prod_map{A B C} (f: B → C) (l: list (A * B)):
    (zip l.*1 (f <$> l.*2)) = al_fmap f l.
  Proof.
    rewrite zip_with_fmap_r. rewrite zip_with_fst_snd.
    congr fmap.
    intros. apply functional_extensionality. intros. destruct x.
    unfold prod_map. unfold uncurry. unfold Datatypes.uncurry. unfold fst. unfold snd. unfold id. reflexivity.
  Qed.

  Lemma ty_own_proph_big_sepAL_mt {𝔄} (ty: type 𝔄) (n: nat) E aπl d tid κ q :
  ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
  ([∗ list] (l, aπ) ∈ aπl, l ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξll q', ⌜Forall2 ty.(ty_proph) aπl.*2 ξll⌝ ∗ q':+[mjoin ξll] ∗
      (q':+[mjoin ξll] ={E}=∗
        ([∗ list] (l, aπ) ∈ aπl, l ↦∗: ty.(ty_own) aπ d tid) ∗ q.[κ]).
  Proof.
    rewrite {1} trans_big_sepAL_mt_ty_own. iIntros (?) "LFT In (%& ↦ & tys) κ".
    iMod (ty_own_proph_big_sepL with "LFT In tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&(%&->&%)& ξl & Totys) !>".
    iExists _, _. rewrite vec_to_list_map vec_to_list_to_vec in H0.
    iSplit; [done|]. iIntros "{$ξl}ξl".
    iMod ("Totys" with "ξl") as "[tys $]".
    rewrite trans_big_sepAL_mt_ty_own.
    iModIntro. iExists _. iFrame.
  Qed.

  Lemma ty_shr_proph_big_sepAL {𝔄} (ty: type 𝔄) (n: nat) E aπl d κ tid κ' q :
  ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
  ([∗ list] (l, aπ) ∈ aπl, ty.(ty_shr) aπ d κ tid l) -∗ q.[κ']
    ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξll q', ⌜Forall2 ty.(ty_proph) aπl.*2 ξll⌝ ∗ q':+[mjoin ξll] ∗
      (q':+[mjoin ξll] ={E}=∗ q.[κ']).
  Proof.
    iIntros (?) "#LFT #In #In' tys κ'".
    unfold alapply.
    iInduction aπl as [|[l x]] "IH" forall (q) =>/=.
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

  Definition big_sepAL {K A} (Φ: K → A → iProp Σ) (l: list (K*A)) :=  ([∗ list] (k, x) ∈ l, Φ k x)%I.

  (* Lemma all_share_peristent {𝔄} (ty: type 𝔄) aπl d' κ tid : Persistent (all_share 𝔄 ty aπl d' κ tid).
  apply big_sepAL_persistent. intros. apply ty_shr_persistent. Qed. *)

  (* Rust's GhostPtrToken<T> *)
  Program Definition ghostptrtoken_ty {𝔄} (ty: type 𝔄) : type (listₛ (locₛ * 𝔄)) := {|
    ty_size := 0;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_proph alπ ξl := exists (aπl: list (loc * (proph 𝔄))) ξll,
      ξl = mjoin ξll /\ alπ = alapply aπl /\ Forall2 ty.(ty_proph) aπl.*2 ξll;
    ty_own alπ d tid vl :=
      [S(d') := d] ∃(aπl: list (loc * (proph 𝔄))),
        ⌜vl = [] ∧ alπ = alapply aπl⌝ ∗
        ▷ (big_sepAL (λ l aπ, l ↦∗: ty.(ty_own) aπ d' tid) aπl) ∗
        (big_sepAL (λ l _, freeable_sz' ty.(ty_size) l) aπl);
    ty_shr alπ d κ tid l' :=
      [S(d') := d] ∃(aπl: list (loc * (proph 𝔄))),
        ⌜alπ = alapply aπl⌝ ∗
        ▷ (big_sepAL (λ l aπ, ty.(ty_shr) aπ d' κ tid l) aπl);
  |}%I.
  Next Obligation.
    iIntros (???[]??) "token //". by iDestruct "token" as (?[-> _]) "?".
  Qed.
  Next Obligation. unfold big_sepAL.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 12 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation. unfold big_sepAL.
    move=> ??[|?][|?]*/=; try (by iIntros); [lia|]. do 8 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation. unfold big_sepAL.
    move=> ?????[|?]*; [by iIntros|]. iIntros "#? (%&?& All)".
    iExists _. iSplit; [done|]. iNext.
    erewrite !big_sepL_forall; [|intros ?[??]; by apply ty_shr_persistent ..]. iIntros (?[??]?).
    iApply ty_shr_lft_mono; by [|iApply ("All" $! _ (_,_))].
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
    iMod (ty_share_big_sepAL with "LFT In Bor κ") as "Toshrs"; [done|].
    iApply (step_fupdN_wand with "Toshrs"). iIntros "!> >[?$] !>".
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|?]) "*% LFT In token κ/="; [done|].
    iDestruct "token" as (?[->->]) "(↦tys & †)". iIntros "!>!>!>".
    iMod (ty_own_proph_big_sepAL_mt with "LFT In ↦tys κ") as "Upd"; [done|done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _. iSplit. iExists _, _. done.
    iIntros "{$ξl}ξl". iMod ("Totys" with "ξl") as "[tys $]". iModIntro.
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (????[|?]) "*%*% LFT In In' token κ'/="; [done|].
    iDestruct "token" as (?->) "tys". iIntros "!>!>!>".
    iMod (ty_shr_proph_big_sepAL with "LFT In In' tys κ'") as "Toκ'"; [done|done|].
    iIntros "!>!>". iApply (step_fupdN_wand with "Toκ'").
    iIntros ">(%&%&%& ξl & Toκ') !>". iExists _, _. iSplit. iExists _, _. done.
    iIntros "{$ξl}ξl". by iMod ("Toκ'" with "ξl") as "$".
  Qed.
  Next Obligation.
    simpl. intros ????(?&?&->&->&?). unfold alapply.
    eassert (proph_dep _ _ _); [|unfold proph_dep; setoid_rewrite <- zip_to_prod_map; exact H0].
    apply proph_dep_constr. by eapply ty_proph_weaken_big_sepL'.
  Qed.

  Global Instance ghostptrtoken_ty_ne {𝔄} : NonExpansive (@ghostptrtoken_ty 𝔄).
  Proof.
    rewrite /ghostptrtoken_ty /big_sepAL. solve_ne_type; simpl. done.
  Qed.
End token.
