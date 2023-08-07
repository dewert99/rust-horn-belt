From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.ghostptrtoken Require Export permdata ghostseq.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Notation "'[∗' 'list]' ( k , x ) ∈ l , P" := ((big_sepL (fun _ '(k, x) => P) l))%core
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


  Program Definition ghostptrtoken_ty {𝔄} (ty: type 𝔄) : type (listₛ (locₛ * 𝔄)) :=
   (ghostseq_ty (permdata_ty ty)).
  

  Lemma ghostptrtoken_own_alt {𝔄} (ty: type 𝔄) alπ d tid vl:
    ty_own (ghostptrtoken_ty ty) alπ d tid vl ⊣⊢
      ∃(aπl: list (loc * (proph 𝔄))),
        ⌜vl = [] ∧ alπ = alapply aπl⌝ ∗
        ([∗ list] (l, aπ) ∈ aπl, [S(d') := d] ▷ l ↦∗: ty.(ty_own) aπ d' tid) ∗
        ([∗ list] (l, aπ) ∈ aπl, freeable_sz' ty.(ty_size) l).
  Proof. iSplit; iIntros "(%&(->&->)&X)"; iStopProof; 
    (induction aπl; [iIntros "_"; iExists []; do 4 (iSplit||iModIntro||done)|]).
    - iIntros "((%&%&(_&->)&X)&rest)". iDestruct (IHaπl with "rest") as "(%&(_&%)&tys&frees)". iExists ((l, vπ') :: aπl0).
    iSplit. iPureIntro. split; [done|]. fun_ext=>π. simpl. by rewrite H.
    destruct d; [done|]. iFrame. iDestruct "X" as "($&free)". rewrite freeable_sz_full. done.
    - simpl. destruct a. iIntros "((ty&tys)&(free&frees))".
    iDestruct (IHaπl with "[$tys $frees]") as "(%&(_&%)&X)". iExists (_ :: aπl0).
    iSplit. iPureIntro. split; [done|]. fun_ext=>π. simpl. by rewrite H.
    iFrame. iExists _, _. iSplit; [done|]. destruct d; iFrame. rewrite freeable_sz_full. done.
  Qed.

  Lemma ghostptrtoken_shr_alt {𝔄} (ty: type 𝔄) alπ d κ tid l:
  ty_shr (ghostseq_ty (permdata_ty ty)) alπ d κ tid l ⊣⊢
    ∃(aπl: list (loc * (proph 𝔄))),
    ⌜alπ = alapply aπl⌝ ∗
    ([∗ list] (l, aπ) ∈ aπl, [S(d') := d] ▷ ty.(ty_shr) aπ d' κ tid l).
  Proof. iSplit; iIntros "(%&->&X)"; iStopProof; 
    (induction aπl; [iIntros "_"; iExists []; do 4 (iSplit||iModIntro||done)|]).
    - iIntros "((%&%&->&X)&rest)". iDestruct (IHaπl with "rest") as "(%&%&tys)". iExists ((l0, vπ') :: aπl0).
    iSplit. iPureIntro. fun_ext=>π. simpl. by rewrite H.
    destruct d; [done|]. iFrame.
    - simpl. destruct a. iIntros "(ty&tys)".
    iDestruct (IHaπl with "tys") as "(%&%&X)". iExists (_ :: aπl0).
    iSplit. iPureIntro. fun_ext=>π. simpl. by rewrite H.
    iFrame. iExists _, _. iSplit; [done|]. destruct d; iFrame.
  Qed.

  Lemma split_mt_token {𝔄} (ty: type 𝔄) l' alπ d tid :
  (l' ↦∗: ty_own (ghostptrtoken_ty ty) alπ d tid ) ⊣⊢
  ∃(aπl: list (loc * (proph 𝔄))),
    ⌜alπ = alapply aπl⌝ ∗ l' ↦∗ [] ∗         
    ([∗ list] (l, aπ) ∈ aπl, [S(d') := d] ▷ l ↦∗: ty.(ty_own) aπ d' tid) ∗
    ([∗ list] (l, aπ) ∈ aπl, freeable_sz' ty.(ty_size) l).
  Proof. setoid_rewrite ghostptrtoken_own_alt.
    iSplit. iIntros "(%&↦&%&(->&?)&ty)". iExists _. iFrame.
    iIntros "(%&->&↦&ty)". iExists []. iFrame. iExists _. iFrame. done.
  Qed.
(* 
Lemma split_mt_token {𝔄} d l' alπ Φ :
  (l' ↦∗: (λ vl, [S(d') := d] ∃ (aπl: list (proph (loc * 𝔄))),
    ⌜vl = [] ∧ alπ = lapply aπl⌝ ∗ Φ d' aπl)) ⊣⊢
  [S(d') := d] ∃(aπl: list (loc * (proph 𝔄))),
    ⌜alπ = alapply aπl⌝ ∗ l' ↦∗ [] ∗ Φ d' aπl.
Proof.
  iSplit.
  - iIntros "(%& ↦ & big)". case d=>// ?. iDestruct "big" as (?[->->]) "Φ".
    iExists _. iSplit; [done|iFrame].
  - iIntros "big". case d=>// ?. iDestruct "big" as (?->) "(↦ & ?)".
    iExists []. iFrame "↦". iExists _. by iFrame.
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
  Qed. *)

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

  Global Instance ghostptrtoken_ty_ne {𝔄} : NonExpansive (@ghostptrtoken_ty 𝔄).
  Proof. solve_ne_type. done. Qed.
End token.
