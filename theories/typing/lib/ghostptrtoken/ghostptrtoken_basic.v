From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_basic.
  Context `{!typeG Σ}.

  Lemma real_big_sepM_ty_shr {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅)
    aπm (d: nat) κ tid E L F q :
    real E L ty f → ↑lftN ⊆ F → lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ map] l ↦ aπ ∈ aπm, ty.(ty_shr) aπ d κ tid l)
      ={F}▷=∗ |={F}▷=>^d |={F}=>
        ⌜∃bm, (fmap f) ∘ mapply aπm = const bm⌝ ∗ llctx_interp L q ∗
        [∗ map] l ↦ aπ ∈ aπm, ty.(ty_shr) aπ d κ tid l.
  Proof.
    setoid_rewrite big_opM_map_to_list.
    rewrite remove_mapply.
    iIntros ([_ Rl]?) "#LFT #E L tys". iInduction (map_to_list aπm) as [|] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. iFrame "L". iPureIntro. unfold compose. rewrite fmap_empty. by exists ∅. }
    iDestruct "tys" as "[ty tys]". iDestruct "L" as "[L L₊]".
    iMod (Rl with "LFT E L ty") as "Upd"; [done|].
    iMod ("IH" with "L₊ tys") as "Upd'". iCombine "Upd Upd'" as "Upd". iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iIntros "[>(%Eq &$&$) >(%Eq' &$&$)] !%".
    move: Eq=> [b Eq]. move: Eq'=> [bm Eq']. exists (<[a.1:=b]>bm).
    fun_ext=>/= π. rewrite fmap_insert. by move: (equal_f Eq π) (equal_f Eq' π)=>/= <-<-.
  Qed.

  Global Instance token_type_contractive 𝔄 : TypeContractive (ghostptrtoken_ty (𝔄:=𝔄)).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| |].
    - move=>/= > ->*. do 13 (f_contractive || f_equiv). by simpl in *.
    - intros ?????????????. unfold ty_shr. unfold ghostptrtoken_ty. do 9 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance token_send {𝔄} (ty: type 𝔄) : Send ty → Send (ghostptrtoken_ty ty).
  Proof. move=> ?>/=. by do 13 (f_equiv || move=>?). Qed.

  Global Instance token_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (ghostptrtoken_ty ty).
  Proof. move=> ?>/=. by do 9 (f_equiv || move=>?). Qed.

  Lemma token_resolve {𝔄} (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (ghostptrtoken_ty ty) (mforall Φ).
  Proof.
    iIntros (????[|]???) "#LFT #PROPH #E L token //=".
    iDestruct "token" as (?[->->]) "[↦tys _]". iIntros "!>!>!>".
    rewrite trans_big_sepM_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
    iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd").
    rewrite vec_to_list_map. rewrite vec_to_list_to_vec.
    setoid_rewrite map_Forall_to_list. setoid_rewrite map_to_list_fmap.
    unfold lapply. setoid_rewrite <- list_fmap_compose. setoid_rewrite lforall_Forall.
    setoid_rewrite Forall_fmap. by iIntros "!> H".
  Qed.

  Lemma token_resolve_just {𝔄} (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (ghostptrtoken_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma token_real {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=fmapₛ _) E L (ghostptrtoken_ty ty) (fmap f).
  Proof.
    move=> Rl. split; iIntros (???[|]) "*% LFT E L token //=".
    - iDestruct "token" as (?[->->]) "[↦tys †]". iIntros "!>!>!>".
      rewrite trans_big_sepM_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
      iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>".
      iSplit; last first.
      { iExists _. iFrame "†". iSplit; [done|]. iNext.
        rewrite trans_big_sepM_mt_ty_own. iExists _. iFrame. }
      iPureIntro. move: Eq=> [bl Eq]. exists (list_to_map(zip (map_to_list aπm).*1 (vec_to_list bl))). fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.
      rewrite 3! vec_to_list_map. rewrite vec_to_list_to_vec.
      rewrite -list_fmap_compose. rewrite zip_to_prod_map. rewrite list_to_map_fmap.
      unfold mapply. rewrite map_fmap_compose. rewrite list_to_map_to_list. reflexivity.
    - iDestruct "token" as (?) "[%Bor tys]". iIntros "!>!>!>".
      iMod (real_big_sepM_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">(%Eq &$& tys) !>". iSplit; [|iExists _; by iFrame].
      iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.  by rewrite Bor.
  Qed.

  Lemma token_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (ghostptrtoken_ty ty) (ghostptrtoken_ty ty') (fmap f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "(%EqSz &?&#Own&#Shr)".
    have Eq: ∀(aπm: gmap loc (proph 𝔄)), fmap f ∘ mapply aπm = mapply (fmap (f ∘.) aπm).
    { move=> ?. fun_ext=>/= ?. f_equal. unfold mapply. rewrite -2! map_fmap_compose. reflexivity. }
    do 2 (iSplit; [done|]). iSplit; iIntros "!>" (?[|]) "* token //=".
    - iDestruct "token" as (?[->->]) "(↦tys & †)". iExists  _.
      iSplit; [done|]. rewrite 2! big_opM_fmap. rewrite EqSz.
      iFrame "†".
      iNext.
      iApply (big_sepM_impl with "↦tys").
      iModIntro. iIntros (???) "↦tys". iDestruct "↦tys" as (?) "(↦&tys)". iExists vl.
      iFrame. iApply ("Own" with "tys").
    - iDestruct "token" as (?->) "↦". iExists _. rewrite Eq.
      iSplit; [done|].
      rewrite big_opM_fmap. iApply (big_sepM_impl with "↦").
      do 2 iModIntro. iIntros (???) "↦". iApply ("Shr" with "↦").
  Qed.
  Lemma token_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (ghostptrtoken_ty ty) (ghostptrtoken_ty ty') (fmap f) (fmap g).
  Proof. move=> [??]. split; by apply token_subtype. Qed.

  (* Rust's GhostPtrToken::new *)
  Definition ghostptrtoken_new: val :=
    fn: [] :=
      let: "r" := new [ #0] in
      let: "dummy" := new [ #0] in
      return: ["r"].

  Lemma ghostptrtoken_new_type {𝔄} (ty: type 𝔄) :
    typed_val ghostptrtoken_new (fn(∅) → ghostptrtoken_ty ty) (λ post _, post ∅).
  Proof.
    eapply type_fn; [apply _|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs". iMod persistent_time_receipt_0 as "⧖".
    wp_bind (new _). iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l) "[† _] ⧖". wp_seq.
    wp_bind (new _). iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l') "[†' _] ⧖".
    do 3 wp_seq.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const ∅] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full split_mt_token'. 
    iFrame "†". iNext. iExists ∅. iSplit.
    iPureIntro. apply functional_extensionality. intros. unfold mapply. by rewrite fmap_empty.
    rewrite heap_mapsto_vec_nil 2! big_opM_empty.
    iSplit; [done|done].
  Qed.
End ghostptrtoken_basic.

Global Hint Resolve token_resolve | 5 : lrust_typing.
Global Hint Resolve token_resolve_just token_subtype token_eqtype : lrust_typing.
