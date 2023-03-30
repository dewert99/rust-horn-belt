From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_basic.
  Context `{!typeG Σ}.

  Lemma real_big_sepM_ty_shr {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅)
    aπl (d: nat) κ tid E L F q :
    real E L ty f → ↑lftN ⊆ F → lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] (l, aπ) ∈ aπl, ty.(ty_shr) aπ d κ tid l)
      ={F}▷=∗ |={F}▷=>^d |={F}=>
        ⌜∃bm, (al_fmap f) ∘ alapply aπl = const bm⌝ ∗ llctx_interp L q ∗
        [∗ list] (l, aπ) ∈ aπl, ty.(ty_shr) aπ d κ tid l.
  Proof.
    iIntros ([_ Rl]?) "#LFT #E L tys". iInduction aπl as [|[??]] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. iFrame "L". iPureIntro. unfold compose. by exists []. }
    iDestruct "tys" as "[ty tys]". iDestruct "L" as "[L L₊]".
    iMod (Rl with "LFT E L ty") as "Upd"; [done|].
    iMod ("IH" with "L₊ tys") as "Upd'". iCombine "Upd Upd'" as "Upd". iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iIntros "[>(%Eq &$&$) >(%Eq' &$&$)] !%".
    move: Eq=> [b Eq]. move: Eq'=> [bm Eq']. exists ((l,b) :: bm).
    fun_ext=>/= π. by move: (equal_f Eq π) (equal_f Eq' π)=>/= <-<-.
  Qed.

  Global Instance token_type_contractive 𝔄 : TypeContractive (ghostptrtoken_ty (𝔄:=𝔄)).
  Proof.
    rewrite /ghostptrtoken_ty /big_sepAL.
    split; [done|split| |]; simpl.
    - by apply type_lft_morphism_id_like.
    - intros. do 6 f_equiv. intros ?. by eapply Forall2_impl.
    - intros ???(?&?&->&->&?). eexists _, _. split. exact H. 
      intros. eexists _, _. done.  
    - move=>/= > ->*. do 14 (f_contractive || f_equiv). by simpl in *.
    - intros ??????????????. unfold ty_shr. unfold ghostptrtoken_ty. do 10 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Global Instance token_send {𝔄} (ty: type 𝔄) : Send ty → Send (ghostptrtoken_ty ty).
  Proof. rewrite /ghostptrtoken_ty /big_sepAL. move=> ?>/=. by do 14 (f_equiv || move=>?). Qed.

  Global Instance token_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (ghostptrtoken_ty ty).
  Proof. rewrite /ghostptrtoken_ty /big_sepAL. move=> ?>/=. by do 10 (f_equiv || move=>?). Qed.

  Lemma token_resolve {𝔄} (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (ghostptrtoken_ty ty) ((lforall Φ) ∘ (fmap snd)).
  Proof.
    iIntros (????[|]???) "#LFT #PROPH #E L token //=".
    unfold big_sepAL.
    iDestruct "token" as (?[->->]) "[↦tys _]". iIntros "!>!>!>".
    rewrite trans_big_sepAL_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
    iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd").
    rewrite vec_to_list_map. rewrite vec_to_list_to_vec.
    unfold lapply. setoid_rewrite <- list_fmap_compose. setoid_rewrite lforall_Forall.
    setoid_rewrite Forall_fmap. by iIntros "!> H".
  Qed.

  Lemma token_resolve_just {𝔄} (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (ghostptrtoken_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma token_real {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ (locₛ*_) ) E L (ghostptrtoken_ty ty) (al_fmap f).
  Proof.
    move=> Rl. split; iIntros (???[|]) "*% LFT E L token //="; unfold big_sepAL.
    - iDestruct "token" as (?[->->]) "[↦tys †]". iIntros "!>!>!>".
      rewrite trans_big_sepAL_mt_ty_own. iDestruct "↦tys" as (?) "[↦ tys]".
      iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>".
      iSplit; last first.
      { iExists _. iFrame "†". iSplit; [done|]. iNext.
        rewrite trans_big_sepAL_mt_ty_own. iExists _. iFrame. }
      iPureIntro. move: Eq=> [bl Eq]. exists (zip aπl.*1 (vec_to_list bl)). fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.
      rewrite 3! vec_to_list_map  vec_to_list_to_vec.
      rewrite -list_fmap_compose zip_to_prod_map /alapply -list_fmap_compose.
      reflexivity.
    - iDestruct "token" as (?) "[%Bor tys]". iIntros "!>!>!>".
      iMod (real_big_sepM_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">(%Eq &$& tys) !>". iSplit; [|iExists _; by iFrame].
      iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.  by rewrite Bor.
  Qed.

  Lemma token_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (ghostptrtoken_ty ty) (ghostptrtoken_ty ty') (al_fmap f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "((%EqSz&%Proph) &?&#Own&#Shr)".
    have Eq: ∀(aπl: list (loc*(proph 𝔄))), al_fmap f ∘ alapply aπl = alapply (al_fmap (f ∘.) aπl).
    { move=> ?. fun_ext=>/= ?. f_equal. unfold alapply. rewrite -2! list_fmap_compose. reflexivity. }
    iSplit. iPureIntro. split; [done|]. intros ??(?&?&->&->&?).
    rewrite Eq. eexists _, _. do 2 (split; [done|]). rewrite 2! Forall2_fmap_l. rewrite Forall2_fmap_l in H.
    eapply Forall2_impl. done. simpl. intros. by apply Proph.
    iSplit; [done|]. iSplit; iIntros "!>" (?[|]) "* token //="; unfold big_sepAL.
    - iDestruct "token" as (?[->->]) "(↦tys & †)". iExists  _.
      iSplit; [done|]. rewrite 2! big_opL_fmap EqSz. simpl.
      iSplitR "†"; [iNext|]; iApply (big_sepL_impl with "[$]");
      iModIntro; iIntros (?[??]?). simpl. iIntros "(%vl&↦&tys)".
      iExists _. iFrame. iApply "Own". done. simpl. iIntros. done.
    - iDestruct "token" as (?->) "↦". iExists _. rewrite Eq.
      iSplit; [done|].
      rewrite big_opL_fmap. iApply (big_sepL_impl with "↦").
      do 2 iModIntro. iIntros (???) "↦". destruct x. simpl. iApply ("Shr" with "↦").
  Qed.
  Lemma token_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (ghostptrtoken_ty ty) (ghostptrtoken_ty ty') (al_fmap f) (al_fmap g).
  Proof. move=> [??]. split; by apply token_subtype. Qed.

  (* Rust's GhostPtrToken::new *)
  Definition ghostptrtoken_new: val :=
    fn: [] :=
      let: "r" := new [ #0] in
      let: "dummy" := new [ #0] in
      return: ["r"].

  Lemma ghostptrtoken_new_type {𝔄} (ty: type 𝔄) :
    typed_val ghostptrtoken_new (fn(∅) → ghostptrtoken_ty ty) (λ post _, post []).
  Proof.
    eapply type_fn; [apply _|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs". iMod persistent_time_receipt_0 as "⧖".
    wp_bind (new _). iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l) "[† _] ⧖". wp_seq.
    wp_bind (new _). iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l') "[†' _] ⧖".
    do 3 wp_seq.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const []] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full split_mt_token'. 
    iFrame "†". iNext. iExists []. iSplit.
    iPureIntro. apply functional_extensionality. intros. unfold alapply. done.
    unfold big_sepAL.
    rewrite heap_mapsto_vec_nil 2! big_sepL_nil.
    iSplit; [done|done].
  Qed.
End ghostptrtoken_basic.

Global Hint Resolve token_resolve | 5 : lrust_typing.
Global Hint Resolve token_resolve_just token_subtype token_eqtype : lrust_typing.
