From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing zst.
From lrust.typing.lib.ghostptrtoken Require Import ghostseq.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostseq_basic.
  Context `{!typeG Σ}.

  Lemma real_big_sepL'_ty_shr {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅)
    aπl (d: nat) κ tid l E L F q :
    real E L ty f → ↑lftN ⊆ F → lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] aπ ∈ aπl, ty.(ty_shr) aπ d κ tid l)
      ={F}▷=∗ |={F}▷=>^d |={F}=>
        ⌜∃bm, (fmap f) ∘ lapply aπl = const bm⌝ ∗ llctx_interp L q ∗
        [∗ list] aπ ∈ aπl, ty.(ty_shr) aπ d κ tid l.
  Proof.
    iIntros ([_ Rl]?) "#LFT #E L tys". iInduction aπl as [|?] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. iFrame "L". iPureIntro. unfold compose. by exists []. }
    iDestruct "tys" as "[ty tys]". iDestruct "L" as "[L L₊]".
    iMod (Rl with "LFT E L ty") as "Upd"; [done|].
    iMod ("IH" with "L₊ tys") as "Upd'". iCombine "Upd Upd'" as "Upd". iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iIntros "[>(%Eq &$&$) >(%Eq' &$&$)] !%".
    move: Eq=> [b Eq]. move: Eq'=> [bm Eq']. exists (b :: bm).
    fun_ext=>/= π. by move: (equal_f Eq π) (equal_f Eq' π)=>/= <-<-.
  Qed.

  Global Instance seq_type_ne 𝔄 : TypeNonExpansive (ghostseq_ty (𝔄:=𝔄)).
  Proof.
    split; [done|split| |]; simpl.
    - by apply type_lft_morphism_id_like.
    - intros. do 6 f_equiv. intros ?. by eapply Forall2_impl.
    - intros ???(?&?&->&->&?). eexists _, _. split. exact H. 
      intros. eexists _, _. done.  
    - intros **. by do 6 (f_contractive || f_equiv).
    - intros **. by do 6 (f_contractive || f_equiv).
  Qed.

  Global Instance seq_send {𝔄} (ty: type 𝔄) : Send ty → Send (ghostseq_ty ty).
  Proof.  move=> ?>/=. by do 6 (f_equiv || move=>?). Qed.

  Global Instance seq_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (ghostseq_ty ty).
  Proof. move=> ?>/=. by do 6 (f_equiv || move=>?). Qed.

  Lemma seq_resolve {𝔄} (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (ghostseq_ty ty) (lforall Φ).
  Proof.
    iIntros (????????) "#LFT #PROPH #E L token //=".
    iDestruct "token" as (?[->->]) "tys".
    rewrite trans_big_sepL'_mt_ty_own.
    iMod (resolve_big_sepL_ty_own with "LFT PROPH E L tys") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd").
    rewrite vec_to_list_to_vec. unfold lapply. setoid_rewrite lforall_Forall.
    setoid_rewrite Forall_fmap. by iIntros "!> H".
  Qed.

  Lemma seq_resolve_just {𝔄} (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (ghostseq_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma seq_real {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ _) E L (ghostseq_ty ty) (fmap f).
  Proof.
    move=> Rl. split; iIntros (????) "*% LFT E L token //=".
    - iDestruct "token" as (?[->->]) "tys".
      rewrite trans_big_sepL'_mt_ty_own.
      iMod (real_big_sepL_ty_own with "LFT E L tys") as "Upd"; [done..|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>".
      iSplit; last first.
      { iExists _. iSplit; [done|].
        rewrite trans_big_sepL'_mt_ty_own.  iFrame. }
      iPureIntro. move: Eq=> [bl Eq]. exists (vec_to_list bl). fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.
      rewrite 2! vec_to_list_map vec_to_list_to_vec -list_fmap_compose. reflexivity.
    - iDestruct "token" as (?) "[%Bor tys]".
      iMod (real_big_sepL'_ty_shr with "LFT E L tys") as "Upd"; [done..|].
      iIntros "!>!>". iApply (step_fupdN_wand with "Upd").
      iIntros ">(%Eq &$& tys) !>". iSplit; [|iExists _; by iFrame].
      iPureIntro. move: Eq=> [bl Eq]. exists bl. fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-.  by rewrite Bor.
  Qed.

  Lemma seq_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (ghostseq_ty ty) (ghostseq_ty ty') (fmap f).
  Proof.
    iIntros (Sub ?) "L". iDestruct (Sub with "L") as "#Sub". iIntros "!> E".
    iDestruct ("Sub" with "E") as "((%EqSz&%Proph) &?&#Own&#Shr)".
    have Eq: ∀(aπl: list (proph 𝔄)), fmap f ∘ lapply aπl = lapply (fmap (f ∘.) aπl).
    { move=> ?. fun_ext=>/= ?. rewrite /lapply -2!list_fmap_compose. reflexivity. }
    iSplit. iPureIntro. split; [done|]. intros ??(?&?&->&->&?).
    rewrite Eq. eexists _, _. do 2 (split; [done|]). rewrite Forall2_fmap_l.
    eapply Forall2_impl. done. simpl. intros. by apply Proph.
    iSplit; [done|]. iSplit; iIntros "!>" (??) "* token //=".
    - iDestruct "token" as (?[->->]) "tys". iExists  _.
      iSplit; [done|]. rewrite big_opL_fmap. simpl.
      iApply (big_sepL_impl with "[$]");
      iModIntro; iIntros (???). simpl. iApply "Own".
    - iDestruct "token" as (?->) "↦". iExists _. rewrite Eq.
      iSplit; [done|].
      rewrite big_opL_fmap. iApply (big_sepL_impl with "↦").
      iModIntro. iIntros (???). iApply "Shr".
  Qed.
  Lemma seq_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (ghostseq_ty ty) (ghostseq_ty ty') (fmap f) (fmap g).
  Proof. move=> [??]. split; by apply seq_subtype. Qed.

  Global Instance seq_zst {𝔄} (ty: type 𝔄) : ZST (ghostseq_ty ty).
  Proof. done. Qed.

  Lemma seq_append {𝔄} (ty: type 𝔄) E L :
  tctx_incl E L +[null_val ◁ (box (ghostseq_ty ty)); null_val ◁ (box (ghostseq_ty ty))] +[null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[s1; s2], post -[s1 ++ s2]).
  Proof. split. solve_proper.
    iIntros (??(s1π&s2π&[])?) "_ _ _ _ $ (ty1&ty2&true) Obs"; 
    iExists (-[λ π, _]); iFrame.
    rewrite 3! tctx_elt_interp_zst.
    iDestruct "ty1" as "(%&⧖&%&>(_&->)&ty1)".
    iDestruct "ty2" as "(%&⧖'&%&>(_&->)&ty2)".
    iCombine "⧖ ⧖'" as "⧖". simpl.
    iModIntro. iExists _. iFrame. iNext. iExists _.
    iSplit. iPureIntro. split; [done|]. fun_ext. intros. rewrite -fmap_app. done.
    rewrite big_sepL_app. iSplitL "ty1"; 
    (iApply (big_sepL_impl with "[-]"); [done|]); iIntros "!> **";
    (iApply ty_own_depth_mono; [|done]); lia.
  Qed.

  Lemma seq_new {𝔄} (ty: type 𝔄) E L :
  tctx_incl E L +[null_val ◁ (box ())] +[null_val ◁ (box (ghostseq_ty ty))]
    (λ post '-[_], post -[[]]).
  Proof. split. solve_proper.
    iIntros (??(?&[])?) "_ _ _ _ $ (⧖&true) Obs"; 
    iExists (-[λ π, _]); iFrame.
    rewrite tctx_elt_interp_zst tctx_hasty_val.
    iDestruct "⧖" as ([|?]) "(⧖&?)"; [done|].
    iModIntro. iExists _. iFrame. iNext. iExists []. iSplit; done.
  Qed.

  (* Lemma seq_split {𝔄 𝔄l} (ty: type 𝔄) `{!Copy ty} (T: tctx 𝔄l) E L :
  tctx_incl E L (null_val ◁ (box (ghostseq_ty ty)) +:: T) (null_val ◁ (box (ghostseq_ty ty)) +:: null_val ◁ (box (ghostseq_ty ty)) +:: T)
    (λ post '(s -:: al), ∃ s1 s2, s1 ++ s2 = s ∧ post (s1 -:: s2 -:: al)).
  Proof. split. solve_proper.
    iIntros (??(sπ&lπ)?) "_ PROPH _ _ $ (ty&?) Obs".
    rewrite tctx_elt_interp_zst.
    iDestruct "ty" as "(%&⧖&%&>(_&->)&ty1)".
    iMod (proph_obs_sat with "PROPH Obs") as "(%&%&%&%&%)"; [done|].
    iExists ((λ π, _) -:: lπ); iFrame. *)
    
    
    (* iDestruct "ty2" as "(%&⧖'&%&>(_&->)&ty2)".
    iCombine "⧖ ⧖'" as "⧖". simpl.
    iModIntro. iExists _. iFrame. iNext. iExists _.
    iSplit. iPureIntro. split; [done|]. fun_ext. intros. rewrite -fmap_app. done.
    rewrite big_sepL_app. iSplitL "ty1"; 
    (iApply (big_sepL_impl with "[-]"); [done|]); iIntros "!> **";
    (iApply ty_own_depth_mono; [|done]); lia.
  Qed. *)

  Lemma seq_one `{!Inhabited 𝔄} (ty: type 𝔄) `{!ZST ty} E L : eqtype E L (!{λ (l: listₛ 𝔄), length l = 1} (ghostseq_ty ty)) ty (λ (l: list 𝔄), l !!! 0) (λ x, [x]).
  Proof. 
    split; iIntros; iModIntro; iIntros "_".
    - iSplit. iPureIntro. split. rewrite zero_size. done.
      intros ??(([|?[|]]&?&->&->&?)&?&?); try done. 
      inversion_clear H. inversion_clear H2. simpl. rewrite right_id. done.
      iSplit. iApply lft_incl_refl.
      iSplit; iModIntro; iIntros (????); [|iIntros (?)]; iIntros "((_&%&%)&%&%&ty)"; [destruct H0 as [->->]| revert H0; intros ->];
      destruct aπl as [|?[|]]; try done; iDestruct "ty" as "(?&_)"; iFrame. 
    - iSplit. iPureIntro. split. rewrite zero_size. done.
      intros. simpl. split. exists [vπ], [ξl]. simpl. rewrite right_id. intuition. 
      exists inhabitant. done.
      iSplit. iApply lft_incl_refl.
      iSplit; iModIntro; iIntros; (iSplit; [by iApply proph_obs_s_true|]); iExists [vπ];
      [iDestruct (zst_size_eq with "[$]") as %->|]; simpl; (iSplit; [done|]); iSplit; done.
  Qed.

  (* Lemma seq_perm {𝔄}  g ty E L :
   (∀ x, f x ≡ₚ x) → subtype E L (ghostseq_ty ty) (ghostseq_ty ty) f.
  Proof. move=> [??]. split; by apply seq_subtype. Qed. *)

  (* Rust's GhostSeq::new *)
  Definition ghostseq_new: val :=
    fn: [] :=
      let: "r" := new [ #0] in
      return: ["r"].

  Lemma ghostseq_new_type {𝔄} (ty: type 𝔄) :
    typed_val ghostseq_new (fn(∅) → ghostseq_ty ty) (λ post _, post []).
  Proof.
    eapply type_fn; [apply _|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs". iMod persistent_time_receipt_0 as "⧖".
    wp_bind (new _). iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l) "[† _] ⧖". wp_seq.
    do 2 wp_seq.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const []] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full split_mt_seq. 
    iFrame "†". iNext. iExists []. iSplit.
    iPureIntro. done.
    rewrite heap_mapsto_vec_nil. iSplit; done.
  Qed.
End ghostseq_basic.

Global Hint Resolve seq_resolve | 5 : lrust_typing.
Global Hint Resolve seq_resolve_just seq_subtype seq_eqtype : lrust_typing.
