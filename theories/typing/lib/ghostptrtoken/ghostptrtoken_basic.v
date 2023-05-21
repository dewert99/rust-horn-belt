From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken ghostseq_basic permdata_basic.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_basic.
  Context `{!typeG Σ}.

  (* Lemma real_big_sepM_ty_shr {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅)
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
  Qed. *)

  Global Instance token_type_contractive 𝔄 : TypeContractive (ghostptrtoken_ty (𝔄:=𝔄)).
  Proof. solve_typing. Qed.

  Global Instance token_send {𝔄} (ty: type 𝔄) : Send ty → Send (ghostptrtoken_ty ty).
  Proof. solve_typing. Qed.

  Global Instance token_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (ghostptrtoken_ty ty).
  Proof. solve_typing. Qed.

  Lemma token_resolve {𝔄} (ty: type 𝔄) Φ E L :
    resolve E L ty Φ → resolve E L (ghostptrtoken_ty ty) (lforall (Φ ∘ snd)).
  Proof. intros. by apply permdata_resolve, seq_resolve in H. Qed.

  Lemma token_resolve_just {𝔄} (ty: type 𝔄) E L :
    resolve E L ty (const True) → resolve E L (ghostptrtoken_ty ty) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma token_real {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) E L :
    real E L ty f → real (𝔅:=listₛ (locₛ*_) ) E L (ghostptrtoken_ty ty) (al_fmap f).
  Proof. intros. by apply permdata_real, seq_real in H. Qed.

  Lemma token_subtype {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty' E L :
    subtype E L ty ty' f → subtype E L (ghostptrtoken_ty ty) (ghostptrtoken_ty ty') (al_fmap f).
  Proof. 
    intros. apply permdata_subtype, seq_subtype in H. done.
  Qed.

  Lemma token_eqtype {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty ty' E L :
    eqtype E L ty ty' f g → eqtype E L (ghostptrtoken_ty ty) (ghostptrtoken_ty ty') (al_fmap f) (al_fmap g).
  Proof. move=> [??]. split; by apply token_subtype. Qed.

  (* Rust's GhostPtrToken::new *)
  Definition ghostptrtoken_new: val :=
    fn: [] :=
      let: "r" := new [ #0] in
      return: ["r"].

  Lemma ghostptrtoken_new_type {𝔄} (ty: type 𝔄) :
    typed_val ghostptrtoken_new (fn(∅) → ghostptrtoken_ty ty) (λ post _, post []).
  Proof. Opaque ghostptrtoken_ty.
    eapply type_fn; [apply _|]=> _ ???. simpl_subst.
    iIntros (???) "_ #TIME _ _ _ Na L C _ Obs". iMod persistent_time_receipt_0 as "⧖".
    wp_bind (new _). iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iApply wp_new; [done..|]. iIntros "!>" (l) "[† _] ⧖". wp_seq.
    do 2 wp_seq.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[const []] with "Na L [-Obs] Obs"). iSplit; [|done].
    iExists _, _. do 2 (iSplit; [done|]). rewrite/= freeable_sz_full split_mt_token. 
    iFrame "†". iNext. iExists []. iSplit. done.
    rewrite heap_mapsto_vec_nil 2! big_sepL_nil.
    iSplit; [done|done].
  Qed.
End ghostptrtoken_basic.

Global Hint Resolve token_resolve | 5 : lrust_typing.
Global Hint Resolve token_resolve_just token_subtype token_eqtype : lrust_typing.
