From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.ghostptrtoken Require Import ghostseq_basic permdata_basic heap_util.
From lrust.typing.lib.ghostptrtoken Require Export ghostptrtoken.
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
  Definition ghostptrtoken_new: val := ghostseq_new.

  Lemma ghostptrtoken_new_type {𝔄} (ty: type 𝔄) :
    typed_val ghostptrtoken_new (fn(∅) → ghostptrtoken_ty ty) (λ post '-[], post []).
  Proof. exact (ghostseq_new_type _). Qed.

  Lemma uniq_ghostptrtoken_resolve {𝔄} E L κ (ty: type 𝔄) :
    (ty_size ty > 0)%Z → lctx_lft_alive E L κ → resolve E L (&uniq{κ} (ghostptrtoken_ty ty)) (λ '(a, a'), a' = a ∧ NoDup a.*1).
  Proof.
    intros. apply (uniq_seq_resolve (λ (a: (locₛ * 𝔄)%ST), fst a)); [|done].
    iIntros (???????) "(%&%&(_&->)&ty1)(%&%&(_&->)&ty2)".
    destruct d; try done. destruct d'; try done. 
    iDestruct "ty1" as "(↦1&†1)". iDestruct "ty2" as "(↦2&†2)".
    iAssert (▷⌜l ≠ l0⌝)%I as "#neq". iNext. iIntros (->). iApply (no_duplicate_heap_mapsto_own with "↦1 ↦2"). done.
    iSplitR. simpl. iIntros "!>!>!>". iApply step_fupdN_full_intro. iDestruct "neq" as "%". by iApply proph_obs_true.
    iSplitL "↦1 †1"; iExists _, _; iFrame; done.
  Qed.
End ghostptrtoken_basic.

Section defs2.
Context `{!typeG Σ}.

Lemma ghost_ptr_token_no_dup {𝔄} (ty: type 𝔄) aπl d tid:
    ([∗ list](l0, aπ)∈ aπl, [S(d') := d] ▷ (∃ vl : list val, l0 ↦∗ vl ∗ ty_own ty aπ d' tid vl)) -∗ ▷⌜(ty.(ty_size) > 0) → NoDup aπl.*1⌝.
Proof.
    iInduction aπl as [|[??]] "IH". rewrite NoDup_nil. iIntros. done.
    simpl. iIntros "(↦1&↦l)". rewrite NoDup_cons.
    destruct d; [done|]. iIntros "%". iSplit.
    iIntros (?). rewrite elem_of_list_fmap in H; destruct H as ([??]&->&H); simpl.
    iDestruct (big_sepL_elem_of _ _ _ H with "↦l") as "↦2". iNext.
    iApply (no_duplicate_heap_mapsto_own with "↦1 ↦2"). lia.
    iDestruct ("IH" with "↦l") as ">%". apply H in a. done. 
Qed.

Lemma ghost_ptr_token_no_dup' {𝔄} (ty: type 𝔄) aπl d tid:
  (ty.(ty_size) > 0) → ([∗ list](l0, aπ)∈ aπl, [S(d') := d] ▷ (∃ vl : list val, l0 ↦∗ vl ∗ ty_own ty aπ d' tid vl)) -∗ ▷⌜NoDup aπl.*1⌝.
Proof.
    iIntros. iDestruct (ghost_ptr_token_no_dup with "[$]") as ">%X".
    specialize (X H). done.
Qed.

End defs2.

Global Hint Resolve token_resolve | 5 : lrust_typing.
Global Hint Resolve token_resolve_just token_subtype token_eqtype : lrust_typing.
