From iris.proofmode Require Import tactics.
From lrust.lang Require Import notation.
From lrust.typing Require Import type lft_contexts type_context.
Set Default Proof Using "Type".

Section cont_context.
  Context `{!typeG Σ}.

  Definition cont_postcondition: iProp Σ := True%I.

  Record cctx_elt := CCtxe {
    cctxe_k: val;  cctxe_L: llctx;  cctxe_Al: syn_typel;  cctxe_n: nat;
    cctxe_T: vec val cctxe_n → tctx cctxe_Al;  cctxe_pre: predl cctxe_Al;
  }.

  Definition cctx_elt_interp (tid: thread_id) (c: cctx_elt) : iProp Σ :=
    let 'CCtxe k L _ _ T pre := c in ∀vl vπl,
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ tctx_interp tid (T vl) vπl -∗
        ⟨π, pre (vπl -$ π)⟩ -∗ WP k (map of_val vl) {{ _, cont_postcondition }}.

  Definition cctx_interp (tid: thread_id) (C: list cctx_elt) : iProp Σ :=
    ∀c, ⌜c ∈ C⌝ -∗ cctx_elt_interp tid c.

End cont_context.
Add Printing Constructor cctx_elt.

Notation cctx := (list cctx_elt).

Notation "k ◁cont{ L , T } pre" := (CCtxe k L _ _ T pre)
  (at level 55, format "k  ◁cont{ L ,  T }  pre").

Section cont_context.
  Context `{!typeG Σ}.

  Global Instance cctx_interp_permut tid :
    Proper ((≡ₚ) ==> (⊣⊢)) (cctx_interp tid).
  Proof. solve_proper. Qed.

  Lemma cctx_interp_cons tid c C :
    cctx_interp tid (c :: C) ⊣⊢ cctx_elt_interp tid c ∧ cctx_interp tid C.
  Proof.
    iSplit; iIntros "cC".
    - iSplit; [|iIntros (??)]; iApply "cC"; iPureIntro; by constructor.
    - iIntros (? In). move: In. rewrite elem_of_cons. case=> [->|?].
      + by iDestruct "cC" as "[? _]".
      + iDestruct "cC" as "[_ C]". by iApply "C".
  Qed.

  Lemma cctx_interp_nil tid : cctx_interp tid [] ⊣⊢ True.
  Proof. iSplit; [by iIntros|]. iIntros "_ % %In". inversion In. Qed.

  Lemma cctx_interp_app tid C C' :
    cctx_interp tid (C ++ C') ⊣⊢ cctx_interp tid C ∧ cctx_interp tid C'.
  Proof.
    elim C. { by rewrite/= cctx_interp_nil left_id. } move=>/= ?? IH.
    by rewrite !cctx_interp_cons IH assoc.
  Qed.

  Lemma cctx_interp_singleton tid c :
    cctx_interp tid [c] ⊣⊢ cctx_elt_interp tid c.
  Proof. by rewrite cctx_interp_cons cctx_interp_nil right_id. Qed.

  Definition cctx_incl (E: elctx) (C C': cctx) : Prop :=
    ∀tid, lft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ cctx_interp tid C -∗ cctx_interp tid C'.

  Global Instance cctx_incl_preorder E : PreOrder (cctx_incl E).
  Proof.
    split; [iIntros (??) "_ _ _ _ $"|].
    iIntros (??? In In' ?) "#LFT #PROPH #UNIQ #E ?".
    iApply (In' with "LFT PROPH UNIQ E"). by iApply (In with "LFT PROPH UNIQ E").
  Qed.

  Lemma incl_cctx_incl E C1 C2 : C1 ⊆ C2 → cctx_incl E C2 C1.
  Proof.
    iIntros (Sub ?) "_ _ _ _ C". iIntros (? In). move/Sub in In. by iApply "C".
  Qed.

  Lemma cctx_incl_nil E C : cctx_incl E C [].
  Proof. iIntros "% _ _ _ _ _ % %In". inversion In. Qed.

  Lemma cctx_incl_cons {𝔄l} k L n (T T': vec _ n → tctx 𝔄l) pre tr C C' E :
    cctx_incl E C C' → (∀vl, tctx_incl E L (T' vl) (T vl) tr) →
    cctx_incl E (k ◁cont{L, T} pre :: C) (k ◁cont{L, T'} (tr pre) :: C').
  Proof.
    iIntros (InC InT ?) "LFT PROPH UNIQ E kC". rewrite !cctx_interp_cons. iSplit.
    - iDestruct "kC" as "[k _]". iIntros (??) "Na L T' Obs".
      iMod (InT with "LFT PROPH UNIQ E L T' Obs") as (?) "(L & T & Obs)".
      iApply ("k" with "Na L T Obs").
    - iDestruct "kC" as "[_ ?]". by iApply (InC with "LFT PROPH UNIQ E").
  Qed.

End cont_context.

Global Hint Resolve cctx_incl_nil cctx_incl_cons : lrust_typing.
