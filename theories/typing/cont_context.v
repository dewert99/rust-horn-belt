From iris.proofmode Require Import tactics.
From lrust.util Require Import types.
From lrust.lang Require Import notation.
From lrust.typing Require Export lft_contexts type type_context.

Set Default Proof Using "Type".

Notation valpl := (plist (const val)).

Fixpoint valpl_to_exprs {As} (vl: valpl As) : list expr :=
  match As, vl with ^[], _ => [] |
    _ ^:: _, v -:: vl' => (v: expr) :: valpl_to_exprs vl' end.

Section cont_context.
  Context `{!typeG Σ}.

  Definition cont_postcondition: iProp Σ := True%I.

  Record cctx_elt := CCtxe {
    cctxe_k: val;  cctxe_L: llctx;  cctxe_As: Types;
    cctxe_T: valpl cctxe_As → tctx cctxe_As;  cctxe_pre: predl cctxe_As;
  }.

  Definition cctx_elt_interp (tid: thread_id) (c: cctx_elt) : iProp Σ :=
    □ let '(CCtxe k L _ T pre) := c in ∀vl vπl,
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ tctx_interp tid (T vl) vπl -∗
        ⟨π, pre (vπl -$ π)⟩ -∗ WP k (valpl_to_exprs vl) {{ _, cont_postcondition }}.

End cont_context.
Add Printing Constructor cctx_elt.

Notation cctx := (tlist cctx_elt).

Notation "k ◁cont{ L , T } pre" := (CCtxe k L _ T pre)
  (at level 55, format "k  ◁cont{ L ,  T }  pre").

Notation cctx_interp tid := (big_sepTL (cctx_elt_interp tid)).

Section cont_context.
  Context `{!typeG Σ}.

  Lemma cctx_interp_forall tid C :
    cctx_interp tid C ⊣⊢ ∀ c, ⌜c ∈ C⌝ → cctx_elt_interp tid c.
  Proof. by rewrite big_sepTL_forall. Qed.

  Global Instance cctx_interp_permut tid :
    Proper ((≡ₜₑ) ==> (⊣⊢)) (cctx_interp tid).
  Proof. move=> *. rewrite !big_sepTL_forall. by do 4 f_equiv. Qed.

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
    iIntros (Sub ?) "_ _ _ _ C". rewrite !cctx_interp_forall.
    iIntros (? In). move/Sub in In. by iApply "C".
  Qed.

  Lemma cctx_incl_nil E C : cctx_incl E C ^[].
  Proof. by iIntros. Qed.

  Lemma cctx_incl_cons {As} E k L (T T': valpl As → tctx As) tr C C' pre :
    cctx_incl E C C' → (∀vl, tctx_incl E L (T' vl) (T vl) tr) →
    cctx_incl E (k ◁cont{L, T} pre ^:: C) (k ◁cont{L, T'} (tr pre) ^:: C').
  Proof.
    iIntros (InC InT ?) "#LFT #PROPH #UNIQ #E /=#[c C]".
    iSplit; [|by iApply InC]. iIntros "!>" (??) "Na L T' Obs".
    iMod (InT with "LFT PROPH UNIQ E L T' Obs") as (?) "(L & Obs & T)".
    iApply ("c" with "Na L T Obs").
  Qed.

End cont_context.

Global Hint Resolve cctx_incl_nil cctx_incl_cons : lrust_typing.
