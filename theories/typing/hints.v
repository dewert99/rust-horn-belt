From lrust.typing Require Import type lft_contexts.

Section hints.
  Context `{!typeG Σ}.

  Lemma lctx_lft_alive_intersect_list αl E L:
    (∀ α, α ∈ αl → lctx_lft_alive E L α) →
    lctx_lft_alive E L (lft_intersect_list αl).
  Proof.
    rewrite -Forall_forall. intros H. induction αl; inversion_clear H. apply lctx_lft_alive_static.
    simpl. apply lctx_lft_alive_intersect. done. apply IHαl. done.
  Qed.

  Lemma elem_of_ty_outlives_E {𝔄} ϝ x (ty: type 𝔄) : x ∈ ty_lfts ty → ϝ ⊑ₑ x ∈ ty_outlives_E ty ϝ .
  Proof.
    intros. rewrite elem_of_list_fmap. eexists. done.
  Qed.

  Global Instance by_just_loc_into_exist (Φ: loc → iProp Σ) vl: IntoExist (by_just_loc vl Φ) (λ (l: loc), ⌜vl = [ #l]⌝ ∗ Φ l)%I (λ l, ()).
  Proof. unfold IntoExist. iIntros "?". destruct vl as [|[[| |]|][|]]; try done. iExists _. iFrame. done. Qed.

  Global Instance by_succ_into_exist (Φ: nat → iProp Σ) d: IntoExist (by_succ d Φ) (λ d', ⌜d = S d'⌝ ∗ Φ d')%I (λ d, ()).
  Proof. unfold IntoExist. iIntros "?". destruct d; try done. iExists _. iFrame. done. Qed.

  Lemma entails_entails (P Q: iProp Σ) : (P ⊢ Q) → (P ⊢ Q).
  Proof. done. Qed.

  Lemma exist_intro {T} (t: T) P: (impl (P t) (∃ t, P t)).
  Proof. intros. exists t. done. Qed.

  Lemma is_True_True {P: Prop} (_: P): P ↔ True.
  Proof. split; done. Qed.
End hints.

Tactic Notation "iFocusConclusion" tactic(tac) := iApply entails_entails; [tac; reflexivity|].
Tactic Notation "iRewrite'" open_constr(lem) := iFocusConclusion setoid_rewrite lem.
Tactic Notation "iRewrite'" "<-" open_constr(lem) := iFocusConclusion setoid_rewrite <- lem.
Tactic Notation "iExists'" uconstr(w) := iRewrite' <- (bi.exist_intro w).
Tactic Notation "iExistsP" uconstr(w) := iRewrite' <- (exist_intro w).
Ltac iFexact H := iApply (entails_entails with H). 

Global Hint Resolve lctx_lft_alive_intersect_list elem_of_ty_outlives_E: lrust_typing.