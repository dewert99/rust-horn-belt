From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Section rules.
  Context `{!typeG Σ}.

  Lemma ty_assgn_box {𝔄 𝔄'} E L p (τ : type 𝔄) p' (τ' : type 𝔄'):
    τ.(ty_size) = τ'.(ty_size) →
    typed_instr E L +[p ◁ box τ; p' ◁ τ'] (p <- p') (λ _, +[p ◁ box τ'])
      (λ post '-[a; b], post -[b]).
  Proof.
    intros Eq ?.
    eapply (type_assign_instr _ τ _ _ _ _ (λ _ p, p)).
    rewrite /box Eq. solve_typing.
    eapply resolve'_just, resolve_just.
  Qed.

  Lemma ty_assgn_bor_mut {𝔄} E L κ (τ : type 𝔄) p p' :
    lctx_lft_alive E L κ →
    typed_instr E L +[p ◁ &uniq{κ} τ; p' ◁ τ] (p <- p') (λ _, +[p ◁ &uniq{κ} τ])
      (λ post '-[a; b], post -[(b, a.2)] ).
  Proof.
    intros ?.
    eapply (type_assign_instr (&uniq{κ} τ) τ (&uniq{κ} τ) τ fst (λ v w, (w, v.2)) (λ _ p, p)).
    solve_typing. eapply resolve'_just, resolve_just.
  Qed.

  Lemma ty_deref_bor_mut_copy {𝔄} E L κ (τ : type 𝔄) p :
    lctx_lft_alive E L κ → Copy τ → τ.(ty_size) = 1%nat →
    typed_instr E L +[p ◁ &uniq{κ} τ] (!p) (λ x, +[x ◁ τ; p ◁ &uniq{κ} τ])
      (λ post '-[a], post -[a.1; a] ).
  Proof.
    intros ???.
    eapply type_deref_instr; [solve_typing| solve_typing].
  Qed.

  Notation "drop: x" := (Skip)%E (at level 102, x at level 1) : expr_scope.

  Lemma ty_resolve {𝔄} E L (τ : type 𝔄) κ p :
  lctx_lft_alive E L κ →
    typed_instr E L +[p ◁ &uniq{κ} τ] (drop: p) (λ _, +[])
      (λ post '-[a], a.2 = a.1 → post -[]).
  Proof. intros ?. eapply type_resolve_instr.
    eapply resolve_impl. solve_typing.
    move => [? ?] //=.
  Qed.

  Notation "let: x := &mut{ κ } p 'in' e" := (let: x := p in e)%E
  (at level 102, x at level 1, e at level 150) : expr_scope.

  Lemma ty_borrow {𝔄 𝔄l ℭ} E L (C : cctx ℭ) (T : tctx 𝔄l) (τ : type 𝔄) p x e κ tr:
    Closed (x :b: []) e → elctx_sat E L (ty_outlives_E τ κ) →
    (∀v: val, typed_body E L C (v ◁ &uniq{κ} τ +:: p ◁{κ} box τ +:: T) (subst' x v e) tr) -∗
    typed_body E L C (p ◁ box τ +:: T) (let: x := &mut{κ} p in e)
      (λ post '(a -:: t), (∀ a', tr post ((a, a') -:: a' -:: t)) : Prop).
  Proof.
    iIntros (??) "H". via_tr_impl.
    iApply typed_body_tctx_incl.
    eapply (tctx_incl_app +[_] +[_; _] T T _ id), tctx_incl_refl.
    eapply tctx_borrow; [done].
    iApply (type_let' +[_]); [eapply type_path_instr| done].
    rewrite /trans_app => ? [? ?] //=.
  Qed.