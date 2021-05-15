From lrust.typing Require Export type.
From lrust.typing Require Import programs array int shr_bor uniq_bor.
Set Default Proof Using "Type".

Implicit Type 𝔄: syn_type.

Section lemmas.
  Context `{!typeG Σ}.

  Lemma array_shr_idx_instr {𝔄} (ty: _ 𝔄) n κ p q E L :
    ⊢ typed_instr_ty E L +[p ◁ &shr{κ} [ty; n]; q ◁ int]
      (p +ₗ q * #ty.(ty_size))%E (&shr{κ} ty)
      (λ post '-[xl; z], ∃i: fin n, z = i ∧ post (xl !!! i))%type.
  Proof.
    iIntros (??(vπ&?&[])) "LFT _ PROPH _ _ $$ (p & q &_) #Obs".
    wp_apply (wp_hasty with "p"). iIntros ([[]|][|]) "_ ⧖ shrs //".
    wp_apply (wp_hasty with "q"). iIntros "%% _ _" ((?&->&[=->]))=>/=.
    iMod (proph_obs_sat with "PROPH Obs") as %(?& i &->&_); [done|].
    do 2 wp_op. iExists -[(.!!! i) ∘ vπ]. iSplit; last first.
    { iApply proph_obs_impl; [|done]=>/= ?[?[Eq +]].
      do 2 apply (inj _) in Eq. by rewrite Eq. }
    iSplit; [|done]. iExists _, _. do 2 (iSplit; [done|]).
    by rewrite/= -Nat2Z.inj_mul big_sepL_vlookup vfunsep_lookup.
  Qed.

  Lemma array_shr_idx {𝔄 𝔄l 𝔅l} (ty: _ 𝔄) n κ p q
    (T: _ 𝔄l) (T': _ 𝔅l) tr pre x e E L C :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} [ty; n]; q ◁ int] T T' tr →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := p +ₗ q * #ty.(ty_size) in e)
      (tr (λ '(xl -:: z -:: bl), ∃i: fin n, z = i ∧ pre (xl !!! i -:: bl)))%type.
  Proof.
    iIntros. iApply type_let; [iApply array_shr_idx_instr|solve_typing| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

End lemmas.
