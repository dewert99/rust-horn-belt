From lrust.typing Require Export type.
From lrust.typing Require Import programs
  array int shr_bor uniq_bor product product_split.
Set Default Proof Using "Type".

Implicit Type 𝔄: syn_type.

Section lemmas.
  Context `{!typeG Σ}.

  Lemma tctx_idx_shr_array {𝔄 𝔅l} (ty: _ 𝔄) n κ p (i: fin n) (T: _ 𝔅l) E L :
    tctx_incl E L (p ◁ &shr{κ} [ty; n] +:: T)
      (p +ₗ #(i * ty.(ty_size))%nat ◁ &shr{κ} ty +:: T)
      (λ post '(xl -:: bl), post (xl !!! i -:: bl))%type.
  Proof.
    iIntros (??[??]?) "_ _ _ _ $ [p T] Obs !>". iExists (_ -:: _).
    iFrame "Obs T". iDestruct "p" as ([[]|][|]Ev) "[⧖ ?]"=>//=. iExists _, _.
    iSplit; [by rewrite/= Ev|]. iFrame "⧖". by rewrite big_sepL_vlookup vfunsep_lookup.
  Qed.

  Lemma tctx_extract_idx_shr_array {𝔄 𝔅l} (ty: _ 𝔄) n κ p (i: fin n) (T: _ 𝔅l) E L :
    tctx_extract_elt E L (p +ₗ #(i * ty.(ty_size))%nat ◁ &shr{κ} ty)
      (p ◁ &shr{κ} [ty; n] +:: T) (p ◁ &shr{κ} [ty; n] +:: T)
      (λ post '(xl -:: bl), post (xl !!! i -:: xl -:: bl))%type.
  Proof.
    by eapply tctx_incl_eq; [eapply tctx_incl_trans;
    [apply copy_tctx_incl, _|apply tctx_idx_shr_array]|].
  Qed.

  Lemma type_idx_shr_array_instr {𝔄} (ty: _ 𝔄) n κ p q E L :
    ⊢ typed_instr_ty E L +[p ◁ &shr{κ} [ty; n]; q ◁ int]
      (p +ₗ q * #ty.(ty_size))%E (&shr{κ} ty)
      (λ post '-[xl; z], ∃i: fin n, z = i ∧ post (xl !!! i))%type.
  Proof.
    iIntros (??(vπ&?&[])) "_ _ PROPH _ _ $$ (p & q &_) #Obs".
    wp_apply (wp_hasty with "p"). iIntros ([[]|][|]) "_ ⧖ ? //".
    wp_apply (wp_hasty with "q"). iIntros "%% _ _" ((?&->&[=->]))=>/=.
    iMod (proph_obs_sat with "PROPH Obs") as %(?& i &->&_); [done|].
    do 2 wp_op. iExists -[(.!!! i) ∘ vπ]. iSplit; last first.
    { iApply proph_obs_impl; [|done]=>/= ?[?[Eq +]].
      do 2 apply (inj _) in Eq. by rewrite Eq. }
    iSplit; [|done]. iExists _, _. do 2 (iSplit; [done|]).
    by rewrite/= -Nat2Z.inj_mul big_sepL_vlookup vfunsep_lookup.
  Qed.

  Lemma type_idx_shr_array {𝔄 𝔄l 𝔅l ℭ} (ty: _ 𝔄) n κ p q
    (T: _ 𝔄l) (T': _ 𝔅l) trx tr x e E L (C: cctx ℭ) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} [ty; n]; q ◁ int] T T' trx →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p +ₗ q * #ty.(ty_size) in e) (trx ∘
      (λ post '(xl -:: z -:: bl), ∃i: fin n, z = i ∧ tr post (xl !!! i -:: bl)))%type.
  Proof.
    iIntros. iApply type_let; [by apply type_idx_shr_array_instr|solve_typing| |done].
    f_equal. fun_ext=> ?. fun_ext. by case=> [?[??]].
  Qed.

  Fixpoint hasty_uniq_idxs {𝔄} (p: path) (κ: lft) (ty: type 𝔄) (n: nat)
    (i: nat) : tctx (replicate n (𝔄 * 𝔄)%ST) :=
    match n with 0 => +[] | S m =>
      p +ₗ #(i * ty.(ty_size))%nat ◁ &uniq{κ} ty +::
      hasty_uniq_idxs p κ ty m (S i) end.

  Lemma tctx_split_uniq_array {𝔄} (ty: _ 𝔄) n κ p E L :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} [ty; n]] (hasty_uniq_idxs p κ ty n 0)
      (λ post '-[(al, al')], post
        (vec_to_plist (vzip al al': vec (𝔄 * 𝔄)%ST _))).
  Proof.
    move=> ?. move: p. elim: n. { move=> ?. eapply tctx_incl_eq;
    [apply tctx_incl_leak_head|]=>/= ?[[v v'][]]. inv_vec v. by inv_vec v'. }
    move=>/= n IH p. eapply tctx_incl_eq. { eapply tctx_incl_trans;
    [eapply tctx_uniq_eqtype; by [apply array_succ_prod|apply _|]|].
    eapply tctx_incl_trans. { eapply (tctx_incl_frame_r +[_]).
    by eapply tctx_split_uniq_prod. } apply (tctx_incl_app +[_] +[_]);
    [apply tctx_to_shift_loc_0, _|]. eapply (tctx_incl_trans _ id); [apply IH|].
    iIntros (?? vπl ?) "_ _ _ _ $ T Obs !>". iExists _. iFrame "Obs". clear.
    move: 0=> k. iInduction n as [|] "IH" forall (p k); [done|]. case vπl=>/= ??.
    iDestruct "T" as "[p T]". iSplitL "p"; [|by iApply "IH"].
    rewrite tctx_elt_interp_hasty_path; [done|]=>/=. case (eval_path p)=>//.
    (do 2 (case=>//))=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add. }
    move=> ?[[v v'][]]. inv_vec v. by inv_vec v'.
  Qed.

  Lemma tctx_extract_split_uniq_array {𝔄 𝔅 ℭl 𝔇l} (t: _ 𝔄) κ (ty: _ 𝔅) n
    (T: _ ℭl) (T': _ 𝔇l) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t (hasty_uniq_idxs p κ ty n 0) T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} [ty; n] +:: T) (T' h++ T)
      (λ post '((bl, bl') -:: cl),
        tr (λ '(a -:: dl), post (a -:: dl -++ cl)) (vec_to_plist (vzip bl bl'))).
  Proof.
    move=> ??. eapply tctx_incl_eq. { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
    eapply tctx_incl_trans; by [apply tctx_split_uniq_array|]. }
    move=>/= ?[[??]?]. rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

End lemmas.

Global Hint Resolve tctx_extract_idx_shr_array tctx_extract_split_uniq_array
  | 5 : lrust_typing.
