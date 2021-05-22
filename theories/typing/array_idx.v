From lrust.typing Require Export type.
From lrust.typing Require Import programs
  array int own shr_bor uniq_bor product product_split.
Set Default Proof Using "Type".

Implicit Type 𝔄: syn_type.

Section lemmas.
  Context `{!typeG Σ}.

  (** * Owning Pointers *)

  Fixpoint hasty_own_idxs {𝔄} (p: path) (k: nat) (ty: type 𝔄) (n: nat)
    (i: nat) : tctx (replicate n 𝔄) :=
    match n with O => +[] | S m =>
      p +ₗ #(i * ty.(ty_size))%nat ◁ own_ptr k ty +::
      hasty_own_idxs p k ty m (S i) end.

  Lemma hasty_own_idxs_equiv {𝔄} p k (ty: _ 𝔄) n i :
    tctx_equiv (hasty_own_idxs (p +ₗ #ty.(ty_size)) k ty n i)
      (hasty_own_idxs p k ty n (S i)).
  Proof.
    apply get_tctx_equiv=> ? vπl. move: p i. induction n; [done|]=> p ?.
    case vπl=>/= ??. f_equiv; [|done].
    rewrite tctx_elt_interp_hasty_path; [done|]=>/=. case (eval_path p)=>//.
    (do 2 (case=>//))=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add.
  Qed.

  Lemma tctx_split_own_array {𝔄} k (ty: _ 𝔄) n p E L :
    tctx_incl E L +[p ◁ own_ptr k [ty;^ n]] (hasty_own_idxs p k ty n 0)
      (λ post '-[al], post (vec_to_plist al)).
  Proof.
    move: p. elim n. { move=> ?. eapply tctx_incl_eq;
    [by apply tctx_incl_leak_head|]=>/= ?[v[]]. by inv_vec v. } move=>/= ? IH ?.
    eapply tctx_incl_eq. { eapply tctx_incl_trans; [by eapply subtype_tctx_incl;
    eapply own_subtype, proj1, array_succ_prod|]. eapply tctx_incl_trans;
    [by eapply tctx_split_own_prod|]. apply (tctx_incl_app +[_] +[_]);
    [by apply tctx_to_shift_loc_0, _|]. eapply tctx_incl_trans; [by apply IH|].
    eapply proj1, hasty_own_idxs_equiv. } move=>/= ?[v[]]. by inv_vec v.
  Qed.

  Lemma tctx_extract_split_own_array {𝔄 𝔄' 𝔅l ℭl} (t: _ 𝔄) k (ty: _ 𝔄') n
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_elt E L t (hasty_own_idxs p k ty n 0) T' tr →
    tctx_extract_elt E L t (p ◁ own_ptr k [ty;^ n] +:: T) (T' h++ T) (λ post
      '(al -:: bl), tr (λ '(a -:: cl), post (a -:: cl -++ bl)) (vec_to_plist al)).
  Proof.
    move=> ?. eapply tctx_incl_eq. { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
    eapply tctx_incl_trans; by [apply tctx_split_own_array|]. }
    move=>/= ?[??]. rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

  Lemma tctx_merge_own_array {𝔄} k (ty: _ 𝔄) n p E L :
    tctx_incl E L (hasty_own_idxs p k ty (S n) 0) +[p ◁ own_ptr k [ty;^ S n]]
      (λ post al, post -[plist_to_vec al]).
  Proof.
    move: p. elim: n. { move=> ?. eapply tctx_incl_eq. { eapply tctx_incl_trans;
    [by apply tctx_of_shift_loc_0|]. eapply subtype_tctx_incl, own_subtype, proj2,
    array_one. } by move=> ?[?[]]. } move=>/= ? IH ?. eapply tctx_incl_eq. {
    eapply tctx_incl_trans; [|by eapply subtype_tctx_incl, own_subtype, proj2,
    array_succ_prod]. eapply tctx_incl_trans; [|by eapply tctx_merge_own_prod].
    apply (tctx_incl_app +[_] +[_]); [by apply tctx_of_shift_loc_0|].
    eapply tctx_incl_trans; [|by apply IH]. apply (tctx_incl_app +[_] +[_]);
    [|by eapply proj2, hasty_own_idxs_equiv]. rewrite Nat2Z.inj_add.
    eapply proj2, tctx_shift_loc_assoc. } by move=>/= ?[?[??]].
  Qed.

  Lemma tctx_extract_merge_own_array {𝔄 𝔅l ℭl} k (ty: _ 𝔄) n
    (T: _ 𝔅l) (T': _ ℭl) tr p E L :
    tctx_extract_ctx E L (hasty_own_idxs p k ty (S n) 0) T T' tr →
    tctx_extract_elt E L (p ◁ own_ptr k [ty;^ S n]) T T' (λ post, tr
      (λ acl, let '(al, cl) := psep acl in post (plist_to_vec al -:: cl))).
  Proof.
    move=> ?. eapply tctx_incl_eq. { eapply tctx_incl_trans; [done|].
    apply (tctx_incl_frame_r _ +[_]), tctx_merge_own_array. } done.
  Qed.

  (** * Shared References *)

  Lemma tctx_idx_shr_array {𝔄 𝔅l} (ty: _ 𝔄) n κ p (i: fin n) (T: _ 𝔅l) E L :
    tctx_incl E L (p ◁ &shr{κ} [ty;^ n] +:: T)
      (p +ₗ #(i * ty.(ty_size))%nat ◁ &shr{κ} ty +:: T)
      (λ post '(xl -:: bl), post (xl !!! i -:: bl))%type.
  Proof.
    iIntros (??[??]?) "_ _ _ _ $ [p T] Obs !>". iExists (_-::_).
    iFrame "Obs T". iDestruct "p" as ([[]|][|]Ev) "[⧖ ?]"=>//=. iExists _, _.
    iSplit; [by rewrite/= Ev|]. iFrame "⧖". by rewrite big_sepL_vlookup vfunsep_lookup.
  Qed.

  Lemma tctx_extract_idx_shr_array {𝔄 𝔅l} (ty: _ 𝔄) n κ p (i: fin n) (T: _ 𝔅l) E L :
    tctx_extract_elt E L (p +ₗ #(i * ty.(ty_size))%nat ◁ &shr{κ} ty)
      (p ◁ &shr{κ} [ty;^ n] +:: T) (p ◁ &shr{κ} [ty;^ n] +:: T)
      (λ post '(xl -:: bl), post (xl !!! i -:: xl -:: bl))%type.
  Proof.
    by eapply tctx_incl_eq; [eapply tctx_incl_trans;
    [apply copy_tctx_incl, _|apply tctx_idx_shr_array]|].
  Qed.

  Lemma type_idx_shr_array_instr {𝔄} (ty: _ 𝔄) n κ p q E L :
    typed_instr_ty E L +[p ◁ &shr{κ} [ty;^ n]; q ◁ int]
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
    tctx_extract_ctx E L +[p ◁ &shr{κ} [ty;^ n]; q ◁ int] T T' trx →
    (∀v: val, typed_body E L C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L C T (let: x := p +ₗ q * #ty.(ty_size) in e) (trx ∘
      (λ post '(xl -:: z -:: bl), ∃i: fin n, z = i ∧ tr post (xl !!! i -:: bl)))%type.
  Proof.
    iIntros. iApply type_let; [by apply type_idx_shr_array_instr|solve_typing| |done].
    f_equal. fun_ext=> ?. fun_ext. by case=> [?[??]].
  Qed.

  (** * Unique References *)

  Fixpoint hasty_uniq_idxs {𝔄} (p: path) (κ: lft) (ty: type 𝔄) (n: nat)
    (i: nat) : tctx (replicate n (𝔄 * 𝔄)%ST) :=
    match n with O => +[] | S m =>
      p +ₗ #(i * ty.(ty_size))%nat ◁ &uniq{κ} ty +::
      hasty_uniq_idxs p κ ty m (S i) end.

  Lemma tctx_split_uniq_array {𝔄} (ty: _ 𝔄) n κ p E L :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} [ty;^ n]] (hasty_uniq_idxs p κ ty n 0)
      (λ post '-[(al, al')], post (vec_to_plist (vzip al al'))).
  Proof.
    move=> ?. move: p. elim: n. { move=> ?. eapply tctx_incl_eq;
    [by apply tctx_incl_leak_head|]=>/= ?[[v v'][]]. inv_vec v. by inv_vec v'. }
    move=>/= n IH p. eapply tctx_incl_eq. { eapply tctx_incl_trans;
    [eapply tctx_uniq_eqtype; by [apply array_succ_prod|apply _|]|].
    eapply tctx_incl_trans; [by eapply (tctx_incl_frame_r +[_]),
    tctx_split_uniq_prod|]. apply (tctx_incl_app +[_] +[_]);
    [by apply tctx_to_shift_loc_0, _|]. eapply tctx_incl_trans; [apply IH|].
    eapply proj1, get_tctx_equiv=> ? vπl. move: p 0%nat. clear.
    induction n; [done|]=> p ?. case vπl=>/= ??. f_equiv; [|done].
    rewrite tctx_elt_interp_hasty_path; [done|]=>/=. case (eval_path p)=>//.
    (do 2 (case=>//))=> ?. by rewrite shift_loc_assoc -Nat2Z.inj_add. }
    move=> ?[[v v'][]]. inv_vec v. by inv_vec v'.
  Qed.

  Lemma tctx_extract_split_uniq_array {𝔄 𝔅 ℭl 𝔇l} (t: _ 𝔄) κ (ty: _ 𝔅) n
    (T: _ ℭl) (T': _ 𝔇l) tr p E L :
    lctx_lft_alive E L κ →
    tctx_extract_elt E L t (hasty_uniq_idxs p κ ty n 0) T' tr →
    tctx_extract_elt E L t (p ◁ &uniq{κ} [ty;^ n] +:: T) (T' h++ T)
      (λ post '((bl, bl') -:: cl),
        tr (λ '(a -:: dl), post (a -:: dl -++ cl)) (vec_to_plist (vzip bl bl'))).
  Proof.
    move=> ??. eapply tctx_incl_eq. { eapply (tctx_incl_frame_r +[_] (_ +:: _)).
    eapply tctx_incl_trans; by [apply tctx_split_uniq_array|]. }
    move=>/= ?[[??]?]. rewrite /trans_upper /=. f_equal. fun_ext. by case.
  Qed.

End lemmas.

Global Hint Resolve tctx_extract_split_own_array
  tctx_extract_idx_shr_array tctx_extract_split_uniq_array | 5 : lrust_typing.
Global Hint Resolve tctx_extract_merge_own_array | 40 : lrust_typing_merge.
