From lrust.typing Require Export type always_true.
From lrust.typing Require Import uniq_util typing ptr logic_fn.
From lrust.typing.lib.ghostptrtoken Require Import ghostptrtoken_basic ghostseq_basic permdata_basic.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Lemma filter_sublist {A} P `{!∀ x : A, Decision (P x)} (l: list A) :
  filter P l `sublist_of` l.
Proof.
  induction l as [|x l IHl]; [done|]. rewrite filter_cons.
  destruct (decide (P x));
    [by apply sublist_skip|by apply sublist_cons].
Qed.

Lemma list_filter_fmap {A B} P `{!∀ x : A, Decision (P x)} (l: list B) (f: B → A): 
  filter P (f <$> l) = f <$> (filter (P∘f) l).
Proof.
  induction l as [|x l IHl]; [done|]. rewrite fmap_cons 2! filter_cons. simpl.
  destruct (decide (P (f x))); rewrite IHl; done.
Qed.

Lemma delete_list_to_map `{FinMap K M} {A} (k: K) (l: list (K * A)) : 
  (base.delete k (list_to_map (M:=M A) l)) = (list_to_map (filter (λ '(k', _), k ≠ k') l)).
Proof.
  induction l as [|[k' x] l IHl]; simpl. apply delete_empty. rewrite filter_cons. destruct (decide (k ≠ k')).
  simpl. rewrite -IHl delete_insert_ne; done.  destruct (decide (k = k')) as [->|?].
  rewrite -IHl delete_insert_delete; done. done.
Qed.

Lemma double_neg P `{Decision P} : ¬¬P ↔ P.
Proof. destruct (decide P); tauto. Qed.

Lemma iff_by_neg P Q `{Decision P} `{Decision Q} : (¬P ↔ ¬Q) → (P ↔ Q).
Proof. intros. rewrite -(double_neg P) -(double_neg Q). f_equiv. done. Qed. 


Section ghostptrtoken_shrink_shr.
  Context `{!typeG Σ}.

  Lemma ghostptrtoken_shrink_shr {𝔄} (ty: type 𝔄) κ p p2 E L :
  tctx_incl E L +[p ◁ (box (&shr{κ} (ghostptrtoken_ty ty))); p2 ◁ (box (ghost (ghostptrtoken_ty ty)))] +[p ◁ (box (&shr{κ} (ghostptrtoken_ty ty)))] 
    (λ post '-[l; g], (list_to_gmap g) ⊆ (list_to_gmap l) ∧ ∀ r, (list_to_gmap g) = (list_to_gmap r) → post -[r]).
  Proof. split. intros ?? H [?[?[]]]. setoid_rewrite H. done.
    iIntros (??(lπ&gπ&[])?) "_ PROPH _ _ $ ((%&%&%&⧖&shr)&ghost&true) #Obs". rewrite tctx_elt_interp_zst''.
    iDestruct "ghost" as (???) "(_&_&>(%&%&%&->&->&%))". iDestruct "shr" as (?->?[=->]) "((%&?&%&>->&%&>->&%&>->&shr)&?)".
    assert (exists (gaπm: (list (loc * (proph 𝔄)))), (lapply aπl) = (alapply gaπm)) as (gaπm&->).
    revert ξll H1. induction aπl; intros; simpl. exists []. done. 
    inversion_clear H1. destruct H2 as (?&?&->&?). destruct (IHaπl _ H3) as (?&?).
    eexists ((_, _)::_). fun_ext=>π. simpl. rewrite H2. done.
    iAssert (▷∃ (aπm: (list (loc * (proph 𝔄)))), ⌜lapply aπl0 = alapply aπm⌝ ∗ [∗ list] (l, aπ) ∈ aπm, ty_shr (permdata_ty ty) (λ π, (l, aπ π)) d κ tid l0)%I with "[shr]" as "(%&>->&shr)".
    iClear "#". iNext. iInduction aπl0 as [|] "IH"; simpl. iExists []. iSplitL. done. done.
    iDestruct "shr" as "[(%&%&->&?) shr]". iDestruct ("IH" with "shr") as "(%&%&?)".
    iExists ((_, _)::_). iSplit. iPureIntro. fun_ext=>π. simpl. rewrite H2. done. iFrame. iExists _, _. iFrame. done.
    set aπm' := (filter (λ '(l, _), l ∈ gaπm.*1) aπm).
    iModIntro. iExists (-[alapply aπm']). iFrame. iSplit. rewrite tctx_hasty_val'; [|done]. iExists _. iFrame. iFrame. iNext.
    iExists _. iFrame. iExists (_<$>aπm').
    iSplit. iPureIntro. fun_ext=>π. rewrite /lapply /alapply -list_fmap_compose. done.
    rewrite big_sepL_fmap. iApply big_sepL_submseteq. apply sublist_submseteq. apply filter_sublist. 
    iFexact "shr". f_equiv. intros ?[??]. done. simpl. iApply (proph_obs_impl with "Obs")=>π [subset Impl]. apply Impl.
    clear Impl. rewrite /aπm' (list_filter_iff _ (λ '(l, _), is_Some (list_to_gmap (alapply gaπm π) !! l)) aπm); last first.
    intros [??]. apply *iff_by_neg. rewrite -eq_None_not_Some -not_elem_of_list_to_map -list_fmap_compose. done.
    remember (list_to_gmap (alapply gaπm π)) as gm. rewrite -Heqgm. rewrite -Heqgm in subset. clear Heqgm.
    revert gm subset. clear aπm' gaπm. induction aπm as [|[??]?]; simpl; intros; remember subset as subset2; clear Heqsubset2; rewrite map_subseteq_spec in subset.
    apply map_empty. intros. remember (gm !! i) as op; symmetry in Heqop. destruct op. specialize (subset _ _ Heqop). done. done.
    rewrite filter_cons. destruct (decide (is_Some (gm !! l2))). destruct i as [??]. specialize (subset _ _ H2). rewrite lookup_insert in subset. injection subset as <-.
    simpl. rewrite -insert_delete_insert delete_list_to_map list_filter_fmap list_filter_filter. erewrite (list_filter_iff _ (λ '(l, _), is_Some ((base.delete l2 gm) !! l))).
    rewrite -IHaπm. rewrite insert_delete_insert insert_id; done. etransitivity. apply delete_mono. exact subset2. rewrite delete_insert_delete. apply delete_subseteq.
    intros [??]. simpl. destruct (decide (l2 = l3)) as [->|]. rewrite lookup_delete. intuition. eapply is_Some_None. done.
    rewrite lookup_delete_ne. intuition. done.
    rewrite -IHaπm. done. etransitivity. eapply (insert_delete_subseteq _ _ _ (o π)). rewrite eq_None_not_Some. done. apply insert_mono. done. rewrite 2! delete_insert_delete. apply delete_subseteq.
  Qed.

  Definition ghostptrtoken_shrink_shr_fn {𝔄} (ty: type 𝔄) : val :=
    fn: ["s"; "g"] :=
      return: ["s"].

  (* Rust's GhostPtrToken::borrow_mut *)
  Lemma ghostptrtoken_shrink_shr_type {𝔄} (ty: type 𝔄):
    typed_val (ghostptrtoken_shrink_shr_fn ty) (fn<α>(∅; &shr{α} (ghostptrtoken_ty ty), (ghost (ghostptrtoken_ty ty))) → &shr{α} (ghostptrtoken_ty ty))
    (λ post '-[l; g], (list_to_gmap g) ⊆ (list_to_gmap l) ∧ ∀ r, (list_to_gmap g) = (list_to_gmap r) → post r).
  Proof.
    fold of_syn_type. eapply type_fn; [apply _|]=> ???[ol[pl[]]]. simpl_subst. via_tr_impl.
    iApply typed_body_tctx_incl. apply ghostptrtoken_shrink_shr.
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
    done.
  Qed.
End ghostptrtoken_shrink_shr.