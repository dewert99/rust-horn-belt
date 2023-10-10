From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Lemma join_app {A} (l1 l2: list (list A)): mjoin l1 ++ mjoin l2 = mjoin (l1 ++ l2).
Proof. induction l1; simpl. done. by rewrite -app_assoc IHl1. Qed. 

Notation "l +ₗ[ ty ] i" := (l%L +ₗ Z.of_nat (i%nat * ty.(ty_size))%nat)
  (format "l  +ₗ[ ty ]  i", at level 50, left associativity) : loc_scope.

Notation "l ↦∗len n" := (∃vl, ⌜length vl = n%nat⌝ ∗ l ↦∗ vl)%I
  (at level 20, format "l  ↦∗len  n") : bi_scope.

Global Instance Forall2_proper {A B} :
  Proper (pointwise_relation _ (pointwise_relation _ (↔)) ==> (=) ==> (=) ==> (↔)) (@Forall2 A B).
Proof. split; subst; induction 1; constructor; by firstorder auto. Qed.

Global Instance Forall2_mono {A B} :
Proper (pointwise_relation _ (pointwise_relation _ impl) ==> (=) ==> (=) ==> impl) (@Forall2 A B).
Proof. intros ?????->??->?. eapply Forall2_impl; done.  Qed.

Lemma fmap_lapply {A B} (f: A → B) (aπl: (list (proph A))) : fmap f ∘ lapply aπl = lapply (fmap (f ∘.) aπl).
Proof. fun_ext=>/= ?. rewrite /lapply -2!list_fmap_compose. reflexivity. Qed.

Lemma fmap_lapply_vmap {A B} (f: A → B) n (aπl: (vec (proph A) n)) : fmap f ∘ lapply aπl = lapply (vmap (f ∘.) aπl).
Proof. rewrite fmap_lapply vec_to_list_map. done. Qed.

Section array_util.
  Context `{!typeG Σ}.

  Lemma shift_loc_ty_assoc {𝔄} (ty: type 𝔄) l m n :
    l +ₗ[ty] (m + n) = l +ₗ[ty] m +ₗ[ty] n.
  Proof. by rewrite Nat.mul_add_distr_r shift_loc_assoc_nat. Qed.

  Lemma trans_big_sepL_mt_ty_own {𝔄} (ty: type 𝔄) n (aπl: vec _ n) l d tid :
    ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) ⊣⊢
    ∃wll: vec (list val) n, l ↦∗ concat wll ∗
      [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2.
  Proof.
    iSplit.
    - iIntros "↦owns". iInduction aπl as [|] "IH" forall (l)=>/=.
      { iExists [#]. by rewrite heap_mapsto_vec_nil /=. }
      iDestruct "↦owns" as "[(%& ↦ & ty) ↦owns]".
      rewrite shift_loc_0. setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct ("IH" with "↦owns") as (?) "(↦s & tys)". iExists (_:::_).
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "ty") as %->.
      iFrame.
    - iIntros "(%& ↦s & tys)". iInduction aπl as [|] "IH" forall (l); [done|].
      inv_vec wll=>/= ??. rewrite heap_mapsto_vec_app.
      iDestruct "↦s" as "[↦ ↦s]". iDestruct "tys" as "[ty tys]".
      iDestruct (ty_size_eq with "ty") as %->. iSplitL "↦ ty".
      { iExists _. rewrite shift_loc_0. iFrame. }
      setoid_rewrite <-shift_loc_assoc_nat. iApply ("IH" with "↦s tys").
  Qed.

  Lemma big_sepL_ty_own_length {𝔄} (ty: type 𝔄) n (aπl: vec _ n) wll d tid :
    ([∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2) -∗
    ⌜length (concat wll) = (n * ty.(ty_size))%nat⌝.
  Proof.
    induction aπl as [|??? IH]; inv_vec wll; [by iIntros|].
    iIntros (??) "/=[ty tys]". iDestruct (ty_size_eq with "ty") as %?.
    iDestruct (IH with "tys") as %?. iPureIntro. rewrite app_length. lia.
  Qed.

  Lemma ty_share_big_sepL {𝔄} (ty: type 𝔄) E aπl d κ l tid q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
    &{κ} ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=>
        ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT #In Bor κ".
    iMod (bor_big_sepL with "LFT Bor") as "Bors"; [done|].
    iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. by iFrame. }
    iDestruct "κ" as "[κ κ₊]". iDestruct "Bors" as "[Bor Bors]".
    iMod (ty_share with "LFT In Bor κ") as "Toshr"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "κ₊ Bors") as "Toshrs".
    iCombine "Toshr Toshrs" as "Toshrs". iApply (step_fupdN_wand with "Toshrs").
    by iIntros "!> [>[$$] >[$$]]".
  Qed.

  Lemma ty_own_proph_big_sepL {𝔄} (ty: type 𝔄) n E (aπl: vec _ n) wll d tid κ q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
    ([∗ list] i ↦ aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜∃ ξll, ξl = mjoin ξll ∧ Forall2 ty.(ty_proph) aπl ξll⌝ ∗ q':+[ξl] ∗
        (q':+[ξl] ={E}=∗
          ([∗ list] i ↦ aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2) ∗ q.[κ]).
  Proof.
    iIntros (?) "#LFT #In tys κ". iInduction aπl as [|] "IH" forall (q)=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>". iExists [], 1%Qp.
      iFrame "κ". iSplit. iExists []. done.
      (iSplit; [done|]). by iIntros. }
    inv_vec wll=> ??. iDestruct "tys" as "[ty tys]". iDestruct "κ" as "[κ κ₊]".
    iMod (ty_own_proph with "LFT In ty κ") as "Upd"; [done|].
    iMod ("IH" with "tys κ₊") as "Upd'". iCombine "Upd Upd'" as "Upd".
    iApply (step_fupdN_wand with "Upd").
    iIntros "!> [>(%&%&%& ξl & Toty) >(%&%&(%&->&%)& ζl & Totys)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iFrame "ξζl". iSplit.
    iExists (ξl :: ξll). rewrite Forall2_cons. done. 
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toty" with "ξl") as "[$$]". by iMod ("Totys" with "ζl") as "[$$]".
  Qed.

  Lemma ty_own_proph_big_sepL_mt {𝔄} (ty: type 𝔄) n E (aπl: vec _ n) l d tid κ q :
    ↑lftN ⊆ E → lft_ctx -∗ κ ⊑ ty_lft ty -∗
    ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) -∗ q.[κ]
      ={E}=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜∃ ξll, ξl = mjoin ξll ∧ Forall2 ty.(ty_proph) aπl ξll⌝ ∗ q':+[ξl] ∗
        (q':+[ξl] ={E}=∗
          ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d tid) ∗ q.[κ]).
  Proof.
    rewrite {1}trans_big_sepL_mt_ty_own. iIntros (?) "LFT In (%& ↦ & tys) κ".
    iMod (ty_own_proph_big_sepL with "LFT In tys κ") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%&%&%& ξl & Totys) !>".
    iExists _, _. iSplit; [done|]. iIntros "{$ξl}ξl".
    iMod ("Totys" with "ξl") as "[tys $]". rewrite trans_big_sepL_mt_ty_own.
    iModIntro. iExists _. iFrame.
  Qed.

  Lemma ty_shr_proph_big_sepL {𝔄} (ty: type 𝔄) n E (aπl: vec _ n) d κ tid l κ' q :
    ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗ κ' ⊑ ty_lft ty -∗
    ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) -∗ q.[κ']
      ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜∃ ξll, ξl = mjoin ξll ∧ Forall2 ty.(ty_proph) aπl ξll⌝ ∗ q':+[ξl] ∗
        (q':+[ξl] ={E}=∗ q.[κ']).
  Proof.
    iIntros (?) "#LFT #In #In' tys κ'". iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. iIntros "!>!>!>!>". iExists [], 1%Qp.
      iFrame "κ'". iSplit. by iExists []. (iSplit; [done|]). by iIntros. }
    iDestruct "κ'" as "[κ' κ'₊]". iDestruct "tys" as "[ty tys]".
    iMod (ty_shr_proph with "LFT In In' ty κ'") as "Upd"; [done|].
    setoid_rewrite <-shift_loc_assoc_nat. iMod ("IH" with "tys κ'₊") as "Upd'".
    iIntros "!>!>". iCombine "Upd Upd'" as "Upd". iApply (step_fupdN_wand with "Upd").
    iIntros "[>(%&%&%& ξl & Toκ') >(%&%&(%&->&%)& ζl & Toκ'₊)] !>".
    iDestruct (proph_tok_combine with "ξl ζl") as (?) "[ξζl Toξζl]".
    iExists _, _. iFrame "ξζl".
    iSplit. iExists (ξl :: ξll). rewrite Forall2_cons. done. 
    iIntros "ξζl". iDestruct ("Toξζl" with "ξζl") as "[ξl ζl]".
    iMod ("Toκ'" with "ξl") as "$". by iMod ("Toκ'₊" with "ζl") as "$".
  Qed.

  Lemma ty_proph_weaken_big_sepL {𝔄} (ty: type 𝔄) n (aπl: vec _ n) ξl:
   (∃ ξll, ξl = mjoin ξll ∧ Forall2 ty.(ty_proph) aπl ξll) → vapply aπl ./[𝔄] ξl.
  Proof. 
    intros (?&->&?). revert x H. induction aπl; intros. done.
    destruct x. inversion H.
    rewrite vec_to_list_cons Forall2_cons in H. destruct H.
    rewrite /vapply. simpl. apply proph_dep_vec_S; unfold compose; simpl.
    by eapply ty_proph_weaken. by apply IHaπl.
  Qed.

  Lemma ty_proph_weaken_big_sepL' {𝔄} (ty: type 𝔄) (aπl: list _) ξll:
    Forall2 ty.(ty_proph) aπl ξll → lapply aπl ./[𝔄] mjoin ξll.
  Proof. 
    intros ?. rewrite -(vec_to_list_to_vec aπl) -vec_to_list_apply. apply proph_dep_constr.
    eapply ty_proph_weaken_big_sepL. eexists _. rewrite vec_to_list_to_vec. done.
  Qed.

  Lemma resolve_big_sepL_ty_own {𝔄} (ty: type 𝔄) Φ n (aπl: vec _ n) wll d tid F q E L :
    resolve E L ty Φ → ↑lftN ∪ ↑prophN ⊆ F →
    lft_ctx -∗ proph_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] i ↦ aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2)
      ={F}=∗ |={F}▷=>^d |={F}=> ⟨π, lforall Φ (lapply aπl π)⟩ ∗ llctx_interp L q.
  Proof.
    iIntros (Rslv ?) "#LFT #PROPH #E L tys".
    iInduction aπl as [|] "IH" forall (q).
    { iApply step_fupdN_full_intro. iFrame "L". by iApply proph_obs_true. }
    inv_vec wll=>/= ??. iDestruct "tys" as "[ty tys]". iDestruct "L" as "[L L₊]".
    iMod (Rslv with "LFT PROPH E L ty") as "Upd"; [done|].
    iMod ("IH" with "L₊ tys") as "Upd'". iCombine "Upd Upd'" as "Upd".
    iApply (step_fupdN_wand with "Upd"). iIntros "!> [>[#? $] >[#? $]]".
    by iApply proph_obs_and.
  Qed.

  Lemma real_big_sepL_ty_own {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) n
      (aπl: vec _ n) wll d tid E L F q :
    real E L ty f → ↑lftN ⊆ F → lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2)
      ={F}=∗ |={F}▷=>^d |={F}=>
        ⌜∃bl, vmap f ∘ vapply aπl = const bl⌝ ∗ llctx_interp L q ∗
        [∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2.
  Proof.
    iIntros ([Rl _]?) "#LFT #E L tys". iInduction aπl as [|] "IH" forall (q).
    { iApply step_fupdN_full_intro. iFrame "L tys". iPureIntro. by exists [#]. }
    inv_vec wll=>/= ??. iDestruct "tys" as "[ty tys]". iDestruct "L" as "[L L₊]".
    iMod (Rl with "LFT E L ty") as "Upd"; [done|].
    iMod ("IH" with "L₊ tys") as "Upd'". iCombine "Upd Upd'" as "Upd".
    iApply (step_fupdN_wand with "Upd"). iIntros "!> [>(%Eq &$&$) >(%Eq' &$&$)] !%".
    move: Eq=> [b Eq]. move: Eq'=> [bl Eq']. exists (b ::: bl).
    fun_ext=>/= π. by move: (equal_f Eq π) (equal_f Eq' π)=>/= <-<-.
  Qed.

  Lemma real_big_sepL_ty_shr {𝔄 𝔅} (ty: type 𝔄) (f: 𝔄 → 𝔅) n
      (aπl: vec _ n) d κ tid l E L F q :
    real E L ty f → ↑lftN ⊆ F → lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
    ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i))
      ={F}▷=∗ |={F}▷=>^d |={F}=>
        ⌜∃bl, vmap f ∘ vapply aπl = const bl⌝ ∗ llctx_interp L q ∗
        [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i).
  Proof.
    iIntros ([_ Rl]?) "#LFT #E L tys". iInduction aπl as [|] "IH" forall (l q)=>/=.
    { iApply step_fupdN_full_intro. iFrame "L". iPureIntro. by exists [#]. }
    iDestruct "tys" as "[ty tys]". iDestruct "L" as "[L L₊]".
    setoid_rewrite <-shift_loc_assoc_nat. iMod (Rl with "LFT E L ty") as "Upd"; [done|].
    iMod ("IH" with "L₊ tys") as "Upd'". iCombine "Upd Upd'" as "Upd". iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iIntros "[>(%Eq &$&$) >(%Eq' &$&$)] !%".
    move: Eq=> [b Eq]. move: Eq'=> [bl Eq']. exists (b ::: bl).
    fun_ext=>/= π. by move: (equal_f Eq π) (equal_f Eq' π)=>/= <-<-.
  Qed.

  Lemma incl_big_sepL_ty_own {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅)
      f n (aπl: vec _ n) wll d tid :
    □ (∀aπ d tid vl, ty.(ty_own) aπ d tid vl -∗ ty'.(ty_own) (f ∘ aπ) d tid vl) -∗
    ([∗ list] aπwl ∈ vzip aπl wll, ty.(ty_own) aπwl.1 d tid aπwl.2) -∗
    [∗ list] bπwl ∈ vzip (vmap (f ∘.) aπl) wll, ty'.(ty_own) bπwl.1 d tid bπwl.2.
  Proof.
    iIntros "#In tys". iInduction aπl as [|] "IH"; inv_vec wll; [done|]=>/= ??.
    iDestruct "tys" as "[ty tys]". iSplitL "ty"; by [iApply "In"|iApply "IH"].
  Qed.

  Lemma incl_big_sepL_ty_shr {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅)
      f n (aπl: vec _ n) d κ tid l :
    ty.(ty_size) = ty'.(ty_size) →
    □ (∀aπ d κ tid l', ty.(ty_shr) aπ d κ tid l' -∗ ty'.(ty_shr) (f ∘ aπ) d κ tid l') -∗
    ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) -∗
    [∗ list] i ↦ bπ ∈ vmap (f ∘.) aπl, ty'.(ty_shr) bπ d κ tid (l +ₗ[ty'] i).
  Proof.
    iIntros (->) "#In tys". iInduction aπl as [|] "IH" forall (l); [done|]=>/=.
    iDestruct "tys" as "[ty tys]". setoid_rewrite <-shift_loc_assoc_nat.
    iSplitL "ty"; by [iApply "In"|iApply "IH"].
  Qed.

  Lemma incl_forall2_ty_proph {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅)
      f n (aπl: vec _ n) ξll:
    (∀aπ ξl, ty.(ty_proph) aπ ξl → ty'.(ty_proph) (f ∘ aπ) ξl) →
    (Forall2 ty.(ty_proph) aπl ξll) → (Forall2 ty'.(ty_proph) (vmap (f ∘.) aπl) ξll).
  Proof.
    revert aπl ξll; induction n; intros ?? In tys; destruct ξll; inv_vec aπl; intros; inversion tys; constructor.
    by apply In. by apply IHn.
  Qed.

  Lemma incl_forall2_ty_proph' {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅)
      f n (aπl: vec _ n) ξll:
    (∀aπ ξl, ty'.(ty_proph) (f ∘ aπ) ξl → ty.(ty_proph) aπ ξl) →
    (Forall2 ty'.(ty_proph) (vmap (f ∘.) aπl) ξll) →
    (Forall2 ty.(ty_proph) aπl ξll).
  Proof.
    revert aπl ξll; induction n; intros ?? In tys; destruct ξll; inv_vec aπl; intros; inversion tys; constructor.
    by apply In. by apply IHn.
  Qed.

  Lemma big_sepL_ty_shr_lft_mono {𝔄} (ty: type 𝔄) aπl d κ κ' tid l :
    κ' ⊑ κ -∗ ([∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ tid (l +ₗ[ty] i)) -∗
    [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d κ' tid (l +ₗ[ty] i).
  Proof.
    iIntros "#? tys". iInduction aπl as [|] "IH" forall (l); [done|]=>/=.
    iDestruct "tys" as "[ty tys]". setoid_rewrite <-shift_loc_assoc_nat.
    iSplitL "ty"; by [iApply ty_shr_lft_mono|iApply "IH"].
  Qed.

  Lemma proph_dep_vlapply m {A n} (aπl: vec (proph A) n) ξl: vapply aπl ./{m} ξl ↔ lapply aπl ./{m} ξl.
  Proof. 
    rewrite -vec_to_list_apply. split; intros. apply proph_dep_constr. done.
    eapply proph_dep_destr; [|done]. typeclasses eauto.
  Qed.

  Lemma proph_eqz_vinsert' {𝔄 n} i xπ yπ (zπl: vec (proph 𝔄) n) (P: (proph 𝔄) → _) :
    xπ :={P}= yπ -∗
    vapply (vinsert i xπ zπl) :={λ vπ ξl, exists ξll, ξl = mjoin ξll /\ Forall2 P (vfunsep vπ) ξll}= vapply (vinsert i yπ zπl).
  Proof.
    iIntros "Eqzs". iApply proph_eqz_mono; [|iApply proph_eqz_vinsert].
    simpl. intros ? (?&->&?). rewrite semi_iso' vec_to_list_insert insert_take_drop in H.
    apply Forall2_app_inv_l in H. destruct H as (?&?&?&?&->). inversion H0.
    rewrite -join_app vapply_insert. simpl. setoid_rewrite vlookup_insert. eexists _, _, _. done.
    rewrite vec_to_list_length. apply fin_to_nat_lt. done. 
  Qed.
End array_util.
