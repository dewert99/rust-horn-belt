From iris.proofmode Require Import proofmode.
From lrust.typing Require Import lft_contexts mod_ty.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Notation max_ty_size := (max_hlist_with (λ _, ty_size)).

Lemma xsum_ghost_level_le {𝔄l} (i: fin (length 𝔄l)) : (ghost_level (𝔄l !!ₗ i) <= ghost_level (Σ! 𝔄l))%nat.
Proof.
  rewrite /llookup. simpl. induction 𝔄l as [|? v IH]; inv_fin i; rewrite fmap_cons; simpl. simpl.
  lia. intros. simpl in i. specialize (IH i).
  simpl. transitivity (foldr Init.Nat.max 0%nat (ghost_level <$> v)). done.
  lia.
Qed.

Section sum.
  Context `{!typeG Σ}.

  Definition is_sum_pad {𝔄l} i (tyl: typel 𝔄l) (vl: list val) : iProp Σ :=
    ⌜((tyl +!! i).(ty_size) + length vl)%nat = max_ty_size tyl⌝.

  Lemma split_mt_sum {𝔄l} (tyl: typel 𝔄l) vπ d l tid :
    (l ↦∗: λ vl, ∃i vπ' vl' vl'',
      ⌜vπ = pinj i ∘ vπ' ∧ vl = #i :: vl' ++ vl'' ∧ length vl = S (max_ty_size tyl)⌝ ∗
      (tyl +!! i).(ty_own) vπ' d tid vl') ⊣⊢
    ∃i vπ', ⌜vπ = pinj i ∘ vπ'⌝ ∗
      (l ↦ #i ∗ (l +ₗ S (tyl +!! i).(ty_size)) ↦∗: is_sum_pad i tyl) ∗
      (l +ₗ 1) ↦∗: (tyl +!! i).(ty_own) vπ' d tid.
  Proof. iSplit.
    - iIntros "(%& ↦ & ty)". iDestruct "ty" as (i vπ' vl' vl'' (->&->&[=])) "ty".
      iExists i, vπ'. iSplit; [done|]. iDestruct (ty_size_eq with "ty") as "%Eq'".
      iDestruct (heap_mapsto_vec_cons with "↦") as "[$ ↦]".
      iDestruct (heap_mapsto_vec_app with "↦") as "[↦ ↦']".
      iSplitL "↦'"; [|iExists vl'; by iFrame]. iExists vl''.
      rewrite (shift_loc_assoc_nat _ 1) Eq'. iFrame "↦'". iPureIntro.
      by rewrite -Eq' -app_length.
    - iDestruct 1 as (i vπ' ->) "[[↦ (%vl'' & ↦'' &%)] (%vl' & ↦' & ty)]".
      iDestruct (ty_size_eq with "ty") as "%Eq". iExists (#i :: vl' ++ vl'').
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app (shift_loc_assoc_nat _ 1) Eq.
      iFrame "↦ ↦' ↦''". iExists i, vπ', vl', vl''. iFrame "ty". iPureIntro.
      do 2 (split; [done|]). rewrite/= app_length Eq. by f_equal.
  Qed.

  Lemma ty_lfts_lookup_incl {𝔄l} (tyl: typel 𝔄l) i :
    ⊢ tyl_lft tyl ⊑ ty_lft (tyl +!! i).
  Proof.
    induction tyl; inv_fin i; rewrite /tyl_lft /tyl_lfts /= lft_intersect_list_app;
    [by iApply lft_intersect_incl_l|]=> ?.
    iApply lft_incl_trans; by [iApply lft_intersect_incl_r|iApply IHtyl].
  Qed.

  Program Definition xsum_ty {𝔄l} (tyl: typel 𝔄l) : type (Σ! 𝔄l) := {|
    ty_size := S (max_ty_size tyl);
    ty_lfts := tyl_lfts tyl;  ty_E := tyl_E tyl;
    ty_proph vπ ξl := exists i (vπ': proph (𝔄l !!ₗ i)), vπ = pinj i ∘ vπ' /\ (tyl +!! i).(ty_proph) vπ' ξl;
    ty_own vπ d tid vl := ∃i (vπ': proph (𝔄l !!ₗ i)) vl' vl'',
      ⌜vπ = pinj i ∘ vπ' ∧ vl = #i :: vl' ++ vl'' ∧ length vl = S (max_ty_size tyl)⌝ ∗
      (tyl +!! i).(ty_own) vπ' d tid vl';
    ty_shr vπ d κ tid l := ∃i (vπ': proph (𝔄l !!ₗ i)), ⌜vπ = pinj i ∘ vπ'⌝ ∗
      &frac{κ} (λ q, l ↦{q} #i ∗
        (l +ₗ S (tyl +!! i).(ty_size)) ↦∗{q}: is_sum_pad i tyl) ∗
      (tyl +!! i).(ty_shr) vπ' d κ tid (l +ₗ 1)
  |}%I.
  Next Obligation. move=> *. by iDestruct 1 as (????(_&_&?)) "_". Qed.
  Next Obligation. move=>/= *. do 9 f_equiv. by apply ty_own_depth_mono. Qed.
  Next Obligation. move=>/= *. do 6 f_equiv. by apply ty_shr_depth_mono. Qed.
  Next Obligation.
    move=> *. iIntros "In (%&%&->&?&?)". iExists _, _. iSplit; [done|].
    iSplit; by [iApply (frac_bor_shorten with "In")|iApply (ty_shr_lft_mono with "In")].
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #? Bor κ". rewrite split_mt_sum.
    iMod (bor_exists_tok with "LFT Bor κ") as (i) "[Bor κ]"; [done|].
    iMod (bor_exists_tok with "LFT Bor κ") as (vπ') "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[↦ Bor]"; [done|].
    iMod (ty_share with "LFT [] Bor κ") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_lookup_incl]. }
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[? $]".
    iMod (bor_fracture (λ q, _ ↦{q} _ ∗ _ ↦∗{q}: _)%I with "LFT ↦") as "?"; [done|].
    iModIntro. iExists i, vπ'. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #?". iDestruct 1 as (i vπ' vl' vl'' (->&->&->)) "ty".
    iIntros "κ". iMod (ty_own_proph with "LFT [] ty κ") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_lookup_incl]. }
    iModIntro. iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q' ?) "[ξl Toty]".
    iModIntro. iExists ξl, q'. iSplit.
    - iPureIntro. eexists _, _. done.
    - iIntros "{$ξl}ξl". iMod ("Toty" with "ξl") as "[?$]".
      iModIntro. iExists i, vπ', vl', vl''. by iSplit.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #In #? (%i & %vπ' &->& Bor & ty) κ".
    iMod (ty_shr_proph with "LFT In [] ty κ") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_lookup_incl]. }
    iIntros "!>!>". iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q' ?) "[ξl Toκ]".
    iModIntro. iExists ξl, q'. iSplit.
    - iPureIntro. eexists _, _. done.
    - iIntros "{$ξl}ξl". by iMod ("Toκ" with "ξl").
  Qed.
  Next Obligation.
    move=> 𝔄l???[x[?[->?]]]. apply proph_dep_constr.
    eapply proph_dep_level_mono; [|by eapply ty_proph_weaken].
    apply xsum_ghost_level_le.
  Qed.

  Global Instance xsum_ty_ne {𝔄l} : NonExpansive (@xsum_ty 𝔄l).
  Proof.
    move=> n tyl tyl' Eqv. have EqMsz: max_ty_size tyl = max_ty_size tyl'.
    { elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv. }
    split=>/=.
    - by rewrite EqMsz.
    - rewrite /tyl_lfts. elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - rewrite /tyl_E. elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - move=> *. do 5 f_equiv. rewrite ty_proph_ne; try done. by apply @hlookup_ne.
    - move=> *. rewrite EqMsz. do 10 f_equiv. by apply @hlookup_ne.
    - move=> *. f_equiv=> i. rewrite /is_sum_pad EqMsz.
      have Eqv': tyl +!! i ≡{n}≡ tyl' +!! i by apply @hlookup_ne.
      repeat (eapply ty_size_ne || f_equiv)=>//. by rewrite Eqv'.
  Qed.

End sum.

Notation "Σ!" := xsum_ty : lrust_type_scope.
Notation empty_ty := (xsum_ty +[]).

Section typing.
  Context `{!typeG Σ}.

  Lemma xsum_lft_morphism {𝔅 𝔄l} (Tl: hlist (λ 𝔄, type 𝔅 → type 𝔄) 𝔄l) :
    TCHForall (λ 𝔄, TypeLftMorphism) Tl →
    TypeLftMorphism (λ ty: type 𝔅, Σ! (Tl +$ ty))%T.
  Proof.
    move=> All. set T := λ ty, Σ!%T (Tl +$ ty).
    have [[?[?[?[??]]]]|[?[?[??]]]]:
      (∃α βs E, (∀ty, ⊢ ty_lft (T ty) ≡ₗ α ⊓ ty_lft ty) ∧
        (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢
          elctx_interp E ∗ elctx_interp ty.(ty_E) ∗ [∗ list] β ∈ βs, β ⊑ ty_lft ty)) ∨
      (∃α E, (∀ty, ⊢ ty_lft (T ty) ≡ₗ α) ∧
        (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢ elctx_interp E)); [|by eleft|by eright].
    induction All=>/=.
    { right. exists static, []. split=> ?; by [|apply lft_equiv_refl]. }
    setoid_rewrite lft_intersect_list_app.
    case IHAll=> [[α[βs[E[Hα HE]]]]|[α[E[Hα HE]]]];
    case H=> [α' βs' E' Hα' HE'|α' E' Hα' HE'].
    - left. exists (α' ⊓ α), (βs' ++ βs), (E' ++ E). split=> ?.
      + iApply lft_equiv_trans.
        { iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα]. }
        rewrite -!assoc (comm (⊓) _ (α ⊓ _)) -!assoc.
        repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
        iApply lft_intersect_equiv_idemp.
      + rewrite !elctx_interp_app HE' HE big_sepL_app -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - left. exists (α' ⊓ α), βs, (E' ++ E). split=> ?.
      + rewrite -assoc. iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
      + by rewrite !elctx_interp_app HE' HE -!assoc.
    - left. exists (α' ⊓ α), βs', (E' ++ E). split=> ?.
      + rewrite -!assoc (comm (⊓) α _) !assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
      + rewrite/= !elctx_interp_app HE' HE -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    - right. exists (α' ⊓ α), (E' ++ E). split=> ?.
      + iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
      + by rewrite !elctx_interp_app HE HE'.
  Qed.

  Global Instance xsum_base_type_ne {𝔄 𝔅l} (Tl: hlist (λ 𝔅, type 𝔄 → type 𝔅) 𝔅l) :
    TCHForall (λ _, TypeNonExpansiveBase) Tl → TypeNonExpansiveBase (Σ! ∘ (happly Tl))%T.
  Proof.
    move=> All. split=>/=.
    - apply xsum_lft_morphism. eapply TCHForall_impl; [|done]. move=> /= ???. apply type_ne_type_lft_morphism.
    - move=> ?? H *. do 5 f_equiv. rewrite !hlookup_apply. by eapply type_ne_ty_proph.
    Unshelve. eapply TCHForall_lookup in All. apply All.
    - intros ???ξ(i&vπ&->&?). rewrite !hlookup_apply in H.
    specialize (TCHForall_lookup i _ _ All) as TNE. simpl in TNE.
     edestruct (type_ne_ty_proph_invert (𝔄:=𝔄) ty vπ ξ H) as (vπl&ξl&?&?).
    exists vπl, ξl. intuition. eexists _, _. rewrite !hlookup_apply. intuition.
  Qed.

  Global Instance xsum_type_ne {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]]. have EqMsz: ∀ty ty',
      ty_size ty = ty_size ty' → max_ty_size (Tl +$ ty) = max_ty_size (Tl +$ ty').
    { move=> *. elim All; [done|]=>/= ???? One _ ->. f_equal. by apply One. }
    split=>/=.
    - move=> *. f_equiv. by apply EqMsz.
    - eapply xsum_base_type_ne, TCHForall_impl; [|done]. move=> /= *. apply type_ne_base.
    - move=> *. f_equiv=> ?. eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      do 7 f_equiv; [|by apply All]. do 5 f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> ?. eapply TCHForall_lookup in All.
      rewrite /is_sum_pad !hlookup_apply. do 4 f_equiv; [|by apply All].
      do 8 f_equiv; [| |by apply EqMsz]; f_equiv; [f_equiv|]; by apply All.
  Qed.
  (* TODO : get rid of this duplication *)
  Global Instance xsum_type_contractive {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeContractive T → TypeContractive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]].
    have EqMsz: ∀ty ty', max_ty_size (Tl +$ ty) = max_ty_size (Tl +$ ty').
    { move=> *. elim All; [done|]=>/= ???? One _ ->. f_equal. by apply One. }
    split=>/=.
    - move=> *. f_equiv. by apply EqMsz.
    - eapply xsum_base_type_ne, TCHForall_impl; [|done]. move=> /= *. apply type_ne_base.
    - move=> *. f_equiv=> ?. eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      do 7 f_equiv; [|by apply All]. do 5 f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> ?. eapply TCHForall_lookup in All.
      rewrite /is_sum_pad !hlookup_apply. do 4 f_equiv; [|by apply All].
      do 8 f_equiv; [| |by apply EqMsz]; f_equiv; [f_equiv|]; by apply All.
  Qed.

  Global Instance xsum_copy {𝔄l} (tyl: typel 𝔄l) : ListCopy tyl → Copy (Σ! tyl).
  Proof.
    move=> ?. have Copy: ∀i, Copy (hlookup tyl i).
    { move=> *. by apply TCHForall_lookup. }
    split; [apply _|]. move=>/= ?????? l ?? SubF.
    iIntros "#LFT (%i &%&->& Bor & ty) Na [κ κ₊]".
    iMod (frac_bor_acc with "LFT Bor κ") as (q) "[>[↦i ↦pad] Toκ]"; [solve_ndisj|]. iDestruct "↦pad" as (vl') "[↦pad %]".
    iMod (copy_shr_acc with "LFT ty Na κ₊") as (q' vl) "(Na & ↦ & #ty & Toκ₊)"; [done|..].
    { rewrite <-SubF, <-union_subseteq_r. apply shr_locsE_subseteq. lia. }
    iDestruct (na_own_acc with "Na") as "[$ ToNa]".
    { apply difference_mono_l. trans (shr_locsE (l +ₗ 1) (max_ty_size tyl)).
      { apply shr_locsE_subseteq. lia. } set_solver+. }
    case (Qp_lower_bound q q')=> [q''[?[?[->->]]]].
    iExists q'', (#i :: vl ++ vl').
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_app shift_loc_assoc
      -Nat.add_1_l Nat2Z.inj_add.
    iDestruct "↦i" as "[$ ↦i]". iDestruct "↦" as "[$ ↦]".
    iDestruct (ty_size_eq with "ty") as ">%Eq". rewrite Eq.
    iDestruct "↦pad" as "[$ ↦pad]". iSplitR.
    { iIntros "!>!>". iExists i, _, vl, vl'. iFrame "ty". iPureIntro.
      do 2 (split; [done|]). rewrite/= app_length Eq. by f_equal. }
    iIntros "!> Na (↦i' & ↦' & ↦pad')". iDestruct ("ToNa" with "Na") as "Na".
    iMod ("Toκ₊" with "Na [$↦ $↦']") as "[$$]". iApply "Toκ".
    iFrame "↦i ↦i'". iExists vl'. by iFrame.
  Qed.

  Global Instance xsum_send {𝔄l} (tyl: typel 𝔄l) : ListSend tyl → Send (Σ! tyl).
  Proof. move=> Send ?*/=. do 9 f_equiv. by eapply TCHForall_lookup in Send. Qed.
  Global Instance xsum_sync {𝔄l} (tyl: typel 𝔄l) : ListSync tyl → Sync (Σ! tyl).
  Proof. move=> Sync ?*/=. do 6 f_equiv. by eapply TCHForall_lookup in Sync. Qed.

  Lemma xsum_resolve {𝔄l} E L (tyl: typel 𝔄l) Φl :
    resolvel E L tyl Φl →
    resolve E L (Σ! tyl) (λ s, let 'xinj i x := to_xsum s in (Φl -!! i) x).
  Proof.
    iIntros (Rslv ???????) "LFT PROPH E L (%&%&%&%&[-> _] & ty)".
    eapply HForall_1_lookup in Rslv.
    iMod (Rslv with "LFT PROPH E L ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). iIntros "!> >[Obs $] !>".
    iApply proph_obs_impl; [|done]=>/= ??. by rewrite to_xsum_pinj.
  Qed.

  Lemma xsum_resolve_just {𝔄l} E L (tyl: typel 𝔄l) :
    HForall (λ _ ty, resolve E L ty (const True)) tyl → resolve E L (Σ! tyl) (const True).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma xsum_real {𝔄l 𝔅l} E L tyl (fl: plist2 _ 𝔄l 𝔅l) :
    reall E L tyl fl → real (𝔅:=Σ!_) E L (Σ! tyl) (psum_map fl).
  Proof.
    move=> Rl. split.
    - iIntros "*% LFT E L (%i &%&%&%&[->%]&ty)". eapply HForall_1'_lookup in Rl.
      iMod (proj1 Rl with "LFT E L ty") as "Upd"; [done|].
      iApply (step_fupdN_wand with "Upd"). iIntros "!> >(%Eq &$&?) !>".
      iSplit; last first. { iExists _, _, _, _. by iFrame. }
      iPureIntro. move: Eq=> [b Eq]. exists (pinj _ b). fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-. by rewrite psum_map_pinj.
    - iIntros "*% LFT E L (%&%&->&?& ty)". eapply HForall_1'_lookup in Rl.
      iMod (proj2 Rl with "LFT E L ty") as "Upd"; [done|]. iIntros "!>!>".
      iApply (step_fupdN_wand with "Upd"). iIntros ">(%Eq &$&?) !>".
      iSplit; last first. { iExists _, _. by iFrame. }
      iPureIntro. move: Eq=> [b Eq]. exists (pinj _ b). fun_ext=>/= π.
      move: (equal_f Eq π)=>/= <-. by rewrite psum_map_pinj.
  Qed.

  Lemma xsum_subtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl :
    subtypel E L tyl tyl' fl → subtype E L (Σ! tyl) (Σ! tyl') (psum_map fl).
  Proof.
    move=> Subs ?. iIntros "L".
    iAssert (□ (elctx_interp E -∗ ⌜max_ty_size tyl = max_ty_size tyl'⌝))%I as "#EqSz".
    { iInduction Subs as [|?????????? Sub Subs] "IH"; [by iIntros "!>_"|].
      iDestruct (Sub with "L") as "#Sub". iDestruct ("IH" with "L") as "#IH'".
      iIntros "!> E /=". iDestruct ("Sub" with "E") as ([->?]) "#_".
      by iDestruct ("IH'" with "E") as %->. }
    iAssert (□ (elctx_interp E -∗ tyl_lft tyl' ⊑ tyl_lft tyl))%I as "#InLft".
    { iClear "EqSz". iInduction Subs as [|?????????? Sub Subs] "IH".
      { iIntros "!>_". by iApply lft_incl_refl. }
      iDestruct (Sub with "L") as "#Sub". iDestruct ("IH" with "L") as "#IH'".
      iIntros "!> E /=". iDestruct ("Sub" with "E") as (?) "#[?_]".
      iDestruct ("IH'" with "E") as "#?".
      rewrite /tyl_lft !lft_intersect_list_app. by iApply lft_intersect_mono. }
    move/subtypel_llctx_lookup in Subs. iDestruct (Subs with "L") as "#InTyl".
    iIntros "!> #E". iDestruct ("EqSz" with "E") as %EqSz.
    iSpecialize ("InLft" with "E"). iSpecialize ("InTyl" with "E").
    iSplit; simpl. iAssert ⌜forall i, (_: Prop)⌝%I as %InProph.
    iApply pure_forall_2. iIntros (i). iDestruct ("InTyl" $! i) as "((_&res)&_&_&_)". iExact "res".
    iPureIntro. split. by f_equal.
    intros ??(i&?&->&?). eexists _, _; split; [|by apply InProph]. 
    fun_ext. simpl. intros. by rewrite psum_map_pinj.
    iSplit; [done|].
    iSplit; iModIntro; iIntros "*".
    - iDestruct 1 as (i vπ' vl' vl'' (->&->&->)) "?".
      iExists (fin_renew_by_plist2 fl i), (_ ∘ vπ'), vl', vl''. rewrite EqSz. iSplit.
      { iPureIntro. split; [|by rewrite fin_to_nat_fin_renew]. fun_ext=>/= ?.
        by rewrite psum_map_pinj. }
      iDestruct ("InTyl" $! i) as (_) "[_[InOwn _]]". by iApply "InOwn".
    - iDestruct 1 as (i vπ' ->) "[??]".
      iExists (fin_renew_by_plist2 fl i), (fl -2!! i ∘ vπ').
      rewrite /is_sum_pad EqSz. iDestruct ("InTyl" $! i) as ([->?]) "[_[_ InShr]]".
      iSplit. { iPureIntro. fun_ext=>/= ?. by rewrite psum_map_pinj. }
      iSplit; [by rewrite fin_to_nat_fin_renew|by iApply "InShr"].
  Qed.

  Lemma xsum_eqtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (Σ! tyl) (Σ! tyl') (psum_map fl) (psum_map gl).
  Proof.
    move=> /eqtypel_subtypel[??]. by split; apply xsum_subtype.
  Qed.

  Lemma fin_renew_inj n m (H: eq_nat n m): Inj (=) (=) (fin_renew H).
  Proof. 
    revert m H. induction n; intros ?????; destruct m; inv_fin x; inv_fin y; try done.
    simpl. intros ??[= ?%existT_inj]. f_equal. eapply IHn. done.
  Qed.

  Lemma HForall2_1_lookup {A Xl Yl} {F G: A → Type} {H: A → A → Type} i {Φ: ∀X Y, F X → G Y → H X Y → Prop} {xl: hlist F Xl} {yl: hlist G Yl} {zl} :
    HForall2_1 Φ xl yl zl → Φ _ _ (xl +!! i) (yl +!! (fin_renew_by_plist2 zl i)) (zl -2!! i).
  Proof. move=> All. induction All; inv_fin i; [done|]. apply IHAll. Qed.

  Lemma xsum_blocked_subtype {𝔄l 𝔅l} (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl :
    blocked_subtypel tyl tyl' fl → blocked_subtype (Σ! tyl) (Σ! tyl') (psum_map fl).
  Proof.
    intros Sub. rewrite /blocked_subtypel in Sub. split. intros ??.
    destruct (psum_destruct x _ eq_refl) as (?&->). intros.
    destruct (psum_destruct y _ eq_refl) as (?&?).
    eassert _ as H1. exact H. rewrite e in H1. revert H1.
    rewrite 2! psum_map_pinj. intros (?%fin_renew_inj&?)%pinj_inj.
    revert H. destruct (psum_destruct y (psum_variant_id x)) as (?&->). done.
    rewrite 2! psum_map_pinj. intros (_&?)%pinj_inj.
    apply JMeq_eq in H. f_equal. destruct (HForall2_1_lookup (psum_variant_id x) Sub) as [??].
    apply (inj _ _ _ H).
    intros ??(i&?).
    specialize (semi_iso' _ (fin_renew_by_plist2 fl) i) as eq.
    rewrite -eq in H. destruct H as (vπ'&?&?). 
    eassert (∀ π, _). intros. specialize (equal_f H π). simpl.
    destruct (psum_destruct (vπ π) _ eq_refl) as (?&->). rewrite psum_map_pinj. intros. apply pinj_inj in H1 as [?%semi_iso_inj _]. exact H1.
    destruct (psum_destruct_fun vπ _ X) as (?&->).
    eexists _, _. split. done.
    destruct (HForall2_1_lookup (fin_renew_by_plist2' fl i) Sub) as [? InProph].
    apply InProph. simpl. revert H0. eassert (impl _ _); [|done]. f_equiv.
    fun_ext. simpl. intros π. specialize (equal_f H π). simpl. rewrite psum_map_pinj. intros. apply pinj_inj in H0 as [?%semi_iso_inj ?].
    symmetry. by apply JMeq_eq.
  Qed.

  Lemma xsum_blocked_eqtype {𝔄l 𝔅l} (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl gl :
    blocked_eqtypel tyl tyl' fl gl →
    blocked_eqtype (Σ! tyl) (Σ! tyl') (psum_map fl) (psum_map gl).
  Proof.
    move=> /blocked_eqtypel_subtypel[??]. by split; apply xsum_blocked_subtype.
  Qed.
End typing.

Global Instance empty_ty_empty `{!typeG Σ} : Empty (type ∅) := empty_ty.

Global Hint Resolve xsum_resolve | 5 : lrust_typing.
Global Hint Resolve xsum_resolve_just xsum_real xsum_subtype xsum_eqtype
  : lrust_typing.
