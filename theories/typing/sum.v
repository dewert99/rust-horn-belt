From lrust.typing Require Export type.
From lrust.typing Require Import mod_ty empty.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Notation max_ty_size := (max_hlist_with (λ _, ty_size)).

Section sum.
  Context `{!typeG Σ}.

  Definition is_pad {𝔄l} i (tyl: _ 𝔄l) (vl: list val) : iProp Σ :=
    ⌜((hnthe tyl i).(ty_size) + length vl)%nat = max_ty_size tyl⌝.

  Lemma split_sum_mt {𝔄l} (tyl: _ 𝔄l) vπ d l tid q :
    (l ↦∗{q}: λ vl, ∃i (vπ': proph (lnthe 𝔄l i)) vl' vl'',
      ⌜vπ = pinj i ∘ vπ' ∧ vl = #i :: vl' ++ vl'' ∧ length vl = S (max_ty_size tyl)⌝ ∗
      (hnthe tyl i).(ty_own) vπ' d tid vl')%I ⊣⊢
    ∃i (vπ': proph (lnthe 𝔄l i)), ⌜vπ = pinj i ∘ vπ'⌝ ∗
      (l ↦{q} #i ∗ (l +ₗ S (hnthe tyl i).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
      (l +ₗ 1) ↦∗{q}: (hnthe tyl i).(ty_own) vπ' d tid.
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

  Local Lemma ty_lfts_nth_incl {𝔄l} (tyl: _ 𝔄l) i :
    ⊢ tyl_lft tyl ⊑ ty_lft (hnthe tyl i).
  Proof.
    elim: tyl i. { move=> ?. apply lft_incl_refl. } move=> ?? ty tyl IH i.
    rewrite /tyl_lft lft_intersect_list_app.
    case i; [iApply lft_intersect_incl_l|]=> ?.
    iApply lft_incl_trans; by [iApply lft_intersect_incl_r|iApply IH].
  Qed.

  Program Definition xsum_ty {𝔄l} (tyl: typel 𝔄l) : type (Σ! 𝔄l) := {|
    ty_size := S (max_ty_size tyl);
    ty_lfts := tyl_lfts tyl;  ty_E := tyl_E tyl;
    ty_own vπ d tid vl := ∃i (vπ': proph (lnthe 𝔄l i)) vl' vl'',
      ⌜vπ = pinj i ∘ vπ' ∧ vl = #i :: vl' ++ vl'' ∧ length vl = S (max_ty_size tyl)⌝ ∗
      (hnthe tyl i).(ty_own) vπ' d tid vl';
    ty_shr vπ d κ tid l := ∃i (vπ': proph (lnthe 𝔄l i)), ⌜vπ = pinj i ∘ vπ'⌝ ∗
      &frac{κ} (λ q, l ↦{q} #i ∗
        (l +ₗ S (hnthe tyl i).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
      (hnthe tyl i).(ty_shr) vπ' d κ tid (l +ₗ 1)
  |}%I.
  Next Obligation. move=> *. by iDestruct 1 as (????(_&_&?)) "_". Qed.
  Next Obligation.
    move=> *. iDestruct 1 as (i vπ' vl' vl'' (->&->&->)) "?".
    iExists i, vπ', vl', vl''. iSplit; [done|]. by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> *. iDestruct 1 as (i vπ' ->) "[??]". iExists i, vπ'.
    do 2 (iSplit; [done|]). by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "In". iDestruct 1 as (i vπ' ->) "[??]". iExists i, vπ'.
    iSplit; [done|]. iSplit;
      by [iApply (frac_bor_shorten with "In")|iApply (ty_shr_lft_mono with "In")].
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #? Bor κ". rewrite split_sum_mt.
    iMod (bor_exists_tok with "LFT Bor κ") as (i) "[Bor κ]"; [done|].
    iMod (bor_exists_tok with "LFT Bor κ") as (vπ') "[Bor κ]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor κ") as "(>-> & Bor & κ)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[↦ Bor]"; [done|].
    iMod (ty_share with "LFT [] Bor κ") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_nth_incl]. }
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[? $]".
    iMod (bor_fracture (λ q, _ ↦{q} _ ∗ _ ↦∗{q}: _)%I with "LFT ↦") as "?"; [done|].
    iModIntro. iExists i, vπ'. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #?". iDestruct 1 as (i vπ' vl' vl'' (->&->&->)) "ty".
    iIntros "κ". iMod (ty_own_proph with "LFT [] ty κ") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_nth_incl]. } iModIntro.
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q' ?) "[ξl Toty]".
    iModIntro. iExists ξl, q'. iSplit. { iPureIntro. by apply proph_dep_constr. }
    iFrame "ξl". iIntros "ξl". iMod ("Toty" with "ξl") as "[?$]".
    iModIntro. iExists i, vπ', vl', vl''. by iSplit.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #In #? (%i & %vπ' &->& Bor & ty) κ".
    iMod (ty_shr_proph with "LFT In [] ty κ") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_nth_incl]. } iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξl q' ?) "[ξl Toty]".
    iModIntro. iExists ξl, q'. iSplit. { iPureIntro. by apply proph_dep_constr. }
    iFrame "ξl". iIntros "ξl". iMod ("Toty" with "ξl") as "[?$]".
    iModIntro. iExists i, vπ'. by do 2 (iSplit; [done|]).
  Qed.

  Global Instance xsum_ty_ne {𝔄l} : NonExpansive (@xsum_ty 𝔄l).
  Proof.
    move=> n tyl tyl' Eqv. have EqMsz: max_ty_size tyl = max_ty_size tyl'.
    { elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv. }
    split=>/=.
    - by rewrite EqMsz.
    - rewrite /tyl_lfts. elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - rewrite /tyl_E. elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - move=> *. rewrite EqMsz. do 10 f_equiv. by apply @hnth_ne.
    - move=> *. f_equiv=> i. rewrite /is_pad EqMsz.
      have Eqv': hnthe tyl i ≡{n}≡ hnthe tyl' i by apply @hnth_ne.
      repeat (eapply ty_size_ne || f_equiv)=>//. by rewrite Eqv'.
  Qed.

  Definition sum_ty {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) : type (𝔄 + 𝔅) :=
    <{of_psum_2: Σ!%ST [𝔄; 𝔅] → (𝔄 + 𝔅)%ST}> (xsum_ty +[ty; ty']).

  Global Instance sum_ty_ne {𝔄 𝔅} : NonExpansive2 (@sum_ty 𝔄 𝔅).
  Proof.
    move=> ???????. rewrite /sum_ty. do 2 f_equiv. constructor; by [|constructor].
  Qed.

End sum.

Notation "Σ!" := xsum_ty : lrust_type_scope.
Notation "ty + ty'" := (sum_ty ty%T ty'%T) : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma xsum_lft_morph {𝔅 𝔄l} (Tl: _ 𝔄l) :
    HForall (λ _, TypeLftMorphism) Tl → TypeLftMorphism (λ (ty: _ 𝔅), Σ! (Tl +$ ty))%T.
  Proof.
    move=> All. set s := λ ty, Σ!%T (Tl +$ ty).
    have [[?[?[?[??]]]]|[?[?[??]]]]:
      (∃α βs E, (∀ty, ⊢ ty_lft (s ty) ≡ₗ α ⊓ ty_lft ty) ∧
        (∀ty, elctx_interp (s ty).(ty_E) ⊣⊢
          elctx_interp E ∗ elctx_interp ty.(ty_E) ∗ [∗ list] β ∈ βs, β ⊑ ty_lft ty)) ∨
      (∃α E, (∀ty, ⊢ ty_lft (s ty) ≡ₗ α) ∧
        (∀ty, elctx_interp (s ty).(ty_E) ⊣⊢ elctx_interp E)); [|by eleft|by eright].
    dependent induction All=>/=.
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

  Global Instance xsum_type_ne {𝔄 𝔅l} (T: _ 𝔄 → _ 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]]. have EqMsz: ∀ty ty',
      ty_size ty = ty_size ty' → max_ty_size (Tl +$ ty) = max_ty_size (Tl +$ ty').
    { move=> *. elim All; [done|]=>/= ???? One _ ->. f_equal. by apply One. }
    split=>/=.
    - apply xsum_lft_morph. eapply HForall_impl; [|done]. by move=> >[].
    - move=> *. f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All;
      [|apply _]. rewrite !(hnth_apply (const ∅)).
      do 7 f_equiv; [|by apply All]. do 5 f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All; [|apply _].
      rewrite /is_pad !(hnth_apply (const ∅)). do 4 f_equiv; [|by apply All].
      do 8 f_equiv; [| |by apply EqMsz]; f_equiv; [f_equiv|]; by apply All.
  Qed.
  (* TODO : get rid of this duplication *)
  Global Instance xsum_type_contr {𝔄 𝔅l} (T: _ 𝔄 → _ 𝔅l) :
    ListTypeContractive T → TypeContractive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]].
    have EqMsz: ∀ty ty', max_ty_size (Tl +$ ty) = max_ty_size (Tl +$ ty').
    { move=> *. elim All; [done|]=>/= ???? One _ ->. f_equal. by apply One. }
    split=>/=.
    - apply xsum_lft_morph. eapply HForall_impl; [|done]. by move=> >[].
    - move=> *. f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All;
      [|apply _]. rewrite !(hnth_apply (const ∅)).
      do 7 f_equiv; [|by apply All]. do 5 f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All; [|apply _].
      rewrite /is_pad !(hnth_apply (const ∅)). do 4 f_equiv; [|by apply All].
      do 8 f_equiv; [| |by apply EqMsz]; f_equiv; [f_equiv|]; by apply All.
  Qed.

  Global Instance xsum_copy {𝔄l} (tyl: _ 𝔄l) : ListCopy tyl → Copy (Σ! tyl).
  Proof.
    move=> ?. have Copy: ∀i, Copy (hnthe tyl i).
    { move=> *. apply (HForall_nth _); by [apply _|]. }
    split; [apply _|]. move=>/= ?????? l ?? SubF.
    iIntros "#LFT (%i &%&->& Bor & ty) Na [κ κ']".
    iMod (frac_bor_acc with "LFT Bor κ") as (q) "[>[↦i ↦pad] Toκ]";
    [solve_ndisj|]. iDestruct "↦pad" as (vl') "[↦pad %]".
    iMod (copy_shr_acc with "LFT ty Na κ'") as
      (q' vl) "(Na & ↦ & #ty & Toκ')"; [done| |].
    { rewrite <-SubF, <-union_subseteq_r. apply shr_locsE_subseteq. lia. }
    iDestruct (na_own_acc with "Na") as "[$ ToNa]".
    { apply difference_mono_l. trans (shr_locsE (l +ₗ 1) (max_ty_size tyl));
      [apply shr_locsE_subseteq; lia|set_solver+]. }
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
    iMod ("Toκ'" with "Na [$↦ $↦']") as "[$$]". iApply "Toκ".
    iFrame "↦i ↦i'". iExists vl'. by iFrame.
  Qed.

  Global Instance xsum_send {𝔄l} (tyl: _ 𝔄l) : ListSend tyl → Send (Σ! tyl).
  Proof. move=> Send ?*/=. do 9 f_equiv. by eapply HForall_nth in Send. Qed.
  Global Instance xsum_sync {𝔄l} (tyl: _ 𝔄l) : ListSync tyl → Sync (Σ! tyl).
  Proof. move=> Sync ?*/=. do 6 f_equiv. by eapply HForall_nth in Sync. Qed.

  Lemma xsum_subtype {𝔄l 𝔅l} E L (tyl: _ 𝔄l) (tyl': _ 𝔅l) fl :
    subtypel E L tyl tyl' fl → subtype E L (Σ! tyl) (Σ! tyl') (psum_map fl).
  Proof.
    move=> Subs ?. iIntros "L".
    iAssert (□ (elctx_interp E -∗ ⌜max_ty_size tyl = max_ty_size tyl'⌝))%I as "#EqSz".
    { iInduction Subs as [|?????????? Sub Subs] "IH"; [by iIntros "!>_"|].
      iDestruct (Sub with "L") as "#Sub". iDestruct ("IH" with "L") as "#IH'".
      iIntros "!> E /=". iDestruct ("Sub" with "E") as (->) "#_".
      by iDestruct ("IH'" with "E") as %->. }
    iAssert (□ (elctx_interp E -∗ tyl_lft tyl' ⊑ tyl_lft tyl))%I as "#InLft".
    { iClear "EqSz". iInduction Subs as [|?????????? Sub Subs] "IH".
      { iIntros "!>_". by iApply lft_incl_refl. }
      iDestruct (Sub with "L") as "#Sub". iDestruct ("IH" with "L") as "#IH'".
      iIntros "!> E /=". iDestruct ("Sub" with "E") as (?) "#[?_]".
      iDestruct ("IH'" with "E") as "#?".
      rewrite /tyl_lft !lft_intersect_list_app. by iApply lft_intersect_mono. }
    move/subtypel_llctx_nth in Subs. iDestruct (Subs with "L") as "#InTyl".
    iIntros "!> #E". iDestruct ("EqSz" with "E") as %EqSz.
    iSpecialize ("InLft" with "E"). iSpecialize ("InTyl" with "E").
    iSplit; simpl; [iPureIntro; by f_equal|]. iSplit; [done|].
    set EqLen := plist2_eq_len fl. iSplit; iModIntro; iIntros "*".
    - iDestruct 1 as (i vπ' vl' vl'' (->&->&->)) "?".
      iExists i, (p2nth id fl i ∘ vπ'), vl', vl''. rewrite EqSz. iSplit.
      { iPureIntro. split; [|done]. fun_ext=>/= ?. by rewrite psum_map_pinj. }
      iDestruct ("InTyl" $! i) as (_) "[_[InOwn _]]". by iApply "InOwn".
    - iDestruct 1 as (i vπ' ->) "[??]". iExists i, (p2nth id fl i ∘ vπ').
      rewrite /is_pad EqSz. iDestruct ("InTyl" $! i) as (->) "[_[_ InShr]]".
      iSplit. { iPureIntro. fun_ext=>/= ?. by rewrite psum_map_pinj. }
      iSplit; by [|iApply "InShr"].
  Qed.

  Lemma xsum_eqtype {𝔄l 𝔅l} E L (tyl: _ 𝔄l) (tyl': _ 𝔅l) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (Σ! tyl) (Σ! tyl') (psum_map fl) (psum_map gl).
  Proof.
    move=> /eqtypel_subtypel[??]. by split; apply xsum_subtype.
  Qed.

  Lemma sum_subtype {𝔄 𝔅 𝔄' 𝔅'} E L (f: 𝔄 → 𝔄') (g: 𝔅 → 𝔅') ty1 ty2 ty1' ty2' :
    subtype E L ty1 ty1' f → subtype E L ty2 ty2' g →
    subtype E L (ty1 + ty2) (ty1' + ty2') (sum_map f g).
  Proof.
    move=> A B. eapply subtype_eq. { apply mod_ty_subtype; [apply _|].
    apply xsum_subtype. solve_typing. } fun_ext. by case.
  Qed.

  Lemma sum_eqtype {𝔄 𝔅 𝔄' 𝔅'} E L (f: 𝔄 → 𝔄') f' (g: 𝔅 → 𝔅') g' ty1 ty2 ty1' ty2' :
    eqtype E L ty1 ty1' f f' → eqtype E L ty2 ty2' g g' →
    eqtype E L (ty1 + ty2) (ty1' + ty2') (sum_map f g) (sum_map f' g').
  Proof. move=> [??][??]. split; by apply sum_subtype. Qed.

End typing.

Global Hint Resolve xsum_subtype xsum_eqtype sum_subtype sum_eqtype: lrust_typing.
