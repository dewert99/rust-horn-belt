Require Import FunctionalExtensionality Equality.
From lrust.typing Require Export type.
From lrust.typing Require Import mod_ty.
Set Default Proof Using "Type".

Notation max_ty_size := (max_hlist_with (λ _, ty_size)).

Section sum.
  Context `{!typeG Σ}.

  (* We define the actual empty type as being the empty sum, so that it is
     convertible to it---and in particular, we can pattern-match on it
     (as in, pattern-match in the language of lambda-rust, not in Coq). *)
  Program Definition empty_ty `{!typeG Σ} : type ∅ :=
    {| pt_size := 1;  pt_own _ _ _ := False; |}%I.
  Next Obligation. by iIntros. Qed.
  Global Instance empty_ty_empty: Empty (type ∅) := empty_ty.

  Global Instance empty_send: Send ∅. Proof. done. Qed.

  Definition is_pad {As} i (tyl: _ As) (vl: list val) : iProp Σ :=
    ⌜((hnthe tyl i).(ty_size) + length vl)%nat = max_ty_size tyl⌝.

  Lemma split_sum_mt {As} (tyl: _ As) vπ d l tid q :
    (l ↦∗{q}: λ vl, ∃i vπ' vl' vl'', ⌜vπ = xinj i ∘ vπ'⌝ ∗
      ⌜vl = #i :: vl' ++ vl''⌝ ∗ ⌜length vl = S (max_ty_size tyl)⌝ ∗
      (hnthe tyl i).(ty_own) vπ' d tid vl')%I ⊣⊢
    ∃i vπ', ⌜vπ = xinj i ∘ vπ'⌝ ∗
      (l ↦{q} #i ∗ (l +ₗ S (hnthe tyl i).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
      (l +ₗ 1) ↦∗{q}: (hnthe tyl i).(ty_own) vπ' d tid.
  Proof. iSplit.
    - iIntros "(%& Mt & Own)". iDestruct "Own" as (i vπ' vl' vl'' ->->[=]) "Own".
      iExists i, vπ'. iSplit; [done|]. iDestruct (ty_size_eq with "Own") as "%Eq'".
      iDestruct (heap_mapsto_vec_cons with "Mt") as "[$ Mt]".
      iDestruct (heap_mapsto_vec_app with "Mt") as "[Mt Mt']".
      iSplitL "Mt'"; [|iExists vl'; by iFrame]. iExists vl''.
      rewrite (shift_loc_assoc_nat _ 1) Eq'. iFrame "Mt'". iPureIntro.
      by rewrite -Eq' -app_length.
    - iDestruct 1 as (i vπ' ->) "[[Mt (%vl''&Mt''&%)](%vl'&Mt'&Own)]".
      iDestruct (ty_size_eq with "Own") as "%Eq". iExists (#i :: vl' ++ vl'').
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app (shift_loc_assoc_nat _ 1) Eq.
      iFrame "Mt Mt' Mt''". iExists i, vπ', vl', vl''. do 2 (iSplit; [done|]).
      iFrame "Own". iPureIntro. rewrite/= app_length Eq. by f_equal.
  Qed.

  Local Lemma ty_lfts_nth_incl {As} (tyl: typel As) i :
    ⊢ tyl_lft tyl ⊑ ty_lft (hnthe tyl i).
  Proof.
    elim: tyl i=>/= [|?? ty tyl IH] [|?];
      [by iApply lft_incl_refl|by iApply lft_incl_refl| |];
      rewrite lft_intersect_list_app; [by iApply lft_intersect_incl_l|].
    iApply lft_incl_trans; by [iApply lft_intersect_incl_r|iApply IH].
  Qed.

  Program Definition xsum_ty {As} (tyl: typel As) : type (Σ! As) := {|
    ty_size := S (max_ty_size tyl);
    ty_lfts := tyl_lfts tyl;  ty_E := tyl_E tyl;
    ty_own vπ d tid vl := ∃i vπ' vl' vl'', ⌜vπ = xinj i ∘ vπ'⌝ ∗
      ⌜vl = #i :: vl' ++ vl''⌝ ∗ ⌜length vl = S (max_ty_size tyl)⌝ ∗
      (hnthe tyl i).(ty_own) vπ' d tid vl';
    ty_shr vπ d κ tid l := ∃i vπ', ⌜vπ = xinj i ∘ vπ'⌝ ∗
      &frac{κ} (λ q, l ↦{q} #i ∗
        (l +ₗ S (hnthe tyl i).(ty_size)) ↦∗{q}: is_pad i tyl) ∗
      (hnthe tyl i).(ty_shr) vπ' d κ tid (l +ₗ 1)
  |}%I.
  Next Obligation. move=> *. by iDestruct 1 as (???????) "?". Qed.
  Next Obligation.
    move=> */=. iDestruct 1 as (i vπ' vl' vl'' ->->->) "?".
    iExists i, vπ', vl', vl''. do 3 (iSplit; [done|]). by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iDestruct 1 as (i vπ' ->) "[??]". iExists i, vπ'.
    do 2 (iSplit; [done|]). by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> */=. iIntros "In". iDestruct 1 as (i vπ' ->) "[??]". iExists i, vπ'.
    iSplit; [done|]. iSplit;
      by [iApply (frac_bor_shorten with "In")|iApply (ty_shr_lft_mono with "In")].
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #? Bor Tok". rewrite split_sum_mt.
    iMod (bor_exists with "LFT Bor") as (i) "Bor"; [done|].
    iMod (bor_exists_tok with "LFT Bor Tok") as (vπ') "[Bor Tok]"; [done|].
    iMod (bor_sep_persistent with "LFT Bor Tok") as "(>-> & Bor & Tok)"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Mt Bor]"; [done|].
    iMod (ty_share with "LFT [] Bor Tok") as "Upd"; [done| |].
    { iApply lft_incl_trans; by [|iApply ty_lfts_nth_incl]. }
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[Shr $]".
    iMod (bor_fracture (λ q, _ ↦{q} _ ∗ _ ↦∗{q}: _)%I with "LFT Mt") as "?"; [done|].
    iModIntro. iExists i, vπ'. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #?". iDestruct 1 as (i vπ' vl' vl'' ->->->) "Own".
    iIntros "Tok". iMod (ty_own_proph with "LFT [] Own Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply ty_lfts_nth_incl]. } iModIntro.
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q' ?) "[PTok Close]".
    iModIntro. iExists ξs, q'. iSplit. { iPureIntro. by apply proph_dep_constr. }
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[?$]".
    iModIntro. iExists i, vπ', vl', vl''. by do 3 (iSplit; [done|]).
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #In #? (%i & %vπ' &->& Bor & Shr) Tok".
    iMod (ty_shr_proph with "LFT In [] Shr Tok") as "Upd"; first done.
    { iApply lft_incl_trans; by [|iApply ty_lfts_nth_incl]. } iIntros "!>!>".
    iApply (step_fupdN_wand with "Upd"). iMod 1 as (ξs q' ?) "[PTok Close]".
    iModIntro. iExists ξs, q'. iSplit. { iPureIntro. by apply proph_dep_constr. }
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[?$]".
    iModIntro. iExists i, vπ'. by do 2 (iSplit; [done|]).
  Qed.

  Global Instance xsum_ty_ne {As} : NonExpansive (@xsum_ty As).
  Proof.
    move=> n tyl tyl' Eqv. have EqMsz: max_ty_size tyl = max_ty_size tyl'.
    { elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv. }
    split=>/=.
    - by rewrite EqMsz.
    - elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - move=> *. rewrite EqMsz. do 12 f_equiv. by apply @hnth_ne.
    - move=> *. f_equiv=> i. rewrite /is_pad EqMsz.
      have Eqv': hnthe tyl i ≡{n}≡ hnthe tyl' i by apply @hnth_ne.
      repeat (eapply ty_size_ne || f_equiv)=>//. by rewrite Eqv'.
  Qed.

  Definition sum_ty {A B} (ty: type A) (ty': type B) : type (A + B) :=
    <{xsum_to_sum}> (xsum_ty +[ty; ty']).

  Global Instance sum_ty_ne {A B} : NonExpansive2 (@sum_ty A B).
  Proof.
    move=> ???????. rewrite /sum_ty. do 2 f_equiv. constructor; by [|constructor].
  Qed.

End sum.

Notation "Σ!" := xsum_ty : lrust_type_scope.
Notation "ty + ty'" := (sum_ty ty%T ty'%T) : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma xsum_nil_empty: (Σ! +[] ≡ <{absurd}> ∅)%T.
  Proof.
    constructor=>//; by [rewrite ![ty_own _]eq_unique|rewrite ![ty_shr _]eq_unique].
  Qed.

  Lemma xsum_lft_morphism {B As} (Tl: _ As) :
    HForall (λ _, TypeLftMorphism) Tl → TypeLftMorphism (λ (ty: _ B), Σ! (Tl +$ ty))%T.
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
      + rewrite /= !elctx_interp_app HE' HE -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    - right. exists (α' ⊓ α), (E' ++ E). split=> ?.
      + iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
      + by rewrite !elctx_interp_app HE HE'.
  Qed.

  Global Instance xsum_type_ne {A Bs} (T: _ A → _ Bs) :
    ListTypeNonExpansive T → TypeNonExpansive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]]. have EqMsz: ∀ty ty',
      ty_size ty = ty_size ty' → max_ty_size (Tl +$ ty) = max_ty_size (Tl +$ ty').
    { move=> *. elim All; [done|]=>/= ???? One _ ->. f_equal. by apply One. }
    split=>/=.
    - apply xsum_lft_morphism. eapply HForall_impl; [|done]. by move=> >[].
    - move=> *. f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All; [|apply _].
      rewrite !hnth_apply. do 9 f_equiv; [|by apply All]. do 3 f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All; [|apply _].
      rewrite /is_pad !hnth_apply. do 4 f_equiv; [|by apply All].
      do 8 f_equiv; [| |by apply EqMsz]; f_equiv; [f_equiv|]; by apply All.
  Qed.
  (* TODO : get rid of this duplication *)
  Global Instance xsum_type_contractive {A Bs} (T: _ A → _ Bs) :
    ListTypeContractive T → TypeContractive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]].
    have EqMsz: ∀ty ty', max_ty_size (Tl +$ ty) = max_ty_size (Tl +$ ty').
    { move=> *. elim All; [done|]=>/= ???? One _ ->. f_equal. by apply One. }
    split=>/=.
    - apply xsum_lft_morphism. eapply HForall_impl; [|done]. by move=> >[].
    - move=> *. f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All; [|apply _].
      rewrite !hnth_apply. do 9 f_equiv; [|by apply All]. do 3 f_equiv. by apply EqMsz.
    - move=> *. f_equiv=> i. apply (HForall_nth _ (const ∅) _ i) in All; [|apply _].
      rewrite /is_pad !hnth_apply. do 4 f_equiv; [|by apply All].
      do 8 f_equiv; [| |by apply EqMsz]; f_equiv; [f_equiv|]; by apply All.
  Qed.

  Global Instance xsum_copy {As} (tyl: _ As) : ListCopy tyl → Copy (Σ! tyl).
  Proof.
    move=> ?. have Copy: ∀i, Copy (hnthe tyl i).
    { move=> *. apply (HForall_nth (λ A, @Copy _ _ A)); by [apply _|]. }
    split; [apply _|]. move=>/= ?????? l ?? SubF. iIntros "#LFT".
    iDestruct 1 as (i d ->) "[Bor Shr]". iIntros "Na [Tok Tok']".
    iMod (frac_bor_acc with "LFT Bor Tok") as (q) "[>[Idx Pad] Close]";
    [solve_ndisj|]. iDestruct "Pad" as (vl') "[Pad %]".
    iMod (copy_shr_acc with "LFT Shr Na Tok'") as
      (q' vl) "(Na & Mt & #Own & Close')"; first done.
    { rewrite <-SubF, <-union_subseteq_r. apply shr_locsE_subseteq. lia. }
    iDestruct (na_own_acc with "Na") as "[$ Close'']".
    { apply difference_mono_l. trans (shr_locsE (l +ₗ 1) (max_ty_size tyl));
      [apply shr_locsE_subseteq; lia|set_solver+]. }
    case (Qp_lower_bound q q')=> [q''[?[?[->->]]]].
    iExists q'', (#i :: vl ++ vl').
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_app shift_loc_assoc
      -Nat.add_1_l Nat2Z.inj_add.
    iDestruct "Idx" as "[$ Idx]". iDestruct "Mt" as "[$ Mt]".
    iDestruct (ty_size_eq with "Own") as ">%Eq". rewrite Eq.
    iDestruct "Pad" as "[$ Pad]". iSplitR.
    { iIntros "!>!>". iExists i, d, vl, vl'. do 2 (iSplit; [done|]).
      iFrame "Own". rewrite /= app_length Eq. iPureIntro. by f_equal. }
    iIntros "!> Na (Idx' & Mt' & Pad')". iDestruct ("Close''" with "Na") as "Na".
    iMod ("Close'" with "Na [$Mt $Mt']") as "[$$]". iApply "Close".
    iFrame "Idx Idx'". iExists vl'. by iFrame.
  Qed.

  Global Instance xsum_send {As} (tyl: _ As) : ListSend tyl → Send (Σ! tyl).
  Proof. move=> Send ?*/=. do 11 f_equiv. by eapply HForall_nth in Send. Qed.
  Global Instance xsum_sync {As} (tyl: _ As) : ListSync tyl → Sync (Σ! tyl).
  Proof. move=> Sync ?*/=. do 6 f_equiv. by eapply HForall_nth in Sync. Qed.

  Lemma xsum_subtype {As Bs} E L (tyl: _ As) (tyl': _ Bs) fl :
    subtypel E L tyl tyl' fl → subtype E L (xsum_map fl) (Σ! tyl) (Σ! tyl').
  Proof.
    move=> Subs ?. iIntros "L".
    iAssert (□ (lft_contexts.elctx_interp E -∗ ⌜max_ty_size tyl =
      max_ty_size tyl'⌝))%I as "#Size".
    { iInduction Subs as [|?????????? Sub Subs] "IH"; [by iIntros "!>_"|].
      iDestruct (Sub with "L") as "#Sub". iDestruct ("IH" with "L") as "#IH'".
      iIntros "!> E /=". iDestruct ("Sub" with "E") as (->) "#_".
      by iDestruct ("IH'" with "E") as %->. }
    iAssert (□ (lft_contexts.elctx_interp E -∗ tyl_lft tyl' ⊑ tyl_lft tyl))%I as "#Lft".
    { iClear "Size". iInduction Subs as [|?????????? Sub Subs] "IH".
      { iIntros "!>_". by iApply lft_incl_refl. }
      iDestruct (Sub with "L") as "#Sub". iDestruct ("IH" with "L") as "#IH'".
      iIntros "!> E /=". iDestruct ("Sub" with "E") as (?) "#[?_]".
      iDestruct ("IH'" with "E") as "#?".
      rewrite !lft_intersect_list_app. by iApply lft_intersect_mono. }
    move/subtypel_llctx_nth in Subs. iDestruct (Subs with "L") as "#Subs".
    iIntros "!> #E". iDestruct ("Size" with "E") as "%Size".
    iDestruct ("Lft" with "E") as "?". iDestruct ("Subs" with "E") as "Incl".
    iSplit; simpl; [iPureIntro; by f_equal|]. iSplit; [done|].
    iSplit; iModIntro; iIntros "*".
    - iDestruct 1 as (i vπ' vl' vl'' ->->->) "Own".
      iExists i, (p2nth id fl i ∘ vπ'), vl', vl''. rewrite Size. do 3 (iSplit; [done|]).
      iDestruct ("Incl" $! i) as (_) "[_[InOwn _]]". by iApply "InOwn".
    - iDestruct 1 as (i vπ' ->) "[Bor Shr]". iExists i, (p2nth id fl i ∘ vπ').
      rewrite /is_pad Size. iDestruct ("Incl" $! i) as (->) "[_[_ InShr]]".
      do 2 (iSplit; [done|]). by iApply "InShr".
  Qed.

  Lemma xsum_eqtype {As Bs} E L (tyl: _ As) (tyl': _ Bs) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (xsum_map fl) (xsum_map gl) (Σ! tyl) (Σ! tyl').
  Proof.
    move=> /eqtypel_subtypel[??]. by split; apply xsum_subtype.
  Qed.

  Lemma sum_subtype {A B A' B'} E L (f: A → A') (g: B → B') ty1 ty2 ty1' ty2' :
    subtype E L f ty1 ty1' → subtype E L g ty2 ty2' →
    subtype E L (sum_map f g) (ty1 + ty2) (ty1' + ty2').
  Proof.
    move=> ??. eapply subtype_eq. { apply mod_ty_subtype; [apply _|].
    apply xsum_subtype. apply subtypel_cons; [done|]. apply subtypel_cons; [done|].
    apply subtypel_nil. } { fun_ext. by case. }
  Qed.

  Lemma sum_eqtype {A B A' B'} E L (f: A → A') f' (g: B → B') g' ty1 ty2 ty1' ty2' :
    eqtype E L f f' ty1 ty1' → eqtype E L g g' ty2 ty2' →
    eqtype E L (sum_map f g) (sum_map f' g') (ty1 + ty2) (ty1' + ty2').
  Proof. move=> [??][??]. split; by apply sum_subtype. Qed.

End typing.

Global Hint Resolve xsum_subtype xsum_eqtype sum_subtype sum_eqtype: lrust_typing.
