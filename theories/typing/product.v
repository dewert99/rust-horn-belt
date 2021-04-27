From lrust.typing Require Export type.
From lrust.typing Require Import uninit mod_ty.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅 ℭ: syn_type) (𝔄l 𝔅l: tlist syn_type).

Section product.
  Context `{!typeG Σ}.

  Lemma split_prod_mt {𝔄 𝔅} (vπ: _ → 𝔄) d (vπ': _ → 𝔅) d' tid ty ty' q l :
    (l ↦∗{q}: λ vl, ∃wl wl', ⌜vl = wl ++ wl'⌝ ∗
      ty.(ty_own) vπ d tid wl ∗ ty'.(ty_own) vπ' d' tid wl')%I ⊣⊢
    l ↦∗{q}: ty.(ty_own) vπ d tid ∗
      (l +ₗ ty.(ty_size)) ↦∗{q}: ty'.(ty_own) vπ' d' tid.
  Proof.
    iSplit.
    - iIntros "(%& Mt &%&%&->& Own & Own')". rewrite heap_mapsto_vec_app.
      iDestruct "Mt" as "[Mt Mt']". iDestruct (ty_size_eq with "Own") as %->.
      iSplitL "Mt Own"; iExists _; iFrame.
    - iIntros "[(%wl & Mt & Own) (%wl' & Mt' & Own')]". iExists (wl ++ wl').
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "Own") as %->.
      iFrame "Mt Mt'". iExists wl, wl'. by iFrame.
  Qed.

  Program Definition prod_ty {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) : type (𝔄 * 𝔅) := {|
    ty_size := ty.(ty_size) + ty'.(ty_size);
    ty_lfts := ty.(ty_lfts) ++ ty'.(ty_lfts);  ty_E := ty.(ty_E) ++ ty'.(ty_E);
    ty_own vπ d tid vl := ∃wl wl', ⌜vl = wl ++ wl'⌝ ∗
      ty.(ty_own) (fst ∘ vπ) d tid wl ∗ ty'.(ty_own) (snd ∘ vπ) d tid wl';
    ty_shr vπ d κ tid l := ty.(ty_shr) (fst ∘ vπ) d κ tid l ∗
      ty'.(ty_shr) (snd ∘ vπ) d κ tid (l +ₗ ty.(ty_size))
  |}%I.
  Next Obligation.
    iIntros "* (%&%&->& H)". rewrite app_length !ty_size_eq. by iDestruct "H" as "[->->]".
  Qed.
  Next Obligation.
    iIntros "*% (%&%&->& Own &?)". iExists wl, wl'. iSplit; [done|].
    by iSplitL "Own"; iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    iIntros "*%[??]". iSplit; by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    iIntros "* In [??]". iSplit; by iApply (ty_shr_lft_mono with "In").
  Qed.
  Next Obligation.
    move=> */=. iIntros "#LFT #? Own [Tok Tok']". rewrite split_prod_mt.
    iMod (bor_sep with "LFT Own") as "[Own Own']"; first done.
    iMod (ty_share with "LFT [] Own Tok") as "Own"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iMod (ty_share with "LFT [] Own' Tok'") as "Own'"; first solve_ndisj.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iDestruct (step_fupdN_combine with "Own Own'") as "Own".
    iApply (step_fupdN_wand with "Own"). by iIntros "!> [>[$$] >[$$]]".
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #? (%wl & %wl' &->& Own & Own') [Tok Tok']".
    iDestruct (ty_own_proph with "LFT [] Own Tok") as ">Close"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iDestruct (ty_own_proph with "LFT [] Own' Tok'") as ">Close'"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iDestruct (step_fupdN_combine with "Close Close'") as "Close".
    iApply (step_fupdN_wand with "Close"). iIntros "!> [Close Close']".
    iMod "Close" as (ξl q ?) "[PTok Close]". iMod "Close'" as (ξl' q' ?) "[PTok' Close']".
    iDestruct (proph_tok_combine with "PTok PTok'") as (q0) "[PTok ToPTok]".
    iExists (ξl ++ ξl'), q0. iModIntro. iSplit. { iPureIntro. by apply proph_dep_pair. }
    iFrame "PTok". iIntros "PTok". iDestruct ("ToPTok" with "PTok") as "[PTok PTok']".
    iMod ("Close" with "PTok") as "[?$]". iMod ("Close'" with "PTok'") as "[?$]".
    iModIntro. iExists wl, wl'. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #In #? [Shr Shr'] [Tok Tok']".
    iDestruct (ty_shr_proph with "LFT In [] Shr Tok") as "> Close"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iDestruct (ty_shr_proph with "LFT In [] Shr' Tok'") as "> Close'"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iIntros "!>!>". iMod (step_fupdN_combine with "Close Close'") as ">Close".
    iApply (step_fupdN_wand with "Close"). iIntros "!> [Close Close']".
    iMod "Close" as (ξl q ?) "[PTok Close]". iMod "Close'" as (ξl' q' ?) "[PTok' Close']".
    iDestruct (proph_tok_combine with "PTok PTok'") as (q0) "[PTok ToPTok]".
    iExists (ξl ++ ξl'), q0. iModIntro. iSplit. { iPureIntro. by apply proph_dep_pair. }
    iFrame "PTok". iIntros "PTok". iDestruct ("ToPTok" with "PTok") as "[PTok PTok']".
    iMod ("Close" with "PTok") as "[$$]". by iMod ("Close'" with "PTok'") as "[$$]".
  Qed.

  Global Instance prod_ty_ne {𝔄 𝔅} : NonExpansive2 (@prod_ty 𝔄 𝔅).
  Proof. solve_ne_type. Qed.

  Definition to_cons_prod' {𝔄 𝔄l}
    : (𝔄 * Π! 𝔄l)%ST → (Π! (𝔄 ^:: 𝔄l))%ST := to_cons_prod.

  Fixpoint xprod_ty {𝔄l} (tyl: typel 𝔄l) : type (Π! 𝔄l) :=
    match tyl with +[] => <{unique}> unit_ty |
      ty +:: tyl' => <{to_cons_prod'}> (prod_ty ty (xprod_ty tyl')) end.

  Global Instance product_ne {𝔄l} : NonExpansive (@xprod_ty 𝔄l).
  Proof. move=> ???. elim; [done|]=> */=. by do 2 f_equiv. Qed.

End product.

Notation "ty * ty'" := (prod_ty ty%T ty'%T) : lrust_type_scope.
Notation "Π!" := xprod_ty : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance prod_lft_morph {𝔄 𝔅 ℭ} (T: _ 𝔄 → _ 𝔅) (T': _ → _ ℭ):
    TypeLftMorphism T → TypeLftMorphism T' → TypeLftMorphism (λ ty, T ty * T' ty)%T.
  Proof.
    case=> [α βs E Hα HE|α E Hα HE]; case=> [α' βs' E' Hα' HE'|α' E' Hα' HE'].
    - apply (type_lft_morph_add _ (α ⊓ α') (βs ++ βs') (E ++ E'))=> ty.
      + rewrite lft_intersect_list_app. iApply lft_equiv_trans.
        { iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα']. }
        rewrite -!assoc (comm (⊓) (ty_lft ty) (α' ⊓ _)) -!assoc.
        repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
        iApply lft_intersect_equiv_idemp.
      + rewrite /= !elctx_interp_app HE HE' big_sepL_app -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morph_add _ (α ⊓ α') βs (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc (comm (⊓) α' (ty_lft ty)) assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + rewrite /= !elctx_interp_app HE HE' -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morph_add _ (α ⊓ α') βs' (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite /= !elctx_interp_app HE HE' -!assoc.
    - apply (type_lft_morph_const _ (α ⊓ α') (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite /= !elctx_interp_app HE HE'.
  Qed.

  Global Instance prod_type_ne {𝔄 𝔅 ℭ} (T: _ 𝔄 → _ 𝔅) (T': _ → _ ℭ) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (λ ty, T ty * T' ty)%T.
  Proof. move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_ne_ty_size.
    - move=> *. do 6 f_equiv; by apply type_ne_ty_own.
    - move=> ? ty ty' *. rewrite (type_ne_ty_size (T:=T) ty ty'); [|done].
      f_equiv; by apply type_ne_ty_shr.
  Qed.
  (* TODO : find a way to avoid this duplication. *)
  Global Instance prod_type_contr {𝔄 𝔅 ℭ} (T: _ 𝔄 → _ 𝔅) (T': _ → _ ℭ) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty * T' ty)%T.
  Proof. move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_contr_ty_size.
    - move=> *. do 6 f_equiv; by apply type_contr_ty_own.
    - move=> ? ty ty' *. rewrite (type_contr_ty_size (T:=T) ty ty').
      f_equiv; by apply type_contr_ty_shr.
  Qed.

  Global Instance xprod_type_ne {𝔄 𝔅l} (T: _ 𝔄 → _ 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (Π! ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. have ->: (Π! ∘ ((T +:: Tl) +$.) =
      <{to_cons_prod'}> ∘ (λ ty, (T ty * Π! (Tl +$ ty))))%T by done.
    apply type_ne_ne_compose; [apply mod_ty_type_ne|]. by apply prod_type_ne.
  Qed.
  Global Instance xprod_type_contr {𝔄 𝔅l} (T: _ 𝔄 → _ 𝔅l) :
    ListTypeContractive T → TypeContractive (Π! ∘ T)%T.
  Proof.
    move=> [?[->All]]. clear T. elim All. { rewrite /happly /compose. apply _. }
    move=> ?? T Tl ???. have ->: (Π! ∘ ((T +:: Tl) +$.) =
      <{to_cons_prod'}> ∘ (λ ty, (T ty * Π! (Tl +$ ty))))%T by done.
    apply type_contr_compose_left; [apply mod_ty_type_ne|]. by apply prod_type_contr.
  Qed.

  Global Instance prod_copy {𝔄 𝔅} (ty: _ 𝔄) (ty': _ 𝔅) :
    Copy ty → Copy ty' → Copy (ty * ty').
  Proof.
    move=> ??. split; [by apply _|]=>/= > ? HF. iIntros "#LFT [Shr Shr'] Na [Tok Tok']".
    iMod (copy_shr_acc with "LFT Shr Na Tok") as (q wl) "(Na & Mt & #Own & Close)";
    first done. { rewrite <-HF. apply shr_locsE_subseteq=>/=. lia. }
    iMod (copy_shr_acc with "LFT Shr' Na Tok'") as (q' wl') "(Na & Mt' & #Own' & Close')";
    first done. { apply subseteq_difference_r. { symmetry. apply shr_locsE_disj. }
      move: HF. rewrite -plus_assoc shr_locsE_shift. set_solver. }
    iDestruct (na_own_acc with "Na") as "[$ ToNa]".
    { rewrite shr_locsE_shift. set_solver. }
    case (Qp_lower_bound q q')=> [q''[?[?[->->]]]].
    iExists q'', (wl ++ wl'). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "Own") as ">->".
    iDestruct "Mt" as "[$ Mtr]". iDestruct "Mt'" as "[$ Mtr']".
    iSplitR. { iIntros "!>!>". iExists wl, wl'. iSplit; by [|iSplit]. }
    iIntros "!> Na [Mt Mt']". iDestruct ("ToNa" with "Na") as "Na".
    iMod ("Close'" with "Na [$Mt' $Mtr']") as "[Na $]".
    iApply ("Close" with "Na [$Mt $Mtr]").
  Qed.

  Global Instance prod_send {𝔄 𝔅} (ty: _ 𝔄) (ty': _ 𝔅) :
    Send ty → Send ty' → Send (ty * ty').
  Proof. move=> >/=. by do 6 f_equiv. Qed.
  Global Instance prod_sync {𝔄 𝔅} (ty: _ 𝔄) (ty': _ 𝔅) :
    Sync ty → Sync ty' → Sync (ty * ty').
  Proof. move=> >/=. by f_equiv. Qed.

  Global Instance xprod_copy {𝔄l} (tyl: _ 𝔄l) : ListCopy tyl → Copy (Π! tyl).
  Proof. elim; apply _. Qed.
  Global Instance xprod_send {𝔄l} (tyl: _ 𝔄l) : ListSend tyl → Send (Π! tyl).
  Proof. elim; apply _. Qed.
  Global Instance xprod_sync {𝔄l} (tyl: _ 𝔄l) : ListSync tyl → Sync (Π! tyl).
  Proof. elim; apply _. Qed.

  Lemma prod_subtype {𝔄 𝔅 𝔄' 𝔅'} E L (f: 𝔄 → 𝔄') (g: 𝔅 → 𝔅') ty1 ty2 ty1' ty2' :
    subtype E L ty1 ty1' f → subtype E L ty2 ty2' g →
    subtype E L (ty1 * ty2) (ty1' * ty2') (prod_map f g).
  Proof.
    move=> Sub Sub' ?. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iDestruct (Sub' with "L") as "#Sub'". iIntros "!> #E".
    iDestruct ("Sub" with "E") as (Eq) "(#InLft & #InOwn & #InShr)".
    iDestruct ("Sub'" with "E") as (?) "(#InLft' & #InOwn' & #InShr')".
    iSplit=>/=. { iPureIntro. by f_equal. } iSplit.
    { rewrite !lft_intersect_list_app. by iApply lft_intersect_mono. }
    iSplit; iModIntro.
    - iIntros "* (%wl & %wl' &->& Own & Own')". iExists wl, wl'.
      iSplit; [done|]. iSplitL "Own"; by [iApply "InOwn"|iApply "InOwn'"].
    - iIntros "* #[??]". rewrite Eq. iSplit; by [iApply "InShr"|iApply "InShr'"].
  Qed.
  Lemma prod_eqtype {𝔄 𝔅 𝔄' 𝔅'} E L (f: 𝔄 → 𝔄') f' (g: 𝔅 → 𝔅') g' ty1 ty2 ty1' ty2' :
    eqtype E L ty1 ty1' f f' → eqtype E L ty2 ty2' g g' →
    eqtype E L (ty1 * ty2) (ty1' * ty2') (prod_map f g) (prod_map f' g').
  Proof. move=> [??][??]. split; by apply prod_subtype. Qed.

  Lemma xprod_subtype {𝔄l 𝔅l} E L (tyl: _ 𝔄l) (tyl': _ 𝔅l) fl :
    subtypel E L tyl tyl' fl → subtype E L (Π! tyl) (Π! tyl') (plist_map fl).
  Proof.
    move=> Subs. elim Subs; [solve_typing|]=> *. eapply subtype_eq.
    { apply mod_ty_subtype; [apply _|]. by apply prod_subtype. } fun_ext. by case.
  Qed.

  Lemma xprod_eqtype {𝔄l 𝔅l} E L (tyl: _ 𝔄l) (tyl': _ 𝔅l) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (Π! tyl) (Π! tyl') (plist_map fl) (plist_map gl).
  Proof.
    move=> /eqtypel_subtypel[??]. by split; apply xprod_subtype.
  Qed.

  Lemma prod_ty_assoc {𝔄 𝔅 ℭ} E L (ty1: _ 𝔄) (ty2: _ 𝔅) (ty3: _ ℭ) :
    eqtype E L (ty1 * (ty2 * ty3)) ((ty1 * ty2) * ty3) prod_assoc prod_assoc'.
  Proof.
    have Eq: ∀vπ: proph (𝔄 * (𝔅 * ℭ)),
      fst ∘ (fst ∘ (prod_assoc ∘ vπ)) = fst ∘ vπ ∧
      snd ∘ (fst ∘ (prod_assoc ∘ vπ)) = fst ∘ (snd ∘ vπ) ∧
      snd ∘ (prod_assoc ∘ vπ) = snd ∘ (snd ∘ vπ).
    { move=> vπ. split; [|split]; fun_ext=>/= xyz; by case (vπ xyz)=> [?[??]]. }
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=". iSplit; [iPureIntro; lia|].
    iSplit; [rewrite (assoc (++)); by iApply lft_equiv_refl|].
    iSplit; iIntros "!>" (vπ) "*"; move: (Eq vπ)=> [->[->->]]; [iSplit|].
    - iIntros "(%wl1 & %&->&?& %wl2 & %wl3 &->&?& Own3)". iExists (wl1 ++ wl2), wl3.
      iSplit; [by rewrite assoc|]. iFrame "Own3". iExists wl1, wl2. by iFrame.
    - iIntros "(%& %wl3 &->& (%wl1 & %wl2 &->& Own1 &?) &?)". iExists wl1, (wl2 ++ wl3).
      iSplit; [by rewrite assoc|]. iFrame "Own1". iExists wl2, wl3. by iFrame.
    - rewrite -assoc shift_loc_assoc_nat. by iApply (bi.iff_refl True%I).
  Qed.

  Lemma prod_ty_left_id {𝔄} E L (ty: _ 𝔄) :
    eqtype E L (() * ty) ty prod_left_id prod_left_id'.
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [by iApply lft_equiv_refl|].
    have Eq: ∀vπ: proph (_ * 𝔄), prod_left_id ∘ vπ = snd ∘ vπ.
    { move=> vπ. fun_ext=> π. simpl. by case (vπ π)=> [[]?]. }
    iSplit; iIntros "!> *"; rewrite Eq.
    - iSplit; [by iDestruct 1 as ([|]?->?) "?"|]. iIntros. iExists [], _. by iFrame.
    - rewrite left_id shift_loc_0. by iApply (bi.iff_refl True%I).
  Qed.

  Lemma prod_ty_right_id {𝔄} E L (ty: _ 𝔄) :
    eqtype E L (ty * ()) ty prod_right_id prod_right_id'.
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_/=".
    rewrite !right_id. iSplit; [done|]. iSplit; [by iApply lft_equiv_refl|].
    have Eq: ∀vπ: proph (𝔄 * _), prod_right_id ∘ vπ = fst ∘ vπ.
    { move=> vπ. fun_ext=> π. simpl. by case (vπ π)=> [?[]]. }
    iSplit; iIntros "!>*"; rewrite Eq; [iSplit|].
    - iDestruct 1 as (?[|]->) "[?%]"; by [rewrite right_id|].
    - iIntros. iExists _, []. rewrite right_id. by iFrame.
    - rewrite right_id. by iApply (bi.iff_refl True%I).
  Qed.

  Lemma xprod_ty_app_prod {𝔄l 𝔅l} E L (tyl: _ 𝔄l) (tyl': _ 𝔅l) :
    eqtype E L (Π! (tyl h++ tyl')) (Π! tyl * Π! tyl') psep (curry papp).
  Proof. elim: tyl=> [|> Eq].
    - eapply eqtype_eq. { eapply eqtype_trans; [apply eqtype_symm;
      apply prod_ty_left_id|]. apply prod_eqtype; [|solve_typing].
      apply mod_ty_inout, _. } { done. } { done. }
    - eapply eqtype_eq. { eapply eqtype_trans; [by apply mod_ty_outin, _|].
      eapply eqtype_trans. { eapply prod_eqtype; [solve_typing|apply Eq]. }
      eapply eqtype_trans; [by apply prod_ty_assoc|]. apply prod_eqtype;
      [apply mod_ty_inout, _|solve_typing]. } { fun_ext. by case. }
      { fun_ext. by case=> [[??]?]. }
  Qed.

  Lemma uninit_plus_prod E L m n :
    eqtype E L (↯ (m + n)) (↯ m * ↯ n) unique unique.
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros "*_!>_". iSplit; [done|].
    iSplit; [iApply lft_equiv_refl|]. iSplit; iIntros "!>*!%"; [|done]. split.
    - move: vl. elim m; [by exists [], vl|]=>/= ? IH [|v?]// [=/IH[wl[wl'[->[??]]]]].
      exists (v :: wl), wl'. split; [done|]. split; [|done]=>/=. by f_equal.
    - move=> [?[?[->[??]]]]. rewrite app_length. by f_equal.
  Qed.

  Lemma prod_outlv_E {𝔄 𝔅} (ty: _ 𝔄) (ty': _ 𝔅) κ :
    ty_outlv_E (ty * ty') κ = ty_outlv_E ty κ ++ ty_outlv_E ty' κ.
  Proof. by rewrite /ty_outlv_E /= fmap_app. Qed.

  Lemma xprod_outlv_E_elctx_sat {𝔄l} E L (tyl: _ 𝔄l) κ:
    elctx_sat E L (tyl_outlv_E tyl κ) → elctx_sat E L (ty_outlv_E (Π! tyl) κ).
  Proof.
    move=> ?. eapply eq_ind; [done|]. rewrite /ty_outlv_E /=.
    elim tyl=>/= [|> IH]; [done|]. by rewrite fmap_app -IH.
  Qed.

End typing.

Global Hint Resolve prod_subtype prod_eqtype xprod_subtype xprod_eqtype
  xprod_outlv_E_elctx_sat : lrust_typing.
