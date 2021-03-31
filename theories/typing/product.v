Require Import FunctionalExtensionality Equality.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import list numbers.
From lrust.util Require Import basic update types.
From lrust.typing Require Import lft_contexts mod_ty.
From lrust.typing Require Export type.

Set Default Proof Using "Type".

Section product.
  Context `{!typeG Σ}.

  Program Definition unit: type unit := {|
    ty_size := 0;  ty_lfts := [];  ty_E := [];
    ty_own _ _ vl := ⌜vl = []⌝%I;  ty_shr _ _ _ _ := True%I
  |}.
  Next Obligation. iIntros. by subst. Qed. Next Obligation. by iIntros. Qed.
  Next Obligation. by iIntros. Qed. Next Obligation. by iIntros. Qed.
  Next Obligation. iIntros. iApply step_fupdN_intro; [done|]. by iFrame. Qed.
  Next Obligation.
    iIntros. iIntros. iApply step_fupdN_intro; [done|]. iIntros "!>!>!>".
    iExists [], 1%Qp=>/=. iSplit; [iPureIntro; by apply proph_dep_unit|]. by iFrame.
  Qed.
  Next Obligation.
    iIntros. iIntros. iApply step_fupdN_intro; [done|]. iIntros "!>!>!>!>!>".
    iExists [], 1%Qp=>/=. iSplit; [iPureIntro; by apply proph_dep_unit|]. by iFrame.
  Qed.

  Global Instance unit_copy: Copy unit.
  Proof.
    split; [apply _|]. move=> */=. iIntros "_ _ Na $". iExists 1%Qp, []. iModIntro.
    iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [solve_ndisj|].
    rewrite heap_mapsto_vec_nil. do 2 (iSplit; [done|]). iIntros "?_!>". by iApply "ToNa".
  Qed.
  Global Instance unit_send: Send unit. Proof. done. Qed.
  Global Instance unit_sync: Sync unit. Proof. done. Qed.

  Lemma split_prod_mt {A B} (vπd: _ A) (vπd': _ B) tid ty ty' q l :
    (l ↦∗{q}: λ vl, ∃wl wl', ⌜vl = wl ++ wl'⌝ ∗
      ty.(ty_own) vπd tid wl ∗ ty'.(ty_own) vπd' tid wl')%I ⊣⊢
    l ↦∗{q}: ty.(ty_own) vπd tid ∗
      (l +ₗ ty.(ty_size)) ↦∗{q}: ty'.(ty_own) vπd' tid.
  Proof.
    iSplit.
    - iDestruct 1 as (?) "[Mt Own]". iDestruct "Own" as (??->) "[Own Own']".
      rewrite heap_mapsto_vec_app. iDestruct "Mt" as "[Mt Mt']".
      iDestruct (ty_size_eq with "Own") as %->.
      iSplitL "Mt Own"; iExists _; iFrame.
    - iDestruct 1 as "[Own Own']". iDestruct "Own" as (wl) "[Mt Own]".
      iDestruct "Own'" as (wl') "[Mt' Own']". iExists (wl ++ wl').
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "Own") as %->.
      iFrame "Mt Mt'". iExists wl, wl'. by iFrame.
  Qed.

  Program Definition product2 {A B} (ty: type A) (ty': type B) : type (A * B) :=
    {| ty_size := ty.(ty_size) + ty'.(ty_size);
       ty_lfts := ty.(ty_lfts) ++ ty'.(ty_lfts);  ty_E := ty.(ty_E) ++ ty'.(ty_E);
       ty_own vπd tid vl := (∃ wl wl', ⌜vl = wl ++ wl'⌝ ∗
        ty.(ty_own) (fst ∘ vπd.1, vπd.2) tid wl ∗ ty'.(ty_own) (snd ∘ vπd.1, vπd.2) tid wl')%I;
       ty_shr vπd κ tid l := (ty.(ty_shr) (fst ∘ vπd.1, vπd.2) κ tid l ∗
          ty'.(ty_shr) (snd ∘ vπd.1, vπd.2) κ tid (l +ₗ ty.(ty_size)))%I |}.
  Next Obligation.
    move=> */=. iDestruct 1 as (??->) "H". rewrite app_length !ty_size_eq.
    by iDestruct "H" as "[->->]".
  Qed.
  Next Obligation.
    move=> *. iDestruct 1 as (wl wl' ->) "[Own Own']". iExists wl, wl'.
    iSplit; [done|]. by iSplitL "Own"; iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "[??]". iSplit; by iApply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    move=> *. iIntros "In [??]". iSplit; by iApply (ty_shr_lft_mono with "In").
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
    move=> *. iIntros "#LFT #?". iDestruct 1 as (wl wl' ->) "[Own Own']".
    iIntros "[Tok Tok']".
    iDestruct (ty_own_proph with "LFT [] Own Tok") as ">Close"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iDestruct (ty_own_proph with "LFT [] Own' Tok'") as ">Close'"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iDestruct (step_fupdN_combine with "Close Close'") as "Close".
    iApply (step_fupdN_wand with "Close"). iIntros "!> [Close Close']".
    iMod "Close" as (ξs q ?) "[PTok Close]". iMod "Close'" as (ξs' q' ?) "[PTok' Close']".
    iDestruct (proph_tok_combine with "PTok PTok'") as (q0) "[PTok PrePTok]".
    iExists (ξs ++ ξs'), q0. iModIntro. iSplit. { iPureIntro. by apply proph_dep_pair. }
    iFrame "PTok". iIntros "PTok". iDestruct ("PrePTok" with "PTok") as "[PTok PTok']".
    iMod ("Close" with "PTok") as "[?$]". iMod ("Close'" with "PTok'") as "[?$]".
    iModIntro. iExists wl, wl'. iSplit; [done|]. iFrame.
  Qed.
  Next Obligation.
    move=> *. iIntros "#LFT #In #?". iDestruct 1 as "[Shr Shr']". iIntros "[Tok Tok']".
    iDestruct (ty_shr_proph with "LFT In [] Shr Tok") as "> Close"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iDestruct (ty_shr_proph with "LFT In [] Shr' Tok'") as "> Close'"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iIntros "!>!>". iMod (step_fupdN_combine with "Close Close'") as ">Close".
    iApply (step_fupdN_wand with "Close"). iIntros "!> [Close Close']".
    iMod "Close" as (ξs q ?) "[PTok Close]". iMod "Close'" as (ξs' q' ?) "[PTok' Close']".
    iDestruct (proph_tok_combine with "PTok PTok'") as (q0) "[PTok PrePTok]".
    iExists (ξs ++ ξs'), q0. iModIntro. iSplit. { iPureIntro. by apply proph_dep_pair. }
    iFrame "PTok". iIntros "PTok". iDestruct ("PrePTok" with "PTok") as "[PTok PTok']".
    iMod ("Close" with "PTok") as "[$$]". by iMod ("Close'" with "PTok'") as "[$$]".
  Qed.

  Global Instance product2_ne {A B} : NonExpansive2 (@product2 A B).
  Proof. solve_ne_type. Qed.

  Definition nil_unit: type :1 := mod_ty (λ _, -[]) unit.

  Definition cons_product2 {A B} (ty: type A) (ty': type B)
    : type (A :* B) := mod_ty pair_to_cons_pair (product2 ty ty').

  Global Instance cons_product2_ne {A B} : NonExpansive2 (@cons_product2 A B).
  Proof. move=> ???????. rewrite /cons_product2. by do 2 f_equiv. Qed.

  Fixpoint product {As} (tyl: typel As) : type (xprod As) :=
    match tyl with +[] => nil_unit | ty +:: tyl' => cons_product2 ty (product tyl') end.

  Global Instance product_ne {As} : NonExpansive (@product As).
  Proof. move=> ???. elim; [done|]=> */=. by f_equiv. Qed.

End product.

Notation "ty * ty'" := (product2 ty%T ty'%T) : lrust_type_scope.
Notation ":1" := nil_unit : lrust_type_scope.
Notation "ty :* ty'" := (cons_product2 ty%T ty'%T) : lrust_type_scope.
Notation Π := product.

Section typing.
  Context `{!typeG Σ}.

  Global Instance product2_lft_morphism {A B C} (T: _ A → _ B) (T' : _ → _ C):
    TypeLftMorphism T → TypeLftMorphism T' →
    TypeLftMorphism (λ ty, product2 (T ty) (T' ty)).
  Proof.
    case=> [α βs E Hα HE|α E Hα HE]; case=> [α' βs' E' Hα' HE'|α' E' Hα' HE'].
    - apply (type_lft_morphism_add _ (α ⊓ α') (βs ++ βs') (E ++ E'))=> ty.
      + rewrite lft_intersect_list_app. iApply lft_equiv_trans.
        { iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα']. }
        rewrite -!assoc (comm (⊓) (ty_lft ty) (α' ⊓ _)) -!assoc.
        repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
        iApply lft_intersect_equiv_idemp.
      + rewrite /= !elctx_interp_app HE HE' big_sepL_app -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc (comm (⊓) α' (ty_lft ty)) assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + rewrite /= !elctx_interp_app HE HE' -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs' (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite /= !elctx_interp_app HE HE' -!assoc.
    - apply (type_lft_morphism_const _ (α ⊓ α') (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite /= !elctx_interp_app HE HE'.
  Qed.

  Global Instance product2_type_ne {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (λ ty, T ty * T' ty)%T.
  Proof. move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_non_expansive_ty_size.
    - move=> *. do 6 f_equiv; by apply type_non_expansive_ty_own.
    - move=> ? ty ty' *. rewrite (type_non_expansive_ty_size (T:=T) ty ty'); [|done].
      f_equiv; by apply type_non_expansive_ty_shr.
  Qed.
  (* TODO : find a way to avoid this duplication. *)
  Global Instance product2_type_contractive {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty * T' ty)%T.
  Proof. move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_contractive_ty_size.
    - move=> *. do 6 f_equiv; by apply type_contractive_ty_own.
    - move=> ? ty ty' *. rewrite (type_contractive_ty_size (T:=T) ty ty').
      f_equiv; by apply type_contractive_ty_shr.
  Qed.

  Global Instance cons_product2_type_ne {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (λ ty, T ty :* T' ty)%T.
  Proof.
    have ->: (λ ty, T ty :* T' ty)%T =
      mod_ty pair_to_cons_pair ∘ (λ ty, T ty * T' ty)%T by done.
    move=> ??. apply type_ne_ne_compose; apply _.
  Qed.
  Global Instance cons_product2_type_contractive {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty :* T' ty)%T.
  Proof.
    have ->: (λ ty, T ty :* T' ty)%T =
      mod_ty pair_to_cons_pair ∘ (λ ty, T ty * T' ty)%T by done.
    move=> ??. apply type_contractive_compose_left; apply _.
  Qed.

  Global Instance product_type_ne {A Bs} (T: _ A → _ Bs) :
    TypeListNonExpansive T → TypeNonExpansive (Π ∘ T).
  Proof.
    move=> [Tl [Eq All]].
    have ->: Π ∘ T = λ ty, Π ((λ _ (T': _ → _), T' ty) +<$>+ Tl).
    { extensionality ty. by rewrite /= Eq. } clear Eq T.
    dependent induction All=>/=; by [apply _|apply cons_product2_type_ne].
  Qed.
  Global Instance product_type_ne_cont {A Bs} (T: _ A → _ Bs) :
    TypeListContractive T → TypeContractive (Π ∘ T).
  Proof.
    move=> [Tl [Eq All]].
    have ->: Π ∘ T = λ ty, Π ((λ _ (T': _ → _), T' ty) +<$>+ Tl).
    { extensionality ty. by rewrite /= Eq. } clear Eq T.
    dependent induction All=>/=; by [apply _|apply cons_product2_type_contractive].
  Qed.

  Global Instance product2_copy {A B} (ty: _ A) (ty': _ B) :
    Copy ty → Copy ty' → Copy (ty * ty').
  Proof.
    move=> ??. split; [by apply _|]=>/= > ? HF. iIntros "#LFT [Shr Shr'] Na [Tok Tok']".
    iMod (copy_shr_acc with "LFT Shr Na Tok") as (q wl) "[Na[Mt[#Own Close]]]";
    first done. { rewrite <-HF. apply shr_locsE_subseteq=>/=. lia. }
    iMod (copy_shr_acc with "LFT Shr' Na Tok'") as (q' wl') "[Na[Mt'[#Own' Close']]]";
    first done. { apply subseteq_difference_r. { symmetry. apply shr_locsE_disj. }
      move: HF. rewrite -plus_assoc shr_locsE_shift. set_solver. }
    iDestruct (na_own_acc with "Na") as "[$ PreNa]".
    { rewrite shr_locsE_shift. set_solver. }
    case (Qp_lower_bound q q')=> [qq[?[?[->->]]]].
    iExists qq, (wl ++ wl'). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "Own") as ">->".
    iDestruct "Mt" as "[$ Mtr]". iDestruct "Mt'" as "[$ Mtr']".
    iSplitR. { iIntros "!>!>". iExists wl, wl'. iSplit; by [|iSplit]. }
    iIntros "!> Na [Mt Mt']". iDestruct ("PreNa" with "Na") as "Na".
    iMod ("Close'" with "Na [$Mt' $Mtr']") as "[Na $]".
    iApply ("Close" with "Na [$Mt $Mtr]").
  Qed.

  Global Instance product2_send {A B} (ty: _ A) (ty': _ B) :
    Send ty → Send ty' → Send (ty * ty').
  Proof.
    move=> *?*. iDestruct 1 as (wl wl' ->) "[Own Own']".
    iExists wl, wl'. iSplit; [done|]. iSplitL "Own"; by iApply @send_change_tid.
  Qed.
  Global Instance product2_sync {A B} (ty: _ A) (ty': _ B) :
    Sync ty → Sync ty' → Sync (ty * ty').
  Proof.
    move=> *?*. iIntros "[#? #?]". iSplit; by iApply @sync_change_tid.
  Qed.

  Global Instance product_copy {As} (tyl: _ As) : ListCopy tyl → Copy (Π tyl).
  Proof. elim; apply _. Qed.
  Global Instance product_send {As} (tyl: _ As) : ListSend tyl → Send (Π tyl).
  Proof. elim; apply _. Qed.
  Global Instance product_sync {As} (tyl: _ As) : ListSync tyl → Sync (Π tyl).
  Proof. elim; apply _. Qed.

  Lemma product2_subtype {A B A' B'} E L (f: A → A') (g: B → B') ty1 ty2 ty1' ty2' :
    subtype E L f ty1 ty1' → subtype E L g ty2 ty2' →
    subtype E L (pair_map f g) (ty1 * ty2) (ty1' * ty2').
  Proof.
    move=> Sub Sub'. iIntros (?) "L". iDestruct (Sub with "L") as "#Sub".
    iDestruct (Sub' with "L") as "#Sub'". iIntros "!> #E".
    iDestruct ("Sub" with "E") as (Eq) "[#InLft[#InOwn #InShr]]".
    iDestruct ("Sub'" with "E") as (?) "[#InLft'[#InOwn' #InShr']]".
    iSplit=>/=. { iPureIntro. by f_equal. } iSplit.
    { rewrite !lft_intersect_list_app. by iApply lft_intersect_mono. }
    iSplit; iModIntro.
    - iIntros "*". iDestruct 1 as (wl wl' ->) "[Own Own']". iExists wl, wl'.
      iSplit; [done|]. iSplitL "Own"; by [iApply "InOwn"|iApply "InOwn'"].
    - iIntros "* #[??]". rewrite Eq. iSplit; by [iApply "InShr"|iApply "InShr'"].
  Qed.

  Lemma product2_eqtype {A B A' B'} E L (f: A → A') f' (g: B → B') g' ty1 ty2 ty1' ty2' :
    eqtype E L f f' ty1 ty1' → eqtype E L g g' ty2 ty2' →
    eqtype E L (pair_map f g) (pair_map f' g') (ty1 * ty2) (ty1' * ty2').
  Proof. move=> [??][??]. split; by apply product2_subtype. Qed.

  Lemma cons_product2_subtype {A B A' B'} E L (f: A → A') (g: B → B') ty1 ty2 ty1' ty2' :
    subtype E L f ty1 ty1' → subtype E L g ty2 ty2' →
    subtype E L (cons_pair_map f g) (ty1 :* ty2) (ty1' :* ty2').
  Proof.
    move=> ??. rewrite cons_pair_map_via_pair_map. apply mod_ty_subtype.
    { apply pair_via_cons_pair. } by apply product2_subtype.
  Qed.

  Lemma product_subtype {As Bs} E L (tyl: _ As) (tyl': _ Bs) fl :
    subtypel E L tyl tyl' fl → subtype E L (xprod_map fl) (Π tyl) (Π tyl').
  Proof.
    move=> Subs. dependent induction Subs; [by apply subtype_refl|].
    by apply cons_product2_subtype.
  Qed.

  Lemma product_eqtype {As Bs} E L (tyl: _ As) (tyl': _ Bs) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (xprod_map fl) (xprod_map gl) (Π tyl) (Π tyl').
  Proof.
    move=> /HForallZip_zip [? /HForallZip_flip ?]. by split; apply product_subtype.
  Qed.

  Lemma outlives_product2 {A B} (ty: _ A) (ty': _ B) ϝ :
    ty_outlives_E (ty * ty') ϝ = ty_outlives_E ty ϝ ++ ty_outlives_E ty' ϝ.
  Proof. by rewrite /ty_outlives_E /= fmap_app. Qed.

(*
  Global Instance prod2_assoc E L : Assoc (eqtype E L) product2.
  Proof.
    intros ???. apply eqtype_unfold. iIntros (?) "_ !> _".
    rewrite /= !(assoc plus) !(assoc app). iSplit; [done|].
    iSplit; [|iSplit].
    - iApply lft_equiv_refl.
    - iIntros "!> *". iSplit; iIntros "H".
      + iDestruct "H" as (vl1 vl') "(-> & Ho1 & H)".
        iDestruct "H" as (vl2 vl3) "(-> & Ho2 & Ho3)".
        iExists _, _. iSplit. by rewrite assoc. iFrame. iExists _, _. by iFrame.
      + iDestruct "H" as (vl1 vl') "(-> & H & Ho3)".
        iDestruct "H" as (vl2 vl3) "(-> & Ho1 & Ho2)".
        iExists _, _. iSplit. by rewrite -assoc. iFrame. iExists _, _. by iFrame.
    - iIntros "!> *". rewrite assoc shift_loc_assoc_nat. by iApply (bi.iff_refl True%I).
  Qed.

  Global Instance prod2_unit_leftid E L : LeftId (eqtype E L) unit product2.
  Proof.
    intros ty. apply eqtype_unfold. iIntros (?) "_ !> _ /=".
    setoid_rewrite (left_id True%I bi_sep). setoid_rewrite shift_loc_0.
    iSplit; [done|iSplit; [|iSplit; iIntros "!> *"; iSplit; iIntros "H //"]].
    - iApply lft_equiv_refl.
    - by iDestruct "H" as (? ?) "(-> & -> & ?)".
    - iExists [], _. eauto.
  Qed.

  Global Instance prod2_unit_rightid E L : RightId (eqtype E L) unit product2.
  Proof.
    intros ty. apply eqtype_unfold. iIntros (?) "_ !> _ /=".
    setoid_rewrite (right_id True%I bi_sep). rewrite (right_id [] app).
    iSplit; [done|iSplit; [|iSplit; iIntros "!> *"; iSplit; iIntros "H //"]].
    - iApply lft_equiv_refl.
    - iDestruct "H" as (? ?) "(-> & ? & ->)". by rewrite right_id.
    - iExists _, []. rewrite right_id. eauto.
  Qed.

  Lemma prod_flatten E L tyl1 tyl2 tyl3 :
    eqtype E L (Π(tyl1 ++ Π tyl2 :: tyl3)) (Π(tyl1 ++ tyl2 ++ tyl3)).
  Proof.
    unfold product. induction tyl1; simpl; last by f_equiv.
    induction tyl2. by rewrite left_id. by rewrite /= -assoc; f_equiv.
  Qed.

  Lemma prod_flatten_l E L tyl1 tyl2 :
    eqtype E L (Π(Π tyl1 :: tyl2)) (Π(tyl1 ++ tyl2)).
  Proof. apply (prod_flatten _ _ []). Qed.
  Lemma prod_flatten_r E L tyl1 tyl2 :
    eqtype E L (Π(tyl1 ++ [Π tyl2])) (Π(tyl1 ++ tyl2)).
  Proof. by rewrite (prod_flatten E L tyl1 tyl2 []) app_nil_r. Qed.
  Lemma prod_app E L tyl1 tyl2 :
    eqtype E L (Π[Π tyl1; Π tyl2]) (Π(tyl1 ++ tyl2)).
  Proof. by rewrite -prod_flatten_r -prod_flatten_l. Qed.

  Lemma ty_outlives_E_elctx_sat_product E L tyl α:
    elctx_sat E L (tyl_outlives_E tyl α) →
    elctx_sat E L (ty_outlives_E (Π tyl) α).
  Proof.
    intro Hsat. eapply eq_ind; [done|]. clear Hsat. rewrite /ty_outlives_E /=.
    induction tyl as [|?? IH]=>//. rewrite /tyl_outlives_E /= fmap_app -IH //.
  Qed.
*)
End typing.

(*
Arguments product : simpl never.
Global Hint Resolve product_mono' product_proper' ty_outlives_E_elctx_sat_product
  : lrust_typing. *)
