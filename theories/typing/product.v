Require Import FunctionalExtensionality Equality.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import list numbers.
From lrust.util Require Import basic update types.
From lrust.typing Require Import lft_contexts mod_ty.
From lrust.typing Require Export type.

Set Default Proof Using "Type".

Section product.
  Context `{!typeG Σ}.

  Program Definition r_unit: type () := {|
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

  Program Definition r_prod {A B} (ty: type A) (ty': type B) : type (A * B) :=
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

  Global Instance prod_ne {A B} : NonExpansive2 (@r_prod A B).
  Proof. solve_ne_type. Qed.

  Definition r_nil_unit: type :1 := <{const -[]}> r_unit.

  Definition r_cons_prod {A B} (ty: type A) (ty': type B)
    : type (A :* B) := <{prod_to_cons_prod}> (r_prod ty ty').

  Global Instance cons_prod_ne {A B} : NonExpansive2 (@r_cons_prod A B).
  Proof. move=> ???????. rewrite /r_cons_prod. by do 2 f_equiv. Qed.

  Fixpoint r_xprod {As} (tyl: typel As) : type (xprod As) :=
    match tyl with +[] => r_nil_unit | ty +:: tyl' => r_cons_prod ty (r_xprod tyl') end.

  Global Instance product_ne {As} : NonExpansive (@r_xprod As).
  Proof. move=> ???. elim; [done|]=> */=. by f_equiv. Qed.

End product.

Notation "()" := (r_unit) : lrust_type_scope.
Notation "ty * ty'" := (r_prod ty%T ty'%T) : lrust_type_scope.
Notation ":1" := r_nil_unit : lrust_type_scope.
Notation "ty :* ty'" := (r_cons_prod ty%T ty'%T) : lrust_type_scope.
Notation Π := (r_xprod).

Section typing.
  Context `{!typeG Σ}.

  Global Instance unit_copy: Copy ().
  Proof.
    split; [apply _|]. move=> */=. iIntros "_ _ Na $". iExists 1%Qp, []. iModIntro.
    iDestruct (na_own_acc with "Na") as "[$ ToNa]"; [solve_ndisj|].
    rewrite heap_mapsto_vec_nil. do 2 (iSplit; [done|]). iIntros "?_!>". by iApply "ToNa".
  Qed.
  Global Instance unit_send: Send (). Proof. done. Qed.
  Global Instance unit_sync: Sync (). Proof. done. Qed.

  Global Instance prod_lft_morphism {A B C} (T: _ A → _ B) (T': _ → _ C):
    TypeLftMorphism T → TypeLftMorphism T' →
    TypeLftMorphism (λ ty, T ty * T' ty)%T.
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

  Global Instance prod_type_ne {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (λ ty, T ty * T' ty)%T.
  Proof. move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_non_expansive_ty_size.
    - move=> *. do 6 f_equiv; by apply type_non_expansive_ty_own.
    - move=> ? ty ty' *. rewrite (type_non_expansive_ty_size (T:=T) ty ty'); [|done].
      f_equiv; by apply type_non_expansive_ty_shr.
  Qed.
  (* TODO : find a way to avoid this duplication. *)
  Global Instance prod_type_contractive {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty * T' ty)%T.
  Proof. move=> ??. split=>/=; first apply _.
    - move=> *. f_equiv; by apply type_contractive_ty_size.
    - move=> *. do 6 f_equiv; by apply type_contractive_ty_own.
    - move=> ? ty ty' *. rewrite (type_contractive_ty_size (T:=T) ty ty').
      f_equiv; by apply type_contractive_ty_shr.
  Qed.

  Global Instance cons_prod_type_ne {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (λ ty, T ty :* T' ty)%T.
  Proof.
    have ->: ((λ ty, T ty :* T' ty) =
      <{prod_to_cons_prod}> ∘ λ ty, T ty * T' ty)%T by done.
    move=> ??. apply type_ne_ne_compose; apply _.
  Qed.
  Global Instance cons_prod_type_contractive {A B C} (T: _ A → _ B) (T': _ → _ C) :
    TypeContractive T → TypeContractive T' → TypeContractive (λ ty, T ty :* T' ty)%T.
  Proof.
    have ->: ((λ ty, T ty :* T' ty) =
      <{prod_to_cons_prod}> ∘ λ ty, T ty * T' ty)%T by done.
    move=> ??. apply type_contractive_compose_left; apply _.
  Qed.

  Global Instance product_type_ne {A Bs} (T: _ A → _ Bs) :
    TypeListNonExpansive T → TypeNonExpansive (Π ∘ T)%T.
  Proof.
    move=> [Tl [Eq All]].
    have ->: (Π ∘ T = λ ty, Π ((λ _ (T': _ → _), T' ty) +<$>+ Tl))%T.
    { extensionality ty. by rewrite /= Eq. } clear Eq T.
    dependent induction All=>/=; by [apply _|apply cons_prod_type_ne].
  Qed.
  Global Instance product_type_ne_cont {A Bs} (T: _ A → _ Bs) :
    TypeListContractive T → TypeContractive (Π ∘ T)%T.
  Proof.
    move=> [Tl [Eq All]].
    have ->: (Π ∘ T = λ ty, Π ((λ _ (T': _ → _), T' ty) +<$>+ Tl))%T.
    { extensionality ty. by rewrite /= Eq. } clear Eq T.
    dependent induction All=>/=; by [apply _|apply cons_prod_type_contractive].
  Qed.

  Global Instance prod_copy {A B} (ty: _ A) (ty': _ B) :
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
    case (Qp_lower_bound q q')=> [q''[?[?[->->]]]].
    iExists q'', (wl ++ wl'). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "Own") as ">->".
    iDestruct "Mt" as "[$ Mtr]". iDestruct "Mt'" as "[$ Mtr']".
    iSplitR. { iIntros "!>!>". iExists wl, wl'. iSplit; by [|iSplit]. }
    iIntros "!> Na [Mt Mt']". iDestruct ("PreNa" with "Na") as "Na".
    iMod ("Close'" with "Na [$Mt' $Mtr']") as "[Na $]".
    iApply ("Close" with "Na [$Mt $Mtr]").
  Qed.

  Global Instance prod_send {A B} (ty: _ A) (ty': _ B) :
    Send ty → Send ty' → Send (ty * ty').
  Proof.
    move=> *?*. iDestruct 1 as (wl wl' ->) "[Own Own']".
    iExists wl, wl'. iSplit; [done|]. iSplitL "Own"; by iApply @send_change_tid.
  Qed.
  Global Instance prod_sync {A B} (ty: _ A) (ty': _ B) :
    Sync ty → Sync ty' → Sync (ty * ty').
  Proof.
    move=> *?*. iIntros "[#? #?]". iSplit; by iApply @sync_change_tid.
  Qed.

  Global Instance xprod_copy {As} (tyl: _ As) : ListCopy tyl → Copy (Π tyl).
  Proof. elim; apply _. Qed.
  Global Instance xprod_send {As} (tyl: _ As) : ListSend tyl → Send (Π tyl).
  Proof. elim; apply _. Qed.
  Global Instance xprod_sync {As} (tyl: _ As) : ListSync tyl → Sync (Π tyl).
  Proof. elim; apply _. Qed.

  Lemma prod_subtype {A B A' B'} E L (f: A → A') (g: B → B') ty1 ty2 ty1' ty2' :
    subtype E L f ty1 ty1' → subtype E L g ty2 ty2' →
    subtype E L (prod_map f g) (ty1 * ty2) (ty1' * ty2').
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

  Lemma prod_eqtype {A B A' B'} E L (f: A → A') f' (g: B → B') g' ty1 ty2 ty1' ty2' :
    eqtype E L f f' ty1 ty1' → eqtype E L g g' ty2 ty2' →
    eqtype E L (prod_map f g) (prod_map f' g') (ty1 * ty2) (ty1' * ty2').
  Proof. move=> [??][??]. split; by apply prod_subtype. Qed.

  Lemma cons_prod_subtype {A B A' B'} E L (f: A → A') (g: B → B') ty1 ty2 ty1' ty2' :
    subtype E L f ty1 ty1' → subtype E L g ty2 ty2' →
    subtype E L (cons_prod_map f g) (ty1 :* ty2) (ty1' :* ty2').
  Proof.
    move=> ??. rewrite cons_prod_map_via_prod_map.
    apply mod_ty_subtype; [apply iso|by apply prod_subtype].
  Qed.

  Lemma xprod_subtype {As Bs} E L (tyl: _ As) (tyl': _ Bs) fl :
    subtypel E L tyl tyl' fl → subtype E L (xprod_map fl) (Π tyl) (Π tyl').
  Proof.
    move=> Subs. dependent induction Subs; [by apply subtype_refl|].
    by apply cons_prod_subtype.
  Qed.

  Lemma xprod_eqtype {As Bs} E L (tyl: _ As) (tyl': _ Bs) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (xprod_map fl) (xprod_map gl) (Π tyl) (Π tyl').
  Proof.
    move=> /HForallZip_zip[? /HForallZip_flip ?]. by split; apply xprod_subtype.
  Qed.

  Lemma outlives_prod {A B} (ty: _ A) (ty': _ B) ϝ :
    ty_outlives_E (ty * ty') ϝ = ty_outlives_E ty ϝ ++ ty_outlives_E ty' ϝ.
  Proof. by rewrite /ty_outlives_E /= fmap_app. Qed.

  Lemma r_prod_assoc {A B C} E L (ty1: _ A) (ty2: _ B) (ty3: _ C) :
    eqtype E L prod_assoc prod_assoc' (ty1 * (ty2 * ty3)) ((ty1 * ty2) * ty3).
  Proof.
    have Eq: ∀vπ: proph_asn → (A * (B * C)),
      fst ∘ (fst ∘ (prod_assoc ∘ vπ)) = fst ∘ vπ ∧
      snd ∘ (fst ∘ (prod_assoc ∘ vπ)) = fst ∘ (snd ∘ vπ) ∧
      snd ∘ (prod_assoc ∘ vπ) = snd ∘ (snd ∘ vπ).
    { move=> vπ. split; [|split]; extensionality xyz=>/=; by case (vπ xyz)=> [?[??]]. }
    apply eqtype_unfold; [apply _|]. iIntros (?) "_!>_/=". iSplit; [iPureIntro; lia|].
    iSplit; [rewrite (assoc (++)); by iApply lft_equiv_refl|].
    iSplit; iIntros "!>" (vπ) "*"; move: (Eq vπ)=> [->[->->]].
    - iSplit.
      + iDestruct 1 as (wl1 wl23 ->) "[Own1 Own23]".
        iDestruct "Own23" as (wl2 wl3 ->) "[Own2 Own3]". iExists (wl1 ++ wl2), wl3.
        iSplit; [by rewrite assoc|]. iFrame "Own3". iExists wl1, wl2. by iFrame.
      + iDestruct 1 as (wl12 wl3 ->) "[Own12 Own3]".
        iDestruct "Own12" as (wl1 wl2 ->) "[Own1 Own2]". iExists wl1, (wl2 ++ wl3).
        iSplit; [by rewrite assoc|]. iFrame "Own1". iExists wl2, wl3. by iFrame.
    - rewrite -assoc shift_loc_assoc_nat. by iApply (bi.iff_refl True%I).
  Qed.
  Lemma r_prod_assoc' {A B C} E L (ty1: _ A) (ty2: _ B) (ty3: _ C) :
    eqtype E L prod_assoc' prod_assoc ((ty1 * ty2) * ty3) (ty1 * (ty2 * ty3)).
  Proof. apply eqtype_symm, r_prod_assoc. Qed.

  Lemma r_prod_left_id {A} E L (ty: _ A) :
    eqtype E L prod_left_id prod_left_id' (() * ty) (ty).
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros (?) "_!>_/=". iSplit; [done|].
    iSplit; [by iApply lft_equiv_refl|].
    have Eq: ∀vπ: proph_asn → (() * A), prod_left_id ∘ vπ = snd ∘ vπ.
    { move=> vπ. extensionality π. simpl. by case (vπ π)=> [[]?]. }
    iSplit; iIntros "!> *"; rewrite Eq; [iSplit|].
    - by iDestruct 1 as (?? ->->) "Own /=".
    - iIntros "Own". iExists [], _. by iFrame "Own".
    - rewrite left_id shift_loc_0. by iApply (bi.iff_refl True%I).
  Qed.

  Lemma r_prod_right_id {A} E L (ty: _ A) :
    eqtype E L prod_right_id prod_right_id' (ty * ()) (ty).
  Proof.
    apply eqtype_unfold; [apply _|]. iIntros (?) "_!>_/=".
    rewrite !right_id. iSplit; [done|]. iSplit; [by iApply lft_equiv_refl|].
    have Eq: ∀vπ: proph_asn → (A * ()), prod_right_id ∘ vπ = fst ∘ vπ.
    { move=> vπ. extensionality π. simpl. by case (vπ π)=> [?[]]. }
    iSplit; iIntros "!> *"; rewrite Eq; [iSplit|].
    - iDestruct 1 as (?? ->) "[Own ->]". by rewrite right_id.
    - iIntros "Own". iExists _, []. iFrame "Own". by rewrite right_id.
    - rewrite right_id. by iApply (bi.iff_refl True%I).
  Qed.

  Lemma xprod_app {As Bs} E L (tyl: _ As) (tyl': _ Bs) :
    eqtype E L (curry papp) psep (Π tyl * Π tyl') (Π (tyl h++ tyl')).
  Proof.
    elim: tyl=> [|A As' ty tyl Eq].
    - have [->->]: curry (@papp id ^[] Bs) = prod_left_id ∘ prod_map (const ()) id ∧
        @psep id ^[] Bs = prod_map (const -[]) id ∘ prod_left_id'.
      { split; extensionality x; by [case x=> [[]?]|]. }
      eapply eqtype_trans; [|apply r_prod_left_id]. apply prod_eqtype; [|done].
      apply mod_ty_outin, functional_extensionality. by move=> [].
    - have [->->]: curry (@papp id (A ^:: As') Bs) = prod_to_cons_prod ∘
        prod_map id (curry papp) ∘ prod_assoc' ∘ prod_map cons_prod_to_prod id ∧
        @psep id (A ^:: As') Bs = prod_map prod_to_cons_prod id ∘
          (prod_assoc ∘ (prod_map id psep ∘ cons_prod_to_prod)).
      { split; extensionality x; [by case x=> [[??]?]|]. case x=> [? xl]/=.
        by case (psep xl). }
      eapply eqtype_trans. { apply prod_eqtype; [apply mod_ty_outin, _|done]. }
      eapply eqtype_trans. { apply r_prod_assoc'. } eapply eqtype_trans.
      { apply prod_eqtype; [done|apply Eq]. } apply mod_ty_inout, _.
  Qed.

  Lemma ty_outlives_E_elctx_sat_product {As} E L (tyl: _ As) α:
    elctx_sat E L (tyl_outlives_E tyl α) → elctx_sat E L (ty_outlives_E (Π tyl) α).
  Proof.
    move=> ?. eapply eq_ind; [done|]. rewrite /ty_outlives_E /=.
    elim tyl=> /=[|> IH]; [done|]. by rewrite fmap_app -IH.
  Qed.

End typing.

Arguments r_xprod : simpl never.
Global Hint Resolve prod_subtype prod_eqtype ty_outlives_E_elctx_sat_product
  : lrust_typing.
