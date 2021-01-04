From iris.proofmode Require Import tactics.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Section product.
  Context `{!typeG Σ}.

  (* TODO: Find a better spot for this. *)
  Lemma Z_nat_add (n1 n2 : nat) : Z.to_nat (n1 + n2) = (n1 + n2)%nat.
  Proof. rewrite Z2Nat.inj_add; [|lia..]. rewrite !Nat2Z.id //. Qed.

  (* "Pre"-unit.  We later define the full unit as the empty product.  That's
     convertible, but products are opaque in some hint DBs, so this does make a
     difference. *)
  Program Definition unit0 : type :=
    {| ty_size := 0; ty_lfts := []; ty_E := [];
       ty_own tid vl := ⌜vl = []⌝%I; ty_shr κ tid l := True%I |}.
  Next Obligation. iIntros (tid vl) "%". by subst. Qed.
  Next Obligation. by iIntros (??????) "_ _ _ $". Qed.
  Next Obligation. by iIntros (????) "_ $". Qed.

  Global Instance unit0_copy : Copy unit0.
  Proof.
    split.
    - simpl. by apply _.
    - iIntros (????????) "_ _ Htok $".
      iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.
      iExists 1%Qp. iModIntro. iExists []. iSplitR; [by rewrite heap_mapsto_vec_nil|].
      simpl. iSplitR; first by auto. iIntros "Htok2 _". by iApply "Htok".
  Qed.

  Global Instance unit0_send : Send unit0.
  Proof. by iIntros (tid1 tid2 vl) "H". Qed.

  Global Instance unit0_sync : Sync unit0.
  Proof. by iIntros (????) "_". Qed.

  Lemma split_prod_mt tid ty1 ty2 q l :
    (l ↦∗{q}: λ vl,
       ∃ vl1 vl2, ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I
       ⊣⊢ l ↦∗{q}: ty1.(ty_own) tid ∗ (l +ₗ ty1.(ty_size)) ↦∗{q}: ty2.(ty_own) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_app. iDestruct "H↦" as "[H↦1 H↦2]".
      iDestruct (ty_size_eq with "H1") as %->.
      iSplitL "H1 H↦1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]". iDestruct "H1" as (vl1) "[H↦1 H1]".
      iDestruct "H2" as (vl2) "[H↦2 H2]". iExists (vl1 ++ vl2).
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "H1") as %->.
      iFrame. iExists _, _. by iFrame.
  Qed.

  Program Definition product2 (ty1 ty2 : type) :=
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_lfts := ty1.(ty_lfts) ++ ty2.(ty_lfts);
       ty_E := ty1.(ty_E) ++ ty2.(ty_E);
       ty_own tid vl := (∃ vl1 vl2,
         ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I;
       ty_shr κ tid l :=
         (ty1.(ty_shr) κ tid l ∗
          ty2.(ty_shr) κ tid (l +ₗ ty1.(ty_size)))%I |}.
  Next Obligation.
    iIntros (ty1 ty2 tid vl) "H". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
    subst. rewrite app_length !ty_size_eq.
    iDestruct "H1" as %->. iDestruct "H2" as %->. done.
  Qed.
  Next Obligation.
    intros ty1 ty2 E κ l tid q ?. iIntros "#LFT /= #Hout H Htok".
    rewrite split_prod_mt.
    iMod (bor_sep with "LFT H") as "[H1 H2]"; first solve_ndisj.
    iMod (ty1.(ty_share) with "LFT [] H1 Htok") as "[? Htok]"; first solve_ndisj.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iMod (ty2.(ty_share) with "LFT [] H2 Htok") as "[? Htok]"; first solve_ndisj.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    by iFrame.
  Qed.
  Next Obligation.
    intros ty1 ty2 κ κ' tid l. iIntros "/= #H⊑ [H1 H2]".
    iSplitL "H1"; by iApply (ty_shr_mono with "H⊑").
  Qed.

  Global Instance product2_lft_morphism T1 T2:
    TypeLftMorphism T1 → TypeLftMorphism T2 →
    TypeLftMorphism (λ ty, product2 (T1 ty) (T2 ty)).
  Proof.
    destruct 1 as [α βs E Hα HE|α E Hα HE], 1 as [α' βs' E' Hα' HE'|α' E' Hα' HE'].
    - apply (type_lft_morphism_add _ (α ⊓ α') (βs ++ βs') (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app. iApply lft_equiv_trans.
        { iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα']. }
        rewrite -!assoc (comm (⊓) (ty_lft ty) (α' ⊓ _)) -!assoc.
        repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
        iApply lft_intersect_equiv_idemp.
      + rewrite /= !elctx_interp_app HE HE' big_sepL_app -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc (comm (⊓) α' (ty_lft ty)) assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + rewrite /= !elctx_interp_app HE HE' -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    - apply (type_lft_morphism_add _ (α ⊓ α') βs' (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app -assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite /= !elctx_interp_app HE HE' -!assoc.
    - apply (type_lft_morphism_const _ (α ⊓ α') (E ++ E'))=>ty.
      + rewrite lft_intersect_list_app.
        iApply lft_intersect_equiv_proper; [iApply Hα|iApply Hα'].
      + by rewrite /= !elctx_interp_app HE HE'.
  Qed.

  Global Instance product2_type_ne T1 T2:
    TypeNonExpansive T1 → TypeNonExpansive T2 →
    TypeNonExpansive (λ ty, product2 (T1 ty) (T2 ty)).
  Proof.
    intros HT1 HT2. split.
    - apply _.
    - move=>ty1 ty2 /= ?.
      rewrite !(type_non_expansive_ty_size (T:=T1) ty1 ty2) //.
      rewrite !(type_non_expansive_ty_size (T:=T2) ty1 ty2) //.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs tid vl /=.
      by do 6 f_equiv; apply type_non_expansive_ty_own.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l /=.
      rewrite !(type_non_expansive_ty_size (T:=T1) ty1 ty2) //.
      by f_equiv; apply type_non_expansive_ty_shr.
  Qed.

  (* TODO : find a way to avoid this duplication. *)
  Global Instance product2_type_contractive T1 T2:
    TypeContractive T1 → TypeContractive T2 →
    TypeContractive (λ ty, product2 (T1 ty) (T2 ty)).
  Proof.
    intros HT1 HT2. split.
    - apply _.
    - move=>ty1 ty2 /=.
      rewrite !(type_contractive_ty_size (T:=T1) ty1 ty2).
      by rewrite !(type_contractive_ty_size (T:=T2) ty1 ty2).
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs tid vl /=.
      by do 6 f_equiv; apply type_contractive_ty_own.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l /=.
      rewrite !(type_contractive_ty_size (T:=T1) ty1 ty2).
      by f_equiv; apply type_contractive_ty_shr.
  Qed.

  Global Instance product2_ne :
    NonExpansive2 product2.
  Proof. solve_ne_type. Qed.

  Global Instance product2_mono E L:
    Proper (subtype E L ==> subtype E L ==> subtype E L) product2.
  Proof.
    iIntros (ty11 ty12 H1 ty21 ty22 H2). iIntros (qL) "HL".
    iDestruct (H1 with "HL") as "#H1". iDestruct (H2 with "HL") as "#H2".
    iIntros "!# #HE".
    iDestruct ("H1" with "HE") as "(% & #Hout1 & #Ho1 & #Hs1)". iClear (H1) "H1".
    iDestruct ("H2" with "HE") as "(% & #Hout2 & #Ho2 & #Hs2)". iClear (H2) "H2".
    iSplit; first by (iPureIntro; simpl; f_equal). iSplit; [|iSplit; iModIntro].
    - rewrite !lft_intersect_list_app. by iApply lft_intersect_mono.
    - iIntros (??) "H /=". iDestruct "H" as (vl1 vl2) "(-> & Hown1 & Hown2)".
      iExists _, _. iSplit. done. iSplitL "Hown1".
      + by iApply "Ho1".
      + by iApply "Ho2".
    - iIntros (???) "/= #[Hshr1 Hshr2]". iSplit.
      + by iApply "Hs1".
      + rewrite -(_ : ty_size ty11 = ty_size ty12) //. by iApply "Hs2".
  Qed.
  Global Instance product2_proper E L:
    Proper (eqtype E L ==> eqtype E L ==> eqtype E L) product2.
  Proof. by intros ??[]??[]; split; apply product2_mono. Qed.

  Global Instance product2_copy `{!Copy ty1} `{!Copy ty2} :
    Copy (product2 ty1 ty2).
  Proof.
    split; first (simpl; apply _).
    intros κ tid E F l q ? HF. iIntros "#LFT [H1 H2] Htl [Htok1 Htok2]".
    iMod (@copy_shr_acc with "LFT H1 Htl Htok1")
      as (q1 vl1) "(Htl & H↦1 & #H1 & Hclose1)"; first solve_ndisj.
    { rewrite <-HF. apply shr_locsE_subseteq. simpl. clear. lia. }
    iMod (@copy_shr_acc with "LFT H2 Htl Htok2")
      as (q2 vl2) "(Htl & H↦2 & #H2 & Hclose2)"; first solve_ndisj.
    { move: HF. rewrite /= -plus_assoc shr_locsE_shift.
      assert (shr_locsE l (ty_size ty1) ## shr_locsE (l +ₗ (ty_size ty1)) (ty_size ty2 + 1))
             by exact: shr_locsE_disj.
      set_solver. }
    iDestruct (na_own_acc with "Htl") as "[$ Htlclose]".
    { generalize (shr_locsE_shift l ty1.(ty_size) ty2.(ty_size)). simpl. set_solver+. }
    destruct (Qp_lower_bound q1 q2) as (qq & q'1 & q'2 & -> & ->).
    iExists qq, (vl1 ++ vl2). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "H1") as ">->".
    iDestruct "H↦1" as "[$ H↦1f]". iDestruct "H↦2" as "[$ H↦2f]".
    iSplitR; [by simpl; eauto 10|]. iIntros "!> Htl [H↦1 H↦2]".
    iDestruct ("Htlclose" with "Htl") as "Htl".
    iMod ("Hclose2" with "Htl [H2 H↦2f H↦2]") as "[Htl $]"; [by iFrame|].
    iApply ("Hclose1" with "Htl [H1 H↦1f H↦1]"). by iFrame.
  Qed.

  Global Instance product2_send `{!Send ty1} `{!Send ty2} :
    Send (product2 ty1 ty2).
  Proof.
    iIntros (tid1 tid2 vl) "H". iDestruct "H" as (vl1 vl2) "(% & Hown1 & Hown2)".
    iExists _, _. iSplit; first done. iSplitL "Hown1"; by iApply @send_change_tid.
  Qed.

  Global Instance product2_sync `{!Sync ty1} `{!Sync ty2} :
    Sync (product2 ty1 ty2).
  Proof.
    iIntros (κ tid1 ti2 l) "[#Hshr1 #Hshr2]". iSplit; by iApply @sync_change_tid.
  Qed.

  Definition product := foldr product2 unit0.
  Definition unit := product [].

  Lemma outlives_product ty1 ty2 ϝ :
    ty_outlives_E (product [ty1; ty2]) ϝ = ty_outlives_E ty1 ϝ ++ ty_outlives_E ty2 ϝ.
  Proof. rewrite /product /ty_outlives_E /= fmap_app right_id //. Qed.

  Global Instance product_type_ne Tl:
    TypeListNonExpansive Tl → TypeNonExpansive (product ∘ Tl).
  Proof.
    intros (Tl' & HTlTl' & HTl').
    eapply type_ne_ext; last first.
    { intros ty. by rewrite /= HTlTl'. }
    clear Tl HTlTl'. induction HTl' as [|T Tl'  HT HTl' ]=>/=; apply _.
  Qed.
  Global Instance product_type_ne_cont Tl:
    TypeListContractive Tl → TypeContractive (product ∘ Tl).
  Proof.
    intros (Tl' & HTlTl' & HTl').
    eapply type_contractive_ext; last first.
    { intros ty. by rewrite /= HTlTl'. }
    clear Tl HTlTl'. induction HTl' as [|T Tl'  HT HTl' ]=>/=; apply _.
  Qed.
  Global Instance product_ne : NonExpansive product.
  Proof. intros ??. induction 1=>//=. by f_equiv. Qed.
  Global Instance product_mono E L:
    Proper (Forall2 (subtype E L) ==> subtype E L) product.
  Proof. intros ??. induction 1=>//=. by f_equiv. Qed.
  Lemma product_mono' E L tyl1 tyl2 :
    Forall2 (subtype E L) tyl1 tyl2 → subtype E L (product tyl1) (product tyl2).
  Proof. apply product_mono. Qed.
  Global Instance product_proper E L:
    Proper (Forall2 (eqtype E L) ==> eqtype E L) product.
  Proof. intros ??. induction 1=>//=. by f_equiv. Qed.
  Lemma product_proper' E L tyl1 tyl2 :
    Forall2 (eqtype E L) tyl1 tyl2 → eqtype E L (product tyl1) (product tyl2).
  Proof. apply product_proper. Qed.
  Global Instance product_copy tys : LstCopy tys → Copy (product tys).
  Proof. induction 1; apply _. Qed.
  Global Instance product_send tys : LstSend tys → Send (product tys).
  Proof. induction 1; apply _. Qed.
  Global Instance product_sync tys : LstSync tys → Sync (product tys).
  Proof. induction 1; apply _. Qed.

  Definition product_cons ty tyl :
    product (ty :: tyl) = product2 ty (product tyl) := eq_refl _.
  Definition product_nil :
    product [] = unit0 := eq_refl _.
End product.

Notation Π := product.

Section typing.
  Context `{!typeG Σ}.

  Global Instance prod2_assoc E L : Assoc (eqtype E L) product2.
  Proof.
    intros ???. apply eqtype_unfold. iIntros (?) "_ !# _".
    rewrite /= !(assoc plus) !(assoc app). iSplit; [done|].
    iSplit; [|iSplit].
    - iApply lft_equiv_refl.
    - iIntros "!# *". iSplit; iIntros "H".
      + iDestruct "H" as (vl1 vl') "(-> & Ho1 & H)".
        iDestruct "H" as (vl2 vl3) "(-> & Ho2 & Ho3)".
        iExists _, _. iSplit. by rewrite assoc. iFrame. iExists _, _. by iFrame.
      + iDestruct "H" as (vl1 vl') "(-> & H & Ho3)".
        iDestruct "H" as (vl2 vl3) "(-> & Ho1 & Ho2)".
        iExists _, _. iSplit. by rewrite -assoc. iFrame. iExists _, _. by iFrame.
    - iIntros "!# *". rewrite assoc shift_loc_assoc_nat. by iApply (bi.iff_refl True%I).
  Qed.

  Global Instance prod2_unit_leftid E L : LeftId (eqtype E L) unit product2.
  Proof.
    intros ty. apply eqtype_unfold. iIntros (?) "_ !# _ /=".
    setoid_rewrite (left_id True%I bi_sep). setoid_rewrite shift_loc_0.
    iSplit; [done|iSplit; [|iSplit; iIntros "!# *"; iSplit; iIntros "H //"]].
    - iApply lft_equiv_refl.
    - by iDestruct "H" as (? ?) "(-> & -> & ?)".
    - iExists [], _. eauto.
  Qed.

  Global Instance prod2_unit_rightid E L : RightId (eqtype E L) unit product2.
  Proof.
    intros ty. apply eqtype_unfold. iIntros (?) "_ !# _ /=".
    setoid_rewrite (right_id True%I bi_sep). rewrite (right_id [] app).
    iSplit; [done|iSplit; [|iSplit; iIntros "!# *"; iSplit; iIntros "H //"]].
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
End typing.

Arguments product : simpl never.
Hint Resolve product_mono' product_proper' ty_outlives_E_elctx_sat_product
  : lrust_typing.
