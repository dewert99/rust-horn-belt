From iris.proofmode Require Import tactics.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export type.
From lrust.util Require Import point_free.

Set Default Proof Using "Type".

Section fupd_combine.
  Context `{BiFUpd PROP}.
  Implicit Types P Q : PROP.
  Lemma step_fupdN_combine n E P Q : (|={E}▷=>^n P) ∗ (|={E}▷=>^n Q) ⊢ |={E}▷=>^n (P ∗ Q)%I. 
  Proof.
    iIntros "[H1 H2]".
    iInduction n as [|n] "IH".
    - iFrame. 
    (* compact this proof down. only challenge is controlling unfolding *)
    - iMod "H1"; iMod "H2"; iModIntro; iNext.
      by iApply ("IH" with "[> $]").
  Qed.
End fupd_combine.

Section product.
  Context `{!typeG Σ}.

  (* TODO: Find a better spot for this. *)
  Lemma Z_nat_add (n1 n2 : nat) : Z.to_nat (n1 + n2) = (n1 + n2)%nat.
  Proof. rewrite Z2Nat.inj_add; [|lia..]. rewrite !Nat2Z.id //. Qed.

  (* "Pre"-unit.  We later define the full unit as the empty product.  That's
     convertible, but products are opaque in some hint DBs, so this does make a
     difference. *)
  Program Definition unit0 {A} : type A :=
    {| ty_size := 0; ty_lfts := []; ty_E := [];
       ty_own depth tid vl := ⌜vl = [] ∧ depth.1 ./ []⌝%I; ty_shr d κ tid l := ⌜ d.1 ./ [] ⌝%I |}.
  
  Next Obligation. iIntros (A depth tid vl) "[% _]". by subst. Qed.
  Next Obligation. by iIntros (??????). Qed.
  Next Obligation. by iIntros (????????). Qed.
  Next Obligation. by iIntros (??????) "?". Qed.
  Next Obligation. iIntros (?????????) "#LFT ? H Htok".
    iApply step_fupdN_intro=>//.
    iModIntro. iNext.
    iMod (bor_exists with "LFT H") as (vl) "H"; first done.
    iMod (bor_sep with "LFT H") as "[_ H]"; first done.
    iMod ((bor_persistent _ E) with "LFT H Htok") as "[> [_ ?] ?]"; first done.
    by iFrame. 
  Qed.
  Next Obligation. iIntros (?????????) "/= ? ? [% %] ?".
    iModIntro. 
    iApply step_fupdN_intro=>//. iNext. iModIntro.
    iExists [], q.
    iSplit; first done.
    iSplit; first by rewrite /proph_toks.
    iIntros; iModIntro; iFrame; done.
  Qed.

  Next Obligation. iIntros (??????????) "/= ? ? ? % ?".
  iModIntro. iApply step_fupdN_intro=>//. do 4 iModIntro.
  iExists [], q.
  iSplit; first done.
  iSplit; first by rewrite /proph_toks.
  iIntros. by iFrame.
  Qed. 

  Global Instance unit0_copy {A} : Copy (@unit0 A).
  Proof.
    split.
    - simpl. by apply _.
    - iIntros (????????) "_ ? Hshr Htok $".
      iDestruct (na_own_acc with "Htok") as "[$ Htok]"; first solve_ndisj.  
      iExists 1%Qp. iModIntro. iExists []. iSplitR; [by rewrite heap_mapsto_vec_nil|].
      iDestruct "Hshr" as "%".
      simpl. iSplitR; first by auto. iIntros "Htok2 _". by iApply "Htok".
  Qed.

  Global Instance unit0_send {A : Type } : Send (@unit0 A).
  Proof. by iIntros (depth tid1 tid2 vl) "H". Qed.

  Global Instance unit0_sync { A : Type } : Sync (@unit0 A).
  Proof. by iIntros (????). Qed.

  Lemma split_prod_mt {A B} (depth1 : pval_depth A) (depth2 : pval_depth B) tid ty1 ty2 q l :
    (l ↦∗{q}: λ vl, ∃ vl1 vl2,
       ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) depth1 tid vl1 ∗ ty2.(ty_own) depth2 tid vl2)%I
       ⊣⊢ l ↦∗{q}: ty1.(ty_own) depth1 tid ∗
          (l +ₗ ty1.(ty_size)) ↦∗{q}: ty2.(ty_own) depth2 tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (vl1 vl2 ?) "[H1 H2]".
      subst. rewrite heap_mapsto_vec_app. iDestruct "H↦" as "[H↦1 H↦2]".
      iDestruct (ty_size_eq with "H1") as %->.
      iSplitL "H1 H↦1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]".
      iDestruct "H1" as (vl1) "[H↦1 H1]". iDestruct "H2" as (vl2) "[H↦2 H2]".
      iExists (vl1 ++ vl2). rewrite heap_mapsto_vec_app.
      iDestruct (ty_size_eq with "H1") as %->. auto with iFrame.
  Qed.

  Program Definition product2 {A B} (ty1 : type A) (ty2 : type B) : type (A * B) :=
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_lfts := ty1.(ty_lfts) ++ ty2.(ty_lfts);
       ty_E := ty1.(ty_E) ++ ty2.(ty_E);
       ty_own vπd tid vl := (∃ vl1 vl2,
         ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) (fst ∘ vπd.1, vπd.2) tid vl1 ∗ ty2.(ty_own) (snd ∘ vπd.1, vπd.2) tid vl2)%I;
       ty_shr d κ tid l :=
         (ty1.(ty_shr) (fst ∘ d.1, d.2) κ tid l ∗
          ty2.(ty_shr) (snd ∘ d.1, d.2) κ tid (l +ₗ ty1.(ty_size)))%I |}.
  Next Obligation.
    iIntros (A B ty1 ty2 depth tid vl) "H". iDestruct "H" as (vl1 vl2 ?) "[H1 H2]".
    subst. rewrite app_length !ty_size_eq.
    iDestruct "H1" as %->. iDestruct "H2" as %->. done.
  Qed.
  Next Obligation.
    move=>A B ty1 ty2 depth1 depth2 tid vl Hdepth /=.
    iDestruct 1 as (vl1 vl2 ->) "[H1 H2]".
    iExists vl1, vl2. iSplitR; [done|]. by iSplitL "H1"; iApply ty_own_depth_mono.
  Qed.

  Next Obligation.
    iIntros (A B ty1 ty2 d1 d2 asn κ tid l Hdepth) "[? ?]".
    iSplit; by iApply (ty_shr_depth_mono _ _ _ _ _ _ _ _ Hdepth).
  Qed.

  Next Obligation.
    iIntros (A B ty1 ty2 κ κ' vπd tid l) "Hout [? ?]".
    iSplit; by iApply (ty_shr_lft_mono with "Hout").
  Qed.

  Next Obligation.
    intros A B ty1 ty2 E vπ depth κ l tid q ?; iIntros "#LFT /= #? H [Htok1 Htok2]".
    rewrite split_prod_mt.

    iMod (bor_sep with "LFT H") as "[H1 H2]"; first solve_ndisj.
    iMod (ty1.(ty_share A) with "LFT [] H1 Htok1") as "H1"; first solve_ndisj.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iMod (ty2.(ty_share B) with "LFT [] H2 Htok2") as "H2"; first solve_ndisj.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }

    iDestruct (step_fupdN_combine with "[H1 H2]") as "H1"; first iFrame.
    iModIntro.
    iApply (step_fupdN_wand with "H1").
    iIntros "[> [? ?] > [? ?]]". by iFrame. 
    Qed.
  
  Next Obligation.
    iIntros (A B ty1 ty2 N vπ d tid vl κ q ?) "#LFT #H⊑". 
    iDestruct 1 as (vl1 vl2) "(? & Hownty1 & Hownty2)".
    iIntros "[Htok1 Htok2]".
    iDestruct (ty_own_proph with "LFT [] Hownty1 Htok1") as "> H1"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iDestruct (ty_own_proph with "LFT [] Hownty2 Htok2") as "> H2"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    
    iDestruct (step_fupdN_combine with "[H1 H2]") as "H1"; first iAccu. 
    iApply (step_fupdN_wand with "H1").
    iModIntro.
    iIntros "[H1 H2]". 
    iMod "H1" as (ξs1 q1') "(% & q1dep & ty1own)".
    iMod "H2" as (ξs2 q2') "(% & q2dep & ty2own)".
    destruct (Qp_lower_bound q1' q2') as (x & r1 & r2 & Hq1 & Hq2); setoid_subst.
    iExists (ξs1 ++ ξs2), x.
    iModIntro.
    iSplit.
    - iPureIntro.
      by apply proph_dep_pair.
    - iDestruct "q1dep" as "[xξ1 r1ξ1]".
      iDestruct "q2dep" as "[xξ2 r2ξ2]".
      iSplitL "xξ1 xξ2"; iFrame.
      iIntros "[xξ1 xξ2]".
      iMod ("ty1own" with "[$]") as "[? ?]"; first iFrame.
      iMod ("ty2own" with "[$]") as "[? ?]"; first iFrame.
      iExists vl1, vl2; by iFrame.
  Qed.    

  Next Obligation.
    iIntros (A B ty1 ty2 E vπ d κ tid l κ' q ?) "/= #LFT #Hsub #? [Hty1 Hty2] [Htok1 Htok2]".
    iMod (ty1.(ty_shr_proph A) with "LFT Hsub [] Hty1 Htok1") as "Hty1"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_l. }
    iMod (ty2.(ty_shr_proph B) with "LFT Hsub [] Hty2 Htok2") as "Hty2"; first done.
    { iApply lft_incl_trans; [done|]. rewrite lft_intersect_list_app.
      iApply lft_intersect_incl_r. }
    iModIntro; iNext.
    iCombine "Hty1 Hty2" as "> ?".
    iDestruct (step_fupdN_combine with "[$]") as "H1". 
    iApply (step_fupdN_wand with "H1").
    iModIntro.
    iIntros "[Hty1 Hty2]".
    iMod "Hty1" as (ξs1 q1') "(% & q1dep & ty1own)".
    iMod "Hty2" as (ξs2 q2') "(% & q2dep & ty2own)".
    destruct (Qp_lower_bound q1' q2') as (x & r1 & r2 & -> & ->).
    iDestruct "q1dep" as "[xξ1 r1ξ1]".
    iDestruct "q2dep" as "[xξ2 r2ξ2]".
    iExists (ξs1 ++ ξs2), x.
    iModIntro.
    iSplit.
    - iPureIntro.
      by apply proph_dep_pair.
    - iSplitL "xξ1 xξ2"; iFrame.
      iIntros "[? ?]".
      iMod ("ty1own" with "[$]") as "[? ?]".
      iMod ("ty2own" with "[$]") as "[? ?]".
      by iFrame.
  Qed.

  Global Instance product2_lft_morphism {A B C} (T1 : type A → type B) (T2 : type A → type C):
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

  Global Instance product2_type_ne {A B C} (T1 : type A → type B) (T2 : type A → type C):
    TypeNonExpansive T1 → TypeNonExpansive T2 →
    TypeNonExpansive (λ ty, product2 (T1 ty) (T2 ty)).
  Proof.
    intros HT1 HT2. split.
    - apply _.
    - move=>ty1 ty2 /= ?.
      rewrite !(type_non_expansive_ty_size (T:=T1) ty1 ty2) //.
      rewrite !(type_non_expansive_ty_size (T:=T2) ty1 ty2) //.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs depth tid vl /=.
      by do 6 f_equiv; apply type_non_expansive_ty_own.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l l' /=.
      rewrite !(type_non_expansive_ty_size (T:=T1) ty1 ty2) //.
      by f_equiv; apply type_non_expansive_ty_shr.
  Qed.

  (* TODO : find a way to avoid this duplication. *)
  Global Instance product2_type_contractive {A B C} (T1 : type A → type B) (T2 : type A → type C):
    TypeContractive T1 → TypeContractive T2 →
    TypeContractive (λ ty, product2 (T1 ty) (T2 ty)).
  Proof.
    intros HT1 HT2. split.
    - apply _.
    - move=>ty1 ty2 /=.
      rewrite !(type_contractive_ty_size (T:=T1) ty1 ty2).
      by rewrite !(type_contractive_ty_size (T:=T2) ty1 ty2).
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs depth tid vl /=.
      by do 6 f_equiv; apply type_contractive_ty_own.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l l' /=.
      rewrite !(type_contractive_ty_size (T:=T1) ty1 ty2).
      by f_equiv; apply type_contractive_ty_shr.
  Qed.

  (* Global Instance product2_ne {A B} :
    NonExpansive2 (@product2 A B).
  Proof. 
    split.
    - pose proof (type_non_expansive_ty_size (A := (A * B)%type)). rewrite !(type_non_expansive_ty_size (T:=T1) ty1 ty2) //.
    rewrite !(type_non_expansive_ty_size (T:=T2) ty1 ty2) //.
  solve_ne_type. Qed. *)

  Global Instance product2_mono A B E L :
    Proper (subtype E L id ==> subtype E L id ==> subtype E L id) (@product2 A B).
  Proof.
    iIntros (ty11 ty12 H1 ty21 ty22 H2). iIntros (qL) "HL".
    iDestruct (H1 with "HL") as "#H1". iDestruct (H2 with "HL") as "#H2".
    iIntros "!> #HE".
    iDestruct ("H1" with "HE") as "(% & #Hout1 & #Ho1 & #Hs1)". iClear (H1) "H1".
    iDestruct ("H2" with "HE") as "(% & #Hout2 & #Ho2 & #Hs2)". iClear (H2) "H2".
    iSplit; first by (iPureIntro; simpl; f_equal). iSplit; [|iSplit; iModIntro].
    - rewrite !lft_intersect_list_app. by iApply lft_intersect_mono.
    - iIntros (????) "H /=". iDestruct "H" as (vl1 vl2) "(-> & Hown1 & Hown2)".
      iExists _, _. iSplit. done. iSplitL "Hown1".
      + by iApply "Ho1".
      + by iApply "Ho2".
    - iIntros (?????) "/= #[Hshr1 Hshr2]". iSplit.
      + by iApply "Hs1".
      + rewrite -(_ : ty_size ty11 = ty_size ty12) //. by iApply "Hs2".
  Qed.

  Global Instance product2_proper A B E L:
    Proper (eqtype E L id id ==> eqtype E L id id ==> eqtype E L id id) (@product2 A B).
  Proof. by intros ??[]??[]; split; apply product2_mono. Qed.

  Global Instance product2_copy {A B} `{!Copy ty1} `{!Copy ty2} :
    Copy (@product2 A B ty1 ty2).
  Proof.
    split; first (intros; apply _).
    intros depth κ tid E F l q ? HF. iIntros "#LFT [H1 H2] Htl [Htok1 Htok2]".
    iMod (@copy_shr_acc with "LFT H1 Htl Htok1")
      as (q1 vl1) "(Htl & H↦1 & #H1 & Hclose1)"; first solve_ndisj.
    { rewrite <-HF. apply shr_locsE_subseteq=>/=. lia. }
    iMod (@copy_shr_acc with "LFT H2 Htl Htok2")
      as (q2 vl2) "(Htl & H↦2 & #H2 & Hclose2)"; first solve_ndisj.
    { move: HF. rewrite /= -plus_assoc shr_locsE_shift.
      assert (shr_locsE l (ty_size ty1) ## shr_locsE (l +ₗ (ty_size ty1)) (ty_size ty2 + 1))
             by exact: shr_locsE_disj.
      set_solver. }
    iDestruct (na_own_acc with "Htl") as "[$ Htlclose]".
    { generalize (shr_locsE_shift l ty1.(ty_size) ty2.(ty_size))=>/=. set_solver+. }
    destruct (Qp_lower_bound q1 q2) as (qq & q'1 & q'2 & -> & ->).
    iExists qq, (vl1 ++ vl2). rewrite heap_mapsto_vec_app.
    iDestruct (ty_size_eq with "H1") as ">->".
    iDestruct "H↦1" as "[$ H↦1f]". iDestruct "H↦2" as "[$ H↦2f]".
    iSplitR; [by simpl; eauto 10|]. iIntros "!> Htl [H↦1 H↦2]".
    iDestruct ("Htlclose" with "Htl") as "Htl".
    iMod ("Hclose2" with "Htl [H2 H↦2f H↦2]") as "[Htl $]"; [by iFrame|].
    iApply ("Hclose1" with "Htl [H1 H↦1f H↦1]"). by iFrame.
  Qed.

  Global Instance product2_send {A B} `{!Send ty1} `{!Send ty2} :
    Send (@product2 A B ty1 ty2).
  Proof.
    iIntros (depth tid1 tid2 vl) "H".
    iDestruct "H" as (vl1 vl2 ->) "[Hown1 Hown2]".
    iExists _, _. iSplit; first done. iSplitL "Hown1"; by iApply @send_change_tid.
  Qed.

  Global Instance product2_sync {A B} `{!Sync ty1} `{!Sync ty2} :
    Sync (@product2 A B ty1 ty2).
  Proof.
    iIntros (κ tid1 ti2 l l') "[#Hshr1 #Hshr2]". iSplit; by iApply @sync_change_tid.
  Qed.

  (*
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
  Global Instance product_copy tys : ListCopy tys → Copy (product tys).
  Proof. induction 1; apply _. Qed.
  Global Instance product_send tys : ListSend tys → Send (product tys).
  Proof. induction 1; apply _. Qed.
  Global Instance product_sync tys : ListSync tys → Sync (product tys).
  Proof. induction 1; apply _. Qed.

  Definition product_cons ty tyl :
    product (ty :: tyl) = product2 ty (product tyl) := eq_refl _.
  Definition product_nil :
    product [] = unit0 := eq_refl _.
*)
End product.
(*
Notation Π := product.

Section typing.
  Context `{!typeG Σ}.

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
End typing.

Arguments product : simpl never.
Global Hint Resolve product_mono' product_proper' ty_outlives_E_elctx_sat_product
  : lrust_typing. *)
