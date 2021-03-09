From iris.proofmode Require Import tactics.
From iris.algebra Require Import list.
From iris.bi Require Import fractional.
From lrust.typing Require Export lft_contexts type.
Set Default Proof Using "Type".

Section sum.
  Context `{!typeG Σ}.

  (* We define the actual empty type as being the empty sum, so that it is
     convertible to it---and in particular, we can pattern-match on it
     (as in, pattern-match in the language of lambda-rust, not in Coq). *)
  Program Definition emp0 : type :=
    {| ty_size := 1%nat; ty_lfts := []; ty_E := [];
       ty_own depth tid vl := False%I; ty_shr κ tid l := False%I |}.
  Next Obligation. iIntros (???) "[]". Qed.
  Next Obligation. iIntros (?????) "[]". Qed.
  Next Obligation.
    iIntros (E depth κ l tid ??) "#LFT _ Hown Htok !>". iApply step_fupdN_intro=>//.
    iIntros "!>". iMod (bor_acc with "LFT Hown Htok") as "[>H _]"; first done.
    iDestruct "H" as (?) "[_ []]".
  Qed.
  Next Obligation. iIntros (κ κ' tid l) "#Hord []". Qed.

  Definition is_pad i tyl (vl : list val) : iProp Σ :=
    ⌜((nth i tyl emp0).(ty_size) + length vl)%nat = (max_list_with ty_size tyl)⌝%I.

  Lemma split_sum_mt l depth tid q tyl :
    (l ↦∗{q}: λ vl,
         ∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                               ⌜length vl = S (max_list_with ty_size tyl)⌝ ∗
                               (nth i tyl emp0).(ty_own) depth tid vl')%I
    ⊣⊢ ∃ (i : nat), (l ↦{q} #i ∗
                     (l +ₗ (S $ (nth i tyl emp0).(ty_size))) ↦∗{q}: is_pad i tyl) ∗
                              (l +ₗ 1) ↦∗{q}: (nth i tyl emp0).(ty_own) depth tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[Hmt Hown]". iDestruct "Hown" as (i vl' vl'') "(% & % & Hown)".
      subst. iExists i. iDestruct (heap_mapsto_vec_cons with "Hmt") as "[$ Hmt]".
      iDestruct (ty_size_eq with "Hown") as "#EQ". iDestruct "EQ" as %Hvl'.
      iDestruct (heap_mapsto_vec_app with "Hmt") as "[Hmt Htail]". iSplitL "Htail".
      + iExists vl''. rewrite (shift_loc_assoc_nat _ 1) Hvl'. iFrame. iPureIntro.
        rewrite -Hvl'. simpl in *. rewrite -app_length. congruence.
      + iExists vl'. by iFrame.
    - iDestruct "H" as (i) "[[Hmt1 Htail] Hown]".
      iDestruct "Hown" as (vl') "[Hmt2 Hown]". iDestruct "Htail" as (vl'') "[Hmt3 %]".
      iDestruct (ty_size_eq with "Hown") as "#EQ". iDestruct "EQ" as %Hvl'.
      iExists (#i::vl'++vl'').
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app (shift_loc_assoc_nat _ 1) Hvl'.
      iFrame. iExists i, vl', vl''. iSplit; first done. iFrame. iPureIntro.
      simpl. f_equal. by rewrite app_length Hvl'.
  Qed.

  Program Definition sum (tyl : list type) :=
    {| ty_size := S (max_list_with ty_size tyl);
       ty_lfts := tyl_lfts tyl; ty_E := tyl_E tyl;
       ty_own depth tid vl :=
         (∃ (i : nat) vl' vl'', ⌜vl = #i :: vl' ++ vl''⌝ ∗
                                ⌜length vl = S (max_list_with ty_size tyl)⌝ ∗
                                (nth i tyl emp0).(ty_own) depth tid vl')%I;
       ty_shr κ tid l :=
         (∃ (i : nat),
           &frac{κ} (λ q, l ↦{q} #i ∗
                     (l +ₗ (S $ (nth i tyl emp0).(ty_size))) ↦∗{q}: is_pad i tyl) ∗
               (nth i tyl emp0).(ty_shr) κ tid (l +ₗ 1))%I
    |}.
  Next Obligation.
    iIntros (tyl depth tid vl) "Hown". iDestruct "Hown" as (i vl' vl'') "(%&%&_)".
    subst. done.
  Qed.
  Next Obligation.
    move=>tyl depth1 depth2 tid vl Hdepth /=.
    iDestruct 1 as (i vl' vl'' -> [= EQl]) "?". iExists _, _, _. rewrite /= EQl.
    do 2 (iSplitR; [done|]). by iApply ty_own_depth_mono.
  Qed.
  Next Obligation.
    intros tyl E depth κ l tid. iIntros (??) "#LFT #Houtlives Hown Htok". rewrite split_sum_mt.
    iMod (bor_exists with "LFT Hown") as (i) "Hown"; first solve_ndisj.
    iMod (bor_sep with "LFT Hown") as "[Hmt Hown]"; first solve_ndisj.
    iMod ((nth i tyl emp0).(ty_share) with "LFT [] Hown Htok") as "H"; try done.
    { destruct (decide (i < length tyl)%nat) as [Hi|].
      - iApply lft_incl_trans; [done|]. iClear "Houtlives LFT".
        iInduction tyl as [|ty tyl] "IH" forall (i Hi); [simpl in Hi; lia|].
        simpl in Hi. rewrite /= lft_intersect_list_app. destruct i.
        + iApply lft_intersect_incl_l.
        + iApply lft_incl_trans; [|iApply "IH"; auto with lia].
          iApply lft_intersect_incl_r.
      - rewrite nth_overflow; [|lia]. iApply lft_incl_static. }
    iModIntro. iApply (step_fupdN_wand with "H"). iIntros ">[#Hshr $]".
    iMod (bor_fracture with "LFT [Hmt]") as "H'"; first solve_ndisj; last eauto.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (tyl κ κ' tid l) "#Hord H".
    iDestruct "H" as (i) "[Hown0 Hown]". iExists i.
    iSplitL "Hown0".
    - by iApply (frac_bor_shorten with "Hord").
    - iApply ((nth i tyl emp0).(ty_shr_mono) with "Hord"); done.
  Qed.

  Global Instance sum_ne : NonExpansive sum.
  Proof.
    intros n x y EQ.
    assert (EQmax : max_list_with ty_size x = max_list_with ty_size y).
    { induction EQ as [|???? EQ _ IH]=>//=.
      rewrite IH. f_equiv. apply EQ. }
    (* TODO: If we had the right lemma relating nth, (Forall2 R) and R, we should
       be able to make this more automatic. *)
    assert (EQnth :∀ i, type_dist n (nth i x emp0) (nth i y emp0)).
    { clear EQmax. induction EQ as [|???? EQ _ IH]=>-[|i] //=. }
    constructor; simpl.
    - by rewrite EQmax.
    - clear -EQ. induction EQ as [|???? EQ _ IH]=>//=.
      rewrite /tyl_lfts /=. f_equiv; [|done]. apply EQ.
    - clear -EQ. induction EQ as [|???? EQ _ IH]=>//=.
      rewrite /tyl_E /=. f_equiv; [|done]. apply EQ.
    - intros tid vl. rewrite EQmax.
      solve_proper_core ltac:(fun _ => exact:EQnth || f_equiv).
    - intros κ tid l. unfold is_pad. rewrite EQmax.
      solve_proper_core ltac:(fun _ => exact:EQnth || (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Lemma product_lft_morphism Tl:
    Forall TypeLftMorphism Tl →
    TypeLftMorphism (λ ty, sum ((λ T, T ty) <$> Tl)).
  Proof.
    intros HTl.
    assert (let s ty := sum ((λ T, T ty) <$> Tl) in
        (∃ α βs E, (∀ ty, ⊢ ty_lft (s ty) ≡ₗ α ⊓ ty_lft ty) ∧
            (∀ ty, elctx_interp (s ty).(ty_E) ⊣⊢
                   elctx_interp E ∗ elctx_interp ty.(ty_E) ∗
                   [∗ list] β ∈ βs, β ⊑ ty_lft ty)) ∨
        (∃ α E, (∀ ty, ⊢ ty_lft (s ty) ≡ₗ α) ∧
                (∀ ty, elctx_interp (s ty).(ty_E) ⊣⊢ elctx_interp E)))
      as [(?&?&?&?&?)|(?&?&?&?)]; [|by eleft|by eright].
    simpl. induction HTl as [|T Tl HT HTl [(α & βs & E & Hα & HE)|(α & E & Hα & HE)]]=>/=.
    - right. exists static, []. split=>_ //. iApply lft_equiv_refl.
    - setoid_rewrite lft_intersect_list_app.
      destruct HT as [α' βs' E' Hα' HE'|α' E' Hα' HE'].
      + left. exists (α' ⊓ α), (βs' ++ βs), (E' ++ E). split.
        * intros ty. iApply lft_equiv_trans.
          { iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα]. }
          rewrite -!assoc (comm (⊓) (ty_lft ty) (α ⊓ _)) -!assoc.
          repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
          iApply lft_intersect_equiv_idemp.
        * intros ty.
          rewrite /tyl_E /= !elctx_interp_app HE' HE big_sepL_app -!assoc.
          iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
      + left. exists (α' ⊓ α), βs, (E' ++ E). split.
        * intros ty. rewrite -assoc.
          iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
        * intros ty.
          by rewrite /tyl_E /= !elctx_interp_app HE' HE -!assoc.
    - setoid_rewrite lft_intersect_list_app.
      destruct HT as [α' βs' E' Hα' HE'|α' E' Hα' HE'].
      + left. exists (α' ⊓ α), βs', (E' ++ E). split.
        * intros ty. rewrite -!assoc (comm (⊓) α (ty_lft ty)) !assoc.
          iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
        * intros ty. rewrite /tyl_E /= !elctx_interp_app HE' HE -!assoc.
          iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
      + right. exists (α' ⊓ α), (E' ++ E). split.
        * intros. iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
        * intros. by rewrite /tyl_E /= !elctx_interp_app HE HE'.
  Qed.

  Global Instance sum_type_ne Tl:
    TypeListNonExpansive Tl → TypeNonExpansive (sum ∘ Tl).
  Proof.
    intros (Tl' & HTlTl' & HTl').
    eapply type_ne_ext; last first.
    { intros ty. by rewrite /= HTlTl'. }
    clear Tl HTlTl'.
    assert (Hsz0 : ∀ ty1 ty2, ty_size ty1 = ty_size ty2 →
      max_list_with ty_size ((λ T, T ty1) <$> Tl') =
      max_list_with ty_size ((λ T, T ty2) <$> Tl')).
    { intros ty1 ty2 Hsz.
      induction HTl' as [|T Tl' HT HTl' IH]=>//=. rewrite IH. f_equal. by apply HT. }
    split.
    - apply product_lft_morphism. eapply Forall_impl; [done|]. apply _.
    - intros. simpl. f_equiv. auto.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs depth tid vl /=. f_equiv=>i. do 6 f_equiv.
      + do 3 f_equiv. by apply Hsz0.
      + rewrite !nth_lookup !list_lookup_fmap.
        rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
        destruct (Tl' !! i)=>//=. by apply HTl'.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l /=. f_equiv=>i.
      rewrite /is_pad !nth_lookup !list_lookup_fmap.
      rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
      destruct (Tl' !! i); [|by rewrite !right_absorb]. simpl.
      repeat ((by apply HTl') || (by apply Hsz0) || f_equiv).
  Qed.

  (* TODO : get rid of this duplication *)
  Global Instance sum_type_ne_cont Tl:
    TypeListContractive Tl → TypeContractive (sum ∘ Tl).
  Proof.
    intros (Tl' & HTlTl' & HTl').
    eapply type_contractive_ext; last first.
    { intros ty. by rewrite /= HTlTl'. }
    clear Tl HTlTl'.
    assert (Hsz0 : ∀ ty1 ty2,
      max_list_with ty_size ((λ T, T ty1) <$> Tl') =
      max_list_with ty_size ((λ T, T ty2) <$> Tl')).
    { intros ty1 ty2.
      induction HTl' as [|T Tl' HT HTl' IH]=>//=. rewrite IH. f_equal. by apply HT. }
    split.
    - apply product_lft_morphism. eapply Forall_impl; [done|]. apply _.
    - intros. simpl. f_equiv. auto.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs depth tid vl /=. f_equiv=>i. do 6 f_equiv.
      + do 3 f_equiv. by apply Hsz0.
      + rewrite !nth_lookup !list_lookup_fmap.
        rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
        destruct (Tl' !! i)=>//=. by apply HTl'.
    - move=> n ty1 ty2 Hsz Hl HE Ho Hs κ tid l /=. f_equiv=>i.
      rewrite /is_pad !nth_lookup !list_lookup_fmap.
      rewrite ->Forall_lookup in HTl'. specialize (HTl' i).
      destruct (Tl' !! i); [|by rewrite !right_absorb]. simpl.
      repeat ((by apply HTl') || (by apply Hsz0) || f_equiv).
  Qed.

  Global Instance sum_mono E L :
    Proper (Forall2 (subtype E L) ==> subtype E L) sum.
  Proof.
    iIntros (tyl1 tyl2 Htyl qL) "HL".
    iAssert (□ (lft_contexts.elctx_interp E -∗ ⌜max_list_with ty_size tyl1 = max_list_with ty_size tyl2⌝))%I with "[#]" as "#Hleq".
    { iInduction Htyl as [|???? Hsub] "IH".
      { iClear "∗". iIntros "!# _". done. }
      iDestruct (Hsub with "HL") as "#Hsub". iDestruct ("IH" with "HL") as "{IH} #IH".
      iModIntro. iIntros "#HE". iDestruct ("Hsub" with "HE") as "(% & _ & _)".
      iDestruct ("IH" with "HE") as %IH. iPureIntro. simpl. inversion_clear IH. by f_equal. }
    iDestruct (subtype_Forall2_llctx with "HL") as "#Htyl"; first done.
    iClear "HL". iIntros "!# #HE".
    iDestruct ("Hleq" with "HE") as %Hleq. iSpecialize ("Htyl" with "HE"). iClear "Hleq HE".
    iAssert (∀ i, type_incl (nth i tyl1 emp0) (nth i tyl2 emp0))%I with "[#]" as "#Hty".
      { iIntros (i). edestruct (nth_lookup_or_length tyl1 i) as [Hl1|Hl]; last first.
        { rewrite nth_overflow // nth_overflow; first by iApply type_incl_refl.
          by erewrite <-Forall2_length. }
        edestruct @Forall2_lookup_l as (ty2 & Hl2 & _); [done..|].
        iDestruct (big_sepL_lookup with "Htyl") as "Hty".
        { rewrite lookup_zip_with. erewrite Hl1. simpl.
          rewrite Hl2 /=. done. }
        rewrite (nth_lookup_Some tyl2 _ _ ty2) //. }
    apply Forall2_length in Htyl.
    clear -Hleq Htyl. iSplit; [|iSplit; [|iSplit]].
    - simpl. by rewrite Hleq.
    - iClear (Hleq) "Hty".
      iInduction tyl1 as [|ty1 tyl1 IH] "IH" forall (tyl2 Htyl);
           destruct tyl2 as [|ty2 tyl2]=>//=.
      + iApply lft_incl_refl.
      + iDestruct "Htyl" as "[Hty Htyl]".
        rewrite !lft_intersect_list_app.
        iApply lft_intersect_mono; [|by iApply "IH"; auto].
        iDestruct "Hty" as "(_ & $ & _ & _)".
    - iModIntro. iIntros (depth tid vl) "H". iDestruct "H" as (i vl' vl'') "(-> & % & Hown)".
      iExists i, vl', vl''. iSplit; first done.
      iSplit; first by rewrite -Hleq.
      iDestruct ("Hty" $! i) as "(_ & _ & #Htyi & _)". by iApply "Htyi".
    - iModIntro. iIntros (κ tid l) "H". iDestruct "H" as (i) "(Hmt & Hshr)".
      iExists i. iSplitR "Hshr".
      + rewrite /is_pad -Hleq. iDestruct ("Hty" $! i) as "(Hlen & _)".
        iDestruct "Hlen" as %<-. done.
      + iDestruct ("Hty" $! i) as "(_ & _ & _ & #Htyi)". by iApply "Htyi".
  Qed.
  Lemma sum_mono' E L tyl1 tyl2 :
    Forall2 (subtype E L) tyl1 tyl2 → subtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_mono. Qed.
  Global Instance sum_proper E L :
    Proper (Forall2 (eqtype E L) ==> eqtype E L) sum.
  Proof.
    intros tyl1 tyl2 Heq; split; eapply sum_mono; [|rewrite -Forall2_flip];
      (eapply Forall2_impl; [done|by intros ?? []]).
  Qed.
  Lemma sum_proper' E L tyl1 tyl2 :
    Forall2 (eqtype E L) tyl1 tyl2 → eqtype E L (sum tyl1) (sum tyl2).
  Proof. apply sum_proper. Qed.

  Lemma nth_empty {A : Type} i (d : A) :
    nth i [] d = d.
  Proof. by destruct i. Qed.

  Global Instance sum_copy tyl : ListCopy tyl → Copy (sum tyl).
  Proof.
    intros HFA. split.
    - intros depth tid vl.
      cut (∀ i vl', Persistent ((nth i tyl emp0).(ty_own) depth tid vl')). by apply _.
      intros. apply @copy_persistent.
      edestruct nth_in_or_default as [| ->]; [by eapply List.Forall_forall| ].
      split; first by apply _. iIntros (?????????) "? []".
    - intros depth κ tid E F l q ? HF.
      iIntros "#LFT #H Htl [Htok1 Htok2]". iDestruct "H" as (i) "[Hfrac Hshr]".
      iMod (frac_bor_acc with "LFT Hfrac Htok1")
        as (q'1) "[>[H↦i Hpad] Hclose]"; first solve_ndisj.
      iDestruct "Hpad" as (pad) "[Hpad %]".
      assert (Copy (nth i tyl emp0)).
      { edestruct nth_in_or_default as [| ->]; first by eapply List.Forall_forall.
        split; first by apply _. iIntros (?????????) "? []". }
      iMod (@copy_shr_acc _ _ (nth i tyl emp0) with "LFT Hshr Htl Htok2")
        as (q'2 vl) "(Htl & H↦C & #HownC & Hclose')"; try done.
      { rewrite <-HF. simpl. rewrite <-union_subseteq_r.
        apply shr_locsE_subseteq. lia. }
      iDestruct (na_own_acc with "Htl") as "[$ Htlclose]".
      { apply difference_mono_l.
        trans (shr_locsE (l +ₗ 1) (max_list_with ty_size tyl)).
        - apply shr_locsE_subseteq. lia.
        - set_solver+. }
      destruct (Qp_lower_bound q'1 q'2) as (q' & q'01 & q'02 & -> & ->).
      iExists q', (#i :: vl ++ pad).
      rewrite heap_mapsto_vec_cons heap_mapsto_vec_app shift_loc_assoc
              -Nat.add_1_l Nat2Z.inj_add.
      iDestruct "H↦i" as "[$ H↦if]". iDestruct "H↦C" as "[$ H↦Cf]".
      iDestruct (ty_size_eq with "HownC") as ">->".
      iDestruct "Hpad" as "[$ Hpadf]". iSplitR.
      { iExists _, _, _. iSplitR; [done|]. iFrame "HownC". rewrite /= app_length.
        iDestruct (ty_size_eq with "HownC") as ">->". auto. }
      iIntros "!> Htl (H↦i & H↦C & Hpad)". iDestruct ("Htlclose" with "Htl") as "Htl".
      iMod ("Hclose'" with "Htl [$H↦Cf $H↦C]") as "[$$]". iApply "Hclose".
      iFrame. iExists pad. by iFrame.
  Qed.

  Global Instance sum_send tyl : ListSend tyl → Send (sum tyl).
  Proof.
    iIntros (Hsend depth tid1 tid2 vl) "H".
    iDestruct "H" as (i vl' vl'') "(% & % & Hown)".
    iExists _, _, _. iSplit; first done. iSplit; first done.
    iApply @send_change_tid; last done.
    edestruct nth_in_or_default as [| ->]; first by eapply List.Forall_forall.
    iIntros (????) "[]".
  Qed.

  Global Instance sum_sync tyl : ListSync tyl → Sync (sum tyl).
  Proof.
    iIntros (Hsync κ tid1 tid2 l) "H". iDestruct "H" as (i) "[Hframe Hown]".
    iExists _. iFrame "Hframe". iApply @sync_change_tid; last done.
    edestruct nth_in_or_default as [| ->]; first by eapply List.Forall_forall.
    iIntros (????) "[]".
  Qed.

  Definition emp_type := sum [].

  Global Instance emp_type_empty : Empty type := emp_type.
End sum.

(* Σ is commonly used for the current functor. So it cannot be defined
   as Π for products. We stick to the following form. *)
Notation "Σ[ ty1 ; .. ; tyn ]" :=
  (sum (cons ty1%T (..(cons tyn%T nil)..))) : lrust_type_scope.

Global Hint Resolve sum_mono' sum_proper' : lrust_typing.
