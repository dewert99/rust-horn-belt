From lrust.lang Require Import proofmode.
From lrust.typing Require Export lft_contexts type bool.
Set Default Proof Using "Type".
Import uPred.

Module fixpoint_defs.
Section S.
  Context `{!typeG Σ} (T : type → type) {HT: TypeContractive T}.

  Definition Tn n := Nat.iter (S n) T bool.

  Lemma Tn_ty_lft_const n n' : ⊢ (Tn n).(ty_lft) ≡ₗ (Tn n').(ty_lft).
  Proof using HT.
    assert (∀ n, ⊢ (Tn n).(ty_lft) ≡ₗ (T bool).(ty_lft)) as H.
    { clear -HT=>n. destruct type_contractive_type_lft_morphism as [α βs E Hα HE|α E Hα HE].
      - induction n as [|n IH]; simpl in *.
        + iApply lft_equiv_refl.
        + unfold Tn. simpl.
          iApply lft_equiv_trans; [iApply type_lft_morphism_lft_equiv_proper; iApply IH|].
          iApply lft_equiv_trans; [iApply Hα|].
          iApply lft_equiv_trans.
          { iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply Hα]. }
          iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
          rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
          iApply lft_intersect_equiv_idemp.
      - iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_sym. iApply Hα. }
    iApply lft_equiv_trans; [|iApply lft_equiv_sym]; iApply H.
  Qed.

  Lemma Tn_ty_E_const n n' :
    elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn (S n')).(ty_E).
  Proof using HT.
    assert (H0 : ∀ n, elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn 1).(ty_E));
      last by rewrite !H0.
    clear n n'. unfold Tn. intro n.
    destruct type_contractive_type_lft_morphism as [α βs E Hα HE|α E Hα HE].
    - induction n as [|n IH]=>//. simpl in *.
      rewrite (HE (Tn (S n))) IH !HE !assoc -!persistent_sep_dup -!assoc.
      iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
      iApply (big_sepL_impl with "H"). iIntros "!# * _". iIntros "#?".
      iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const (S n) 0) as "[_ $]".
    - by rewrite !HE.
  Qed.

  Lemma Tn_cauchy n i :
    (n ≤ i)%nat →
    (∀ depth tid vl, dist_later n ((Tn (2 + i)).(ty_own) depth tid vl)
                                  ((Tn (2 + n)).(ty_own) depth tid vl)) ∧
    (∀ κ tid l, (Tn (2 + i)).(ty_shr) κ tid l ≡{n}≡ (Tn (2 + n)).(ty_shr) κ tid l).
  Proof using HT.
    revert i. unfold Tn. induction n as [|n IH]=>i Hni /=.
    - split=>//. apply HT=>//.
      + apply type_contractive_ty_size.
      + apply (Tn_ty_lft_const (S i) 1).
      + apply (Tn_ty_E_const i 0).
    - destruct i; [lia|]. destruct (IH i) as [Hown Hshr]; [lia|].
      split; apply HT=>//;
       (apply type_contractive_ty_size || apply (Tn_ty_lft_const (2 + i) (2 + n)) ||
        apply (Tn_ty_E_const (S i) (S n))).
  Qed.
  Program Definition own_shr_chain :=
    {| chain_car n := ((Tn (3 + n)).(ty_own), (Tn (3 + n)).(ty_shr)) :
               prodO (nat -d> thread_id -d> list val -d> iPropO Σ)
                     (lft -d> thread_id -d> loc -d> iPropO Σ) |}.
  Next Obligation.
    intros n i Hni. split=>/=.
    - intros ???. apply (Tn_cauchy (S _)). lia.
    - intros ???. apply dist_S, Tn_cauchy. lia.
  Qed.

  Program Definition Tn' n :=
    {| ty_size := (T bool).(ty_size);
       ty_lfts := (T bool).(ty_lfts); ty_E := (Tn 1).(ty_E);
       ty_own := (Tn n).(ty_own); ty_shr := (Tn n).(ty_shr) |}.
  Next Obligation.
    intros. rewrite ty_size_eq /Tn /=. iIntros "-> !%".
    apply type_contractive_ty_size.
  Qed.
  Next Obligation. intros. by apply ty_own_depth_mono. Qed.
  Next Obligation.
    iIntros (????????) " #LFT #Hκ /=". iApply (ty_share with "LFT")=>//.
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.
  Next Obligation. intros n. apply ty_shr_mono. Qed.

  Program Definition type_fixpoint : type :=
    {| ty_size := (T bool).(ty_size);
       ty_lfts := (T bool).(ty_lfts); ty_E := (Tn 1).(ty_E);
       ty_own := (compl own_shr_chain).1; ty_shr := (compl own_shr_chain).2 |}.
  Next Obligation.
    intros. apply @limit_preserving, _.
    apply limit_preserving_Persistent=>??? EQ. apply EQ.
  Qed.
  Next Obligation.
    intros. apply @limit_preserving.
    - apply limit_preserving_entails; [|solve_proper]. intros ??? EQ. apply EQ.
    - intros n. apply (Tn' _).(ty_size_eq).
  Qed.
  Next Obligation.
    intros. apply @limit_preserving.
    - apply limit_preserving_entails=>??? EQ; apply EQ.
    - intros n. by apply ty_own_depth_mono.
  Qed.
  Next Obligation.
    intros. apply @limit_preserving.
    - apply limit_preserving_entails; [solve_proper|].
      intros ??? EQ. do 4 f_equiv; [do 2 f_equiv; apply EQ|].
      induction depth as [|depth IH]; simpl; [|by rewrite IH].
      do 2 f_equiv; apply EQ.
    - intros n. by apply (Tn' _).(ty_share).
  Qed.
  Next Obligation.
    intros. apply @limit_preserving.
    - apply limit_preserving_entails; [solve_proper|].
      intros ??? EQ. repeat (apply EQ || f_equiv).
    - intros n. apply ty_shr_mono.
  Qed.

  Lemma type_fixpoint_Tn'_dist n :
    type_fixpoint ≡{n}≡ Tn' (3 + n).
  Proof. split=>//; intros; apply conv_compl. Qed.
End S.
End fixpoint_defs.

Notation type_fixpoint := fixpoint_defs.type_fixpoint.

Lemma fixpoint_unfold_eqtype `{!typeG Σ} (T : type → type) {HT: TypeContractive T} E L :
  eqtype E L (type_fixpoint T) (T (type_fixpoint T)).
Proof.
  intros. apply eqtype_unfold=>qL.
  assert (Ho : ∀ n depth tid vl,
     (T $ fixpoint_defs.Tn T (3 + n)).(ty_own) depth tid vl ≡
     (T $ fixpoint_defs.Tn' T (3 + n)).(ty_own) depth tid vl).
  { intros. apply equiv_dist=>n'. apply HT=>//.
    - apply HT.
    - apply (fixpoint_defs.Tn_ty_lft_const T (3 + n) 0).
    - apply (fixpoint_defs.Tn_ty_E_const T (2 + n) 0). }
  assert (Hs : ∀ n κ tid l, (T $ fixpoint_defs.Tn T (2 + n)).(ty_shr) κ tid l ≡
                            (T $ fixpoint_defs.Tn' T (2 + n)).(ty_shr) κ tid l).
  { intros. apply equiv_dist=>n'. apply HT=>//.
    - apply HT.
    - apply (fixpoint_defs.Tn_ty_lft_const T (2 + n) 0).
    - apply (fixpoint_defs.Tn_ty_E_const T (1 + n) 0).
    - destruct n' as [|[|n']]=>//. }
  assert (Ho' :
    ∀ depth tid vl,
      (type_fixpoint T).(ty_own) depth tid vl ≡ (T (type_fixpoint T)).(ty_own) depth tid vl).
  { intros. apply equiv_dist=>n. etrans; [apply dist_S, conv_compl|].
    rewrite /= (Ho n). symmetry. apply HT=>//.
    - iApply lft_equiv_refl.
    - intros. destruct n as [|n]=>//=.
      destruct (fixpoint_defs.type_fixpoint_Tn'_dist T (S n)) as [_ _ _ HTn' _].
      apply dist_S, HTn'.
    - intros. destruct (fixpoint_defs.type_fixpoint_Tn'_dist T n) as [_ _ _ _ HTn'].
      apply HTn'. }
  assert (Hs' :
    ∀ κ tid l, (type_fixpoint T).(ty_shr) κ tid l ≡ (T (type_fixpoint T)).(ty_shr) κ tid l).
  { intros. apply equiv_dist=>n. etrans; [apply conv_compl|].
    rewrite /= (Hs n). symmetry. apply HT=>//.
    - iApply lft_equiv_refl.
    - intros. destruct n as [|[|n]]=>//=.
      destruct (fixpoint_defs.type_fixpoint_Tn'_dist T (S n)) as [_ _ _ HTn' _].
      apply dist_S, HTn'.
    - intros. destruct n as [|n]; [done|].
      destruct (fixpoint_defs.type_fixpoint_Tn'_dist T n) as [_ _ _ _ HTn']. apply HTn'. }
  iIntros "_ !# _"; iSplit; [|iSplit; [|iSplit; iIntros "!# *"]].
  - iPureIntro. apply HT.
  - destruct type_contractive_type_lft_morphism as [α βs E' Hα HE'|α E' Hα HE'].
    + iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα]. simpl.
      iApply lft_equiv_trans; [iApply Hα|].
      iApply lft_equiv_trans; [|
        iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|
                                            iApply lft_equiv_sym; iApply Hα]].
      rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
      iApply lft_equiv_sym. iApply lft_intersect_equiv_idemp.
    + iApply lft_equiv_trans; [iApply Hα|iApply lft_equiv_sym; iApply Hα].
  - rewrite Ho'. by iApply (bi.iff_refl True%I).
  - rewrite Hs'. by iApply (bi.iff_refl True%I).
Qed.

Lemma type_fixpoint_ne `{!typeG Σ} (T1 T2 : type → type)
    `{!TypeContractive T1, !NonExpansive T1, !TypeContractive T2} n :
  (∀ t, T1 t ≡{n}≡ T2 t) → type_fixpoint T1 ≡{n}≡ type_fixpoint T2.
Proof.
  intros EQ.
  assert (EQ' : compl (fixpoint_defs.own_shr_chain T1) ≡{n}≡
                compl (fixpoint_defs.own_shr_chain T2)).
  { assert (EQ' : fixpoint_defs.Tn T1 (3 + n) ≡{n}≡ fixpoint_defs.Tn T2 (3 + n)).
    { unfold fixpoint_defs.Tn.
      induction (S (3 + n))%nat as [|k IH]=>//. rewrite !Nat_iter_S IH EQ //. }
    etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl]. simpl.
    by split; repeat intro; simpl; f_equiv. }
  unfold type_fixpoint. split; simpl.
  - apply EQ.
  - apply EQ.
  - by rewrite /fixpoint_defs.Tn /= (EQ bool) EQ.
  - apply EQ'.
  - apply EQ'.
Qed.

Lemma type_fixpoint_type_ne `{!typeG Σ} (T : type → type → type)
      `{!(∀ ty, TypeContractive (T ty))}
  : (∀ `{!TypeNonExpansive U}, TypeNonExpansive (λ ty, T ty (U ty))) →
    TypeNonExpansive (λ ty, type_fixpoint (T ty)).
Proof.
  intros HT.
  assert (Hne : ∀ n, TypeNonExpansive (λ ty, fixpoint_defs.Tn (T ty) n)).
  { intros n. induction n as [|n IH]; [apply HT, _|apply HT, IH]. }
  split; simpl.
  - destruct (type_non_expansive_type_lft_morphism (T:=λ ty, T ty (T ty bool)))
    as [α βs E Hα HE|α E Hα HE].
    + eapply (type_lft_morphism_add _ α βs E), HE.
      intros. iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (fixpoint_defs.Tn_ty_lft_const _ 1 0).
    + eapply (type_lft_morphism_const _ α E), HE.
      intros. iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (fixpoint_defs.Tn_ty_lft_const _ 1 0).
  - apply HT, _.
  - intros. etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
    by apply Hne.
  - intros. etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
    by apply Hne.
Qed.

Lemma type_fixpoint_contracive `{!typeG Σ} (T : type → type → type)
      `{!(∀ ty, TypeContractive (T ty))}
  : (∀ `{!TypeContractive U}, TypeContractive (λ ty, T ty (U ty))) →
    TypeContractive (λ ty, type_fixpoint (T ty)).
Proof.
  intros HT.
  assert (Hne : ∀ n, TypeContractive (λ ty, fixpoint_defs.Tn (T ty) n)).
  { intros n. induction n as [|n IH]; [apply HT, _|apply HT, IH]. }
  split; simpl.
  - destruct (type_non_expansive_type_lft_morphism (T:=λ ty, T ty (T ty bool)))
    as [α βs E Hα HE|α E Hα HE].
    + eapply (type_lft_morphism_add _ α βs E), HE.
      intros. iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (fixpoint_defs.Tn_ty_lft_const (T ty) 1 0).
    + eapply (type_lft_morphism_const _ α E), HE.
      intros. iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (fixpoint_defs.Tn_ty_lft_const (T ty) 1 0).
  - apply HT, _.
  - intros. etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
    by apply Hne.
  - intros. etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
    by apply Hne.
Qed.

Section fixpoint.
  Context `{!typeG Σ}.
  Context (T : type → type) {HT: TypeContractive T}.

  Global Instance fixpoint_copy :
    (∀ `(!Copy ty), Copy (T ty)) → Copy (type_fixpoint T).
  Proof.
    intros ?. assert (∀ n, Copy (fixpoint_defs.Tn T n)); [by induction n; apply _|].
    split; rewrite /type_fixpoint /=.
    - intros depth tid vl. eapply @limit_preserving; [|simpl; apply _].
      apply limit_preserving_Persistent=>??? EQ. apply EQ.
    - pattern (compl (fixpoint_defs.own_shr_chain T)). eapply @limit_preserving.
      { repeat apply limit_preserving_forall=>?.
        apply limit_preserving_entails; [solve_proper|]=>??? EQ.
        repeat f_equiv; apply EQ. }
      intros n.
      rewrite (_ : (T bool).(ty_size) = (fixpoint_defs.Tn T (3 + n)).(ty_size)); last first.
      { rewrite /fixpoint_defs.Tn /=. apply type_contractive_ty_size. }
      simpl. apply copy_shr_acc.
  Qed.

  Global Instance fixpoint_send :
    (∀ `(!Send ty), Send (T ty)) → Send (type_fixpoint T).
  Proof.
    intros ?. assert (∀ n, Send (fixpoint_defs.Tn T n)); [by induction n; apply _|].
    rewrite /type_fixpoint => depth tid1 tid2 vl /=. eapply @limit_preserving.
    - apply limit_preserving_entails=>??? EQ; apply EQ.
    - intros n. simpl. apply send_change_tid.
  Qed.

  Global Instance fixpoint_sync :
    (∀ `(!Sync ty), Sync (T ty)) → Sync (type_fixpoint T).
  Proof.
    intros ?. assert (∀ n, Sync (fixpoint_defs.Tn T n)); [by induction n; apply _|].
    rewrite /type_fixpoint => κ tid1 tid2 vl /=. eapply @limit_preserving.
    - apply limit_preserving_entails=>??? EQ; apply EQ.
    - intros n. simpl. apply sync_change_tid.
  Qed.
End fixpoint.

Section subtyping.
  Context `{!typeG Σ} (E : elctx) (L : llctx).

  (* TODO : is there a way to declare these as a [Proper] instances ? *)
  Lemma fixpoint_mono T1 `{!TypeContractive T1} T2 `{!TypeContractive T2} :
    (∀ ty1 ty2, subtype E L ty1 ty2 → subtype E L (T1 ty1) (T2 ty2)) →
    subtype E L (type_fixpoint T1) (type_fixpoint T2).
  Proof.
    intros H12 qL.
    assert (Hwand_forall : ∀ P (Φ : nat → iProp Σ), (∀ n, P -∗ Φ n) ⊢ (P -∗ ∀ n, Φ n)).
    { iIntros (P Φ) "H HP %". iApply ("H" with "HP"). }
    assert (Hsub : llctx_interp L qL
      -∗ □ (elctx_interp E -∗
         ∀ n, type_incl (Nat.iter (S n) T1 bool) (Nat.iter (S n) T2 bool))).
    { rewrite intuitionistically_into_persistently -Hwand_forall
              persistently_forall. apply forall_intro=>n.
      rewrite -intuitionistically_into_persistently.
      revert qL. apply H12. induction n as [|n IH]=>//. by apply H12. }
    rewrite Hsub /type_incl -!persistent_and_sep /=. f_equiv. f_equiv.
    (* FIXME : change the definition of limit_preserving so that it
       applies even if the limti is not computed with compl. *)
    assert (Hentails_equiv : ∀ P Q : iProp Σ, (P ⊣⊢ P ∧ Q) ↔ (P ⊢ Q)).
    { intros P Q; split; [by iIntros (->) "[_ $]"|].
      intros HPQ. iSplit; [|by iIntros "[$ _]"]. iIntros "H". iSplit; [done|].
      by iApply HPQ. }
    apply and_intro; [|apply and_intro; [|apply and_intro]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($ & _ & _ & _)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_ & $ & _ & _)".
    - apply Hentails_equiv, equiv_dist=>n. setoid_rewrite conv_compl; simpl.
      apply equiv_dist, Hentails_equiv. iIntros "H".
      iDestruct ("H" $! _) as "(_ & _ & $ & _)".
    - apply Hentails_equiv, equiv_dist=>n. setoid_rewrite conv_compl; simpl.
      apply equiv_dist, Hentails_equiv. iIntros "H".
      iDestruct ("H" $! _) as "(_ & _ & _ & $)".
  Qed.

  Lemma fixpoint_proper T1 `{!TypeContractive T1} T2 `{!TypeContractive T2} :
    (∀ ty1 ty2, eqtype E L ty1 ty2 → eqtype E L (T1 ty1) (T2 ty2)) →
    eqtype E L (type_fixpoint T1) (type_fixpoint T2).
  Proof.
    intros H12. apply eqtype_unfold=>qL.
    assert (Hwand_forall : ∀ P (Φ : nat → iProp Σ), (∀ n, P -∗ Φ n) ⊢ (P -∗ ∀ n, Φ n)).
    { iIntros (P Φ) "H HP %". iApply ("H" with "HP"). }
    assert (Hsub : llctx_interp L qL
      -∗ □ (elctx_interp E -∗ ∀ n,
            let ty1 := (fixpoint_defs.Tn T1 n) in
            let ty2 := (fixpoint_defs.Tn T2 n) in
            ⌜ty_size ty1 = ty_size ty2⌝ ∗ ty_lft ty1 ≡ₗ ty_lft ty2
            ∗ □ (∀ depth tid vl, ty1.(ty_own) depth tid vl ↔ ty2.(ty_own) depth tid vl)
            ∗ □ (∀ κ tid l, ty1.(ty_shr) κ tid l ↔ ty2.(ty_shr) κ tid l))).
    { rewrite intuitionistically_into_persistently -Hwand_forall
              persistently_forall. apply forall_intro=>n.
      rewrite -intuitionistically_into_persistently.
      revert qL. rewrite -eqtype_unfold. by induction n as [|n IH]; apply H12. }
    rewrite Hsub /type_incl -!persistent_and_sep /=. f_equiv. f_equiv.
    (* FIXME : change the definition of limit_preserving so that it
       applies even if the limti is not computed with compl. *)
    assert (Hentails_equiv : ∀ P Q : iProp Σ, (P ⊣⊢ P ∧ Q) ↔ (P ⊢ Q)).
    { intros P Q; split; [by iIntros (->) "[_ $]"|].
      intros HPQ. iSplit; [|by iIntros "[$ _]"]. iIntros "H". iSplit; [done|].
      by iApply HPQ. }
    apply and_intro; [|apply and_intro; [|apply and_intro]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($ & _ & _ & _)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_ & $ & _ & _)".
    - apply Hentails_equiv, equiv_dist=>n. setoid_rewrite conv_compl; simpl.
      apply equiv_dist, Hentails_equiv. iIntros "H".
      iDestruct ("H" $! _) as "(_ & _ & $ & _)".
    - apply Hentails_equiv, equiv_dist=>n. setoid_rewrite conv_compl; simpl.
      apply equiv_dist, Hentails_equiv. iIntros "H".
      iDestruct ("H" $! _) as "(_ & _ & _ & $)".
  Qed.

  Lemma fixpoint_unfold_subtype_l ty T `{!TypeContractive T} :
    subtype E L ty (T (type_fixpoint T)) → subtype E L ty (type_fixpoint T).
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_subtype_r ty T `{!TypeContractive T} :
    subtype E L (T (type_fixpoint T)) ty → subtype E L (type_fixpoint T) ty.
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_eqtype_l ty T `{!TypeContractive T} :
    eqtype E L ty (T (type_fixpoint T)) → eqtype E L ty (type_fixpoint T).
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
  Lemma fixpoint_unfold_eqtype_r ty T `{!TypeContractive T} :
    eqtype E L (T (type_fixpoint T)) ty → eqtype E L (type_fixpoint T) ty.
  Proof. intros. by rewrite fixpoint_unfold_eqtype. Qed.
End subtyping.

Hint Resolve fixpoint_mono fixpoint_proper : lrust_typing.

(* These hints can loop if [fixpoint_mono] and [fixpoint_proper] have
   not been tried before, so we give them a high cost *)
Hint Resolve fixpoint_unfold_subtype_l|100 : lrust_typing.
Hint Resolve fixpoint_unfold_subtype_r|100 : lrust_typing.
Hint Resolve fixpoint_unfold_eqtype_l|100 : lrust_typing.
Hint Resolve fixpoint_unfold_eqtype_r|100 : lrust_typing.
