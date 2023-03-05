From lrust.lang Require Import proofmode.
From lrust.typing Require Export lft_contexts type.
From lrust.typing Require Import base_type.
Import uPred.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Module fix_defs.

Section S.
  Context `{!typeG Σ} {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T}.

  Definition Tn_h n := Nat.iter n T base.

  Program Definition base : type 𝔄 :=
  {| st_size := 0; st_lfts := [];  st_E := [];
     st_proph vπ ξl := exists i, (Tn_h i).(ty_proph) vπ ξl;
      st_own _ _ _ _ := False |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. move=> /= ??[??]. by eapply ty_proph_weaken. Qed.

  Global Instance base_send: Send (base).
  Proof. done. Qed.

  Lemma base_resolve E L Φ : resolve E L base Φ.
  Proof. iIntros "* _ _ _ _" ([]). Qed.

  Lemma base_real {𝔅} E L (f: 𝔄 → 𝔅) : real E L base f.
  Proof.
    split.
    - iIntros "*% _ _ _" ([]).
    - by iIntros "*% _ _ _ (%x&_&>%)".
  Qed.

  Definition Tn n := Nat.iter (S n) T base.

  Lemma Tn_ty_lft_const n n' : ⊢ ty_lft (Tn n) ≡ₗ ty_lft (Tn n').
  Proof using HT.
    have Eq: ∀n, ⊢ ty_lft (Tn n) ≡ₗ ty_lft (Tn 0); last first.
    { iApply lft_equiv_trans; [|iApply lft_equiv_sym]; iApply Eq. }
    clear n n'=> n. case type_ne_type_lft_morphism=> [> Hα ?|> Hα ?]; last first.
    { iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_sym. iApply Hα. }
    elim: n=> [|n IH]; [apply lft_equiv_refl|]. rewrite /Tn /=.
    iApply lft_equiv_trans; [iApply type_lft_morphism_lft_equiv_proper; iApply IH|].
    iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_trans.
    { iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply Hα]. }
    iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
    iApply lft_intersect_equiv_idemp.
  Qed.

  Lemma Tn_ty_E_const n n' :
    elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn (S n')).(ty_E).
  Proof using HT.
    have Eq: ∀n, elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn 1).(ty_E);
    [|by rewrite !Eq]. clear n n'=> n.
    case type_ne_type_lft_morphism=> [> Hα HE|> ? HE]; last by rewrite !HE.
    elim: n; [done|]=> n IH.
    rewrite (HE (Tn (S n))) IH !HE !assoc -!persistent_sep_dup -!assoc.
    iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    iApply (big_sepL_impl with "H"). iIntros "!> * _". iIntros "#?".
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const (S n) 0) as "[_ $]".
  Qed.

  Lemma Tn_ty_proph_const (n n': nat) vπ ξl : (ty_proph (Nat.iter n T base) vπ ξl ≡ ty_proph (Nat.iter n' T base) vπ ξl).
  Proof using HT.
    assert (forall n vπ ξ, (ty_proph (Nat.iter n T base) vπ ξ ≡ ty_proph base vπ ξ)); [|by rewrite 2! H].
    clear -HT. intros. induction n. done. rewrite -IHn.
    clear -HT. revert vπ ξ. induction n; intros.  
    simpl. split. 
    - intros. destruct (type_ne_ty_proph_invert _ _ _ H) as (vπl&ξl&?&?).
    assert (exists i, Forall2 (Tn_h i).(ty_proph) vπl ξl) as (i&?); last first.
    exists (S i). simpl. by apply H1.
    clear H1. revert ξl H0. induction vπl; intros; inversion_clear H0. exists 0%nat. done.
    destruct (IHvπl _ H2) as (i&?). destruct H1 as (i'&?).
    exists (i `max` i')%nat. assert (forall i i' vπ ξl, (ty_proph (Tn_h i) vπ ξl) -> (ty_proph (Tn_h (i+i')) vπ ξl)) as Tn'mono.
    clear -HT. intros ?????. induction i'. replace (i + 0)%nat with i; [done|lia].
    replace (i + S i')%nat with (S (i + i'))%nat; [|lia]. remember (i + i')%nat as i0.
    clear -HT IHi'. revert ξl vπ IHi'. induction i0; simpl; intros. done. simpl in IHi0. eapply type_ne_ty_proph; [|done]. intros ???. by apply IHi0.
    constructor. replace (i `max` i')%nat with (i' + ((i `max` i') - i'))%nat; [|lia]. by apply Tn'mono.
    eapply Forall2_impl; [done|]. intros ???. replace (i `max` i')%nat with (i + ((i `max` i') - i))%nat; [|lia]. by apply Tn'mono.
    - intros ([|?]&?). done. simpl in H. eapply type_ne_ty_proph; [|done]. simpl. intros ???. eexists _. done.
    - simpl. apply type_ne_ty_proph'. done.
  Qed.

  Lemma Tn_cauchy n i : (n ≤ i)%nat →
    (∀vπ d tid vl, dist_later n
      ((Tn (2 + i)).(ty_own) vπ d tid vl) ((Tn (2 + n)).(ty_own) vπ d tid vl)) ∧
    (∀vπ d κ tid l,
      (Tn (2 + i)).(ty_shr) vπ d κ tid l ≡{n}≡ (Tn (2 + n)).(ty_shr) vπ d κ tid l).
  Proof using HT.
    move: i. elim: n=> /=[|n IH]=> i ?.
    - split; [done|]. apply HT=>//; [apply type_contractive_ty_size|
    apply (Tn_ty_lft_const (S i) 1)|apply (Tn_ty_E_const i 0)|apply (Tn_ty_proph_const (2 + i) 2)].
    - case i as [|]; [lia|]. case (IH i) as [??]; [lia|].
      split; (apply HT=>//; [apply type_contractive_ty_size|
        apply (Tn_ty_lft_const (2 + i) (2 + n))|apply (Tn_ty_E_const (S i) (S n))|apply (Tn_ty_proph_const (3 + i) (3 + n))]).
  Qed.
  Program Definition own_shr_chain :=
    {| chain_car n := ((Tn (3 + n)).(ty_own), (Tn (3 + n)).(ty_shr)) :
        prodO (proph 𝔄 -d> nat -d> thread_id -d> list val -d> iPropO Σ)
          (proph 𝔄 -d> nat -d> lft -d> thread_id -d> loc -d> iPropO Σ) |}.
  Next Obligation.
    move=> n i Hni. split=>/=.
    - move=> >. apply (Tn_cauchy (S _)). lia.
    - move=> >. apply dist_S, Tn_cauchy. lia.
  Qed.

  Program Definition Tn' n : type 𝔄 := {|
    ty_size := (Tn 0).(ty_size);  ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_proph := base.(ty_proph); ty_own := (Tn n).(ty_own);  ty_shr := (Tn n).(ty_shr)
  |}.
  Next Obligation.
    move=> *. rewrite ty_size_eq /Tn. iIntros "->!%/=". apply type_contractive_ty_size.
  Qed.
  Next Obligation. move=> >. apply ty_own_depth_mono. Qed.
  Next Obligation. move=> >. apply ty_shr_depth_mono. Qed.
  Next Obligation. move=> >. apply ty_shr_lft_mono. Qed.
  Next Obligation.
    move=> n *. iIntros "#LFT #?". iApply (ty_share with "LFT"); [done|].
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.
  Next Obligation.
    move=> n *. iIntros "#LFT #?". setoid_rewrite (Tn_ty_proph_const 0 (S n)). 
    iApply (ty_own_proph with "LFT"); [done|].
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.
  Next Obligation.
    move=> n *. iIntros "#LFT #? #?". setoid_rewrite (Tn_ty_proph_const 0 (S n)).
    iApply (ty_shr_proph with "LFT"); [done|done|].
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.
  Next Obligation.
    move=> *. eapply ty_proph_weaken. done.
  Qed.

  Program Definition fix_ty: type 𝔄 := {|
    ty_size := (Tn 0).(ty_size);  ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_proph := base.(ty_proph); ty_own := (compl own_shr_chain).1;  ty_shr := (compl own_shr_chain).2
  |}.
  Next Obligation.
    move=> *. apply @limit_preserving, _.
    apply limit_preserving_Persistent=> ??? Eq. apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply (ty_size_eq (Tn' _))].
    apply limit_preserving_entails; [|done]. move=> ??? Eq. apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply ty_own_depth_mono].
    apply limit_preserving_entails=> ??? Eq; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply ty_shr_depth_mono].
    apply limit_preserving_entails=> ??? Eq; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply ty_shr_lft_mono].
    apply limit_preserving_entails; [done|]=> ??? Eq. f_equiv; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply (ty_share (Tn' _))].
    apply limit_preserving_entails; [done|]=> ??? Eq. do 6 f_equiv; [|f_equiv]; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply (ty_own_proph (Tn' _))].
    apply limit_preserving_entails; [done|]=> ??? Eq.
    do 2 f_equiv; [|do 13 f_equiv]; apply Eq.
  Qed.
  Next Obligation.
    move=> *. apply @limit_preserving; [|move=> ?; by apply (ty_shr_proph (Tn' _))].
    apply limit_preserving_entails; [done|]=> ??? Eq. do 3 f_equiv. apply Eq.
  Qed.
  Next Obligation.
    move=> *. eapply ty_proph_weaken. done.
  Qed.


  Lemma fix_ty_Tn'_dist n : fix_ty ≡{n}≡ Tn' (3 + n).
  Proof. split=>// *; apply conv_compl. Qed.
End S.
End fix_defs.

Import fix_defs.
Global Notation fix_ty := fix_ty.

Section fix_ty.
  Context `{!typeG Σ}.
  Opaque base.

  Lemma fix_unfold_fold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    eqtype E L (fix_ty T) (T (fix_ty T)) id id.
  Proof.
    have EqOwn: ∀n vπ d tid vl, (T $ Tn T (3 + n)).(ty_own) vπ d tid vl ≡
      (T $ Tn' T (3 + n)).(ty_own) vπ d tid vl.
    { move=> n *. apply equiv_dist=> ?. apply HT=>//; [apply HT|
        apply (Tn_ty_lft_const T (3 + n) 0)|apply (Tn_ty_E_const T (2 + n) 0)|
        apply (Tn_ty_proph_const T (4 + n) 0)]. }
    have EqShr: ∀n vπ d κ tid l, (T $ Tn T (2 + n)).(ty_shr) vπ d κ tid l ≡
      (T $ Tn' T (2 + n)).(ty_shr) vπ d κ tid l.
    { move=> n *. apply equiv_dist=> n'. apply HT=>//; [apply HT|
        apply (Tn_ty_lft_const T (2 + n) 0)|apply (Tn_ty_E_const T (1 + n) 0)|
        apply (Tn_ty_proph_const T (3 + n) 0)|
        by case n'=> [|[|?]]]. }
    have EqOwn': ∀vπ d tid vl, (fix_ty T).(ty_own) vπ d tid vl ≡
      (T (fix_ty T)).(ty_own) vπ d tid vl.
    { move=> *. apply equiv_dist=> n. etrans; [apply dist_S, conv_compl|].
      rewrite/= (EqOwn n). symmetry. apply HT=>// *; [apply lft_equiv_refl| |].
      - move: n=> [|n]; [done|].
        case (fix_ty_Tn'_dist T (S n))=> [_ _ _ _ Eq _]. apply dist_S, Eq.
      - case (fix_ty_Tn'_dist T n)=> [_ _ _ _ _ Eq]. apply Eq. }
    have EqShr': ∀vπ d κ tid l, (fix_ty T).(ty_shr) vπ d κ tid l ≡
      (T (fix_ty T)).(ty_shr) vπ d κ tid l.
    { move=> *. apply equiv_dist=> n. etrans; [apply conv_compl|].
      rewrite/= (EqShr n). symmetry. apply HT=>// *; [apply lft_equiv_refl| |].
      - move: n=> [|[|n]]; [done|done|].
        case (fix_ty_Tn'_dist T (S n))=> [_ _ _ _ Eq _]. apply dist_S, Eq.
      - move: n=> [|n]; [done|].
        case (fix_ty_Tn'_dist T n)=> [_ _ _ _ _ Eq]. apply Eq. }
    apply eqtype_id_unfold. iIntros "*_!>_". iSplit; [iPureIntro|].
    split; [apply HT|]. setoid_rewrite (type_ne_ty_proph' (fix_ty T) (base T)); [|done]. by apply (Tn_ty_proph_const T 0 1).
    iSplit; [|iSplit; iIntros "!> *"].
    - case type_ne_type_lft_morphism=> [α βs E' Hα HE'|α E' Hα HE'].
      + iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
        iApply lft_equiv_trans; [iApply Hα|].
        iApply lft_equiv_trans; [|iApply lft_intersect_equiv_proper;
          [iApply lft_equiv_refl|iApply lft_equiv_sym; iApply Hα]].
        rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
        iApply lft_equiv_sym. iApply lft_intersect_equiv_idemp.
      + iApply lft_equiv_trans; [iApply Hα|iApply lft_equiv_sym; iApply Hα].
    - rewrite EqOwn'. by iApply bi.equiv_iff.
    - rewrite EqShr'. by iApply bi.equiv_iff.
  Qed.
  Lemma fix_fold_unfold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    eqtype E L (T (fix_ty T)) (fix_ty T) id id.
  Proof. apply eqtype_symm, fix_unfold_fold. Qed.
  Lemma fix_unfold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    subtype E L (fix_ty T) (T (fix_ty T)) id.
  Proof. eapply proj1, fix_unfold_fold. Qed.
  Lemma fix_fold {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T} E L :
    subtype E L (T (fix_ty T)) (fix_ty T) id.
  Proof. eapply proj2, fix_unfold_fold. Qed.

  Lemma base_ne' {𝔄} (T T': type 𝔄 → type 𝔄) {HT: TypeContractive T} {HT': TypeContractive T'} : (∀ ty vπ ξ, (T ty).(ty_proph) vπ ξ → (T' ty).(ty_proph) vπ ξ) → (∀ vπ ξ, (base T).(ty_proph) vπ ξ → (base T').(ty_proph) vπ ξ).
  Proof. 
    intros ???. simpl. intros (i&?). exists i. revert vπ ξ H0.
    (induction i; [done|]). simpl. intros. apply H. by eapply type_ne_ty_proph.
  Qed.

  Lemma base_ne {𝔄} (T T': type 𝔄 → type 𝔄) {HT: TypeContractive T} {HT': TypeContractive T'} n : (∀ ty, T ty ≡{n}≡ T' ty) → (base T) ≡{n}≡ (base T').
  Proof. intros. constructor; try done. intros. split; apply base_ne'; try done; by setoid_rewrite H. Qed.

  Lemma fix_ty_ne {𝔄} (T T': type 𝔄 → type 𝔄)
      `{!TypeContractive T, !NonExpansive T} {HT: TypeContractive T'} n :
    (∀ty, T ty ≡{n}≡ T' ty) → fix_ty T ≡{n}≡ fix_ty T'.
  Proof.
    move=> Eq.
    have Eq': compl (own_shr_chain T) ≡{n}≡ compl (own_shr_chain T').
    { have Eq'': Tn T (3 + n) ≡{n}≡ Tn T' (3 + n).
      { rewrite /Tn. elim (S (3 + n)); [by apply base_ne|]=> ? IH. by rewrite !Nat_iter_S IH Eq. }
      etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
      split; repeat move=> ? /=; apply Eq''. }
    split=>/=; try apply Eq; try apply Eq'; [..|intros]; try rewrite /Tn /= -!Eq; try by rewrite base_ne.
  Qed.
(* 
  Program Definition base' {𝔄} (T: type 𝔄 → type 𝔄) : type 𝔄 :=
  {| st_size := (Tn T 0).(ty_size);  st_lfts := (Tn T 0).(ty_lfts);  st_E := (Tn T 1).(ty_E);
     st_proph vπ ξl := false;
      st_own _ _ _ _ := False |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. by intros. Qed.

  Lemma Tn_h_proph_alt {𝔄} (T: type 𝔄 → type 𝔄) `{!TypeContractive T} vπ ξl i: (Tn_h T i).(ty_proph) vπ ξl <-> (Nat.iter i T (base' T)).(ty_proph) vπ ξl.
  Proof. revert vπ ξl. induction i; simpl. done. by eapply type_ne_ty_proph'. Qed. *)

  Lemma base_type_contractive {𝔄 𝔅} (P: (type 𝔄 → type 𝔅) → Prop) (T : type 𝔄 → type 𝔅 → type 𝔅)
    `{!(∀ty, TypeContractive (T ty))} :
   (∀`{!P U}, TypeNonExpansiveBase U) → P (λ _, base_type.base) → (∀`{!P U}, P (λ ty, T ty (U ty))) → 
    TypeContractive (λ ty, base (T ty)).
  Proof.
  move=> HP ? HT. have Hne: ∀n, TypeNonExpansiveBase (λ ty, Tn_h (T ty) n).
  { intros. apply HP. induction n as [|? IH]; [done|apply HT, IH].  }
  split; [done|split|done|done].
  - eapply (type_lft_morphism_const _ _ []); simpl; intros; by [iApply lft_equiv_refl|].
  - intros. simpl. intros (i&?). exists i.  by eapply Hne.
  - simpl. intros ??? (i&?). destruct (Hne i). destruct (type_ne_ty_proph_invert _ _ _ H0) as (vπl&ξl&?&?).
  exists vπl, ξl. intuition. exists i. intuition.
  Qed.


  Lemma fix_type_ne {𝔄 𝔅} (T : type 𝔄 → type 𝔅 → type 𝔅)
      `{!(∀ty, TypeContractive (T ty))} :
    (∀`{!TypeNonExpansive U}, TypeNonExpansive (λ ty, T ty (U ty))) →
      TypeNonExpansive (λ ty, fix_ty (T ty)).
  Proof.
    move=> HT.
    have Hbase: TypeContractive (λ ty, base (T ty)).
    eapply (base_type_contractive TypeNonExpansive); intuition.
    apply type_ne_base.  apply type_contractive_type_ne, const_type_contractive.
    have Hne: ∀n, TypeNonExpansive (λ ty, Tn (T ty) n).
    { elim=> [|? IH]; [eapply HT, _|apply HT, IH]. }
    split; [|split|..]=>/=.
    - eapply HT, _.
    - case (type_ne_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
      [α βs E Hα HE|α E Hα HE].
      + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
      + eapply (type_lft_morphism_const _ α E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
    - move=> *. by apply Hbase.
    - move=> *. by apply Hbase.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
  Qed.

  Lemma fix_type_contractive {𝔄 𝔅} (T : type 𝔄 → type 𝔅 → type 𝔅)
      `{!(∀ty, TypeContractive (T ty))} :
    (∀`{!TypeContractive U}, TypeContractive (λ ty, T ty (U ty))) →
      TypeContractive (λ ty, fix_ty (T ty)).
  Proof.
    move=> HT.
    have Hbase: TypeContractive (λ ty, base (T ty)).
    eapply (base_type_contractive TypeContractive); intuition.
    apply type_contractive_base. apply const_type_contractive.
    have Hne: ∀n, TypeContractive (λ ty, Tn (T ty) n).
    { elim=> [|? IH]; [apply HT, _|apply HT, IH]. }
    split; [|split|..]=>/=.
    - apply HT, _.
    - case (type_ne_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
      [α βs E Hα HE|α E Hα HE].
      + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
      + eapply (type_lft_morphism_const _ α E), HE=> ?.
        iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
        iApply (Tn_ty_lft_const _ 1 0).
    - move=> *. by apply Hbase.
    - move=> *. by apply Hbase.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
    - move=> *. etrans; [apply conv_compl|].
      etrans; [|symmetry; apply conv_compl]. by apply Hne.
  Qed.
End fix_ty.

Section fix_ty.
  Context `{!typeG Σ} {𝔄} (T: type 𝔄 → type 𝔄) {HT: TypeContractive T}.

  Global Instance fix_copy :
    (∀`(!Copy ty), Copy (T ty)) → Copy (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Copy (Tn T n) by elim; apply _.
    split; rewrite /fix_ty /=.
    - move=> >. eapply @limit_preserving; [|apply _].
      apply limit_preserving_Persistent=> ??? Eq. apply Eq.
    - move=> > ?. eapply @limit_preserving.
      { apply limit_preserving_forall=> ?.
        apply limit_preserving_entails; [done|]=> ??? Eq.
        f_equiv; [|do 11 f_equiv]; apply Eq. }
      move=> n. have ->: (Tn T 0).(ty_size) = (Tn T (3 + n)).(ty_size).
      { rewrite /Tn /=. apply type_contractive_ty_size. }
      by apply copy_shr_acc.
  Qed.

  Global Instance fix_send :
    (∀`(!Send ty), Send (T ty)) → Send (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Send (Tn T n) by elim; apply _. rewrite /fix_ty=> > /=.
    eapply @limit_preserving; [|move=> ?; by apply send_change_tid].
    apply limit_preserving_equiv=> ??? Eq; apply Eq.
  Qed.

  Global Instance fix_sync :
    (∀`(!Sync ty), Sync (T ty)) → Sync (fix_ty T).
  Proof.
    move=> ?. have ?: ∀n, Sync (Tn T n) by elim; apply _. rewrite /fix_ty=> > /=.
    eapply @limit_preserving; [|move=> ?; by apply sync_change_tid].
    apply limit_preserving_equiv=> ??? Eq; apply Eq.
  Qed.

  Lemma fix_resolve E L Φ :
    (∀ty, resolve E L ty Φ → resolve E L (T ty) Φ) → resolve E L (fix_ty T) Φ.
  Proof.
    move=> Loop. have Rslv: ∀n, resolve E L (Tn T n) Φ.
    { elim=> [|? H]; apply Loop; [apply base_resolve|apply H]. }
    rewrite /fix_ty=> > /=. eapply @limit_preserving; [|move=> ?; apply Rslv].
    apply limit_preserving_forall=> ?.
    apply limit_preserving_entails; [done|]=> ??? Eq. do 4 f_equiv. apply Eq.
  Qed.

  Lemma fix_real {𝔅} E L (f: _ → 𝔅) :
    (∀ty, real E L ty f → real E L (T ty) f) → real E L (fix_ty T) f.
  Proof.
    move=> Loop. have Rl: ∀n, real E L (Tn T n) f.
    { elim=> [|? H]; apply Loop; [apply base_real|apply H]. }
    rewrite /fix_ty. split=>/= >; (
      eapply @limit_preserving; [|move=> ?; apply Rl];
      apply limit_preserving_forall=> ?;
      apply limit_preserving_entails; [done|]=> ??? Eq;
      do 3 f_equiv; [apply Eq|]; do 5 f_equiv); [|do 2 f_equiv]; apply Eq.
  Qed.
End fix_ty.

(* Section fix_subtyping.
  Context `{!typeG Σ}.

  Local Lemma wand_forall P (Φ: nat → iProp Σ) : (∀n, P -∗ Φ n) ⊢ (P -∗ ∀n, Φ n).
  Proof. iIntros "To P %". iApply ("To" with "P"). Qed.
  Local Lemma entails_dist_True (P Q: iProp Σ) : (P ⊢ Q) ↔ ∀n, (P → Q)%I ≡{n}≡ True%I.
  Proof. by rewrite entails_eq_True equiv_dist. Qed.

  Lemma fix_subtype {𝔄 𝔅} f
    (T : type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T' : type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ty ty', subtype E L ty ty' f → subtype E L (T ty) (T' ty') f) →
    subtype E L (fix_ty T) (fix_ty T') f.
  Proof.
    move=> Loop qL.
    have Incl: llctx_interp L qL -∗ □ (elctx_interp E -∗
      ∀n, type_incl (Tn T n) (Tn T' n) f).
    { rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      move: qL. apply Loop. elim n=> [|??]; [solve_typing|by apply Loop]. }
    rewrite Incl /type_incl -!persistent_and_sep /=. do 2 f_equiv.
    (* FIXME : change the definition of limit_preserving so that it
       applies even if the limti is not computed with compl. *)
    apply and_intro; [|apply and_intro; [|apply and_intro]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$)".
  Qed.

  Lemma fix_eqtype_subtype {𝔄 𝔅} f g
    (T : type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T' : type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L ty ty' f g → eqtype E L (T ty) (T' ty') f g) →
    subtype E L (fix_ty T) (fix_ty T') f.
  Proof.
    move=> Loop qL.
    have Incl: llctx_interp L qL -∗ □ (elctx_interp E -∗
      ∀n, type_incl (Tn T n) (Tn T' n) f).
    { rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      move: qL. apply Loop. elim n=> [|??]; [solve_typing|by apply Loop]. }
    rewrite Incl /type_incl -!persistent_and_sep /=. do 2 f_equiv.
    apply and_intro; [|apply and_intro; [|apply and_intro]].
    - iIntros "H". iDestruct ("H" $! 0%nat) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0%nat) as "(_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_dist_True=> ?. setoid_rewrite conv_compl=>/=.
      apply entails_dist_True. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$)".
  Qed.

  Lemma fix_eqtype {𝔄 𝔅} f g
    (T: type 𝔄 → type 𝔄) `{!TypeContractive T}
    (T': type 𝔅 → type 𝔅) `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L ty ty' f g → eqtype E L (T ty) (T' ty') f g) →
    eqtype E L (fix_ty T) (fix_ty T') f g.
  Proof.
    move=> Loop.
    have ?: ∀ty' ty, eqtype E L ty' ty g f → eqtype E L (T' ty') (T ty) g f.
    { move=> ??[??]. split; apply Loop; by split. }
    split; by eapply fix_eqtype_subtype.
  Qed.

  Lemma fix_subtype_l {𝔄 𝔅} (f: 𝔄 → 𝔅) ty T `{!TypeContractive T} E L :
    subtype E L ty (T (fix_ty T)) f → subtype E L ty (fix_ty T) f.
  Proof.
    move=> ?. eapply (subtype_trans _ _ _ _ id); [done|]. apply fix_fold.
  Qed.
  Lemma fix_subtype_r {𝔄 𝔅} (f: 𝔄 → 𝔅) ty T `{!TypeContractive T} E L :
    subtype E L (T (fix_ty T)) ty f → subtype E L (fix_ty T) ty f.
  Proof.
    move=> ?. eapply (subtype_trans _ _ _ id); [|done]. apply fix_unfold.
  Qed.
  Lemma fix_eqtype_l {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty T `{!TypeContractive T} E L :
    eqtype E L ty (T (fix_ty T)) f g → eqtype E L ty (fix_ty T) f g.
  Proof.
    move=> ?. eapply (eqtype_trans _ _ _ _ _ id id); [done|]. apply fix_fold_unfold.
  Qed.
  Lemma fix_eqtype_r {𝔄 𝔅} (f: 𝔄 → 𝔅) g ty T `{!TypeContractive T} E L :
    eqtype E L (T (fix_ty T)) ty f g → eqtype E L (fix_ty T) ty f g.
  Proof.
    move=> ?. eapply (eqtype_trans _ _ _ id id); [|done]. apply fix_unfold_fold.
  Qed.
End fix_subtyping. *)

(* Global Hint Resolve fix_subtype_l fix_subtype_r fix_eqtype_l fix_eqtype_r | 100
  : lrust_typing. *)
