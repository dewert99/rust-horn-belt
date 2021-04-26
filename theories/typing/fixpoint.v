From lrust.typing Require Export type.
Import uPred.
Set Default Proof Using "Type".

Module fix_defs.

Section base.
  Context `{!typeG Σ}.

  Program Definition base {A} : type A := {| pt_size := 0; pt_own _ _ _ := False |}%I.
  Next Obligation. by iIntros. Qed.

  Global Instance base_send {A} : Send (@base A). Proof. done. Qed.

  Lemma base_subtype {A B} E L (f: A → B) : subtype E L f base base.
  Proof.
    apply subtype_plain_type. iIntros "*_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|by iIntros].
  Qed.
  Lemma base_eqtype {A B} E L (f: A → B) g : eqtype E L f g base base.
  Proof. split; apply base_subtype. Qed.

End base.

Section S.
  Context `{!typeG Σ} {A: Type} (T: type A → type A) {HT: TypeContractive T}.

  Definition Tn n := Nat.iter (S n) T base.

  Lemma Tn_ty_lft_const n n' : ⊢ (Tn n).(ty_lft) ≡ₗ (Tn n').(ty_lft).
  Proof using HT.
    have H: ∀n, ⊢ (Tn n).(ty_lft) ≡ₗ (Tn 0).(ty_lft); last first.
    { iApply lft_equiv_trans; [|iApply lft_equiv_sym]; iApply H. } clear n n'=> n.
    case type_contractive_type_lft_morphism=> [> Hα ?|> Hα ?]; last first.
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
    have H: ∀n, elctx_interp (Tn (S n)).(ty_E) ≡ elctx_interp (Tn 1).(ty_E); last first.
    { by rewrite H. } clear n n'=> n.
    case type_contractive_type_lft_morphism=> [> Hα HE|> ? HE]; last by rewrite !HE.
    elim: n; [done|]=> n IH.
    rewrite (HE (Tn (S n))) IH !HE !assoc -!persistent_sep_dup -!assoc.
    iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    iApply (big_sepL_impl with "H"). iIntros "!> * _". iIntros "#?".
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const (S n) 0) as "[_ $]".
  Qed.

  Lemma Tn_cauchy n i : n ≤ i →
    (∀vπ d tid vl, dist_later n
      ((Tn (2 + i)).(ty_own) vπ d tid vl) ((Tn (2 + n)).(ty_own) vπ d tid vl)) ∧
    (∀vπ d κ tid l,
      (Tn (2 + i)).(ty_shr) vπ d κ tid l ≡{n}≡ (Tn (2 + n)).(ty_shr) vπ d κ tid l).
  Proof using HT.
    move: i. elim: n=> /=[|n IH]=> i ?.
    - split; [done|]. apply HT=>//; [apply type_contractive_ty_size|
        apply (Tn_ty_lft_const (S i) 1)|apply (Tn_ty_E_const i 0)].
    - case i as [|]; [lia|]. case (IH i) as [??]; [lia|].
      split; (apply HT=>//; [apply type_contractive_ty_size|
        apply (Tn_ty_lft_const (2 + i) (2 + n))|apply (Tn_ty_E_const (S i) (S n))]).
  Qed.
  Program Definition own_shr_chain :=
    {| chain_car n := ((Tn (3 + n)).(ty_own), (Tn (3 + n)).(ty_shr)) :
        prodO (proph A -d> nat -d> thread_id -d> list val -d> iPropO Σ)
          (proph A -d> nat -d> lft -d> thread_id -d> loc -d> iPropO Σ) |}.
  Next Obligation.
    move=> n i Hni. split=>/=.
    - move=> >. apply (Tn_cauchy (S _)). lia.
    - move=> >. apply dist_S, Tn_cauchy. lia.
  Qed.

  Program Definition Tn' n : type A := {|
    ty_size := (Tn 0).(ty_size);  ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_own := (Tn n).(ty_own);  ty_shr := (Tn n).(ty_shr)
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
    move=> n *. iIntros "#LFT #?". iApply (ty_own_proph with "LFT"); [done|].
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.
  Next Obligation.
    move=> n *. iIntros "#LFT #? #?". iApply (ty_shr_proph with "LFT"); [done|done|].
    iApply lft_incl_trans; [done|]. iDestruct (Tn_ty_lft_const n 0) as "[_ $]".
  Qed.

  Program Definition fix_ty: type A := {|
    ty_size := (Tn 0).(ty_size);  ty_lfts := (Tn 0).(ty_lfts);  ty_E := (Tn 1).(ty_E);
    ty_own := (compl own_shr_chain).1;  ty_shr := (compl own_shr_chain).2
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
    apply limit_preserving_entails; [done|]=> ??? Eq.
    do 3 f_equiv; [|do 15 f_equiv]; apply Eq.
  Qed.

  Lemma fix_ty_Tn'_dist n : fix_ty ≡{n}≡ Tn' (3 + n).
  Proof. split=>// *; apply conv_compl. Qed.

End S.

End fix_defs.

Import fix_defs.
Global Notation fix_ty := fix_ty.

Lemma fix_unfold_eqtype `{!typeG Σ} {A} (T: _ → _ A) {HT: TypeContractive T} E L :
  eqtype E L id id (fix_ty T) (T (fix_ty T)).
Proof.
  have EqOwn: ∀n vπ d tid vl, (T $ Tn T (3 + n)).(ty_own) vπ d tid vl ≡
    (T $ Tn' T (3 + n)).(ty_own) vπ d tid vl.
  { move=> n *. apply equiv_dist=> ?. apply HT=>//; [apply HT|
      apply (Tn_ty_lft_const T (3 + n) 0)|apply (Tn_ty_E_const T (2 + n) 0)]. }
  have EqShr: ∀n vπ d κ tid l, (T $ Tn T (2 + n)).(ty_shr) vπ d κ tid l ≡
    (T $ Tn' T (2 + n)).(ty_shr) vπ d κ tid l.
  { move=> n *. apply equiv_dist=> n'. apply HT=>//; [apply HT|
      apply (Tn_ty_lft_const T (2 + n) 0)|apply (Tn_ty_E_const T (1 + n) 0)|
      by case n'=> [|[|?]]]. }
  have EqOwn': ∀vπ d tid vl, (fix_ty T).(ty_own) vπ d tid vl ≡
    (T (fix_ty T)).(ty_own) vπ d tid vl.
  { move=> *. apply equiv_dist=> n. etrans; [apply dist_S, conv_compl|].
    rewrite/= (EqOwn n). symmetry. apply HT=>// *; [apply lft_equiv_refl| |].
    - move: n=> [|n]; [done|].
      case (fix_ty_Tn'_dist T (S n))=> [_ _ _ Eq _]. apply dist_S, Eq.
    - case (fix_ty_Tn'_dist T n)=> [_ _ _ _ Eq]. apply Eq. }
  have EqShr': ∀vπ d κ tid l, (fix_ty T).(ty_shr) vπ d κ tid l ≡
    (T (fix_ty T)).(ty_shr) vπ d κ tid l.
  { move=> *. apply equiv_dist=> n. etrans; [apply conv_compl|].
    rewrite/= (EqShr n). symmetry. apply HT=>// *; [apply lft_equiv_refl| |].
    - move: n=> [|[|n]]; [done|done|].
      case (fix_ty_Tn'_dist T (S n))=> [_ _ _ Eq _]. apply dist_S, Eq.
    - move: n=> [|n]; [done|].
      case (fix_ty_Tn'_dist T n)=> [_ _ _ _ Eq]. apply Eq. }
  apply eqtype_id_unfold. iIntros "*_!>_". iSplit; [iPureIntro; by apply HT|].
  iSplit; [|iSplit; iIntros "!> *"].
  - case type_contractive_type_lft_morphism=> [α βs E' Hα HE'|α E' Hα HE'].
    + iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
      iApply lft_equiv_trans; [iApply Hα|].
      iApply lft_equiv_trans; [|iApply lft_intersect_equiv_proper;
        [iApply lft_equiv_refl|iApply lft_equiv_sym; iApply Hα]].
      rewrite assoc. iApply lft_intersect_equiv_proper; [|iApply lft_equiv_refl].
      iApply lft_equiv_sym. iApply lft_intersect_equiv_idemp.
    + iApply lft_equiv_trans; [iApply Hα|iApply lft_equiv_sym; iApply Hα].
  - rewrite EqOwn'. by iApply (bi.iff_refl True%I).
  - rewrite EqShr'. by iApply (bi.iff_refl True%I).
Qed.

Lemma fix_ty_ne `{!typeG Σ} {A} (T T': _ → _ A)
  `{!TypeContractive T, !NonExpansive T, !TypeContractive T'} n :
  (∀ty, T ty ≡{n}≡ T' ty) → fix_ty T ≡{n}≡ fix_ty T'.
Proof. move=> Eq.
  have Eq': compl (own_shr_chain T) ≡{n}≡ compl (own_shr_chain T').
  { have Eq'': Tn T (3 + n) ≡{n}≡ Tn T' (3 + n).
    { rewrite /Tn. elim (S (3 + n)); [done|]=> ? IH. by rewrite !Nat_iter_S IH Eq. }
    etrans; [apply conv_compl|]. etrans; [|symmetry; apply conv_compl].
    split; repeat move=> ? /=; apply Eq''. }
  split=>/=; try apply Eq; try apply Eq'. by rewrite /Tn /= (Eq base) Eq.
Qed.

Lemma fix_type_ne `{!typeG Σ} {A B} (T : _ A → _ → _ B)
  `{!(∀ty, TypeContractive (T ty))} :
  (∀`{!TypeNonExpansive U}, TypeNonExpansive (λ ty, T ty (U ty))) →
    TypeNonExpansive (λ ty, fix_ty (T ty)).
Proof.
  move=> HT. have Hne: ∀n, TypeNonExpansive (λ ty, Tn (T ty) n).
  { elim=> [|? IH]; [apply HT, _|apply HT, IH]. } split=>/=.
  - case (type_non_expansive_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
    [α βs E Hα HE|α E Hα HE].
    + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
      iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (Tn_ty_lft_const _ 1 0).
    + eapply (type_lft_morphism_const _ α E), HE=> ?.
      iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (Tn_ty_lft_const _ 1 0).
  - apply HT, _.
  - move=> *. etrans; [apply conv_compl|].
    etrans; [|symmetry; apply conv_compl]. by apply Hne.
  - move=> *. etrans; [apply conv_compl|].
    etrans; [|symmetry; apply conv_compl]. by apply Hne.
Qed.

Lemma fix_type_contracive `{!typeG Σ} {A B} (T : _ A → _ → _ B)
  `{!(∀ty, TypeContractive (T ty))} :
  (∀`{!TypeContractive U}, TypeContractive (λ ty, T ty (U ty))) →
    TypeContractive (λ ty, fix_ty (T ty)).
Proof.
  move=> HT. have Hne: ∀n, TypeContractive (λ ty, Tn (T ty) n).
  { elim=> [|? IH]; [apply HT, _|apply HT, IH]. } split=>/=.
  - case (type_non_expansive_type_lft_morphism (T := λ ty, Tn (T ty) 1))=>
    [α βs E Hα HE|α E Hα HE].
    + eapply (type_lft_morphism_add _ α βs E), HE=> ?.
      iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (Tn_ty_lft_const _ 1 0).
    + eapply (type_lft_morphism_const _ α E), HE=> ?.
      iApply lft_equiv_trans; [|iApply Hα]. iApply lft_equiv_sym.
      iApply (Tn_ty_lft_const _ 1 0).
  - apply HT, _.
  - move=> *. etrans; [apply conv_compl|].
    etrans; [|symmetry; apply conv_compl]. by apply Hne.
  - move=> *. etrans; [apply conv_compl|].
    etrans; [|symmetry; apply conv_compl]. by apply Hne.
Qed.

Section traits.
  Context `{!typeG Σ}.
  Context {A} (T: type A → type A) {HT: TypeContractive T}.

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
      { rewrite /Tn /=. apply type_contractive_ty_size. } by apply copy_shr_acc.
  Qed.

  Global Instance fix_send :
    (∀`(!Send ty), Send (T ty)) → Send (fix_ty T).
  Proof. move=> ?.
    have ?: ∀n, Send (Tn T n) by elim; apply _. rewrite /fix_ty=> > /=.
    eapply @limit_preserving; [|move=> ?; apply send_change_tid].
    apply limit_preserving_equiv=> ??? Eq; apply Eq.
  Qed.

  Global Instance fix_sync :
    (∀`(!Sync ty), Sync (T ty)) → Sync (fix_ty T).
  Proof. move=> ?.
    have ?: ∀n, Sync (Tn T n) by elim; apply _. rewrite /fix_ty=> > /=.
    eapply @limit_preserving; [|move=> ?; apply sync_change_tid].
    apply limit_preserving_equiv=> ??? Eq; apply Eq.
  Qed.

End traits.

Section subtyping.
  Context `{!typeG Σ}.

  Local Lemma wand_forall P (Φ: nat → iProp Σ) : (∀n, P -∗ Φ n) ⊢ (P -∗ ∀n, Φ n).
  Proof. iIntros "To P %". iApply ("To" with "P"). Qed.
  Local Lemma entails_equiv (P Q: iProp Σ) : (P ⊣⊢ P ∧ Q) ↔ (P ⊢ Q).
  Proof.
    split; [by iIntros (->) "[_ $]"|]=> To. iSplit; [|by iIntros "[$ _]"].
    iIntros "?". iSplit; [done|]. by iApply To.
  Qed.

  Lemma fix_subtype {A B} (f: A → B)
    T `{!TypeContractive T} T' `{!TypeContractive T'} E L :
    (∀ty ty', subtype E L f ty ty' → subtype E L f (T ty) (T' ty')) →
    subtype E L f (fix_ty T) (fix_ty T').
  Proof. move=> Loop qL.
    have Incl: llctx_interp L qL -∗ □ (elctx_interp E -∗
      ∀n, type_incl f (Tn T n) (Tn T' n)).
    { rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      move: qL. apply Loop. elim n=> [|??]; [apply base_subtype|by apply Loop]. }
    rewrite Incl /type_incl -!persistent_and_sep /=. do 2 f_equiv.
    (* FIXME : change the definition of limit_preserving so that it
       applies even if the limti is not computed with compl. *)
    apply and_intro; [|apply and_intro; [|apply and_intro]].
    - iIntros "H". iDestruct ("H" $! 0) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0) as "(_&$&_)".
    - apply entails_equiv, equiv_dist=> ?. setoid_rewrite conv_compl=>/=.
      apply equiv_dist, entails_equiv. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_equiv, equiv_dist=> ?. setoid_rewrite conv_compl=>/=.
      apply equiv_dist, entails_equiv. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$)".
  Qed.

  Lemma fix_eqtype_subtype {A B} (f: A → B) g
    T `{!TypeContractive T} T' `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L f g ty ty' → eqtype E L f g (T ty) (T' ty')) →
    subtype E L f (fix_ty T) (fix_ty T').
  Proof. move=> Loop qL.
    have Incl: llctx_interp L qL -∗ □ (elctx_interp E -∗
      ∀n, type_incl f (Tn T n) (Tn T' n)).
    { rewrite intuitionistically_into_persistently -wand_forall persistently_forall.
      apply forall_intro=> n. rewrite -intuitionistically_into_persistently.
      move: qL. apply Loop. elim n=> [|??]; [apply base_eqtype|by apply Loop]. }
    rewrite Incl /type_incl -!persistent_and_sep /=. do 2 f_equiv.
    apply and_intro; [|apply and_intro; [|apply and_intro]].
    - iIntros "H". iDestruct ("H" $! 0) as "($&_)".
    - iIntros "H". iDestruct ("H" $! 0) as "(_&$&_)".
    - apply entails_equiv, equiv_dist=> ?. setoid_rewrite conv_compl=>/=.
      apply equiv_dist, entails_equiv. iIntros "H". iDestruct ("H" $! _) as "(_&_&$&_)".
    - apply entails_equiv, equiv_dist=> ?. setoid_rewrite conv_compl=>/=.
      apply equiv_dist, entails_equiv. iIntros "H". iDestruct ("H" $! _) as "(_&_&_&$)".
  Qed.

  Lemma fix_eqtype {A B} (f: A → B) g
    T `{!TypeContractive T} T' `{!TypeContractive T'} E L :
    (∀ty ty', eqtype E L f g ty ty' → eqtype E L f g (T ty) (T' ty')) →
    eqtype E L f g (fix_ty T) (fix_ty T').
  Proof. move=> Loop.
    have ?: ∀ty' ty, eqtype E L g f ty' ty → eqtype E L g f (T' ty') (T ty).
    { move=> ??[??]. split; apply Loop; by split. }
    split; by eapply fix_eqtype_subtype.
  Qed.

End subtyping.

Global Hint Resolve fix_subtype fix_eqtype : lrust_typing.
