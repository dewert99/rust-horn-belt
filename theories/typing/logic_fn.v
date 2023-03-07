From lrust.typing Require Export type.
From lrust.typing Require Import ghost shr_bor uniq_bor own product sum array bool int.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.
Implicit Type 𝔄l: (list syn_type).

Section typing.
  Context `{!typeG Σ}.

  Lemma plain_logic_fn {𝔄l 𝔅} (tyl: (hlist plain_type 𝔄l)) (tyr: plain_type 𝔅) (f: (plist of_syn_type 𝔄l) → 𝔅):
    logic_fn ((λ 𝔄 (x: plain_type 𝔄), (x: type 𝔄)) +<$> tyl) tyr f.
  Proof. 
    intros aπl. intros. simpl. exists [], (f (aπl -$ inhabitant)). 
    fun_ext. intros. simpl. f_equal. clear f.
    induction tyl; destruct aπl. done.
    destruct H as [(?&?&->) rest]. specialize (IHtyl ptl).
    simpl. f_equal. by apply IHtyl.
  Qed.

  Lemma ghost_deref_logic_fn {𝔄} (ty: type 𝔄) : logic_fn +[ghost ty] ty (λ '-[x], x).
  Proof. intros [gπ[]][(?&?&?)[]]. eexists _. simpl. done. Qed.

  Lemma shr_deref_logic_fn {𝔄} (ty: type 𝔄) κ : logic_fn +[(&shr{κ} ty)%T] ty (λ '-[x], x).
  Proof. intros [gπ[]][(?&?)[]]. eexists _. simpl. done. Qed.

  Lemma box_deref_logic_fn {𝔄} (ty: type 𝔄) : logic_fn +[(box ty)%T] ty (λ '-[x], x).
  Proof. intros [gπ[]][(?&?)[]]. eexists _. simpl. done. Qed.

  Lemma uniq_curr_logic_fn {𝔄} (ty: type 𝔄) κ : logic_fn +[(&uniq{κ} ty)%T] ty (λ '-[(xc, xf)], xc).
  Proof. intros [gπ[]][(?&?&?&_&?&?)[]]. eexists _. simpl. done. Qed. 

  Lemma prod_fst_logic_fn {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔄) : logic_fn +[(ty*ty')%T] ty (λ '-[(f, s)], f).
  Proof. intros [gπ[]][(?&?&?&_&?&?)[]]. eexists _. simpl. done. Qed. 

  Lemma prod_snd_logic_fn {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔄) : logic_fn +[(ty*ty')%T] ty' (λ '-[(f, s)], s).
  Proof. intros [gπ[]][(?&?&?&_&?&?)[]]. eexists _. simpl. done. Qed.

  Lemma prod_create_logic_fn {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔄) : logic_fn +[ty; ty'] (ty*ty')%T (λ '-[f; s], (f, s)).
  Proof. intros (gπ1&gπ2&[])((?&?)&(?&?)&[]). eexists _, _, _. done. Qed. 

  Lemma xprod_create_logic_fn {𝔄l} (tyl: typel 𝔄l) : logic_fn tyl (Π! tyl)%T (λ xl, xl).
  Proof. induction tyl; simpl.
    intros ??. eexists _. done.
    intros [aπ rπ][(?&?)?]. destruct (IHtyl rπ H0) as (ξlr&?).
    eexists _, (λ π, (_, _)). split. done. eexists _, _. done.
  Qed.

  Lemma xprod_destruct_logic_fn {𝔄l 𝔅l 𝔅} (tyl: typel 𝔄l) (tyoth: typel 𝔅l) (tyr: type 𝔅) (f: (plist of_syn_type (𝔄l ++ 𝔅l)) → 𝔅) : 
    logic_fn (tyl h++ tyoth) tyr f → logic_fn ((Π! tyl)%T +:: tyoth) tyr (λ '(xl -:: xoth), f (xl -++ xoth)).
  Proof.
    intros ?[lπ othπ][(?&?) ?]. unfold logic_fn in H.
    edestruct (H ((pfunsep lπ) -++ othπ)) as (?&?). rewrite -(semi_iso' _ _ lπ) in H0.
    clear H f. revert x H0. induction tyl; destruct (pfunsep lπ). done.
    intros ? (?&?&?&?&?).
    replace x0 with (λ π, (phd π, papply ptl π)) in H0. destruct H0 as (->&?&?).
    split. eexists _. done. rewrite -(semi_iso' papply _ ptl).
    eapply IHtyl. rewrite semi_iso'. done.
    fun_ext. intros. specialize (equal_f H x3). unfold to_cons_prod. simpl. 
    destruct (x0 x3). intros [= ->->]. done.
    eexists x0. f_exact H2.
    fun_ext. simpl. intros. rewrite papply_app semi_iso'. done. 
  Qed.

  Lemma xsum_inj_ghost_fun {𝔄l} (tyl: typel 𝔄l) i: logic_fn +[(tyl +!! i)] (Σ! tyl)%T (λ '-[v], pinj i v).
  Proof. intros [?[]][(?&?)[]]. eexists _, _, _. done. Qed.

  Lemma xsum_match_logic_fn {𝔄l 𝔅l 𝔅} (tyl: typel 𝔄l) (tyoth: typel 𝔅l) (tyr: type 𝔅) (fl: (plist (λ 𝔄, (plist of_syn_type (𝔄 :: 𝔅l)) → 𝔅) 𝔄l)): 
    forallHL_1 (λ _ ty f, logic_fn (ty +:: tyoth) tyr f) tyl fl → logic_fn (Σ! tyl +:: tyoth)%T tyr (λ '(x -:: rest), psum_match ((λ _ f x, f (x -:: rest)) -<$> fl) x).
  Proof.
    intros ?[pπ rπ][(?&i&vπ&->&?)?].
    apply (forallHL_1_lookup i) in H. simpl.
    edestruct (H (vπ -:: rπ)). simpl. split. by eexists _. done.
    exists x0. f_exact H2. 
    fun_ext. intros. rewrite psum_match_pinj. simpl.
    clear -fl.
    induction 𝔄l; destruct fl; inv_fin i; simpl; intros.
    done. rewrite IH𝔄l. done.
  Qed.

  Lemma ite_logic_fun {𝔄} (ty: type 𝔄): logic_fn +[bool_ty; ty; ty] ty (λ '-[i; t; e], if i then t else e).
  Proof. 
    intros (?&?&?&[]) ((?&[|]&->)&(?&?)&(?&?)&[]);
    eexists _; done.
  Qed.

  Lemma cut_logic_fun {𝔄l 𝔄 𝔅} (tyl: typel 𝔄l) (tyr1: type 𝔄) (tyr2: type 𝔅) f1 f2:
    logic_fn tyl tyr1 f1 → logic_fn (tyr1 +:: tyl) tyr2 f2 → logic_fn tyl tyr2 (λ xl, f2 (f1 xl -:: xl)).
  Proof.
    intros ????. destruct (H aπl H1). edestruct (H0 ((λ π, f1 (aπl -$ π)) -:: aπl)). split. by eexists. done.
    eexists _. done.
  Qed.

End typing.
