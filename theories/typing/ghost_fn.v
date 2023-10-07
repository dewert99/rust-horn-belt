From lrust.typing Require Export type ghost.
From lrust.typing Require Import shr_bor uniq_bor own product sum array bool int mod_ty fixpoint.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.
Implicit Type 𝔄l: (list syn_type).

Section core.
Context `{!typeG Σ}.
  Lemma ghost_fn_app `{!typeG Σ} {𝔄 𝔅} {aty: type 𝔄} {rty: ghost_fn_type 𝔅} {fπ xπ} : (ghost_fn_proph (aty → rty) fπ) → (ghost_fn_proph aty xπ) → (ghost_fn_proph rty (λ π, fπ π (xπ π))).
  Proof. intros ??. destruct H0. specialize (H _ _ H0). done. Qed.

  Lemma arg_ghost_fn `{!typeG Σ} {𝔄 𝔅} {tya: (type 𝔄)} {tyr: ghost_fn_type 𝔅} {fπ: (proph (𝔄 → 𝔅)%ST)} :
    (∀ xπ, (ghost_fn_proph tya xπ) → (ghost_fn_proph tyr (λ π, fπ π (xπ π)))) → ghost_fn_proph (tya → tyr) fπ.
  Proof. intros ????. simpl. apply H. eexists. done. Qed.

  Lemma ghost_fn_coerce {𝔄} {aty: type 𝔄} {bty: type 𝔄} {xπ} : (ghost_fn (aty → bty) id) → (ghost_fn_proph aty xπ) → (ghost_fn_proph bty xπ).
  Proof. intros ??. destruct H0. specialize (H _ _ H0). done. Qed.

  Lemma plain_arg_ghost_fn {𝔄 𝔅} {tya: (plain_type 𝔄)} {tyr: ghost_fn_type 𝔅} {fπ: (proph (𝔄 → 𝔅)%ST)} :
    (∀ x, (ghost_fn_proph tyr (λ π, fπ π x))) → ghost_fn_proph (tya → tyr) fπ.
  Proof.
    intros ???(?&->). simpl. apply H.
  Qed.

  Lemma plain_ret_ghost_fn {𝔄} {tya: (plain_type 𝔄)} x:
    ghost_fn tya x.
  Proof. eexists [], _. done. Qed.

  Lemma ghost_deref_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn ((ghost ty) → ty) id.
  Proof. intros ??(?&?). eexists _. done. Qed.

  Lemma shr_deref_ghost_fn {𝔄} {ty: type 𝔄} {κ} : ghost_fn ((&shr{κ} ty) → ty) id.
  Proof. intros ???. eexists _. done. Qed.

  Lemma shr_create_ghost_fn {𝔄} {ty: type 𝔄} {κ} : ghost_fn (ty → (&shr{κ} ty)%T) id.
  Proof. intros ???. eexists _. done. Qed.

  Lemma box_deref_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn ((box ty) → ty) id.
  Proof. intros ???. eexists _. done. Qed.

  Lemma box_create_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (ty → (box ty)%T) id.
  Proof. intros ???. eexists _. done. Qed.

  Definition uniq_curr {A B} := @fst A B.

  Lemma uniq_curr_ghost_fn {𝔄} {ty: type 𝔄} {κ} : ghost_fn ((&uniq{κ} ty) → ty) uniq_curr.
  Proof. intros ??(?&?&->&?&?). eexists _. done. Qed.

  Lemma pair_destruct_ghost_fn {𝔄 𝔄2 𝔅} {tya: (type 𝔄)} {tyb: (type 𝔄2)} {tyr: ghost_fn_type 𝔅} {fπ} :
    ghost_fn_proph (tya → tyb → tyr) (λ π a b, fπ π (a, b)) → ghost_fn_proph  ((tya * tyb) → tyr) fπ.
  Proof.
    intros ???(?&?&_&?&?). rewrite (surjective_pairing_fun vπ'). simpl. 
    do 2 (eapply ghost_fn_app in H; [|eexists _; done]). done.
  Qed.

  Lemma unit_destruct_ghost_fn {𝔅} {tyr: ghost_fn_type 𝔅} {fπ} :
    (ghost_fn_proph tyr (λ π, fπ π ())) → ghost_fn_proph (() → tyr) fπ.
  Proof.
    intros ????. f_exact H. fun_ext=>π. destruct (vπ' π). done.
  Qed.

  Lemma unit_create_ghost_fn: ghost_fn ()%T ().
  Proof. eexists _, (const -[]). done. Qed.

  Lemma pair_create_ghost_fn {𝔄 𝔅} {ty: type 𝔄} {ty': type 𝔅} : ghost_fn (ty → ty' → (ty*ty')%T) pair.
  Proof. intros ??????. eexists _, _, _. done. Qed. 

  Lemma mod_create_ghost_fn `{SameLevel 𝔄 𝔅} {ty: type 𝔄} {f: 𝔄 → 𝔅} : ghost_fn (ty → (<{f}> ty)%T) f.
  Proof. intros ???. eexists _, _. done. Qed. 

  Lemma mod_destruct_ghost_fn `{SameLevel 𝔄 𝔄'} {𝔅} {ty: type 𝔄} {tyr: ghost_fn_type 𝔅} {f: 𝔄 → 𝔄'} {fπ} :
    ghost_fn_proph (ty → tyr) (λ π a, fπ π (f a)) → ghost_fn_proph ((<{f}> ty) → tyr) fπ.
  Proof. fold of_syn_type. intros ???(?&->&?). eapply H0. done. Qed. 

  Lemma xprod_nil_ghost_fn : ghost_fn ((Π! +[])%T) nil_tt.
  Proof. eexists _. done. Qed.

  Lemma xprod_destruct_nil_ghost_fn {𝔅} {tyr: ghost_fn_type 𝔅} {fπ} :
    (ghost_fn_proph tyr (λ π, fπ π -[])) → ghost_fn_proph ((Π! +[]) → tyr) fπ.
  Proof.
    intros ????. f_exact H. fun_ext=>π. destruct (vπ' π). done.
  Qed.

  Lemma xsum_inj_ghost_fun {𝔄l} {tyl: typel 𝔄l} i: ghost_fn ((tyl +!! i) → (Σ! tyl)%T) (pinj i).
  Proof. intros ???. eexists _, _, _. done. Qed.

  Lemma xsum_destruct_ghost_fn {𝔄l 𝔅} {tyl: typel 𝔄l} {tyr: ghost_fn_type 𝔅} {fπ} : 
    (forall i, ghost_fn_proph ((tyl +!! i) → tyr) (λ π a, fπ π (pinj i a)) ) → ghost_fn_proph ((Σ! tyl) → tyr) fπ.
  Proof.
    intros ?. intros ??(i&?&->&?). specialize (H i). eapply ghost_fn_app in H; [|eexists _; done]. done.
  Qed.

  Lemma fix_ind_ghost_fn {𝔄 𝔅} {T : type 𝔄 → type 𝔄} `{!TypeContractive T} {tyr: ghost_fn_type 𝔅} {fπ} :
   (forall (ty: type 𝔄), ghost_fn_proph (ty → tyr) fπ → ghost_fn_proph ((T ty) → tyr) fπ ) → ghost_fn_proph ((fix_ty T) → tyr) fπ.
  Proof. intros ???(?&?).  eapply ghost_fn_app; [|eexists _; done]. clear H0. induction x. intros ??[]. apply H. done. Qed.

  Lemma fix_unfold_ghost_fn {𝔄} {T : type 𝔄 → type 𝔄} `{!TypeContractive T} :
    ghost_fn ((fix_ty T) → T (fix_ty T)) id.
  Proof. intros ???. eexists _. setoid_rewrite (type_ne_ty_proph' (fix_ty T) (fix_defs.base T)); [|done]. by apply (fix_defs.Tn_ty_proph_const T 0 1). Qed.

  Lemma fix_fold_ghost_fn {𝔄} {T : type 𝔄 → type 𝔄} `{!TypeContractive T} :
  ghost_fn (T (fix_ty T) → (fix_ty T)) id.
  Proof. intros ???. eexists _. setoid_rewrite (type_ne_ty_proph' (fix_ty T) (fix_defs.base T)) in H; [|done]. by apply (fix_defs.Tn_ty_proph_const T 1 0). Qed.

End core.


Declare Scope ghost_fn_builder_scope.
Bind Scope ghost_fn_builder_scope with ghost_fn_proph.
Delimit Scope ghost_fn_builder_scope with GB.
Infix "$" := ghost_fn_app : ghost_fn_builder_scope.
Notation "%" := plain_ret_ghost_fn.
Notation "( x , y , .. , z )" := ((pair_create_ghost_fn $ .. ((pair_create_ghost_fn $ x) $ y) ..) $ z)%GB : ghost_fn_builder_scope.
Notation "( )" := unit_create_ghost_fn: ghost_fn_builder_scope.
Notation "( `inj` i x )" := ((xsum_inj_ghost_fun i) $ x)%GB: ghost_fn_builder_scope.
Notation "'λ2' x , t " := (arg_ghost_fn (λ _ x , t))
(at level 200, right associativity): ghost_fn_builder_scope.
Notation "'λp' x , t " := (plain_arg_ghost_fn (λ x , t))
(at level 200, right associativity): ghost_fn_builder_scope.
Notation "'λ' x .. y , t " := (λ2 x , .. (λ2 y, t)..)%GB
(at level 200, x binder, y binder, right associativity): ghost_fn_builder_scope.

Section typing.
  Context `{!typeG Σ}.

  Lemma forallHL_1_app {A F G Xl Xl2} (Φ: ∀X, F X → G X → Prop)
    (xl: hlist F Xl) (yl: plist G Xl) (xl2: hlist F Xl2) (yl2: plist G Xl2) : 
   @forallHL_1 A F G (Xl ++ Xl2) Φ (xl h++ xl2) (yl -++ yl2) ↔ forallHL_1 Φ xl yl /\ forallHL_1 Φ xl2 yl2.
   Proof. induction xl; destruct yl; try done. simpl. intuition. simpl. rewrite IHxl. intuition. Qed.

  Lemma papply_map {A} {F: A → Type} {B Xl}
    (fl: plist (λ X, B → F X) Xl) x: 
  fl -$ x = (λ _ f, f x) -<$> fl.
  Proof. move: fl. induction Xl; destruct fl; try done. simpl. by rewrite IHXl. Qed.

  Lemma pmap_sepl {A} {F G: A → Type} {Xl Yl} (f: ∀X, F X → G X)
        (xl: plist F (Xl++Yl)):
    f -<$> (psepl xl) = (psepl (f -<$> xl)).
  Proof. move: xl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

  Lemma pmap_sepr {A} {F G: A → Type} {Xl Yl} (f: ∀X, F X → G X)
        (xl: plist F (Xl++Yl)):
    f -<$> (psepl xl) = (psepl (f -<$> xl)).
  Proof. move: xl. elim Xl; [done|]=>/= ?? IH [??]. by rewrite IH. Qed.

  Lemma pmap_lookup {A} {F G: A → Type} {Xl} (f: ∀X, F X → G X) i
        (xl: plist F Xl):
    (f -<$> xl) -!! i = f _ (xl -!! i).
  Proof. move: xl. induction Xl; simpl in i; inv_fin i; destruct xl; try done. simpl. by rewrite IHXl. Qed.

  Program Definition id_proph {𝔄} (vπ: proph 𝔄): type 𝔄 := {|
    st_size := 0;  st_lfts :=[];  st_E := [];
    st_proph vπ' ξl := vπ' = vπ /\ vπ' ./[𝔄] ξl;
    st_own vπ d tid vl := False
  |}%I.
  Next Obligation. by iIntros. Qed.
  Next Obligation. done. Qed.
  Next Obligation. by iIntros. Qed.
  Next Obligation. move=> /= ????[??]. done. Qed.

  Lemma nat_ind_ghost_fn {𝔄 𝔅} {ty : type 𝔄} {tyr: ghost_fn_type 𝔅} {fπ} :
  (forall (ty': (type Zₛ)), (ghost_fn_proph (ty' → tyr) fπ → ghost_fn_proph (ty' → tyr) (λ π x, (fπ π (S (Z.to_nat x))))))
   → (ghost_fn_proph tyr (λ π, fπ π 0)) → ghost_fn_proph (int → tyr) (λ π x, fπ π (Z.to_nat x)).
  Proof. 
    fold of_syn_type. intros ??. refine (λp x, _)%GB. induction (Z.to_nat x). done. 
    epose (H _ (λ x, _) $ _)%GB. simpl in g. Unshelve. 2:{eapply id_proph. exact (const n). }
    2:{exact (const n). } simpl in g. f_exact g. fun_ext=>?. rewrite Nat2Z.id. done. unfold ghost_fn_proph in x.
    destruct x as [? [-> ?]]. done. eexists []. done.
  Qed.

  Opaque ghost_fn_proph.

  Lemma succ_ghost_fn {fπ: (proph nat)} : ghost_fn_proph int (λ π, (fπ π)) →  ghost_fn_proph int (λ π, S (fπ π) ).
  Proof. 
    intro. erewrite functional_extensionality. eapply ((λp x, _) $ H )%GB. Unshelve. 2:{exact (λ π x, S (Z.to_nat x)). }
    simpl. intros. rewrite Nat2Z.id. done. simpl. eapply plain_ret_ghost_fn. 
  Qed.



  Lemma plain_ghost_fn {𝔄l 𝔅} (tya: (hlist plain_type 𝔄l)) (tyr: plain_type 𝔅) x:
    ghost_fn (curry_ty ((λ _ (x: plain_type _), (x: type _)) +<$> tya) tyr) x.
  Proof. induction tya. apply plain_ret_ghost_fn. apply plain_arg_ghost_fn=>?. apply IHtya. Qed.

  Lemma binop_ghost_fn f: ghost_fn (int → int → int) f.
  Proof. apply (plain_ghost_fn +[_; _]). Qed.

  Lemma cmp_ghost_fn f: ghost_fn (int → int → bool_ty) f.
  Proof. apply (plain_ghost_fn +[_; _]). Qed.

  Lemma curry_fn_ghost_fn {𝔄l 𝔅 𝔅'} {tyl: typel 𝔄l} {tyr: type 𝔅} {tyr': ghost_fn_type 𝔅'} {fπ gπ} : 
    ghost_fn_proph (curry_ty tyl tyr) (λ π, (curry_fn (fπ π))) →  ghost_fn_proph (tyr→tyr') gπ → ghost_fn_proph (curry_ty tyl tyr') (λ π, (curry_fn (λ x, gπ π (fπ π x)))).
  Proof. 
     induction tyl; simpl; intros. eapply (H0 $ H)%GB.
     eapply (λ HF, (IHtyl _ (H $ HF) H0))%GB.
  Qed.

  Definition fst_ghost_fn {𝔄 𝔅} {ty: type 𝔄} {ty': type 𝔅} : ghost_fn ((ty*ty') → ty) fst
    := (pair_destruct_ghost_fn (λ a b, a))%GB.

  Definition snd_ghost_fn {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) : ghost_fn ((ty*ty') → ty') snd
    := (pair_destruct_ghost_fn (λ a b, b))%GB.

  Lemma xprod_cons_ghost_fn {𝔄 𝔅l} {ty: type 𝔄} {tyl': typel 𝔅l} : ghost_fn (ty → (Π! tyl') → (Π! (ty+::tyl'))%T) (-::).
  Proof. eapply (λ a b, _)%GB. Unshelve. exact (mod_create_ghost_fn $ ((pair_create_ghost_fn $ a) $ b))%GB. Qed.

  Lemma xprod_destruct_cons_ghost_fn {𝔄 𝔄l 𝔅} {tya: (type 𝔄)} {tyb: (typel 𝔄l)} {tyr: ghost_fn_type 𝔅} {fπ} :
    (ghost_fn_proph (tya → (Π! tyb)%T → tyr) (λ π a b, fπ π (a -:: b))) → ghost_fn_proph ((Π! (tya +:: tyb)) → tyr) fπ.
  Proof. intros ?. eapply mod_destruct_ghost_fn, pair_destruct_ghost_fn. done. Qed.

  Lemma xprod_create_ghost_fn {𝔄l} (tyl: typel 𝔄l): 
    ghost_fn (curry_ty tyl (Π! tyl)%T) (curry_fn (λ x, (x: (Π! 𝔄l)%ST))).
  Proof.
   induction tyl; simpl. exact xprod_nil_ghost_fn. exact (λ x, (curry_fn_ghost_fn IHtyl (xprod_cons_ghost_fn $ x)))%GB.
  Qed.

  Lemma xprod_destruct_ghost_fn {𝔄 𝔄l 𝔅} (tyl: (typel 𝔄l)) (tyr: ghost_fn_type 𝔅) (fπ: (proph ((Π! 𝔄l) → 𝔅)%ST)):
    (ghost_fn_proph (curry_ty tyl tyr) (λ π, (curry_fn (fπ π)))) → ghost_fn_proph ((Π! tyl) → tyr) fπ.
  Proof.
    induction tyl; simpl; intros H. apply (xprod_destruct_nil_ghost_fn H). 
    apply (xprod_destruct_cons_ghost_fn (λ x, IHtyl _ (H $ x)))%GB.
  Qed.

  Lemma xprod_project_ghost_fn {𝔄 𝔄l 𝔅} (tyl: (typel 𝔄l)) i:
    (ghost_fn ((Π! tyl)%T → (tyl +!! i)) (λ x, x -!! i)).
  Proof.  
    induction tyl; simpl; fold of_syn_type. inv_fin i.
    eapply xprod_destruct_cons_ghost_fn; fold of_syn_type. do 2 apply arg_ghost_fn=>??. inv_fin i; simpl. done.
    intros. specialize (IHtyl i). eapply  ghost_fn_app in IHtyl; [|done]. done.
  Qed.

  Lemma xsum_match_ghost_fn {𝔄l 𝔅} (tyl: typel 𝔄l) (tyr: ghost_fn_type 𝔅) (fl: (plist (λ 𝔄, (proph (𝔄 → 𝔅)%ST)) 𝔄l)): 
    forallHL_1 (λ _ ty fπ, ghost_fn_proph (ty→tyr) fπ) tyl fl → ghost_fn_proph ((Σ! tyl)%T→tyr) (λ π x, psum_match (fl -$ π) x).
  Proof.
    intros. apply xsum_destruct_ghost_fn. intros. apply (forallHL_1_lookup i) in H. 
    f_exact H. do 2 fun_ext=>?. rewrite psum_match_pinj papply_map pmap_lookup. done.
  Qed.

  Lemma ite_ghost_fn {𝔄} {ty: type 𝔄} : ghost_fn (bool_ty→ty→ty→ty) (λ i t e, if i then t else e).
  Proof. fold of_syn_type. eapply (λp i, λ t e, _)%GB. Unshelve. destruct i; done. Qed.

End typing.

Infix "-::" := xprod_cons_ghost_fn : ghost_fn_builder_scope.