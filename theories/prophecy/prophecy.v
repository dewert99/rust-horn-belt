Import EqNotations.
From Coq Require Import Sorted.
From stdpp Require Import strings.
From iris.algebra Require Import auth cmra functions gmap csum frac agree.
From iris.bi Require Import fractional.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From lrust.util Require Import basic vector discrete_fun.
From lrust.prophecy Require Export syn_type.

(** * Basic Notions *)

Record proph_var := PrVar { pv_ty: syn_typei; pv_id: positive }.
Add Printing Constructor proph_var.

Global Instance proph_var_eq_dec: EqDecision proph_var.
Proof. solve_decision. Qed.

Definition proph_asn := ∀ξ: proph_var, ξ.(pv_ty).
Notation proph A := (proph_asn → A).

Implicit Type (ξ ζ: proph_var) (ξl ζl: list proph_var) (π: proph_asn).

Global Instance proph_asn_inhabited: Inhabited proph_asn.
Proof. apply populate. case=> ??. apply inhabitant. Qed.

(** * Prophecy Dependency *)
Definition pv_level ξ := (ghost_level (proj1_sig ξ.(pv_ty))).
Notation pv_sty ξ := (proj1_sig ξ.(pv_ty)).
Local Definition pv_in ξ ξl level := (pv_level ξ <= level) ∧ (ξ ∈ ξl ∨ pv_level ξ < level).
Local Notation "ξ .∈{ ξl , level }" := (pv_in ξ ξl level)
  (at level 70, format "ξ .∈{ ξl , level }").

Local Definition proph_asn_eqv ξl level π π' := ∀ξ, ξ.∈{ξl, level} → π ξ = π' ξ.
Local Notation "π .≡{ ξl , level }≡ π'" := (proph_asn_eqv ξl level π π')
  (at level 70, format "π  .≡{ ξl , level }≡  π'").

Definition proph_dep {A} (vπ: proph A) (ξl: list proph_var) level :=
  ∀π π', π .≡{ξl, level}≡ π' → vπ π = vπ π'.
Notation "vπ ./{ level } ξl" := (proph_dep vπ ξl level) (at level 70, format "vπ  ./{ level }  ξl").
Notation "vπ ./[ 𝔄 ] ξl" := (proph_dep vπ ξl (ghost_level 𝔄)) (at level 70, format "vπ  ./[ 𝔄 ]  ξl").

(** ** Lemmas *)

Lemma proph_dep_one ξ : (.$ ξ) ./{pv_level ξ} [ξ].
Proof. move=> ?? Eqv. apply Eqv. split. lia. left. constructor. Qed.

Lemma proph_dep_ghost ξ : (.$ ξ) ./{S (pv_level ξ)} [].
Proof. move=> ?? Eqv. apply Eqv. split. lia. right. lia. Qed.

Lemma proph_dep_ghost' {A} (vπ: proph A) ξl' ξl level: vπ ./{level} ξl → vπ ./{S level} ξl'.
Proof. move=> H ?? Eqv. apply H. intros ?[? _]. apply Eqv. split. lia. right. lia. Qed.

Lemma proph_dep_constr {A B} (f: A → B) vπ ξl level: vπ ./{level} ξl → f ∘ vπ ./{level} ξl.
Proof. move=> Dep ?? /Dep ?. by apply (f_equal f). Qed.

Lemma proph_dep_mono {A} ξl ζl (vπ: proph A) level :
  ξl ⊆ ζl → vπ ./{level} ξl → vπ ./{level} ζl.
Proof. 
  move=> In Dep ?? Eqv. apply Dep => ?[?[?|?]]; apply Eqv; 
  split. done. left. by apply In. done. right. done.
Qed.

Lemma proph_dep_level_mono {A} level level' ξl (vπ: proph A) :
  level <= level' → vπ ./{level} ξl → vπ ./{level'} ξl.
Proof. 
  move=> In Dep ?? Eqv. apply Dep => ?[?[?|?]]; apply Eqv; 
  split. lia. left. done. lia. right. lia.
Qed.

Lemma proph_dep_constr2 {A B C} (f: A → B → C) vπ wπ ξl ζl level :
  vπ ./{level} ξl → wπ ./{level} ζl → f ∘ vπ ⊛ wπ ./{level} ξl ++ ζl.
Proof.
  move=> Dep Dep' ?? Eqv.
  eapply proph_dep_mono, (.$ Eqv) in Dep, Dep'; [|set_solver..]=>/=. by f_equal.
Qed.

Lemma proph_dep_constr3 {A B C D} (f: A → B → C → D) uπ vπ wπ ξl₀ ξl₁ ξl₂ level :
  uπ ./{level} ξl₀ → vπ ./{level} ξl₁ → wπ ./{level} ξl₂ → f ∘ uπ ⊛ vπ ⊛ wπ ./{level} ξl₀ ++ ξl₁ ++ ξl₂.
Proof.
  move=> Dep₀ Dep₁ Dep₂ ?? Eqv.
  eapply proph_dep_mono, (.$ Eqv) in Dep₀, Dep₁, Dep₂; [|set_solver..]=>/=. by f_equal.
Qed.

Lemma proph_dep_destr {A B} f `{!@Inj A B (=) (=) f} vπ ξl level:
  f ∘ vπ ./{level} ξl → vπ ./{level} ξl.
Proof. by move=> Dep ?? /Dep/(inj f) ?. Qed.

Lemma proph_dep_destr2 {A B C} f `{!@Inj2 A B C (=) (=) (=) f} vπ wπ ξl level:
  f ∘ vπ ⊛ wπ ./{level} ξl → vπ ./{level} ξl ∧ wπ ./{level} ξl.
Proof.
  move=> Dep. split; move=> ?? /Dep Eq; apply (inj2 f) in Eq; tauto.
Qed.

Lemma proph_dep_destr3 {A B C D} f `{!@Inj3 A B C D (=) (=) (=) (=) f} uπ vπ wπ ξl level:
  f ∘ uπ ⊛ vπ ⊛ wπ ./{level} ξl → uπ ./{level} ξl ∧ vπ ./{level} ξl ∧ wπ ./{level} ξl.
Proof.
  move=> Dep. split; [|split]; move=> ?? /Dep/= Eq; apply (inj3 f) in Eq; tauto.
Qed.

Lemma proph_dep_singleton {A} (vπ: proph A) level :
  (∀ u v : A, u = v) → vπ ./{level} [].
Proof. by intros ????. Qed.

Lemma proph_dep_eq {A} (vπ wπ: proph A) ξl level:
  vπ ./{level} ξl → vπ = wπ → wπ ./{level} ξl.
Proof. by move=> ?<-. Qed.

Lemma proph_dep_prod {A B} ξl ζl (vπ: proph (A * B)) level1 level2:
  fst ∘ vπ ./{level1} ξl → snd ∘ vπ ./{level2} ζl → vπ ./{level1 `max` level2} ξl ++ ζl.
Proof.
  move=> ??. rewrite (surjective_pairing_fun vπ). apply proph_dep_constr2; eapply proph_dep_level_mono; [ |done| |done]; lia.
Qed.

Lemma proph_dep_list_prod {A B} ξl ζl (f: proph (list (A * B))) level :
  map fst ∘ f ./{level} ξl → map snd ∘ f ./{level} ζl → f ./{level} ξl ++ ζl.
Proof. move=> ??. rewrite -(zip_fst_snd_fun f). by apply proph_dep_constr2. Qed.

Lemma proph_dep_vec_S {A n} ξl ζl (vπ: proph (vec A (S n))) level:
  vhd ∘ vπ ./{level} ξl → vtl ∘ vπ ./{level} ζl → vπ ./{level} ξl ++ ζl.
Proof.
  move=> ??. rewrite (surjective_vcons_fun vπ). by apply proph_dep_constr2.
Qed.

Lemma proph_dep_vinsert {A n} (vπl: vec (proph A) n) i wπ ξ ζl ζl' level:
  vapply (vtake i vπl) ./{level} ζl → wπ ./{level} [ξ] → vapply (vdrop' i vπl) ./{level} ζl' →
  vapply (vinsert i wπ vπl) ./{level} ζl ++ ξ :: ζl'.
Proof.
  move=> ???. rewrite vapply_insert_backmid.
  have ->: ξ :: ζl' = [ξ] ++ ζl' by done. by apply proph_dep_constr3.
Qed.

Local Lemma ForallOrdPairs_nil {A} (R: relation A):
  (ForallOrdPairs R []) <-> True.
Proof. split. intros. by inversion H. intros ?. by apply FOP_nil. Qed.

Local Lemma ForallOrdPairs_cons {A} (R: relation A) x l:
  (ForallOrdPairs R (x :: l)) <-> ForallOrdPairs R l ∧ Forall (R x) l.
Proof. split. intros. by inversion H. intros [??]. by apply FOP_cons. Qed.

Local Lemma ForallOrdPairs_app {A} (R: relation A) (l l': list A):
  (ForallOrdPairs R (l ++ l')) <-> (ForallOrdPairs R l ∧ ForallOrdPairs R l' ∧ Forall (λ x, Forall (R x) l') l).
Proof. induction l. 
  rewrite left_id ForallOrdPairs_nil. split. intros. done. intros [?[??]]. done.
  rewrite -app_comm_cons 2! ForallOrdPairs_cons IHl Forall_app Forall_cons. split.
  intros [[?[??]][??]]. done.
  intros [[??][?[??]]]. done.
Qed.

(** * Prophecy Log *)

Record proph_log_item :=
  ProphLogItem { pli_pv: proph_var; pli_val: proph pli_pv.(pv_ty) }.
Local Notation ".{ ξ := vπ }" := (ProphLogItem ξ vπ)
  (at level 1, format ".{ ξ  :=  vπ }").

Local Definition proph_log := list proph_log_item.

Local Definition res (L: proph_log) := pli_pv <$> L.

(* Local Definition proph_asn_eqv_out ξl π π' := ∀ξ, ξ ∉ ξl → π ξ = π' ξ.
Local Notation "π .≡~{ ξl }≡ π'" := (proph_asn_eqv_out ξl π π')
  (at level 70, format "π  .≡~{ ξl }≡  π'").
Local Definition proph_dep_out {A} (vπ: proph A) ξl :=
  ∀ π π', π .≡~{ ξl }≡ π' → vπ π = vπ π'.
Local Notation "vπ ./~ ξl" := (proph_dep_out vπ ξl)
  (at level 70, format "vπ  ./~  ξl").

Local Lemma proph_dep_out_mono {A} ξl ζl (vπ: proph A) :
vπ ./~ ξl → ζl ⊆ ξl → vπ ./~ ζl.
Proof. 
  move=> Dep In ?? Eqv. apply Dep => ? nin; apply Eqv => ?; apply nin. 
  by apply In.
Qed. *)

Local Definition proph_asn_eqv_out P π π' := ∀ξ, ~(P ξ) → π ξ = π' ξ.
Local Notation "π .≡~{ P }≡ π'" := (proph_asn_eqv_out P π π')
  (at level 70, format "π  .≡~{ P }≡  π'").
Local Definition proph_dep_out {A} (vπ: proph A) P :=
  ∀ π π', π .≡~{ P }≡ π' → vπ π = vπ π'.
Local Notation "vπ ./~ P" := (proph_dep_out vπ P)
  (at level 70, format "vπ  ./~  P").

Local Lemma proph_dep_out_mono {A} (P Q: _ → Prop) (vπ: proph A) :
 vπ ./~ P → (∀ ξ, Q ξ → P ξ) → vπ ./~ Q.
Proof. 
  move=> Dep In ?? Eqv. apply Dep => ? nin; apply Eqv => ?; apply nin. 
  by apply In.
Qed.

Notation level_lt ξ ξ' := ((pv_level ξ) < (pv_level ξ')).

Local Fixpoint proph_log_ok L :=
  match L with
  | [] => True
  | .{ξ := vπ} :: L' => ξ ∉ res L' ∧ vπ ./~ (λ ξ', ξ' ∈ res L ∨ level_lt ξ ξ') ∧ proph_log_ok L'
  end.
Local Notation ".✓ L" := (proph_log_ok L) (at level 20, format ".✓  L").


Local Notation StronglySorted := ForallOrdPairs.

Local Fixpoint insert_sorted {A} (x: A) (L: list A) R `{RelDecision A A R}:=
  match L with
  | [] => [x]
  | y :: L' => if decide (R x y) then x :: L else y :: insert_sorted x L' R
  end.

Local Lemma insert_sorted_correct {A} (x: A) L R `{RelDecision A A R} `{Transitive A R}:
 (StronglySorted R L) → ∃ L1 L2, L = L1 ++ L2 ∧ insert_sorted x L R = L1 ++ x :: L2 ∧ Forall (R x) L2 ∧ Forall (λ y, ~(R x y)) L1.
Proof. 
  intros. induction L as [|y L]. exists [], []. done.
  rewrite ForallOrdPairs_cons in H1.
  destruct H1 as [ssrest ssfirst].
  simpl. destruct (decide (R x y)). exists [], (y :: L).
  rewrite 2! left_id. do 2 split; [done|]. split; [|done].
  apply Forall_cons. split. done. apply (Forall_impl _ _ _ ssfirst).
  intros. transitivity y. done. done.
  destruct (IHL ssrest) as (L1&L2&->&->&sL1&sL2).
  exists (y :: L1), L2. 
  rewrite 2! app_comm_cons. do 3 split; [done|].
  apply Forall_cons. split. done. done.
Qed.

Local Lemma insert_sorted_sorted {A} (x: A) L R `{RelDecision A A R} `{Transitive A R} `{Total A R}:
 (StronglySorted R L) → (StronglySorted R (insert_sorted x L R)).
Proof.
  intros. destruct (insert_sorted_correct x L R H2) as (L1&L2&->&->&sL2&sL1).
  rewrite ForallOrdPairs_app in H2. destruct H2 as (ssL1&ssL2&sL12).
  rewrite ForallOrdPairs_app ForallOrdPairs_cons.
  setoid_rewrite Forall_cons. rewrite Forall_and. split; [done|]. split; [done|].
  split. apply (Forall_impl _ _ _ sL1). intros. by apply total_not. done.
Qed.

Local Lemma insert_sorted_perm {A} (x: A) L R `{RelDecision A A R} `{Transitive A R}:
 (StronglySorted R L) → x :: L ≡ₚ (insert_sorted x L R).
Proof.
  intros. destruct (insert_sorted_correct x L R H1) as (L1&L2&->&->&_).
  apply Permutation_middle.
Qed.

Local Fixpoint insertion_sort {A} (L: list A) R `{RelDecision A A R} :=
  match L with
  | [] => []
  | x :: L' => insert_sorted x (insertion_sort L' R) R
  end.

Local Lemma insertion_sort_sorted {A} L R `{RelDecision A A R} `{Transitive A R} `{Total A R}:
  (StronglySorted R (insertion_sort L R)).
Proof.
  induction L; simpl. by apply ForallOrdPairs_nil.
  by apply insert_sorted_sorted.
Qed.

Local Lemma insertion_sort_perm {A} L R `{RelDecision A A R} `{Transitive A R} `{Total A R}:
  (L ≡ₚ (insertion_sort L R)).
Proof.
  induction L; simpl. done.
  rewrite -insert_sorted_perm. f_equiv. done. 
  by apply insertion_sort_sorted.
Qed.

Local Definition log_item_le (li1 li2: proph_log_item) := pv_level li1.(pli_pv) <= pv_level li2.(pli_pv).

Global Instance log_item_le_transitive: Transitive log_item_le.
Proof. unfold log_item_le. intros ? *. by transitivity (pv_level (pli_pv y)). Qed.

Global Instance log_item_le_total: Total log_item_le.
Proof. unfold log_item_le. intros ? *. lia. Qed.

Local Instance log_item_le_decision: RelDecision log_item_le.
Proof. unfold log_item_le. solve_decision. Qed.

Local Definition proph_asn_eqv_out_l level π π' := ∀ξ, (pv_level ξ) > level → π ξ = π' ξ.
Local Notation "π .≡>{ level }≡ π'" := (proph_asn_eqv_out_l level π π')
  (at level 70, format "π  .≡>{ level }≡  π'").
Local Definition proph_dep_out_l {A} (vπ: proph A) level :=
  ∀ π π', π .≡>{ level }≡ π' → vπ π = vπ π'.
Local Notation "vπ ./> level" := (proph_dep_out_l vπ level)
  (at level 70, format "vπ  ./>  level").

Local Definition proph_log_ok' L:= (proph_log_ok (insertion_sort L log_item_le)) ∧ Forall (λ pli, pli.(pli_val) ./> (pv_level pli.(pli_pv))) L.

Local Notation ".✓' L" := (proph_log_ok (insertion_sort L log_item_le)) (at level 20, format ".✓'  L").

(* Local Definition proph_asn_eqv_out' ξl level π π' := ∀ξ, ~(ξ.∈{ξl, level}) → π ξ = π' ξ.
Local Notation "π .≡~{ ξl , level }≡ π'" := (proph_asn_eqv_out' ξl level π π')
  (at level 70, format "π  .≡~{ ξl , level }≡  π'").
Local Definition proph_dep_out' {A} (vπ: proph A) ξl level :=
  ∀ π π', π .≡~{ ξl , level }≡ π' → vπ π = vπ π'.
Local Notation "vπ ./~{ level } ξl" := (proph_dep_out' vπ ξl level)
  (at level 70, format "vπ  ./~{ level }  ξl"). *)

Local Definition proph_sat π L := Forall (λ pli, π pli.(pli_pv) = pli.(pli_val) π) L.
Local Notation "π ◁ L" := (proph_sat π L) (at level 70, format "π  ◁  L").

(** ** Satisfiability *)

Local Definition proph_upd ξ vπ π : proph_asn := λ ζ,
  match decide (ξ = ζ) with left eq => rew eq in vπ π | right _ => π ζ end.
Local Notation ":<[ ξ := vπ ]>" := (proph_upd ξ vπ)
  (at level 5, format ":<[ ξ  :=  vπ ]>").

Local Lemma proph_upd_lookup π ξ vπ : :<[ξ := vπ]> π ξ = vπ π.
Proof. rewrite /proph_upd. case (decide (ξ = ξ))=> [?|?]; by [simpl_eq|]. Qed.
Local Lemma proph_upd_lookup_ne π ξ vπ ζ : ξ ≠ ζ → :<[ξ := vπ]> π ζ = π ζ.
Proof. rewrite /proph_upd. by case (decide (ξ = ζ))=> [?|?]. Qed.

Local Fixpoint proph_modify π L :=
  match L with
  | [] => π
  | .{ξ := vπ} :: L' => proph_modify (:<[ξ := vπ]> π) L'
  end.
Local Notation "π ! L" := (proph_modify π L) (at level 30, format "π  !  L").

Local Definition proph_modify' π L := proph_modify π (insertion_sort L log_item_le).
Local Notation "π !' L" := (proph_modify' π L) (at level 30, format "π  !'  L").

Local Lemma proph_modify_eqv L : ∀π, π ! L .≡~{(.∈ res L )}≡ π.
Proof.
  elim L=>/= [|[??]? IH]; [done|]=> > /not_elem_of_cons [??].
  rewrite IH; [|done]. by apply proph_upd_lookup_ne.
Qed.

Local Lemma proph_ok_modify_sat L : .✓ L → ∀π, π ! L ◁ L.
Proof.
  rewrite /proph_sat. elim: L=>/= [|[ξ vπ] L' IH]; [done|]. move=> [?[? /IH ?]]?.
  apply Forall_cons=>/=. split; [|done]. rewrite proph_modify_eqv; [|done].
  rewrite proph_upd_lookup. set L := .{ξ := vπ} :: L'.
  assert (vπ ./~ (.∈ res L )) as Dep'. eapply proph_dep_out_mono; [done|]. intros. left. done.
  symmetry. apply Dep', (proph_modify_eqv L).
Qed.

Local Lemma proph_ok_modify_sat' L : .✓' L → ∀π, π !' L ◁ L.
Proof.
  intros ??. specialize (proph_ok_modify_sat _ H π) as H'.
  unfold proph_sat. rewrite /proph_sat in H'. revert H'. eassert (impl _ _); [|done]. f_equiv. rewrite -insertion_sort_perm. done.
Qed.

Local Lemma proph_ok_sat L : .✓' L → ∃π, π ◁ L.
Proof. exists (inhabitant !' L). by apply proph_ok_modify_sat'. Qed.

(** * Prophecy Camera *)

Local Definition proph_itemR (𝔄i: syn_typei) :=
  csumR fracR (agreeR (leibnizO (proph 𝔄i))).
Local Definition proph_gmapUR 𝔄i := gmapUR positive (proph_itemR 𝔄i).
Local Definition proph_smryUR := discrete_funUR proph_gmapUR.
Definition prophUR: ucmra := authUR proph_smryUR.

Local Definition aitem {𝔄i} vπ : proph_itemR 𝔄i := Cinr (to_agree vπ).
Local Definition fitem {𝔄i} (q: Qp) : proph_itemR 𝔄i := Cinl q.
Local Definition line ξ it : proph_smryUR := .{[ξ.(pv_ty) := {[ξ.(pv_id) := it]}]}.
Local Definition add_line ξ it (S: proph_smryUR) : proph_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_id) := it]> (S ξ.(pv_ty))]> S.

Definition prophΣ: gFunctors := #[GFunctor prophUR].
Class prophPreG Σ := ProphPreG { proph_preG_inG :> inG Σ prophUR }.
Class prophG Σ := ProphG { proph_inG :> prophPreG Σ; proph_name: gname }.
Global Instance subG_prophPreG Σ : subG prophΣ Σ → prophPreG Σ.
Proof. solve_inG. Qed.

Definition prophN: namespace := nroot .@ "proph".

(** * Iris Propositions *)

Local Definition proph_sim (S: proph_smryUR) (L: proph_log) :=
  ∀ξ vπ, S ξ.(pv_ty) !! ξ.(pv_id) ≡ Some (aitem vπ) ↔ .{ξ := vπ} ∈ L.
Local Notation "S :~ L" := (proph_sim S L) (at level 70, format "S  :~  L").

Section defs.
Context `{!invGS Σ, !prophG Σ}.

(** Prophecy Context *)
Local Definition proph_inv: iProp Σ :=
  ∃S, ⌜∃L, .✓' L ∧ S :~ L⌝ ∗ own proph_name (● S).
Definition proph_ctx: iProp Σ := inv prophN proph_inv.

(** Prophecy Token *)
Definition proph_tok (ξ: proph_var) (q: Qp) : iProp Σ :=
  own proph_name (◯ line ξ (fitem q)).

(** Prophecy Observation *)
Local Definition proph_atom pli : iProp Σ :=
  own proph_name (◯ line pli.(pli_pv) (aitem pli.(pli_val))).
Definition proph_obs (φπ: proph Prop) : iProp Σ :=
  ∃L, ⌜∀π, π ◁ L → φπ π⌝ ∗ [∗ list] pli ∈ L, proph_atom pli.
End defs.

Notation "q :[ ξ ]" := (proph_tok ξ q)
  (at level 2, left associativity, format "q :[ ξ ]") : bi_scope.
Notation "q :+[ ξl ]" := ([∗ list] ξ ∈ ξl, q:[ξ])%I
  (at level 2, left associativity, format "q :+[ ξl ]") : bi_scope.
Notation ".⟨ φπ ⟩" := (proph_obs φπ%type%stdpp)
  (at level 1, format ".⟨ φπ ⟩") : bi_scope.
Notation "⟨ π , φ ⟩" := (proph_obs (λ π, φ%type%stdpp))
  (at level 1, format "⟨ π ,  φ ⟩") : bi_scope.

(** * Iris Lemmas *)

Section proph.
Context `{!invGS Σ, !prophG Σ}.

(** Instances *)

Global Instance proph_ctx_persistent: Persistent proph_ctx := _.

Global Instance proph_tok_timeless q ξ : Timeless q:[ξ] := _.
Global Instance proph_tok_fractional ξ : Fractional (λ q, q:[ξ]%I).
Proof.
  move=> ??. by rewrite -own_op -auth_frag_op discrete_fun_singleton_op
    singleton_op -Cinl_op.
Qed.
Global Instance proph_tok_as_fractional q ξ : AsFractional q:[ξ] (λ q, q:[ξ]%I) q.
Proof. split; by [|apply _]. Qed.
Global Instance frame_proph_tok p ξ q1 q2 RES :
  FrameFractionalHyps p q1:[ξ] (λ q, q:[ξ])%I RES q1 q2 →
  Frame p q1:[ξ] q2:[ξ] RES | 5.
Proof. apply: frame_fractional. Qed.

Global Instance proph_toks_as_fractional q ξl : AsFractional q:+[ξl] (λ q, q:+[ξl]%I) q.
Proof. split; by [|apply _]. Qed.
Global Instance frame_proph_toks p ξl q1 q2 RES :
  FrameFractionalHyps p q1:+[ξl] (λ q, q:+[ξl])%I RES q1 q2 →
  Frame p q1:+[ξl] q2:+[ξl] RES | 5.
Proof. apply: frame_fractional. Qed.

Global Instance proph_obs_persistent φπ : Persistent .⟨φπ⟩ := _.
Global Instance proph_obs_timeless φπ : Timeless .⟨φπ⟩ := _.
Global Instance proph_obs_proper :
  Proper (pointwise_relation _ (↔) ==> (⊣⊢)) proph_obs.
Proof.
  move=> ?? Iff. rewrite /proph_obs. do 4 f_equiv. apply forall_proper=> ?.
  by rewrite Iff.
Qed.
Global Instance proph_obs_mono :
  Proper (pointwise_relation _ impl ==> (⊢)) proph_obs.
Proof.
  move=> ?? Imp. rewrite /proph_obs. do 4 f_equiv. move=> Imp' ??. by apply Imp, Imp'.
Qed.

(** Manipulating Tokens *)

Lemma proph_tok_singleton ξ q : q:[ξ] ⊣⊢ q:+[[ξ]].
Proof. by rewrite/= right_id. Qed.

Lemma proph_tok_combine ξl ζl q q' :
  q:+[ξl] -∗ q':+[ζl] -∗
    ∃q'', q'':+[ξl ++ ζl] ∗ (q'':+[ξl ++ ζl] -∗ q:+[ξl] ∗ q':+[ζl]).
Proof.
  case (Qp_lower_bound q q')=> [q''[?[?[->->]]]]. iIntros "[ξl ξl'][ζl ζl']".
  iExists q''. iFrame "ξl ζl". iIntros "[ξl ζl]".
  iSplitL "ξl ξl'"; iApply fractional_split; iFrame.
Qed.

(** Initialization *)

Lemma proph_init `{!prophPreG Σ} E :
  ↑prophN ⊆ E → ⊢ |={E}=> ∃_: prophG Σ, proph_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "●ε"; [by apply auth_auth_valid|].
  set IProphG := ProphG Σ _ γ. iExists IProphG.
  iMod (inv_alloc _ _ proph_inv with "[●ε]") as "?"; [|done]. iModIntro.
  iExists ε. iFrame "●ε". iPureIntro. exists []. split; [done|]=> ??.
  rewrite lookup_empty. split=> Hyp; inversion Hyp.
Qed.

(** Taking 𝔄i Fresh Prophecy Variable *)

Lemma proph_intro 𝔄i (I: gset positive) E :
  ↑prophN ⊆ E → proph_ctx ={E}=∗ ∃i, ⌜i ∉ I⌝ ∗ 1:[PrVar 𝔄i i].
Proof.
  iIntros (?) "?". iInv prophN as (S) ">[(%L &%& %Sim) ●S]".
  case (exist_fresh (I ∪ dom _ (S 𝔄i)))
    => [i /not_elem_of_union [? /not_elem_of_dom EqNone]].
  set ξ := PrVar 𝔄i i. set S' := add_line ξ (fitem 1) S.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ (fitem 1)) with "●S") as "[●S' ?]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitL "●S'"; last first. { by iModIntro; iExists i; iFrame. }
  iModIntro. iExists S'. iFrame "●S'". iPureIntro. exists L.
  split; [done|]. case=> [𝔅i j]?. rewrite /S' /add_line /discrete_fun_insert -Sim.
  case (decide (𝔄i = 𝔅i))=> [?|?]; [|done]. subst=>/=.
  case (decide (i = j))=> [<-|?]; [|by rewrite lookup_insert_ne].
  rewrite lookup_insert EqNone. split=> Eqv; [apply (inj Some) in Eqv|]; inversion Eqv.
Qed.

(** Prophecy Resolution *)

Local Lemma proph_tok_out S L ξ q :
  S :~ L → own proph_name (● S) -∗ q:[ξ] -∗ ⌜ξ ∉ res L⌝.
Proof.
  move=> Sim. iIntros "●S ξ".
  iDestruct (own_valid_2 with "●S ξ") as %ValBoth. iPureIntro.
  move=> /(elem_of_list_fmap_2 pli_pv) [[[𝔄i i]?][? /Sim Eqv]]. simpl in *.
  subst. move: ValBoth=> /auth_both_valid_discrete [Inc _].
  move/(discrete_fun_included_spec_1 _ _ 𝔄i) in Inc.
  rewrite /line discrete_fun_lookup_singleton /= in Inc.
  move: Eqv. move: Inc=> /singleton_included_l [?[-> Inc]]. move=> Eqv.
  apply (inj Some) in Eqv. move: Inc. rewrite Eqv.
  by move=> /Some_csum_included [|[[?[?[_[?]]]]|[?[?[?]]]]].
Qed.

Local Lemma proph_tok_ne ξ ζ q : 1:[ξ] -∗ q:[ζ] -∗ ⌜ξ ≠ ζ⌝.
Proof.
  iIntros "ξ ζ". iDestruct (own_valid_2 with "ξ ζ") as %ValBoth.
  iPureIntro=> ?. subst. move: ValBoth.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid -Cinl_op Cinl_valid.
  apply exclusive_l, _.
Qed.

Lemma proph_resolve E ξ vπ ζl q : ↑prophN ⊆ E → vπ ./{pv_level ξ} ζl →
  proph_ctx -∗ 1:[ξ] -∗ q:+[ζl] ={E}=∗ ⟨π, π ξ = vπ π⟩ ∗ q:+[ζl].
Proof.
  move: ξ vπ => [𝔄i i] vπ. set ξ := PrVar 𝔄i i.
  iIntros (? Dep) "? ξ ζl". iInv prophN as (S) ">[(%L & % & %Sim) ●S]".
  iDestruct (proph_tok_out with "●S ξ") as %Outξ; [done|].
  set L' := .{ξ := vπ} :: L. iAssert ⌜∀ζ, ζ ∈ ζl → ζ ∉ res L'⌝%I as %Outζl.
  { iIntros (? In). iDestruct (big_sepL_elem_of with "ζl") as "ζ"; [apply In|].
    iDestruct (proph_tok_ne with "ξ ζ") as %?.
    iDestruct (proph_tok_out with "●S ζ") as %?; [done|].
    by rewrite not_elem_of_cons. }
  set S' := add_line ξ (aitem vπ) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (aitem vπ)) with "●S ξ")
    as "[●S' #?]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "●S'"; last first.
  { iModIntro. iFrame "ζl". iExists [.{ξ := vπ}]. rewrite big_sepL_singleton.
    iSplitR; [|done]. iPureIntro=> ? Sat. by inversion Sat. }
  iModIntro. iExists S'. iFrame "●S'". iPureIntro. exists L'. split.
  { simpl.
  destruct (insert_sorted_correct .{ξ := vπ} (insertion_sort L log_item_le) log_item_le) as (L1&L2&?&->&sL2&sL1). apply insertion_sort_sorted; [exact _ ..].
  rewrite H1 in H0.
  assert (L ≡ₚ (L1 ++ L2)). rewrite -H1 -insertion_sort_perm. done.
  rewrite /res H2 in Outξ. rewrite /res /L' /not_elem_of_cons in Outζl. setoid_rewrite H2 in Outζl.
  clear H2 Sim H1.
  induction L1 as [|[ξ' vπ'] L1].  
  - rewrite (left_id []). rewrite left_id in H0. rewrite left_id in Outξ. rewrite left_id in Outζl. 
  split; [done|]. split; [|done].
  intros ?? In. apply Dep. intros ?[?[?|?]]; apply In.
  rewrite /res. intros [?|?]; [|lia]. revert H3. apply Outζl. done.
  rewrite /res fmap_cons. intros [?|?]; [|lia]. revert H3. apply not_elem_of_cons.
  split. intros ->. simpl in H2. lia. rewrite elem_of_list_fmap.
  intros ([??]&->&?). rewrite Forall_forall in sL2. specialize (sL2 _ H3).
  unfold log_item_le in sL2. simpl in sL2. simpl in H2. lia.
  - rewrite -app_comm_cons in H0. simpl. simpl in H0. destruct H0 as (?&?&?). 
  rewrite Forall_cons in sL1. destruct sL1 as [nle sL1].
  split.
  rewrite /res fmap_app fmap_cons not_elem_of_app not_elem_of_cons.
  rewrite /res fmap_app not_elem_of_app in H0. destruct H0.
  split. done. split; [|done]. intros ->. apply nle. unfold log_item_le. simpl. lia.
  split. intros ?? Dep'.
  apply H1. intros ? nin.
  destruct (decide (ξ0=ξ)) as [->|]; last first.
  apply Dep'. intros [?|?]; apply nin. left.
  rewrite /res fmap_app fmap_cons elem_of_cons elem_of_app elem_of_cons in H3.
  rewrite /res fmap_app elem_of_cons elem_of_app.
  destruct H3. left. done. right.
  destruct H3. left. done. right.
  destruct H3. done. done.
  right. done.
  exfalso. apply nin. right. unfold log_item_le in nle. simpl in nle. lia.
  apply IHL1. done. done.
  rewrite -app_comm_cons fmap_cons not_elem_of_cons in Outξ. by destruct Outξ.
  intros ? ζin. specialize (Outζl  _ ζin).
  rewrite -app_comm_cons perm_swap fmap_cons not_elem_of_cons in Outζl. by destruct Outζl.
 }
  have InLNe ζ wπ : .{ζ := wπ} ∈ L → ξ ≠ ζ.
  { move=> /(elem_of_list_fmap_1 pli_pv) ??. by subst. }
  move=> [𝔅i j] ?. rewrite elem_of_cons. case (decide (ξ = PrVar 𝔅i j))=> [Eq|Ne].
  { dependent destruction Eq.
    rewrite /S' /add_line discrete_fun_lookup_insert lookup_insert. split.
    - move=> /(inj (Some ∘ aitem)) ->. by left.
    - move=> [Eq'|/InLNe ?]; [|done]. by dependent destruction Eq'. }
  have Eqv : S' 𝔅i !! j ≡ S 𝔅i !! j.
  { rewrite /S' /add_line /discrete_fun_insert.
    case (decide (𝔄i = 𝔅i))=> [?|?]; [|done]. simpl_eq.
    case (decide (i = j))=> [?|?]; [|by rewrite lookup_insert_ne]. by subst. }
  rewrite Eqv Sim. split; [by right|]. case; [|done]=> Eq. by dependent destruction Eq.
Qed.

(** Manipulating Prophecy Observations *)

Implicit Type φπ ψπ: proph Prop.

Lemma proph_obs_true φπ : (∀π, φπ π) → ⊢ ⟨π, φπ π⟩.
Proof. move=> ?. iExists []. by iSplit. Qed.

Lemma proph_obs_impl φπ ψπ : (∀π, φπ π → ψπ π) → .⟨φπ⟩ -∗ .⟨ψπ⟩.
Proof. move=> Imp. do 2 f_equiv. move=> ?. by apply Imp. Qed.

Lemma proph_obs_eq φπ ψπ : (∀π, φπ π = ψπ π) → .⟨φπ⟩ -∗ .⟨ψπ⟩.
Proof. move=> Eq. apply proph_obs_impl=> ?. by rewrite Eq. Qed.

Lemma proph_obs_and φπ ψπ : .⟨φπ⟩ -∗ .⟨ψπ⟩ -∗ ⟨π, φπ π ∧ ψπ π⟩.
Proof.
  iIntros "(%L & %Toφπ & L) (%L' & %Toψπ & L')". iExists (L ++ L'). iFrame "L L'".
  iPureIntro=> ? /Forall_app[??]. split; by [apply Toφπ|apply Toψπ].
Qed.

Global Instance proph_obs_from_sep φπ ψπ : FromSep ⟨π, φπ π ∧ ψπ π⟩ .⟨φπ⟩ .⟨ψπ⟩.
Proof. rewrite /FromSep. iIntros "#[??]". by iApply proph_obs_and. Qed.

Lemma proph_obs_sat E φπ :
  ↑prophN ⊆ E → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ ⌜∃π₀, φπ π₀⌝.
Proof.
  iIntros "% ? (%L' & %Toφπ & #L')". iInv prophN as (S) ">[(%L & %Ok & %Sim) ●S]".
  move: (Ok)=> /proph_ok_sat [π /Forall_forall Sat]. iModIntro.
  iAssert ⌜π ◁ L'⌝%I as %?; last first.
  { iSplitL; last first. { iPureIntro. exists π. by apply Toφπ. }
    iModIntro. iExists S. iFrame "●S". iPureIntro. by exists L. }
  rewrite /proph_sat Forall_forall. iIntros ([[𝔄i i] vπ] In)=>/=.
  set ξ := PrVar 𝔄i i. iAssert (proph_atom .{ξ := vπ}) with "[L']" as "ξvπ".
  { iApply big_sepL_elem_of; by [apply In|]. }
  iDestruct (own_valid_2 with "●S ξvπ") as %ValBoth. iPureIntro.
  move: ValBoth=> /auth_both_valid_discrete [Inc Val]. apply (Sat .{ξ := vπ}), Sim.
  move/(discrete_fun_included_spec_1 _ _ 𝔄i) in Inc.
  rewrite /line discrete_fun_lookup_singleton in Inc.
  move: Inc=> /singleton_included_l [it [Eqv /Some_included [->|Inc]]]; [done|].
  rewrite Eqv. constructor. apply (lookup_valid_Some _ i it) in Val; [|done]. move: Val.
  move: Inc=> /csum_included [->|[[?[?[?]]]|[?[?[Eq[-> Inc]]]]]]; [done|done|].
  move=> Val. move: Inc. move: Val=> /Cinr_valid/to_agree_uninj [?<-].
  inversion Eq. by move/to_agree_included <-.
Qed.

Lemma proph_obs_false E φπ :
  ↑prophN ⊆ E → (∀π, ¬ φπ π) → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ False.
Proof.
  iIntros (? Neg) "PROPH Obs".
  iMod (proph_obs_sat with "PROPH Obs") as %[? Ex]; [done|]. by apply Neg in Ex.
Qed.

End proph.

Global Opaque proph_ctx proph_tok proph_obs.

(** * Prophecy Equalizer *)

Definition proph_eqz `{!invGS Σ, !prophG Σ} {A} (uπ vπ: proph A) P : iProp Σ :=
  ∀E ξl q, ⌜↑prophN ⊆ E ∧ P vπ ξl⌝ -∗ q:+[ξl] ={E}=∗ ⟨π, uπ π = vπ π⟩ ∗ q:+[ξl].

Notation "uπ :={ P }= vπ" := (proph_eqz uπ vπ P) (at level 70, format "uπ  :={ P }=  vπ") : bi_scope.

Section proph_eqz.
Context `{!invGS Σ, !prophG Σ}.

(** ** Constructing Prophecy Equalizers *)

Lemma proph_eqz_token ξ vπ : proph_ctx -∗ 1:[ξ] -∗ (.$ ξ) :={λ vπ ξl, vπ ./[pv_sty ξ] ξl}= vπ.
Proof.
  iIntros "PROPH ξ" (???[??]) "ξl". by iMod (proph_resolve with "PROPH ξ ξl").
Qed.

Lemma proph_eqz_obs {A} (uπ vπ: proph A) P : ⟨π, uπ π = vπ π⟩ -∗ uπ :={P}= vπ.
Proof. iIntros "?" (???[??]) "? !>". iFrame. Qed.

Lemma proph_eqz_refl {A} (vπ: proph A) P : ⊢ vπ :={P}= vπ.
Proof. iApply proph_eqz_obs. by iApply proph_obs_true. Qed.

Lemma proph_eqz_modify {A} (uπ uπ' vπ: proph A) P:
  ⟨π, uπ' π = uπ π⟩ -∗ uπ :={P}= vπ -∗ uπ' :={P}= vπ.
Proof.
  iIntros "Obs Eqz" (???[??]) "ξl". iMod ("Eqz" with "[%//] ξl") as "[Obs' $]".
  iModIntro. iCombine "Obs Obs'" as "?". by iApply proph_obs_impl; [|done]=> ?[->].
Qed.

Lemma proph_eqz_constr {A B} (f: A → B) `{!@Inj A B (=) (=) f} uπ vπ P:
  uπ :={P}= vπ -∗ f ∘ uπ :={λ vπ ξl, exists vπ0, vπ = f ∘ vπ0 /\ P vπ0 ξl}= f ∘ vπ.
Proof.
  iIntros "Eqz" (???[? (vπ0&?&?)]) "ξl". 
  replace vπ0 with vπ in H2.
  iMod ("Eqz" with "[%//] ξl") as "[Obs $]". iModIntro.
  iApply proph_obs_impl; [|by iApply "Obs"]=> ??/=. by f_equal.
  fun_ext; intros; specialize ((equal_f H1) x) => /= eq; specialize (inj _ _ _ eq); done.
Qed.

Lemma proph_eqz_constr2 {A B C} f `{!@Inj2 A B C (=) (=) (=) f} uπ uπ' vπ vπ' P Q:
  uπ :={P}= vπ -∗ uπ' :={Q}= vπ' -∗ f ∘ uπ ⊛ uπ' :={λ vπ ξl, exists vπ0 ξl0 vπ1 ξl1, ξl = ξl0 ++ ξl1 /\ vπ = f ∘ vπ0 ⊛ vπ1 /\ P vπ0 ξl0 /\ Q vπ1 ξl1}= f ∘ vπ ⊛ vπ'.
Proof.
  iIntros "Eqz Eqz'" (???[? (vπ0&ξl0&vπ1&ξl1&->&?&?&?)]) "[ξl0 ξl1]".
  replace vπ0 with vπ in H2. replace vπ1 with vπ' in H3.
  iMod ("Eqz" with "[%//] ξl0") as "[Obs ξl0]".
  iMod ("Eqz'" with "[%//] ξl1") as "[Obs' ξl1]". iModIntro. iFrame.
  iCombine "Obs Obs'" as "?". by iApply proph_obs_impl; [|done] =>/= ?[->->].
  fun_ext; intros; specialize ((equal_f H1) x) => /= eq; destruct (inj2 _ _ _ _ _ eq) as [??]; done.
  fun_ext; intros; specialize ((equal_f H1) x) => /= eq; destruct (inj2 _ _ _ _ _ eq) as [??]; done.
Qed.

Lemma proph_eqz_constr3 {A B C D} f `{!@Inj3 A B C D (=) (=) (=) (=) f} P0 P1 P2
    uπ₀ uπ₁ uπ₂ vπ₀ vπ₁ vπ₂ :
  uπ₀ :={P0}= vπ₀ -∗ uπ₁ :={P1}= vπ₁ -∗ uπ₂ :={P2}= vπ₂ -∗
  f ∘ uπ₀ ⊛ uπ₁ ⊛ uπ₂ :={λ vπ ξl, exists vπ0 ξl0 vπ1 ξl1 vπ2 ξl2, ξl = ξl0 ++ ξl1 ++ ξl2 /\ vπ = f ∘ vπ0 ⊛ vπ1 ⊛ vπ2 /\ P0 vπ0 ξl0 /\ P1 vπ1 ξl1 /\ P2 vπ2 ξl2}= f ∘ vπ₀ ⊛ vπ₁ ⊛ vπ₂.
Proof.
  iIntros "Eqz0 Eqz1 Eqz2" (???[? (vπ0&ξl0&vπ1&ξl1&vπ2&ξl2&->&?&?&?&?)]) "(ξl0&ξl1&ξl2)".
  replace vπ₀ with vπ0. replace vπ₁ with vπ1. replace vπ₂ with vπ2.
  iMod ("Eqz0" with "[%//] ξl0") as "[Obs0 ξl0]".
  iMod ("Eqz1" with "[%//] ξl1") as "[Obs1 ξl1]".
  iMod ("Eqz2" with "[%//] ξl2") as "[Obs2 ξl2]". iModIntro. iFrame.
  iCombine "Obs0 Obs1 Obs2" as "?". by iApply proph_obs_impl; [|done] =>/= ? [->[->->]].
  fun_ext; intros; specialize ((equal_f H1) x) => /= eq; destruct (inj3 _ _ _ _ _ _ _ eq) as [?[??]]; done.
  fun_ext; intros; specialize ((equal_f H1) x) => /= eq; destruct (inj3 _ _ _ _ _ _ _ eq) as [?[??]]; done.
  fun_ext; intros; specialize ((equal_f H1) x) => /= eq; destruct (inj3 _ _ _ _ _ _ _ eq) as [?[??]]; done.
Qed.

Lemma proph_eqz_eq {A} (uπ uπ' vπ vπ': proph A) ξl P :
  uπ = uπ' → vπ = vπ' → uπ :={P}= vπ -∗ uπ' :={P}= vπ'.
Proof. iIntros (->->) "$". Qed.

Lemma proph_eqz_mono {A} (P P': _ → _ → Prop) (uπ vπ: proph A):
  (∀ ξl, P' vπ ξl → P vπ ξl) → uπ :={P}= vπ -∗ uπ :={P'}= vπ.
Proof.
  iIntros "%H Eqz" (???[??]). iApply "Eqz". iPureIntro.
  split. done. by apply H. 
Qed.

Lemma proph_eqz_prod {A B} (uπ vπ: proph (A * B)) P Q:
 fst ∘ uπ :={P}= fst ∘ vπ -∗ snd ∘ uπ :={Q}= snd ∘ vπ -∗ uπ :={λ vπ ξl, exists ξl0 ξl1, ξl = ξl0 ++ ξl1 /\ P (fst∘vπ) ξl0 /\ Q (snd∘vπ) ξl1}= vπ.
Proof.
  iIntros "Eqz Eqz'". iDestruct (proph_eqz_constr2 with "Eqz Eqz'") as "?".
  rewrite -!surjective_pairing_fun. iApply proph_eqz_mono; [|done].
  simpl. intros ?(?&?&->&?&?). eexists (fst ∘ vπ), _, (snd ∘ vπ), _. rewrite -surjective_pairing_fun. done.
Qed.


Lemma proph_eqz_vinsert {A n} xπ yπ (zπl: vec (proph A) n) i P :
  xπ :={P}= yπ -∗ vapply (vinsert i xπ zπl) :={λ vπ ξl, exists ξl0 ξl1 ξl2, ξl = ξl0 ++ ξl1 ++ ξl2 /\ P (λ π, (vπ π) !!! i) ξl1}= vapply (vinsert i yπ zπl).
Proof.
  iIntros "Eqz". rewrite !vapply_insert_backmid.
  iApply proph_eqz_mono; last first.
  iApply ((proph_eqz_constr3 _ (const (const True)) _ (const (const True))) with "[] Eqz []"); iApply proph_eqz_refl.
  intros ?(?&?&?&->&?). eexists _, _, _, _, _, _. 
  do 3 (split; [done|]). split; [|done]. revert H. eassert (impl _ _); [|done]. f_equiv.
  rewrite -vapply_insert_backmid. fun_ext. intros.
  rewrite /vapply vmap_insert vlookup_insert. done.
Qed.
End proph_eqz.
