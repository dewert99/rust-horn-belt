Import EqNotations.
Require Import ProofIrrelevance Equality FunctionalExtensionality.
From stdpp Require Import strings.
From iris.algebra Require Import auth cmra functions gmap csum frac agree.
From iris.bi Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lrust.util Require Import basic discrete_fun functional_choice.

Ltac proof_subst x y :=
  (have ?: x = y by apply proof_irrelevance); subst x.

Section basic.
Context `{EqDecision TYPE} {Ty: TYPE → Type}.
Coercion Ty: TYPE >-> Sortclass.
Implicit Type a b: TYPE.

(** * Basic Notions *)

Definition proph_var_body a : Type := positive * inhabited a.
Record proph_var := PrVar { pv_ty: TYPE; pv_bd: proph_var_body pv_ty }.
Add Printing Constructor proph_var.

Global Instance proph_var_eq_dec: EqDecision proph_var.
Proof.
  move=> [a[i inh]][b[j inh']]. case (decide (a = b))=> [?|?];
  [|by apply right=> [=]]. subst. case (decide (i = j))=> [?|?].
  - subst. apply left. by proof_subst inh inh'.
  - apply right=> Eq. by dependent destruction Eq.
Qed.

Definition proph_asn := ∀ξ, ξ.(pv_ty).
Definition proph A := proph_asn → A.

Implicit Type (ξ ζ: proph_var) (ξs ζs: list proph_var) (π: proph_asn).

Lemma proph_asn_inhabited: inhabited proph_asn.
Proof. apply inhabited_forall_commute. by move=> [?[??]]. Qed.

(** * Prophecy Dependency *)

Local Definition proph_asn_eqv ξs π π' := ∀ξ, ξ ∈ ξs → π ξ = π' ξ.
Local Notation "π .≡{ ξs }≡ π'" := (proph_asn_eqv ξs π π')
  (at level 70, format "π  .≡{ ξs }≡  π'").

Definition proph_dep {A} (vπ: _ → A) ξs := ∀π π', π .≡{ξs}≡ π' → vπ π = vπ π'.
Local Notation "vπ ./ ξs" := (proph_dep vπ ξs) (at level 70, format "vπ  ./  ξs").

(** ** Lemmas *)

Lemma proph_dep_one ξ : (.$ ξ) ./ [ξ].
Proof. move=> ?? Eqv. apply Eqv. constructor. Qed.

Lemma proph_dep_constr {A B} (f: A → B) vπ ξs : vπ ./ ξs → f ∘ vπ ./ ξs.
Proof. move=> Dep ?? /Dep ?. by apply (f_equal f). Qed.

Local Lemma proph_dep_mono {A} ξs ζs (vπ: _ → A) :
  ξs ⊆ ζs → vπ ./ ξs → vπ ./ ζs.
Proof. move=> In Dep ?? Eqv. apply Dep => ??. by apply Eqv, In. Qed.

Local Lemma subseteq_app_l ξs ζs : ξs ⊆ ξs ++ ζs.
Proof. move=> ??. rewrite elem_of_app. by left. Qed.

Local Lemma subseteq_app_r ξs ζs : ζs ⊆ ξs ++ ζs.
Proof. move=> ??. rewrite elem_of_app. by right. Qed.

Lemma proph_dep_constr2 {A B C} (f: A → B → C) vπ wπ ξs ζs :
  vπ ./ ξs → wπ ./ ζs → f ∘ vπ ⊛ wπ ./ ξs ++ ζs.
Proof.
  move=> Dep Dep' ?? Eqv. eapply proph_dep_mono in Dep, Dep';
    [|apply subseteq_app_r|apply subseteq_app_l].
  move: (Eqv) (Eqv) => /Dep ? /Dep' ?. by apply (f_equal2 f).
Qed.

Lemma proph_dep_destr {A B} f `{Inj A B (=) (=) f} vπ ξs :
  f ∘ vπ ./ ξs → vπ ./ ξs.
Proof. by move=> Dep ?? /Dep/(inj f) ?. Qed.

Lemma proph_dep_destr2 {A B C} f `{Inj2 A B C (=) (=) (=) f} vπ wπ ξs :
  f ∘ vπ ⊛ wπ ./ ξs → vπ ./ ξs ∧ wπ ./ ξs.
Proof.
  move=> Dep. split; move=> ?? /Dep Eq; apply (inj2 f) in Eq; by inversion Eq.
Qed.

Lemma proph_dep_unique `{Unique A} (vπ: _ → A) : vπ ./ [].
Proof. by rewrite (eq_unique vπ). Qed.

Lemma proph_dep_pair {A B} (vπ: _ → A * B) ξs ζs :
  fst ∘ vπ ./ ξs → snd ∘ vπ ./ ζs → vπ ./ ξs ++ ζs.
Proof.
  move=> ??. rewrite (surjective_pairing_fun vπ). by apply proph_dep_constr2.
Qed.

(** * Prophecy Log *)

Record proph_log_item :=
  ProphLogItem { pli_pv: proph_var; pli_val: proph pli_pv.(pv_ty) }.
Local Notation ".{ ξ := vπ }" := (ProphLogItem ξ vπ)
  (at level 1, format ".{ ξ  :=  vπ }").

Local Definition proph_log := list proph_log_item.

Implicit Type L: proph_log.

Local Definition res L := pli_pv <$> L.

Local Definition proph_asn_eqv_out ξs π π' := ∀ξ, ξ ∉ ξs → π ξ = π' ξ.
Local Notation "π .≡~{ ξs }≡ π'" := (proph_asn_eqv_out ξs π π')
  (at level 70, format "π  .≡~{ ξs }≡  π'").
Local Definition proph_dep_out {A} (vπ: _ → A) ξs :=
  ∀ π π', π .≡~{ ξs }≡ π' → vπ π = vπ π'.
Local Notation "vπ ./~ ξs" := (proph_dep_out vπ ξs)
  (at level 70, format "vπ  ./~  ξs").

Local Fixpoint proph_log_ok L := match L with [] => True |
  .{ξ := vπ} :: L' => ξ ∉ res L' ∧ vπ ./~ res L ∧ proph_log_ok L' end.
Local Notation ".✓ L" := (proph_log_ok L) (at level 20, format ".✓  L").

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

Local Fixpoint proph_modify π L := match L with
  [] => π | .{ξ := vπ} :: L' => proph_modify (:<[ξ := vπ]> π) L' end.
Local Notation "π ! L" := (proph_modify π L) (at level 30, format "π  !  L").

Local Lemma proph_modify_eqv L : ∀π, π ! L .≡~{res L}≡ π.
Proof.
  elim L=>/= [|[??]? IH]; [done|]=> > /not_elem_of_cons [??].
  rewrite IH; [|done]. by apply proph_upd_lookup_ne.
Qed.

Local Lemma proph_ok_modify_sat L : .✓ L → ∀π, π ! L ◁ L.
Proof.
  rewrite /proph_sat. elim: L=>/= [|[ξ vπ] L' IH]; [done|]. move=> [?[? /IH ?]]?.
  apply Forall_cons=>/=. split; [|done]. rewrite proph_modify_eqv; [|done].
  rewrite proph_upd_lookup. set L := .{ξ := vπ} :: L'.
  have Dep': vπ ./~ res L by done. symmetry. apply Dep', (proph_modify_eqv L).
Qed.

Local Lemma proph_ok_sat L : .✓ L → ∃π, π ◁ L.
Proof.
  move: proph_asn_inhabited=> [π]?. exists (π ! L). by apply proph_ok_modify_sat.
Qed.

(** * Prophecy Camera *)

Local Definition proph_itemR a := csumR fracR (agreeR (leibnizO (proph a))).
Local Definition proph_gmapUR a := gmapUR positive (proph_itemR a).
Local Definition proph_smryUR := discrete_funUR proph_gmapUR.
Definition prophUR := authUR proph_smryUR.

Implicit Type (S: proph_smryUR) (q: Qp).

Local Definition aitem {a} vπ : proph_itemR a := Cinr (to_agree vπ).
Local Definition fitem {a} q : proph_itemR a := Cinl q.
Local Definition line ξ it : proph_smryUR := .{[ξ.(pv_ty) := {[ξ.(pv_bd).1 := it]}]}.
Local Definition add_line ξ it S : proph_smryUR :=
  .<[ξ.(pv_ty) := <[ξ.(pv_bd).1 := it]> (S ξ.(pv_ty))]> S.

Definition prophΣ := #[GFunctor prophUR].
Class prophPreG Σ := ProphPreG { proph_preG_inG:> inG Σ prophUR }.
Class prophG Σ := ProphG { proph_inG:> prophPreG Σ; proph_name: gname }.
Instance subG_prophPreG {Σ} : subG prophΣ Σ → prophPreG Σ.
Proof. solve_inG. Qed.

Definition prophN := nroot .@ "proph".

(** * Iris Propositions *)

Local Definition proph_sim S L :=
  ∀ξ vπ, S ξ.(pv_ty) !! ξ.(pv_bd).1 ≡ Some (aitem vπ) ↔ .{ξ := vπ} ∈ L.
Local Notation "S :~ L" := (proph_sim S L) (at level 70, format "S  :~  L").

Section defs.
Context `{!invG Σ, !prophG Σ}.

(** Prophecy Context *)
Local Definition proph_inv: iProp Σ :=
  ∃ S, ⌜∃L, .✓ L ∧ S :~ L⌝ ∗ own proph_name (● S).
Definition proph_ctx: iProp Σ := inv prophN proph_inv.

(** Prophecy Token *)
Definition proph_tok ξ q : iProp Σ := own proph_name(◯ line ξ (fitem q)).

(** Prophecy Observation *)
Local Definition proph_atom pli : iProp Σ :=
  own proph_name (◯ line pli.(pli_pv) (aitem pli.(pli_val))).
Definition proph_obs (φπ: proph Prop) : iProp Σ :=
  ∃L, ⌜∀π, π ◁ L → φπ π⌝ ∗ [∗ list] pli ∈ L, proph_atom pli.

End defs.
End basic.

Arguments prophG: clear implicits.
Arguments prophPreG: clear implicits.

Notation "q :[ ξ ]" := (proph_tok ξ q)
  (at level 2, left associativity, format "q :[ ξ ]") : bi_scope.
Notation "q :+[ ξs ]" := ([∗ list] ξ ∈ ξs, q:[ξ])%I
  (at level 2, left associativity, format "q :+[ ξs ]") : bi_scope.
Notation ".⟨ φπ ⟩" := (proph_obs φπ%type%stdpp)
  (at level 1, format ".⟨ φπ ⟩") : bi_scope.
Notation "⟨ π , φ ⟩" := (proph_obs (λ π, φ%type%stdpp))
  (at level 1, format "⟨ π ,  φ ⟩") : bi_scope.

Notation "vπ ./ ξs" := (proph_dep vπ ξs) (at level 70, format "vπ  ./  ξs").

Add Printing Constructor proph_var.
Local Notation ".{ ξ := vπ }" := (ProphLogItem ξ vπ)
  (at level 1, format ".{ ξ  :=  vπ }").
Local Notation "π ◁ L" := (proph_sat π L) (at level 70, format "π  ◁  L").
Local Notation "S :~ L" := (proph_sim S L) (at level 70, format "S  :~  L").

(** * Iris Lemmas *)

Section lemmas.
Context `{!invG Σ, !prophG TYPE Ty Σ, !EqDecision TYPE}.
Coercion Ty: TYPE >-> Sortclass.
Implicit Type a b: TYPE.

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

Global Instance proph_toks_as_fractional q ξs : AsFractional q:+[ξs] (λ q, q:+[ξs]%I) q.
Proof. split; by [|apply _]. Qed.

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
Proof. by rewrite /= right_id. Qed.

Lemma proph_tok_combine ξs ζs q q' :
  q:+[ξs] -∗ q':+[ζs] -∗
    ∃q'', q'':+[ξs ++ ζs] ∗ (q'':+[ξs ++ ζs] -∗ q:+[ξs] ∗ q':+[ζs]).
Proof.
  case (Qp_lower_bound q q')=> [q''[?[?[->->]]]]. iIntros "[??][??]".
  iExists q''. iFrame. iIntros "[$$]".
Qed.

(** Initialization *)

Lemma proph_init `{!prophPreG TYPE Ty Σ} E :
  ↑prophN ⊆ E → ⊢ |={E}=> ∃ _: prophG TYPE Ty Σ, proph_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "Own"; [by apply auth_auth_valid|].
  set IProphG := ProphG Σ _ γ. iExists IProphG.
  iMod (inv_alloc _ _ proph_inv with "[Own]") as "?"; [|done]. iModIntro.
  iExists ε. iFrame. iPureIntro. exists []. split; [done|]=> ??.
  rewrite lookup_empty. split=> Hyp; inversion Hyp.
Qed.

(** Taking a Fresh Prophecy Variable *)

Lemma proph_intro a (I: gset positive) E (inh: inhabited a) :
  ↑prophN ⊆ E → proph_ctx ={E}=∗ ∃i, ⌜i ∉ I⌝ ∗ 1:[PrVar a (i, inh)].
Proof.
  iIntros (?) "?". iInv prophN as (S) "> [(%L & %Ok & %Sim) Auth]".
  case (exist_fresh (I ∪ dom _ (S a)))
    => [i /not_elem_of_union [? /not_elem_of_dom EqNone]].
  set ξ := PrVar a (i, inh). set S' := add_line ξ (fitem 1) S.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ (fitem 1)) with "Auth") as "[Auth ?]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitL "Auth"; last first. { iModIntro. iExists i. by iFrame. }
  iModIntro. iExists S'. iFrame. iPureIntro. exists L.
  split; [done|]. case=> [b[j ?]]?. rewrite /S' /add_line /discrete_fun_insert -Sim.
  case (decide (a = b))=> [?|?]; [|done]. subst=>/=.
  case (decide (i = j))=> [<-|?]; [|by rewrite lookup_insert_ne].
  rewrite lookup_insert EqNone. split=> Eqv; [apply (inj Some) in Eqv|]; inversion Eqv.
Qed.

(** Prophecy Resolution *)

Local Lemma proph_tok_out S L ξ q :
  S :~ L → own proph_name (● S) -∗ q:[ξ] -∗ ⌜ξ ∉ res L⌝.
Proof.
  move=> Sim. iIntros "Auth Tok".
  iDestruct (own_valid_2 with "Auth Tok") as %ValBoth. iPureIntro.
  move=> /(elem_of_list_fmap_2 pli_pv) [[[a[i ?]]?][? /Sim Eqv]]. simpl in *.
  subst. move: ValBoth=> /auth_both_valid_discrete [Inc _].
  move/(discrete_fun_included_spec_1 _ _ a) in Inc.
  rewrite /line discrete_fun_lookup_singleton /= in Inc.
  move: Eqv. move: Inc=> /singleton_included_l [?[-> Inc]]. move=> Eqv.
  apply (inj Some) in Eqv. move: Inc. rewrite Eqv.
  by move=> /Some_csum_included [|[[?[?[_[?]]]]|[?[?[?]]]]].
Qed.

Local Lemma proph_tok_ne ξ ζ q : 1:[ξ] -∗ q:[ζ] -∗ ⌜ξ ≠ ζ⌝.
Proof.
  iIntros "Tok Ptok". iDestruct (own_valid_2 with "Tok Ptok") as %ValBoth.
  iPureIntro=> ?. subst. move: ValBoth.
  rewrite -auth_frag_op auth_frag_valid discrete_fun_singleton_op
    discrete_fun_singleton_valid singleton_op singleton_valid -Cinl_op
    Cinl_valid. apply exclusive_l, _.
Qed.

Lemma proph_resolve E ξ vπ ζs q : ↑prophN ⊆ E → vπ ./ ζs →
  proph_ctx -∗ 1:[ξ] -∗ q:+[ζs] ={E}=∗ ⟨π, π ξ = vπ π⟩ ∗ q:+[ζs].
Proof.
  move: ξ vπ => [a[i inh]] vπ. set ξ := PrVar a (i, inh).
  iIntros (? Dep) "? Tok Ptoks". iInv prophN as (S) "> [(%L & %Ok & %Sim) Auth]".
  iDestruct (proph_tok_out with "Auth Tok") as %Outξ; [done|].
  set L' := .{ξ := vπ} :: L. iAssert ⌜∀ζ, ζ ∈ ζs → ζ ∉ res L'⌝%I as %Outζs.
  { iIntros (? In).
    iDestruct (big_sepL_elem_of with "Ptoks") as "Ptok"; [apply In|].
    iDestruct (proph_tok_ne with "Tok Ptok") as %?.
    iDestruct (proph_tok_out with "Auth Ptok") as %?; [done|].
    by rewrite not_elem_of_cons. }
  set S' := add_line ξ (aitem vπ) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (aitem vπ)) with "Auth Tok")
    as "[Auth #?]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "Auth"; last first.
  { iModIntro. iFrame. iExists [.{ξ := vπ}]. rewrite big_sepL_singleton.
    iSplitR; [|done]. iPureIntro=> ? Sat. by inversion Sat. }
  iModIntro. iExists S'. iFrame. iPureIntro. exists L'. split.
  { split; [done| split; [|done]] => ?? Eqv. apply Dep => ? /Outζs ?.
    by apply Eqv. }
  have InLNe ζ wπ : .{ζ := wπ} ∈ L → ξ ≠ ζ.
  { move=> /(elem_of_list_fmap_1 pli_pv) ??. by subst. }
  move=> [b[j inh']] ?. rewrite elem_of_cons.
  case (decide (ξ = PrVar b (j, inh')))=> [Eq|Ne].
  { move: (Eq)=> ?. dependent destruction Eq.
    rewrite /S' /add_line discrete_fun_lookup_insert lookup_insert. split.
    - move=> /(inj (Some ∘ aitem)) ->. left. by proof_subst inh' inh.
    - move=> [Eq'|/InLNe ?]; [|done]. proof_subst inh' inh.
      by dependent destruction Eq'. }
  have Eqv : S' b !! j ≡ S b !! j.
  { rewrite /S' /add_line /discrete_fun_insert.
    case (decide (a = b))=> [?|?]; [|done]. simpl_eq.
    case (decide (i = j))=> [?|?]; [|by rewrite lookup_insert_ne]. subst.
    by proof_subst inh' inh. }
  rewrite Eqv Sim. split; [by right|]. move=> [Eq|?]; [|done].
  dependent destruction Eq. by proof_subst inh' inh.
Qed.

(** Manipulating Prophecy Observations *)

Implicit Type φπ ψπ: @proph TYPE Ty Prop.

Lemma proph_obs_true φπ : (∀π, φπ π) → ⊢ ⟨π, φπ π⟩.
Proof. move=> ?. iExists []. by iSplit. Qed.

Lemma proph_obs_impl φπ ψπ : (∀π, φπ π → ψπ π) → .⟨φπ⟩ -∗ .⟨ψπ⟩.
Proof. move=> Imp. do 2 f_equiv. move=> ?. by apply Imp. Qed.

Lemma proph_obs_eq φπ ψπ : (∀π, φπ π = ψπ π) → .⟨φπ⟩ -∗ .⟨ψπ⟩.
Proof. move=> Eq. apply proph_obs_impl=> ?. by rewrite Eq. Qed.

Lemma proph_obs_and φπ ψπ : .⟨φπ⟩ -∗ .⟨ψπ⟩ -∗ ⟨π, φπ π ∧ ψπ π⟩.
Proof.
  iIntros "(%L & %SatTo &?) (%L' & %SatTo' &?)". iExists (L ++ L'). iFrame.
  iPureIntro=> ? /Forall_app [??]. split; by [apply SatTo|apply SatTo'].
Qed.

Lemma proph_obs_sat E φπ :
  ↑prophN ⊆ E → proph_ctx -∗ .⟨φπ⟩ ={E}=∗ ⌜∃π₀, φπ π₀⌝.
Proof.
  iIntros "% ? (%L' & %SatTo & #Atoms)". iInv prophN as (S) ">[(%L & %Ok & %Sim) Auth]".
  move: (Ok)=> /proph_ok_sat [π /Forall_forall Sat]. iModIntro.
  iAssert ⌜π ◁ L'⌝%I as %?; last first.
  { iSplitL; last first. { iPureIntro. exists π. by apply SatTo. }
    iModIntro. iExists S. iFrame. iPureIntro. by exists L. }
  rewrite /proph_sat Forall_forall. iIntros ([[a[i inh]] vπ] In)=>/=.
  set ξ := PrVar a (i, inh). iAssert (proph_atom .{ξ := vπ}) with "[Atoms]" as "Atom".
  { iApply big_sepL_elem_of; by [apply In|]. }
  iDestruct (own_valid_2 with "Auth Atom") as %ValBoth. iPureIntro.
  move: ValBoth=> /auth_both_valid_discrete [Inc Val]. apply (Sat .{ξ := vπ}), Sim.
  move/(discrete_fun_included_spec_1 _ _ a) in Inc.
  rewrite /line discrete_fun_lookup_singleton in Inc.
  move: Inc=> /singleton_included_l [it [Eqv /Some_included [->|Inc]]]; [done|].
  rewrite Eqv. constructor. apply (lookup_valid_Some _ i it) in Val; [|done]. move: Val.
  move: Inc=> /csum_included [->|[[?[?[?]]]|[?[?[Eq[-> Inc]]]]]]; [done|done|].
  move=> Val. move: Inc. move: Val=> /Cinr_valid/to_agree_uninj [?<-].
  inversion Eq. by move/to_agree_included <-.
Qed.

End lemmas.

Global Opaque proph_ctx proph_tok proph_obs.

(** * Prophecy Equalizer *)

Section def.
Context `{!invG Σ, !prophG TYPE Ty Σ, !EqDecision TYPE}.

Definition proph_eqz {A} (uπ vπ: _ → A) : iProp Σ :=
  ∀E ξs q, ⌜↑prophN ⊆ E ∧ vπ ./ ξs⌝ -∗ q:+[ξs] ={E}=∗ ⟨π, uπ π = vπ π⟩ ∗ q:+[ξs].

End def.

Notation "uπ :== vπ" := (proph_eqz uπ vπ) (at level 70, format "uπ  :==  vπ") : bi_scope.

Section lemmas.
Context `{!invG Σ, !prophG TYPE Ty Σ, !EqDecision TYPE}.

(** ** Constructing Prophecy Equalizers *)

Lemma proph_eqz_token ξ vπ : proph_ctx -∗ 1:[ξ] -∗ (.$ ξ) :== vπ.
Proof.
  iIntros "PROPH Tok" (???[??]) "Ptoks". by iMod (proph_resolve with "PROPH Tok Ptoks").
Qed.

Lemma proph_eqz_obs {A} (uπ vπ: _ → A) : ⟨π, uπ π = vπ π⟩ -∗ uπ :== vπ.
Proof. iIntros "?" (???[??]) "? !>". iFrame. Qed.

Lemma proph_eqz_eq {A} (vπ: _ → A) : ⊢ vπ :== vπ.
Proof. iApply proph_eqz_obs. by iApply proph_obs_true. Qed.

Lemma proph_eqz_modify {A} (uπ uπ' vπ: _ → A) :
  ⟨π, uπ' π = uπ π⟩ -∗ uπ :== vπ -∗ uπ' :== vπ.
Proof.
  iIntros "Obs Eqz" (???[??]) "Ptoks".
  iMod ("Eqz" with "[%//] Ptoks") as "[Obs' $]". iModIntro.
  iDestruct (proph_obs_and with "Obs Obs'") as "Obs''".
  by iApply proph_obs_impl; [|by iApply "Obs''"]=> ?[->?].
Qed.

Lemma proph_eqz_constr {A B} f `{Inj A B (=) (=) f} uπ vπ :
  uπ :== vπ -∗ f ∘ uπ :== f ∘ vπ.
Proof.
  iIntros "Eqz" (???[? Dep]) "Ptoks". move/proph_dep_destr in Dep.
  iMod ("Eqz" with "[%//] Ptoks") as "[Obs $]". iModIntro.
  iApply proph_obs_impl; [|by iApply "Obs"]=> ??/=. by f_equal.
Qed.

Lemma proph_eqz_constr2 {A B C} f `{Inj2 A B C (=) (=) (=) f} uπ uπ' vπ vπ' :
  uπ :== vπ -∗ uπ' :== vπ' -∗ f ∘ uπ ⊛ uπ' :== f ∘ vπ ⊛ vπ'.
Proof.
  iIntros "Eqz Eqz'" (???[? Dep]) "Ptoks". move: Dep=> /proph_dep_destr2 [??].
  iMod ("Eqz" with "[%//] Ptoks") as "[Obs Ptoks]".
  iMod ("Eqz'" with "[%//] Ptoks") as "[Obs' $]". iModIntro.
  iDestruct (proph_obs_and with "Obs Obs'") as "Obs''".
  iApply proph_obs_impl; [|by iApply "Obs''"]=> ?[??]/=. by f_equal.
Qed.

Lemma proph_eqz_pair {A B} (uπ vπ: _ → A * B) :
  fst ∘ uπ :== fst ∘ vπ -∗ snd ∘ uπ :== snd ∘ vπ -∗ uπ :== vπ.
Proof.
  iIntros "Eqz Eqz'". iDestruct (proph_eqz_constr2 with "Eqz Eqz'") as "?".
  by rewrite -!surjective_pairing_fun.
Qed.

End lemmas.
