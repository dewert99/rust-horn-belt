Import EqNotations.
Require Import ClassicalDescription Equality.
From stdpp Require Import strings.
From iris.algebra Require Import auth cmra functions gmap csum frac agree.
From iris.bi Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lrust.prophecy Require Import functions.

(** * Pointed Type *)

Record ptType: Type := PtType { pt_ty: Type; pt_val: pt_ty }.
Coercion pt_ty: ptType >-> Sortclass.

Implicit Type Ap Bp: ptType.

(** We use classical axioms only here. *)
Global Instance pt_type_eq_dec : EqDecision ptType :=
  { decide_rel _ _ := excluded_middle_informative _ }.

(** * Basic Notions *)

Record proph_var := ProphVar { pv_ty: ptType; pv_id: positive }.
Notation "$( Ap , i )" := (ProphVar Ap i) (at level 2, format "$( Ap ,  i )").
Notation "ξ .ty" := (ξ.(pv_ty)) (at level 2, format "ξ .ty").
Notation "ξ .id" := (ξ.(pv_id)) (at level 2, format "ξ .id").

Global Instance proph_var_eq_dec : EqDecision proph_var.
Proof. solve_decision. Qed.

Implicit Type (ξ ζ: proph_var) (ξs ζs: list proph_var).

Definition proph_asn := ∀ξ, ξ.ty.

Global Instance proph_asn_inhabited : Inhabited proph_asn :=
  populate (λ π, π.ty.(pt_val)).

Implicit Type π: proph_asn.

Definition s_comb {A B C} (f: A → B → C) (g: A → B) x := (f x) (g x).
Global Infix "⊛" := (s_comb) (left associativity, at level 50).

(** * Prophecy Dependency *)

Local Definition proph_asn_eqv ξs π π' := ∀ξ, ξ ∈ ξs → π ξ = π' ξ.
Local Notation "π .≡{ ξs }≡ π'" := (proph_asn_eqv ξs π π')
  (at level 70, format "π  .≡{ ξs }≡  π'").

Definition proph_dep {A} (vπ: _ → A) ξs := ∀π π', π .≡{ξs}≡ π' → vπ π = vπ π'.
Notation "vπ ./ ξs" := (proph_dep vπ ξs) (at level 70, format "vπ  ./  ξs").

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

(** * Prophecy Log *)

Record proph_log_item :=
  ProphLogItem { pli_pv: proph_var; pli_val: proph_asn → pli_pv.ty }.
Local Notation ".{ ξ := vπ }" := (ProphLogItem ξ vπ)
  (at level 2, format ".{ ξ  :=  vπ }").
Local Notation "pli .pv" := (pli.(pli_pv)) (at level 2, format "pli .pv").
Local Notation "pli .val" := (pli.(pli_val)) (at level 2, format "pli .val").

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

Local Fixpoint proph_log_ok L := match L with
| [] => True
| .{ξ:=vπ} :: L' => ξ ∉ res L' ∧ vπ ./~ res L ∧ proph_log_ok L'
end.
Local Notation ".✓ L" := (proph_log_ok L)
  (at level 20, format ".✓  L").

Local Definition proph_sat π L := Forall (λ pli, π pli.pv = pli.val π) L.
Local Notation "π ◁ L" := (proph_sat π L)
  (at level 70, format "π  ◁  L").

(** ** Satisfiability *)

Local Definition proph_upd ξ vπ π : proph_asn := λ ζ,
  match decide (ξ = ζ) with left eq => rew eq in vπ π | right _ => π ζ end.
Local Notation ":<[ ξ := vπ ]>" := (proph_upd ξ vπ)
  (at level 5, format ":<[ ξ  :=  vπ ]>").

Local Lemma proph_upd_lookup π ξ vπ : :<[ξ:=vπ]> π ξ = vπ π.
Proof. rewrite /proph_upd. case (decide (ξ = ξ))=> [?|?]; by [simpl_eq|]. Qed.
Local Lemma proph_upd_lookup_ne π ξ vπ ζ : ξ ≠ ζ → :<[ξ:=vπ]> π ζ = π ζ.
Proof. rewrite /proph_upd. by case (decide (ξ = ζ))=> [?|?]. Qed.

Local Fixpoint proph_modify π L := match L with
| [] => π
| .{ξ:=vπ} :: L' => proph_modify (:<[ξ:=vπ]> π) L'
end.
Local Notation "π ! L" := (proph_modify π L) (at level 30, format "π  !  L").

Local Lemma proph_modify_eqv L : ∀π, π ! L .≡~{res L}≡ π.
Proof.
  elim L=> [|[??]?] /=; [done|] => Eqv ?? /not_elem_of_cons [??].
  rewrite Eqv; [|done]. by apply proph_upd_lookup_ne.
Qed.

Local Lemma proph_ok_modify_sat L : .✓ L → ∀π, π ! L ◁ L.
Proof.
  rewrite /proph_sat. elim L=> [|[ξ vπ] L'] /=; [done|] => IH [? [? /IH ?]] ?.
  apply Forall_cons. simpl. split; [|done]. rewrite proph_modify_eqv; [|done].
  rewrite proph_upd_lookup. symmetry. set L₀ := .{ξ:=vπ} :: L'.
  have Dep': vπ ./~ res L₀ by done. apply Dep', (proph_modify_eqv L₀).
Qed.

Local Lemma proph_ok_sat L : .✓ L → ∃π, π ◁ L.
Proof. move=> ?. exists (inhabitant ! L). by apply proph_ok_modify_sat. Qed.

(** * Prophecy Camera *)

Implicit Type q: Qp.

Local Definition proph_itemR Ap :=
  csumR fracR (agreeR (leibnizO (proph_asn → Ap))).
Local Definition proph_gmapUR Ap := gmapUR positive (proph_itemR Ap).
Local Definition proph_smryUR := discrete_funUR proph_gmapUR.
Definition prophUR := authUR proph_smryUR.

Implicit Type S: proph_smryUR.

Local Definition aitem {Ap} vπ : proph_itemR Ap := Cinr (to_agree vπ).
Local Definition fitem {Ap} q : proph_itemR Ap := Cinl q.
Local Definition line ξ it : proph_smryUR := .{[ ξ.ty := {[ξ.id := it]} ]}.
Local Definition add_line ξ it S : proph_smryUR :=
  .<[ξ.ty := <[ξ.id := it]> (S ξ.ty)]> S.

Definition prophΣ := #[GFunctor prophUR].
Class prophPreG Σ := ProphPreG { proph_preG_inG:> inG Σ prophUR }.
Class prophG Σ := ProphG { proph_inG:> prophPreG Σ; proph_name : gname }.
Instance subG_prophPreG {Σ} : subG prophΣ Σ → prophPreG Σ.
Proof. solve_inG. Qed.

Definition prophN := nroot .@ "proph".

(** * Iris Propositions *)

Local Definition proph_sim S L :=
  ∀Ap i vπ, S Ap !! i ≡ Some (aitem vπ) ↔ .{$(Ap,i):=vπ} ∈ L.
Local Notation "S :~ L" := (proph_sim S L) (at level 70, format "S  :~  L").

Implicit Type (φπ ψπ: proph_asn → Prop) (φ ψ: Prop).

Section defs.
Context `{!invG Σ, !prophG Σ}.

(** Prophecy Context *)
Local Definition proph_inv: iProp Σ :=
  ∃ S, ⌜∃L, .✓ L ∧ S :~ L⌝ ∗ own proph_name (● S).
Definition proph_ctx: iProp Σ := inv prophN proph_inv.

(** Prophecy Token *)
Definition proph_tok ξ q : iProp Σ := own proph_name(◯ line ξ (fitem q)).
Definition proph_toks ξs q : iProp Σ := [∗ list] ξ ∈ ξs, proph_tok ξ q.

(** Prophecy Observation *)
Local Definition proph_atom pli : iProp Σ :=
  own proph_name (◯ line pli.pv (aitem pli.val)).
Definition proph_obs φπ : iProp Σ :=
  ∃L, ⌜∀π, π ◁ L → φπ π⌝ ∗ [∗ list] pli ∈ L, proph_atom pli.

End defs.

Notation "q :[ ξ ]" := (proph_tok ξ q)
  (at level 2, format "q :[ ξ ]") : bi_scope.
Notation "q :+[ ξs ]" := (proph_toks ξs q)
  (at level 2, format "q :+[ ξs ]") : bi_scope.
Notation "⟨ π , φ ⟩" := (proph_obs (λ π, φ%type%stdpp))
  (π name, at level 5, format "⟨ π ,  φ ⟩") : bi_scope.

(** * Iris Lemmas *)

Section lemmas.
Context `{!invG Σ, !prophG Σ}.

(** Instances *)

Global Instance proph_ctx_persistent : Persistent proph_ctx := _.

Global Instance proph_tok_timeless q ξ : Timeless q:[ξ] := _.
Global Instance proph_tok_fractional ξ : Fractional (λ q, q:[ξ]%I).
Proof.
  move=> ??. by rewrite -own_op -auth_frag_op discrete_fun_singleton_op
    singleton_op -Cinl_op.
Qed.
Global Instance proph_tok_as_fractional q ξ :
  AsFractional q:[ξ] (λ q, q:[ξ]%I) q.
Proof. split; by [|apply _]. Qed.

Global Instance proph_toks_timeless q ξs : Timeless q:+[ξs] := _.
Global Instance proph_toks_fractional ξs : Fractional (λ q, q:+[ξs]%I) := _.
Global Instance proph_toks_as_fractional q ξs :
  AsFractional q:+[ξs] (λ q, q:+[ξs]%I) q.
Proof. split; by [|apply _]. Qed.

Global Instance proph_obs_persistent φπ : Persistent ⟨π, φπ π⟩ := _.
Global Instance proph_obs_timeless φπ : Timeless ⟨π, φπ π⟩ := _.

(** Initialization *)

Lemma proph_init `{!prophPreG Σ} E :
  ↑prophN ⊆ E → ⊢ |={E}=> ∃ _: prophG Σ, proph_ctx.
Proof.
  move=> ?. iMod (own_alloc (● ε)) as (γ) "Own"; [by apply auth_auth_valid|].
  set IProphG := ProphG Σ _ γ. iExists IProphG.
  iMod (inv_alloc _ _ proph_inv with "[Own]") as "?"; [|done]. iModIntro.
  iExists ε. iSplitR; [|done]. iPureIntro. exists []. split; [done|] => ???.
  rewrite lookup_empty. split; move=> Hyp; inversion Hyp.
Qed.

(** Taking a Fresh Prophecy Variable *)

Lemma proph_intro {Ap} E (I: gset positive) :
  ↑prophN ⊆ E → proph_ctx ={E}=∗ ∃i, ⌜i ∉ I⌝ ∗ 1:[$(Ap,i)].
Proof.
  iIntros (?) "?". iInv prophN as (S) "> [OkSim Auth]".
  iDestruct "OkSim" as %[L [? Sim]].
  case (exist_fresh (I ∪ dom _ (S Ap)))
    => [i /not_elem_of_union [? /not_elem_of_dom EqNone]].
  set ξ := $(Ap,i). set S' := add_line ξ (fitem 1) S.
  iMod (own_update _ _ (● S' ⋅ ◯ line ξ (fitem 1)) with "Auth") as "[Auth' ?]".
  { by apply auth_update_alloc,
      discrete_fun_insert_local_update, alloc_singleton_local_update. }
  iModIntro. iSplitL "Auth'"; last first. { iModIntro. iExists i. by iSplit. }
  iModIntro. iExists S'. iSplitR; [|done]. iPureIntro. exists L.
  split; [done|] => Bp j ?. rewrite /S' /add_line /discrete_fun_insert -Sim.
  case (decide (Ap = Bp))=> [?|?]; [|done]. subst. simpl.
  case (decide (i = j))=> [<-|?]; [|by rewrite lookup_insert_ne].
  rewrite lookup_insert EqNone.
  split; move=> Eqv; [apply (inj Some) in Eqv|]; inversion Eqv.
Qed.

(** Prophecy Resolution *)

Local Lemma proph_tok_out S L ξ q :
  S :~ L → own proph_name (● S) -∗ q:[ξ] -∗ ⌜ξ ∉ res L⌝.
Proof.
  move=> Sim. iIntros "Auth Tok".
  iDestruct (own_valid_2 with "Auth Tok") as %ValBoth. iPureIntro.
  move=> /(elem_of_list_fmap_2 pli_pv) [[[Ap ?]?] [? /Sim Eqv]]. subst.
  move: ValBoth=> /auth_both_valid_discrete [Inc _].
  move/(discrete_fun_included_spec_1 _ _ Ap) in Inc.
  rewrite /line discrete_fun_lookup_singleton in Inc. simpl in Inc.
  move: Eqv. move: Inc=> /singleton_included_l [? [-> Inc]]. move=> Eqv.
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
  move: ξ vπ => [Ap i] vπ. set ξ := $(Ap,i). iIntros (? Dep) "? Tok Ptoks".
  iInv prophN as (S) "> [OkSim Auth]". iDestruct "OkSim" as %[L [? Sim]].
  iDestruct (proph_tok_out with "Auth Tok") as %Outξ; [done|].
  set L' := .{ξ := vπ} :: L. iAssert ⌜∀ζ, ζ ∈ ζs → ζ ∉ res L'⌝%I as %Outζs.
  { iIntros (? In).
    iDestruct (big_sepL_elem_of with "Ptoks") as "Ptok"; [apply In|].
    iDestruct (proph_tok_ne with "Tok Ptok") as %?.
    iDestruct (proph_tok_out with "Auth Ptok") as %?; [done|].
    by rewrite not_elem_of_cons. }
  set S' := add_line ξ (aitem vπ) S.
  iMod (own_update_2 _ _ _ (● S' ⋅ ◯ line ξ (aitem vπ)) with "Auth Tok")
    as "[Auth' #?]".
  { apply auth_update, discrete_fun_singleton_local_update_any,
      singleton_local_update_any => ? _. by apply exclusive_local_update. }
  iModIntro. iSplitL "Auth'"; last first.
  { iModIntro. iSplitR; [|done]. iExists [.{ξ:=vπ}].
    iSplitR; [|by rewrite big_sepL_singleton]. iPureIntro=> ? Sat.
    by inversion Sat. }
  iModIntro. iExists S'. iSplitR; [|done]. iPureIntro. exists L'. split.
  { split; [done| split; [|done]] => ?? Eqv. apply Dep => ? /Outζs ?.
    by apply Eqv. }
  have InLNe ζ wπ : .{ζ:=wπ} ∈ L → ξ ≠ ζ.
  { move=> /(elem_of_list_fmap_1 pli_pv) ??. by subst. }
  move=> Bp j ?. rewrite elem_of_cons. case (decide (ξ = $(Bp,j)))=> [Eq|?].
  { inversion Eq. subst.
    rewrite /S' /add_line discrete_fun_lookup_insert lookup_insert. split.
    - move=> /(inj (Some ∘ aitem)) ->. by left.
    - move=> [Eq'|/InLNe ?]; by [dependent destruction Eq'|]. }
  have Eqv : S' Bp !! j ≡ S Bp !! j.
  { rewrite /S' /add_line /discrete_fun_insert.
    case (decide (Ap = Bp))=> [?|?]; [|done]. simpl_eq.
    case (decide (i = j))=> [?|?]; by [subst|rewrite lookup_insert_ne]. }
  rewrite Eqv Sim. split; [by right|].
  move=> [Eq|?]; by [dependent destruction Eq|].
Qed.

(** Operations on Prophecy Observations *)

Lemma proph_obs_trivial φ : φ → ⊢ ⟨_, φ⟩.
Proof. move=> ?. iExists []. by iSplit. Qed.

Lemma proph_obs_weaken φπ ψπ : (∀π, φπ π → ψπ π) → ⟨π, φπ π⟩ -∗ ⟨π, ψπ π⟩.
Proof.
  move=> Wkn. iIntros "Obs". iDestruct "Obs" as (L) "[SatImp ?]".
  iDestruct "SatImp" as %SatImp. iExists L. iSplitR; [|done]. iPureIntro=> ??.
  by apply Wkn, SatImp.
Qed.

Lemma proph_obs_merge φπ ψπ : ⟨π, φπ π⟩ -∗ ⟨π, ψπ π⟩ -∗ ⟨π, φπ π ∧ ψπ π⟩.
Proof.
  iIntros "Obs Obs'". iDestruct "Obs" as (L) "[SatImp Atoms]".
  iDestruct "Obs'" as (L') "[SatImp' Atoms']". iDestruct "SatImp" as %SatImp.
  iDestruct "SatImp'" as %SatImp'. iExists (L ++ L').
  iSplitR; [|by rewrite big_sepL_app; iCombine "Atoms Atoms'" as "?"].
  iPureIntro=> ? /Forall_app [??]. split; by [apply SatImp|apply SatImp'].
Qed.

Lemma proph_obs_sat E φπ :
  ↑prophN ⊆ E → proph_ctx -∗ ⟨π, φπ π⟩ ={E}=∗ ⌜∃π₀, φπ π₀⌝.
Proof.
  iIntros (?) "? Obs". iDestruct "Obs" as (L') "[SatImp #Atoms]".
  iDestruct "SatImp" as %SatImp. iInv prophN as (S) "> [OkSim Auth]".
  iDestruct "OkSim" as %[L [Ok Sim]].
  move: (Ok)=> /proph_ok_sat [π /Forall_forall Sat]. iModIntro.
  iAssert ⌜π ◁ L'⌝%I as %?; last first.
  { iSplitL; last first. { iPureIntro. exists π. by apply SatImp. }
    iModIntro. iExists S. iSplitR; [|done]. iPureIntro. by exists L. }
  rewrite /proph_sat Forall_forall. iIntros ([[Ap i] vπ] In). simpl.
  iAssert (proph_atom .{$(Ap,i):=vπ}) with "[Atoms]" as "Atom".
  { iApply big_sepL_elem_of; by [apply In|]. }
  iDestruct (own_valid_2 with "Auth Atom") as %ValBoth. simpl in ValBoth.
  iPureIntro. apply (Sat .{$(Ap,i):=vπ}), Sim.
  move: ValBoth=> /auth_both_valid_discrete [Inc Val].
  move/(discrete_fun_included_spec_1 _ _ Ap) in Inc.
  rewrite /line discrete_fun_lookup_singleton in Inc.
  move: Inc=> /singleton_included_l [it [Eqv /Some_included [->|Inc]]]; [done|].
  rewrite Eqv. constructor.
  apply (lookup_valid_Some _ i it) in Val; [|done]. move: Val.
  move: Inc=> /csum_included [->|[[?[?[?]]]|[?[?[Eq[-> Inc]]]]]]; [done|done|].
  move=> Val. move: Inc. move: Val=> /Cinr_valid/to_agree_uninj [? <-].
  inversion Eq. by move/to_agree_included <-.
Qed.

End lemmas.

(** * Prophecy Equalizer *)

Definition proph_eqz `{!invG Σ, !prophG Σ} {A} (uπ vπ: _ → A) : iProp Σ :=
  ∀ξs q, ⌜vπ ./ ξs⌝ -∗ q:+[ξs] ={↑prophN}=∗ ⟨π, uπ π = vπ π⟩ ∗ q:+[ξs].

Notation "uπ :== vπ" := (proph_eqz uπ vπ)
  (at level 70, format "uπ  :==  vπ") : bi_scope.

Section lemmas.
Context `{!invG Σ, !prophG Σ}.

(** ** Constructing Prophecy Equalizers *)

Lemma proph_token_eqz ξ vπ : proph_ctx -∗ 1:[ξ] -∗ (.$ ξ) :== vπ.
Proof.
  iIntros "PROPH Tok". iIntros (???) "Ptoks".
  by iMod (proph_resolve with "PROPH Tok Ptoks").
Qed.

Lemma proph_obs_eqz {A} (uπ vπ: _ → A) : ⟨π, uπ π = vπ π⟩ -∗ uπ :== vπ.
Proof. iIntros "?". iIntros (???) "?". iModIntro. by iSplit. Qed.

Lemma proph_eqz_modify {A} (uπ uπ' vπ: _ → A) :
  ⟨π, uπ' π = uπ π⟩ -∗ uπ :== vπ -∗ uπ' :== vπ.
Proof.
  iIntros "#Obs Eqz". iIntros (???) "Ptoks".
  iMod ("Eqz" with "[%//] Ptoks") as "[#Obs' ?]". iModIntro. iSplitR; [|done].
  iDestruct (proph_obs_merge with "Obs Obs'") as "Obs''".
  by iApply proph_obs_weaken; [|iApply "Obs''"] => ? [-> ?].
Qed.

Lemma proph_eqz_constr {A B} f `{Inj A B (=) (=) f} uπ vπ :
  uπ :== vπ -∗ f ∘ uπ :== f ∘ vπ.
Proof.
  iIntros "Eqz". iIntros (?? Dep) "Ptoks". move/proph_dep_destr in Dep.
  iMod ("Eqz" with "[%//] Ptoks") as "[#Obs ?]". iModIntro. iSplitR; [|done].
  iApply proph_obs_weaken; [|by iApply "Obs"] => ??. by apply (f_equal f).
Qed.

Lemma proph_eqz_constr2 {A B C} f `{Inj2 A B C (=) (=) (=) f} uπ uπ' vπ vπ' :
  uπ :== vπ -∗ uπ' :== vπ' -∗ f ∘ uπ ⊛ uπ' :== f ∘ vπ ⊛ vπ'.
Proof.
  iIntros "Eqz Eqz'". iIntros (?? Dep) "Ptoks".
  move: Dep=> /proph_dep_destr2 [??].
  iMod ("Eqz" with "[%//] Ptoks") as "[#Obs Ptoks]".
  iMod ("Eqz'" with "[%//] Ptoks") as "[#Obs' ?]". iModIntro. iSplitR; [|done].
  iDestruct (proph_obs_merge with "Obs Obs'") as "Obs''".
  iApply proph_obs_weaken; [|by iApply "Obs''"] => ?[??]. by apply (f_equal2 f).
Qed.

End lemmas.
