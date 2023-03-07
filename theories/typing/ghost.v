From lrust.typing Require Export type.
From lrust.typing Require Import programs shr_bor own type_context product.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.
Implicit Type 𝔄l: (list syn_type).

Lemma proph_dep_ghost' {A} (vπ: proph A) ξl' ξl level: vπ ./{level} ξl → vπ ./{S level} ξl'.
Proof. move=> H ?? Eqv. apply H. intros ?[? _]. apply Eqv. split. lia. right. lia. Qed.

Fixpoint hrenew {A B: Type} (F: B → Type) (G: A → B) {Xl} (xl: hlist (F∘G) Xl)
: hlist F (G<$>Xl).
  destruct Xl. simpl. exact +[].
  simpl. inversion xl. constructor. exact X0. apply hrenew. exact X1.
Defined.

Fixpoint hrenew' {A B: Type} (F: B → Type) (G: A → B) {Xl} (xl: hlist F (G<$>Xl))
: hlist (F∘G) Xl.
  destruct Xl. simpl. exact +[].
  simpl. inversion xl. constructor. exact X0. apply hrenew'. exact X1.
Defined.

Definition prenew {A B: Type} (F: B → Type) (G: A → B) {Xl} (xl: plist (F∘G) Xl)
: plist F (G<$>Xl).
  induction Xl. simpl. exact -[].
  simpl. inversion xl. constructor. exact phd. apply IHXl. exact ptl.
Defined.

Definition prenew' {A B: Type} (F: B → Type) (G: A → B) {Xl} (xl: plist F (G<$>Xl))
: plist (F∘G) Xl.
  induction Xl. simpl. exact -[].
  simpl. inversion xl. constructor. exact phd. apply IHXl. exact ptl.
Defined.

Lemma prenew_apply' {A B I: Type} (F: B → Type) (G: A → B) {Xl} (pl: plist (λ X, I -> F X) (G<$>Xl)) (x: I) :
  prenew' F G (pl -$ x) = prenew' _ G pl -$ x.
Proof.
  induction Xl; simpl. done. destruct pl; rewrite IHXl; done.
Qed.

Lemma prenew_iso A B F G Xl: Iso (@prenew A B F G Xl) (@prenew' A B F G Xl).
Proof. 
  split; fun_ext; simpl; intros; induction Xl; 
  simpl; destruct x; try done; rewrite IHXl; done.
Qed.

Section ghost.
  Context `{!typeG Σ}.

  Program Definition ghost {𝔄} (ty: type 𝔄) : type (ghostₛ 1 𝔄) := {|
    st_size := 0;  st_lfts :=[];  st_E := [];
    st_proph (vπ: (proph (ghostₛ 1 𝔄))) _ := exists ξl, ty.(ty_proph) vπ ξl;
    st_own vπ d tid vl := ⌜vl = [] ∧ ∃ ξl, ty.(ty_proph) vπ ξl⌝
  |}%I.
  Next Obligation.
    move=> * /=. by iIntros "(->&_)".
  Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> * /=. iIntros "**".
    iApply step_fupdN_full_intro. do 2 iModIntro. destruct H as [->?].
    iExists [], 1%Qp. iFrame. do 2 (iSplit; [done|]).
    iIntros. iModIntro. done.
  Qed.
 Next Obligation. 
  move=> /= ????[??]. eapply proph_dep_ghost'. eapply ty_proph_weaken. done.
 Qed.

  Global Instance ghost_ne {𝔄} : NonExpansive (@ghost 𝔄).
  Proof. split; intros; simpl; try done; setoid_rewrite H; done. Qed.
End ghost.

Section typing.
  Context `{!typeG Σ}.

  Global Instance ghost_send {𝔄} (ty: type 𝔄) : Send (ghost ty).
  Proof. move=> Eq >/=. done. Qed.

  Lemma ghost_resolve {𝔄} (ty: type 𝔄) E L : resolve E L (ghost ty) (const True).
  Proof. apply resolve_just. Qed.
(* 
  Lemma ghost_type_incl {𝔄 𝔅}(f: 𝔄 → 𝔅) ty ty' :
    type_incl ty ty' f -∗ type_incl (ghost ty) (ghost ty') f.
  Proof.
    iIntros "([_ %ProphIn]&LftIn&_)".
    iApply (type_incl_simple_type with "[] []"); [done| | |]; simpl.
    intros ??[??]. eexists. apply ProphIn. done.
    iApply lft_incl_refl.
    iModIntro; iIntros (????[->[??]]). iPureIntro. split. done.
    eexists. apply ProphIn. done. 2:{iDestruct #1 as "(%&?&?)". } [| ]
  Qed. *)

  (* Lemma ghost_subtype {𝔄 𝔅} E L κ κ' (f: 𝔄 → 𝔅) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    subtype E L (&shr{κ} ty) (&shr{κ'} ty') f.
  Proof.
    move=> In Sub ?. iIntros "L". iDestruct (In with "L") as "#In".
    iDestruct (Sub with "L") as "#Sub". iIntros "!> #?".
    iApply shr_type_incl; by [iApply "In"|iApply "Sub"].
  Qed. *)

  (* Lemma ghost_eqtype {𝔄 𝔅} E L κ κ' (f: 𝔄 → 𝔅) g ty ty' :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' f g →
    eqtype E L (&shr{κ} ty) (&shr{κ'} ty') f g.
  Proof. move=> [??] [??]. split; by apply shr_subtype. Qed. *)

  Definition null_loc : loc := inhabitant.
  Definition null_val : val := #null_loc.

  Lemma ghost_new {𝔄} (ty: type 𝔄) κ E L p:
    lctx_lft_alive E L (ty_lft (&shr{κ} ty)%T) →
     typed_instr E L +[p ◁ (&shr{κ} ty)] Skip (λ _, +[null_val ◁ (box (ghost ty))]) id.
  Proof.
    intros Alv.
    iIntros (??[aπ[]]) "LFT TIME _ _ E $ L [p _] Obs".
    iMod (Alv with "E L") as (?) "[κ ToL]"; [done|].
    iDestruct "p" as ([[]|][|]Ev) "[#⧖ ty]"=>//.
    iMod (ty_own_proph with "LFT [] ty κ") as "Upd";
      [done| iApply lft_incl_refl| ].
    iApply (wp_step_fupdN_persistent_time_receipt _ _ ∅ with "TIME ⧖ [Upd]")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L.  }
    wp_seq. iIntros "(%&%&%&ξl&tolft)".
    iMod ("tolft" with "ξl") as "(_&lft)".
    iMod ("ToL" with "lft") as "$".
    iExists -[aπ]. iModIntro. iSplit. iSplit; [|done]. 
    iExists _, _. iFrame "⧖". iSplit; [done|].
    simpl. iSplit; [|done]. iNext. iExists _. iSplit; [by iApply heap_mapsto_vec_nil|].
    iPureIntro. split; [done|]. eexists _. done. done.
  Qed.

  Definition logic_fn {𝔄l 𝔅} (tyl: typel 𝔄l) (tyr: type 𝔅) (f: (plist of_syn_type 𝔄l) → 𝔅) :=
    forall (aπl: (plist _ 𝔄l)), 
    (forallHL_1 (λ _ ty aπ, ∃ ξl, (ty_proph ty aπ ξl)) tyl aπl) 
    → ∃ ξl, (ty_proph tyr (λ π, f (papply aπl π)) ξl).

  Definition tctx_ghost {𝔄l} (tyl: typel 𝔄l) := ((λ _ ty, null_val ◁ (box (ghost ty))) +<$> tyl).

  Definition tctx_ghost' {𝔄l} (tyl: typel 𝔄l) :=
    hrenew tctx_elt (ghostₛ 1) (tctx_ghost tyl).

  Lemma logic_fn_ghost_tctx_incl {𝔄l 𝔅} (tyl: typel 𝔄l) (tyr: type 𝔅) f E L:
   logic_fn tyl tyr f → tctx_incl E L (null_val ◁ (box ()) +:: (tctx_ghost' tyl)) +[null_val ◁ (box (ghost tyr))] (λ post '(_ -:: l), post (-[f (prenew' _ _ l)])).
  Proof. 
    unfold logic_fn. intros.
    (split; [solve_proper|]); iIntros (??[? vπl]?) "_ _ _ _ $ ty Obs"; iModIntro;  simpl.
    set pπ := ((prenew' _ _ vπl): plist (λ 𝔄, proph 𝔄) 𝔄l).
    iExists -[_]. iFrame "Obs". iSplit; [|done].
    rewrite 2! (tctx_hasty_val null_val).
    iDestruct "ty" as "((%&⧖&?)&ty)". destruct d; [done|].
    iExists _. iFrame "⧖". 
    simpl. iSplit; [|done].
    iAssert (▷⌜_⌝)%I with "[ty]" as ">X"; last first.
    iAssert ⌜_⌝%I as %X. done. destruct (H pπ X).
    iNext. iExists []. iSplit. by iApply heap_mapsto_vec_nil.
    iPureIntro. split; [done|]. exists x. unfold pπ in H0.
    revert H0. eassert (impl _ _); [|done]. f_equiv. 
    fun_ext. intros. by rewrite prenew_apply'. clear H postπ f.
    iInduction tyl as [|? ?] "IH"; destruct vπl. iPureIntro. constructor.
    rewrite /tctx_ghost' /tctx_ghost. simpl. rewrite (tctx_hasty_val null_val).
    iDestruct "ty" as "((%&_&own)&ty)". destruct d0; [done|simpl].
    iDestruct "own" as "((%&_&_&>%fst)&_)".
    iDestruct ("IH" with "ty") as ">%rest".
    iNext. iPureIntro. unfold pπ. simpl. by constructor.
  Qed.

End typing.
