From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l ℭl 𝔇l: list syn_type).

Definition path := expr.
Bind Scope expr_scope with path.

(* TODO: Consider making this a pair of a path and the rest. We could
   then e.g. formulate tctx_elt_hasty_path more generally. *)
Inductive tctx_elt `{!typeG Σ} 𝔄 : Type :=
| TCtx_hasty (p: path) (ty: type 𝔄)
| TCtx_blocked (p: path) (κ: lft) (ty: type 𝔄).

Notation tctx := (hlist tctx_elt).

Notation "p ◁ ty" := (TCtx_hasty _ p ty%T) (at level 55).
Notation "p ◁{ κ } ty" := (TCtx_blocked _ p κ ty%T)
   (at level 55, format "p  ◁{ κ }  ty").

Definition pred A := A → Prop.
Definition predl 𝔄l := pred (plist of_syn_type 𝔄l).
Definition predl_trans 𝔄l 𝔅l := predl 𝔅l → predl 𝔄l.

Definition trans_app {𝔄l 𝔅l ℭl 𝔇l} (tr: predl_trans 𝔄l 𝔅l) (tr': predl_trans ℭl 𝔇l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ 𝔇l) :=
  λ post bdl, tr (λ al, tr' (λ cl, post (al -++ cl)) (psepr bdl)) (psepl bdl).

Definition trans_lower {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (ℭl ++ 𝔄l) (ℭl ++ 𝔅l) :=
  λ post cal, tr (λ bl, post (psepl cal -++ bl)) (psepr cal).

Definition trans_upper {𝔄l 𝔅l ℭl} (tr: predl_trans 𝔄l 𝔅l)
  : predl_trans (𝔄l ++ ℭl) (𝔅l ++ ℭl) :=
  λ post acl, tr (λ bl, post (bl -++ psepr acl)) (psepl acl).

Definition trans_tail {𝔄 𝔅l ℭl} (tr: predl_trans 𝔅l ℭl)
  : predl_trans (𝔄 :: 𝔅l) (𝔄 :: ℭl) :=
  λ post '(a -:: cl), tr (λ bl, post (a -:: bl)) cl.

Section type_context.
  Context `{!typeG Σ}.

  Fixpoint eval_path (p: path) : option val := match p with
    | BinOp OffsetOp e (Lit (LitInt n)) => match eval_path e with
        Some (#(LitLoc l)) => Some (#(l +ₗ n)) | _ => None end
    | e => to_val e end.

  Lemma eval_path_of_val (v: val) : eval_path v = Some v.
  Proof. destruct v. done. simpl. rewrite (decide_left _). done. Qed.

  Lemma wp_eval_path E p v : eval_path p = Some v → ⊢ WP p @ E {{ v', ⌜v' = v⌝ }}.
  Proof.
    revert v; induction p; intros v; try done.
    { intros [=]. by iApply wp_value. }
    { move=> /of_to_val=> ?. by iApply wp_value. }
    simpl. destruct op; try discriminate; [].
    destruct p2; try (intros ?; by iApply wp_value); [].
    destruct l; try (intros ?; by iApply wp_value); [].
    destruct (eval_path p1); try done.
    destruct v0; try discriminate; [].
    destruct l; try discriminate; [].
    intros [=<-]. wp_bind p1. iApply (wp_wand with "[]").
    { iApply IHp1. done. }
    iIntros (v) "%". subst v. wp_op. done.
  Qed.

  Lemma eval_path_closed p v : eval_path p = Some v → Closed [] p.
  Proof.
    intros Hpv. revert v Hpv.
    induction p as [| | |[] p IH [|[]| | | | | | | | | |] _| | | | | | | |]=>//.
    - unfold eval_path=>? /of_to_val <-. apply is_closed_of_val.
    - simpl. destruct (eval_path p) as [[[]|]|]; intros ? [= <-].
      specialize (IH _ eq_refl). apply _.
  Qed.

  (** Type context element *)
  Definition tctx_elt_interp {𝔄} (tid: thread_id) (t: tctx_elt 𝔄) (vπ: proph 𝔄)
    : iProp Σ := match t with
    | p ◁ ty => ∃v d, ⌜eval_path p = Some v⌝ ∗ ⧖d ∗ ty.(ty_own) vπ d tid [v]
    | p ◁{κ} ty => ∃v, ⌜eval_path p = Some v⌝ ∗
        ([†κ] ={⊤}=∗ ∃vπ' d, ▷(vπ :== vπ') ∗ ⧖d ∗ ty.(ty_own) vπ' d tid [v]) end%I.

  (* Block tctx_elt_interp from reducing with simpl when t is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.

End type_context.

(** Type context *)
Notation tctx_interp tid :=
  (big_sepHL_1 (λ 𝔄 t vπ, @tctx_elt_interp _ _ 𝔄 tid t vπ)).

Section lemmas.
  Context `{!typeG Σ}.

  Lemma tctx_hasty_val {𝔄} (v: val) (ty: _ 𝔄) vπ tid :
    tctx_elt_interp tid (v ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty.(ty_own) vπ d tid [v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (??) "(#EQ & ? & ?)".
      iDestruct "EQ" as %[=->]. eauto.
    - iDestruct 1 as (d) "[??]". eauto.
  Qed.

  Lemma tctx_elt_interp_hasty_path {𝔄} p1 p2 (ty: _ 𝔄) tid vπ :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (p1 ◁ ty) vπ ≡ tctx_elt_interp tid (p2 ◁ ty) vπ.
  Proof. intros Hp. rewrite /tctx_elt_interp /=. setoid_rewrite Hp. done. Qed.

  Lemma tctx_hasty_val' {𝔄} tid p v (ty: _ 𝔄) vπ:
    Some v = eval_path p →
    tctx_elt_interp tid (p ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty.(ty_own) vπ d tid [v].
  Proof.
    move=> ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    by rewrite eval_path_of_val.
  Qed.

  Lemma wp_hasty {𝔄} E tid p (ty : type 𝔄) vπ Φ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗
    (∀v d, ⌜Some v = eval_path p⌝ -∗ ⧖d -∗ ty.(ty_own) vπ d tid [v] -∗ Φ v) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iDestruct 1 as (???) "[#? ?]". iIntros "ToΦ". iApply (wp_wand with "[]");
    [by iApply wp_eval_path|]. iIntros (?) "->". by iApply "ToΦ".
  Qed.

  Lemma closed_hasty {𝔄} tid p (ty: _ 𝔄) vπ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗ ⌜Closed [] p⌝.
  Proof. iDestruct 1 as (???) "(_ & _)". eauto using eval_path_closed. Qed.

  (** Copy typing contexts *)
  Class CopyC {𝔄l} (T: tctx 𝔄l) :=
    copyc_persistent tid vπl : Persistent (tctx_interp tid T vπl).
  Global Existing Instances copyc_persistent.

  Global Instance tctx_nil_copy: CopyC +[].
  Proof. rewrite /CopyC. apply _. Qed.

  Global Instance tctx_cons_copy {𝔄 𝔄l} p (ty: _ 𝔄) (T: _ 𝔄l) :
    Copy ty → CopyC T → CopyC (p ◁ ty +:: T).
  Proof. rewrite /CopyC=> ???[??]. apply _. Qed.

  (** Send typing contexts *)
  Class SendC {𝔄l} (T: tctx 𝔄l) := sendc_change_tid tid1 tid2 vπl :
    tctx_interp tid1 T vπl ⊣⊢ tctx_interp tid2 T vπl.

  Global Instance tctx_nil_send: SendC +[].
  Proof. done. Qed.

  Global Instance tctx_cons_send {𝔄 𝔄l} p (ty: _ 𝔄) (T: _ 𝔄l) :
    Send ty → SendC T → SendC (p ◁ ty +:: T).
  Proof.
    move=> Eq Eq' ??[??]/=. rewrite Eq' /tctx_elt_interp. do 7 f_equiv.
    by rewrite Eq.
  Qed.

  (** Type context inclusion *)
  Definition tctx_incl {𝔄l 𝔅l} (E: elctx) (L: llctx) (T: tctx 𝔄l) (T': tctx 𝔅l)
    (tr: predl_trans 𝔄l 𝔅l) : Prop := ∀tid q vπl postπ,
      lft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
      tctx_interp tid T vπl -∗ ⟨π, tr (postπ π) (vπl -$ π)⟩ ={⊤}=∗ ∃vπl',
      llctx_interp L q ∗ ⟨π, postπ π (vπl' -$ π)⟩ ∗ tctx_interp tid T' vπl'.

  Lemma tctx_incl_impl {𝔄l 𝔅l} (T: _ 𝔄l) (T': _ 𝔅l) (tr tr': _ → _ → Prop) E L :
    (∀post vl, tr post vl → tr' post vl) →
    tctx_incl E L T T' tr' → tctx_incl E L T T' tr.
  Proof.
    move=> Imp In. iIntros (????) "LFT PROPH UNIQ E L T #Obs".
    iMod (In with "LFT PROPH UNIQ E L T []") as "$"; [|done].
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma tctx_incl_eq {𝔄l 𝔅l} (T: _ 𝔄l) (T': _ 𝔅l) tr tr' E L :
    (∀post vl, tr post vl = tr' post vl) →
    tctx_incl E L T T' tr' → tctx_incl E L T T' tr.
  Proof. move=> Eq. apply tctx_incl_impl=> ??. by rewrite Eq. Qed.

  Lemma tctx_incl_refl {𝔄l} (T: _ 𝔄l) E L : tctx_incl E L T T id.
  Proof. move=> ?? vπl ?. iIntros. iExists vπl. by iFrame. Qed.

  Lemma tctx_incl_trans {𝔄l 𝔅l ℭl} (T1: _ 𝔄l) (T2: _ 𝔅l) (T3: _ ℭl) tr tr' E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L T2 T3 tr' → tctx_incl E L T1 T3 (tr ∘ tr').
  Proof.
    move=> In In' >. iIntros "#LFT #PROPH #UNIQ #E L T Obs".
    iMod (In with "LFT PROPH UNIQ E L T Obs") as (?) "(L & Obs & T)".
    iMod (In' with "LFT PROPH UNIQ E L T Obs") as (vπl'') "(?&?&?)".
    iExists vπl''. by iFrame.
  Qed.

  Lemma tctx_incl_app {𝔄l 𝔅l ℭl 𝔇l}
    (T1: _ 𝔄l) (T1': _ 𝔅l) (T2: _ ℭl) (T2': _ 𝔇l) tr tr' E L :
    tctx_incl E L T1 T1' tr → tctx_incl E L T2 T2' tr' →
    tctx_incl E L (T1 h++ T2) (T1' h++ T2') (trans_app tr tr').
  Proof.
    move=> Hincl1 Hincl2 ?? vπl ?. move: (papp_ex vπl)=> [?[?->]].
    iIntros "#LFT #PROPH #UNIQ #E L [T1 T2] Obs".
    iMod (Hincl1 with "LFT PROPH UNIQ E L T1 [Obs]")  as (wπl) "(L & Obs & T1')".
    { iApply proph_obs_eq; [|done]=> ?.
      by rewrite /trans_app papply_app papp_sepl papp_sepr. }
    iMod (Hincl2 with "LFT PROPH UNIQ E L T2 Obs") as (wπl') "(L &?& T2')".
    iExists (wπl -++ wπl'). iCombine "T1' T2'" as "$". iFrame "L".
    iApply proph_obs_eq; [|done]=>/= ?. by rewrite papply_app.
  Qed.

  Lemma tctx_incl_frame_l {𝔄l 𝔅l ℭl} (T: _ 𝔄l) (T': _ 𝔅l) (Tf: _ ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (Tf h++ T) (Tf h++ T') (trans_lower tr).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first.
    { apply tctx_incl_app=>//. apply tctx_incl_refl. } done.
  Qed.
  Lemma tctx_incl_frame_r {𝔄l 𝔅l ℭl} (T: _ 𝔄l) (T': _ 𝔅l) (Tf: _ ℭl) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (T h++ Tf) (T' h++ Tf) (trans_upper tr).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first.
    { apply tctx_incl_app=>//. apply tctx_incl_refl. } done.
  Qed.
  Lemma tctx_incl_tail {𝔄 𝔄l 𝔅l} (t: _ 𝔄) (T1: _ 𝔄l) (T2: _ 𝔅l) tr E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L (t +:: T1) (t +:: T2) (trans_tail tr).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first.
    { by apply (tctx_incl_frame_l _ _ +[_]). } by move=> ?[??].
  Qed.

  Lemma tctx_incl_swap {𝔄 𝔅 𝔄l} (t: _ 𝔄) (t': _ 𝔅) (T: _ 𝔄l) E L :
    tctx_incl E L (t +:: t' +:: T) (t' +:: t +:: T)
      (λ post '(a -:: b -:: al), post (b -:: a -:: al)).
  Proof.
    iIntros (??(vπ & vπ' & wπl)?) "_ _ _ _ $ (?&?&?) ?!>".
    iExists (vπ' -:: vπ -:: wπl). iFrame.
  Qed.

  Lemma tctx_incl_leak_lower {𝔄l 𝔅l} (T: _ 𝔄l) (T': _ 𝔅l) E L :
    tctx_incl E L (T h++ T') T (λ post abl, post (psepl abl)).
  Proof.
    move=> ?? abπl ?. move: (papp_ex abπl)=> [aπl[?->]].
    iIntros "_ _ _ _ $ [T _] ? !>". iExists aπl. iFrame "T".
    iApply proph_obs_eq; [|done]=> ?. by rewrite/= papply_app papp_sepl.
  Qed.

  Lemma copy_tctx_incl {𝔄 𝔄l} (ty: _ 𝔄) `{!Copy ty} (T: _ 𝔄l) p E L :
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty +:: p ◁ ty +:: T)
      (λ post '(a -:: al), post (a -:: a -:: al)).
  Proof.
    iIntros (??[vπ wπl]?) "_ _ _ _ $ /=[#? T] Obs !>".
    iExists (vπ -:: vπ -:: wπl). iFrame "Obs T". by iSplit.
  Qed.

  Lemma subtype_tctx_incl {𝔄 𝔅 𝔄l} ty ty' (f: 𝔄 → 𝔅) (T: _ 𝔄l) p E L :
    subtype E L ty ty' f →
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty' +:: T)
      (λ post '(a -:: al), post (f a -:: al)).
  Proof.
    iIntros (Sub ??[vπ wπl]?) "#LFT _ _ E L /=[(%v & %d &%&?& ty) T] Obs /=".
    iDestruct (Sub with "L E") as "#(_ & _ & #InOwn & _)". iModIntro.
    iExists (f ∘ vπ -:: wπl). iFrame "L Obs T". iExists v, d.
    do 2 (iSplit; [done|]). by iApply "InOwn".
  Qed.

  Lemma subtype_tctx_incl_blocked {𝔄 𝔅 𝔄l} ty ty' `{!@Inj 𝔄 𝔅 (=) (=) f}
    κ κ' (T: _ 𝔄l) p E L :
    subtype E L ty ty' f → lctx_lft_incl E L κ κ' →
    tctx_incl E L (p ◁{κ} ty +:: T) (p ◁{κ'} ty' +:: T)
      (λ post '(a -:: al), post (f a -:: al)).
  Proof.
    iIntros (Sub InLft ??[vπ wπl]?) "#LFT _ _ E L /=[(%v &%& Upd) T] Obs".
    iDestruct (Sub with "L E") as "#(_&_& #InOwn &_)".
    iDestruct (InLft with "L E") as "#InLft". iModIntro. iExists (f ∘ vπ -:: wπl).
    iFrame "L Obs T". iExists v. iSplit; [done|]. iIntros "†κ'".
    iMod (lft_incl_dead with "InLft †κ'") as "†κ"; [done|].
    iMod ("Upd" with "†κ") as (vπ' d) "(?& d & ty)". iModIntro.
    iExists (f ∘ vπ'), d. iFrame "d".
    iSplitR "ty"; by [iApply proph_eqz_constr|iApply "InOwn"].
  Qed.

  (* Extracting from a type context. *)

  Definition tctx_extract_elt {𝔄 𝔄l 𝔅l} E L (t: tctx_elt 𝔄)
    (T: tctx 𝔄l) (T': tctx 𝔅l) (tr: predl_trans 𝔄l (𝔄 :: 𝔅l)) : Prop :=
    tctx_incl E L T (t +:: T') tr.

  Lemma tctx_extract_elt_further {𝔄 𝔅 𝔄l 𝔅l}
    (t: _ 𝔄) (t': _ 𝔅) (T: _ 𝔄l) (T': _ 𝔅l) tr E L :
    tctx_extract_elt E L t T T' tr →
    tctx_extract_elt E L t (t' +:: T) (t' +:: T')
      (λ post '(b -:: al), tr (λ '(a -:: bl), post (a -:: b -:: bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first. { eapply tctx_incl_trans;
    by [eapply tctx_incl_tail|apply tctx_incl_swap]. } move=> ?[??]/=. f_equal.
  Qed.

  Lemma tctx_extract_elt_here_copy {𝔄 𝔅 𝔄l} ty ty' (f: 𝔄 → 𝔅) (T: _ 𝔄l) p p' E L :
    p = p' → Copy ty' → subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p' ◁ ty' +:: T) (p' ◁ ty' +:: T)
      (λ post '(b -:: al), post (f b -:: b -:: al)).
  Proof.
    move=> ->??. eapply tctx_incl_eq; last first. { eapply tctx_incl_trans;
    by [apply copy_tctx_incl|apply subtype_tctx_incl]. } by move=> ?[??].
  Qed.

  Lemma tctx_extract_elt_here_exact {𝔄 𝔄l} (t: _ 𝔄) (T: _ 𝔄l) E L :
    tctx_extract_elt E L t (t +:: T) T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_elt_here {𝔄 𝔅 𝔄l} ty ty' (f: 𝔅 → 𝔄) (T: _ 𝔄l) p E L :
    subtype E L ty' ty f →
    tctx_extract_elt E L (p ◁ ty) (p ◁ ty' +:: T) T
      (λ post '(b -:: al), post (f b -:: al)).
  Proof.
    move=> ?. eapply tctx_incl_eq; [|by apply subtype_tctx_incl].
    by move=> ?[??].
  Qed.

  Lemma tctx_extract_elt_here_blocked {𝔄 𝔅 𝔄l} κ κ' ty ty'
    (f: 𝔅 → 𝔄) `{!Inj (=) (=) f} (T: _ 𝔄l) p E L :
    subtype E L ty' ty f → lctx_lft_incl E L κ' κ →
    tctx_extract_elt E L (p ◁{κ} ty) (p ◁{κ'} ty' +:: T) T
      (λ post '(b -:: al), post (f b -:: al)).
  Proof.
    move=> ??. eapply tctx_incl_eq; [|by apply subtype_tctx_incl_blocked].
    by move=> ?[??].
  Qed.

  Definition tctx_extract_ctx {𝔄l 𝔅l ℭl} E L (T: tctx 𝔄l)
    (T1: tctx 𝔅l) (T2: tctx ℭl) (tr: predl_trans 𝔅l (𝔄l ++ ℭl)) : Prop :=
    tctx_incl E L T1 (T h++ T2) tr.

  Lemma tctx_extract_ctx_nil {𝔄l} (T: _ 𝔄l) E L : tctx_extract_ctx E L +[] T T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_ctx_elt {𝔄 𝔄l 𝔅l ℭl 𝔇l}
    (t: _ 𝔄) (T: _ 𝔄l) (T1: _ 𝔅l) (T2: _ ℭl) (T3: _ 𝔇l) tr tr' E L :
    tctx_extract_elt E L t T1 T2 tr → tctx_extract_ctx E L T T2 T3 tr' →
    tctx_extract_ctx E L (t +:: T) T1 T3 (tr ∘ trans_tail tr').
  Proof. move=> ??. eapply tctx_incl_trans; by [|apply tctx_incl_tail]. Qed.

  Lemma tctx_extract_ctx_incl {𝔄l 𝔅l ℭl} (T: _ 𝔄l) (T': _ 𝔅l) (Tx: _ ℭl) tr E L :
    tctx_extract_ctx E L T' T Tx tr →
    tctx_incl E L T T' (λ post, tr (λ bcl, post (psepl bcl))).
  Proof.
    move=> Ex. eapply tctx_incl_eq; last first. { eapply tctx_incl_trans;
    [apply Ex|apply tctx_incl_leak_lower]. } done.
  Qed.

  (** Unblocking a type context. *)
  (* TODO : That would be great if this could also remove all the
     instances mentionning the lifetime in question.
     E.g., if [p ◁ &uniq{κ} ty] should be removed, because this is now
     useless. *)

  Class UnblockTctx {𝔄l} (E: elctx) (L: llctx) (κ: lft) (T T': tctx 𝔄l) : Prop :=
    unblock_tctx: ∀qL tid vπl, lft_ctx -∗ elctx_interp E -∗ llctx_interp L qL -∗
      [†κ] -∗ tctx_interp tid T vπl ={⊤}=∗ ∃d vπl', ⧖d ∗ |={⊤}▷=> |={⊤}▷=>^d |={⊤}=>
        llctx_interp L qL ∗ ⟨π, vπl -$ π = vπl' -$ π⟩ ∗ tctx_interp tid T' vπl'.

  Global Instance unblock_tctx_nil κ E L : UnblockTctx E L κ +[] +[].
  Proof.
    iIntros (??[]) "_ _ L _ _". iMod persist_time_rcpt_0. iExists 0, -[].
    iModIntro. iSplit; [done|]. iIntros "!>!>!>!>". iFrame "L".
    iSplit; [|done]. by iApply proph_obs_true.
  Qed.

  Global Instance unblock_tctx_cons_unblock {𝔄 𝔄l} p (ty: _ 𝔄) (T T': _ 𝔄l) κ E L :
    lctx_lft_alive E L ty.(ty_lft) → UnblockTctx E L κ T T' →
    UnblockTctx E L κ (p ◁{κ} ty +:: T) (p ◁ ty +:: T').
  Proof.
    iIntros (Alv Un ??[??]) "#LFT #E [L L'] #†κ /=[(%v &%& Upd) T]".
    iMod ("Upd" with "†κ") as (vπ' dp) "(Eqz & #timep & ty)".
    iMod (Un with "LFT E L †κ T") as (dT vπl') "[timeT >ToT']".
    iMod (Alv with "E L'") as (?) "[Tok ToL']"; [done|].
    iMod (ty_own_proph with "LFT [] ty Tok") as "Toty";
    [done|by iApply lft_incl_refl|]. iExists (dp `max` dT), (vπ' -:: vπl').
    rewrite persist_time_rcpt_sep. iFrame "timep timeT". iIntros "!>!>!>".
    iDestruct (step_fupdN_combine_max with "Toty ToT'") as "Big".
    iApply (step_fupdN_wand with "Big"). iIntros "[>(%&%&%& PTok & Toty) >($& Obs' &$)]".
    iMod ("Eqz" with "[] PTok") as "[Obs PTok]"; [done|].
    iMod ("Toty" with "PTok") as "[ty Tok]". iMod ("ToL'" with "Tok") as "$".
    iDestruct (proph_obs_and with "Obs Obs'") as "?". iModIntro. iSplit.
    { by iApply proph_obs_impl; [|done]=> ?[->->]. } iExists v, dp.
    iSplit; [done|]. by iFrame.
  Qed.

  Global Instance unblock_tctx_cons {𝔄 𝔄l} (t: _ 𝔄) (T T': _ 𝔄l) κ E L :
    UnblockTctx E L κ T T' → UnblockTctx E L κ (t +:: T) (t +:: T') | 100.
  Proof.
    iIntros (Un ??[vπ ?]) "LFT E L †κ [t T]".
    iMod (Un with "LFT E L †κ T") as (d vπl') "[time Upd]". iModIntro.
    iExists d, (vπ -:: vπl'). iFrame "time". iApply (step_fupdN_wand with "Upd").
    iIntros "!> >($&?&$) !>". iFrame "t". by iApply proph_obs_impl; [|done]=>/= ?->.
  Qed.

End lemmas.

Global Hint Resolve tctx_extract_elt_here_copy | 1 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here_exact | 2 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here tctx_extract_elt_here_blocked | 20 : lrust_typing.
Global Hint Resolve tctx_extract_elt_further | 50 : lrust_typing.
Global Hint Resolve tctx_extract_ctx_nil tctx_extract_ctx_elt
                    tctx_extract_ctx_incl : lrust_typing.
Global Hint Opaque tctx_extract_ctx tctx_extract_elt tctx_incl : lrust_typing.
