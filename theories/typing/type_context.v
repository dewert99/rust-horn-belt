From iris.proofmode Require Import tactics.
From lrust.typing Require Import type lft_contexts.
From lrust.util Require Import types.
Set Default Proof Using "Type".

Definition path := expr.
Bind Scope expr_scope with path.

(* TODO: Consider making this a pair of a path and the rest. We could
   then e.g. formulate tctx_elt_hasty_path more generally. *)
Inductive tctx_elt `{!typeG Σ} (A: Type) : Type :=
| TCtx_hasty (p: path) (ty: type A)
| TCtx_blocked (p: path) (κ: lft) (ty: type A).

Notation tctx := (hlist tctx_elt).

Notation "p ◁ ty" := (TCtx_hasty _ p ty%T) (at level 55).
Notation "p ◁{ κ } ty" := (TCtx_blocked _ p κ ty%T)
   (at level 55, format "p  ◁{ κ }  ty").

Definition pred A := A → Prop.
Definition predl As := pred (Π! As).
Definition predl_trans As Bs := predl Bs → predl As.

Definition trans_app {As Bs Cs Ds} (tr: predl_trans As Bs) (tr': predl_trans Cs Ds)
  : predl_trans (As ^++ Cs) (Bs ^++ Ds) :=
  λ post bdl, tr (λ al, tr' (λ cl, post (al -++ cl)) (psepr bdl)) (psepl bdl).

Definition trans_lower {As Bs Cs} (tr: predl_trans As Bs)
  : predl_trans (Cs ^++ As) (Cs ^++ Bs) :=
  λ post cal, tr (λ bl, post (psepl cal -++ bl)) (psepr cal).

Definition trans_upper {As Bs Cs} (tr: predl_trans As Bs)
  : predl_trans (As ^++ Cs) (Bs ^++ Cs) :=
  λ post acl, tr (λ bl, post (bl -++ psepr acl)) (psepl acl).

Definition trans_tail {A Bs Cs} (tr: predl_trans Bs Cs)
  : predl_trans (A ^:: Bs) (A ^:: Cs) :=
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
  Definition tctx_elt_interp {A} (tid: thread_id) (t: tctx_elt A) (vπ: proph A)
    : iProp Σ := match t with
    | p ◁ ty => ∃v d, ⌜eval_path p = Some v⌝ ∗ ⧖d ∗ ty.(ty_own) vπ d tid [v]
    | p ◁{κ} ty => ∃v, ⌜eval_path p = Some v⌝ ∗
        ([†κ] ={⊤}=∗ ∃vπ' d, ▷(vπ :== vπ') ∗ ⧖d ∗ ty.(ty_own) vπ' d tid [v]) end%I.

  (* Block tctx_elt_interp from reducing with simpl when t is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.

End type_context.

(** Type context *)
Notation tctx_interp tid :=
  (big_sepHL_1 (λ A t vπ, @tctx_elt_interp _ _ A tid t vπ)).

Section lemmas.
  Context `{!typeG Σ}.

  Lemma tctx_hasty_val {A} (v: val) (ty: _ A) vπ tid :
    tctx_elt_interp tid (v ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty.(ty_own) vπ d tid [v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (??) "(#EQ & ? & ?)".
      iDestruct "EQ" as %[=->]. eauto.
    - iDestruct 1 as (d) "[??]". eauto.
  Qed.

  Lemma tctx_elt_interp_hasty_path {A} p1 p2 (ty: _ A) tid vπ :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (p1 ◁ ty) vπ ≡ tctx_elt_interp tid (p2 ◁ ty) vπ.
  Proof. intros Hp. rewrite /tctx_elt_interp /=. setoid_rewrite Hp. done. Qed.

  Lemma tctx_hasty_val' {A} tid p v (ty: _ A) vπ:
    Some v = eval_path p →
    tctx_elt_interp tid (p ◁ ty) vπ ⊣⊢ ∃d, ⧖d ∗ ty.(ty_own) vπ d tid [v].
  Proof.
    move=> ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    by rewrite eval_path_of_val.
  Qed.

  Lemma wp_hasty {A} E tid p (ty : type A) vπ Φ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗
    (∀v d, ⌜Some v = eval_path p⌝ -∗ ⧖d -∗ ty.(ty_own) vπ d tid [v] -∗ Φ v) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iDestruct 1 as (???) "[#? ?]". iIntros "ToΦ". iApply (wp_wand with "[]");
    [by iApply wp_eval_path|]. iIntros (?) "->". by iApply "ToΦ".
  Qed.

  Lemma closed_hasty {A} tid p (ty: _ A) vπ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗ ⌜Closed [] p⌝.
  Proof. iDestruct 1 as (???) "(_ & _)". eauto using eval_path_closed. Qed.

  (** Copy typing contexts *)
  Class CopyC {As} (T: tctx As) :=
    copyc_persistent tid vπl : Persistent (tctx_interp tid T vπl).
  Global Existing Instances copyc_persistent.

  Global Instance tctx_nil_copy: CopyC +[].
  Proof. rewrite /CopyC. apply _. Qed.

  Global Instance tctx_cons_copy {A As} p (ty: _ A) (T: _ As) :
    Copy ty → CopyC T → CopyC (p ◁ ty +:: T).
  Proof. rewrite /CopyC=> ???[??]. apply _. Qed.

  (** Send typing contexts *)
  Class SendC {As} (T: tctx As) := sendc_change_tid tid1 tid2 vπl :
    tctx_interp tid1 T vπl ⊣⊢ tctx_interp tid2 T vπl.

  Global Instance tctx_nil_send: SendC +[].
  Proof. done. Qed.

  Global Instance tctx_cons_send {A As} p (ty: _ A) (T: _ As) :
    Send ty → SendC T → SendC (p ◁ ty +:: T).
  Proof.
    move=> Eq Eq' ??[??]/=. rewrite Eq' /tctx_elt_interp. do 7 f_equiv.
    by rewrite Eq.
  Qed.

  (** Type context inclusion *)
  Definition tctx_incl {As Bs} (E: elctx) (L: llctx) (T: tctx As) (T': tctx Bs)
    (tr: predl_trans As Bs) : Prop := ∀tid q vπl postπ,
      lft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
      tctx_interp tid T vπl -∗ ⟨π, tr (postπ π) (vπl -$ π)⟩ ={⊤}=∗ ∃vπl',
      llctx_interp L q ∗ ⟨π, postπ π (vπl' -$ π)⟩ ∗ tctx_interp tid T' vπl'.

  Lemma tctx_incl_impl {As Bs} (T: _ As) (T': _ Bs) (tr tr': _ → _ → Prop) E L :
    (∀post vl, tr post vl → tr' post vl) →
    tctx_incl E L T T' tr' → tctx_incl E L T T' tr.
  Proof.
    move=> Imp In. iIntros (????) "LFT PROPH UNIQ E L T #Obs".
    iMod (In with "LFT PROPH UNIQ E L T []") as "$"; [|done].
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma tctx_incl_eq {As Bs} (T: _ As) (T': _ Bs) tr tr' E L :
    (∀post vl, tr post vl = tr' post vl) →
    tctx_incl E L T T' tr' → tctx_incl E L T T' tr.
  Proof. move=> Eq. apply tctx_incl_impl=> ??. by rewrite Eq. Qed.

  Lemma tctx_incl_refl {As} (T: _ As) E L : tctx_incl E L T T id.
  Proof. move=> ?? vπl ?. iIntros. iExists vπl. by iFrame. Qed.

  Lemma tctx_incl_trans {As Bs Cs} (T1: _ As) (T2: _ Bs) (T3: _ Cs) tr tr' E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L T2 T3 tr' → tctx_incl E L T1 T3 (tr ∘ tr').
  Proof.
    move=> In In' >. iIntros "#LFT #PROPH #UNIQ #E L T Obs".
    iMod (In with "LFT PROPH UNIQ E L T Obs") as (?) "(L & Obs & T)".
    iMod (In' with "LFT PROPH UNIQ E L T Obs") as (vπl'') "(?&?&?)".
    iExists vπl''. by iFrame.
  Qed.

  Lemma tctx_incl_app {As Bs Cs Ds}
    (T1: _ As) (T1': _ Bs) (T2: _ Cs) (T2': _ Ds) tr tr' E L :
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

  Lemma tctx_incl_frame_l {As Bs Cs} (T: _ As) (T': _ Bs) (Tf: _ Cs) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (Tf h++ T) (Tf h++ T') (trans_lower tr).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first.
    { apply tctx_incl_app=>//. apply tctx_incl_refl. } done.
  Qed.
  Lemma tctx_incl_frame_r {As Bs Cs} (T: _ As) (T': _ Bs) (Tf: _ Cs) tr E L :
    tctx_incl E L T T' tr → tctx_incl E L (T h++ Tf) (T' h++ Tf) (trans_upper tr).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first.
    { apply tctx_incl_app=>//. apply tctx_incl_refl. } done.
  Qed.
  Lemma tctx_incl_tail {A As Bs} (t: _ A) (T1: _ As) (T2: _ Bs) tr E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L (t +:: T1) (t +:: T2) (trans_tail tr).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first.
    { by apply (tctx_incl_frame_l _ _ +[_]). } by move=> ?[??].
  Qed.

  Lemma tctx_incl_swap {A B As} (t: _ A) (t': _ B) (T: _ As) E L :
    tctx_incl E L (t +:: t' +:: T) (t' +:: t +:: T)
      (λ post '(a -:: b -:: al), post (b -:: a -:: al)).
  Proof.
    iIntros (??(vπ & vπ' & wπl)?) "_ _ _ _ $ (?&?&?) ?!>".
    iExists (vπ' -:: vπ -:: wπl). iFrame.
  Qed.

  Lemma tctx_incl_leak_lower {As Bs} (T: _ As) (T': _ Bs) E L :
    tctx_incl E L (T h++ T') T (λ post abl, post (psepl abl)).
  Proof.
    move=> ?? abπl ?. move: (papp_ex abπl)=> [aπl[?->]].
    iIntros "_ _ _ _ $ [T _] ? !>". iExists aπl. iFrame "T".
    iApply proph_obs_eq; [|done]=> ?. by rewrite/= papply_app papp_sepl.
  Qed.

  Lemma copy_tctx_incl {A As} (ty: _ A) `{!Copy ty} (T: _ As) p E L :
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty +:: p ◁ ty +:: T)
      (λ post '(a -:: al), post (a -:: a -:: al)).
  Proof.
    iIntros (??[vπ wπl]?) "_ _ _ _ $ /=[#? T] Obs !>".
    iExists (vπ -:: vπ -:: wπl). iFrame "Obs T". by iSplit.
  Qed.

  Lemma subtype_tctx_incl {A B As} ty ty' (f: A → B) (T: _ As) p E L :
    subtype E L f ty ty' →
    tctx_incl E L (p ◁ ty +:: T) (p ◁ ty' +:: T)
      (λ post '(a -:: al), post (f a -:: al)).
  Proof.
    iIntros (Sub ??[vπ wπl]?) "#LFT _ _ E L /=[(%v & %d &%&?& ty) T] Obs /=".
    iDestruct (Sub with "L E") as "#(_ & _ & #InOwn & _)". iModIntro.
    iExists (f ∘ vπ -:: wπl). iFrame "L Obs T". iExists v, d.
    do 2 (iSplit; [done|]). by iApply "InOwn".
  Qed.

  Lemma subtype_tctx_incl_blocked {A B As} ty ty' `{@Inj A B (=) (=) f}
    κ κ' (T: _ As) p E L :
    subtype E L f ty ty' → lctx_lft_incl E L κ κ' →
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

  Definition tctx_extract_elt {A As Bs} E L (t: tctx_elt A)
    (T: tctx As) (T': tctx Bs) (tr: predl_trans As (A ^:: Bs)) : Prop :=
    tctx_incl E L T (t +:: T') tr.

  Lemma tctx_extract_elt_further {A B As Bs}
    (t: _ A) (t': _ B) (T: _ As) (T': _ Bs) tr E L :
    tctx_extract_elt E L t T T' tr →
    tctx_extract_elt E L t (t' +:: T) (t' +:: T')
      (λ post '(b -:: al), tr (λ '(a -:: bl), post (a -:: b -:: bl)) al).
  Proof.
    move=> ?. eapply tctx_incl_eq; last first. { eapply tctx_incl_trans;
    by [eapply tctx_incl_tail|apply tctx_incl_swap]. } move=> ?[??]/=. f_equal.
  Qed.

  Lemma tctx_extract_elt_here_copy {A B As} ty ty' (f: A → B) (T: _ As) p p' E L :
    p = p' → Copy ty' → subtype E L f ty' ty →
    tctx_extract_elt E L (p ◁ ty) (p' ◁ ty' +:: T) (p' ◁ ty' +:: T)
      (λ post '(b -:: al), post (f b -:: b -:: al)).
  Proof.
    move=> ->??. eapply tctx_incl_eq; last first. { eapply tctx_incl_trans;
    by [apply copy_tctx_incl|apply subtype_tctx_incl]. } by move=> ?[??].
  Qed.

  Lemma tctx_extract_elt_here_exact {A As} (ty: _ A) (T: _ As) p p' E L :
    p = p' → tctx_extract_elt E L (p ◁ ty) (p' ◁ ty +:: T) T id.
  Proof. move=> ->. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_elt_here {A B As} ty ty' (f: B → A) (T: _ As) p p' E L :
    p = p' → subtype E L f ty' ty →
    tctx_extract_elt E L (p ◁ ty) (p' ◁ ty' +:: T) T
      (λ post '(b -:: al), post (f b -:: al)).
  Proof.
    move=> ->?. eapply tctx_incl_eq; [|by apply subtype_tctx_incl].
    by move=> ?[??].
  Qed.

  Definition tctx_extract_ctx {As Bs Cs} E L (T: tctx As)
    (T1: tctx Bs) (T2: tctx Cs) (tr: predl_trans Bs (As ^++ Cs)) : Prop :=
    tctx_incl E L T1 (T h++ T2) tr.

  Lemma tctx_extract_ctx_nil {As} (T: _ As) E L : tctx_extract_ctx E L +[] T T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_ctx_elt {A As Bs Cs Ds}
    (t: _ A) (T: _ As) (T1: _ Bs) (T2: _ Cs) (T3: _ Ds) tr tr' E L :
    tctx_extract_elt E L t T1 T2 tr → tctx_extract_ctx E L T T2 T3 tr' →
    tctx_extract_ctx E L (t +:: T) T1 T3 (tr ∘ trans_tail tr').
  Proof. move=> ??. eapply tctx_incl_trans; by [|apply tctx_incl_tail]. Qed.

  Lemma tctx_extract_ctx_incl {As Bs Cs} (T: _ As) (T': _ Bs) (Tx: _ Cs) tr E L :
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

  Class UnblockTctx {As} (κ: lft) (T T': tctx As) : Prop := unblock_tctx:
    ∀tid vπl, [†κ] -∗ tctx_interp tid T vπl ={⊤}=∗ ∃vπl',
      ([∗ plist] vπ; vπ' ∈ vπl; vπl', ▷(vπ :== vπ')) ∗ tctx_interp tid T' vπl'.

  Global Instance unblock_tctx_nil κ : UnblockTctx κ +[] +[].
  Proof. move=> ??. by iIntros. Qed.

  Global Instance unblock_tctx_cons_unblock {A As} (ty: _ A) (T T': _ As) p κ :
    UnblockTctx κ T T' → UnblockTctx κ (p ◁{κ} ty +:: T) (p ◁ ty +:: T').
  Proof.
    move=> Un ?/=[??]. iIntros "#†κ [(%v &%& Upd) T]".
    iMod ("Upd" with "†κ") as (vπ' d) "(Eqz &?&?)".
    iMod (Un with "†κ T") as (vπl') "[Eqzs T']". iModIntro.
    iExists (vπ' -:: vπl'). iFrame "Eqz Eqzs T'". iExists v, d. by iFrame.
  Qed.

  Global Instance unblock_tctx_cons {A As} (t: _ A) (T T': _ As) κ :
    UnblockTctx κ T T' → UnblockTctx κ (t +:: T) (t +:: T') | 100.
  Proof.
    move=> Un ?/=[vπ ?]. iIntros "†κ [t T]".
    iMod (Un with "†κ T") as (vπl') "[Eqzs T']". iModIntro.
    iExists (vπ -:: vπl'). iFrame "Eqzs t T'". iApply proph_eqz_eq.
  Qed.

End lemmas.

Global Hint Resolve tctx_extract_elt_here_copy | 1 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here_exact | 2 : lrust_typing.
Global Hint Resolve tctx_extract_elt_here | 20 : lrust_typing.
Global Hint Resolve tctx_extract_elt_further | 50 : lrust_typing.
Global Hint Resolve tctx_extract_ctx_nil tctx_extract_ctx_elt
                    tctx_extract_ctx_incl : lrust_typing.
Global Hint Opaque tctx_extract_ctx tctx_extract_elt tctx_incl : lrust_typing.
