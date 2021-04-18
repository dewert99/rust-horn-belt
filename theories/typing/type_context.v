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

Notation pred As := (Π! As → Prop).
Notation pred_trans As Bs := (pred Bs → pred As).

Definition trans_app {As Bs Cs Ds} (tr: pred_trans As Bs) (tr': pred_trans Cs Ds)
  : pred_trans (As ^++ Cs) (Bs ^++ Ds) :=
  λ post bd, tr (λ a, tr' (λ c, post (a -++ c)) (psepr bd)) (psepl bd).

Definition trans_tail {A Bs Cs} (tr: pred_trans Bs Cs)
  : pred_trans (A ^:: Bs) (A ^:: Cs) :=
  λ post '(a -:: cl), tr (λ bl, post (a -:: bl)) cl.

Definition trans_upper {As Bs Cs} (tr: pred_trans As Bs)
  : pred_trans (As ^++ Cs) (Bs ^++ Cs) :=
  λ post ac, tr (λ b, post (b -++ psepr ac)) (psepl ac).

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
        ([†κ] ={⊤}=∗ ∃vπ' d, ▷(vπ :== vπ') ∗ ⧖d ∗ ty.(ty_own) vπ d tid [v]) end%I.

  (* Block tctx_elt_interp from reducing with simpl when t is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.

  Lemma tctx_hasty_val {A} tid (v: val) (ty: _ A) vπ:
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
    eval_path p = Some v →
    tctx_elt_interp tid (p ◁ ty) vπ ⊣⊢ ∃ depth, ⧖depth ∗ ty.(ty_own) vπ depth tid [v].
  Proof.
    intros ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    rewrite eval_path_of_val. done.
  Qed.

  Lemma wp_hasty {A} E tid p (ty : type A) vπ Φ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗
    (∀v d, ⧖d -∗ ty.(ty_own) vπ d tid [v] -∗ Φ v) -∗ WP p @ E {{ Φ }}.
  Proof.
    iDestruct 1 as (???) "[#? ?]". iIntros "ToΦ".
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (?) "->". by iApply "ToΦ".
  Qed.

  Lemma closed_hasty {A} tid p (ty: _ A) vπ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗ ⌜Closed [] p⌝.
  Proof. iDestruct 1 as (???) "(_ & _)". eauto using eval_path_closed. Qed.

  (** Type context *)
  Definition tctx_interp {As} (tid: thread_id) (T: tctx As) (vπl: plist proph As)
    : iProp Σ := [∗ hlist] t;- vπ ∈ T;- vπl, tctx_elt_interp tid t vπ.

  Lemma tctx_interp_singleton {A} tid (t: _ A) vπ :
    tctx_interp tid +[t] -[vπ] ⊣⊢ tctx_elt_interp tid t vπ.
  Proof. by rewrite /tctx_interp big_sepHL_1_singleton. Qed.

  Lemma tctx_interp_cons {A As} tid (t: _ A) (T: _ As) vπ vπl :
    tctx_interp tid (t +:: T) (vπ -:: vπl) ⊣⊢
    tctx_elt_interp tid t vπ ∗ tctx_interp tid T vπl.
  Proof. done. Qed.

  Lemma tctx_interp_app {As Bs} tid (T: _ As) (T': _ Bs) vπl vπl' :
    tctx_interp tid (T h++ T') (vπl -++ vπl') ⊣⊢
    tctx_interp tid T vπl ∗ tctx_interp tid T' vπl'.
  Proof. by rewrite /tctx_interp big_sepHL_1_app. Qed.

  (** Copy typing contexts *)
  Class CopyC {As} (T : tctx As) vπl :=
    copyc_persistent tid : Persistent (tctx_interp tid T vπl).
  Global Existing Instances copyc_persistent.

  Global Instance tctx_nil_copy : CopyC +[] -[].
  Proof. rewrite /CopyC. apply _. Qed.

  Global Instance tctx_ty_copy {A As} (T: _ As) vπl p (ty: _ A) vπ :
    CopyC T vπl → Copy ty → CopyC (p ◁ ty +:: T) (vπ -:: vπl).
  Proof. rewrite /CopyC=> *. rewrite tctx_interp_cons. apply _. Qed.

  (** Send typing contexts *)
  Class SendC {As} (T: tctx As) vπl :=
    sendc_change_tid tid1 tid2 : tctx_interp tid1 T vπl ⊣⊢ tctx_interp tid2 T vπl.

  Global Instance tctx_nil_send : SendC +[] -[].
  Proof. done. Qed.

  Global Instance tctx_ty_send {A As} (T : tctx As) vπl p (ty : type A) vπ :
    SendC T vπl → Send ty → SendC (p ◁ ty +:: T) (vπ -:: vπl).
  Proof.
    move=> Eq Eq' >. rewrite !tctx_interp_cons Eq. f_equiv.
    rewrite /tctx_elt_interp. do 6 f_equiv. by rewrite Eq'.
  Qed.

  (** Type context inclusion *)
  Definition tctx_incl {As Bs} (E: elctx) (L: llctx) (T: tctx As) (T': tctx Bs)
    (tr: pred_trans As Bs) : Prop :=
    ∀tid q vπl post, lft_ctx -∗ elctx_interp E -∗ llctx_interp L q -∗
      tctx_interp tid T vπl -∗ ⟨π, tr (post π) (vπl -$ π)⟩ ={⊤}=∗ ∃vπl',
      llctx_interp L q ∗ ⟨π, post π (vπl' -$ π)⟩ ∗ tctx_interp tid T' vπl'.
  (* Global Instance : ∀ A E L f, RewriteRelation (@tctx_incl A A E L f) := {}. *)

  (* Global Instance tctx_incl_preorder A E L : PreOrder (@tctx_incl A A E L).
  Proof.
    split.
    - by iIntros (???) "_ _ $ $".
    - rewrite /Transitive. iIntros (??? H1 H2 ??) "#LFT #HE HL H".
      iMod (H1 with "LFT HE HL H") as "(HL & H)".
      by iMod (H2 with "LFT HE HL H") as "($ & $)".
  Qed. *)

  Lemma tctx_incl_impl {As Bs} (T: _ As) (T': _ Bs) (tr tr': _ → _ → Prop) E L :
    (∀post vl, tr post vl → tr' post vl) →
    tctx_incl E L T T' tr' → tctx_incl E L T T' tr.
  Proof.
    move=> Imp In. iIntros (????) "#LFT E L T #Obs".
    iMod (In with "LFT E L T []") as "$"; [|done].
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma tctx_incl_refl {As} (T: _ As) E L : tctx_incl E L T T id.
  Proof. move=> ?? vπl ?. iIntros. iExists vπl. by iFrame. Qed.

  Lemma tctx_incl_trans {As Bs Cs} (T1: _ As) (T2: _ Bs) (T3: _ Cs) tr tr' E L :
    tctx_incl E L T1 T2 tr → tctx_incl E L T2 T3 tr' → tctx_incl E L T1 T3 (tr ∘ tr').
  Proof.
    move=> In In' >. iIntros "#LFT #E L T Obs".
    iMod (In with "LFT E L T Obs") as (?) "(L & Obs & T)".
    iMod (In' with "LFT E L T Obs") as (vπl'') "(?&?&?)". iExists vπl''. by iFrame.
  Qed.

(*
  Definition xprod_hsubmseteq {As Bs} {T1 : tctx As} {T2 : tctx Bs} (sub : T1 ⊆+ₕ T2) : Π! Bs → Π! As.
    intros. dependent induction sub; simpl in *; intuition.
  Qed. *)

  (* Lemma contains_tctx_incl {As Bs} E L (T1 : tctx As) (T2 : tctx Bs) (s : T1 ⊆+ₕ T2) : tctx_incl E L T2 T1 (xprod_hsubmseteq s).
  Proof.
    rewrite /tctx_incl. iIntros (??) "_ _ $ H". by iApply big_sepHL_submseteq.
  Qed. *)

  Lemma tctx_incl_app {As Bs Cs Ds}
    (T1: _ As) (T1': _ Bs) (T2: _ Cs) (T2': _ Ds) tr tr' E L :
    tctx_incl E L T1 T1' tr → tctx_incl E L T2 T2' tr' →
    tctx_incl E L (T1 h++ T2) (T1' h++ T2') (trans_app tr tr').
  Proof.
    move=> Hincl1 Hincl2 ?? vπl ?. move: (papp_ex vπl)=> [?[?->]].
    rewrite /tctx_incl tctx_interp_app.
    iIntros "#LFT #HE HL [H1 H2] HP".
    iMod (Hincl1 with "LFT HE HL H1 [HP]")  as (wπl) "(HL & Hp1 & ?)".
    { iApply proph_obs_impl; [|done]=> ?.
      rewrite /trans_app papply_app papp_sepl papp_sepr. exact id. }
    iMod (Hincl2 with "LFT HE HL H2 [Hp1]") as (wπl') "(HL & Hp2 & ?)".
    { iApply proph_obs_impl; [|done]=> ?. exact id. }
    iExists (wπl -++ wπl'). rewrite tctx_interp_app. iFrame.
    iApply proph_obs_impl; [|done]=>/= ?. rewrite papply_app. exact id.
  Qed.

  (* Lemma tctx_incl_frame_l {E L As Bs Cs} (T :tctx As) (T1 : tctx Bs) (T2 : tctx Cs) f:
    tctx_incl E L T1 T2 f → tctx_incl E L (T +++ T1) (T +++ T2) (xprod_bimap id f).
  Proof. apply tctx_incl_app, tctx_incl_refl. Qed.

  Lemma tctx_incl_frame_r {E L As Bs Cs} (T : tctx As) (T1 : tctx Bs) (T2 : tctx Cs) f :
    tctx_incl E L T1 T2 f → tctx_incl E L (T1+++T) (T2+++T) (xprod_bimap f id).
  Proof.  intros. by apply tctx_incl_app, tctx_incl_refl. Qed.
  *)

  Lemma tctx_incl_tail {A As Bs} E L (t: _ A) (T1: _ As) (T2: _ Bs) tr :
    tctx_incl E L T1 T2 tr → tctx_incl E L (t +:: T1) (t +:: T2) (trans_tail tr).
  Proof.
    move=> ?. eapply tctx_incl_impl; last first.
    { apply (tctx_incl_app +[_] +[_]); [apply tctx_incl_refl|done]. }
    move=> ?[??]. exact id.
  Qed.

  (*
  Lemma copy_tctx_incl {A} E L p vπ `{!Copy (ty : type A)} :
    tctx_incl E L +[p ◁ ty] +[p ◁ ty; p ◁ ty] (λ x, xprod_merge x x).
  Proof. iIntros (??) "_ _ $ * [#$ $] //". Qed. *)

(*
  Lemma copy_elem_of_tctx_incl E L A As (T : tctx As) p `{!Copy (ty : type A)} :
    p ◁ ty ∈ T → tctx_incl E L T ((p ◁ ty) +:: T).
  Proof.
  Qed. *)

  (* Lemma subtype_tctx_incl A B E L (f : A → B) p (ty1 : type A) (ty2 : type B)  :
    subtype E L f ty1 ty2 → tctx_incl E L +[p ◁ ty1] +[p ◁ ty2 [{ f ∘  }]] (xprod_singleton f).
  Proof.
    iIntros (Hst ??) "#LFT #HE HL [H _]".
    iDestruct "H" as (v depth) "(? & % & H)".
    iDestruct (Hst with "HL HE") as "#(_ & _ & Ho & _)". iFrame "HL".
    iApply big_sepHL_singleton. iExists _, _.
    iFrame "%∗". by iApply "Ho".
  Qed. *)

  (* Extracting from a type context. *)

  Definition tctx_extract_hasty {As Bs A} E L p (ty: type A)
    (T: tctx As) (T': tctx Bs) (tr: pred_trans As (A ^:: Bs)) : Prop :=
    tctx_incl E L T (p ◁ ty +:: T') tr.

  Definition xprod_extract {As A B Bs} (f : Π! As → Π! (B ^:: Bs)) : Π! (A ^:: As) → Π! (B ^:: A ^:: Bs) :=
    λ '(a -:: ass), let '(b -:: bss) := f ass in b -:: a -:: bss.

  (* Lemma tctx_extract_hasty_further {As Bs A B} E L p (ty : type B)  (T : tctx As) (T' : tctx Bs) f (x : tctx_elt A) :
    tctx_extract_hasty E L p ty  T T' f →
    tctx_extract_hasty E L p ty  (x+::T) (x+::T') (xprod_extract f).
  Proof.
    rewrite /tctx_extract_hasty.
    intros.
    eapply tctx_incl_trans;
      [eapply tcx_incl_cons, H| apply contains_tctx_incl].

    Unshelve.
    constructor.
  Qed. *)

  (* Lemma tctx_extract_hasty_here_copy {A B As} E L f p1 p2 (ty : type A)  (ty' : type B)  (T : tctx As) :
    p1 = p2 → Copy ty → subtype E L f ty ty' →
    tctx_extract_hasty E L p1 ty' (f ∘ ) ((p2 ◁ ty)+::T) ((p2 ◁ ty [{ }])+::T) (λ p, (f p.1, p)).
  Proof.
    intros -> ??. apply (tctx_incl_frame_r _ +[_] +[_;_] (λ p, (f p.1, p))).
    eapply tctx_incl_trans; first by apply copy_tctx_incl, _.
    by apply (tctx_incl_frame_r _ +[_] +[_]), (subtype_tctx_incl _ _ _ _ f).
  Qed.

  Lemma tctx_extract_hasty_here {A B As} E L f p1 p2 (ty : type A)  (ty' : type B) (T : tctx As) :
    p1 = p2 → subtype E L f ty ty' → tctx_extract_hasty E L p1 ty' (f ∘ ) ((p2 ◁ ty)+::T) T  (λ p, (f p.1, p.2)).
  Proof.
    intros -> ?. by apply (tctx_incl_frame_r _ +[_] +[_] (λ p, (f p.1, p.2))), (subtype_tctx_incl _ _ _ _ f).
  Qed.

  Lemma tctx_extract_hasty_here_eq {A As} E L p1 p2 (ty : type A)  (T : tctx As) :
    p1 = p2 → tctx_extract_hasty E L p1 ty  ((p2 ◁ ty)+::T) T id.
  Proof. intros ->. by eapply (tctx_extract_hasty_here _ _ id), subtype_refl. Qed. *)
(*
  Definition tctx_extract_blocked {A As Bs} E L p κ (ty : type A)  (T : tctx As) (T' : tctx Bs) f : Prop :=
    tctx_incl E L T ((p ◁{κ} ty)+::T') (λ A,  +:: f). *)

  (* Lemma tctx_extract_blocked_cons {A B As Bs} E L p κ (ty : type B)  (T : tctx As) (T' : tctx Bs) (x : tctx_elt A) f :
    tctx_extract_blocked E L p κ ty  T T' f →
    tctx_extract_blocked E L p κ ty  (x+::T) (x+::T') (xprod_extract f).
  Proof.
    rewrite /tctx_extract_blocked.
    intros.
    eapply tctx_incl_trans;
      [eapply tcx_incl_cons, H| apply contains_tctx_incl].

    Unshelve.
    constructor.
  Qed. *)

  (* Lemma tctx_extract_blocked_here {A As} E L p κ (ty : type A)  (T : tctx As) f:
    tctx_extract_blocked E L p κ ty  ((p ◁{κ} ty)+::T) T f.
  Proof. intros. apply (tctx_incl_frame_r _ +[_] +[_] id), tctx_incl_refl. Qed. *)

  Definition tctx_extract_ctx {As Bs Cs} E L (T: tctx As)
    (T1: tctx Bs) (T2: tctx Cs) (tr: pred_trans Bs (As ^++ Cs)) : Prop :=
    tctx_incl E L T1 (T h++ T2) tr.

  Lemma tctx_extract_ctx_nil {As} (T: _ As) E L : tctx_extract_ctx E L +[] T T id.
  Proof. apply tctx_incl_refl. Qed.

  Lemma tctx_extract_ctx_hasty {A As Bs Cs Ds}
    (ty: _ A) (T: _ As) (T1: _ Bs) (T2: _ Cs) (T3: _ Ds) p tr tr' E L :
    tctx_extract_hasty E L p ty T1 T2 tr → tctx_extract_ctx E L T T2 T3 tr' →
    tctx_extract_ctx E L (p ◁ ty +:: T) T1 T3 (tr ∘ trans_tail tr').
  Proof. move=> ??. eapply tctx_incl_trans; by [|apply tctx_incl_tail]. Qed.

  (*
  Lemma tctx_extract_ctx_blocked {A As Bs Cs Ds} E L (T : tctx As) (T1 : tctx Bs) (T2 : tctx Cs) (T3 : tctx Ds) p κ (ty : type A) :
    tctx_extract_blocked E L p κ ty  T1 T2 → tctx_extract_ctx E L T T2 T3 →
    tctx_extract_ctx E L ((p ◁{κ} ty)+::T) T1 T3.
  Proof. unfold tctx_extract_ctx, tctx_extract_blocked => ?? //.
    eapply tctx_incl_trans, tcx_incl_cons; eassumption.
  Qed.

  Lemma tctx_extract_ctx_incl {As Bs Cs} E L (T : tctx As) (T' : tctx Bs) (T0 : tctx Cs):
    tctx_extract_ctx E L T' T T0 →
    tctx_incl E L T T'.
  Proof.
    unfold tctx_extract_ctx=> ?.
    eapply tctx_incl_trans; first eassumption.
    apply contains_tctx_incl, hsubmseteq_inserts_r, hpermutation_hsubmseteq, hpermutation_refl.
  Qed. *)

  (* Unblocking a type context. *)
  (* TODO : That would be great if this could also remove all the
     instances mentionning the lifetime in question.
     E.g., if [p ◁ &uniq{κ} ty] should be removed, because this is now
     useless. *)

  (* Class UnblockTctx (κ : lft) (A : Types) (T1 T2 : tctx A) : Prop :=
    unblock_tctx : ∀ tid, [†κ] -∗ tctx_interp tid T1 ={⊤}=∗ tctx_interp tid T2.

  Global Instance unblock_tctx_nil κ : UnblockTctx κ _ +[] +[].
  Proof. by iIntros (tid) "_ $". Qed.

  Global Instance unblock_tctx_cons_unblock A As (T1 T2 : tctx As) p κ (ty : type A) :
    UnblockTctx κ _ T1 T2 →
    UnblockTctx κ _ ((p ◁{κ} ty) +:: T1) ((p ◁ ty) +:: T2).
  Proof.
    iIntros (H12 tid) "#H†". rewrite !tctx_interp_cons. iIntros "[H HT1]".
    iMod (H12 with "H† HT1") as "$". iDestruct "H" as (v) "[% H]".
    iMod ("H" with "H†") as (depth) "[??]". iExists v, depth. auto.
  Qed.

  Global Instance unblock_tctx_cons κ A As (T1 T2 : tctx As) (x : tctx_elt A) :
    UnblockTctx κ _ T1 T2 → UnblockTctx κ _ (x +:: T1) (x +:: T2) | 100.
  Proof.
    iIntros (H12 tid) "#H†". rewrite !tctx_interp_cons. iIntros "[$ HT1]".
    by iMod (H12 with "H† HT1") as "$".
  Qed.  *)
End type_context.

(* Global Hint Resolve tctx_extract_hasty_here_copy | 1 : lrust_typing.
Global Hint Resolve tctx_extract_hasty_here | 20 : lrust_typing.
Global Hint Resolve tctx_extract_hasty_further | 50 : lrust_typing. *)
Global Hint Resolve (* tctx_extract_blocked_here tctx_extract_blocked_cons *)
             tctx_extract_ctx_nil tctx_extract_ctx_hasty
             (* tctx_extract_ctx_blocked tctx_extract_ctx_incl *) : lrust_typing.
Global Hint Opaque tctx_extract_ctx (* tctx_extract_hasty tctx_extract_blocked *)
            tctx_incl : lrust_typing.

(* In general, we want reborrowing to be tried before subtyping, so
   that we get the extraction. However, in the case the types match
   exactly, we want to NOT use reborrowing. Therefore, we add
   [tctx_extract_hasty_here_eq] as a hint with a very low cost. *)
(* Global Hint Resolve tctx_extract_hasty_here_eq | 2 : lrust_typing. *)
