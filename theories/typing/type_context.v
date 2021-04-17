From iris.proofmode Require Import tactics.
From lrust.typing Require Import type lft_contexts.
From lrust.util Require Import types.
Require Import Coq.Program.Equality.


Set Default Proof Using "Type".

Definition path := expr.
Bind Scope expr_scope with path.

(* TODO: Consider making this a pair of a path and the rest. We could
   then e.g. formulate tctx_elt_hasty_path more generally. *)
Inductive tctx_elt `{!typeG Σ} (A : Type) : Type :=
| TCtx_hasty  (p : path) (ty : type A)
| TCtx_blocked (p : path) (κ : lft) (ty : type A). 

Notation tctx := (hlist tctx_elt).

Notation "p ◁ ty" := (TCtx_hasty _ p ty%list%T) (at level 70).
Notation "p ◁{ κ } ty" := (TCtx_blocked _ p κ ty)
   (at level 70, format "p  ◁{ κ }  ty").

Section type_context.
  Context `{!typeG Σ}.

  Fixpoint eval_path (p : path) : option val :=
    match p with
    | BinOp OffsetOp e (Lit (LitInt n)) =>
      match eval_path e with
      | Some (#(LitLoc l)) => Some (#(l +ₗ n))
      | _ => None
      end
    | e => to_val e
    end.

  Lemma eval_path_of_val (v : val) :
    eval_path v = Some v.
  Proof. destruct v. done. simpl. rewrite (decide_left _). done. Qed.

  Lemma wp_eval_path E p v :
    eval_path p = Some v → ⊢ WP p @ E {{ v', ⌜v' = v⌝ }}.
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

  Lemma eval_path_closed p v :
    eval_path p = Some v → Closed [] p.
  Proof.
    intros Hpv. revert v Hpv.
    induction p as [| | |[] p IH [|[]| | | | | | | | | |] _| | | | | | | |]=>//.
    - unfold eval_path=>? /of_to_val <-. apply is_closed_of_val.
    - simpl. destruct (eval_path p) as [[[]|]|]; intros ? [= <-].
      specialize (IH _ eq_refl). apply _.
  Qed.

  (** Type context element *)
  (* TODO(xavier): Add prophecy equalizer *)
  Definition tctx_elt_interp {A} (tid : thread_id) (x : tctx_elt A) (vπ : proph_asn → A): iProp Σ :=
      match x with
      | p ◁ ty =>
        ∃ v depth, ⧖depth ∗ ⌜eval_path p = Some v⌝ ∗ ty.(ty_own) vπ depth tid [v]
      | p ◁{κ} ty => ∃ v, ⌜eval_path p = Some v⌝ ∗
                  ([†κ] ={⊤}=∗ ∃ depth, ⧖depth ∗ ty.(ty_own) vπ depth tid [v])
      end%I.

  (* Block tctx_elt_interp from reducing with simpl when x is a constructor. *)
  Global Arguments tctx_elt_interp : simpl never.

  Lemma tctx_hasty_val {A} tid (v : val) (ty : type A) vπ:
    tctx_elt_interp tid (v ◁ ty) vπ ⊣⊢ ∃ depth, ⧖depth ∗ ty.(ty_own) vπ depth tid [v].
  Proof.
    rewrite /tctx_elt_interp eval_path_of_val. iSplit.
    - iIntros "H". iDestruct "H" as (??) "(#Ht & EQ & ?)".
      iDestruct "EQ" as %[=->]. eauto.
    - iDestruct 1 as (depth) "[??]". eauto.
  Qed.

  Lemma tctx_elt_interp_hasty_path {A} p1 p2 (ty : type A) tid vπ :
    eval_path p1 = eval_path p2 →
    tctx_elt_interp tid (p1 ◁ ty) vπ ≡ tctx_elt_interp tid (p2 ◁ ty) vπ.
  Proof. intros Hp. rewrite /tctx_elt_interp /=. setoid_rewrite Hp. done. Qed.

  Lemma tctx_hasty_val' {A} tid p (v : val) (ty : type A) vπ:
    eval_path p = Some v →
    tctx_elt_interp tid (p ◁ ty) vπ ⊣⊢ ∃ depth, ⧖depth ∗ ty.(ty_own) vπ depth tid [v].
  Proof.
    intros ?. rewrite -tctx_hasty_val. apply tctx_elt_interp_hasty_path.
    rewrite eval_path_of_val. done.
  Qed.

  Lemma wp_hasty {A} E tid p (ty : type A) vπ Φ :
    tctx_elt_interp tid (p ◁ ty) vπ -∗
    (∀ depth v, ⧖depth -∗ ⌜eval_path p = Some v⌝ -∗ ty.(ty_own) vπ depth tid [v] -∗ Φ v) -∗
    WP p @ E {{ Φ }}.
  Proof.
    iIntros "Hty HΦ". iDestruct "Hty" as (v depth) "(Hdepth & % & Hown)".
    iApply (wp_wand with "[]"). { iApply wp_eval_path. done. }
    iIntros (v') "%". subst v'. by iApply ("HΦ" with "Hdepth [] Hown").
  Qed.

  Lemma closed_hasty {A} tid p (ty : type A) vπ : tctx_elt_interp tid (p ◁ ty) vπ -∗ ⌜Closed [] p⌝.
  Proof. iDestruct 1 as (??) "(_ & % & _)". eauto using eval_path_closed. Qed.

  (* Fixpoint hzip {F G A B} (x : hlist F A) (y : hlist G B) : hlist (λ ) _. *)
  (** Type context *)
  Definition tctx_interp {As} (tid : thread_id) (T : tctx As) (Vs : hlist (λ A, proph_asn → A) As) : iProp Σ :=
    big_sepHLZip' (λ A x v, tctx_elt_interp tid x v) T Vs.
  
  Fixpoint tctx_values {A} π (V : hlist (λ T, proph_asn → T) A) : xprod A :=
    match V in hlist _ A return xprod A with 
    | x +:: V => x π -:: tctx_values π V
    | +[] => -[]
    end.

  Lemma tctx_values_distr {T1 T2} (V1 : hlist _ T1) (V2 : hlist _ T2) π : 
    tctx_values π (V1 h++ V2) = tctx_values π V1 -++ tctx_values π V2.
  Proof. elim V1 => [//| /= ???? -> //]. Qed.

  Lemma tctx_values_split_l {A B} (V1 : hlist _ A) (V2 : hlist _ B) π : 
    xprod_split_l (tctx_values π (V1 h++ V2)) = tctx_values π V1.
  Proof. elim/hlist_ind: V1 => [ //| ???? /= -> //=]. Qed.

  Lemma tctx_values_split_r {A B} (V1 : hlist _ A) (V2 : hlist _ B) π : 
    xprod_split_r (tctx_values π (V1 h++ V2)) = tctx_values π V2.
  Proof. elim/hlist_ind: V1 => [ //| ???? /= -> //=]. Qed.

  Lemma tctx_values_split {A B} (V1 : hlist _ A) (V2 : hlist _ B) π : 
    xprod_split (tctx_values π (V1 h++ V2)) = (tctx_values π V1, tctx_values π V2).
  Proof. elim/hlist_ind: V1 => [ //| ???? /= -> //=]. Qed.  

  Lemma tctx_values_merge {A B} (V1 : hlist _ A) (V2 : hlist _ B) π : 
    tctx_values π V1 -++ tctx_values π V2 = tctx_values π (V1 h++ V2).
  Proof. elim/hlist_ind: V1 => [ //| ???? /= -> //=]. Qed.

  (* Lemma tctx_interp_permut {As Bs} tid (T1 : tctx As) (T2 : tctx Bs) :
    T1 ≡ₕₚ T2 -> tctx_interp tid T1  ⊣⊢ tctx_interp tid T2.
  Proof. apply big_sepHL_permutation. Qed. *)

  Lemma tctx_interp_cons {A As} tid (x : tctx_elt A) (T : tctx As) vπ Vs :
    tctx_interp tid (x +:: T) (vπ +:: Vs) ⊣⊢ (tctx_elt_interp tid x vπ ∗ tctx_interp tid T Vs).
  Proof. done. Qed.

  Lemma tctx_interp_app {As Bs} tid (T1 : tctx As) V1 (T2 : tctx Bs) V2 :
    tctx_interp tid (T1 h++ T2) (V1 h++ V2) ⊣⊢ (tctx_interp tid T1 V1 ∗ tctx_interp tid T2 V2).
  Proof. 
    induction As as [|?? IH]; dependent destruction T1; dependent destruction V1.
    - by rewrite left_id.
    - by rewrite // !tctx_interp_cons -assoc IH.
  Qed.

  (* Definition tctx_interp_nil tid :
    tctx_interp tid +[] = True%I := eq_refl _. *)

  Lemma tctx_interp_singleton {A} tid (x : tctx_elt A) v :
    tctx_interp tid +[x] +[v] ⊣⊢ tctx_elt_interp tid x v.
  Proof. rewrite /tctx_interp /= right_id //. Qed.

  (** Copy typing contexts *)
  Class CopyC {As: Types} (T : tctx As) Vs :=
    copyc_persistent tid : Persistent (tctx_interp tid T Vs).
  Global Existing Instances copyc_persistent.

  Global Instance tctx_nil_copy : CopyC +[] +[].
  Proof. rewrite /CopyC. apply _. Qed.

  Global Instance tctx_ty_copy {A As} (T : tctx As) Vs p (ty : type A) vπ:
    CopyC T Vs → Copy ty → CopyC  ((p ◁ ty) +:: T) (vπ +:: Vs).
  Proof. intros ???. rewrite tctx_interp_cons. apply _. Qed.

  (** Send typing contexts *)
  Class SendC {As} (T : tctx As) Vs :=
    sendc_change_tid tid1 tid2 : tctx_interp tid1 T Vs -∗ tctx_interp tid2 T Vs.

  Global Instance tctx_nil_send : SendC +[] +[].
  Proof. done. Qed.

  Global Instance tctx_ty_send {A As} (T : tctx As) Vs p (ty : type A) vπ :
    SendC T Vs → Send ty → SendC ((p ◁ ty) +:: T) (vπ +:: Vs).
  Proof.
    iIntros (HT Hty ??). rewrite !tctx_interp_cons.
    iIntros "[Hty HT]". iSplitR "HT".
    - iDestruct "Hty" as (??) "(? & % & Hty)". iExists _, _.
      iSplit; first done. iSplit; first done. by iApply Hty.
    - by iApply HT.
  Qed.


  (** Type context inclusion *)
  Definition tctx_incl {A1 A2} (E : elctx) (L : llctx) (T1 : tctx A1) (T2 : tctx A2) (f : (xprod A2 → Prop) → xprod A1 → Prop) : Prop :=
    ∀ tid q2 V post, lft_ctx -∗ elctx_interp E -∗ llctx_interp L q2 -∗
              tctx_interp tid T1 V -∗ ⟨ π , f (post π) (tctx_values π V) ⟩ ={⊤}=∗ ∃ V2, llctx_interp L q2 ∗ ⟨ π, post π (tctx_values π V2) ⟩ ∗ tctx_interp tid T2 V2.
  (* Global Instance : ∀ A E L f, RewriteRelation (@tctx_incl A A E L f) := {}. *)

  (* Global Instance tctx_incl_preorder A E L : PreOrder (@tctx_incl A A E L).
  Proof.
    split.
    - by iIntros (???) "_ _ $ $".
    - rewrite /Transitive. iIntros (??? H1 H2 ??) "#LFT #HE HL H".
      iMod (H1 with "LFT HE HL H") as "(HL & H)".
      by iMod (H2 with "LFT HE HL H") as "($ & $)".
  Qed. *)

  Lemma tctx_incl_reflexive {A} E L (T : tctx A) : tctx_incl E L T T id. 
    iIntros (?? V?) "#LFT #HE HL ??".
    iExists V.
    by iFrame. 
  Qed.

  Lemma tctx_incl_transitive E L A B C (x : tctx A) (y : tctx B) (z : tctx C) f g :
    tctx_incl E L x y f → tctx_incl E L y z g → tctx_incl E L x z (f ∘ g).
  Proof.
    iIntros (H1 H2 tid q V post) "#LFT #HE HL H Hp".
    iMod (H1 with "LFT HE HL H Hp") as (?) "(HL & Hp1 & H)".
    iMod (H2 with "LFT HE HL H Hp1") as (?) "(? & Hp2 & ?)".
    iExists V0. by iFrame. 
  Qed.

(* 
  Definition xprod_hsubmseteq {As Bs} {T1 : tctx As} {T2 : tctx Bs} (sub : T1 ⊆+ₕ T2) : xprod Bs → xprod As.
    intros. dependent induction sub; simpl in *; intuition.
  Qed. *)

  (* Lemma contains_tctx_incl {As Bs} E L (T1 : tctx As) (T2 : tctx Bs) (s : T1 ⊆+ₕ T2) : tctx_incl E L T2 T1 (xprod_hsubmseteq s).
  Proof.
    rewrite /tctx_incl. iIntros (??) "_ _ $ H". by iApply big_sepHL_submseteq.
  Qed. *)
  Definition trans_app {A B C D} (f : (Π! A → Prop) → Π! B → Prop) (g : (Π! C → Prop) → Π! D → Prop) : (Π! (A ^++ C) → Prop) → Π! (B ^++ D) → Prop := 
    λ post bd, f (λ a, g (λ c, post (a -++ c)) (xprod_split_r bd)) (xprod_split_l bd).

  Lemma tctx_incl_app {As Bs Cs Ds} E L (T1 : tctx As) (T1' : tctx Bs) f (T2 : tctx Cs) (T2' : tctx Ds) g:  
    tctx_incl E L T1 T1' f → tctx_incl E L T2 T2' g → tctx_incl E L (T1 h++ T2) (T1' h++ T2') (trans_app f g).
  Proof.
    intros Hincl1 Hincl2 ????. destruct (hlist_app_split V) as (? & ? & ->). rewrite /tctx_incl /tctx_interp !big_sepHLZip'_app.
    iIntros "#LFT #HE HL [H1 H2] #HP".
    iMod (Hincl1 with "LFT HE HL H1 [HP]")  as (W1) "(HL & Hp1 & ?)".
    { by rewrite /trans_app; setoid_rewrite tctx_values_split_l. }
    iMod (Hincl2 with "LFT HE HL H2 [Hp1]") as (W2) "(HL & Hp2 & ?)".
    { by setoid_rewrite tctx_values_split_r. }
    iExists (W1 h++ W2).
    rewrite big_sepHLZip'_app.
    iFrame; by setoid_rewrite tctx_values_distr. 
  Qed.

  (* Lemma tctx_incl_frame_l {E L As Bs Cs} (T :tctx As) (T1 : tctx Bs) (T2 : tctx Cs) f:
    tctx_incl E L T1 T2 f → tctx_incl E L (T +++ T1) (T +++ T2) (xprod_bimap id f).
  Proof. apply tctx_incl_app, tctx_incl_reflexive. Qed.

  Lemma tctx_incl_frame_r {E L As Bs Cs} (T : tctx As) (T1 : tctx Bs) (T2 : tctx Cs) f :
    tctx_incl E L T1 T2 f → tctx_incl E L (T1+++T) (T2+++T) (xprod_bimap f id).
  Proof.  intros. by apply tctx_incl_app, tctx_incl_reflexive. Qed.
  *)

  Lemma tcx_incl_cons {A As Bs} E L (x : tctx_elt A) (T1 : tctx As) (T2 : tctx Bs) f : 
    tctx_incl E L T1 T2 f → 
    tctx_incl E L (x +:: T1) (x +:: T2) (trans_app (id : (Π! ^[A] → Prop) → Π! ^[A] → Prop )  f).
  Proof.
    apply (tctx_incl_app E L +[_] +[_]), tctx_incl_reflexive.
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

  Definition tctx_extract_hasty {As Bs A} E L p (ty : type A) (T : tctx As) (T' : tctx Bs) f : Prop :=
    tctx_incl E L T ((p ◁ ty) +:: T') f.

  Definition xprod_extract {As A B Bs} (f : xprod As → xprod (B ^:: Bs)) : xprod (A ^:: As) → xprod (B ^:: A ^:: Bs) :=
    λ '(a -:: ass), let '(b -:: bss) := f ass in b -:: a -:: bss.

  (* Lemma tctx_extract_hasty_further {As Bs A B} E L p (ty : type B)  (T : tctx As) (T' : tctx Bs) f (x : tctx_elt A) :
    tctx_extract_hasty E L p ty  T T' f →
    tctx_extract_hasty E L p ty  (x+::T) (x+::T') (xprod_extract f).
  Proof.
    rewrite /tctx_extract_hasty.
    intros.
    eapply tctx_incl_transitive;
      [eapply tcx_incl_cons, H| apply contains_tctx_incl].
      
    Unshelve.
    constructor.
  Qed. *)
    
  (* Lemma tctx_extract_hasty_here_copy {A B As} E L f p1 p2 (ty : type A)  (ty' : type B)  (T : tctx As) :
    p1 = p2 → Copy ty → subtype E L f ty ty' →
    tctx_extract_hasty E L p1 ty' (f ∘ ) ((p2 ◁ ty)+::T) ((p2 ◁ ty [{ }])+::T) (λ p, (f p.1, p)).
  Proof.
    intros -> ??. apply (tctx_incl_frame_r _ +[_] +[_;_] (λ p, (f p.1, p))).
    eapply tctx_incl_transitive; first by apply copy_tctx_incl, _.
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
    eapply tctx_incl_transitive;
      [eapply tcx_incl_cons, H| apply contains_tctx_incl].
      
    Unshelve.
    constructor.
  Qed. *)

  (* Lemma tctx_extract_blocked_here {A As} E L p κ (ty : type A)  (T : tctx As) f:
    tctx_extract_blocked E L p κ ty  ((p ◁{κ} ty)+::T) T f.
  Proof. intros. apply (tctx_incl_frame_r _ +[_] +[_] id), tctx_incl_reflexive. Qed. *)

  Definition tctx_extract_ctx {As Bs Cs} E L (T : tctx As) (T1 : tctx Bs) (T2 : tctx Cs) f : Prop :=
    tctx_incl E L T1 (T h++T2) f.

  Lemma tctx_extract_ctx_nil {As} E L (T : tctx As):
    tctx_extract_ctx E L +[] T T id.
  Proof. apply tctx_incl_reflexive. Qed.

  Definition tctx_extract_ctx_hasty_trans {A As Bs Cs Ds} 
    (f : (Π! (A ^:: Cs) → Prop) → Π! Bs → Prop ) 
    (g : (Π! (As ^++ Ds) → Prop) → Π! Cs → Prop)
  : (Π! ((A ^:: As) ^++ Ds) → Prop) → Π! Bs → Prop := 
  λ post b, f (λ '(a -:: c),  g (λ ad, post (a -:: ad)) c) b.

  Lemma tctx_extract_ctx_hasty {A As Bs Cs Ds} E L (T : tctx As) (T1 : tctx Bs) (T2 : tctx Cs) (T3 : tctx Ds) p (ty : type A) f g:
    tctx_extract_hasty E L p ty T1 T2 f → tctx_extract_ctx E L T T2 T3 g →
    tctx_extract_ctx E L ((p ◁ ty)+::T) T1 T3 (f ∘ trans_app (id : (Π! ^[A] → Prop) → _) g).
  Proof. unfold tctx_extract_ctx, tctx_extract_hasty => ??.
    eapply tctx_incl_transitive; [eassumption |  by eapply tcx_incl_cons]. 
  Qed.
  (*
  Lemma tctx_extract_ctx_blocked {A As Bs Cs Ds} E L (T : tctx As) (T1 : tctx Bs) (T2 : tctx Cs) (T3 : tctx Ds) p κ (ty : type A) :
    tctx_extract_blocked E L p κ ty  T1 T2 → tctx_extract_ctx E L T T2 T3 →
    tctx_extract_ctx E L ((p ◁{κ} ty)+::T) T1 T3.
  Proof. unfold tctx_extract_ctx, tctx_extract_blocked => ?? //.
    eapply tctx_incl_transitive, tcx_incl_cons; eassumption.
  Qed.

  Lemma tctx_extract_ctx_incl {As Bs Cs} E L (T : tctx As) (T' : tctx Bs) (T0 : tctx Cs):
    tctx_extract_ctx E L T' T T0 →
    tctx_incl E L T T'.
  Proof.
    unfold tctx_extract_ctx=> ?.
    eapply tctx_incl_transitive; first eassumption.
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
