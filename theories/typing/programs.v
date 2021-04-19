From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context.
From lrust.util Require Import types.
Set Default Proof Using "Type".

Section typing.
  Context `{!typeG Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body {As} (E: elctx) (L: llctx)
    (C: cctx) (T: tctx As) (e: expr) (pre: predl As) : iProp Σ :=
    ∀tid vπl, lft_ctx -∗ time_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
      llctx_interp L 1 -∗ cctx_interp tid C -∗ tctx_interp tid T vπl -∗
      ⟨π, pre (vπl -$ π)⟩ -∗ WP e {{ _, cont_postcondition }}.
  Global Arguments typed_body {_} _ _ _ _ _%E _.

  Lemma typed_body_impl {As} (pre pre': predl As) E L C T e :
    (∀vl, pre vl → pre' vl) → typed_body E L C T e pre' -∗ typed_body E L C T e pre.
  Proof.
    move=> Imp. rewrite /typed_body. do 12 f_equiv=>/=. do 2 f_equiv. move=> ?.
    by apply Imp.
  Qed.

  (* Global Instance typed_body_llctx_permut E :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> (⊢)) (typed_body E).
  Proof.
    intros L1 L2 HL C ? <- T ? <- e ? <-. rewrite /typed_body.
    by setoid_rewrite HL.
  Qed. *)

  (* Global Instance typed_body_elctx_permut :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> eq ==> (⊢)) typed_body.
  Proof.
    intros E1 E2 HE L ? <- C ? <- T ? <- e ? <-. rewrite /typed_body.
    by setoid_rewrite HE.
  Qed. *)

  (* Global Instance typed_body_mono E L:
    Proper (flip (cctx_incl E) ==> flip (tctx_incl E L) ==> eq ==> (⊢))
           (typed_body E L).
  Proof.
    intros C1 C2 HC T1 T2 HT e ? <-. iIntros "H".
    iIntros (tid) "#LFT #TIME #HE Htl HL HC HT".
    iMod (HT with "LFT HE HL HT") as "(HL & HT)".
    iApply ("H" with "LFT TIME HE Htl HL [HC] HT").
    by iApply (HC with "LFT HE HC").
  Qed. *)

  (* Global Instance typed_body_mono_flip E L:
    Proper (cctx_incl E ==> tctx_incl E L ==> eq ==> flip (⊢))
           (typed_body E L).
  Proof. intros ?????????. by eapply typed_body_mono. Qed. *)

  (** Instruction *)
  Definition typed_instr {As Bs} (E: elctx) (L: llctx)
    (T: tctx As) (e: expr) (T': val → tctx Bs) (tr: predl_trans As Bs) : iProp Σ :=
    ∀tid postπ vπl, lft_ctx -∗ time_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
      llctx_interp L 1 -∗ tctx_interp tid T vπl -∗ ⟨π, tr (postπ π) (vπl -$ π)⟩ -∗
      WP e {{ v, ∃vπl', na_own tid ⊤ ∗ llctx_interp L 1 ∗
        tctx_interp tid (T' v) vπl' ∗ ⟨π, postπ π (vπl' -$ π)⟩ }}.
  Global Arguments typed_instr _ _ _ _ _ _%E _ _.

  (** Writing and Reading *)
(*
  Definition typed_write_def (E : elctx) (L : llctx) (ty1 ty ty2 : type) : iProp Σ :=
    (□ ∀ v depth tid F qL, ⌜↑lftN ∪ ↑lrustN ⊆ F⌝ →
      lft_ctx -∗ elctx_interp E -∗ llctx_interp L qL -∗ ty1.(ty_own) depth tid [v] ={F}=∗
        ∃ (l : loc) vl, ⌜length vl = ty.(ty_size) ∧ v = #l⌝ ∗ l ↦∗ vl ∗
          (▷ l ↦∗: ty.(ty_own) depth tid -∗ ⧖(S depth) ={F}=∗
            llctx_interp L qL ∗ ty2.(ty_own) (S depth) tid [v]))%I.
  Definition typed_write_aux : seal (@typed_write_def). by eexists. Qed.
  Definition typed_write := typed_write_aux.(unseal).
  Definition typed_write_eq : @typed_write = @typed_write_def := typed_write_aux.(seal_eq).
  Global Arguments typed_write _ _ _%T _%T _%T.

  Global Instance typed_write_persistent (E : elctx) (L : llctx) (ty1 ty ty2 : type) :
    Persistent (typed_write E L ty1 ty ty2).
  Proof. rewrite typed_write_eq. apply _. Qed.
*)

  (* Technically speaking, we could remvoe the vl quantifiaction here and use
     mapsto_pred instead (i.e., l ↦∗: ty.(ty_own) tid). However, that would
     make work for some of the provers way harder, since they'd have to show
     that nobody could possibly have changed the vl (because only half the
     fraction was given). So we go with the definition that is easier to prove. *)
  Definition typed_read {A B A'} (E: elctx) (L: llctx) (ty: type A) (tyb: type B)
    (ty': type A') (gt: A → B) (st: A → A') : Prop := ∀vπ d v tid qL,
      lft_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗ llctx_interp L qL -∗
      ty.(ty_own) vπ d tid [v] ={⊤}=∗ ∃(l: loc) vl q,
        ⌜v = #l⌝ ∗ l ↦∗{q} vl ∗ ▷ tyb.(ty_own) (gt ∘ vπ) d tid vl ∗ (l ↦∗{q} vl ={⊤}=∗
          na_own tid ⊤ ∗ llctx_interp L qL ∗ ty'.(ty_own) (st ∘ vπ) d tid [v]).
  Global Arguments typed_read {_ _ _} _ _ _%T _%T _%T _ _.

End typing.

Definition typed_instr_ty `{!typeG Σ} {As B} (E: elctx) (L: llctx)
  (T: tctx As) (e: expr) (ty: type B) (tr: pred B → predl As) : iProp Σ :=
  typed_instr E L T e (λ v, +[v ◁ ty]) (λ post al, tr (λ b, post -[b]) al).
Arguments typed_instr_ty {_ _ _ _} _ _ _ _%E _%T _.

Definition typed_val `{!typeG Σ} {A} (v: val) (ty: type A) (tr: pred (pred A)) : Prop :=
  ∀E L, ⊢ typed_instr_ty E L +[] (of_val v) ty (λ post _, tr post).
Arguments typed_val {_ _ _} _%V _%T _.

Section typing_rules.
  Context `{!typeG Σ}.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type {As} E L C (T: tctx As) e p:
    typed_body E L C T e p -∗ typed_body E L C T e p.
  Proof. done. Qed.

  (* TODO: Proof a version of this that substitutes into a compatible context...
     if we really want to do that. *)
  Lemma type_equivalize_lft {As} E L C (T: _ As) κ κ' e pre :
    typed_body (κ ⊑ₑ κ' :: κ' ⊑ₑ κ :: E) L C T e pre -∗
    typed_body E (κ ⊑ₗ [κ'] :: L) C T e pre.
  Proof.
    iIntros "He" (??) "#LFT TIME E Na [Eq L] C T".
    iMod (lctx_equalize_lft with "LFT Eq") as "[In In']".
    iApply ("He" with "LFT TIME [$E $In $In'] Na L C T").
  Qed.

  Lemma type_let' {As Bs Cs} E L (T1: _ As) (T2: _ → _ Bs) (T: _ Cs) C xb e e' tr pre:
    Closed (xb :b: []) e' → typed_instr E L T1 e T2 tr -∗
    (∀v: val, typed_body E L C (T2 v h++ T) (subst' xb v e') pre) -∗
    typed_body E L C (T1 h++ T) (let: xb := e in e') (trans_upper tr pre).
  Proof.
    iIntros (?) "He He'". iIntros (tid vπl2). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #E Na L C [T1 T] Obs". wp_bind e.
    iApply (wp_wand with "[He L T1 Na Obs]").
    { iApply ("He" with "LFT TIME E Na L T1"). iApply proph_obs_impl; [|done]=> ?.
      rewrite /trans_upper papply_app papp_sepl. exact id. }
    iIntros (v). iIntros "(%vπ & Na & L & T2 & ?)". wp_let. iCombine "T2 T" as "T2T".
    iApply ("He'" $! v tid (vπ -++ vπl') with "LFT TIME E Na L C T2T").
    iApply proph_obs_impl; [|done]=>/= ?. rewrite papply_app papp_sepr. exact id.
  Qed.

  Lemma typed_body_tctx_incl {A B} E L C (T: tctx A) (T': tctx B) e pre tr :
    tctx_incl E L T T' tr →
    typed_body E L C T' e pre -∗ typed_body E L C T e (tr pre).
  Proof.
    iIntros (In) "He". iIntros (??) "#LFT TIME #E Na L C T Obs".
    iMod (In with "LFT E L T Obs") as (?) "(L & Obs & T')".
    iApply ("He" with "LFT TIME E Na L C T' Obs").
  Qed.

  (* We do not make the [typed_instr] hypothesis part of the
     Iris hypotheses, because we want to preserve the order of the
     hypotheses. The is important, since proving [typed_instr]
     will instantiate [T1] and [T2], and hence we know what to search
     for the following hypothesis. *)
  Lemma type_let {As Bs Cs Ds} (T1: _ As) (T2: _ → _ Bs)
    (T: _ Cs) (T': _ Ds) E L C xb e e' tr tr' pre (tr_res: predl _) :
    Closed (xb :b: []) e' → (⊢ typed_instr E L T1 e T2 tr) →
    tctx_extract_ctx E L T1 T T' tr' → tr_res = tr' (trans_upper tr pre) →
    (∀v: val, typed_body E L C (T2 v h++ T') (subst' xb v e') pre) -∗
    typed_body E L C T (let: xb := e in e') tr_res.
  Proof.
    rewrite /tctx_extract_ctx=> ???->. iIntros.
    rewrite -typed_body_tctx_incl; [|done]. by iApply type_let'.
  Qed.

  Lemma type_seq {As Bs Cs Ds} (T1: _ As) (T2: _ Bs)
    (T: _ Cs) (T': _ Ds) E L C e e' tr tr' pre (tr_res: predl _) :
    Closed [] e' → (⊢ typed_instr E L T1 e (const T2) tr) →
    tctx_extract_ctx E L T1 T T' tr' → tr_res = tr' (trans_upper tr pre) →
    typed_body E L C (T2 h++ T') e' pre -∗ typed_body E L C T (e ;; e') tr_res.
  Proof. iIntros. iApply (type_let _ (const T2))=>//. by iIntros. Qed.

  Lemma type_newlft {As} κs E L C (T: _ As) e pre :
    Closed [] e → (∀κ, typed_body E (κ ⊑ₗ κs :: L) C T e pre) -∗
    typed_body E L C T (Newlft ;; e) pre.
  Proof.
    iIntros (?) "He". iIntros (??) "#LFT TIME E Na L C T Obs".
    iMod (lft_create with "LFT") as (Λ) "[Tok #Hinh]"; [done|].
    set κ' := lft_intersect_list κs. wp_seq.
    iApply ("He" $! κ' ⊓ Λ with "LFT TIME E Na [Tok $L] C T Obs").
    rewrite /llctx_interp. iExists Λ. iFrame "Tok". by iSplit.
  Qed.

(*
  (* TODO: It should be possible to show this while taking only one step.
     Right now, we could take two. *)
  Lemma type_endlft E L C T1 T2 κ κs e :
    Closed [] e → UnblockTctx κ T1 T2 →
    typed_body E L C T2 e -∗ typed_body E ((κ ⊑ₗ κs) :: L) C T1 (Endlft ;; e).
  Proof.
    iIntros (Hc Hub) "He". iIntros (tid) "#LFT #TIME #HE Htl [Hκ HL] HC HT".
    iDestruct "Hκ" as (Λ) "(% & Htok & #Hend)".
    iSpecialize ("Hend" with "Htok"). wp_bind Endlft.
    iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); first done.
    iApply (wp_step_fupd with "Hend"); first set_solver-. wp_seq.
    iIntros "#Hdead !>". wp_seq. iApply ("He" with "LFT TIME HE Htl HL HC [> -]").
    iApply (Hub with "[] HT"). simpl in *. subst κ. rewrite -lft_dead_or. auto.
  Qed.
*)

  Lemma type_path_instr {A} p (ty: _ A) E L :
    ⊢ typed_instr_ty E L +[p ◁ ty] p ty (λ post '(-[v]), post v).
  Proof.
    iIntros (??[vπ[]]) "_ _ _ $$ [T _] Obs". iApply (wp_hasty with "T").
    iIntros (v d _) "??". iExists -[vπ]. do 2 (iSplit; [|done]). iExists v, d.
    rewrite eval_path_of_val. by iFrame.
  Qed.

  Lemma type_letpath {A Bs Cs} E L (ty: _ A) C (T: _ Bs) (T': _ Cs) x p e tr pre :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' tr →
    (∀v: val, typed_body E L C (v ◁ ty +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := p in e) (tr pre).
  Proof.
    iIntros. iApply type_let; [by apply (@type_path_instr A)|done| |done].
    f_equal. fun_ext. by case.
  Qed.

(*
  Lemma type_assign_instr {E L} ty ty1 ty1' p1 p2 :
    (⊢ typed_write E L ty1 ty ty1') →
    (⊢ typed_instr E L [p1 ◁ ty1; p2 ◁ ty] (p1 <- p2) (λ _, [p1 ◁ ty1'])).
  Proof.
    iIntros (Hwrt tid) "#LFT #TIME #HE $ HL".
    rewrite tctx_interp_cons tctx_interp_singleton. iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (depth1 v1) "Hdepth1 % Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (depth2 v2) "Hdepth2 _ Hown2".
    iCombine "Hdepth1 Hdepth2" as "Hdepth". rewrite -persistent_time_receipt_sep.
    iApply wp_fupd. rewrite typed_write_eq in Hwrt.
    iMod (Hwrt with "[] LFT HE HL [> Hown1]") as (l vl) "([% %] & Hl & Hclose)"; first done.
    { iApply (ty_own_depth_mono _ _ (depth1 `max` depth2) with "Hown1"). lia. }
    iApply (wp_persistent_time_receipt with "TIME Hdepth")=>//.
    subst v1. iDestruct (ty_size_eq with "Hown2") as "#Hsz". iDestruct "Hsz" as %Hsz.
    rewrite <-Hsz in *. destruct vl as [|v[|]]; try done.
    rewrite heap_mapsto_vec_singleton. wp_write. rewrite -heap_mapsto_vec_singleton.
    iIntros "#Hdepth". iMod ("Hclose" with "[> Hl Hown2] Hdepth") as "($ & Hown)".
    { iExists _. iFrame. iApply (ty_own_depth_mono with "Hown2"); lia. }
    rewrite tctx_interp_singleton tctx_hasty_val' //. eauto.
  Qed.

  Lemma type_assign {E L} ty1 ty ty1' C T T' p1 p2 e:
    Closed [] e →
    tctx_extract_ctx E L [p1 ◁ ty1; p2 ◁ ty] T T' →
    (⊢ typed_write E L ty1 ty ty1') →
    typed_body E L C ((p1 ◁ ty1') :: T') e -∗
    typed_body E L C T (p1 <- p2 ;; e).
  Proof. iIntros. by iApply type_seq; first apply type_assign_instr. Qed.
*)

  Lemma type_deref_instr {A B A'} (ty: _ A) (tyb: _ B) (ty': _ A') gt st p E L :
    tyb.(ty_size) = 1%nat → typed_read E L ty tyb ty' gt st →
    ⊢ typed_instr E L +[p ◁ ty] (!p) (λ v, +[v ◁ tyb; p ◁ ty'])
      (λ post '(-[a]), post -[gt a; st a]).
  Proof.
    move=> Sz Read. iIntros (??[vπ[]]) "#LFT #TIME #E Na L [p _] Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (???) "#Time ty".
    iMod (Read with "LFT E Na L ty") as (l vl q ->) "(Mt & tyb & Close)".
    iDestruct (ty_size_eq with "tyb") as "#>%Len". rewrite Sz in Len.
    case vl as [|v[|]]=>//. rewrite heap_mapsto_vec_singleton. iApply wp_fupd.
    wp_read. iMod ("Close" with "Mt") as "($&$& ty')". iModIntro.
    iExists -[gt ∘ vπ; st ∘ vπ]. iSplit; [|done]. rewrite right_id
    tctx_hasty_val tctx_hasty_val'; [|done]. iSplitL "tyb"; iExists d; by iSplit.
  Qed.

  Lemma type_deref {A B A' As Bs} (ty: _ A) (tyb: _ B) (ty': _ A') gt st
    (T: _ As) (T': _ Bs) p x e tr pre E L C :
    Closed (x :b: []) e → tctx_extract_hasty E L p ty T T' tr →
    typed_read E L ty tyb ty' gt st → tyb.(ty_size) = 1%nat →
    (∀v: val, typed_body E L C (v ◁ tyb +:: p ◁ ty' +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := !p in e)
      (tr (λ '(a -:: al), pre (gt a -:: st a -:: al))).
  Proof. iIntros. iApply type_let; by [eapply type_deref_instr|solve_typing|]. Qed.

(*
  Lemma type_memcpy_iris E L qL tid ty ty1 ty1' ty2 ty2' (n : Z) p1 p2 :
    Z.of_nat (ty.(ty_size)) = n →
    typed_write E L ty1 ty ty1' -∗ typed_read E L ty2 ty ty2' -∗
    {{{ lft_ctx ∗ time_ctx ∗ elctx_interp E ∗ na_own tid ⊤ ∗ llctx_interp L qL ∗
        tctx_elt_interp tid (p1 ◁ ty1) ∗ tctx_elt_interp tid (p2 ◁ ty2) }}}
      (p1 <-{n} !p2)
    {{{ RET #☠; na_own tid ⊤ ∗ llctx_interp L qL ∗
                 tctx_elt_interp tid (p1 ◁ ty1') ∗ tctx_elt_interp tid (p2 ◁ ty2') }}}.
  Proof.
    iIntros (<-) "#Hwrt #Hread !>".
    iIntros (Φ) "(#LFT & #TIME & #HE & Htl & [HL1 HL2] & [Hp1 Hp2]) HΦ".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (depth1 v1) "Hdepth1 % Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (depth2 v2) "Hdepth2 % Hown2".
    iCombine "Hdepth1 Hdepth2" as "Hdepth". rewrite -persistent_time_receipt_sep.
    iApply wp_fupd. rewrite typed_write_eq typed_read_eq.
    iMod ("Hwrt" with "[] LFT HE HL1 [> Hown1]")
      as (l1 vl1) "([% %] & Hl1 & Hcl1)"; first done.
    { iApply (ty_own_depth_mono _ _ (depth1 `max` depth2) with "Hown1"). lia. }
    iMod ("Hread" with "[] LFT HE Htl HL2 Hown2")
      as (l2 vl2 q2) "(% & Hl2 & Hown2 & Hcl2)"; first done.
    iApply (wp_persistent_time_receipt with "TIME Hdepth")=>//.
    iDestruct (ty_size_eq with "Hown2") as "#>%". subst v1 v2.
    iApply (wp_memcpy with "[$Hl1 $Hl2]"); try congruence; [].
    iNext. iIntros "[Hl1 Hl2] #Hdepth".
    iMod ("Hcl1" with "[> Hl1 Hown2] Hdepth") as "[? H1]".
    { iExists _. iFrame. iApply (ty_own_depth_mono with "Hown2"). lia. }
    iMod ("Hcl2" with "Hl2") as "(? & ? & H2)".
    iApply "HΦ". iFrame. rewrite !tctx_hasty_val' //.
    iSplitL "H1"; [by eauto with iFrame|]. iExists _. iFrame.
    iApply persistent_time_receipt_mono; [|done]. lia.
  Qed.

  Lemma type_memcpy_instr {E L} ty ty1 ty1' ty2 ty2' (n : Z) p1 p2 :
    Z.of_nat (ty.(ty_size)) = n →
    (⊢ typed_write E L ty1 ty ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    ⊢ typed_instr E L [p1 ◁ ty1; p2 ◁ ty2] (p1 <-{n} !p2)
                      (λ _, [p1 ◁ ty1'; p2 ◁ ty2']).
  Proof.
    iIntros (Hsz Hwrt Hread tid) "#LFT #TIME #HE Htl HL HT".
    iApply (type_memcpy_iris with "[] [] [$LFT $TIME $Htl $HE $HL HT]"); try done.
    { by rewrite tctx_interp_cons tctx_interp_singleton. }
    rewrite tctx_interp_cons tctx_interp_singleton. auto.
  Qed.

  Lemma type_memcpy {E L} ty ty1 ty2 (n : Z) C T T' ty1' ty2' p1 p2 e:
    Closed [] e →
    tctx_extract_ctx E L [p1 ◁ ty1; p2 ◁ ty2] T T' →
    (⊢ typed_write E L ty1 ty ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C ((p1 ◁ ty1') :: (p2 ◁ ty2') :: T') e -∗
    typed_body E L C T (p1 <-{n} !p2;; e).
  Proof. iIntros. by iApply type_seq; first eapply (type_memcpy_instr ty ty1 ty1'). Qed.
*)

End typing_rules.
