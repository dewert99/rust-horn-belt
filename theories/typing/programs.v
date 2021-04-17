From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context.
From lrust.util Require Import types.

Set Default Proof Using "Type".

Section typing.
  Context `{!typeG Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body {As} (E : elctx) (L : llctx) (C : cctx) (T : tctx As)
                        (e : expr) (pre : xprod As → Prop): iProp Σ :=
    (∀ tid V, lft_ctx -∗ time_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗ llctx_interp L 1 -∗
               cctx_interp tid C -∗ tctx_interp tid T V -∗
               ⟨ π, pre (tctx_values π V) ⟩ -∗
               WP e {{ _, cont_postcondition }})%I.
  Global Arguments typed_body _ _ _ _ _ _%E.

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
  Definition typed_instruction {As Bs} (E : elctx) (L : llctx)
             (T1 : tctx As) (e : expr) (T2 : val → tctx Bs) (pre : (xprod Bs → Prop) → xprod As → Prop): iProp Σ :=
    (∀ tid post V1, lft_ctx -∗ time_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
              llctx_interp L 1 -∗ tctx_interp tid T1 V1 -∗
              ⟨π, pre (post π) (tctx_values π V1) ⟩ -∗
              WP e {{ 𝔳, ∃ V', (na_own tid ⊤ ∗
                         llctx_interp L 1 ∗ tctx_interp tid (T2 𝔳) V' ∗  ⟨ π, post π (tctx_values π V') ⟩ )}})%I.
  Global Arguments typed_instruction _ _ _ _ _ _ _%E _.

  (* * Writing and Reading *
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

  (* Technically speaking, we could remvoe the vl quantifiaction here and use
     mapsto_pred instead (i.e., l ↦∗: ty.(ty_own) tid). However, that would
     make work for some of the provers way harder, since they'd have to show
     that nobody could possibly have changed the vl (because only half the
     fraction was given). So we go with the definition that is easier to prove. *)
  Definition typed_read_def (E : elctx) (L : llctx) (ty1 ty ty2 : type) : iProp Σ :=
    (□ ∀ v depth tid F qL, ⌜↑lftN ∪ ↑lrustN ⊆ F⌝ →
      lft_ctx -∗ elctx_interp E -∗ na_own tid F -∗
      llctx_interp L qL -∗ ty1.(ty_own) depth tid [v] ={F}=∗
        ∃ (l : loc) vl q, ⌜v = #l⌝ ∗ l ↦∗{q} vl ∗ ▷ ty.(ty_own) depth tid vl ∗
              (l ↦∗{q} vl ={F}=∗ na_own tid F ∗
                              llctx_interp L qL ∗ ty2.(ty_own) depth tid [v]))%I.
  Definition typed_read_aux : seal (@typed_read_def). by eexists. Qed.
  Definition typed_read := typed_read_aux.(unseal).
  Definition typed_read_eq : @typed_read = @typed_read_def := typed_read_aux.(seal_eq).
  Global Arguments typed_read _ _ _%T _%T _%T.

  Global Instance typed_read_persistent (E : elctx) (L : llctx) (ty1 ty ty2 : type) :
    Persistent (typed_read E L ty1 ty ty2).
  Proof. rewrite typed_read_eq. apply _. Qed. *)
End typing.

Definition typed_instruction_ty {As A} `{!typeG Σ} (E : elctx) (L : llctx) (T : tctx As)
    (e : expr) (ty : type A) pre : iProp Σ :=
  typed_instruction E L T e (λ 𝔳, +[𝔳 ◁ ty]) pre.
Arguments typed_instruction_ty {_ _} {_ _} _ _ _ _%E _%T _.

Definition typed_val {A} `{!typeG Σ} (v : val) (ty : type A) pre : Prop :=
  ∀ E L, ⊢ typed_instruction_ty E L +[] (of_val v) ty pre.
Arguments typed_val {_} {_ _} _%V _%T.

Section typing_rules.
  Context `{!typeG Σ}.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type {As} E L C (T : tctx As) e p:
    typed_body E L C T e p -∗ typed_body E L C T e p.
  Proof. done. Qed.

  (* TODO: Proof a version of this that substitutes into a compatible context...
     if we really want to do that. *)
  (* Lemma type_equivalize_lft E L C T κ1 κ2 e :
    (⊢ typed_body ((κ1 ⊑ₑ κ2) :: (κ2 ⊑ₑ κ1) :: E) L C T e) →
    ⊢ typed_body E ((κ1 ⊑ₗ [κ2]) :: L) C T e.
  Proof.
    iIntros (He tid) "#LFT #TIME #HE Htl [Hκ HL] HC HT".
    iMod (lctx_equalize_lft with "LFT Hκ") as "[Hκ1 Hκ2]".
    iApply (He with "LFT TIME [Hκ1 Hκ2 HE] Htl HL HC HT").
    rewrite /elctx_interp /=. by iFrame.
  Qed. *)

  Definition let_pre {A1 A2 O} 
    (p : (xprod A2 → Prop) → xprod A1 → Prop) 
    (x : xprod (A2 ^++ O) → Prop) 
    : xprod (A1 ^++ O) → Prop :=
    λ a1o, let '(a1, o) := xprod_split a1o in
      p (λ a2, x (a2 -++ o)) a1.
    
  Lemma type_let' {A B D} E L (T1 : tctx A) (T2 : val → tctx B) (T : tctx D) C xb e e' trans pre:
    Closed (xb :b: []) e' →
    typed_instruction E L T1 e T2 trans -∗
    (∀ v : val, typed_body E L C (T2 v h++ T) (subst' xb v e') pre) -∗
    typed_body E L C (T1 h++ T) (let: xb := e in e') (let_pre trans pre).
  Proof.
    iIntros (Hc) "He He'". iIntros (tid V) "#LFT #TIME #HE Htl HL HC HT #Hp".
    destruct (hlist_app_split V) as (V1 & V2 & ->).
    rewrite tctx_interp_app.
    iDestruct "HT" as "[HT1 HT]". wp_bind e. iApply (wp_wand with "[He HL HT1 Htl]").
    {
      rewrite /let_pre.
      setoid_rewrite (tctx_values_split V1 V2).
      iApply ("He" with "LFT TIME HE Htl HL HT1 Hp").
    }
    iIntros (v). iIntros "Hx". iDestruct "Hx" as (x) "(Htl & HL & HT2 & ?)".  wp_let.
    iApply ("He'" $! v tid (x h++ V2) with "LFT TIME HE Htl HL HC [HT2 HT]").
    rewrite tctx_interp_app. by iFrame.
    iClear "Hp".
    rewrite (proph_obs_proper); [ | intro; rewrite tctx_values_merge]; done.
  Qed.
(* 
  Lemma incl_values_compat {A B C } E L (T : tctx A) (T1 : tctx B) (T2 : tctx C) π f: 
    tctx_incl E L T (T1 h++ T2) f ->
    f (tctx_values π T) = tctx_values π (T1 h++ T2).
  Proof. *)
   
  Lemma type_body_incl {A B} E L C (T : tctx A) (T' : tctx B) e pre f:
    tctx_incl E L T T' f →
    typed_body E L C T' e pre -∗
    typed_body E L C T e (f pre).
  Proof.
    iIntros (?) "Hb".
    iIntros (tid V) "#LFT #TIME #HE Htl HL HC HT #Hp".
    iMod (H with "LFT HE HL HT Hp") as (X) "(HL & Hp' & HT')".
    by iApply ("Hb" with "LFT TIME HE Htl HL HC HT'").
  Qed.

  (* We do not make the [typed_instruction] hypothesis part of the
     Iris hypotheses, because we want to preserve the order of the
     hypotheses. The is important, since proving [typed_instruction]
     will instantiate [T1] and [T2], and hence we know what to search
     for the following hypothesis. *)

     (* λ d, let '(a, c) := xprod_split (f d) in trans (λ b, pre (xprod_merge b c)) a *)
  Lemma type_let {A B Cs D} E L (T : tctx D) (T' : tctx Cs) (T1 : tctx A) (T2 : val → tctx B) C xb e e' trans pre f g:
    Closed (xb :b: []) e' →
    (⊢ typed_instruction E L T1 e T2 trans) →
    tctx_extract_ctx E L T1 T T' f →
    f (let_pre trans pre) = g →
    (∀ v : val, typed_body E L C (T2 v h++ T') (subst' xb v e') pre) -∗
    typed_body E L C T (let: xb := e in e') g.
  Proof.
    unfold tctx_extract_ctx. iIntros (? He ? <-) "?". 
    rewrite -(type_body_incl _ _ _ _ _ _ _ _ H0). 
    iApply type_let'; done.
  Qed.

  (*
  Lemma type_seq E L T T' T1 T2 C e e' :
    Closed [] e' →
    (⊢ typed_instruction E L T1 e (λ _, T2)) →
    tctx_extract_ctx E L T1 T T' →
    typed_body E L C (T2 ++ T') e' -∗
    typed_body E L C T (e ;; e').
  Proof. iIntros. iApply (type_let E L T T' T1 (λ _, T2)); auto. Qed.

  Lemma type_newlft {E L C T} κs e :
    Closed [] e →
    (∀ κ, typed_body E ((κ ⊑ₗ κs) :: L) C T e) -∗
    typed_body E L C T (Newlft ;; e).
  Proof.
    iIntros (Hc) "He". iIntros (tid) "#LFT #TIME #HE Htl HL HC HT".
    iMod (lft_create with "LFT") as (Λ) "[Htk #Hinh]"; first done.
    set (κ' := lft_intersect_list κs). wp_seq.
    iApply ("He" $! (κ' ⊓ Λ) with "LFT TIME HE Htl [HL Htk] HC HT").
    rewrite /llctx_interp /=. iFrame "HL".
    iExists Λ. iSplit; first done. iFrame. done.
  Qed.

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

  Lemma type_path_instr {E L} p ty :
    ⊢ typed_instruction_ty E L [p ◁ ty] p ty.
  Proof.
    iIntros (?) "_ _ _ $$ [? _]".
    iApply (wp_hasty with "[-]"). done. iIntros (depth v) "Hdepth _ Hv".
    rewrite tctx_interp_singleton. iExists v, depth. iFrame. by rewrite eval_path_of_val.
  Qed.

  Lemma type_letpath {E L} ty C T T' x p e :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p ty T T' →
    (∀ (v : val), typed_body E L C ((v ◁ ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := p in e).
  Proof. iIntros. iApply type_let; [by apply type_path_instr|solve_typing|done]. Qed.

  Lemma type_assign_instr {E L} ty ty1 ty1' p1 p2 :
    (⊢ typed_write E L ty1 ty ty1') →
    (⊢ typed_instruction E L [p1 ◁ ty1; p2 ◁ ty] (p1 <- p2) (λ _, [p1 ◁ ty1'])).
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

  Lemma type_deref_instr {E L} ty ty1 ty1' p :
    ty.(ty_size) = 1%nat → (⊢ typed_read E L ty1 ty ty1') →
    (⊢ typed_instruction E L [p ◁ ty1] (!p) (λ v, [p ◁ ty1'; v ◁ ty])).
  Proof.
    iIntros (Hsz Hread tid) "#LFT #TIME #HE Htl HL Hp".
    rewrite tctx_interp_singleton. wp_bind p. iApply (wp_hasty with "Hp").
    iIntros (depth v) "#Hdepth % Hown".
    rewrite typed_read_eq in Hread.
    iMod (Hread with "[] LFT HE Htl HL Hown") as
        (l vl q) "(% & Hl & Hown & Hclose)"; first done.
    subst v. iDestruct (ty_size_eq with "Hown") as "#>%". rewrite ->Hsz in *.
    destruct vl as [|v [|]]; try done.
    rewrite heap_mapsto_vec_singleton. iApply wp_fupd. wp_read.
    iMod ("Hclose" with "Hl") as "($ & $ & Hown2)".
    rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
    iSplitR "Hown"; eauto.
  Qed.

  Lemma type_deref {E L} ty1 C T T' ty ty1' x p e:
    Closed (x :b: []) e →
    tctx_extract_hasty E L p ty1 T T' →
    (⊢ typed_read E L ty1 ty ty1') →
    ty.(ty_size) = 1%nat →
    (∀ (v : val), typed_body E L C ((p ◁ ty1') :: (v ◁ ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. by iApply type_let; [apply type_deref_instr|solve_typing|]. Qed.

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
    ⊢ typed_instruction E L [p1 ◁ ty1; p2 ◁ ty2] (p1 <-{n} !p2)
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
  Proof. iIntros. by iApply type_seq; first eapply (type_memcpy_instr ty ty1 ty1'). Qed. *)
End typing_rules. 
