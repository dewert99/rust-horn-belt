From lrust.lang Require Import memcpy.
From lrust.typing Require Export type_context cont_context.
Set Default Proof Using "Type".

Section typing.
  Context `{!typeG TYPE Ty Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body {As} (E: elctx) (L: llctx)
    (C: cctx) (T: tctx As) (e: expr) (pre: predl As) : iProp Σ :=
    ∀tid vπl, lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ cctx_interp tid C -∗ tctx_interp tid T vπl -∗
      ⟨π, pre (vπl -$ π)⟩ -∗ WP e {{ _, cont_postcondition }}.
  Global Arguments typed_body {_} _ _ _ _ _%E _.

  Lemma typed_body_eq {As} pre pre' E L C (T: _ As) e :
    pre = pre' → typed_body E L C T e pre' -∗ typed_body E L C T e pre.
  Proof. by move=> ->. Qed.

  Lemma typed_body_impl {As} (pre pre': predl As) E L C T e :
    (∀vl, pre vl → pre' vl) → typed_body E L C T e pre' -∗ typed_body E L C T e pre.
  Proof.
    move=> Imp. rewrite /typed_body. do 14 f_equiv=>/=. do 2 f_equiv. move=> ?.
    by apply Imp.
  Qed.

  Lemma typed_body_tctx_incl {As Bs} (T: _ As) (T': _ Bs) tr pre E L C e :
    tctx_incl E L T T' tr →
    typed_body E L C T' e pre -∗ typed_body E L C T e (tr pre).
  Proof.
    iIntros (In) "e". iIntros (??) "#LFT TIME #PROPH #UNIQ #E Na L C T Obs".
    iMod (In with "LFT PROPH UNIQ E L T Obs") as (?) "(L & Obs & T')".
    iApply ("e" with "LFT TIME PROPH UNIQ E Na L C T' Obs").
  Qed.

  (** Instruction *)
  Definition typed_instr {As Bs} (E: elctx) (L: llctx)
    (T: tctx As) (e: expr) (T': val → tctx Bs) (tr: predl_trans As Bs) : iProp Σ :=
    ∀tid postπ vπl, lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ tctx_interp tid T vπl -∗
      ⟨π, tr (postπ π) (vπl -$ π)⟩ -∗ WP e {{ v, ∃vπl', na_own tid ⊤ ∗
        llctx_interp L 1 ∗ tctx_interp tid (T' v) vπl' ∗ ⟨π, postπ π (vπl' -$ π)⟩ }}.
  Global Arguments typed_instr {_ _} _ _ _ _%E _ _.

  (** Writing and Reading *)

  Definition typed_write {A B A'} (E: elctx) (L: llctx) (ty: type A) (tyb: type B)
    (ty': type A') (st: A → B → A') : Prop := ∀vπ d v tid qL,
    lft_ctx -∗ elctx_interp E -∗ llctx_interp L qL -∗ ty.(ty_own) vπ d tid [v] ={⊤}=∗
      ∃(l: loc) vl, ⌜v = #l ∧ length vl = tyb.(ty_size)⌝ ∗ l ↦∗ vl ∗
        ∀wπ db, ▷ l ↦∗: tyb.(ty_own) wπ db tid -∗ ⧖(S db) ={⊤}=∗
          llctx_interp L qL ∗ ty'.(ty_own) (st ∘ vπ ⊛ wπ) (S db) tid [v].
  Global Arguments typed_write {_ _ _} _ _ _%T _%T _%T _.

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

Definition typed_instr_ty `{!typeG TYPE Ty Σ} {As B} (E: elctx) (L: llctx)
  (T: tctx As) (e: expr) (ty: type B) (tr: pred B → predl As) : iProp Σ :=
  typed_instr E L T e (λ v, +[v ◁ ty]) (λ post al, tr (λ b, post -[b]) al).
Global Arguments typed_instr_ty {_ _ _ _ _ _} _ _ _ _%E _%T _.

Definition typed_val `{!typeG TYPE Ty Σ} {A} (v: val) (ty: type A) (tr: pred (pred A)) : Prop :=
  ∀E L, ⊢ typed_instr_ty E L +[] (of_val v) ty (λ post _, tr post).
Global Arguments typed_val {_ _ _ _ _} _%V _%T _.

Section typing_rules.
  Context `{!typeG TYPE Ty Σ}.

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
    iIntros "e" (??) "#LFT TIME PROPH UNIQ E Na [Eq L] C T".
    iMod (lctx_equalize_lft with "LFT Eq") as "[In In']".
    iApply ("e" with "LFT TIME PROPH UNIQ [$E $In $In'] Na L C T").
  Qed.

  Lemma type_let' {As Bs Cs} E L (T1: _ As) (T2: _ → _ Bs) (T: _ Cs) C xb e e' tr pre:
    Closed (xb :b: []) e' → typed_instr E L T1 e T2 tr -∗
    (∀v: val, typed_body E L C (T2 v h++ T) (subst' xb v e') pre) -∗
    typed_body E L C (T1 h++ T) (let: xb := e in e') (trans_upper tr pre).
  Proof.
    iIntros (?) "e e'". iIntros (tid vπl2). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #PROPH #UNIQ #E Na L C [T1 T] Obs". wp_bind e.
    iApply (wp_wand with "[e L T1 Na Obs]").
    { iApply ("e" with "LFT TIME PROPH UNIQ E Na L T1"). iApply proph_obs_eq; [|done]=> ?.
      by rewrite /trans_upper papply_app papp_sepl. }
    iIntros (v). iIntros "(%vπ & Na & L & T2 & ?)". wp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" $! v tid (vπ -++ vπl') with "LFT TIME PROPH UNIQ E Na L C T2T").
    iApply proph_obs_eq; [|done]=>/= ?. by rewrite papply_app papp_sepr.
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
    rewrite /tctx_extract_ctx=> ??? ->.
    rewrite -typed_body_tctx_incl; [|done]. by iApply type_let'.
  Qed.

  Lemma type_seq {As Bs Cs Ds} (T1: _ As) (T2: _ Bs)
    (T: _ Cs) (T': _ Ds) E L C e e' tr tr' pre (tr_res: predl _) :
    Closed [] e' → (⊢ typed_instr E L T1 e (const T2) tr) →
    tctx_extract_ctx E L T1 T T' tr' → tr_res = tr' (trans_upper tr pre) →
    typed_body E L C (T2 h++ T') e' pre -∗ typed_body E L C T (e;; e') tr_res.
  Proof. iIntros. iApply (type_let _ (const T2))=>//. by iIntros. Qed.

  Lemma type_newlft {As} κs E L C (T: _ As) e pre :
    Closed [] e → (∀κ, typed_body E (κ ⊑ₗ κs :: L) C T e pre) -∗
    typed_body E L C T (Newlft;; e) pre.
  Proof.
    iIntros (?) "He". iIntros (??) "#LFT TIME PROPH UNIQ E Na L C T Obs".
    iMod (lft_create with "LFT") as (Λ) "[Tok #Hinh]"; [done|].
    set κ' := lft_intersect_list κs. wp_seq.
    iApply ("He" $! κ' ⊓ Λ with "LFT TIME PROPH UNIQ E Na [Tok $L] C T Obs").
    rewrite /llctx_interp. iExists Λ. iFrame "Tok". by iSplit.
  Qed.

  Lemma type_endlft {As} (T T': _ As) κ κs pre e E L C :
    Closed [] e → UnblockTctx E L κ T T' →
    typed_body E L C T' e pre -∗ typed_body E (κ ⊑ₗ κs :: L) C T (Endlft;; e) pre.
  Proof.
    iIntros (? Un) "e". iIntros (??) "#LFT #TIME PROPH UNIQ #E Na
    [(%&%& Tok & End) L] C T Obs". iSpecialize ("End" with "Tok").
    wp_bind Skip. iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); [done|].
    iApply (wp_step_fupd with "End"); [set_solver|]. wp_seq. iIntros "#Dead !>".
    wp_seq. wp_bind Skip. iMod (Un with "LFT E L [] T") as (d vπl') "[time ToT']".
    { simpl in *. subst. rewrite -lft_dead_or. by iRight. }
    iApply (wp_step_fupdN_persist_time_rcpt _ _ ∅ with "TIME time [ToT']")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L. } wp_seq.
    iIntros "(L & Obs' & T') !>". iDestruct (proph_obs_and with "Obs Obs'") as "?".
    wp_seq. iApply ("e" with "LFT TIME PROPH UNIQ E Na L C T'").
    by iApply proph_obs_impl; [|done]=> ?[?<-].
  Qed.

  Lemma type_path_instr {A} p (ty: _ A) E L :
    ⊢ typed_instr_ty E L +[p ◁ ty] p ty (λ post '(-[v]), post v).
  Proof.
    iIntros (??[vπ[]]) "_ _ _ _ _ $$ [T _] Obs". iApply (wp_hasty with "T").
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

  Lemma type_assign_instr {A B A'} (ty: _ A) (tyb: _ B) (ty': _ A') st p pb E L :
    typed_write E L ty tyb ty' st →
    ⊢ typed_instr E L +[p ◁ ty; pb ◁ tyb] (p <- pb) (λ _, +[p ◁ ty'])
      (λ post '(-[a; b]), post -[st a b]).
  Proof.
    iIntros (Wrt ?? (vπ & wπ &[])) "LFT TIME _ _ E $ L (p & pb & _) Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (???) "_ ty".
    wp_bind pb. iApply (wp_hasty with "pb"). iIntros (vb db ?) "#time tyb".
    iApply wp_fupd. iMod (Wrt with "LFT E L ty") as (? vl (->&Sz)) "[Mt Close]".
    iApply (wp_persist_time_rcpt with "TIME time")=>//.
    iDestruct (ty_size_eq with "tyb") as "%Sz'". move: Sz. rewrite -Sz' /=.
    case vl=> [|?[|]]=>// ?. rewrite heap_mapsto_vec_singleton. wp_write.
    iIntros "#timeS". iMod ("Close" with "[Mt tyb] timeS") as "($ & ty')".
    { iExists [vb]. rewrite -heap_mapsto_vec_singleton. iFrame. }
    iExists (-[st ∘ vπ ⊛ wπ]). iFrame "Obs".
    rewrite right_id tctx_hasty_val'; [|done]. iExists (S db). by iFrame.
  Qed.

  Lemma type_assign {A B A' As Bs} (ty: _ A) (tyb: _ B) (ty': _ A') st p pb E L C
    (T: _ As) (T': _ Bs) tr e pre:
    Closed [] e → tctx_extract_ctx E L +[p ◁ ty; pb ◁ tyb] T T' tr →
    typed_write E L ty tyb ty' st → typed_body E L C (p ◁ ty' +:: T') e pre -∗
    typed_body E L C T (p <- pb;; e) (tr (λ '(a -:: b -:: bl), pre (st a b -:: bl))).
  Proof.
    iIntros. iApply type_seq; [by eapply type_assign_instr|done| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

  Lemma type_deref_instr {A B A'} (ty: _ A) (tyb: _ B) (ty': _ A') gt st p E L :
    tyb.(ty_size) = 1 → typed_read E L ty tyb ty' gt st →
    ⊢ typed_instr E L +[p ◁ ty] (!p) (λ v, +[v ◁ tyb; p ◁ ty'])
      (λ post '(-[a]), post -[gt a; st a]).
  Proof.
    move=> Sz Read. iIntros (??[vπ[]]) "LFT _ _ _ E Na L [p _] ?".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (???) "#? ty".
    iMod (Read with "LFT E Na L ty") as (l vl q ->) "(Mt & tyb & Close)".
    iDestruct (ty_size_eq with "tyb") as "#>%Len". rewrite Sz in Len.
    case vl as [|v[|]]=>//. rewrite heap_mapsto_vec_singleton. iApply wp_fupd.
    wp_read. iMod ("Close" with "Mt") as "($&$& ty')". iModIntro.
    iExists -[gt ∘ vπ; st ∘ vπ]. iSplit; [|done]. rewrite right_id
    tctx_hasty_val tctx_hasty_val'; [|done]. iSplitL "tyb"; iExists d; by iSplit.
  Qed.

  Lemma type_deref {A B A' As Bs} (ty: _ A) (tyb: _ B) (ty': _ A') gt st
    (T: _ As) (T': _ Bs) p x e tr pre E L C :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' tr →
    typed_read E L ty tyb ty' gt st → tyb.(ty_size) = 1 →
    (∀v: val, typed_body E L C (v ◁ tyb +:: p ◁ ty' +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := !p in e)
      (tr (λ '(a -:: al), pre (gt a -:: st a -:: al))).
  Proof.
    iIntros. iApply type_let; [by eapply type_deref_instr|done| |done].
    f_equal. fun_ext. by case.
  Qed.

  Local Lemma type_memcpy_iris {A A' B B' C} (tyw: _ A) (tyw': _ A') (tyr: _ B)
    (tyr': _ B') (tyb: _ C) stw gtr str (n: Z) pw pr vπw vπr E L qL tid :
    n = tyb.(ty_size) →
    typed_write E L tyw tyb tyw' stw → typed_read E L tyr tyb tyr' gtr str →
    {{{ lft_ctx ∗ time_ctx ∗ elctx_interp E ∗ na_own tid ⊤ ∗ llctx_interp L qL ∗
        tctx_interp tid +[pw ◁ tyw; pr ◁ tyr] -[vπw; vπr] }}}
      (pw <-{n} !pr)
    {{{ RET #☠; na_own tid ⊤ ∗ llctx_interp L qL ∗ tctx_interp tid
        +[pw ◁ tyw'; pr ◁ tyr'] -[stw ∘ vπw ⊛ (gtr ∘ vπr); str ∘ vπr] }}}.
  Proof.
    iIntros (-> Wrt Read ?) "(#LFT & #TIME & #E & Na & [L L'] & (pw & pr &_)) ToΦ".
    wp_bind pw. iApply (wp_hasty with "pw"). iIntros (???) "_ tyw".
    wp_bind pr. iApply (wp_hasty with "pr"). iIntros (???) "#time tyr".
    iApply wp_fupd. iMod (Wrt with "LFT E L tyw") as (??[->?]) "[Mtw Closew]".
    iMod (Read with "LFT E Na L' tyr") as (? vlb ?->) "(Mtr & tyb & Closer)".
    iApply (wp_persist_time_rcpt with "TIME time"); [done|].
    iDestruct (ty_size_eq with "tyb") as "#>%".
    iApply (wp_memcpy with "[$Mtw $Mtr]"); [congruence|congruence|]. iNext.
    iIntros "[Mtw Mtr] #timeS". iMod ("Closew" with "[Mtw tyb] timeS") as "[L tyw']".
    { iExists vlb. iFrame. } iMod ("Closer" with "Mtr") as "(Na & L' & tyr')".
    iApply "ToΦ". iFrame "L L' Na". rewrite right_id.
    iSplitL "tyw'"; (rewrite tctx_hasty_val'; [|done]); iExists _; by iFrame.
  Qed.

  Lemma type_memcpy_instr {A A' B B' C} (tyw: _ A) (tyw': _ A') (tyr: _ B)
    (tyr': _ B') (tyb: _ C) stw gtr str (n: Z) pw pr E L :
    n = tyb.(ty_size) → typed_write E L tyw tyb tyw' stw →
    typed_read E L tyr tyb tyr' gtr str →
    ⊢ typed_instr E L +[pw ◁ tyw; pr ◁ tyr] (pw <-{n} !pr)
      (λ _, +[pw ◁ tyw'; pr ◁ tyr']) (λ post '(-[a; b]), post -[stw a (gtr b); str b]).
  Proof.
    iIntros (?????(?&?&[])) "LFT TIME _ _ E Na L T ?".
    iApply (type_memcpy_iris with "[$LFT $TIME $Na $E $L $T]")=>//. iNext.
    iIntros "($&$&?&?&_)". iExists -[_; _]. iFrame.
  Qed.

  Lemma type_memcpy {A A' B B' D As Bs} (tyw: _ A) (tyw': _ A') (tyr: _ B) (tyr': _ B')
    (tyb: _ D) stw gtr str (n: Z) pw pr E L C (T: _ As) (T': _ Bs) e tr pre :
    Closed [] e → tctx_extract_ctx E L +[pw ◁ tyw; pr ◁ tyr] T T' tr →
    typed_write E L tyw tyb tyw' stw → typed_read E L tyr tyb tyr' gtr str →
    n = tyb.(ty_size) → typed_body E L C (pw ◁ tyw' +:: pr ◁ tyr' +:: T') e pre -∗
    typed_body E L C T (pw <-{n} !pr;; e)
      (tr (λ '(a -:: b -:: bl), pre (stw a (gtr b) -:: str b -:: bl))).
  Proof.
    iIntros. iApply type_seq; [by eapply type_memcpy_instr|done| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

End typing_rules.
