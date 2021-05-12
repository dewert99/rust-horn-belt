From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context.
Set Default Proof Using "Type".

Section typing.
  Context `{!typeG Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body {𝔄l} (E: elctx) (L: llctx)
    (C: cctx) (T: tctx 𝔄l) (e: expr) (pre: predl 𝔄l) : iProp Σ :=
    ∀tid vπl, lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ cctx_interp tid C -∗ tctx_interp tid T vπl -∗
      ⟨π, pre (vπl -$ π)⟩ -∗ WP e {{ _, cont_postcondition }}.
  Global Arguments typed_body {_} _ _ _ _ _%E _%type.

  Lemma typed_body_eq {𝔄l} pre pre' E L C (T: _ 𝔄l) e :
    pre = pre' → typed_body E L C T e pre' -∗ typed_body E L C T e pre.
  Proof. by move=> ->. Qed.

  Lemma typed_body_impl {𝔄l} (pre pre': predl 𝔄l) E L C T e :
    (∀vl, pre vl → pre' vl) → typed_body E L C T e pre' -∗ typed_body E L C T e pre.
  Proof.
    move=> Imp. rewrite /typed_body. do 14 f_equiv=>/=. do 2 f_equiv. move=> ?.
    by apply Imp.
  Qed.

  Lemma typed_body_tctx_incl {𝔄l 𝔅l} (T: _ 𝔄l) (T': _ 𝔅l) tr pre E L C e :
    tctx_incl E L T T' tr →
    typed_body E L C T' e pre -∗ typed_body E L C T e (tr pre).
  Proof.
    iIntros (In) "e". iIntros (??) "#LFT TIME #PROPH #UNIQ #E Na L C T Obs".
    iMod (In with "LFT PROPH UNIQ E L T Obs") as (?) "(L & T' & Obs)".
    iApply ("e" with "LFT TIME PROPH UNIQ E Na L C T' Obs").
  Qed.

  (** Instruction *)
  Definition typed_instr {𝔄l 𝔅l} (E: elctx) (L: llctx)
    (T: tctx 𝔄l) (e: expr) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) : iProp Σ :=
    ∀tid postπ vπl, lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      na_own tid ⊤ -∗ llctx_interp L 1 -∗ tctx_interp tid T vπl -∗
      ⟨π, tr (postπ π) (vπl -$ π)⟩ -∗ WP e {{ v, ∃vπl', na_own tid ⊤ ∗
        llctx_interp L 1 ∗ tctx_interp tid (T' v) vπl' ∗ ⟨π, postπ π (vπl' -$ π)⟩ }}.
  Global Arguments typed_instr {_ _} _ _ _ _%E _ _%type.

  (** Writing and Reading *)

  Definition typed_write {𝔄 𝔅 𝔄' 𝔅'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (tyb': type 𝔅') (gt: 𝔄 → 𝔅) (st: 𝔄 → 𝔅' → 𝔄') : Prop :=
    tyb.(ty_size) = tyb'.(ty_size) ∧ ∀vπ d v tid qL,
    lft_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
    llctx_interp L qL -∗ ty.(ty_own) vπ d tid [v] ={⊤}=∗ ∃l: loc,
      ⌜v = #l⌝ ∗ ▷ l ↦∗: tyb.(ty_own) (gt ∘ vπ) d tid ∗
      ∀wπ db', ▷ l ↦∗: tyb'.(ty_own) wπ db' tid -∗ ⧖(S db') ={⊤}=∗
        llctx_interp L qL ∗ ty'.(ty_own) (st ∘ vπ ⊛ wπ) (S db') tid [v].
  Global Arguments typed_write {_ _ _ _} _ _ _%T _%T _%T _%T _%type _%type.

  (* Technically speaking, we could remvoe the vl quantifiaction here and use
     mapsto_pred instead (i.e., l ↦∗: ty.(ty_own) tid). However, that would
     make work for some of the provers way harder, since they'd have to show
     that nobody could possibly have changed the vl (because only half the
     fraction was given). So we go with the definition that is easier to prove. *)
  Definition typed_read {𝔄 𝔅 𝔄'} (E: elctx) (L: llctx) (ty: type 𝔄) (tyb: type 𝔅)
    (ty': type 𝔄') (gt: 𝔄 → 𝔅) (st: 𝔄 → 𝔄') : Prop := ∀vπ d v tid qL,
    lft_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗ llctx_interp L qL -∗
    ty.(ty_own) vπ d tid [v] ={⊤}=∗ ∃(l: loc) vl q, ⌜v = #l⌝ ∗
      l ↦∗{q} vl ∗ ▷ tyb.(ty_own) (gt ∘ vπ) d tid vl ∗ (l ↦∗{q} vl ={⊤}=∗
        na_own tid ⊤ ∗ llctx_interp L qL ∗ ty'.(ty_own) (st ∘ vπ) d tid [v]).
  Global Arguments typed_read {_ _ _} _ _ _%T _%T _%T _ _%type.

  Definition typed_instr_ty {𝔄l 𝔅} (E: elctx) (L: llctx)
    (T: tctx 𝔄l) (e: expr) (ty: type 𝔅) (tr: pred' 𝔅 → predl 𝔄l) : iProp Σ :=
    typed_instr E L T e (λ v, +[v ◁ ty]) (λ post al, tr (λ b, post -[b]) al).
  Global Arguments typed_instr_ty {_ _} _ _ _ _%E _%T _%type.

  Definition typed_val {𝔄} (v: val) (ty: type 𝔄) (tr: pred' (pred' 𝔄)) : Prop :=
    ∀E L, ⊢ typed_instr_ty E L +[] (of_val v) ty (λ post _, tr post).
  Global Arguments typed_val {_} _%V _%T _%type.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type {𝔄l} E L C (T: tctx 𝔄l) e p:
    typed_body E L C T e p -∗ typed_body E L C T e p.
  Proof. done. Qed.

  (* TODO: Proof a version of this that substitutes into a compatible context...
     if we really want to do that. *)
  Lemma type_equivalize_lft {𝔄l} E L C (T: _ 𝔄l) κ κ' e pre :
    typed_body (κ ⊑ₑ κ' :: κ' ⊑ₑ κ :: E) L C T e pre -∗
    typed_body E (κ ⊑ₗ [κ'] :: L) C T e pre.
  Proof.
    iIntros "e" (??) "#LFT TIME PROPH UNIQ E Na [Eq L] C T".
    iMod (lctx_equalize_lft with "LFT Eq") as "[In In']".
    iApply ("e" with "LFT TIME PROPH UNIQ [$E $In $In'] Na L C T").
  Qed.

  Lemma type_let' {𝔄l 𝔅l ℭl} E L (T1: _ 𝔄l) (T2: _ → _ 𝔅l) (T: _ ℭl) C xb e e' tr pre:
    Closed (xb :b: []) e' → typed_instr E L T1 e T2 tr -∗
    (∀v: val, typed_body E L C (T2 v h++ T) (subst' xb v e') pre) -∗
    typed_body E L C (T1 h++ T) (let: xb := e in e')
      (λ acl, let '(al, cl) := psep acl in tr (λ bl, pre (bl -++ cl)) al).
  Proof.
    iIntros (?) "e e'". iIntros (tid vπl2). move: (papp_ex vπl2)=> [vπl[vπl'->]].
    iIntros "#LFT #TIME #PROPH #UNIQ #E Na L C [T1 T] Obs". wp_bind e.
    iApply (wp_wand with "[e L T1 Na Obs]").
    { iApply ("e" with "LFT TIME PROPH UNIQ E Na L T1").
      iApply proph_obs_eq; [|done]=> ?. by rewrite /trans_upper papply_app papp_sepl. }
    iIntros (v). iIntros "(%vπ & Na & L & T2 & ?)". wp_let. iCombine "T2 T" as "T2T".
    iApply ("e'" $! v tid (vπ -++ vπl') with "LFT TIME PROPH UNIQ E Na L C T2T").
    iApply proph_obs_eq; [|done]=>/= ?. by rewrite papply_app papp_sepr.
  Qed.

  (* We do not make the [typed_instr] hypothesis part of the
     Iris hypotheses, because we want to preserve the order of the
     hypotheses. The is important, since proving [typed_instr]
     will instantiate [T1] and [T2], and hence we know what to search
     for the following hypothesis. *)
  Lemma type_let {𝔄l 𝔅l ℭl 𝔇l} (T1: _ 𝔄l) (T2: _ → _ 𝔅l)
    (T: _ ℭl) (T': _ 𝔇l) E L C xb e e' tr tr' pre (tr_res: predl _) :
    Closed (xb :b: []) e' → (⊢ typed_instr E L T1 e T2 tr) →
    tctx_extract_ctx E L T1 T T' tr' → tr_res = tr' (trans_upper tr pre) →
    (∀v: val, typed_body E L C (T2 v h++ T') (subst' xb v e') pre) -∗
    typed_body E L C T (let: xb := e in e') tr_res.
  Proof.
    rewrite /tctx_extract_ctx=> ??? ->.
    rewrite -typed_body_tctx_incl; [|done]. by iApply type_let'.
  Qed.

  Lemma type_seq {𝔄l 𝔅l ℭl 𝔇l} (T1: _ 𝔄l) (T2: _ 𝔅l)
    (T: _ ℭl) (T': _ 𝔇l) E L C e e' tr tr' pre (tr_res: predl _) :
    Closed [] e' → (⊢ typed_instr E L T1 e (const T2) tr) →
    tctx_extract_ctx E L T1 T T' tr' → tr_res = tr' (trans_upper tr pre) →
    typed_body E L C (T2 h++ T') e' pre -∗ typed_body E L C T (e;; e') tr_res.
  Proof. iIntros. iApply (type_let _ (const T2))=>//. by iIntros. Qed.

  Lemma type_newlft {𝔄l} κs E L C (T: _ 𝔄l) e pre :
    Closed [] e → (∀κ, typed_body E (κ ⊑ₗ κs :: L) C T e pre) -∗
    typed_body E L C T (Newlft;; e) pre.
  Proof.
    iIntros (?) "e". iIntros (??) "#LFT TIME PROPH UNIQ E Na L C T Obs".
    iMod (lft_create with "LFT") as (Λ) "[Λ #Hinh]"; [done|].
    set κ' := lft_intersect_list κs. wp_seq.
    iApply ("e" $! κ' ⊓ Λ with "LFT TIME PROPH UNIQ E Na [Λ $L] C T Obs").
    rewrite /llctx_interp. iExists Λ. iFrame "Λ". by iSplit.
  Qed.

  Lemma type_endlft {𝔄l} (T T': _ 𝔄l) κ κs pre e E L C :
    Closed [] e → UnblockTctx E L κ T T' →
    typed_body E L C T' e pre -∗ typed_body E (κ ⊑ₗ κs :: L) C T (Endlft;; e) pre.
  Proof.
    iIntros (? Un) "e". iIntros (??) "#LFT #TIME PROPH UNIQ #E Na
    [(%&%& κ' & To†) L] C T Obs". iSpecialize ("To†" with "κ'").
    wp_bind Skip. iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); [done|].
    iApply (wp_step_fupd with "To†"); [set_solver|]. wp_seq. iIntros "#? !>".
    wp_seq. wp_bind Skip. iMod (Un with "LFT E L [] T") as (d vπl') "[⧖ ToT']".
    { simpl in *. subst. rewrite -lft_dead_or. by iRight. }
    iApply (wp_step_fupdN_persist_time_rcpt _ _ ∅ with "TIME ⧖ [ToT']")=>//.
    { iApply step_fupdN_with_emp. by rewrite difference_empty_L. } wp_seq.
    iIntros "(L & Obs' & T') !>". wp_seq. iCombine "Obs Obs'" as "?".
    iApply ("e" with "LFT TIME PROPH UNIQ E Na L C T'").
    by iApply proph_obs_impl; [|done]=> ?[?<-].
  Qed.

  Lemma type_path_instr {𝔄} p (ty: _ 𝔄) E L :
    ⊢ typed_instr_ty E L +[p ◁ ty] p ty (λ post '-[v], post v).
  Proof.
    iIntros (??[vπ[]]) "_ _ _ _ _ $$ [T _] Obs". iApply (wp_hasty with "T").
    iIntros (v d _) "??". iExists -[vπ]. do 2 (iSplit; [|done]). iExists v, d.
    rewrite eval_path_of_val. by iFrame.
  Qed.

  Lemma type_letpath {𝔄 𝔅l ℭl} E L (ty: _ 𝔄) C (T: _ 𝔅l) (T': _ ℭl) x p e tr pre :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' tr →
    (∀v: val, typed_body E L C (v ◁ ty +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := p in e) (tr pre).
  Proof.
    iIntros. iApply type_let; [by apply (@type_path_instr 𝔄)|done| |done].
    f_equal. fun_ext. by case.
  Qed.

  Lemma type_assign_instr {𝔄 𝔅 𝔄' 𝔅'} (ty: _ 𝔄) (tyb: _ 𝔅)
    (ty': _ 𝔄') (tyb': _ 𝔅') gt st Φ p pb E L :
    typed_write E L ty tyb ty' tyb' gt st → leak E L tyb Φ →
    ⊢ typed_instr E L +[p ◁ ty; pb ◁ tyb'] (p <- pb) (λ _, +[p ◁ ty'])
      (λ post '-[a; b], Φ (gt a) → post -[st a b])%type.
  Proof.
    iIntros ([Eq Wrt] Lk ?? (vπ & wπ &[]))
      "#LFT #TIME PROPH UNIQ #E $ [L L'] (p & pb & _) Obs".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (???) "⧖ ty".
    iMod (Wrt with "LFT UNIQ E L ty") as (? ->) "[(%vl & ↦ & tyb) Toty']".
    iDestruct (ty_size_eq with "tyb") as "#>%Sz".
    iDestruct (Lk (⊤ ∖ (⊤ ∖ ↑lftN ∖ ↑prophN)) with "LFT PROPH E L' tyb") as "ToObs";
    [set_solver|]. iApply (wp_step_fupdN_persist_time_rcpt _ _ (⊤ ∖ ↑lftN ∖ ↑prophN)
    with "TIME ⧖ [ToObs]")=>//. { by iApply step_fupdN_with_emp. }
    wp_bind pb. iApply (wp_hasty with "pb"). iIntros (vb db ?) "#⧖' tyb'".
    iDestruct (ty_size_eq with "tyb'") as %Sz'. move: Sz. rewrite Eq -Sz' /=.
    case vl=> [|?[|]]=>// ?. iApply (wp_persist_time_rcpt with "TIME ⧖'")=>//.
    { solve_ndisj. } rewrite heap_mapsto_vec_singleton.
    wp_write. iIntros "#⧖S [Obs' $]". iCombine "Obs Obs'" as "Obs".
    iMod ("Toty'" with "[↦ tyb'] ⧖S") as "[$ ty']".
    { iExists [vb]. rewrite -heap_mapsto_vec_singleton. iFrame. }
    iExists -[st ∘ vπ ⊛ wπ]. iSplitR "Obs".
    - rewrite right_id tctx_hasty_val'; [|done]. iExists (S db). by iFrame.
    - iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp.
  Qed.

  Lemma type_assign {𝔄 𝔅 𝔄' 𝔅' 𝔄l 𝔅l} (ty: _ 𝔄) (tyb: _ 𝔅) (ty': _ 𝔄')
    (tyb': _ 𝔅') gt st Φ p pb E L C (T: _ 𝔄l) (T': _ 𝔅l) tr e pre:
    Closed [] e → tctx_extract_ctx E L +[p ◁ ty; pb ◁ tyb'] T T' tr →
    typed_write E L ty tyb ty' tyb' gt st → leak E L tyb Φ →
    typed_body E L C (p ◁ ty' +:: T') e pre -∗
    typed_body E L C T (p <- pb;; e)
      (tr (λ '(a -:: b -:: bl), Φ (gt a) → pre (st a b -:: bl)))%type.
  Proof.
    iIntros. iApply type_seq; [by eapply type_assign_instr|done| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

  Lemma type_deref_instr {𝔄 𝔅 𝔄'} (ty: _ 𝔄) (tyb: _ 𝔅) (ty': _ 𝔄') gt st p E L :
    tyb.(ty_size) = 1%nat → typed_read E L ty tyb ty' gt st →
    ⊢ typed_instr E L +[p ◁ ty] (!p) (λ v, +[v ◁ tyb; p ◁ ty'])
      (λ post '-[a], post -[gt a; st a]).
  Proof.
    move=> Sz Rd. iIntros (??[vπ[]]) "LFT _ _ _ E Na L [p _] ?".
    wp_bind p. iApply (wp_hasty with "p"). iIntros (???) "#? ty".
    iMod (Rd with "LFT E Na L ty") as (l vl q ->) "(↦ & tyb & Toty')".
    iDestruct (ty_size_eq with "tyb") as "#>%Len". rewrite Sz in Len.
    case vl as [|v[|]]=>//. rewrite heap_mapsto_vec_singleton. iApply wp_fupd.
    wp_read. iMod ("Toty'" with "↦") as "($&$& ty')". iModIntro.
    iExists -[gt ∘ vπ; st ∘ vπ]. iSplit; [|done]. rewrite right_id
    tctx_hasty_val tctx_hasty_val'; [|done]. iSplitL "tyb"; iExists d; by iSplit.
  Qed.

  Lemma type_deref {𝔄 𝔅 𝔄' 𝔄l 𝔅l} (ty: _ 𝔄) (tyb: _ 𝔅) (ty': _ 𝔄') gt st
    (T: _ 𝔄l) (T': _ 𝔅l) p x e tr pre E L C :
    Closed (x :b: []) e → tctx_extract_ctx E L +[p ◁ ty] T T' tr →
    typed_read E L ty tyb ty' gt st → tyb.(ty_size) = 1%nat →
    (∀v: val, typed_body E L C (v ◁ tyb +:: p ◁ ty' +:: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := !p in e)
      (tr (λ '(a -:: al), pre (gt a -:: st a -:: al))).
  Proof.
    iIntros. iApply type_let; [by eapply type_deref_instr|done| |done].
    f_equal. fun_ext. by case.
  Qed.

  Lemma type_memcpy_instr {𝔄 𝔄' 𝔅 𝔅' ℭ ℭ'} (tyw: _ 𝔄) (tyw': _ 𝔄') (tyr: _ 𝔅)
    (tyr': _ 𝔅') (tyb: _ ℭ) (tyb': _ ℭ') gtw stw gtr str Φ (n: Z) pw pr E L :
    typed_write E L tyw tyb tyw' tyb' gtw stw → leak E L tyb Φ →
    typed_read E L tyr tyb' tyr' gtr str → n = tyb'.(ty_size) →
    ⊢ typed_instr E L +[pw ◁ tyw; pr ◁ tyr] (pw <-{n} !pr)
      (λ _, +[pw ◁ tyw'; pr ◁ tyr'])
      (λ post '-[a; b], Φ (gtw a) → post -[stw a (gtr b); str b])%type.
  Proof.
    iIntros ([Eq Wrt] Lk Rd ->??(?&?&[]))
      "/= #LFT #TIME PROPH UNIQ #E Na [[L L'] L''] (pw & pr &_) Obs".
    wp_bind pw. iApply (wp_hasty with "pw"). iIntros (???) "⧖ tyw".
    iMod (Wrt with "LFT UNIQ E L tyw") as (?->) "[(% & >↦ & tyb) Totyw]".
    wp_bind pr. iApply (wp_hasty with "pr"). iIntros (???) "#⧖' tyr".
    iMod (Rd with "LFT E Na L' tyr") as (? vlb ?->) "(↦' & tyb' & Totyr')".
    iDestruct (ty_size_eq with "tyb") as "#>%".
    iDestruct (ty_size_eq with "tyb'") as "#>%".
    iDestruct (Lk (⊤ ∖ (⊤ ∖ ↑lftN ∖ ↑prophN)) with "LFT PROPH E L'' tyb") as "ToObs";
    [set_solver|]. iApply (wp_step_fupdN_persist_time_rcpt _ _ (⊤ ∖ ↑lftN ∖ ↑prophN)
    with "TIME ⧖ [ToObs]")=>//; [by iApply step_fupdN_with_emp|].
    iApply (wp_persist_time_rcpt with "TIME ⧖'"); [solve_ndisj|].
    iApply (wp_memcpy with "[$↦ $↦']"); [congruence|congruence|]. iNext.
    iIntros "[↦ ↦'] #⧖'S [Obs' $]". iCombine "Obs Obs'" as "Obs".
    iMod ("Totyw" with "[↦ tyb'] ⧖'S") as "[$ tyw']". { iExists vlb. iFrame. }
    iMod ("Totyr'" with "↦'") as "($&$& tyr')". iModIntro. iExists -[_; _].
    iSplit; [rewrite right_id|].
    - iSplitL "tyw'"; (rewrite tctx_hasty_val'; [|done]); iExists _; by iFrame.
    - iApply proph_obs_impl; [|done]=>/= ?[Imp ?]. by apply Imp.
  Qed.

  Lemma type_memcpy {𝔄 𝔄' 𝔅 𝔅' ℭ ℭ' 𝔄l 𝔅l} (tyw: _ 𝔄) (tyw': _ 𝔄') (tyr: _ 𝔅)
    (tyr': _ 𝔅') (tyb: _ ℭ) (tyb': _ ℭ') gtw stw gtr str Φ
    (n: Z) pw pr E L C (T: _ 𝔄l) (T': _ 𝔅l) e tr pre :
    Closed [] e → tctx_extract_ctx E L +[pw ◁ tyw; pr ◁ tyr] T T' tr →
    typed_write E L tyw tyb tyw' tyb' gtw stw → leak E L tyb Φ →
    typed_read E L tyr tyb' tyr' gtr str → n = tyb'.(ty_size) →
    typed_body E L C (pw ◁ tyw' +:: pr ◁ tyr' +:: T') e pre -∗
    typed_body E L C T (pw <-{n} !pr;; e) (tr (λ '(a -:: b -:: bl),
      Φ (gtw a) → pre (stw a (gtr b) -:: str b -:: bl)))%type.
  Proof.
    iIntros. iApply type_seq; [by eapply type_memcpy_instr|done| |done].
    f_equal. fun_ext. by case=> [?[??]].
  Qed.

End typing.
