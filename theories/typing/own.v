From lrust.lang.lib Require Import memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import uninit type_context programs.
Set Default Proof Using "Type".
Open Scope nat_scope.

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: tlist syn_type).

Section own.
  Context `{!typeG Σ}.

  Definition freeable_sz (n sz: nat) (l: loc) : iProp Σ :=
    match sz, n with 0, _ => True | _, 0 => False |
      sz, n => †{pos_to_Qp (Pos.of_nat sz) / pos_to_Qp (Pos.of_nat n)}l…sz end.
  Arguments freeable_sz: simpl never.

  Global Instance freeable_sz_timeless n sz l : Timeless (freeable_sz n sz l).
  Proof. case sz, n; apply _. Qed.

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ †{1}l…n ∨ ⌜Z.of_nat n = 0⌝.
  Proof.
    case n=> [|n']. { iSplit; iIntros; by [iRight|]. }
    have ->: Z.of_nat (S n') = 0 ↔ False by done.
    by rewrite right_id /freeable_sz Qp_div_diag.
  Qed.

  Lemma freeable_sz_full_S n l : freeable_sz (S n) (S n) l ⊣⊢ †{1}l…(S n).
  Proof.
    rewrite freeable_sz_full. iSplit; [|iIntros; by iLeft]. by iIntros "[$|%]".
  Qed.

  Lemma freeable_sz_split n sz sz' l :
    freeable_sz n sz l ∗ freeable_sz n sz' (l +ₗ sz) ⊣⊢
    freeable_sz n (sz + sz') l.
  Proof.
    case sz; [|case sz'; [|rewrite /freeable_sz; case n]]=>/= *.
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit; by [iIntros "[??]"|iIntros].
    - rewrite heap_freeable_op_eq. f_equiv.
      by rewrite -Qp_div_add_distr pos_to_Qp_add -Nat2Pos.inj_add.
  Qed.

  (* Make sure 'simpl' doesn't unfold. *)
  Global Opaque freeable_sz.

  Program Definition own_ptr {𝔄} (n: nat) (ty: type 𝔄) : type 𝔄 := {|
    ty_size := 1;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
    ty_own vπ d tid vl := [S d' := d] [loc[l] := vl]
      ▷ l ↦∗: ty.(ty_own) vπ d' tid ∗ freeable_sz n ty.(ty_size) l;
    ty_shr vπ d κ tid l := [S d' := d]
      ∃l': loc, &frac{κ}(λ q', l ↦{q'} #l') ∗ ▷ ty.(ty_shr) vπ d' κ tid l';
  |}%I.
  Next Obligation.
    move=> ????[|?]*; [by iIntros|]. rewrite/= by_just_loc_ex. by iIntros "[%[->?]]".
  Qed.
  Next Obligation.
    move=> ???[|?][|?] */=; try (by iIntros); [lia|]. do 7 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ???[|?][|?] */=; try (by iIntros); [lia|]. do 4 f_equiv.
    apply ty_shr_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ??????[|?]*; [by iIntros|]. iIntros "#? [%l[??]]". iExists l.
    iSplit; by [iApply frac_bor_shorten|iApply ty_shr_lft_mono].
  Qed.
  Next Obligation.
    move=> ????? d *. iIntros "#LFT #In Bor Tok".
    iMod (bor_exists with "LFT Bor") as (?) "Bor"; [done|].
    iMod (bor_sep with "LFT Bor") as "[Mt Bor]"; [done|].
    move: d=> [|d]; [by iMod (bor_persistent with "LFT Bor Tok") as "[>[]_]"|]=>/=.
    rewrite {1}by_just_loc_ex. iMod (bor_exists with "LFT Bor") as (l) "Bor"; [done|].
    iMod (bor_sep_persistent with "LFT Bor Tok") as "(>-> & Bor & Tok)"; [done|].
    rewrite heap_mapsto_vec_singleton.
    iMod (bor_sep with "LFT Bor") as "[Bor _]"; [done|].
    iMod (bor_fracture (λ q, _ ↦{q} _)%I with "LFT Mt") as "Mt"; [done|].
    iMod (bor_later_tok with "LFT Bor Tok") as "Bor"; [done|].
    iIntros "!>!>!>". iMod "Bor" as "[Bor Tok]".
    iMod (ty_share with "LFT In Bor Tok") as "Upd"; [done|]. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iIntros ">[?$] !>". iExists l. iFrame.
  Qed.
  Next Obligation.
    move=> ?????[|?]*; [by iIntros|]. rewrite/= {1}by_just_loc_ex.
    iIntros "#LFT #In (%&->& [%[Mt Own]] & Fr) Tok !>!>!>".
    iDestruct (ty_own_proph with "LFT In Own Tok") as "Upd"; [done|].
    iApply (step_fupdN_wand with "Upd"). iIntros ">(%ξl & %q &%& PTok & Close) !>".
    iExists ξl, q. iSplit; [done|]. iFrame "PTok Fr". iIntros "PTok".
    iMod ("Close" with "PTok") as "[?$]". iExists vl. by iFrame.
  Qed.
  Next Obligation.
    move=> ?????[|?]*/=; [by iIntros|]. iIntros "#LFT #In #In' [%l[Mt Shr]] Tok !>!>".
    iDestruct (ty_shr_proph with "LFT In In' Shr Tok") as "> Upd"; [done|].
    iIntros "!>!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%ξl & %q &%& PTok & Close) !>". iExists ξl, q. iSplit; [done|].
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[Shr $]".
    iExists l. by iFrame.
  Qed.

  Global Instance own_type_contr 𝔄 n : TypeContractive (@own_ptr 𝔄 n).
  Proof.
    split; [by apply type_lft_morph_id_like|done| |].
    - move=>/= > ->*. do 9 (f_contractive || f_equiv). by simpl in *.
    - move=>/= > *. do 6 (f_contractive || f_equiv). by simpl in *.
  Qed.
  Global Instance own_ne 𝔄 n : NonExpansive (@own_ptr 𝔄 n).
  Proof. solve_ne_type. Qed.

  Global Instance own_send 𝔄 n ty : Send ty → Send (@own_ptr 𝔄 n ty).
  Proof. move=> >/=. by do 9 f_equiv. Qed.

  Global Instance own_sync 𝔄 n ty : Sync ty → Sync (@own_ptr 𝔄 n ty).
  Proof. move=> >/=. by do 6 f_equiv. Qed.

  Lemma own_type_incl {𝔄 𝔅} n (f: 𝔄 → 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗ type_incl (own_ptr n ty1) (own_ptr n ty2) f.
  Proof.
    iIntros "#(%Eq &?& InOwn & InShr)". do 2 (iSplit; [done|]). iSplit; iModIntro.
    - iIntros (?[|?]??); [done|]. rewrite/= {1}by_just_loc_ex Eq.
      iIntros "(%&->& Mt &$)". iApply (heap_mapsto_pred_wand with "Mt"). iApply "InOwn".
    - iIntros (?[|?]???); [done|]. iIntros "#[%l'[??]]". iExists l'.
      iSplit; [done|]. by iApply "InShr".
  Qed.

  Lemma own_subtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (own_ptr n ty) (own_ptr n ty') f.
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply own_type_incl; by [|iApply "Incl"].
  Qed.

  Lemma own_eqtype {𝔄 𝔅} E L n (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (own_ptr n ty) (own_ptr n ty') f g.
  Proof. move=> [??]. split; by apply own_subtype. Qed.

End own.

Section box.
  Context `{!typeG Σ}.

  Definition box {𝔄} (ty: type 𝔄) : type 𝔄 := own_ptr ty.(ty_size) ty.

  Global Instance box_ne 𝔄 : NonExpansive (@box 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance box_type_contr 𝔄 : TypeContractive (@box 𝔄).
  Proof.
    split; [by apply type_lft_morph_id_like|done| |].
    - move=>/= > ->*. do 9 (f_contractive || f_equiv). by simpl in *.
    - move=>/= *. do 6 (f_contractive || f_equiv). by simpl in *.
  Qed.

  Lemma box_type_incl {𝔄 𝔅} (f: 𝔄 → 𝔅) ty ty':
    type_incl ty ty' f -∗ type_incl (box ty) (box ty') f.
  Proof.
    iIntros "[%Eq ?]". rewrite /box Eq. iApply own_type_incl. by iSplit.
  Qed.

  Lemma box_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (box ty) (box ty') f.
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #?". iApply box_type_incl. by iApply "Incl".
  Qed.

  Lemma box_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (box ty) (box ty') f g.
  Proof. move=> [??]. split; by apply box_subtype. Qed.

End box.

Section typing.
  Context `{!typeG Σ}.

  Lemma write_own {𝔄 𝔅} (ty: _ 𝔄) (ty': _ 𝔅) n E L :
    ty.(ty_size) = ty'.(ty_size) →
    typed_write E L (own_ptr n ty') ty (own_ptr n ty) (λ _ a, a).
  Proof.
    iIntros (Sz ?[|?]???) "_ _ _ $ own"; [done|]. setoid_rewrite by_just_loc_ex at 1.
    iDestruct "own" as (l[=->]) "[(%vl & >Mt & ty') Fr]". rewrite Sz.
    iDestruct (ty_size_eq with "ty'") as ">%". iModIntro. iExists l, vl.
    iSplit; [done|]. iFrame "Mt". iIntros (??) "$ ? !>". by rewrite Sz.
  Qed.

  Lemma read_own_copy {𝔄} (ty: _ 𝔄) n E L :
    Copy ty → typed_read E L (own_ptr n ty) ty (own_ptr n ty) id id.
  Proof.
    move=> ??[|?]???; iIntros "_ _ $$ own"=>//=. setoid_rewrite by_just_loc_ex at 1.
    iDestruct "own" as (l[=->]) "[(%vl & >Mt & ty) Fr]". iModIntro.
    iExists l, vl, 1%Qp. iSplit; [done|]. iFrame "Mt Fr". iSplit.
    { iApply ty_own_depth_mono; [|done]. lia. } iIntros "? !>!>". iExists vl. iFrame.
  Qed.

  Lemma read_own_move {𝔄} (ty: _ 𝔄) n E L :
    typed_read E L (own_ptr n ty) ty (own_ptr n (↯ ty.(ty_size))) id unique.
  Proof.
    move=> ?[|?]???; iIntros "_ _ $$ own"=>//. setoid_rewrite by_just_loc_ex at 1.
    iDestruct "own" as (l[=->]) "[(%vl & >Mt & ty) Fr]".
    iDestruct (ty_size_eq with "ty") as "#>%". iModIntro.
    iExists l, vl, 1%Qp. iSplit; [done|]. iFrame "Mt Fr". iSplitL "ty".
    { iApply ty_own_depth_mono; [|done]. lia. } iIntros "?!>!>". iExists vl. by iSplit.
  Qed.

  Lemma type_new_instr n E L :
    (0 ≤ n)%Z → let n' := Z.to_nat n in
    ⊢ typed_instr_ty E L +[] (new [ #n])%E (own_ptr n' (↯ n')) (λ post _, post ()).
  Proof.
    iIntros (?????) "_ TIME _ _ _ $$ _ ?". iMod persist_time_rcpt_0 as "Time".
    iApply (wp_persist_time_rcpt with "TIME Time"); [done|].
    iApply wp_new=>//. iIntros "!>" (l) "(Fr & Mt) #Time". iExists -[const ()].
    iSplit; [|done]. rewrite/= right_id (tctx_hasty_val #l).
    iExists 1. iFrame "Time". rewrite/= freeable_sz_full Z2Nat.id; [|done].
    iFrame "Fr". iNext. iExists _. iFrame "Mt". by rewrite repeat_length.
  Qed.

  Lemma type_new {𝔄l} (n: Z) n' x e pre E L C (T: _ 𝔄l) :
    Closed (x :b: []) e → (0 ≤ n)%Z → n' = Z.to_nat n →
    (∀v: val, typed_body E L C (v ◁ own_ptr n' (↯ n') +:: T) (subst' x v e) pre) -∗
    typed_body E L C T (let: x := new [ #n] in e) (λ al, pre (() -:: al)).
  Proof. iIntros. subst. iApply type_let; by [apply type_new_instr|solve_typing]. Qed.

  Lemma type_new_subtype {𝔄 𝔄l} (ty: _ 𝔄) n' (n: Z) (T: _ 𝔄l) f e pre x E L C :
    Closed (x :b: []) e → (0 ≤ n)%Z → n' = Z.to_nat n → subtype E L (↯ n') ty f →
    (∀v: val, typed_body E L C (v ◁ own_ptr n' ty +:: T) (subst' x v e) pre) -∗
    typed_body E L C T (let: x := new [ #n] in e) (λ al, pre (f () -:: al)).
  Proof.
    iIntros (??->Sub) "?". iApply type_let; [by apply type_new_instr|solve_typing| |];
    last first. { iIntros (?). iApply typed_body_tctx_incl;
    [eapply subtype_tctx_incl, own_subtype, Sub|done]. } done.
  Qed.

  Lemma type_delete_instr {𝔄} (ty: _ 𝔄) (n: Z) p E L :
    let n' := ty.(ty_size) in n = Z.of_nat n' →
    ⊢ typed_instr E L +[p ◁ own_ptr n' ty] (delete [ #n; p])%E (λ _, +[])
      (λ post _, post -[]).
  Proof.
    iIntros (?->??[?[]]) "_ TIME _ _ E $$ [p _] #Obs". wp_bind p.
    iApply (wp_hasty with "p"). iIntros (?[|?] _) "? own"; [done|].
    setoid_rewrite by_just_loc_ex. iDestruct "own" as (?[=->]) "[(%& >Mt & ty)?]".
    iDestruct (ty_size_eq with "ty") as "#>%Sz". iApply (wp_delete with "[-]").
    { by rewrite /n' -Sz. } { iFrame "Mt". rewrite Sz. by iApply freeable_sz_full. }
    { iIntros "!>_". iExists -[]. by iSplit. }
  Qed.

  Lemma type_delete {𝔄 𝔄l 𝔅l} (ty: _ 𝔄) n' (n: Z) p e E L C (T: _ 𝔄l) (T': _ 𝔅l) tr pre :
    Closed [] e → tctx_extract_ctx E L +[p ◁ own_ptr n' ty] T T' tr →
    n' = ty.(ty_size) → n = n' → typed_body E L C T' e pre -∗
    typed_body E L C T (delete [ #n; p ];; e) (tr (λ '(_ -:: al), pre al)).
  Proof.
    iIntros (??->?) "?". iApply type_seq; [by eapply type_delete_instr|done| |done].
    f_equal. fun_ext. by case.
  Qed.

  Lemma type_letalloc_1 {𝔄 𝔄l 𝔅l} (ty: _ 𝔄) (x: string) p e
    (T: _ 𝔄l) (T': _ 𝔅l) tr pre E L C :
    Closed [] p → Closed [x] e →
    tctx_extract_ctx E L +[p ◁ ty] T T' tr → ty.(ty_size) = 1 →
    (∀v: val, typed_body E L C (v ◁ own_ptr 1 ty +:: T') (subst x v e) pre) -∗
    typed_body E L C T (letalloc: x <- p in e) (tr pre).
  Proof.
    iIntros (??? Sz) "e". iApply typed_body_eq; last first.
    { iApply type_new; [|done|done|].
      - rewrite /Closed /= !andb_True. split; [done|]. split; [|done].
        split; [apply bool_decide_spec|eapply is_closed_weaken=>//]; set_solver.
      - rewrite -Sz. iIntros (xv) "/=".
        have ->: (subst x xv (x <- p;; e))%E = (xv <- p;; subst x xv e)%E.
        { rewrite /subst /=. repeat f_equal;
          [by rewrite bool_decide_true|eapply is_closed_subst=>//; set_solver]. }
        iApply type_assign; [|solve_typing|by eapply write_own|done].
        apply subst_is_closed; [|done]. apply is_closed_of_val. }
    f_equal. fun_ext. by case.
  Qed.

  Lemma type_letalloc_n {𝔄 𝔅 𝔅' 𝔄l 𝔅l} (ty: _ 𝔄) (tyr: _ 𝔅) (tyr': _ 𝔅')
    gt st (T: _ 𝔄l) (T': _ 𝔅l) tr pre (x: string) p e E L C :
    Closed [] p → Closed [x] e → tctx_extract_ctx E L +[p ◁ tyr] T T' tr →
    typed_read E L tyr ty tyr' gt st →
    (∀v: val, typed_body E L C
      (v ◁ box ty +:: p ◁ tyr' +:: T') (subst x v e) pre) -∗
    typed_body E L C T (letalloc: x <-{ty.(ty_size)} !p in e)
      (tr (λ '(b -:: bl), pre (gt b -:: st b -:: bl))).
  Proof.
    iIntros. iApply typed_body_eq; last first.
    { iApply type_new; [|lia|done|]=>/=.
      - rewrite /Closed /= !andb_True !right_id. split; [done|].
        split; [by apply is_closed_of_val|]. split;
        [apply bool_decide_spec|eapply is_closed_weaken=>//]; set_solver.
      - iIntros (xv). have ->: subst x xv (x <-{ty.(ty_size)} !p;; e)%E =
          (xv <-{ty.(ty_size)} !p;; subst x xv e)%E.
        { rewrite /subst /=. repeat f_equal.
          - eapply (is_closed_subst []); [apply is_closed_of_val|set_solver].
          - by rewrite bool_decide_true.
          - eapply is_closed_subst; [done|set_solver]. } rewrite Nat2Z.id.
        iApply type_memcpy; [|solve_typing| |solve_typing|done|done].
        { apply subst_is_closed; [|done]. apply is_closed_of_val. }
        by apply write_own. } done.
  Qed.

End typing.

Global Hint Resolve own_subtype own_eqtype box_subtype box_eqtype
            write_own read_own_copy : lrust_typing.
(* By setting the priority high, we make sure copying is tried before
   moving. *)
Global Hint Resolve read_own_move | 100 : lrust_typing.
