From lrust.lang.lib Require Import memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import uninit type_context programs.
Set Default Proof Using "Type".
Open Scope nat_scope.

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

  Program Definition own_ptr {A} (n: nat) (ty: type A) : type A := {|
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
    move=> ???[|?][|?] */=; (try by iIntros); [lia|]. do 7 f_equiv.
    apply ty_own_depth_mono. lia.
  Qed.
  Next Obligation.
    move=> ???[|?][|?] */=; (try by iIntros); [lia|]. do 4 f_equiv.
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
    iApply (step_fupdN_wand with "Upd"). iIntros ">(%ξs & %q &%& PTok & Close) !>".
    iExists ξs, q. iSplit; [done|]. iFrame "PTok Fr". iIntros "PTok".
    iMod ("Close" with "PTok") as "[?$]". iExists vl. by iFrame.
  Qed.
  Next Obligation.
    move=> ?????[|?]*/=; [by iIntros|]. iIntros "#LFT #In #In' [%l[Mt Shr]] Tok !>!>".
    iDestruct (ty_shr_proph with "LFT In In' Shr Tok") as "> Upd"; [done|].
    iIntros "!>!>!>". iApply (step_fupdN_wand with "Upd").
    iIntros ">(%ξs & %q &%& PTok & Close) !>". iExists ξs, q. iSplit; [done|].
    iFrame "PTok". iIntros "PTok". iMod ("Close" with "PTok") as "[Shr $]".
    iExists l. by iFrame.
  Qed.

  Global Instance own_type_contractive A n : TypeContractive (@own_ptr A n).
  Proof.
    split.
    - by apply type_lft_morphism_id_like.
    - done.
    - move=>/= > ->*. do 9 (f_contractive || f_equiv). by simpl in *.
    - move=>/= > *. do 6 (f_contractive || f_equiv). by simpl in *.
  Qed.
  Global Instance own_ne A n : NonExpansive (@own_ptr A n).
  Proof. solve_ne_type. Qed.

  Global Instance own_send A n ty : Send ty → Send (@own_ptr A n ty).
  Proof. move=> >/=. by do 9 f_equiv. Qed.

  Global Instance own_sync A n ty : Sync ty → Sync (@own_ptr A n ty).
  Proof. move=> >/=. by do 6 f_equiv. Qed.

  Lemma own_type_incl {A B} n (f: A → B) ty1 ty2 :
    type_incl f ty1 ty2 -∗ type_incl f (own_ptr n ty1) (own_ptr n ty2).
  Proof.
    iIntros "#(%Eq &?& InOwn & InShr)". do 2 (iSplit; [done|]). iSplit; iModIntro.
    - iIntros (?[|?]??); [done|]. rewrite/= {1}by_just_loc_ex Eq.
      iIntros "(%&->& Mt &$)". iApply (heap_mapsto_pred_wand with "Mt"). iApply "InOwn".
    - iIntros (?[|?]???); [done|]. iIntros "#[%l'[??]]". iExists l'.
      iSplit; [done|]. by iApply "InShr".
  Qed.

  Lemma own_subtype {A B} E L n (f: A → B) ty ty' :
    subtype E L f ty ty' → subtype E L f (own_ptr n ty) (own_ptr n ty').
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply own_type_incl; by [|iApply "Incl"].
  Qed.

  Lemma own_eqtype {A B} E L n (f: A → B) g ty ty' :
    eqtype E L f g ty ty' → eqtype E L f g (own_ptr n ty) (own_ptr n ty').
  Proof. move=> [??]. split; by apply own_subtype. Qed.

End own.

Section box.
  Context `{!typeG Σ}.

  Definition box {A} (ty: type A) : type A := own_ptr ty.(ty_size) ty.

  Global Instance box_type_contractive A : TypeContractive (@box A).
  Proof.
    split.
    - by apply type_lft_morphism_id_like.
    - done.
    - move=>/= > ->*. do 9 (f_contractive || f_equiv). by simpl in *.
    - move=>/= *. do 6 (f_contractive || f_equiv). by simpl in *.
  Qed.
  Global Instance box_ne A : NonExpansive (@box A).
  Proof. solve_ne_type. Qed.

  Lemma box_type_incl {A B} (f: A → B) ty ty':
    type_incl f ty ty' -∗ type_incl f (box ty) (box ty').
  Proof.
    iIntros "[%Eq ?]". rewrite /box Eq. iApply own_type_incl. by iSplit.
  Qed.

  Lemma box_subtype {A B} E L (f: A → B) ty ty' :
    subtype E L f ty ty' → subtype E L f (box ty) (box ty').
  Proof.
    move=> Sub ?. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #?". iApply box_type_incl. by iApply "Incl".
  Qed.

  Lemma box_eqtype {A B} E L (f: A → B) g ty ty' :
    eqtype E L f g ty ty' → eqtype E L f g (box ty) (box ty').
  Proof. move=> [??]. split; by apply box_subtype. Qed.

End box.

Section typing.
  Context `{!typeG Σ}.

(*
  Lemma write_own {E L} ty ty' n :
    ty.(ty_size) = ty'.(ty_size) → ⊢ typed_write E L (own_ptr n ty') ty (own_ptr n ty).
  Proof.
    rewrite typed_write_eq. iIntros (Hsz) "!>".
    iIntros ([[]|] [|depth] tid F qL ?) "_ _ $ Hown"; try done.
    rewrite /= Hsz. iDestruct "Hown" as "[H↦ $]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". auto 10 with iFrame.
  Qed.
*)

  Lemma read_own_copy {A} (ty: _ A) n E L :
    Copy ty → typed_read E L (own_ptr n ty) ty (own_ptr n ty) id id.
  Proof.
    move=> ??[|?]???; iIntros "_ _ $$ own"=>//=. setoid_rewrite by_just_loc_ex at 1.
    iDestruct "own" as (l[=->]) "[(%vl & >Mt & ty) Fr]". iModIntro.
    iExists l, vl, 1%Qp. iSplit; [done|]. iFrame "Mt Fr". iSplit.
    { iApply ty_own_depth_mono; [|done]. lia. } iIntros "? !>!>". iExists vl. iFrame.
  Qed.

  Lemma read_own_move {A} (ty: _ A) n E L :
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
    iIntros (?????) "_ TIME _ $$ _ ?". iMod persistent_time_receipt_0 as "Time".
    iApply (wp_persistent_time_receipt with "TIME Time"); [done|].
    iApply wp_new=>//. iIntros "!>" (l) "(Fr & Mt) #Time". iExists -[const ()].
    iSplit; [|done]. rewrite/= right_id (tctx_hasty_val #l).
    iExists 1. iFrame "Time". rewrite/= freeable_sz_full Z2Nat.id; [|done].
    iFrame "Fr". iNext. iExists _. iFrame "Mt". by rewrite repeat_length.
  Qed.

  Lemma type_new {As} x (n: Z) n' e pre E L C (T: _ As) :
    Closed (x :b: []) e → (0 ≤ n)%Z → n' = Z.to_nat n →
    (∀v: val, typed_body E L C (v ◁ own_ptr n' (↯ n') +:: T) (subst' x v e) pre) -∗
    typed_body E L C T (let: x := new [ #n] in e) (λ al, pre (() -:: al)).
  Proof. iIntros. subst. iApply type_let; by [apply type_new_instr|solve_typing]. Qed.

(*
  Lemma type_new_subtype ty E L C T x (n : Z) e :
    Closed (x :b: []) e →
    0 ≤ n →
    let n' := Z.to_nat n in
    subtype E L (uninit n') ty →
    (∀ (v : val), typed_body E L C ((v ◁ own_ptr n' ty) :: T) (subst' x v e)) -∗
    typed_body E L C T (let: x := new [ #n ] in e).
  Proof.
    iIntros (????) "Htyp". iApply type_let; [by apply type_new_instr|solve_typing|].
    iIntros (v). iApply typed_body_mono; last iApply "Htyp"; try done.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, own_subtype.
  Qed.
*)

  Lemma type_delete_instr {A} (ty: _ A) (n: Z) p E L :
    let n' := ty.(ty_size) in n = n' →
    ⊢ typed_instr E L +[p ◁ own_ptr n' ty] (delete [ #n; p])%E (λ _, +[])
      (λ post _, post -[]).
  Proof.
    iIntros (?->??[?[]]) "_ TIME E $$ [p _] #Obs". wp_bind p.
    iApply (wp_hasty with "p"). iIntros (?[|?] _) "? own"; [done|].
    setoid_rewrite by_just_loc_ex. iDestruct "own" as (?[=->]) "[(%& >Mt & ty)?]".
    iDestruct (ty_size_eq with "ty") as "#>%Sz". iApply (wp_delete with "[-]").
    { by rewrite /n' -Sz. } { iFrame "Mt". rewrite Sz. by iApply freeable_sz_full. }
    { iIntros "!>_". iExists -[]. by iSplit. }
  Qed.

  Lemma type_delete {A As Bs} (ty: _ A) n' (n: Z) p e E L C (T: _ As) (T': _ Bs) tr pre :
    Closed [] e → tctx_extract_ctx E L +[p ◁ own_ptr n' ty] T T' tr →
    n' = ty.(ty_size) → n = n' → typed_body E L C T' e pre -∗
    typed_body E L C T (delete [ #n; p ] ;; e) (tr (λ '(_ -:: al), pre al)).
  Proof.
    iIntros (??->?) "?". iApply type_seq; [by eapply type_delete_instr|done| |done].
    f_equal. fun_ext. by case.
  Qed.

(*
  Lemma type_letalloc_1 {E L} ty C T T' (x : string) p e :
    Closed [] p → Closed (x :b: []) e →
    tctx_extract_hasty E L p ty T T' →
    ty.(ty_size) = 1%nat →
    (∀ (v : val), typed_body E L C ((v ◁ own_ptr 1 ty)::T') (subst x v e)) -∗
    typed_body E L C T (letalloc: x <- p in e).
  Proof.
    iIntros (??? Hsz) "**". iApply type_new.
    - rewrite /Closed /=. rewrite !andb_True.
      eauto 10 using is_closed_weaken with set_solver.
    - done.
    - solve_typing.
    - iIntros (xv) "/=". rewrite -Hsz.
      assert (subst x xv (x <- p ;; e)%E = (xv <- p ;; subst x xv e)%E) as ->.
      { (* TODO : simpl_subst should be able to do this. *)
        unfold subst=>/=. repeat f_equal.
        - by rewrite bool_decide_true.
        - eapply is_closed_subst. done. set_solver. }
      iApply type_assign; [|solve_typing|by eapply write_own|solve_typing].
      apply subst_is_closed; last done. apply is_closed_of_val.
  Qed.

  Lemma type_letalloc_n {E L} ty ty1 ty2 C T T' (x : string) p e :
    Closed [] p → Closed (x :b: []) e →
    tctx_extract_hasty E L p ty1 T T' →
    (⊢ typed_read E L ty1 ty ty2) →
    (∀ (v : val),
        typed_body E L C ((v ◁ own_ptr (ty.(ty_size)) ty)::(p ◁ ty2)::T') (subst x v e)) -∗
    typed_body E L C T (letalloc: x <-{ty.(ty_size)} !p in e).
  Proof.
    iIntros. iApply type_new.
    - rewrite /Closed /=. rewrite !andb_True.
      eauto 10 using is_closed_of_val, is_closed_weaken with set_solver.
    - lia.
    - done.
    - iIntros (xv) "/=".
      assert (subst x xv (x <-{ty.(ty_size)} !p ;; e)%E =
              (xv <-{ty.(ty_size)} !p ;; subst x xv e)%E) as ->.
      { (* TODO : simpl_subst should be able to do this. *)
        unfold subst=>/=. repeat f_equal.
        - eapply (is_closed_subst []). apply is_closed_of_val. set_solver.
        - by rewrite bool_decide_true.
        - eapply is_closed_subst. done. set_solver. }
      rewrite Nat2Z.id. iApply type_memcpy.
      + apply subst_is_closed; last done. apply is_closed_of_val.
      + solve_typing.
      + (* TODO: Doing "eassumption" here shows that unification takes *forever* to fail.
           I guess that's caused by it trying to unify typed_read and typed_write,
           but considering that the Iris connectives are all sealed, why does
           that take so long? *)
        by eapply (write_own ty (↯ _)).
      + solve_typing.
      + done.
      + done.
  Qed.
*)
End typing.

Global Hint Resolve own_subtype own_eqtype box_subtype box_eqtype
            (* write_own read_own_copy *) : lrust_typing.
(* By setting the priority high, we make sure copying is tried before
   moving. *)
(*
Global Hint Resolve read_own_move | 100 : lrust_typing.
*)
