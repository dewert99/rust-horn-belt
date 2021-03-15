From iris.proofmode Require Import tactics.
From lrust.lang.lib Require Import memcpy.
From lrust.typing Require Export type.
(* From lrust.typing Require Import uninit type_context programs. *)
Set Default Proof Using "Type".

Section own.
  Context `{!typeG Σ}.

  Definition freeable_sz (n : nat) (sz : nat) (l : loc) : iProp Σ :=
    match sz, n return _ with
    | 0%nat, _ => True
    | _, 0%nat => False
    | sz, n => †{pos_to_Qp (Pos.of_nat sz) / pos_to_Qp (Pos.of_nat n)}l…sz
    end%I.
  Arguments freeable_sz : simpl never.

  Global Instance freeable_sz_timeless n sz l : Timeless (freeable_sz n sz l).
  Proof. destruct sz, n; apply _. Qed.

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ †{1}l…n ∨ ⌜Z.of_nat n = 0⌝.
  Proof.
    destruct n as [|n].
    - iSplit; iIntros "H /="; auto.
    - assert (Z.of_nat (S n) = 0 ↔ False) as -> by done. rewrite right_id.
      by rewrite /freeable_sz Qp_div_diag.
  Qed.

  Lemma freeable_sz_full_S n l : freeable_sz (S n) (S n) l ⊣⊢ †{1}l…(S n).
  Proof. rewrite freeable_sz_full. iSplit; auto. iIntros "[$|%]"; done. Qed.

  Lemma freeable_sz_split n sz1 sz2 l :
    freeable_sz n sz1 l ∗ freeable_sz n sz2 (l +ₗ sz1) ⊣⊢
                freeable_sz n (sz1 + sz2) l.
  Proof.
    destruct sz1; [|destruct sz2;[|rewrite /freeable_sz plus_Sn_m; destruct n]].
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit. by iIntros "[[]?]". by iIntros "[]".
    - rewrite heap_freeable_op_eq. f_equiv.
      by rewrite -Qp_div_add_distr pos_to_Qp_add -Nat2Pos.inj_add.
  Qed.

  (* Make sure 'simpl' doesn't unfold. *)
  Global Opaque freeable_sz.

  Program Definition own_ptr {A} (n : nat) (ty : type A) :=
    {| ty_size := 1;
       ty_lfts := ty.(ty_lfts); ty_E := ty.(ty_E);
       ty_own depth tid vl :=
         match depth, vl return _ with
         | (asn, S depth), [ #(LitLoc l) ] =>
         (* We put a later in front of the †{q}, because we cannot use
            [ty_size_eq] on [ty] at step index 0, which would in turn
            prevent us to prove [subtype_own].

            Since this assertion is timeless, this should not cause
            problems. *)
           ▷ (l ↦∗: ty.(ty_own) (asn, depth) tid ∗ freeable_sz n ty.(ty_size) l)
         | _, _ => False
         end%I;
         ty_shr depth κ tid l :=
          match depth return _ with
          | (asn, S n) =>
            (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ∗ ▷ ty.(ty_shr) (asn, n) κ tid l')%I
          | _ => False
          end%I
    |}.
    Next Obligation. iIntros (A q ty [? [|depth]] κ tid l); typeclasses eauto. Qed.

    Next Obligation. by iIntros (A q ty [? [|depth]] tid [|[[]|][]]) "H". Qed.
  Next Obligation.
    intros A n ty [|depth1] [|depth2] asn tid vl Hdepth12;
      [iIntros "[]"|iIntros "[]"|lia|].
    do 6 f_equiv. apply ty_own_mt_depth_mono. lia.
  Qed.

  Next Obligation.
    iIntros (A n ty [|d1] [|d2] asn tid1 tid2 l Hdepth12);
      [iIntros "[]"|iIntros "[]"|lia|].
    do 4 f_equiv. iIntros "Hintros".
    by iApply (ty_shr_depth_mono _ _ d1); [lia|].
  Qed.

  Next Obligation.
    iIntros (A q ty κ κ' [? [|n]] tid l) "/= #LFT"; [iIntros "[]"|].
    iDestruct 1 as (l') "[? ?]".
    iExists (l'); iSplit.
    - by iApply frac_bor_shorten.
    - by iApply ty_shr_lft_mono.
  Qed.

  Next Obligation.
    iIntros (A n ty N asn depth κ l tid ??) "/= #LFT #Hout Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as (vl) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]"; first solve_ndisj.
    destruct depth as [|depth], vl as [|[[|l'|]|][]];
      try (iMod (bor_persistent with "LFT Hb2 Htok") as "[>[]_]"; solve_ndisj).
    rewrite heap_mapsto_vec_singleton bi.later_sep.
    iMod (bor_sep with "LFT Hb2") as "[Hb2 _]"; first solve_ndisj.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "Hb1"; first solve_ndisj.
    iMod (bor_later_tok with "LFT Hb2 Htok") as "Hb2"=>//.
    iIntros "/= !> !> !>". iMod "Hb2" as "[Hb2 Htok]".
    iMod (ty_share with "LFT Hout Hb2 Htok") as "Hb2"=>//. iModIntro.
    iApply (step_fupdN_wand with "Hb2"). iIntros ">[Hb2 $]".
    iExists (l'); by iFrame.
  Qed.

  Next Obligation.
    iIntros (A n ty N asn [|d] tid [|[[]|][]] κ ??) "#LFT #Hout"; try iIntros "[]".
    iIntros "Hown Htok".
    iModIntro. iModIntro. iNext.
    iDestruct "Hown" as "[Hown Hfrz]".
    iDestruct "Hown" as (vl) "[Hown Hb]".
    iDestruct ((ty_own_proph A _ N _ _ _ _ _ q H) with "LFT Hout Hb Htok") as "X".
    iApply (step_fupdN_wand with "X"). iDestruct 1 as "> Hupd".
    iDestruct "Hupd" as (ξs q') "(? & ? & Hb)".
    iExists ξs, q'; iFrame. iModIntro.
    iIntros "Hq".
    iMod ("Hb" with "Hq") as "[Hb ?]"; iFrame.
    iExists vl; by iFrame.
  Qed.

  Next Obligation.
    iIntros (A q ty N asn [|d] κ tid l κ' ??) "/= #LFT #Hout #Hshrt"; try iIntros "[]";
    iDestruct 1 as (l') "[Hfrac Hshr]";iIntros "Htok".
    iModIntro; iNext.
    iDestruct ((ty_shr_proph A _ N) with "LFT Hout Hshrt Hshr Htok") as "> Hb2"; [done|].
    iModIntro. iModIntro. iNext.
    iApply (step_fupdN_wand with "Hb2"). iDestruct 1 as "> Hupd".
    iDestruct "Hupd" as (ξs q') "(Hdep &deptoks &depres)".
    iExists ξs, q'; iFrame. iModIntro.
    iIntros "Htok".
    iMod ("depres" with "Htok") as "[Hshr ?]"; iFrame.
    iExists l'; by iFrame.
  Qed.

  Lemma own_type_incl A B (f : A → B) n m ty1 ty2 :
    ▷ ⌜n = m⌝ -∗ type_incl f ty1 ty2 -∗ type_incl f (own_ptr n ty1) (own_ptr m ty2).
  Proof.
    iIntros "#Heq #(Hsz & Hout & Ho & Hs)".
    iSplit; first done. iSplit; [done|iSplit; iModIntro].
    - iIntros (? [|depth]?[|[[| |]|][]]) "H"; try done. simpl.
      iDestruct "H" as "[Hmt H†]". iNext. iDestruct ("Hsz") as %<-.
      iDestruct "Heq" as %->. iFrame. iApply (heap_mapsto_pred_wand with "Hmt").
      iApply "Ho".
    - iIntros (?[|depth] ???) "H"; first done. iDestruct "H" as (l') "[Hfb #Hshr]".
      iExists l'. iFrame. iApply ("Hs" with "Hshr").
  Qed.
  
  Global Instance own_mono A E L n :
    Proper (subtype E L id ==> subtype E L id) (@own_ptr A n).
  Proof.
    intros ty1 ty2 Hincl. iIntros (qL) "HL".
    iDestruct (Hincl with "HL") as "#Hincl".
    iClear "∗". iIntros "!> #HE".
    iApply own_type_incl; first by auto. iApply "Hincl"; auto.
  Qed.

  Lemma own_mono' A E L n1 n2 ty1 ty2 :
    n1 = n2 → subtype E L id ty1 ty2 → subtype E L id (own_ptr n1 ty1) (@own_ptr A n2 ty2).
  Proof. intros -> *. by apply own_mono. Qed.

  Global Instance own_proper A E L n :
    Proper (eqtype E L id id ==> eqtype E L id id) (@own_ptr A n).
  Proof. intros ??[]; split; by apply own_mono. Qed.

  Lemma own_proper' A E L n1 n2 ty1 ty2 :
    n1 = n2 → eqtype E L id id ty1 ty2 → eqtype E L id id (@own_ptr A n1 ty1) (@own_ptr A n2 ty2).
  Proof. intros -> *. by apply own_proper. Qed.

  Global Instance own_type_contractive A n : @TypeContractive _ _ A A (own_ptr n).
  Proof.
    split.
    - apply (type_lft_morphism_add _ static [] []) => ?.
      + rewrite left_id. iApply lft_equiv_refl.
      + by rewrite /= /elctx_interp /= left_id right_id.
    - done.
    - move=> ??? Hsz ?? Ho ? [? [|depth]]? [|[[|l|]|] []] //=.
      rewrite Hsz. repeat (apply Ho || f_contractive || f_equiv).
    - move=> ??????? Hs [? [|?]] ??? /=;  repeat (apply Hs || f_contractive || f_equiv).  
  Qed.

  Global Instance own_ne A n : NonExpansive (@own_ptr A n).
  Proof. solve_ne_type. Qed.

  Global Instance own_send A n ty :
    Send ty → Send (@own_ptr A n ty).
  Proof.
    iIntros (Hsend tid1 tid2 [? [|depth]] [|[[| |]|][]]) "H"; try done.
    iDestruct "H" as "[Hm $]". iNext. iApply (heap_mapsto_pred_wand with "Hm").
    iIntros (vl) "?". by iApply Hsend.
  Qed.

  Global Instance own_sync A n ty :
    Sync ty → Sync (@own_ptr A n ty).
  Proof.
    iIntros (Hsync tid1 tid2 [? [|?]] κ  l) "H"; first done. iDestruct "H" as (l') "[Hm #Hshr]".
    iExists _. iFrame "Hm". by iApply Hsync.
  Qed.
End own.


Section box.
  Context `{!typeG Σ}.

  Definition box {A} (ty : type A) := own_ptr ty.(ty_size) ty.

  Lemma box_type_incl A ty1 ty2:
    type_incl id ty1 ty2 -∗ type_incl id (@box A ty1) (@box A ty2).
  Proof.
    iIntros "#Hincl". iApply own_type_incl; last done.
    iDestruct "Hincl" as "(? & _ & _)". done.
  Qed.

  Global Instance box_mono A E L :
    Proper (subtype E L id ==> subtype E L id) (@box A).
  Proof.
    intros ty1 ty2 Hincl. iIntros (qL) "HL".
    iDestruct (Hincl with "HL") as "#Hincl".
    iClear "∗". iIntros "!> #HE".
    iApply box_type_incl. iApply "Hincl"; auto.
  Qed.

  Lemma box_mono' A E L ty1 ty2 :
    subtype E L id ty1 ty2 → subtype E L id (@box A ty1) (@box A ty2).
  Proof. intros. by apply box_mono. Qed.

  Global Instance box_proper A E L :
    Proper (eqtype E L id id ==> eqtype E L id id) (@box A).
  Proof. intros ??[]; split; by apply box_mono. Qed.
  Lemma box_proper' A E L ty1 ty2 :
    eqtype E L id id ty1 ty2 → eqtype E L id id (@box A ty1) (@box A ty2).
  Proof. intros. by apply box_proper. Qed.

  Global Instance box_type_contractive A : TypeContractive (@box A).
  Proof.
    split.
    - apply (type_lft_morphism_add _ static [] []) => ?.
      + rewrite left_id. iApply lft_equiv_refl.
      + by rewrite /= /elctx_interp /= left_id right_id.
    - done.
    - move=> ??? Hsz ?? Ho ? [? [|depth]] ? [|[[|l|]|] []] //=.
      rewrite Hsz. repeat (apply Ho || f_contractive || f_equiv).
    - move=> ??????? Hs [? [|?]] ??? /=; repeat (apply Hs || f_contractive || f_equiv).
  Qed.

  Global Instance box_ne A : NonExpansive (@box A).
  Proof. solve_ne_type. Qed.
End box.

Section util.
  Context `{!typeG Σ}.

  Lemma ownptr_own A n (ty : type A) tid depth v :
    (own_ptr n ty).(ty_own) depth tid [v] ⊣⊢
       ∃ (l : loc) (vl : vec val ty.(ty_size)),
         ⌜depth.2 > 0⌝%nat ∗ ⌜v = #l⌝ ∗ ▷ l ↦∗ vl ∗
         ▷ ty.(ty_own) (depth.1, (pred depth.2)) tid vl ∗ ▷ freeable_sz n ty.(ty_size) l.
  Proof.
    iSplit.
    - iIntros "Hown". destruct depth as [? [|depth]], v as [[|l|]|]; try done.
      iExists l. iDestruct "Hown" as "[Hown $]". rewrite heap_mapsto_ty_own.
      iDestruct "Hown" as (vl) "[??]". simpl. eauto with iFrame lia.
    - iIntros "Hown". iDestruct "Hown" as (l vl) "(% & -> & ? & ? & ?)".
      destruct depth as [? [|depth]]; simpl in *; try lia. iFrame. iExists _. iFrame.
  Qed.
  (*
  Lemma ownptr_uninit_own n m tid depth v :
    (own_ptr n (uninit m)).(ty_own) depth tid [v] ⊣⊢
         ∃ (l : loc) (vl' : vec val m), ⌜depth > 0⌝%nat ∗ ⌜v = #l⌝ ∗
                                      ▷ l ↦∗ vl' ∗ ▷ freeable_sz n m l.
  Proof.
    rewrite ownptr_own. apply bi.exist_proper=>l. iSplit.
    (* FIXME: The goals here look rather confusing:  One cannot tell that we are looking at
       a statement in Iris; the top-level → could just as well be a Coq implication. *)
    - iIntros "H". iDestruct "H" as (vl) "(% & -> & Hl & _ & $)". auto.
    - iIntros "H". iDestruct "H" as (vl) "(% & -> & Hl & $)".
      iExists vl. rewrite /= vec_to_list_length. auto.
  Qed.*)
End util.
(*
Section typing.
  Context `{!typeG Σ}.

  (** Typing *)
  Lemma write_own {E L} ty ty' n :
    ty.(ty_size) = ty'.(ty_size) → ⊢ typed_write E L (own_ptr n ty') ty (own_ptr n ty).
  Proof.
    rewrite typed_write_eq. iIntros (Hsz) "!>".
    iIntros ([[]|] [|depth] tid F qL ?) "_ _ $ Hown"; try done.
    rewrite /= Hsz. iDestruct "Hown" as "[H↦ $]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". auto 10 with iFrame.
  Qed.

  Lemma read_own_copy E L ty n :
    Copy ty → ⊢ typed_read E L (own_ptr n ty) ty (own_ptr n ty).
  Proof.
    rewrite typed_read_eq. iIntros (Hsz) "!>".
    iIntros ([[]|] [|depth] tid F qL ?) "_ _ $ $ Hown"; try done.
    iDestruct "Hown" as "[H↦ H†]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_own_depth_mono _ _ (S depth) with "Hown") as "#?"; [lia|].
    iExists l, _, _. iFrame "∗#". iSplitR; first done. iIntros "!> Hl !>".
    iExists _. auto.
  Qed.

  Lemma read_own_move E L ty n :
    ⊢ typed_read E L (own_ptr n ty) ty (own_ptr n $ uninit ty.(ty_size)).
  Proof.
    rewrite typed_read_eq. iModIntro.
    iIntros ([[]|] [|depth] tid F qL ?) "_ _ $ $ Hown"; try done.
    iDestruct "Hown" as "[H↦ H†]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%".
    iDestruct (ty_own_depth_mono _ _ (S depth) with "Hown") as "Hown"; [lia|].
    iExists l, vl, _. iFrame "∗#". iSplitR; first done. iIntros "!> Hl !> !>".
    iExists _. iFrame. done.
  Qed.

  Lemma type_new_instr {E L} (n : Z) :
    0 ≤ n →
    ⊢ let n' := Z.to_nat n in
      typed_instruction_ty E L [] (new [ #n ]%E) (own_ptr n' (uninit n')).
  Proof.
    iIntros (? tid) "#LFT #TIME #HE $ $ _". iMod persistent_time_receipt_0 as "Ht".
    iApply (wp_persistent_time_receipt with "TIME Ht")=>//.
    iApply wp_new; try done. iModIntro.
    iIntros (l) "(H† & Hlft) #Ht". rewrite tctx_interp_singleton tctx_hasty_val.
    iExists 1%nat. iFrame "Ht". rewrite /= freeable_sz_full Z2Nat.id //. iFrame.
    iExists (repeat #☠ (Z.to_nat n)). iFrame. by rewrite /= repeat_length.
  Qed.

  Lemma type_new {E L C T} (n' : nat) x (n : Z) e :
    Closed (x :b: []) e →
    0 ≤ n →
    n' = Z.to_nat n →
    (∀ (v : val),
        typed_body E L C ((v ◁ own_ptr n' (uninit n')) :: T) (subst' x v e)) -∗
    typed_body E L C T (let: x := new [ #n ] in e).
  Proof. iIntros. subst. iApply type_let; [by apply type_new_instr|solve_typing..]. Qed.

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
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, own_mono.
  Qed.

  Lemma type_delete_instr {E L} ty (n : Z) p :
    Z.of_nat (ty.(ty_size)) = n →
    ⊢ typed_instruction E L [p ◁ own_ptr ty.(ty_size) ty] (delete [ #n; p])%E (λ _, []).
  Proof.
    iIntros (<- tid) "#LFT #TIME #HE $ $ Hp". rewrite tctx_interp_singleton.
    wp_bind p. iApply (wp_hasty with "Hp").
    iIntros ([|depth] [[]|]) "Hdepth _ Hown"; try done.
    iDestruct "Hown" as "[H↦: >H†]". iDestruct "H↦:" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>EQ".
    iDestruct "EQ" as %<-. iApply (wp_delete with "[-]"); auto.
    - iFrame "H↦". by iApply freeable_sz_full.
    - rewrite /tctx_interp /=; auto.
  Qed.

  Lemma type_delete {E L} ty C T T' (n' : nat) (n : Z)  p e :
    Closed [] e →
    tctx_extract_hasty E L p (own_ptr n' ty) T T' →
    n = n' → Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C T' e -∗
    typed_body E L C T (delete [ #n; p ] ;; e).
  Proof.
    iIntros (?? -> Hlen) "?". iApply type_seq; [by apply type_delete_instr| |done].
    by rewrite (inj _ _ _ Hlen).
  Qed.

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
        by eapply (write_own ty (uninit _)).
      + solve_typing.
      + done.
      + done.
  Qed.
End typing.

Global Hint Resolve own_mono' own_proper' box_mono' box_proper'
             write_own read_own_copy : lrust_typing.
(* By setting the priority high, we make sure copying is tried before
   moving. *)
Global Hint Resolve read_own_move | 100 : lrust_typing.
  *)
