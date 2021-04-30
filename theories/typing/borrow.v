From iris.proofmode Require Import tactics.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export uniq_bor shr_bor own.
From lrust.typing Require Import lft_contexts type_context programs.
Set Default Proof Using "Type".

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{!typeG Σ}.

  Lemma tctx_borrow {𝔄} E L p n (ty: type 𝔄) κ:
    elctx_sat E L (ty_outlv_E ty κ) →
    tctx_incl E L +[p ◁ own_ptr n ty] +[p ◁ &uniq{κ} ty; p ◁{κ} own_ptr n ty]
      (λ post '-[a], ∀a': 𝔄, post -[(a, a'); a']).
  Proof.
    iIntros (Out ??[vπ[]]?) "#LFT #PROPH #UNIQ #E L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (vπ inhabitant).
    iDestruct "p" as ([[]|][|]?) "[#⧖ own]"=>//.
    iDestruct "own" as "[(%& >↦ & ty) †]". iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlv_E with "Out") as "#?".
    iMod (uniq_intro vπ with "PROPH UNIQ") as (i) "[Vo Pc]"; [done|].
    set ξ := PrVar (𝔄 ↾ prval_to_inh vπ) i.
    iMod (bor_create ⊤ κ (∃vπ' d, _ ↦∗: ty.(ty_own) vπ' d _ ∗
      ⧖(S d) ∗ .PC[ξ] vπ' d)%I with "LFT [↦ ty Pc]") as "[Bor Toty]"; [done| |].
    { iExists _, _. iFrame "Pc ⧖". iExists _. iFrame. }
    iExists -[pair ∘ vπ ⊛ (.$ ξ); (.$ ξ)]. rewrite/= right_id. iFrame "L". iModIntro.
    iSplitR "Obs"; [|by iApply proph_obs_impl; [|done]=>/=]. iSplitL "Vo Bor".
    - iExists _, _. do 2 (iSplit; [done|]). iFrame "#". iExists _, _. by iFrame.
    - iExists _. iSplit; [done|]. iIntros "†κ". iMod ("Toty" with "†κ") as
      (??) "(↦ty & >⧖' & Pc)". iExists _, _. iFrame "⧖' ↦ty †".
      iIntros "!>!>". iDestruct (proph_ctrl_eqz with "PROPH Pc") as "$".
  Qed.

  Lemma type_share_instr {𝔄} E L p κ (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    (* κ ⊑ ty_lft ty  *)
    ⊢ typed_instr E L +[p ◁ &uniq{κ}ty] Share (const +[p ◁ &shr{κ} ty]) (λ post '-[a], a.1 = a.2 -> post -[a.1]).
  Proof.
    iIntros (Hκ ?? [vπ []]) "#LFT #TIME #PROPH #UNIQ #HE $ HL [Huniq _] Hproph".
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; [done..|].
    iDestruct "Huniq" as ([[]|] [|d]) "(% & _ & [#? H]) /="; try done;
      iDestruct "H" as (? ?) "([% %] & Hvo & Huniq)"; try lia.
    set (ξ := PrVar _ i).
    iMod (bor_exists_tok with "LFT Huniq Htok1") as (vπ') "[Huniq Htok1]"; first solve_ndisj.
    iMod (bor_exists_tok with "LFT Huniq Htok1") as (d'') "[Huniq Htok1]"; first solve_ndisj.
    iMod (bor_acc with "LFT Huniq Htok1") as "[(Hown & > #Hd'' & Hpc) Hclose']"; first solve_ndisj.
    iDestruct "Hown" as (?) "[H↦ Hown]".
    iDestruct (ty.(ty_own_proph) with "LFT [$] Hown [$Htok2]") as "H"; first solve_ndisj.
    wp_bind Skip. 
    iApply (wp_step_fupdN_persist_time_rcpt _ _ ∅ with "TIME Hd'' [H]"); [done..| |].
    { iApply step_fupdN_with_emp.  
      iApply (fupd_step_fupdN_fupd_mask_mono with "H"); done.
    }
    wp_seq. iDestruct 1 as (ξl q') "/= (%Hdep & Hdt & Hclose'')". 
    iDestruct (uniq_agree with "Hvo Hpc") as "%Hag"; inversion Hag; subst; clear Hag.
    iMod (uniq_resolve with "PROPH Hvo Hpc Hdt") as "(Hobs & Hpc & Hdt)"; [done|done| ].
    iMod ("Hclose''" with "Hdt") as "[Hown Htok]".
    iMod ("Hclose'" with "[H↦ Hown Hpc]") as "[Huniq Htok2]". 
    { iFrame "#∗". iExists _. iFrame. }
    iMod (bor_sep with "LFT Huniq") as "[Huniq _]"; first solve_ndisj.
    iDestruct (ty.(ty_share) with "LFT [$] Huniq Htok") as "Hshr"; first solve_ndisj.
    iModIntro. wp_seq.
    iApply (wp_step_fupdN_persist_time_rcpt _ _ ∅ with "TIME Hd'' [Hshr]");
      [done..| |].
    { iApply step_fupdN_with_emp.  
      iApply (fupd_step_fupdN_fupd_mask_mono with "Hshr"); done.
    }
    wp_seq. iIntros "[Hshr Htok1]". iMod ("Hclose" with "[$Htok1 $Htok2]") as "$".
    iExists -[_]. rewrite /= right_id. iSplitR "Hproph Hobs".
    - iExists _, _. by iFrame "# % Hshr".
    - iCombine "Hobs Hproph" as "Hobs". iApply proph_obs_impl; [|done] => π /=. 
      rewrite -(f_equal (.$ π) H1) => [] /= [<- ?]; auto. 
  Qed.

  Lemma type_share {𝔄 As Bs E L} p e κ (ty : type 𝔄) C (T : tctx As) (T' : tctx Bs) f pre:
    Closed [] e →
    tctx_extract_elt E L (p ◁ &uniq{κ} ty)%T T T' f →
    lctx_lft_alive E L κ →
    typed_body E L C ((p ◁ &shr{κ} ty) +:: T') e  pre-∗
    typed_body E L C T (Share ;; e) (f (λ '(b -:: bs), (b.1 = b.2 → pre (b.1 -:: bs)) : Prop)).
  Proof. iIntros. iApply type_seq; [ by iApply type_share_instr |solve_typing | done | done ]. Qed.
  
  (* Lemma tctx_extract_hasty_borrow E L p n ty ty' κ T :
    subtype E L ty' ty →
    elctx_sat E L (ty_outlv_E ty κ) →
    tctx_extract_hasty E L p (&uniq{κ}ty) ((p ◁ own_ptr n ty')::T)
                       ((p ◁{κ} own_ptr n ty)::T).
  Proof.
    intros. apply (tctx_incl_frame_r _ [_] [_;_]). rewrite subtype_tctx_incl.
    - by eapply tctx_borrow.
    - by f_equiv.
  Qed. *)

  Lemma type_deref_uniq_own_instr {𝔄} κ p n (ty: type 𝔄) E L :
    lctx_lft_alive E L κ →
    ⊢ typed_instr_ty E L +[p ◁ &uniq{κ} (own_ptr n ty)]
        (!p) (&uniq{κ} ty) (λ post '-[a], post a).
  Proof.
    iIntros (Alvκ ?? [vπ []]) "#LFT #TIME #PROPH #UNIQ #E $ L [p _] Obs".
    have ?: Inhabited 𝔄 := populate (fst (vπ inhabitant)).
    iMod (Alvκ with "E L") as (q) "[κ ToL]"; [done|]. wp_apply (wp_hasty with "p").
    iIntros ([[]|] ??) "#⧖ [#? uniq]"=>//.
    iDestruct "uniq" as (? ξi [? Eq]) "[ξVo Bor]". set (ξ := PrVar _ ξi).
    iMod (bor_acc_cons with "LFT Bor κ") as "[Body ToBor]"; [done|].
    iDestruct "Body" as (?[|]) "(↦own & _ & ξPc)";
      iDestruct "↦own" as ([|[[| |]|][]]) "[>↦ own]"; try iDestruct "own" as ">[]".
    iDestruct "own" as "[ty †]". rewrite heap_mapsto_vec_singleton -wp_fupd.
    iApply wp_cumul_time_rcpt; [done|done|]. wp_read. iIntros "⧗1".
    iDestruct (uniq_agree with "ξVo ξPc") as %[<-->].
    iMod (uniq_intro (fst ∘ vπ) with "PROPH UNIQ") as (ζi) "[ζVo ζPc]"; [done|].
    set (ζ := PrVar _ ζi).
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζ & ToζPc)".
    rewrite proph_tok_singleton. iMod (uniq_preresolve with "PROPH ξVo ξPc ζ")
    as "(EqObs & ζ & ToξPc)"; [done|apply (proph_dep_one ζ)|].
    iCombine "EqObs Obs" as "Obs". iDestruct ("ToζPc" with "ζ") as "ζPc".
    iMod ("ToBor" $! (∃vπ' d', (∃vl', _ ↦∗ vl' ∗ ty_own ty vπ' d' _ vl') ∗
      ⧖(S d') ∗ .PC[ζ] vπ' d')%I with "[↦ ⧗1 † ToξPc] [ty ζPc]") as "[Bor κ]".
    - iIntros "!> (%&%& ? & >⧖' & ζPc)".
      iMod (cumul_persist_time_rcpts with "TIME ⧗1 ⧖'") as "⧖'"; [solve_ndisj|].
      iIntros "!>!>". iDestruct ("ToξPc" with "[ζPc]") as "ξPc".
      { iApply (proph_ctrl_eqz with "PROPH ζPc"). } iExists _, _. iFrame "⧖' ξPc".
      iExists [_]. rewrite heap_mapsto_vec_singleton. iFrame "↦". iFrame.
    - iExists _, _. iFrame "ty ζPc". iApply persist_time_rcpt_mono; [|done]. lia.
    - iExists -[λ π, ((vπ π).1, π ζ)]. iMod ("ToL" with "κ") as "$".
      rewrite right_id tctx_hasty_val'; [|done]. iModIntro. iSplitR "Obs".
      { iExists _. iFrame "⧖". iFrame "#". iExists _, _. iFrame "ζVo Bor". iPureIntro.
      split; by [lia|]. } iApply proph_obs_impl; [|done]=> π[<-?].
      eapply eq_ind; [done|]. move: (equal_f Eq π)=>/=. by case (vπ π)=>/= ??->.
  Qed.

  (* Lemma type_deref_uniq_own {E L} κ x p e n ty C T T' f pre:
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&uniq{κ}(own_ptr n ty)) T T' f →
    lctx_lft_alive E L κ →
    (∀ (v:val), typed_body E L C ((v ◁ &uniq{κ}ty) :: T') (subst' x v e) pre) -∗
    typed_body E L C T (let: x := !p in e) _.
  Proof. iIntros. iApply type_let; [by apply type_deref_uniq_own_instr|solve_typing|done]. Qed. *)

  (* Lemma type_deref_shr_own_instr {E L} κ p n ty :
    lctx_lft_alive E L κ →
    ⊢ typed_instr_ty E L [p ◁ &shr{κ}(own_ptr n ty)] (!p) (&shr{κ} ty).
  Proof.
    iIntros (Hκ tid) "#LFT #TIME HE $ HL Hp".
    rewrite tctx_interp_singleton.
    iMod (Hκ with "HE HL") as (q) "[[Htok1 Htok2] Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros (depth [[]|]) "_ _ Hown"; try done.
    iDestruct "Hown" as (l') "#[H↦b #Hown]".
    iMod (frac_bor_acc with "LFT H↦b Htok1") as (q''') "[>H↦ Hclose']". done.
    iApply wp_fupd. wp_read. iMod ("Hclose'" with "[H↦]") as "Htok1"; first by auto.
    iMod ("Hclose" with "[Htok1 Htok2]") as "($ & $)"; first by iFrame.
    rewrite tctx_interp_singleton tctx_hasty_val' //. iFrame "#".
    iExists 0%nat. iApply persist_time_rcpt_0.
  Qed. *)

  (* Lemma type_deref_shr_own {E L} κ x p e n ty C T T' :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&shr{κ}(own_ptr n ty)) T T' →
    lctx_lft_alive E L κ →
    (∀ (v:val), typed_body E L C ((v ◁ &shr{κ} ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. iApply type_let; [by apply type_deref_shr_own_instr|solve_typing|done]. Qed. *)

  (* Lemma type_deref_uniq_uniq_instr {E L} κ κ' p ty :
    lctx_lft_alive E L κ →
    ⊢ typed_instr_ty E L [p ◁ &uniq{κ}(&uniq{κ'}ty)] (!p) (&uniq{κ} ty).
  Proof.
    iIntros (Hκ tid) "#LFT #TIME #HE $ HL Hp".
    rewrite tctx_interp_singleton.
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp").
    iIntros ([|depth1] [[]|]) "#Hdepth1"; iIntros (?) "[#Hκκ' H]"; try done.
    iAssert (κ ⊑ foldr meet static (ty_lfts ty))%I as "Hκ".
    { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_r. }
    iDestruct "H" as (depth2 γ ?) "[H◯ Hbor]".
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[H Hclose']"; [done|].
    iDestruct "H" as ([|depth2']) "(>H● & >#Hdepth2' & H)";
    iDestruct "H" as ([|[[]|] []]) "(>Hl & #Hκ' & H)"; try by iDestruct "H" as ">[]".
    iDestruct (own_valid_2 with "H● H◯") as %<-%excl_auth_agree_L.
    iDestruct "H" as (depth3 γ') "(>% & >H◯' & Hbor)".
    iMod ("Hclose'" $! (∃ (l' : loc) γ', l ↦ #l' ∗
          (∃ depth3, ⧖S (S depth3) ∗ own γ' (◯E depth3)) ∗
      &{κ'}(∃ depth3', own γ' (●E depth3') ∗ ⧖S depth3' ∗
           l' ↦∗: ty.(ty_own) depth3' tid))%I
            with "[H● H◯] [H◯' Hbor Hl]"
         ) as "[Hbor Htok]".
    { iIntros "!> H". iDestruct "H" as (l'' γ'') "(>? & >Hd & Ho)".
      iDestruct "Hd" as (depth3') "[Hdepth3' ?]".
      iMod (own_update_2 with "H● H◯") as "[? _]"; [by apply excl_auth_update|].
      iCombine "Hdepth2' Hdepth3'" as "Hd".
      rewrite -persist_time_rcpt_sep -!Max.succ_max_distr. iExists _.
      iFrame "Hd ∗". iExists [ #l'']. rewrite heap_mapsto_vec_singleton.
      iFrame "∗#". auto 10 with lia iFrame. }
    { rewrite heap_mapsto_vec_singleton. iExists _, _. iFrame. iExists _. iFrame.
      iApply (persist_time_rcpt_mono with "Hdepth2'"). lia. }
    iClear "Hdepth1 Hdepth2'". clear dependent p depth1 depth2' depth3 γ γ' Hκ.
    iMod (bor_exists with "LFT Hbor") as (l') "Hbor". done.
    iMod (bor_exists with "LFT Hbor") as (γ') "Hbor". done.
    iMod (bor_sep with "LFT Hbor") as "[H↦ Hbor]". done.
    iMod (bor_acc with "LFT H↦ Htok") as "[>H↦ Hclose']". done.
    iMod (bor_sep with "LFT Hbor") as "[Hdepth3 Hbor]". done.
    iMod (bor_unnest with "LFT Hbor") as "Hbor"; [done|].
    iApply wp_fupd. iApply wp_cumul_time_rcpt=>//. wp_read. iIntros "Ht".
    iMod "Hbor".
    iMod ("Hclose'" with "[H↦]") as "[_ Htok]"; first by auto.
    iMod (bor_combine with "LFT Hdepth3 [Hbor]") as "Hbor"; [done| |].
    { iApply (bor_shorten with "[] Hbor").
      iApply lft_incl_glb; [|iApply lft_incl_refl].
      iApply lft_incl_trans; [iApply "Hκκ'"|]. iApply lft_intersect_incl_l. }
    iMod (bor_acc_cons with "LFT Hbor Htok") as "[[>Hdepth3 Hown] Hclose']"; [done|].
    iDestruct "Hdepth3" as (depth3) "[#Hdepth3 H◯']".
    iDestruct "Hown" as (depth3') "(>H●' & _ & Hown)".
    iDestruct (own_valid_2 with "H●' H◯'") as %->%excl_auth_agree_L.
    iMod (own_alloc (◯E (S depth3) ⋅ ●E (S depth3))) as (γ'') "[H◯'' H●'']";
      [by apply excl_auth_valid|].
    iMod ("Hclose'" $! (∃ depth3,
      (own γ'' (●E depth3) ∗ ⧖S depth3 ∗ l' ↦∗: ty.(ty_own) depth3 tid))%I
      with "[H●' H◯' Ht] [H●'' Hown]") as "[Hbor Htok]".
    { iIntros "!> H". iDestruct "H" as (depth3') "(_ & >#Hd & Ho)".
      iMod (own_update_2 with "H●' H◯'") as "[H●' H◯']"; [by apply excl_auth_update|].
      iSplitR "Ho H●'"; [|by auto with iFrame]. iExists _. iFrame.
      by iMod (cumul_persist_time_rcpts with "TIME Ht Hd") as "$";
        [solve_ndisj|]. }
    { iExists _. iIntros "{$H●'' $Hdepth3} !>". iApply ty_own_mt_depth_mono; [|done]. lia. }
    rewrite tctx_interp_singleton /tctx_elt_interp /=.
    iMod ("Hclose" with "Htok") as "$". iExists _, _. iFrame "#".
    iSplitR; [done|]. auto with iFrame.
  Qed. *)

  (* Lemma type_deref_uniq_uniq {E L} κ κ' x p e ty C T T' :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&uniq{κ}(&uniq{κ'}ty))%T T T' →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀ (v:val), typed_body E L C ((v ◁ &uniq{κ}ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. iApply type_let; [by apply type_deref_uniq_uniq_instr|solve_typing|done]. Qed. *)

  (* Lemma type_deref_shr_uniq_instr {E L} κ κ' p ty :
    lctx_lft_alive E L κ →
    ⊢ typed_instr_ty E L [p ◁ &shr{κ}(&uniq{κ'}ty)] (!p) (&shr{κ}ty).
  Proof.
    iIntros (Hκ tid) "#LFT #TIME HE $ HL Hp". rewrite tctx_interp_singleton.
    iMod (Hκ with "HE HL") as (q) "[Htok Hclose]"; first solve_ndisj.
    wp_apply (wp_hasty with "Hp"). iIntros (depth [[]|]) "Hdepth _ Hshr"; try done.
    iDestruct "Hshr" as (l') "[H↦ Hshr]".
    iMod (frac_bor_acc with "LFT H↦ Htok") as (q'') "[>H↦ Hclose']". done.
    iApply wp_fupd. wp_read.
    iMod ("Hclose'" with "[H↦]") as "Htok"; first by auto.
    iMod ("Hclose" with "Htok") as "$".
    rewrite tctx_interp_singleton tctx_hasty_val' //. auto.
  Qed. *)

  (* Lemma type_deref_shr_uniq {E L} κ κ' x p e ty C T T' :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p (&shr{κ}(&uniq{κ'}ty))%T T T' →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀ (v:val), typed_body E L C ((v ◁ &shr{κ}ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. iApply type_let; [by apply type_deref_shr_uniq_instr|solve_typing|done]. Qed. *)
End borrow.

(* Global Hint Resolve tctx_extract_hasty_borrow | 10 : lrust_typing. *)
