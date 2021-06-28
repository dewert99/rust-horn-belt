From lrust.typing Require Export type.
From lrust.typing Require Import array_util uniq_util typing lib.option.
From lrust.typing.lib.vec Require Import vec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section vec_pushpop.
  Context `{!typeG Σ}.

  Definition vec_push {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"; "x"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      let: "len" := !("v'" +ₗ #1) in let: "ex" := !("v'" +ₗ #2) in
      "v'" +ₗ #1 <- "len" + #1;;
      withcont: "push":
        if: "ex" ≤ #0 then
          "v'" +ₗ #2 <- "len";; let: "l" := !"v'" in
          let: "l'" := new [(#2 * "len" + #1) * #ty.(ty_size)] in
          memcpy ["l'"; "len" * #ty.(ty_size); "l"];;
          delete ["len" * #ty.(ty_size); "l"];;
          "v'" <- "l'";; "push" []
        else
          "v'" +ₗ #2 <- "ex" - #1;; "push" []
      cont: "push" [] :=
        !"v'" +ₗ "len" * #ty.(ty_size) <-{ty.(ty_size)} !"x";;
        delete [ #ty.(ty_size); "x"];;
        let: "r" := new [ #0] in return: ["r"].

  Lemma vec_push_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_push ty) (fn<α>(∅; &uniq{α} (vec_ty ty), ty) → ())
      (λ post '-[(al, al'); a], al' = al ++ [a] → post ()).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[x[]]]. simpl_subst.
    iIntros (tid (vπ & aπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(v & x &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "v" as ([|dv]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦ & [#LftIn uniq]) †]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//.
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_persistent_time_receipt with "TIME ⧖x"); [done|].
    iApply (wp_delete with "[$↦ $†]"); [done|]. iIntros "!>_ ⧖x".
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]".
    move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& ⧖u & Pc & ↦vec) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_vec. case du as [|du]=>//.
    iDestruct "↦vec" as (? len ex aπl Eq1) "(↦₀ & ↦₁ & ↦₂ & ↦tys & (%wl &%& ↦ex) & †)".
    do 2 (wp_op; wp_read; wp_let). do 2 wp_op. wp_write.
    have ->: (len + 1)%Z = S len by lia.
    iCombine "⧖u ⧖x" as "#⧖"=>/=. set d := du `max` dx.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    set push := (rec: "push" _ := _)%E.
    iAssert (
      (∃(l: loc) (ex: nat), v' ↦ #l ∗ (v' +ₗ 1) ↦ #(S len) ∗ (v' +ₗ 2) ↦ #ex ∗
        ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ du tid) ∗
        (l +ₗ[ty] len) ↦∗len (S ex * ty.(ty_size)) ∗
        freeable_sz' ((S len + ex) * ty.(ty_size)) l) -∗
      WP push [] {{ _, cont_postcondition }})%I
      with "[L ToL Na C Vo Pc ToBor x]" as "push".
    { iIntros "/=(%&%& ↦₀ & ↦₁ & ↦₂ & ↦tys & (%vl & %Len & ↦ex) & †)".
      rewrite /push. wp_rec. wp_read. do 2 wp_op. wp_bind (_ <-{_} !_)%E.
      move: {Len}(app_length_ex vl _ _ Len)=> [vl'[?[->[Len ?]]]].
      rewrite heap_mapsto_vec_app shift_loc_assoc_nat Len -Nat2Z.inj_mul.
      iDestruct "↦ex" as "[↦ ↦ex]". iDestruct "x" as "[(%& ↦x & ty) †x]".
      iDestruct (ty_size_eq with "ty") as %Sz. rewrite freeable_sz_full.
      iApply (wp_memcpy with "[$↦ $↦x]"); [lia..|]. iIntros "!> [↦ ↦x]". wp_seq.
      wp_bind (delete _). iApply (wp_delete with "[$↦x †x]"); [lia|by rewrite Sz|].
      iIntros "!>_". wp_seq. set vπ' := λ π, (lapply (vsnoc aπl aπ) π, π ξ).
      iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦tys ↦ ty ↦ex † Pc]") as "[Bor α]".
      { iNext. iExists _, _. rewrite split_mt_vec. iFrame "⧖ Pc".
        iExists _, _, _, (vsnoc aπl _). iFrame "↦₀ ↦₁ ↦₂ †". iSplit; [done|].
        iSplitR "↦ex"; last first. { iExists _. rewrite/= plus_comm. by iFrame. }
        iNext. rewrite vec_to_list_snoc big_sepL_app. iSplitL "↦tys".
        { iClear "#". iStopProof. do 6 f_equiv. apply ty_own_depth_mono. lia. }
        rewrite/= right_id. iExists _. rewrite vec_to_list_length Nat.add_0_r.
        iFrame "↦". iApply ty_own_depth_mono; [|done]. lia. }
      iMod ("ToL" with "α L") as "L".
      iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty)] -[vπ']
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst.
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= right_id (tctx_hasty_val #_). iExists _.
        iFrame "⧖ LftIn". iExists _, _. rewrite /uniq_own.
        rewrite (proof_irrel (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ'))
          (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ))). by iFrame.
      - iApply proph_obs_impl; [|done]=> π.
        move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (vπ π)=>/= ??->-> Imp Eq.
        apply Imp. move: Eq. by rewrite vec_to_list_snoc lapply_app. }
    rewrite /push. wp_let. wp_op. wp_case. case ex as [|ex']=>/=; last first.
    { do 2 wp_op. have ->: (S ex' - 1)%Z = ex' by lia. wp_write.
      iApply "push". iExists _, _. iFrame "↦tys ↦₀ ↦₁ ↦₂".
      iSplitL "↦ex". { iExists _. iFrame. iPureIntro. lia. }
      iClear "#". iStopProof. f_equiv. lia. }
    wp_op. wp_write. wp_read. wp_let. do 3 wp_op. wp_bind (new _).
    iApply wp_new; [lia|done|]. iIntros "!>" (?) "[†' ↦']". wp_let. wp_op.
    have ->: ∀sz: nat, ((2 * len + 1) * sz)%Z = (len + S len) * sz by lia.
    rewrite trans_big_sepL_mt_ty_own plus_0_r Nat2Z.id Nat.mul_add_distr_r
      repeat_app heap_mapsto_vec_app.
    iDestruct "↦tys" as (?) "[↦ tys]". iDestruct "↦'" as "[↦' ↦ex']".
    iDestruct (big_sepL_ty_own_length with "tys") as %Len. wp_bind (memcpy _).
    iApply (wp_memcpy with "[$↦' $↦]"); [rewrite repeat_length; lia|lia|].
    iIntros "!>[↦' ↦]". wp_seq. wp_op. rewrite -Nat2Z.inj_mul. wp_bind (delete _).
    iApply (wp_delete with "[$↦ †]"); [lia|by rewrite Len|]. iIntros "!>_".
    wp_seq. wp_write. iApply "push". iExists _, _. iFrame "↦₀ ↦₁ ↦₂".
    iSplitL "↦' tys". { rewrite trans_big_sepL_mt_ty_own. iExists _. iFrame. }
    iSplitR "†'".
    - iExists _. rewrite repeat_length. iFrame "↦ex'". by rewrite repeat_length.
    - by have <-: ∀sz, sz + (len + len) * sz = len * sz + (sz + len * sz) by lia.
  Qed.

  Definition vec_pop {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"] :=
      let: "v'" := !"v" in delete [ #1; "v"];;
      let: "len" := !("v'" +ₗ #1) in
      if: "len" ≤ #0 then
        let: "r" := new [ #(option_ty ty).(ty_size)] in "r" <-{Σ 0} ();;
        return: ["r"]
      else
        let: "len'" := "len" - #1 in
        "v'" +ₗ #1 <- "len'";; "v'" +ₗ #2 <- !("v'" +ₗ #2) + #1;;
        let: "r" := new [ #(option_ty ty).(ty_size)] in
        "r" <- #1;; "r" +ₗ #1 <-{ty.(ty_size)} ! (!"v'" +ₗ "len'" * #ty.(ty_size));;
        return: ["r"].

  (* The precondition requires that the input list is non-empty *)
  Lemma vec_pop_type {𝔄} (ty: type 𝔄) :
    typed_val (vec_pop ty) (fn<α>(∅; &uniq{α} (vec_ty ty)) → option_ty ty)
      (λ post '-[(al, al')],
        (al = [] → al' = [] → post None) ∧
        ∀alᵢ (a: 𝔄), al = alᵢ ++ [a] → al' = alᵢ → post (Some a)).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[]]. simpl_subst.
    iIntros (?[vπ[]]?) "#LFT TIME #PROPH #UNIQ #E Na L C /=[v _] #Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦ & [#LftIn uniq]) †]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    rewrite heap_mapsto_vec_singleton. wp_read. wp_let. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_delete with "[$↦ $†]"); [done|]. iIntros "!>_".
    iDestruct "uniq" as (d ξi [? Eq2]) "[Vo Bor]". move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc with "LFT Bor α") as "[(%&%& #⧖ & Pc & ↦vec) ToBor]"; [done|].
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_vec. case d=>// ?.
    iDestruct "↦vec" as (? len ex aπl Eq1) "(↦₀ & ↦₁ & ↦₂ & ↦tys & (%wl &%& ↦ex) & †)".
    wp_op. wp_read. wp_let. wp_op. wp_case. case len as [|].
    { iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦tys ↦ex † ⧖ Pc]") as "[Bor β]".
      { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_vec. iExists _, _, _, _.
        iFrame "↦₀ ↦₁ ↦₂ ↦tys †". iSplit; [done|]. iExists _. by iFrame. }
      iMod ("ToL" with "β L") as "L".
      iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty)] -[vπ]
        with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
      - iApply type_new; [done|]. intro_subst. rewrite Nat2Z.id.
        iApply (type_sum_unit +[(); ty]%T 0%fin); [done|solve_extract|solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
      - rewrite/= !(tctx_hasty_val #_). iSplitL; [|done]. iExists _.
        iFrame "⧖ LftIn". iExists _, _. iFrame. iPureIntro. split; [lia|done].
      - iApply proph_obs_impl; [|done]=> π. move: (equal_f Eq1 π)=>/=. clear.
        inv_vec aπl. case (vπ π)=>/= ??->[Imp _]. by apply Imp. }
    inv_vec aπl=> aπₕ aπlₜ Eq1.
    iDestruct (big_sepL_vinitlast with "↦tys") as "[↦tys (%vl & ↦last & ty)]"=>/=.
    set aπl' := vinit' aπₕ aπlₜ. set aπ := vlast' aπₕ aπlₜ.
    set vπ' := λ π, (lapply aπl' π, π ξ).
    wp_op. wp_let. wp_op. wp_write. do 2 wp_op. wp_read. wp_op. wp_write.
    wp_bind (new _). iApply wp_new; [lia|done|]. iIntros "!>" (r) "[†r ↦r]". wp_let.
    rewrite Nat2Z.id /= heap_mapsto_vec_cons. have ->: (S len - 1)%Z = len by lia.
    iDestruct "↦r" as "[↦r ↦r']". iDestruct (ty_size_eq with "ty") as %Eqvl.
    wp_write. wp_op. wp_read. do 2 wp_op. rewrite -Nat2Z.inj_mul.
    wp_apply (wp_memcpy with "[$↦r' $↦last]"); [rewrite repeat_length; lia|lia|].
    iIntros "[↦r' ↦last]". wp_seq.
    iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
    iMod ("ToBor" with "[↦₀ ↦₁ ↦₂ ↦tys ↦last ↦ex † ⧖ Pc]") as "(Bor & α)".
    { iNext. iExists _, _. iFrame "⧖ Pc". rewrite split_mt_vec.
      have ->: ∀sz, sz + (len + ex) * sz = (len + S ex) * sz by lia.
      have ->: (ex + 1)%Z = S ex by lia. iExists _, _, _, _.
      iFrame "↦₀ ↦₁ ↦₂ ↦tys †". iSplit; [done|]. iExists (vl ++ wl).
      rewrite app_length heap_mapsto_vec_app shift_loc_assoc_nat plus_comm Eqvl.
      iSplit; [iPureIntro; lia|]. iFrame. }
    iMod ("ToL" with "α L") as "L".
    iApply (type_type +[#v' ◁ &uniq{α} (vec_ty ty); #r ◁ box (option_ty ty)]
      -[vπ'; Some ∘ aπ] with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
    - iApply type_jump; [solve_typing|solve_extract|solve_typing].
    - rewrite/= !(tctx_hasty_val #_) right_id. iSplitL "Vo Bor".
      + iExists _. iFrame "⧖ LftIn". iExists _, _. rewrite /uniq_own.
        rewrite (proof_irrel (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ'))
          (@prval_to_inh (listₛ 𝔄) (fst ∘ vπ))). by iFrame.
      + iExists _. rewrite -freeable_sz_full. iFrame "⧖ †r". iNext.
        rewrite /option_ty. setoid_rewrite mod_ty_own; [|apply _].
        rewrite split_mt_sum. iExists 1%fin, aπ. iSplit; [done|]. iFrame "↦r". iSplitR.
        { iExists []. rewrite heap_mapsto_vec_nil left_id. iPureIntro=>/=.
          move: ty.(ty_size)=> ?. lia. }
        iExists _. iFrame "↦r'". iApply ty_own_depth_mono; [|done]. lia.
    - iApply proph_obs_impl; [|done]=>/= π. move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=.
      case (vπ π)=>/= ??->->[_ Imp]. apply Imp. rewrite /aπl' /aπ. clear.
      move: aπₕ π. induction aπlₜ; [done|]=>/= ??. by f_equal.
  Qed.
End vec_pushpop.
