From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.smallvec Require Import smallvec.
From lrust.typing.lib.vec Require Import vec_pushpop vec.

Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.


Section smallvec_push.
    Context `{!typeG Σ}.

    (* 
        check the tag,
        if its an array and there's room, store it there
        otherwise, push to the vector
    *)
    Definition smallvec_push {𝔄} (ty: type 𝔄) (n : nat ) : val :=
      fn: ["self"; "v"] :=    
        let: "self'" := !"self" in delete [ #1; "self"];;
        let: "tag" := !"self'" in 
        withcont: "push":
        if: "tag" then (* array mode *)
          let: "len" := !("self'" +ₗ #2) in
          if: ( "len" + #1)  ≤ #n then
            "self'" +ₗ #4 +ₗ "len" * #ty.(ty_size) <-{ty_size ty} !"v";;
            ("self'" +ₗ #2) <- "len" + #1;;
            let: "r" := new [ #0] in return: ["r"]
          else (* ruh-roh gotta allocate a vector and copy everything over*) 
            let: "l'" := new [("len") * #ty.(ty_size)] in
            memcpy ["l'"; "len" * #ty.(ty_size); "self'" +ₗ #4];;
            ("self'" +ₗ #1) <- ("l'");;
            ("self'" +ₗ #3) <- #0;;
            "self'" <- #false;; "push" []
        else 
          "push" []
        (* vector mode *)
        cont: "push" [] := 
          let: "vec_push" := vec_push ty in
          let: "vec" := new [ #1] in
          "vec" <- "self'" +ₗ #1;;
          letcall: "r" := "vec_push" ["vec"; "v"]  in
          return: ["r"] .

(* useful to force type inverence to choose the correct type for vπ' *)
Definition bor_cnts {𝔄} (ty: type 𝔄) (vπ: proph 𝔄) (ξi: positive) (d: nat)
  (tid: thread_id) (l: loc) : iProp Σ :=
  let ξ := PrVar (𝔄 ↾ prval_to_inh vπ) ξi in
  (∃vπ' d', ⧖(S d') ∗ .PC[ξ] vπ' d' ∗ l ↦∗: ty.(ty_own) vπ' d' tid).

Definition smallvec_push_type {𝔄} (ty: type 𝔄) (n : nat ) :
  typed_val (smallvec_push ty n) (fn<α>(∅; &uniq{α} (smallvec n ty), ty) → ())
    (λ post '-[(al, al'); a], al' = al ++ [a] → post ()).
  Proof.
    eapply type_fn; [apply _|]=> α ϝ k [v[x[]]]. simpl_subst.
    iIntros (tid (vπ & aπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(v & x &_) #Obs".
    rewrite tctx_hasty_val. iDestruct "v" as ([|dv]) "[_ v]"=>//.
    case v as [[|v|]|]=>//. iDestruct "v" as "[(%vl & >↦ & [#LftIn uniq]) †]".
    case vl as [|[[|v'|]|][]]; try by iDestruct "uniq" as ">[]".
    rewrite heap_mapsto_vec_singleton.  wp_read. wp_let. wp_bind (delete _).
    rewrite -heap_mapsto_vec_singleton freeable_sz_full.
    iApply (wp_delete with "[$↦ $†]"); [done|]. iIntros "!>_".
    iDestruct "uniq" as (du ξi [? Eq2]) "[Vo Bor]". move: Eq2. set ξ := PrVar _ ξi=> Eq2.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (bor_acc_cons with "LFT Bor α") as "[(%&%& #⧖u & Pc & ↦vec) ToBor]"; [done|].
    set bor_body := (∃ vπ' d', ⧖(S d') ∗ .PC[ξ] vπ' d' ∗ (∃ vl : list val, v' ↦∗ vl ∗ ty_own (smallvec n ty) vπ' d' tid vl))%I.
    wp_seq. iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
    rewrite split_mt_smallvec. case du as [|du]=>//.
    iDestruct "↦vec" as (tag ? len ex aπl Eq1) "(↦ & ↦tys)".
    rewrite !heap_mapsto_vec_cons shift_loc_assoc. iDestruct "↦" as "(↦₀ & ↦l & ↦len & ↦ex)".
    wp_read. wp_let. set push := (rec: "push" _ := _)%E.
    iAssert ( v' ↦ #false  -∗ (v' +ₗ 1) ↦∗: ty_own (vec_ty ty) (fst ∘ vπ) (S du) tid -∗ 
      (∃ wl : list val, ⌜length wl = (n * ty_size ty)%nat⌝ ∗ (v' +ₗ 4) ↦∗ wl) -∗
      .PC[ξ] (fst ∘ vπ) (S du) -∗ .VO[ξ] (fst ∘ vπ) (S du) -∗
      (cctx_interp tid postπ [k ◁cont{[_], (λ v : vec val 1, +[vhd v ◁ box ()])} tr_ret]) -∗
      na_own tid ⊤ -∗
      (q'.[α] ={⊤}=∗ llctx_interp [ ϝ ⊑ₗ []] 1)%I -∗
      tctx_elt_interp tid (x ◁ box ty) aπ -∗
      (∀ Q : iPropI Σ, ▷ (▷ Q ={↑lft_userN}=∗ ▷ bor_body) -∗ ▷ Q ={⊤}=∗ &{α} Q ∗ q'.[α]) -∗
      WP push [] {{ _, cont_postcondition }})%I with "[]" as "push".
    { iIntros "↦₀ ↦vec ↦tl Pc Vo C Na ToL Tx ToBor". rewrite /push. wp_rec.
      iMod ("ToBor" $! (bor_cnts (vec_ty ty) (fst ∘ vπ) ξi (S du) _ (v' +ₗ 1))
        with "[↦₀ ↦tl] [↦vec Pc]") as "[o tok]".
      { iIntros "!> Hvec !>". rewrite /bor_cnts. iDestruct "Hvec" as (vπ' d') "(? & ? & Hvals)". rewrite /bor_body.
        iExists vπ', d'. iFrame. iDestruct "Hvals" as (vl) "(>v1 & Hvec)".
        case d' as [|d]=>//=; [by iMod ("Hvec") as "?"|]. iNext.
        iDestruct "Hvec" as (????) "([-> %] & ?)". iDestruct "↦tl" as (?) "(% & ↦tl)".
        iCombine "↦₀ v1" as "↦v". iCombine "↦v ↦tl" as "↦v".
        rewrite -heap_mapsto_vec_cons -heap_mapsto_vec_app.
        iExists _. iFrame.   iExists false, _, _, _, _, _. by iFrame. } 
      { iExists (fst ∘ vπ), (S du). iFrame "# Pc".
        iDestruct "↦vec" as (vl) "(? & v)". iExists vl. iFrame. 
        iDestruct "v" as (????) "(? & ? & ?)". iExists _, _, _, _. iFrame.  }
      iMod ("ToL" with "tok") as "L".
      iAssert (tctx_elt_interp tid (#v' +ₗ #1 ◁ &uniq{α} (vec_ty ty)) vπ ) with "[o Vo]" as "te".
      { iExists _, _. iFrame "# ∗". iSplitR; [done|]. iExists _, ξi. by iFrame. }
      iApply (type_type +[_; _] -[_; _] with "[] LFT TIME PROPH UNIQ E Na L C [$Tx $te]").
      - iApply type_val; [apply vec_push_type|]. intro_subst.
        iApply type_new; [done|]. intro_subst. iApply type_assign; [solve_typing..|].
        iApply (type_letcall α); [solve_typing|solve_extract|solve_typing|]. intro_subst.
        iApply type_jump; [solve_typing| solve_extract| solve_typing].
      - by iApply (proph_obs_impl with "Obs").
    }
    rewrite /push. wp_let. wp_if. case tag.
    { iDestruct "↦tys" as "(Z & ↦vec)". iDestruct "↦vec" as (tl) "(% & ↦tl)".
      set vπ' := λ π, (lapply (vsnoc aπl aπ) π, π ξ).
      wp_op. wp_read. wp_let. do 2 wp_op. wp_if. case_eq (bool_decide (len + 1 ≤ n)%Z) => LenN.
      { iClear "push". assert (len + 1 ≤ n). { case_bool_decide; lia. }
        rewrite tctx_hasty_val. iDestruct "x" as ([|dx]) "[⧖x x]"=>//. case x as [[|x|]|]=>//.
        do 3 wp_op. wp_bind (_ <-{_} !_)%E. iApply (wp_persistent_time_receipt with "TIME ⧖x"); [done|].
        assert (length tl = ty_size ty + (n - len - 1) * ty_size ty) as Len. 
        { rewrite -Nat.sub_add_distr Nat.mul_sub_distr_r Nat.add_sub_assoc; [lia|]. by apply Nat.mul_le_mono_r. }
        move: {Len}(app_length_ex tl _ _ Len)=> [vl'[z[->[Len K]]]].
        rewrite heap_mapsto_vec_app shift_loc_assoc_nat Len -Nat2Z.inj_mul.
        iDestruct "↦tl" as "[↦ ↦tl]". iDestruct "x" as "[(%& ↦x & ty) †x]". iDestruct (ty_size_eq with "ty") as %Sz.
        iApply (wp_memcpy with "[$↦ $↦x]") ; [lia..|].
        iIntros "!> [↦ ↦x] ⧖x". iCombine "⧖u ⧖x" as "#⧖"=>/=. set d := du `max` dx.
        wp_seq. wp_op. wp_op. wp_write.
        iAssert (∃ vl, (v' +ₗ 4 +ₗ[ty] (length aπl)) ↦∗ vl ∗ ty_own ty aπ d tid vl)%I with "[ty ↦]" as "ty_vec".
        { iExists vl. rewrite vec_to_list_length. iFrame. iApply (ty_own_depth_mono with "[$]"); lia. }
        iMod (uniq_update ξ (fst ∘ vπ') with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
        iMod ("ToBor" $! bor_body with "[] [Pc ↦₀ ↦l ↦len ty_vec Z ↦tl ↦ex]") as "[? tok]".
        { by iIntros "!> $". }
        { iExists _, (S d). iFrame "# ∗". iCombine "↦₀ ↦l ↦len ↦ex" as "↦v" .
          rewrite -shift_loc_assoc Nat2Z.inj_add Nat2Z.inj_mul -!shift_loc_assoc  -!heap_mapsto_vec_cons.
          rewrite split_mt_smallvec. iExists true, l, _, ex, (aπl +++ [#aπ]). iFrame. iSplitR.
          { iPureIntro. fun_ext. rewrite /vπ' /= => ?. rewrite vec_to_list_app vec_to_list_snoc lapply_app //=. }
          iSplitL "↦v"; [by rewrite !Nat2Z.inj_add Nat2Z.inj_succ Nat2Z.inj_0 Z.one_succ|]. 
          rewrite vec_to_list_app. iSplitL "ty_vec Z". 
          { rewrite big_sepL_snoc Nat2Z.inj_mul. iFrame. iNext. iClear "#". iStopProof. do 6 f_equiv. apply ty_own_depth_mono. lia. }
          iExists z. rewrite shift_loc_assoc !Nat2Z.inj_mul -Z.mul_succ_l -Z.add_1_r.
          rewrite  Nat2Z.inj_add Nat2Z.inj_succ Nat2Z.inj_0 -Z.one_succ. iFrame.
          iPureIntro. rewrite K -Nat.mul_add_distr_r -Nat.sub_add_distr Nat.add_sub_assoc; lia.                     
        }
        iMod ("ToL" with "tok L") as "L".
        iApply (type_type +[#v' ◁ &uniq{α} (smallvec n ty)] -[vπ'] with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
        - iApply type_new; [done|]. intro_subst. iApply type_jump; [solve_typing|solve_extract|solve_typing].
        - rewrite /= right_id (tctx_hasty_val #_). iExists _.
          iFrame "⧖ LftIn". iExists (S d), ξi.
          rewrite /uniq_body /bor_body /vπ' /ξ (proof_irrel (prval_to_inh (𝔄 := listₛ _) (fst ∘ vπ)) (prval_to_inh (𝔄 := listₛ _) (fst ∘ vπ'))).
          iSplitR. iSplit; [done|]. iPureIntro. fun_ext => ? //=. iFrame.
          - iApply proph_obs_impl;[|done] => π //=.
        move: (equal_f Eq1 π) (equal_f Eq2 π)=>/=. case (vπ π)=>/= ??->-> Imp Eq.
        apply Imp. move: Eq. by rewrite vec_to_list_snoc lapply_app.
      }
      { wp_op. wp_bind (new _). iApply wp_new; [lia| done|].
      iIntros "!>" (?) "[†' ↦']". wp_let. wp_op. wp_op.  wp_bind (memcpy _).
      rewrite trans_big_sepL_mt_ty_own. iDestruct "Z" as (?) "[↦ tys]".  iDestruct (big_sepL_ty_own_length with "tys") as %Len.
      iApply (wp_memcpy with "[$↦' $↦]"); [rewrite repeat_length; lia|lia|].
      iIntros "!>[↦' ↦]". wp_seq. wp_op. rewrite -Nat2Z.inj_mul.
      wp_write. wp_op. iDestruct "↦ex" as "(↦ex & ↦ε)". rewrite !shift_loc_assoc.  wp_write.
      wp_write. iApply ( "push" with "[$]  [tys †' ↦' ↦l ↦ex ↦ε ↦len] [↦tl ↦] [$] [$] [$] [$] [ToL L] [$] ToBor").
        { iExists [_; _; _]. iClear "push". rewrite !heap_mapsto_vec_cons -!shift_loc_assoc. iFrame.
          iExists _, _, 0,_. iSplitR; [done|].  
          rewrite trans_big_sepL_mt_ty_own Nat.add_0_r Nat2Z.id. iFrame. iSplitL. 
          - iExists _. iFrame.
          - iExists [].  rewrite heap_mapsto_vec_nil //=. }
        { iExists (concat wll ++ tl). rewrite heap_mapsto_vec_app app_length Len -!shift_loc_assoc. by iFrame. } 
        { iIntros. iApply ("ToL" with "[$] [$]"). } } }
    { iDestruct "↦tys" as (wl) "(% & ↦tl & proph & a)".
        iApply ( "push" with "[$] [↦l ↦len ↦ex proph a] [↦tl] [$] [$] [$] [$] [ToL L] [$] ToBor").    
        { iExists [_; _; _]. rewrite !heap_mapsto_vec_cons -!shift_loc_assoc. iFrame. iExists _, _, _, _. by iFrame. }
        { iExists wl. by iFrame. }
        { iIntros "?". iApply ("ToL" with "[$] [$]"). }
    }
  Qed.
End smallvec_push.