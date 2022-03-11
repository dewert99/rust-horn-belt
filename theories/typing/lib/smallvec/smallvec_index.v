From lrust.typing Require Export type.
From lrust.typing Require Import array_util typing.
From lrust.typing.lib.smallvec Require Import smallvec.
Set Default Proof Using "Type".

Open Scope nat.
Implicit Type 𝔄 𝔅: syn_type.

Section smallvec_index.
  Context `{!typeG Σ}.

  Definition smallvec_index {𝔄} (ty: type 𝔄) : val :=
    fn: ["v"; "i"] :=
      let: "r" := new [ #1] in
      if: !(!"v") then
        "r" <- !"v" +ₗ #4 +ₗ !"i" * #ty.(ty_size);;
        delete [ #1; "v"];; delete [ #1; "i"];;
        return: ["r"]
      else
        "r" <- !(!"v" +ₗ #1) +ₗ !"i" * #ty.(ty_size);;
        delete [ #1; "v"];; delete [ #1; "i"];;
        return: ["r"].

  (* The precondition requires that the index is within bounds of the list *)
  Lemma smallvec_index_shr_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_index ty) (fn<α>(∅; &shr{α} (smallvec n ty), int) → &shr{α} ty)
      (λ post '-[al; z], ∃(i: nat) (a: 𝔄), z = i ∧ al !! i = Some a ∧ post a).
  Proof.
    eapply type_fn; [apply _|]=> α ??[v[i[]]]. simpl_subst.
    iIntros (?(?&?&[])?) "LFT TIME PROPH _ E Na L C (v & i & _) #Obs".
    rewrite !tctx_hasty_val.
    iDestruct "v" as ([|d]) "[⧖ v]"=>//. case v as [[|v|]|]=>//=.
    iDestruct "i" as ([|]) "[_ i]"=>//. case i as [[|i|]|]=>//=.
    iDestruct "v" as "[(%vl & >↦v & svec) †v]". wp_bind (new _).
    iApply wp_new; [done..|]. iIntros "!>% [†r ↦r]". wp_let.
    case d as [|d]=>//. case vl as [|[[]|][]]=>//. case d as [|d]=>//.
    iDestruct "svec" as (?????->) "[Bor tys]".
    iDestruct "i" as "[(%& ↦i & (%&->&->)) †i]"=>/=.
    iMod (lctx_lft_alive_tok α with "E L") as (?) "(α & L & ToL)"; [solve_typing..|].
    iMod (frac_bor_acc with "LFT Bor α") as (?) "[>↦ Toα]"; [done|].
    rewrite !heap_mapsto_vec_singleton !heap_mapsto_vec_cons !heap_mapsto_vec_nil.
    iDestruct "↦" as "(↦₀ & ↦₁ & ↦₂ & ↦₃ &_)". do 2 wp_read. case b; wp_case.
    - wp_read. wp_op. wp_read. do 2 wp_op. wp_write.
      iMod ("Toα" with "[$↦₀ $↦₁ $↦₂ $↦₃]") as "α". iMod ("ToL" with "α L") as "L".
      do 2 rewrite -heap_mapsto_vec_singleton freeable_sz_full.
      wp_bind (delete _). iApply (wp_delete with "[$↦v $†v]"); [done|].
      iIntros "!> _". wp_seq. wp_bind (delete _).
      iApply (wp_delete with "[$↦i $†i]"); [done|]. iIntros "!> _". do 3 wp_seq.
      iMod (proph_obs_sat with "PROPH Obs") as %(?& inat &?&->& Lkup &_); [done|].
      move: Lkup. rewrite -vec_to_list_apply -vlookup_lookup'. move=> [In _].
      set ifin := nat_to_fin In. have Eqi: inat = ifin by rewrite fin_to_nat_to_fin.
      rewrite cctx_interp_singleton.
      iApply ("C" $! [# #_] -[aπl !!! ifin] with "Na L [-] []").
      + iSplit; [|done]. rewrite tctx_hasty_val. iExists (S (S d)).
        iSplit. { iApply persistent_time_receipt_mono; [|done]. lia. }
        rewrite/= freeable_sz_full. iFrame "†r". iNext. iExists [_].
        rewrite heap_mapsto_vec_singleton. iFrame "↦r".
        rewrite/= -Nat2Z.inj_mul Eqi. iApply (big_sepL_vlookup with "tys").
      + iApply proph_obs_impl; [|done]=>/= ?[?[?[/Nat2Z.inj <-[++]]]].
        by rewrite Eqi -vlookup_lookup -vapply_lookup=> <-.
    - wp_read. wp_op. do 2 wp_read. do 2 wp_op. wp_write.
      iMod ("Toα" with "[$↦₀ $↦₁ $↦₂ $↦₃]") as "α". iMod ("ToL" with "α L") as "L".
      do 2 rewrite -heap_mapsto_vec_singleton freeable_sz_full.
      wp_bind (delete _). iApply (wp_delete with "[$↦v $†v]"); [done|].
      iIntros "!> _". wp_seq. wp_bind (delete _).
      iApply (wp_delete with "[$↦i $†i]"); [done|]. iIntros "!> _". do 3 wp_seq.
      iMod (proph_obs_sat with "PROPH Obs") as %(?& inat &?&->& Lkup &_); [done|].
      move: Lkup. rewrite -vec_to_list_apply -vlookup_lookup'. move=> [In _].
      set ifin := nat_to_fin In. have Eqi: inat = ifin by rewrite fin_to_nat_to_fin.
      rewrite cctx_interp_singleton.
      iApply ("C" $! [# #_] -[aπl !!! ifin] with "Na L [-] []").
      + iSplit; [|done]. rewrite tctx_hasty_val. iExists (S (S d)).
        iSplit. { iApply persistent_time_receipt_mono; [|done]. lia. }
        rewrite/= freeable_sz_full. iFrame "†r". iNext. iExists [_].
        rewrite heap_mapsto_vec_singleton. iFrame "↦r".
        rewrite/= -Nat2Z.inj_mul Eqi. iApply (big_sepL_vlookup with "tys").
      + iApply proph_obs_impl; [|done]=>/= ?[?[?[/Nat2Z.inj <-[++]]]].
        by rewrite Eqi -vlookup_lookup -vapply_lookup=> <-.
  Qed.

  (* The precondition requires that the index is within bounds of the list *)
  Lemma smallvec_index_uniq_type {𝔄} n (ty: type 𝔄) :
    typed_val (smallvec_index ty) (fn<α>(∅; &uniq{α} (smallvec n ty), int) → &uniq{α} ty)
      (λ post '-[(al, al'); z], ∃(i: nat) (a: 𝔄), z = i ∧
        al !! i = Some a ∧ ∀a': 𝔄, al' = <[i := a']> al → post (a, a')).
  Proof.
  Admitted.
End smallvec_index.
