From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util typing ptr.
From lrust.typing.lib Require Import ghostptrtoken.ghostptrtoken.
Set Default Proof Using "Type".

Open Scope nat.

Implicit Type 𝔄 𝔅: syn_type.

Section ghostptrtoken_borrow.
  Context `{!typeG Σ}.

  Definition ghostptrtoken_borrow {𝔄} (ty: type 𝔄) : val :=
    fn: ["t"; "p"] :=
      delete [ #1; "t"];;
      return: ["p"].

  (* Rust's GhostPtrToken::borrow_mut *)
  Lemma ghostptrtoken_borrow_type {𝔄} (ty: type 𝔄):
    typed_val (ghostptrtoken_borrow ty) (fn<α>(∅; &shr{α} (ghostptrtoken_ty ty), ptr) → &shr{α} ty)
      (λ post '-[l; ptr], exists v, (list_to_gmap l) !! ptr = Some(v) ∧ post (v)).
  Proof.
    fold of_syn_type. eapply type_fn; [apply _|]=> ???[ol[pl[]]]. simpl_subst.
    iIntros (?(lπ & pπ &[]) ?) "#LFT #TIME #PROPH #UNIQ #E Na L C /=(ol & p &_) #Obs".
    rewrite !tctx_hasty_val. iDestruct "ol" as ([|dm]) "[⧖ ol]"=>//.
    case ol as [[|ol|]|]=>//. iDestruct "ol" as "[(%oll & >↦ol & shr) †ol]".
    destruct dm; [by iDestruct "shr" as ">[]"|].
    case oll as [|[[|oll|]|][]]; try  by iDestruct "shr" as ">[]".
    iDestruct "p" as ([|dx]) "[_ p]"=>//. case pl as [[|pl|]|]=>//=.
    iDestruct "p" as "[p' †p]".
    wp_bind (delete _). rewrite freeable_sz_full.
    iApply ((wp_delete [ #oll])with "[↦ol †ol]"); [done| by iFrame|]. 
    iNext. iIntros. destruct dm; [done|].
    iDestruct "shr" as "(%aπl&->&shr)".
    iDestruct "p'" as (?) "(↦p&(%p&->&->))". simpl.
    remember ((list_to_gmap aπl) !! p) as vπ. symmetry in Heqvπ. destruct vπ as [vπ|]; last first.
    iMod (proph_obs_sat with "PROPH Obs") as %(πw&obs). done.
    exfalso. destruct obs as (v&obs&_). 
    rewrite /alapply list_to_map_fmap lookup_fmap Heqvπ in obs.
    done.
    destruct (elem_of_list_to_map_2' _ _ _ Heqvπ) as (rπ&perm&reinsert).
    unfold big_sepAL.
    iEval (rewrite perm big_sepL_cons) in "shr".
    iDestruct "shr" as "(shr&_)".
    do 3 wp_seq.
    rewrite cctx_interp_singleton.
    iApply ("C" $! [# #_] -[vπ] with "Na L [-Obs] [Obs]"). iSplit; [|done].
    rewrite (tctx_hasty_val #_). iExists _. iFrame "⧖ †p".
    iNext. iExists _. iFrame "↦p". simpl.
    iApply (ty_shr_depth_mono with "shr"). lia.
    iApply (proph_obs_impl with "Obs").
    move => ?/= [?[lookup?]].
    rewrite /alapply list_to_map_fmap lookup_fmap Heqvπ in lookup.
    injection lookup as ->. done.
  Qed.

End ghostptrtoken_borrow.
