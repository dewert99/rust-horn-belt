From iris.proofmode Require Import environments.
From lrust.typing Require Export type.
From lrust.typing Require Import typing lib.panic .

Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section option.
  Context `{!typeG Σ}.

  Definition sum' A B : Type := A + (B + ∅).

  Definition option_to_sum' {A} (o: option A) : sum' () A :=
    match o with None => inl () | Some x => (inr (inl x)) end.
  Definition sum'_to_option {A} (s: sum' () A) : option A :=
    match s with inl _ => None | inr (inl x) => Some x
      | inr (inr a) => absurd a end.
  Global Instance option_sum'_iso {A} : Iso (@option_to_sum' A) sum'_to_option.
  Proof. split; fun_ext; case=>//; by case. Qed.

  Definition option_ty {𝔄} (ty: type 𝔄) : type (optionₛ 𝔄) :=
    <{sum'_to_option: (Σ! [(); 𝔄])%ST → optionₛ 𝔄}> (Σ! +[(); ty])%T.

  Lemma option_leak {𝔄} E L (ty: type 𝔄) Φ :
    leak E L ty Φ →
    leak E L (option_ty ty) (λ o, match o with None => True | Some o => Φ o end).
  Proof. move=> ?. eapply leak_impl; [solve_typing|]. by case. Qed.

  Lemma option_leak_just {𝔄} E L (ty: type 𝔄) :
    leak E L ty (const True) → leak E L (option_ty ty) (const True).
  Proof. move=> ?. apply leak_just. Qed.

  Lemma option_subtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (option_ty ty) (option_ty ty') (option_map f).
  Proof. move=> ?. eapply subtype_eq; [solve_typing|]. fun_ext. by case. Qed.

  Lemma option_eqtype {𝔄 𝔅} E L (f: 𝔄 → 𝔅) g ty ty' :
    eqtype E L ty ty' f g →
    eqtype E L (option_ty ty) (option_ty ty') (option_map f) (option_map g).
  Proof. move=> [??]. split; by apply option_subtype. Qed.


  (* Variant indices. *)
  Definition none := 0%nat.
  Definition some := 1%nat.

  Definition option_as_mut : val :=
    fn: ["o"] :=
      let: "o'" := !"o" in
      let: "r" := new [ #2 ] in
    withcont: "k":
      case: !"o'" of
        [ "r" <-{Σ none} ();; jump: "k" [];
          "r" <-{Σ some} "o'" +ₗ #1;; jump: "k" [] ]
    cont: "k" [] :=
      delete [ #1; "o"];; return: ["r"].

  Lemma tctx_extract_ctx_eq {𝔄 𝔅l ℭl} tr tr' E L
      (t: _ 𝔄) (T1: tctx 𝔅l) (T2: tctx ℭl) :
      tctx_extract_elt E L t T1 T2 tr' → tr = tr' → tctx_extract_elt E L t T1 T2 tr.
Proof. by move=> ? ->. Qed.

  Lemma option_as_mut_type {𝔄} (τ : _ 𝔄) :
    typed_val
      option_as_mut (fn<α>(∅; &uniq{α} (option_ty τ)) → option_ty (&uniq{α} τ))
      (λ (post : of_syn_type (predₛ (optionₛ (_ * _))))  '-[a], match a with
        | (Some a, Some a') => post (Some (a, a'))
        | (None, None) => post None
        | _ => False
      end).
  Proof.
    eapply type_fn; [solve_typing|]. iIntros (α ϝ ret [o []]). simpl_subst. via_tr_impl.
    iApply type_deref; [solve_extract|solve_typing..|]. iIntros (o'). simpl_subst.
    iApply type_new; [solve_typing..|]. iIntros (r). simpl_subst.
    iApply (type_cont [] (λ _, +[o ◁ _ ; r ◁ _ ]) [ϝ ⊑ₗ []]).
    iIntros (k). simpl_subst. set E := fp_E _ _. set L := [ϝ ⊑ₗ []].
    - iApply (type_case_uniq (𝔄l := [_ ; _ ]) +[inl _; inl _] _ _ _ _ +[_; _] _ α +[unit_ty; τ]);
      [ solve_typing | solve_typing | | solve_typing | ].
      eapply tctx_extract_elt_further, tctx_uniq_mod_ty_out'; [apply _| solve_typing].
      constructor; last constructor; last constructor.
      + iStartProof;
        match goal with |- envs_entails _ (typed_body _ _ [k ◁cont{_, _} ?c; _] _ _ _) =>
            iApply (typed_body_impl (𝔄l:=[_; _; _]) (λ post '-[e; f; d], c post -[d; _] )); last first
        end.
        iApply (type_sum_unit _ +[unit_ty ; (&uniq{α} τ)%T] 0 _ _ _  _  _  _ _  _ _  _  _ eq_refl); [solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
        rewrite /compose /= => ? [? [? [ ? []]]]  //.
      + iStartProof;
        match goal with |- envs_entails _ (typed_body _ _ [k ◁cont{_, _} ?c; _] _ _ _) =>
          iApply (typed_body_impl (𝔄l:=[(𝔄 * 𝔄)%ST; _; _]) (λ post '-[e; f; d], c post -[d; inr (inl e)] )); last first
        end.
        iApply (type_sum_assign _ +[() ; &uniq{α} τ]%T 1 _ _ _); [try solve_typing..|].
        iApply type_jump; [solve_typing|solve_extract|solve_typing].
        rewrite /compose /= => ? [? [? [? []]]] //.
    - iIntros "/= !>". iIntros (k args). inv_vec args. simpl_subst.
      iApply (typed_body_impl (𝔄l := [() ; Σ! [(); _]]%ST) (𝔅 := optionₛ _) (λ post '-[_; b], post (sum'_to_option b))); last first.
      iApply type_delete; [solve_extract|solve_typing..|].
      iApply type_jump; [solve_typing| |solve_typing].
      eapply tctx_extract_ctx_elt; last solve_extract.
      eapply tctx_extract_elt_here, own_subtype, mod_ty_in.
      rewrite /compose /= => ? [? [b []]] //.
    - move => ? [[+ +] []] + ?? ++ [|[|?]] //=.
      + move => [?|] [?|] // _  ++ ?? [= ??]. by subst.
      + move => [?|] [?|] // ? ++ ?? [= ??]; subst; try done.
        move => [= <-] [= <-] //.
      + move => ?? _ _ _ [[] _].
  Qed.

  Definition option_unwrap_or {𝔄} (τ : type 𝔄) : val :=
    fn: ["o"; "def"] :=
      case: !"o" of
      [ delete [ #(S τ.(ty_size)); "o"];;
        return: ["def"];

        letalloc: "r" <-{τ.(ty_size)} !("o" +ₗ #1) in
        delete [ #(S τ.(ty_size)); "o"];; delete [ #τ.(ty_size); "def"];;
        return: ["r"]].

  Lemma option_unwrap_or_type {𝔄} (τ : type 𝔄) :
    typed_val (option_unwrap_or τ) (fn(∅; option_ty τ, τ) → τ)
      (λ post '-[opt; def], match opt with
        | Some v => post v
        | None => post def
      end).
  Proof.
    eapply type_fn; [solve_typing|]. iIntros (α ϝ ret [o []]). simpl_subst. via_tr_impl.
    iApply (type_case_own +[inr _; inl _]); [solve_typing..| ].
    constructor; last constructor; last constructor.
    + iApply (typed_body_impl (𝔄l := [_; _]) (λ post '-[_; a], post a)); last first.
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
      rewrite /compose /= => ? [? [? []]] H //=.
    +
      iApply (typed_body_impl (𝔄l := [_; _; _; _]) (λ post '-[_; a; _; _], post a)); last first.
      iApply type_letalloc_n; [solve_typing..|]. iIntros (r). simpl_subst.
      iApply (type_delete (Π! +[↯ _;↯ _;↯ _]%T)); [solve_typing..|].
      iApply type_delete; [solve_typing..|].
      iApply type_jump; solve_typing.
      rewrite /compose /=  => ? [? [? [? [? []]]]] //=.
    + move => ? [[opt|] [def []]].
      * move => ? [|[|i]] //= => [[? ?] | ? [= <-] | [? ?]] //=.
      * move => ? [|[|i]] //= [? ?] //.
  Qed.

  Definition option_unwrap {𝔄} (τ : type 𝔄) : val :=
    fn: ["o"] :=
      case: !"o" of
      [ let: "panic" := panic in
        letcall: "emp" := "panic" [] in
        case: !"emp" of [];

        letalloc: "r" <-{τ.(ty_size)} !("o" +ₗ #1) in
        delete [ #(S τ.(ty_size)); "o"];;
        return: ["r"]].

  Lemma option_unwrap_type {𝔄} (τ : type 𝔄) :
    typed_val (option_unwrap τ) (fn(∅; option_ty τ) → τ)
    (λ post '-[o], match o with
      | Some v => post v
      | None => False
    end).
  Proof.
    eapply type_fn; [solve_typing|]. iIntros (α ϝ ret [o []]). simpl_subst. via_tr_impl.
    iApply (type_case_own +[inr _; inl _]); [solve_typing..| ]. constructor; last constructor; last constructor.
    + iApply (typed_body_impl (λ _ _, False)); last first.
      iApply type_val;[eapply panic_type|].
      iIntros (panic). simpl_subst.
      iApply (type_letcall ()); [solve_typing..|]. iIntros (r). simpl_subst.
      iApply (type_case_own +[]); [solve_typing..|]. constructor.
      rewrite /compose //=.
    + iApply (typed_body_impl (𝔄l := [_; _; _]) (λ post '-[_; a; _], post a)); last first.
      iApply type_letalloc_n; [solve_typing..|]. iIntros (r). simpl_subst.
      iApply (type_delete (Π! +[uninit _;uninit _;uninit _])); [solve_typing..|].
      iApply type_jump; solve_typing.
      rewrite /compose /= => ? [? [? [? []]]] //=.
    + move => ? [[?|] []] ? [|[|i]] //= => [[? ?] |? [= <-]|[? ?]] //.
  Qed.
End option.

Global Hint Resolve option_leak | 5 : lrust_typing.
Global Hint Resolve option_leak_just option_subtype option_eqtype : lrust_typing.
