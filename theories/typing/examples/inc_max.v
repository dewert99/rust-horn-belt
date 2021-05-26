From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Open Scope Z_scope.

Section inc_max.
  Context `{!typeG Σ}.

  Definition take_max: val :=
    fn: ["oua"; "oub"] :=
      let: "ua" := !"oua" in let: "ub" := !"oub" in
      let: "a" := !"ua" in let: "b" := !"ub" in let: "ord" := "b" ≤ "a" in
      if: "ord" then
        "oua" <- "ua";; return: ["oua"]
      else
        "oub" <- "ub";; return: ["oub"].

  Lemma type_take_max :
    typed_val take_max (fn<α>(∅; &uniq{α} int, &uniq{α} int) → &uniq{α} int)
      (λ (post: pred' (_*_)) '-[(a, a'); (b, b')], if bool_decide (b ≤ a)
        then b' = b → post (a, a') else a' = a → post (b, b')).
  Proof.
    eapply type_fn; [solve_typing|]=>/= ???[?[?[]]]. simpl_subst. via_tr_impl.
    { unshelve (
        do 2 (iApply type_deref; [solve_extract|solve_typing|done|];
          intro_subst; cushion_tr);
        do 2 (iApply type_deref; [solve_extract|solve_typing|done|];
          intro_subst; cushion_tr);
        iApply type_le; [solve_extract|]; intro_subst; cushion_tr;
        iApply type_if; [solve_extract| |]; (cushion_tr; iApply type_assign;
          [solve_extract|solve_typing|solve_typing|]; cushion_tr;
          iApply type_jump; [solve_typing|solve_extract|solve_typing]));
      revgoals. by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr.
      by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr. }
    by move=> ?[[??][[??][]]]/=.
  Qed.
  
  Definition inc_max: val :=
    fn: ["oa"; "ob"] := Newlft;;
      letalloc: "oua" <- "oa" in letalloc: "oub" <- "ob" in
      let: "take_max" := take_max in
      letcall: "ouc" := "take_max" ["oua"; "oub"] in
      let: "uc" := !"ouc" in let: "c" := !"uc" in let: "1" := #1 in
      let: "c'" := "c" + "1" in "uc" <- "c'";;
      letcont: "ret" ["oa"; "ob"] := Endlft;;
        let: "a" := !"oa" in let: "b" := !"ob" in let: "d" := "a" - "b" in
        letalloc: "od" <- "d" in return: ["od"] in
      jump: "ret" ["oa"; "ob"].

  Lemma type_inc_max :
    typed_val inc_max (fn(∅; int, int) → int)
      (λ (post: pred' _) _, ∀n, n ≠ 0 → post n).
  Proof.
    eapply type_fn; [solve_typing|]=>/= _ ??[?[?[]]]. simpl_subst. via_tr_impl.
    { unshelve (
        iApply type_newlft; iIntros (α); cushion_tr;
        do 2 (iApply (type_letalloc_1 (&uniq{α} _)); [solve_extract|done|];
          intro_subst; cushion_tr);
        iApply type_val; [apply type_take_max|]; intro_subst; cushion_tr;
        iApply type_letcall; [solve_typing|solve_extract|solve_typing|];
        intro_subst; cushion_tr;
        do 2 (iApply type_deref; [solve_extract|solve_typing|done|];
          intro_subst; cushion_tr);
        iApply type_int; intro_subst; cushion_tr; iApply type_plus;
        [solve_extract|]; intro_subst; cushion_tr; iApply type_assign;
        [solve_extract|solve_typing|solve_typing|]; cushion_tr;
        iApply (type_cont_norec [_;_] (λ vl, +[vhd vl ◁{_} _; vhd (vtl vl) ◁{_} _]));
        [intro_subst; iApply type_jump; [solve_typing|solve_extract|solve_typing]|];
        iIntros (? vl); inv_vec vl; iIntros; simpl_subst;
        iApply type_endlft; [solve_typing|]; cushion_tr;
        do 2 (iApply type_deref; [solve_extract|solve_typing|done|];
          intro_subst; cushion_tr);
        iApply type_minus; [solve_extract|]; intro_subst; cushion_tr;
        iApply type_letalloc_1; [solve_extract|done|]; intro_subst; cushion_tr;
        iApply type_jump; [solve_typing|solve_extract|solve_typing]);
      revgoals. by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr.
      by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr.
      by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr. by_simpl_tr. }
    move=>/= ?[a[b[]]] Imp ??.
    case Le: (bool_decide (b ≤ a))=> ->->; apply Imp; move: Le;
    [rewrite bool_decide_eq_true|rewrite bool_decide_eq_false]; lia.
  Qed.
End inc_max.
