Import EqNotations.
From iris.algebra Require Import vector list.
From lrust.typing Require Export type.
From lrust.typing Require Import own programs cont.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Fixpoint subst_plv {𝔄l} (bl: plistc binder 𝔄l) (vl: plistc val 𝔄l)
  (e: expr) : expr := match 𝔄l, bl, vl with [], _, _ => e |
    _ :: _, b -:: bl', v -:: vl' => subst' b v (subst_plv bl' vl' e) end.

Instance do_subst_plv {𝔄l} (bl vl: plistc _ 𝔄l) e :
  DoSubstL bl (map of_val vl) e (subst_plv bl vl e).
Proof.
  rewrite /DoSubstL. induction 𝔄l, bl, vl; [done|]=>/=. by rewrite IH𝔄l.
Qed.

Lemma subst_plv_renew {𝔄l 𝔅l} (bl: _ 𝔄l) (vl': _ 𝔅l) ew e :
  subst_plv (plistc_renew ew bl) vl' e =
    subst_plv bl (plistc_renew (symm_eq_len_wit ew) vl') e.
Proof.
  move: 𝔄l 𝔅l bl vl' ew. fix FIX 1. case=> [|??]; case=>//= ??[??][??]?.
  f_equal. apply FIX.
Qed.

Section fn.
  Context `{!typeG Σ} {A: Type} {𝔄l 𝔅}.

  Record fn_params :=
    FP { fp_E_ex: lft → elctx;  fp_ityl: typel 𝔄l;  fp_oty: type 𝔅 }.

  Definition fn_params_dist n fp fp' : Prop :=
    (∀ϝ, fp.(fp_E_ex) ϝ = fp'.(fp_E_ex) ϝ) ∧
    fp.(fp_ityl) ≡{n}≡ fp'.(fp_ityl) ∧ fp.(fp_oty) ≡{n}≡ fp'.(fp_oty).

  Definition fp_E (fp: fn_params) ϝ : elctx :=
    fp.(fp_E_ex) ϝ ++ tyl_E fp.(fp_ityl) ++ tyl_outlv_E fp.(fp_ityl) ϝ ++
    fp.(fp_oty).(ty_E) ++ ty_outlv_E fp.(fp_oty) ϝ.

  Global Instance fp_E_ne n : Proper (fn_params_dist n ==> (=) ==> (=)) fp_E.
  Proof.
    rewrite /fp_E. move=> ?? Eq ??->. move: Eq=> [->[Eqi Eqo]].
    f_equiv. do 2 (f_equiv; [by rewrite Eqi|]). by rewrite Eqo.
  Qed.

  Program Definition fn (fp: A → fn_params) : type (predₛ 𝔅 → predlₛ 𝔄l) :=
    {| (* FIXME : The definition of ty_lfts is less restrictive than the one
          used in Rust. In Rust, the type of parameters are taken into account
          for well-formedness, and all the liftime constrains relating a
          generalized liftime are ignored. For simplicity, we ignore all of
          them, but this is not very faithful. *)
      pt_size := 1;
      pt_own (tr: (predₛ _ → predlₛ _)%ST) tid vl := tc_opaque
        (∃fb kb (bl: plistc _ _) e H, ⌜vl = [@RecV fb (kb :: bl) e H]⌝ ∗
        ▷ □ ∀x ϝ k ℭl (T: _ ℭl) pre (wl: plistc _ _),
          typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
            [k ◁cont{[ϝ ⊑ₗ []], λ v: vec _ 1, vhd v ◁ box (fp x).(fp_oty) +:: T} pre]
            (hzip_with (λ _ ty (w: val), w ◁ box ty) (fp x).(fp_ityl) wl h++ T)
            (subst' fb (RecV fb (kb :: bl) e) $ subst' kb k $ subst_plv bl wl e)
            (λ acl, tr (λ b: 𝔅, pre (b -:: psepr acl)) (psepl acl)))
    |}%I.
  Next Obligation. rewrite /tc_opaque. apply _. Qed.
  Next Obligation. move=> *. by iDestruct 1 as (?????->) "?". Qed.

  Global Instance fn_ne n :
    Proper (pointwise_relation A (fn_params_dist n) ==> (≡{n}≡)) fn.
  Proof.
    move=> fp fp' Eq. apply ty_of_st_ne, st_of_pt_ne. split; [done|]=>/= ???.
    do 5 apply bi.exist_ne=> ?. do 3 f_equiv. f_equiv=> x. (do 11 f_equiv)=> wl.
    rewrite /typed_body. (do 3 f_equiv)=> vπl.
    do 6 f_equiv; [by eapply fp_E_ne|]. do 2 f_equiv; [|f_equiv].
    - rewrite !cctx_interp_singleton /cctx_elt_interp. do 3 f_equiv.
      case=>/= [??]. rewrite /tctx_elt_interp. do 12 f_equiv. apply Eq.
    - move: (Eq x)=> [_[+ _]]. rewrite {1}/dist.
      move: (fp x).(fp_ityl) (fp' x).(fp_ityl)=> ??. clear=> Eq.
      dependent induction Eq; [done|]. case wl=> ??. case vπl=> ??/=.
      f_equiv; [|by apply IHEq]. rewrite /tctx_elt_interp. by do 8 f_equiv.
  Qed.

End fn.

Arguments fn_params {_ _} _ _.

Instance elctx_empty : Empty (lft → elctx) := λ _, [].

Notation "fn< p > ( E ; ity , .. , ity' ) → oty" :=
  (fn (λ p, FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn< p > ( E ) → oty" := (fn (λ p, FP E%EL +[] oty%T))
  (at level 99, p pattern, oty at level 200, format
    "fn< p > ( E )  →  oty") : lrust_type_scope.
Notation "fn( E ; ity , .. , ity' ) → oty" :=
  (fn (λ _: (), FP E%EL (ity%T +:: .. (+[ity'%T]) ..) oty%T))
  (at level 99, oty at level 200, format
    "fn( E ;  ity ,  .. ,  ity' )  →  oty") : lrust_type_scope.
Notation "fn( E ) → oty" := (fn (λ _: (), FP E%EL +[] oty%T))
  (at level 99, oty at level 200, format "fn( E )  →  oty") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance fn_type_contr {A 𝔄l 𝔅 ℭ} E (IT: A → _ ℭ → _ 𝔄l) (OT: _ → _ → _ 𝔅) :
    (∀x, ListTypeNonExpansive (IT x)) → (∀x, TypeNonExpansive (OT x)) →
    TypeContractive (λ ty, fn (λ x, FP (E x) (IT x ty) (OT x ty))).
  Proof.
    move=> NeIT NeOT.
    have Eq: (∀n ty ty', ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
      elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
      (∀vπ d tid vl, dist_later n (ty.(ty_own) vπ d tid vl) (ty'.(ty_own) vπ d tid vl)) →
      (∀vπ d κ tid l, (ty.(ty_shr) vπ d κ tid l) ≡{n}≡ (ty'.(ty_shr) vπ d κ tid l)) →
      ∀vπ vl,
        (fn (λ x, FP (E x) (IT x ty) (OT x ty))).(ty_own) vπ 0 xH vl ≡{n}≡
        (fn (λ x, FP (E x) (IT x ty') (OT x ty'))).(ty_own) vπ 0 xH vl); last first.
    { split; [|done| |].
      - apply (type_lft_morph_const _ static [])=>//= ?. apply lft_equiv_refl.
      - move=> *. by apply Eq.
      - move=>/= n *. apply bi.exist_ne=> ?. apply bi.sep_ne; [done|].
        apply uPred_primitive.later_contractive. destruct n=>/=; [done|by apply Eq]. }
    move=>/= n ty ty' *. apply bi.exist_ne=> ?. apply bi.sep_ne; [done|].
    do 5 apply bi.exist_ne=> ?. f_equiv. f_contractive. (do 2 f_equiv)=> x.
    (do 11 f_equiv)=> wl. rewrite /typed_body. (do 3 f_equiv)=> acπl.
    move: (papp_ex acπl)=> [aπl[?->]]. move: (NeIT x)=> [ITl[->NeITl]].
    have EqBox: ∀𝔄 (T: _ → _ 𝔄), TypeNonExpansive T → ∀vπ d tid vl,
      (box (T ty)).(ty_own) vπ d tid vl ≡{n}≡ (box (T ty')).(ty_own) vπ d tid vl.
    { move=> ?? Ne. apply box_type_contr=> *.
      - by apply Ne.
      - by iApply type_lft_morph_lft_equiv_proper.
      - apply type_lft_morph_elctx_interp_proper=>//. apply _.
      - apply dist_dist_later. by apply Ne.
      - apply dist_S. by apply Ne. }
    do 5 f_equiv; [|do 3 f_equiv; [|f_equiv]].
    - apply equiv_dist. rewrite /fp_E /= !elctx_interp_app.
      do 2 f_equiv; [|f_equiv; [|f_equiv]].
      + elim: NeITl; [done|]=> ????? _ ?. rewrite /tyl_E /= !elctx_interp_app.
        f_equiv; [|done]. apply type_lft_morph_elctx_interp_proper=>//. apply _.
      + elim: NeITl; [done|]=> ????? _ ?. rewrite /tyl_outlv_E /= !elctx_interp_app.
        f_equiv; [|done]. rewrite !elctx_interp_ty_outlv_E.
        apply lft_incl_equiv_proper_r. by iApply type_lft_morph_lft_equiv_proper.
      + apply type_lft_morph_elctx_interp_proper=>//. apply _.
      + rewrite !elctx_interp_ty_outlv_E. apply lft_incl_equiv_proper_r.
        by iApply type_lft_morph_lft_equiv_proper.
    - rewrite !cctx_interp_singleton /cctx_elt_interp. do 3 f_equiv. case=>/= ??.
      do 4 f_equiv. rewrite /tctx_elt_interp. do 6 f_equiv. by apply EqBox.
    - clear -NeITl EqBox. induction NeITl, wl, aπl; [done|]=>/=.
      f_equiv; [|done]. rewrite /tctx_elt_interp. do 6 f_equiv. by apply EqBox.
  Qed.

  Global Instance fn_send {A 𝔄l 𝔅} (fp: A → _ 𝔄l 𝔅) : Send (fn fp).
  Proof. done. Qed.

  Local Lemma subtypel_llctx_big_sep_box {𝔄l 𝔅l} (tyl: _ 𝔄l) (tyl': _ 𝔅l) fl q E L :
    subtypel E L tyl tyl' fl →
    llctx_interp L q -∗ □ (elctx_interp E -∗
      [∗ hlist] ty; ty';- f ∈ tyl; tyl';- fl, type_incl (box ty) (box ty') f).
  Proof.
    elim=> [|>/box_subtype Sub _ IH]; [by iIntros "_!>_"|]. iIntros "L".
    iDestruct (Sub with "L") as "#Sub". iDestruct (IH with "L") as "#IH".
    iIntros "!> #E /=". iDestruct ("Sub" with "E") as "$".
    iDestruct ("IH" with "E") as "$".
  Qed.

  Lemma fn_subtype {A 𝔄l 𝔄l' 𝔅 𝔅'} (fp: A → _) fp' (fl: _ 𝔄l' 𝔄l) (g: 𝔅 → 𝔅') E L :
    (∀x ϝ, let E' := E ++ fp_E (fp' x) ϝ in elctx_sat E' L (fp_E (fp x) ϝ) ∧
      subtypel E' L (fp' x).(fp_ityl) (fp x).(fp_ityl) fl ∧
      subtype E' L (fp x).(fp_oty) (fp' x).(fp_oty) g) →
    subtype E L (fn fp) (fn fp')
     (λ tr (pre: predₛ _) (al': Π!%ST _), tr (pre ∘ g) (plist_map fl al')).
  Proof.
    move=> Big. apply subtype_plain_type=>/= ?. iIntros "L".
    iAssert (∀x ϝ, □ (elctx_interp (E ++ fp_E (fp' x) ϝ) -∗
      elctx_interp (fp_E (fp x) ϝ) ∗
      ([∗ hlist] ty'; ty;- f ∈ (fp' x).(fp_ityl); (fp x).(fp_ityl);- fl,
        type_incl (box ty') (box ty) f) ∗
      type_incl (box (fp x).(fp_oty)) (box (fp' x).(fp_oty)) g))%I as "#Big".
    { iIntros (x ϝ). case (Big x ϝ)=> Efp
        [/subtypel_llctx_big_sep_box Il /box_subtype O].
      iDestruct (Efp with "L") as "#Efp". iDestruct (Il with "L") as "#Il".
      iDestruct (O with "L") as "#O". iIntros "!> E'".
      iSplit; last iSplit; by [iApply "Efp"|iApply "Il"|iApply "O"]. }
    iIntros "!> #E". iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
    iIntros (tr _ vl). iDestruct 1 as (fb kb bl e H ->) "#fn".
    set ew := symm_eq_len_wit (plist2_eq_len_wit fl). set bl' := plistc_renew ew bl.
    have Eq: (bl: list _) = bl' by rewrite plistc_renew_eq.
    iExists fb, kb, bl', e, (rew [λ bl₀, _ (_ :b: _ :b: bl₀ +b+ _) _] Eq in H).
    simpl_eq. iSplit; [done|]. iNext. rewrite /typed_body.
    iIntros (x ϝ ??? pre wl') "!> % %acπl LFT TIME PROPH UNIQ #Efp' Na L C T Obs".
    move: (papp_ex acπl)=> [aπl[cπl->]]. rewrite subst_plv_renew. set wl := plistc_renew _ wl'.
    iDestruct ("Big" with "[$E $Efp']") as "(Efp & InIl & InO)".
    iApply ("fn" $! _ _ _ _ _ (λ '(b -:: cl), pre (g b -:: cl)) _
      _ (plist_map_with (λ _ _, (∘)) fl aπl -++ cπl) with
      "LFT TIME PROPH UNIQ Efp Na L [C] [T] [Obs]").
    - rewrite !cctx_interp_singleton. iRevert "InO C". iClear "#".
      iIntros "#(_&_& InO &_) C". iIntros (?[??]) "Na L /=[(%&%&%& ⧖ & oty) Tf] Obs".
      iApply ("C" $! _ (_ -:: _) with "Na L [⧖ oty $Tf] Obs").
      iExists _, _. iSplitR; [done|]. iFrame "⧖". by iApply "InO".
    - iRevert "InIl T". iClear "#". iIntros "?". iStopProof. rewrite /wl.
      move: (fp x).(fp_ityl) (fp' x).(fp_ityl)=> tyl tyl'. clear.
      move: 𝔄l 𝔄l' tyl tyl' fl ew wl' aπl. fix FIX 1. case=> [|??]; case=>//=;
      dependent destruction tyl; dependent destruction tyl'; [by iIntros|].
      iIntros ([]?[][]) "/= #[(_&_& In &_) ?] [t ?]".
      iSplitL "t"; [|by iApply FIX]. iDestruct "t" as (???) "[⧖ ?]".
      iExists _, _. iSplit; [done|]. iFrame "⧖". by iApply "In".
    - iApply proph_obs_eq; [|done]=>/= ?. rewrite !papply_app !papp_sepl !papp_sepr.
      f_equal. clear. move: 𝔄l 𝔄l' fl aπl. fix FIX 1.
      case=> [|??]; case=>//= ??[??][??]. f_equal. apply FIX.
  Qed.

  Lemma fn_subtype_specialize {A B 𝔄l 𝔅} (σ: A → B) (fp: _ → _ 𝔄l 𝔅) E L :
    subtype E L (fn fp) (fn (fp ∘ σ)) id.
  Proof.
    apply subtype_plain_type. iIntros (?) "_!>_/=". iSplit; [done|].
    iSplit; [iApply lft_incl_refl|]. iIntros "* ?". iStopProof. do 13 f_equiv.
    iIntros "Big" (?). iApply "Big".
  Qed.

  Local Lemma wp_app_hasty_box {𝔄l} vl r (f: val)
    (pl: plistc _ 𝔄l) tyl vπl tid (Φ: val → iProp Σ) :
    tctx_interp tid (hzip_with (λ _ ty q, q ◁ box ty) tyl pl) vπl -∗
    (∀wl: plistc _ _,
      tctx_interp tid (hzip_with (λ _ ty (w: val), w ◁ box ty) tyl wl) vπl -∗
      WP f (of_val r :: map of_val (vl ++ wl)) {{ Φ }}) -∗
    WP f (of_val r :: map of_val vl ++ pl) {{ Φ }}.
  Proof.
    move: tyl pl vπl vl. elim 𝔄l=> [|?? IH]; dependent destruction tyl.
    { iIntros "* _ Wp". iSpecialize ("Wp" $! -[] with "[//]"). by rewrite !right_id. }
    iIntros ([p pl'][??]vl) "/= [p pl'] ToWp".
    have ->: App f (of_val r :: map of_val vl ++ p :: pl') =
      fill_item (AppRCtx f (r :: vl) pl') p by done.
    iApply wp_bind. iApply (wp_hasty with "p"). iIntros (w ? _) "⧖ p".
    have ->: fill_item (AppRCtx f (r :: vl) pl') w =
      App f (of_val r :: map of_val (vl ++ [w]) ++ pl') by rewrite map_app -assoc.
    iApply (IH with "pl'"). iIntros (?) "pl'". rewrite -assoc.
    iApply ("ToWp" $! (_ -:: _)). iFrame "pl'". iExists w, _. iFrame "⧖ p".
    by rewrite eval_path_of_val.
  Qed.

  Lemma type_call {A 𝔄l 𝔅 ℭl 𝔇l 𝔈l} x (fp: A → _ 𝔄l 𝔅) p (ql: list _)
    (ql': plistc _ _) (T: _ ℭl) (T': _ 𝔇l) tr k (Tk: _ → _ 𝔈l) pre tr' E L C :
    ql = ql' → Forall (lctx_lft_alive E L) L.*1 →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    tctx_extract_ctx E L (p ◁ fn fp +::
      hzip_with (λ _ ty q, q ◁ box ty) (fp x).(fp_ityl) ql') T T' tr →
    k ◁cont{L, Tk} pre ∈ C →
    (∀ret: val, tctx_incl E L (ret ◁ box (fp x).(fp_oty) +:: T') (Tk [#ret]) tr') →
    ⊢ typed_body E L C T (call: p ql → k) (tr (λ '(trp -:: adl),
        let '(al, dl) := psep adl in trp (λ b: 𝔅, tr' pre (b -:: dl)) al))%type.
  Proof.
    iIntros (-> Alv ToEfp ?? InTk). iApply typed_body_tctx_incl; [done|].
    iIntros (?[? adπl]). move: (papp_ex adπl)=> [aπl[dπl->]].
    iIntros "/= #LFT #TIME #PROPH #UNIQ #E Na L C [p[ql T']] Obs".
    iMod (lctx_lft_alive_tok_list with "E L") as (?) "(κL & L & ToL)"; [done|done|].
    iMod (lft_create with "LFT") as (ϝ) "[ϝ #To†ϝ]"; [done|].
    iMod (bor_create _ ϝ with "LFT κL") as "[BorκL ToκL]"; [done|].
    iDestruct (frac_bor_lft_incl with "LFT [>BorκL]") as "#?".
    { iApply (bor_fracture with "LFT"); [done|]. by rewrite Qp_mul_1_r. }
    iDestruct (ToEfp ϝ with "L [$E]") as "#Efp".
    { move: L.*1=> κl. iInduction κl as [|κ κl] "IH"; [done|]=>/=.
      iSplit. { iApply lft_incl_trans; [done|]. iApply lft_intersect_incl_l. }
      iApply "IH". iModIntro. iApply lft_incl_trans; [done|].
      iApply lft_intersect_incl_r. }
    rewrite /call_def. wp_apply (wp_hasty with "p"). iIntros (???) "_".
    iDestruct 1 as (trp->?????[=->]) "Body".
    have ->: (λ: ["_r"], Skip;; k ["_r"])%E = (λ: ["_r"], Skip;; k ["_r"])%V by unlock.
    iApply (wp_app_hasty_box [] with "ql")=>/=. iIntros (?) "ityl". wp_rec.
    iApply ("Body" with "LFT TIME PROPH UNIQ Efp Na [ϝ] [C ToκL L ToL]
      [$ityl $T'] Obs").
    { iSplitL; [|done]. iExists _. iSplit; [by rewrite/= left_id|]. by iFrame "ϝ". }
    rewrite cctx_interp_singleton. iIntros (v[bπ ?]). inv_vec v=> v.
    iIntros "Na [(%& %Eq & ϝ &_) _] [oty Tk] Obs". rewrite/= left_id in Eq.
    rewrite -Eq. wp_rec. wp_bind Skip. iSpecialize ("To†ϝ" with "ϝ").
    iApply (wp_mask_mono _ (↑lftN ∪ ↑lft_userN)); [done|].
    iApply (wp_step_fupd with "To†ϝ"); [set_solver|]. wp_seq. iIntros "†ϝ !>".
    wp_seq. iMod ("ToκL" with "†ϝ") as "> κL". iMod ("ToL" with "κL L") as "L".
    iSpecialize ("C" with "[//]"). have ->: [v: expr] = map of_val ([#v]) by done.
    iMod (InTk _ _ _ (_ -:: _) with "LFT PROPH UNIQ E L [$oty $Tk] Obs")
    as (?) "(L & Tk & Obs)". iApply ("C" with "Na L Tk Obs").
  Qed.

  Lemma type_letcall {A 𝔄l 𝔅 ℭl 𝔇l} x (fp: A → _ 𝔄l 𝔅) p (ql: list _)
    (ql': plistc _ _) (T: _ ℭl) (T': _ 𝔇l) b e tr pre E L C :
    ql = ql' → Closed (b :b: []) e → Closed [] p → Forall (Closed []) ql →
    Forall (lctx_lft_alive E L) L.*1 →
    (∀ϝ, elctx_sat (map (λ κ, ϝ ⊑ₑ κ) L.*1 ++ E) L (fp_E (fp x) ϝ)) →
    tctx_extract_ctx E L (p ◁ fn fp +::
      hzip_with (λ _ ty q, q ◁ box ty) (fp x).(fp_ityl) ql') T T' tr →
    (∀ret: val, typed_body E L C
      (ret ◁ box (fp x).(fp_oty) +:: T') (subst' b ret e) pre) -∗
    typed_body E L C T (letcall: b := p ql in e) (tr (λ '(trp -:: adl),
      let '(al, dl) := psep adl in trp (λ b: 𝔅, pre (b -:: dl)) al)).
  Proof.
    iIntros (->?? Clql ???) "e". iApply type_cont_norec.
    - (* TODO : make [solve_closed] work here. *)
      eapply is_closed_weaken; [done|]. set_solver+.
    - (* TODO : make [solve_closed] work here. *)
      rewrite /Closed /= !andb_True. split.
      + by eapply is_closed_weaken, list_subseteq_nil.
      + eapply Is_true_eq_left, forallb_forall, List.Forall_forall, Forall_impl
        =>// ??. eapply Is_true_eq_true, is_closed_weaken=>//. set_solver+.
    - iIntros (k).
      (* TODO : make [simpl_subst] work here. *)
      have ->: subst' "_k" k (call: p ql' → "_k")%E = subst "_k" k p $
        (λ: ["_r"], Skip;; k ["_r"])%E :: map (subst "_k" k) ql' by done.
      rewrite is_closed_nil_subst; [|done].
      have ->: map (subst "_k" k) ql' = ql'.
      { clear -Clql. elim Clql; [done|]=>/= ????->. by rewrite is_closed_nil_subst. }
      iApply typed_body_eq; last first. { iApply type_call=>//; [constructor|]=> v.
      have {1}->: v = vhd [#v] by done. move: [#v]=> ?. apply tctx_incl_refl. } done.
    - iIntros (k ret). inv_vec ret=>ret. rewrite /subst_v /=.
      rewrite (is_closed_subst []); [| |set_solver+]; last first.
      { apply subst'_is_closed; [|done]. apply is_closed_of_val. } iApply "e".
  Qed.

  Lemma type_fnrec_instr {A 𝔄l 𝔅} (tr: pred' 𝔅 → predl 𝔄l) (fp: A → _)
    fb (bl: plistc _ _) e E L :
    Closed (fb :b: "return" :: bl +b+ []) e →
    □ (∀x ϝ (f: val) k ℭl (T: _ ℭl) pre (wl: plistc _ 𝔄l),
      typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
        [k ◁cont{[ϝ ⊑ₗ []], λ v: vec _ 1, vhd v ◁ box (fp x).(fp_oty) +:: T} pre]
        (f ◁ fn fp +:: hzip_with (λ _ ty (v: val), v ◁ box ty) (fp x).(fp_ityl) wl h++ T)
        (subst' fb f $ subst "return" k $ subst_plv bl wl e)
        (λ '(tr' -:: acl), tr' = tr ∧ let '(al, cl) := psep acl in
          tr (λ b: 𝔅, pre (b -:: cl)) al)%type) -∗
    typed_instr_ty E L +[] (fnrec: fb bl := e) (fn fp) (λ post _, post tr).
  Proof.
    iIntros (Cl) "#Body %%% _ _ _ _ _ $$ _ Obs". iMod persist_time_rcpt_0 as "#⧖".
    have ?: Closed (fb :b: ("return" :: bl)%binder +b+ []) e by done.
    iApply (wp_value _ _ _ _ (RecV _ _ _)); [done|]. iExists -[const tr]. iFrame "Obs".
    iSplit; [|done]. iLöb as "IH". iExists _, 0. iSplit; [by rewrite/= decide_left|].
    iFrame "⧖". iExists tr=>/=. iSplit; [done|]. iExists fb, "return", bl, e, _.
    iSplit; [done|]. iIntros "!>!> * %% LFT TIME PROPH UNIQ Efp Na L C T ?".
    iApply ("Body" $! _ _ (RecV _ _ _) _ _ _ _ _ _ (_ -:: _) with
      "LFT TIME PROPH UNIQ Efp Na L C [$T $IH]").
    by iApply proph_obs_impl; [|done]=>/= ??.
  Qed.

  Lemma type_fn_instr {A 𝔄l 𝔅} (tr: pred' 𝔅 → predl 𝔄l) (fp: A → _)
    (bl: plistc _ _) e E L :
    Closed ("return" :: bl +b+ []) e →
    □ (∀x ϝ k ℭl (T: _ ℭl) pre (wl: plistc _ 𝔄l),
      typed_body (fp_E (fp x) ϝ) [ϝ ⊑ₗ []]
        [k ◁cont{[ϝ ⊑ₗ []], λ v: vec _ 1, vhd v ◁ box (fp x).(fp_oty) +:: T} pre]
        (hzip_with (λ _ ty (v: val), v ◁ box ty) (fp x).(fp_ityl) wl h++ T)
        (subst "return" k $ subst_plv bl wl e)
        (λ acl, let '(al, cl) := psep acl in tr (λ b: 𝔅, pre (b -:: cl)) al)%type) -∗
    typed_instr_ty E L +[] (fn: bl := e) (fn fp) (λ post _, post tr).
  Proof.
    iIntros (?) "#?". iApply type_fnrec_instr. iIntros "!> *".
    iApply typed_body_impl; last first. { iApply typed_body_tctx_incl; [|done].
    apply tctx_incl_leak_head. } by move=>/= [??][_ ?].
  Qed.

End typing.

Global Hint Resolve fn_subtype : lrust_typing.
