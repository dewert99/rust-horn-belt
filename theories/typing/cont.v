From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Class IntoVecVal {n} (el: list expr) (vl: vec val n) :=
  into_vec_val: el = map of_val vl.

Global Instance into_vec_val_nil: IntoVecVal [] [#].
Proof. done. Qed.

Global Instance into_vec_val_cons {n} e v el (vl: _ n) :
  IntoVal e v → IntoVecVal el vl → IntoVecVal (e :: el) (v ::: vl).
Proof. by move=>/= <-->. Qed.

Section typing.
  Context `{!typeG Σ}.

  (** Jumping to and defining a continuation. *)
  Lemma type_jump {𝔄l 𝔅l n} E (T: _ 𝔄l) C k L (T': _ → _ 𝔅l) pre el (vl: _ n) tr :
    IntoVecVal el vl → k ◁cont{L, T'} pre ∈ C → tctx_incl E L T (T' vl) tr →
    ⊢ typed_body E L C T (k el) (tr pre).
  Proof.
    move=> -> ?. iIntros (TT' ??) "LFT _ PROPH UNIQ E Na L C T Obs".
    iMod (TT' with "LFT PROPH UNIQ E L T Obs") as (?) "(L & T & Obs)".
    iApply ("C" with "[%//] Na L T Obs").
  Qed.

  Lemma type_cont {𝔄l 𝔅l} E L C (T: _ 𝔄l) kb bl ec e L' (T': _ → _ 𝔅l) prek pre :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k, typed_body E L (k ◁cont{L', T'} prek :: C) T (subst' kb k e) pre) -∗
    □(∀k (vl: vec val (length bl)), typed_body E L' (k ◁cont{L', T'} prek :: C)
      (T' vl) (subst' kb k $ subst_v bl vl ec) prek) -∗
    typed_body E L C T (letcont: kb bl := ec in e) pre.
  Proof.
    iIntros (??) "e #ec %% #LFT #TIME #PROPH #UNIQ #E Na L C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME PROPH UNIQ E Na L [C] T Obs").
    iLöb as "IH". iIntros (?). rewrite elem_of_cons.
    iIntros ([->|?]); [|by iApply "C"]. iIntros (??) "Na L' T' Obs".
    wp_rec. iApply ("ec" with "LFT TIME PROPH UNIQ E Na L' [C] T' Obs").
    by iApply "IH".
  Qed.

  Lemma type_cont_norec {𝔄l 𝔅l} E L C (T: _ 𝔄l) kb bl ec e L' (T': _ → _ 𝔅l) prek pre :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k, typed_body E L (k ◁cont{L', T'} prek :: C) T (subst' kb k e) pre) -∗
    (∀k (vl: vec val (length bl)),
      typed_body E L' C (T' vl) (subst' kb k $ subst_v bl vl ec) prek) -∗
    typed_body E L C T (letcont: kb bl := ec in e) pre.
  Proof.
    iIntros (??) "e ec %% #LFT #TIME #PROPH #UNIQ #E Na L C T Obs".
    have ->: (rec: kb bl := ec)%E = of_val (rec: _ _ := _) by unlock.
    wp_let. iApply ("e" with "LFT TIME PROPH UNIQ E Na L [ec C] T Obs").
    iIntros (?). rewrite elem_of_cons. iIntros ([->|?]); [|by iApply "C"].
    iIntros (??) "Na L' T' Obs". wp_rec.
    iApply ("ec" with "LFT TIME PROPH UNIQ E Na L' C T' Obs").
  Qed.

End typing.
