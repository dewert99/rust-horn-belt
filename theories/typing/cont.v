From iris.proofmode Require Import tactics.
From lrust.typing Require Export type.
From lrust.typing Require Import programs.
Set Default Proof Using "Type".

Section typing.
  Context `{!typeG Σ}.

  (** Jumping to and defining a continuation. *)
  Lemma type_jump {𝔄l 𝔅l} E (T: _ 𝔄l) C k L n (T': _ → _ 𝔅l) pre vl (vl': vec _ n) tr :
    k ◁cont{L, T'} pre ∈ C →
    vl = map of_val vl' → tctx_incl E L T (T' vl') tr →
    ⊢ typed_body E L C T (k vl) (tr pre).
  Proof.
    iIntros (InC -> TT' ??) "LFT _ PROPH UNIQ E Na L C T Obs".
    iMod (TT' with "LFT PROPH UNIQ E L T Obs") as (?) "(L & T & Obs)".
    rewrite cctx_interp_forall. iSpecialize ("C" with "[%//]").
    iApply ("C" with "Na L T Obs").
  Qed.

  Lemma type_cont {𝔄l 𝔅l} E L C (T: tctx 𝔄l) kb bl ec e L' (T': _ → _ 𝔅l) prec pre :
    Closed (kb :b: bl +b+ []) ec → Closed (kb :b: []) e →
    (∀k, typed_body E L (k ◁cont{L', T'} prec :: C) T (subst' kb k e) pre) -∗
    □(∀k (vl: vec val (length bl)), typed_body E L' (k ◁cont{L', T'} prec :: C)
        (T' vl) (subst_v (kb :: bl) (k ::: vl) ec) prec) -∗
    typed_body E L C T (letcont: kb bl := ec in e) pre.
  Proof.
    iIntros (??) "e #ec". iIntros (??) "#LFT #TIME #PROPH #UNIQ #E Na L #C T Obs".
    rewrite (_ : (rec: kb bl := ec)%E = of_val (rec: kb bl := ec)%V); [|by unlock].
    wp_let. iApply ("e" with "LFT TIME PROPH UNIQ E Na L [$C] T Obs").
    iLöb as "IH". iIntros "!>" (??) "Na L' T' Obs". wp_rec.
    by iApply ("ec" with "LFT TIME PROPH UNIQ E Na L' [$C] T' Obs").
  Qed.

End typing.
