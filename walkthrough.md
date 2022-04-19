# Walkthrough

Here we present a walkthrough of RustHornBelt's Coq mechanization.

RustHornBelt's proof is built on many artifacts: Iris Proof Mode & the Iris
separation logic, RustBelt's lifetime logic, the λ core calculus and its
low-level program logic in Iris, RustHornBelt's prophecy framework,
dependent-type heterogeneous lists, and RustHornBelt's semantic type-spec system.
There are many tricky things going on behind the scene.
Still, what we really need to understand for verification in RustHornBelt
is fairly limited.

Below we walk through some real examples of verification in our Coq mechanization
of RustHornBelt to provide readers with a good intuition of how to reuse and
extend our Coq artifacts.

## Verifying integer addition `+`

Let's start with a small example: integer addition `+` (see `typing/int.v`).

### Semantic lemma for the type-spec rule

It's treated as an *instruction* (instead of a function) in RustHornBelt's
type-spec system.
We have a type-spec rule for this instruction. Since we are in a *semantic*
framework, it can be formulated as a separate *lemma* in Coq, as follows:
```
Lemma type_plus_instr E L p1 p2 :
  typed_instr_ty E L +[p1 ◁ int; p2 ◁ int] (p1 + p2) int
    (λ post '-[z; z'], post (z + z')).
```

The semantic Coq predicate
```
typed_instr_ty E L +[p ◁ ty; ...] e ty' tr : Prop
```
means that, by taking objects `p ◁ ty` (`p: path` typed `ty`) etc.
as input, you can execute the expression `e: expr` and get an object typed `ty'`,
under the *spec (predicate transformer)* `tr`.
We have two lifetime contexts, the external one `E` and the local one `L`,
but usually you can ignore them.

For integer addition, you take two integer operands `p1 ◁ int`
and `p2 ◁ int`, perform `p1 + p2`, and output `int`.
Here, `int` is a *semantic Rust type* for integer, typed `int: type Zₛ`.
Also, `+` in `p1 + p2` is not usual Coq addition, but the notation for
addition in the λRust core calculus.

Here, `type 𝔄: Type` is the Coq data type for a *semantic Rust type*
(`typing/type.v`).
It is parametrized over `𝔄: syn_type`, which is the *sort* of
a representation value for the Rust type.
Here, `syn_type` (`prophecy/syn_type.v`) is an inductive Coq data type for
a *syntax tree* representing a Coq type.
There is a function `of_syn_type: syn_type -> Type` for interpreting
a `syn_type`, which is registered as a coercion.
```
Coercion of_syn_type: syn_type >-> Sortclass.
```

For the integer, we use `Zₛ: syn_type` (where the subscript `ₛ` indicates that
it is syntactic), which is interpreted into Coq's integer type `Z: Type`.

For integer addition, the input type context (list of typed input objects) is:
```
+[p1 ◁ int; p2 ◁ int] : tctx [Zₛ; Zₛ]
```
Here, `tctx 𝔄l` (`𝔄l: list syn_type`), the type for a type context, is actually
a shorthand for `hlist tctx_elt 𝔄l`.
Each object `p ◁ ty` (`ty: type 𝔄`) has the type `tctx_elt 𝔄`.
The Coq type `hlist F [X; Y; ...]` (`util/fancy_lists.v`) is for a
*heterogeneous list* that consists of items of Coq type `F X`, `F Y`, and so on.
You can use the notation `+[x; y; ...]` for constructing a heterogeneous list.

Finally, the spec (predicate transformer) for integer addition is:
```
λ (post: Z → Prop) ('-[z; z']: *[Z; Z]), post (z + z') : Prop
```
It takes the *postcondition* `post: Z → Prop` and the input objects' integer values
`z, z': Z`, and returns the *precondition* `post (z + z') : Prop`.
Intuitively, it is like in the *continuation-passing style*, with the postcondition
`post` working as a kind of *continuation*.
The Coq type `*[A; B; ...]` is for what we call a *passive heterogeneous list*,
which is of the form `-[a; b; ...]`, where `a: A`, `b: B`, and so on.
(Technically, the passive heterogeneous list type is a type *function* whereas the
heterogeneous list type `hlist` is a GADT, but let's first get used to real usage.)

### Proving the lemma

Proof of the lemma can go as follows, for example.
```
Proof.
  intros tid postπ (zπ & zπ' &[]).
  iIntros "_ _ _ _ _ $ $ (P1 & P2 &_) Obs".
  wp_apply (wp_hasty with "P1").
  iIntros (v1 d1 _) "⧖". iIntros ([z [-> [=->]]]).
  wp_apply (wp_hasty with "P2").
  iIntros (v2 d2 _) "_". iIntros ([z' [-> [=->]]]).
  wp_op. iExists -[const (z + z')]. iFrame "Obs".
  iSplit; [|done]. rewrite tctx_hasty_val'; [|done].
  iExists d1. iFrame "⧖". by iExists (z + z').
Qed.
```
Let's go step by step.

First, you perform `intros tid postπ (zπ & zπ' & [])`, because the goal is universally
quantified over the *thread id* `tid: thread_id` (you can usually ignore it),
the *clairvoyant postcondition* `postπ: proph (*[Z] → Prop)`, and the list of
*clairvoyant input values* `zπl: *[proph Z; proph Z]`, which gets decomposed
into `zπ, zπ': proph Z`.
The type `proph A: Type` is actually a shorthand for the *clairvoyant* reader
monad `proph_asn → A`.
In Coq, we indicate clairvoyant values by the suffix `π` (instead of the hat
used in the paper).

Now you have the following goal (it is modified a bit for better readability;
the same applies hereafter).
```
lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
  elctx_interp E -∗ na_own tid ⊤ -∗ llctx_interp L 1 -∗
  tctx_interp tid +[p1 ◁ int; p2 ◁ int] -[zπ; zπ'] -∗
  ⟨π, postπ π -[(zπ π + zπ' π)]⟩ -∗
  WP p1 + p2 {{ v, ∃ zπl': *[proph Z],
    na_own tid ⊤ ∗ llctx_interp L 1
    ∗ tctx_interp tid +[v ◁ int] zπl'
    ∗ ⟨π, postπ π (zπl' -$ π)⟩
  }}
```
This is an *Iris proposition*, of the type `iProp Σ: Type` (`Σ` specifies the
form of resources, but you can ignore it).
As expected, `∗` is the *separating conjunction*, `-∗` is the *magic wand*
(right-associative, just like implication), and `∃ x: A, P` is the existential
quantifier (notation overloaded for Iris and pure Coq).
The predicate `WP e {{ v, P }}` is Iris's weakest precondition for the expression
`e` and the postcondition `(λ v, P) : val → iProp Σ`.

You are given some *contexts* `lft_ctx`, `time_ctx`, `proph_ctx`, `uniq_ctx`,
i.e., global Iris invariants, but they can be ignored now.
You are also given `elctx_interp E` (persistent resource for `E`), `na_own tid ⊤`
(token for the thread `tid`), and `llctx_interp L 1` (resource for `L`),
but they can be usually ignored.

More importantly, you get the resource for the *input objects*
`tctx_interp tid +[p1 ◁ int; p2 ◁ int] -[zπ; zπ']`
and the prophecy observation for the *precondition* `⟨π, postπ π -[(zπ π + zπ' π)]⟩`.
Because the predicate `tctx_interp` is defined as `foldr` over the list of input
objects, the resource for the input objects is unfolded into the following.
```
tctx_elt_interp tid (p1 ◁ int) zπ ∗ tctx_elt_interp tid (p2 ◁ int) zπ' ∗ True
```

In the postcondition, we can specify the list of *clairvoyant output values*
`zπl': *[proph Z]`, and return the resource for the *output objects*
`tctx_interp tid +[v ◁ int] zπl'` and the *postcondition prophecy observation*
`⟨π, postπ π (zπl' -$ π)⟩` (`fl -$ x` feeds the argument `x` to each element of
the list `fl`), along with the minor resources `na_own tid ⊤` and `llctx_interp L 1`.

Let's do `iIntros "_ _ _ _ _ $ $ (P1 & P2 &_) Obs"`, a tactic of *Iris Proof Mode*.
You ignore the contexts and `elctx_interp E`.
You want to directly pass the resources `na_own tid ⊤` and `llctx_interp L 1`
to `WP`'s postcondition.
In that case, you can *frame* them out using the directive `$`.
You name the resources for the input objects `p1` and `p2` as `P1` and `P2`
respectively, and name the precondition prophecy observation as `Obs`.

Now the goal is as follows.
```
"P1" : tctx_elt_interp tid (p1 ◁ int) zπ
"P2" : tctx_elt_interp tid (p2 ◁ int) zπ'
"Obs" : ⟨π, postπ π -[(zπ π + zπ' π)]⟩
--------------------------------------∗
WP p1 + p2 {{ v, ∃ zπl': *[proph Z],
  tctx_interp tid +[v ◁ int] zπl'
  ∗ ⟨π, postπ π (zπl' -$ π)⟩
}}
```
Here, `P1`, `P2` and `Obs` are *Iris-level hypotheses*.

Technically, `p1` and `p2` are paths, which can contain some location-offset
operations, so we should evaluate them.
By the tactic `wp_apply (wp_hasty with "P1")`, you can execute `p1`
using the lemma `wp_hasty` and the resource `P1`.
Then we have the following goal.
```
"P2" : tctx_elt_interp tid (p2 ◁ int) zπ'
"Obs" : ⟨π, postπ π -[(zπ π + zπ' π)]⟩
--------------------------------------∗
∀ (v1: val) (d1: nat),
  ⌜Some v1 = eval_path p1⌝ -∗ ⧖d1 -∗
  int.(ty_own) zπ d1 tid [v1] -∗
  WP v1 + p2 {{ v, ∃ zπl': *[proph Z],
    tctx_interp tid +[v ◁ int] zπl'
    ∗ ⟨π, postπ π (zπl' -$ π)⟩
  }}
```
The path `p1` gets evaluated into a low-level value `v1: val`, and `p1 + p2`
has changed into `v1 + p2` (usually `Some v1 = eval_path p1` can be ignored).
The integer object has the pointer-nesting depth `d1: nat`, and so we get a
time receipt `⧖d1` for it.
Therefore we do `iIntros (v1 d1 _) "⧖"`.

We also have the ownership predicate `int.(ty_own) zπ d1 tid [v1]`, which is
unfolded into the following lifted pure proposition (after slight modification):
```
⌜∃ z: Z, zπ = const z ∧ [v] = [#z]⌝
```
It says that the low-level value `v: val` is the literal `#z` for some Coq
integer `z: Z` and the clairvoyant value `zπ` is actually constantly `z`.
By performing `iIntros ([z [-> [=->]]])`, we can destruct it to get `z: Z`,
rewrite `zπ` into `const z`, and rewrite `v` into `#z`
(the `[=...]` pattern destructs `[v] = [#z]` into `v = #z`).

Now the goal is as follows.
```
"P2" : tctx_elt_interp tid (p2 ◁ int) zπ'
"Obs" : ⟨π, postπ π -[(z + zπ' π)]⟩
"⧖" : ⧖d1
--------------------------------------∗
WP #z + p2 {{ v, ∃ zπl': *[proph Z],
  tctx_interp tid +[v ◁ int] zπl'
  ∗ ⟨π, postπ π (zπl' -$ π)⟩
}}
```

You perform similar tactics `wp_apply (wp_hasty with "P2")`, `iIntros (v2 d2 _) "_"`
and `iIntros ([z' [-> [=->]]])` for `p2` (now you ignore the time receipt) to get:
```
"Obs" : ⟨π, postπ π -[(z + z')]⟩
"⧖" : ⧖d1
--------------------------------------∗
WP #z + #z' {{ v, ∃ zπl': *[proph Z],
  tctx_interp tid +[v ◁ int] zπl'
  ∗ ⟨π, postπ π (zπl' -$ π)⟩
}}
```
Finally, you can perform the integer addition by `wp_op`.
As expected, the operation returns `#(z + z')`, the literal for `z + z'`.

Now the goal is as follows, out of `WP`.
```
"Obs" : ⟨π, postπ π -[(z + z')]⟩
"⧖" : ⧖d1
--------------------------------------∗
∃ zπl': *[proph Z],
  tctx_interp tid +[#(z + z') ◁ int] zπl'
  ∗ ⟨π, postπ π (zπl' -$ π)⟩
```

By `iExists -[const (z + z')]`, you set `zπl'` to `-[const (z + z')]`,
which updates the goal into the following (unfolding `tctx_interp`):
```
"Obs" : ⟨π, postπ π -[(z + z')]⟩
"⧖" : ⧖d1
--------------------------------------∗
(tctx_elt_interp tid (#(z + z') ◁ int) (const (z + z')) ∗ True)
∗ ⟨π, postπ π -[(z + z')]⟩
```
Now the postcondition prophecy observation is exactly the same as `Obs`,
the precondition prophecy observation.
So you can frame it out by `iFrame "Obs"`.
You can remove `∗ True` by `iSplit; [|done]`.

Now the goal is as follows.
```
"⧖" : ⧖d1
--------------------------------------∗
tctx_elt_interp tid (#(z + z') ◁ int) (const (z + z'))
```
You can change the goal into the following by the tactic
`rewrite tctx_hasty_val'; [|done]`:
```
"⧖" : ⧖d1
--------------------------------------∗
∃ d: nat, ⧖d
  ∗ ty_own int (const (z + z')) d tid [#(z + z')]
```
Let's set `d` to `d1` by `iExists d1`.
Then you can frame out `⧖d1` by `iFrame "⧖"`.
Now the goal is just `ty_own int ...`, which is unfolded into an existential
quantification over the Coq integer as we observed before.
So you set the integer to `z + z'` and finish the remaining goal by
`by iExists (z + z')`.

## Modeling `Vec<T>`

Now let's verify the `Vec<T>` API, whose methods encapsulate *unsafe* implementation!

We first model the vector type itself (`typing/lib/vec`).
We use the following model:
```
Program Definition vec_ty {𝔄} (ty: type 𝔄) : type (listₛ 𝔄) := {|
  ty_size := 3;  ty_lfts := ty.(ty_lfts);  ty_E := ty.(ty_E);
  ty_own alπ d tid vl :=
    [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜vl = [#l; #len; #ex] ∧ alπ = lapply aπl⌝ ∗
      ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
      (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
      freeable_sz' ((len + ex) * ty.(ty_size)) l;
  ty_shr alπ d κ tid l' :=
    [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
      ⌜alπ = lapply aπl⌝ ∗
      &frac{κ} (λ q, l' ↦∗{q} [#l; #len; #ex]) ∗
      ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i);
|}%I.
```
The vector type `vec_ty ty` is parametrized over the element type `ty: type 𝔄`.
The representation sort is set to `listₛ 𝔄`, where `listₛ` is a data constructor
in `syn_type`, corresponding to `list: Type → Type`.

The field `ty_size` is the number of memory cells it takes (at the topmost level).

The fields `ty_lfts` and `ty_E` are newly introduced in RustHornBelt (not
existent in RustBelt), but you can usually ignore them.

The most important are the ownership predicate `ty_own` and the sharing predicate `ty_shr`.

### Ownership predicate `(vec_ty ty).(ty_own)`

Let's read the ownership predicate of `vec_ty ty`.
```
ty_own alπ d tid vl :=
  [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
    ⌜vl = [#l; #len; #ex] ∧ alπ = lapply aπl⌝ ∗
    ▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid) ∗
    (l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size)) ∗
    freeable_sz' ((len + ex) * ty.(ty_size)) l
```

The exotic notation `[S(d') := d] P` is shorthand of
`match d with S d' => P | _ => False`.
The vector object's (pointer-nesting) depth `d: nat` is the successor of
the depth `d': nat` of the element objects.

The low-level values `vl` of the vector consists of the literals for
the memory block's head location `l: loc`, the vector's length `len: nat`,
and the extra capacity `ex`.

Letting `aπl = [# aπ0; aπ1; ...]` the list of the elements' values (whose
length is `len`), the vector object's representation value `alπ π : list 𝔄`
equals `lapply aπl π = [aπ0 π; aπ1 π; ...]`.

The main resources consist of
1. `▷ ([∗ list] i ↦ aπ ∈ aπl, (l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid)` ---
  the iterated separating conjunction of the i-th element object with the
  points-to token `(l +ₗ[ty] i) ↦∗: ty.(ty_own) aπ d' tid)`,
  under the later modality `▷`;
2. `(l +ₗ[ty] len) ↦∗len (ex * ty.(ty_size))` --- the points-to token over
  the extra region; and
3. `freeable_sz' ((len + ex) * ty.(ty_size)) l` --- the right to free the
  memory block.

The notation `l ↦∗: Φ` stands for `∃vl, l ↦∗ vl ∗ Φ vl` and the notation
`l ↦∗len n` stands for `∃vl, ⌜length vl = n⌝ ∗ l ↦∗ vl`.
The later modality `▷` added to the element objects is for *contractiveness*
of `vec_ty ty` over `ty` (a technical key for supporting recursive types with
self reference under `vec_ty`).

Usually, the ownership predicate appears in the form
`l' ↦∗ (vec_ty ty).(ty_own) alπ d tid`, accompanied with the points-to token.
To smoothly handle this form, we have a special lemma `split_mt_vec`,
which allows us to rewrite `l' ↦∗ (vec_ty ty).(ty_own) alπ d tid` into the form:
```
[S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
  ⌜alπ = lapply aπl⌝ ∗ l' ↦∗ [#l; #len; #ex] ∗
  ...(the main resources)...
```
This makes work a bit easier.

### Sharing predicate `(vec_ty ty).(ty_shr)`

Let's read the sharing predicate of `vec_ty ty`.
```
ty_shr alπ d κ tid l' :=
  [S(d') := d] ∃(l: loc) (len ex: nat) (aπl: vec (proph 𝔄) len),
    ⌜alπ = lapply aπl⌝ ∗
    &frac{κ} (λ q, l' ↦∗{q} [#l; #len; #ex]) ∗
    ▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i);
```
Basically, `(vec_ty ty).(ty_shr) alπ d κ tid l'` is quite similar to
`l' ↦∗ (vec_ty ty).(ty_own) alπ d κ tid`, but we have:
1. `&frac{κ} (λ q, l' ↦∗{q} [#l; #len; #ex])` --- a fractional borrow
  over the topmost memory cells; and
2. `▷ [∗ list] i ↦ aπ ∈ aπl, ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i)` ---
  the iterated separating conjunction of the sharing predicate of the i-th
  element object  `ty.(ty_shr) aπ d' κ tid (l +ₗ[ty] i)`,
  under the later modality `▷`.

### Pre-installed Lemmas

We have not yet finished defining `vec_ty`.
Like in RustBelt, RustHornBelt's semantic type `type 𝔄` is equipped with several
pre-installed lemmas about `ty_own` and `ty_shr`, the ownership and sharing
predicates: `ty_size_eq`, `ty_own/shr_depth_mono`, `ty_shr_lft_mono`,
`ty_share`, and `ty_own/shr_proph`.
This is why we used `Program Definition` instead of just `Definition`.
We can start proving the next remaining lemma by:
```
Next Obligation.
```
Typically, the proof is mostly boilerplate code.

## Verifying `Vec::new`

Now let's verify a simple method of the `Vec` API, `Vec::new`
(`typing/lib/vec/vec_basic.v`).

### Implementation in λRust

It is implemented as follows.
```
Definition vec_new: val :=
  fn: [] :=
    let: "r" := new [ #3] in
    "r" <- new [ #0];; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;
    return: ["r"].
```
You can use a *function* literal `fn: ["x"; "y"; ...] := e`, where `"x"`,
`"y"`, ... are the arguments and `e: expr` is the executed body.

The function first allocates a new memory block of length 3 (`new [#3]`)
and names its head location `"r"`.
It allocates a memory block of length `0` (`new [#0]`) and writes its
head location at "r".
Then it writes `#0` to `"r" +ₗ #1` and `"r" +ₗ #2` (`+ₗ` is the location
offset operation), to set the length and extra capacity to 0.
Finally it returns `"r"`.

In this way, the function is expected to return a *box pointer* to
a vector of empty elements, `box (vec_ty ty)` (`Box<Vec<T>>` in Rust).
Note that the ownership predicate of the box pointer
`(box ty').(ty_own) pπ d tid [l']` is the following:
```
[S(d') := d]
  ▷ l ↦∗: ty'.(ty_own) pπ d' tid ∗ freeable_sz ty'.(ty_size) ty'.(ty_size) l';
```
Here, `freeable_sz n n l'` is the same as `freeable_sz' l'`
(as stated by the lemma `freeable_sz_full` in `theories/typing/own.v`).

### The type-spec rule

Now let's prove the type-spec rule for the function `vec_new`.
```
Lemma vec_new_type {𝔄} (ty: type 𝔄) :
  typed_val vec_new (fn(∅) → vec_ty ty) (λ post _, post []).
```
This type-spec rule allows you to use `vec_new` as a *function object* of
type `fn(∅) → vec_ty ty`, which takes no input (you can ignore the `∅` part)
and outputs a *box pointer* to a vector `vec_ty ty`.
Its representation value is a *predicate transformer* spec
`(λ post _, post []) : (list 𝔄 → Prop) → *[] → Prop`,
which just returns the empty list `[]: list 𝔄`.

### Proving the type-spec rule

Proof of this lemma can go as follows.
```
Proof.
  eapply type_fn; [apply _|]. intros _ ϝ k []. simpl_subst.
  iIntros (tid [] postπ) "_ #TIME _ _ _ Na L C _ Obs".
  (* new [ #3] *)
  wp_apply wp_new; [done..|]. iIntros (r).
  rewrite !heap_mapsto_vec_cons !shift_loc_assoc.
  iIntros "[† (↦₀ & ↦₁ & ↦₂ &_)]". wp_let.
  (* "r" <- new [ #0];; *)
  iMod persistent_time_receipt_0 as "⧖". wp_bind (new _).
  iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
  iApply wp_new; [done..|]. iIntros "!>" (l) "[†' _] ⧖".
  wp_bind (_ <- _)%E.
  iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
  wp_write. iIntros "⧖". wp_seq.
  (* "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;; *)
  wp_op. wp_write. wp_op. wp_write. do 2 wp_seq.
  (* continuation *)
  rewrite cctx_interp_singleton.
  iApply ("C" $! [# #r] -[const []] with "Na L [-Obs] Obs").
  iSplit; [|done]. iExists #r, 2. do 2 (iSplit; [done|]).
  rewrite/= freeable_sz_full. iFrame "†". iNext.
  (* constructing the vector *)
  iExists [ #l; #0; #0].
  rewrite !heap_mapsto_vec_cons !shift_loc_assoc heap_mapsto_vec_nil.
  iFrame "↦₀ ↦₁ ↦₂". iExists l, 0, 0, [#].
  iSplit; [done|]. iFrame "†'". iSplit; [by iNext|].
  iExists []. by rewrite heap_mapsto_vec_nil.
Qed.
```

The first trick is `eapply type_fn; [apply _|]`.
This makes the goal into the following form.
```
∀(_: ()) (ϝ: lft) (k: val) (_: *[]), ⊢ typed_body ...
```
We have some Coq-level inputs here.
* The first input `_: ()` is the parameter of the function, which is just
the unit for this function.
* The second input `ϝ: lft` is the *lifetime of the function* (`ϝ` is digamma).
* The third input `k: val` is the *continuation*.
  In λRust, a function is in the continuation-passing style, and the `return: [e]`
  directive actually calls the continuation function with the return value `e`.
  The continuation function is internally bound to a special variable `"return"`.
  Here we get the actual function value `k: val` of the continuation.
* The fourth input `_: *[]` is the list of *clairvoyant input values*.
  In this case, it is empty.

We perform `intros _ ϝ k []` to introduce these inputs.
We perform `simpl_subst` to complete substitution of `"return"` into `k`.

Now the goal is as follows:
```
⊢ typed_body
    (fp_E {|fp_E_ex := ∅; fp_ityl := +[]; fp_oty := vec_ty ty|} ϝ)
    [ϝ ⊑ₗ []]
    [k ◁cont{[ϝ ⊑ₗ []], λ v: vec val 1, +[vhd v ◁ box (vec_ty ty)]} tr_ret]
    +[]
    (let: "r" := new [#3] in
      "r" <- new [#0];; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;
      jump: k ["r"])
    (λ (post: list 𝔄 → Prop) (_: *[]), post [])
```
The sequent `⊢ P : Prop` embeds an Iris proposition `P: iProp Σ` into
a pure proposition.
The *Iris* predicate `typed_body` (`typing/programs.v`) takes several arguments.
1. The first argument `fp_E ... ϝ` is the external lifetime context. You can
  usually ignore it.
2. The second argument `[ϝ ⊑ₗ []]` is the local lifetime
3. The third argument
  `[k ◁cont{[ϝ ⊑ₗ []], λ v: vec val 1, +[vhd v ◁ box (vec_ty ty)]} tr_ret]`
  is the continuation context.
  The argument `v` is the continuation's argument list, which consists of
  only one value `vhd v`.
  We return a box pointer to a vector `box (vec_ty ty)`.
  The spec of the output is `tr_ret`, which is shorthand for
  `λ post '-[a], post a`.
4. The fourth argument `+[]` is the input type context.
  For this function, it is empty.
5. The fifth argument `let: "r" := ... in ...` is the executed expression.
  Note that `return: ["r"]` has been updated into `jump: k ["r"]`.
6. The sixth argument `λ (post: list 𝔄 → Prop) (_: *[]), post [])`
  is the predicate transformer spec.

The `typed_body` goal unfolds into the following:
```
⊢ ∀ tid (pπl: *[]) (postπ : proph (list 𝔄 → Prop)),
  lft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
  elctx_interp (fp_E ... ϝ) -∗ na_own tid ⊤ -∗ llctx_interp [ϝ ⊑ₗ []] 1 -∗
  cctx_interp tid postπ [k ◁cont{...} tr_ret] -∗
  tctx_interp tid +[] pπl -∗ ⟨π, postπ π []⟩ -∗
  WP let: "r" := new [#3] in
    "r" <- new [#0];; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;
    jump: k ["r"] {{ _, True }}
```
By `iIntros (tid [] postπ) "_ #TIME _ _ _ Na L C _ Obs"`,
the goal turns into the following.
```
"TIME" : time_ctx
--------------------------------------□
"Na" : na_own tid ⊤
"L" : llctx_interp [ϝ ⊑ₗ []] 1
"C" : cctx_interp tid postπ [k ◁cont{...} tr_ret]
"Obs" : ⟨π, postπ π []⟩
--------------------------------------∗
WP let: "r" := new [#3] in
  "r" <- new [#0];; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;
  jump: k ["r"] {{ _, True }}
```

#### **Execute `new [#3]`**

We first execute `new [#3]` by `wp_apply wp_new; [done..|]`.
This updates the goal into the following.
```
...
--------------------------------------∗
∀ r: loc,
  freeable_sz' 3 r ∗ r ↦∗ [#☠; #☠; #☠] -∗
  WP let: "r" := #r in
    "r" <- new [#0];; "r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;
    jump: k ["r"] {{ _, True }}
```
Here, `r` is the return value of `new [#3]`.
You get the right to free the memory block `freeable_sz' 3 r` and the
points-to token `r ↦∗ [#☠; #☠; #☠]`.
You first do `iIntros (r)`.
By `rewrite !heap_mapsto_vec_cons !shift_loc_assoc`,
you can destruct `r ↦∗ [#☠; #☠; #☠]` into three points-to tokens to
each location of the memory block.
By `iIntros "[† (↦₀ & ↦₁ & ↦₂ &_)]"`, you can name the resources.
By `wp_let`, you can resolve `let: "r" := #r in`, replacing `"r"` with `#r`.

#### **Execute `"r" <- new [ #0];;`**

Now the goal is as follows.
```
...
"Obs" : ⟨π, postπ π []⟩
"†" : freeable_sz' 3 r
"↦₀" : r ↦ #☠
"↦₁" : (r +ₗ 1) ↦ #☠
"↦₂" : (r +ₗ (1 + 1)) ↦ #☠
--------------------------------------∗
WP #r <- new [#0];; #r +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;
  jump: k ["r"] {{ _, True }}
```
Now you want to construct a time receipt `⧖2` for the returned object.
You can get `⧖0` for free by `iMod persistent_time_receipt_0 as "⧖0"`;
this adds the hypothesis:
```
...
"⧖0" : ⧖0
--------------------------------------∗
...
```
You can grow up a time receipt by 1 for each program step.
Let's use the two program steps of `#r <- new [#0]`.
You first do `wp_bind (new _)`, which updates the goal into:
```
...
"⧖0" : ⧖0
--------------------------------------∗
WP new [#0] {{ v,
  WP #r <- v;; #r +ₗ #1 <- #0;; #r +ₗ #2 <- #0;;
    jump: k [#r] {{ _, True }}
}}
```
We perform `iApply (wp_persistent_time_receipt with "TIME ⧖0"); [done|]`
to grow `⧖0` into `⧖1`.
Now we have the goal:
```
...
--------------------------------------∗
WP new [#0] @ ⊤ ∖ ↑timeN {{ v,
  ⧖1 -∗ WP #r <- v;; #r +ₗ #1 <- #0;; #r +ₗ #2 <- #0;;
          jump: k [#r] {{ _, True }}
}}
```
Here, `@ ⊤ ∖ ↑timeN` is the mask (this prevents us from using the `timeN`
invariant multiple times at the program step; you can usually ignore it).
By `iApply wp_new; [done..|]`, we can execute `new [#0]`,
which turns the goal into:
```
...
--------------------------------------∗
▷ ∀ l: loc, freeable_sz' 0 l ∗ l ↦∗ [] -∗ ⧖1 -∗
  WP #r <- l;; #r +ₗ #1 <- #0;; #r +ₗ #2 <- #0;;
    jump: k [#r] {{ _, True }}
```
By `iIntros "!>" (l) "[†' _] ⧖1"`, the goal turns into:
```
...
"†'" : freeable_sz' 0 l
"⧖1" : ⧖1
--------------------------------------∗
WP #r <- l;; #r +ₗ #1 <- #0;; #r +ₗ #2 <- #0;;
  jump: k [#r] {{ _, True }}
```
Similarly, you perform `wp_bind (_ <- _)%E` and
`iApply (wp_persistent_time_receipt with "TIME ⧖1"); [done|]`.
```
...
"↦₀" : r ↦ #☠
...
--------------------------------------∗
WP #r <- #l @ ⊤ ∖ ↑timeN {{ v,
  ⧖2 -∗ WP #r +ₗ #1 <- #0;; #r +ₗ #2 <- #0;;
          jump: k [#r] {{ _, True }}
}}
```
By `wp_write`, we perform `#r <- #l`, which writes the value `#l` to the
location `r`, updating the goal into the following.
```
...
"↦₀" : r ↦ #l
...
--------------------------------------∗
⧖2 -∗
WP #☠;; #r +ₗ #1 <- #0;; #r +ₗ #2 <- #0;; jump: k [#r] {{ _, True }}
```
Here, `#☠` is the return value of the operation, which is unusable
(as indicated by the mark `☠`).
By `iIntros "⧖2"` and `wp_seq`, the goal turns into:
```
...
"⧖2" : ⧖2
--------------------------------------∗
WP #r +ₗ #1 <- #0;; #r +ₗ #2 <- #0;; jump: k [#r] {{ _, True }}
```

#### **Execute `"r" +ₗ #1 <- #0;; "r" +ₗ #2 <- #0;;`**

Now let's perform the remaining writes.
By `wp_op`, we can perform the location offset operation `+ₗ`:
```
...
--------------------------------------∗
WP #(r +ₗ 1) <- #0;; #r +ₗ #2 <- #0;; jump: k [#r] {{ _, True }}
```
Here, `+ₗ` in `r +ₗ 1` is a Coq-level operation, whereas `+ₗ` in `#r +ₗ #1`
was a connective in λRust.
By `wp_write` we perform the write to `r +ₗ 1`, updating `"↦₁"`.
Similarly, by `wp_op` and `wp_write`, we perform the write to `r +ₗ 2`,
updating `"↦₂"`.
We perform `do 2 wp_seq` to perform extra program steps included in
`jump: k [#r]`.

#### **Call the continuation**

Now the goal is as follows.
```
"Na" : na_own tid ⊤
"L" : llctx_interp [ϝ ⊑ₗ []] 1
"C" : cctx_interp tid postπ [k ◁cont{...} tr_ret]
"Obs" : ⟨π, postπ π []⟩
"†" : freeable_sz' 3 r
"↦₀" : r ↦ #l
"↦₁" : (r +ₗ 1) ↦ #0
"↦₂" : (r +ₗ 2) ↦ #0
"†'" : freeable_sz' 0 l
"⧖2" : ⧖2
--------------------------------------∗
WP k [#r] {{ _, True }}
```
By performing `rewrite cctx_interp_singleton`,
you can modify `"C"` into `cctx_elt_interp tid postπ (k ◁cont{...} tr_ret)`,
which unfolds into the following:
```
∀ (vl: vec val 1) (pπl: *[list 𝔄]),
  na_own tid ⊤ -∗ llctx_interp [ϝ ⊑ₗ []] 1 -∗
  tctx_interp tid +[vhd vl ◁ box (vec_ty ty)] pπl -∗
  ⟨π, tr_ret (postπ π) (pπl -$ π)⟩ -∗
  WP k (map of_val vl) {{ _, True }}
```
Setting `vl` to `[# #r]` and `pπl` to `-[const []]`, this simplifies into
the following:
```
na_own tid ⊤ -∗ llctx_interp [ϝ ⊑ₗ []] 1 -∗
tctx_interp tid +[#r ◁ box (vec_ty ty)] pπl -∗
⟨π, postπ π []⟩ -∗
WP k [#r] {{ _, True }}
```
So we can apply `"C"` to the goal.
The premises `na_own tid ⊤` and `llctx_interp [ϝ ⊑ₗ []] 1` can be resolved
by `"Na"` and `"L"`.
The premise `⟨π, postπ π []⟩` can be resolved by `"Obs"`.
So the remaining goal is the output type context
`tctx_interp tid +[#r ◁ box (vec_ty ty)] pπl`.
For that, you can perform the tactic:
```
iApply ("C" $! [# #r] -[const []] with "Na L [-Obs] Obs").
```
After `$!` are the pure-level arguments `vl := [# #r]` and
`pπl := -[const []]`.
For the output type context goal, we specify `[-Obs]`,
which allows us to use all the resources we have other than `"Obs"`.

Now we have the following goal:
```
"†" : freeable_sz' 3 r
"↦₀" : r ↦ #l
"↦₁" : (r +ₗ 1) ↦ #0
"↦₂" : (r +ₗ 2) ↦ #0
"†'" : freeable_sz' 0 l
"⧖2" : ⧖2
--------------------------------------∗
tctx_interp tid +[#r ◁ box (vec_ty ty)] -[const []]
```
The main goal simplifies into
`tctx_elt_interp tid (#r ◁ box (vec_ty ty)) (const []) ∗ True`.
You can remove `∗ True` by `iSplit; [|done]`.
The main goal `tctx_elt_interp ...` further simplifies into:
```
∃ (v: val) (d: nat),
  ⌜eval_path #r = Some v⌝ ∗ ⧖d ∗
  ty_own (box (vec_ty ty)) (const []) d tid [v]
```
You set `v := #r` and `d := 2` by `iExists #r, 2`.
You can resolve `⌜eval_path #r = Some v⌝` and `⧖d` by `do 2 (iSplit; [done|])`.
Now the main goal is `ty_own (box (vec_ty ty)) (const []) 2 tid [#r]`, which
simplifies into:
```
▷ (∃ vl, r ↦∗ vl ∗ ty_own (vec_ty ty) (const []) 2 tid vl) ∗
freeable_sz 3 3 r
```
By `rewrite/= freeable_sz_full`, `freeable_sz 3 3 r` turns into `freeable_sz' 3 r`.
So you can frame out `†`, using `iFrame "†"`.
You can remove the later modality `▷` by `iNext`.

#### **Construct the vector**

You set `vl := [#l; #0; #0]` by `iExists [ #l; #0; #0]`.
You can destruct the goal's `r ↦∗ [#l; #0; #0]` by
`rewrite !heap_mapsto_vec_cons !shift_loc_assoc heap_mapsto_vec_nil`.
Then you can frame out `"↦₀"`, `"↦₁"` and `"↦₂"` by `iFrame "↦₀ ↦₁ ↦₂"`.

Now the main goal is just `ty_own (vec_ty ty) (const []) 2 tid vl`,
which simplifies into:
```
∃ (l0 : loc) (len ex : nat) (aπl : vec (proph 𝔄) len),
  ⌜[#l; #0; #0] = [#l0; #len; #ex] ∧ const [] = lapply aπl⌝ ∗
  ▷ ([∗ list] i↦aπ ∈ aπl, (l0 +ₗ[ty] i) ↦∗: ty_own ty aπ 0 tid) ∗
  (l0 +ₗ[ty] len) ↦∗len ex * ty.(ty_size) ∗
  freeable_sz' ((len + ex) * ty_size ty) l0
```
You set `l0 := l`, `len := 0`, `ex := 0`, and `aπl := [#]`
(the empty list) by `iExists l, 0, 0, [#]`.
Now the main goal simplifies into:
```
⌜[#l; #0; #0] = [#l; #0; #0] ∧ const [] = lapply []⌝ ∗
▷ True ∗ (l +ₗ[ty] 0) ↦∗len 0 ∗ freeable_sz' 0 l
```
The pure proposition can be resolved by `iSplit; [done|]`.
You can frame out `"†'"` by `iFrame "†'"`.
The `▷ True` part can be resolved by `iSplit; [by iNext|]`.
Finally, the main goal simplifies into:
```
∃ vl, ⌜length vl = 0⌝ ∗ (l +ₗ 0) ↦∗ vl
```
You can resolve it by `iExists []` and `by rewrite heap_mapsto_vec_nil`.

## Verifying swap via mutable references `mem::swap`

Now let's verify a simple function that handle *mutable borrows*,
`mem::swap`.
The function takes two mutable references of type `&'a mut T`
and swaps the contents of the two.
(Rather surprisingly, it cannot be implemented within safe code in Rust,
due to the limit of Rust's automated ownership/borrow check.)

### Implementation in λRust

Here is the implementation of the function in λRust (`typing/lib/swap.v`).
```
Definition swap {𝔄} (ty: type 𝔄) : val :=
  fn: ["ba"; "bb"] :=
    let: "a" := !"ba" in let: "b" := !"bb" in
    delete [ #1; "ba"];; delete [ #1; "bb"];;
    lang.lib.swap.swap ["a"; "b"; #ty.(ty_size)];;
    let: "r" := new [ #0] in return: ["r"].
```

The inputs `"ba"` and `"bb"` are respectively a *box pointer* to a mutable
reference, because for simplicity a function's inputs is always *boxed* in our
type-spec system.
The mutable references `"a"` and `"b"` can be taken by dereferencing them
(`!"ba"` and `!"bb"`),
and then we can delete the memory blocks for the box pointers
(`delete [ #1; "ba"]` and `delete [ #1; "bb"]`).

Now we swap the values of `"a"` and `"b"`'s memory regions.
The size of the memory regions is respectively `ty.(ty_size)`,
where `ty` is the target type of the mutable references.
We can perform this (low-level) swap by `lang.lib.swap.swap` (`lang/lib/swap.v`),
which satisfies the following Hoare triple law (the lemma `wp_swap`).
```
  Z.of_nat (length vl1) = n → Z.of_nat (length vl2) = n →
  {{{ l1 ↦∗ vl1 ∗ l2 ↦∗ vl2 }}}
    swap [ #l1; #l2; #n] @ E
  {{{ RET #☠; l1 ↦∗ vl2 ∗ l2 ↦∗ vl1 }}}
```

Finally, we should return a box pointer to a unit (because the type-spec
system expects some boxed output, again for simplicity).
So we do `let: "r" := new [ #0] in return: ["r"]`.

### The type-spec rule

The lemma for the type-spec rule of `swap` is as follows.
```
Lemma swap_type {𝔄} (ty: type 𝔄) :
  typed_val (swap ty) (fn<α>(∅; &uniq{α} ty, &uniq{α} ty) → ())
    (λ post '-[(a, a'); (b, b')], a' = b → b' = a → post ()).
```
The function inputs two mutable references typed `&uniq{α} ty` and
outputs a unit `()` (where the inputs and output are actually boxed,
as we saw earlier).
The function has the lifetime parameter `α`.

Let's focus on the predicate transformer spec:
```
λ post '-[(a, a'); (b, b')], a' = b → b' = a → post ()
```
The mutable references are respectively represented by a *pair* of
values, `(a, a')` / `(b, b')`.
Here, `a` / `b` is the target object's *current* representation value,
whereas `a'` / `b'` is the *prophecy* for the target object's *final*
representation value.

Because you *drop* the input mutable references, you *resolve*
the prophecies `a'` and `b'` to the final values, which are
`b` and `a`, respectively, as the result of swap.
So we get equalities `a' = b` and `b' = a` as *postconditions*,
which are appended to `post ()` by *implication* `→`.
(Recall that the predicate transformer returns the *precondition*;
hence we use *implication* to weaken the precondition.)

### Proving the type-spec rule

Proof of this lemma can go as follows.
```
Proof.
  eapply type_fn; [apply _|].
  intros α ϝ k (w & w' &[]). simpl_subst.
  (* destruct typed_body *)
  iIntros (tid (pπ & pπ' &[]) postπ)
    "/= #LFT TIME PROPH #UNIQ #E Na L C (ba & bb &_) #Obs".
  rewrite/= !tctx_hasty_val.
  (* destruct box pointers *)
  iDestruct "ba" as ([|da']) "[_ box]"=>//.
  iDestruct "bb" as ([|db']) "[_ box']"=>//.
  case w as [[|bl|]|]=>//. case w' as [[|bl'|]|]=>//=.
  rewrite !split_mt_uniq_bor.
  iDestruct "box" as "[[#In mut] †ba]".
  iDestruct "box'" as "[[_ mut'] †bb]".
  iDestruct "mut" as (l d ξi) "(>[% %Eq] & >↦ba & Vo & Bor)".
  iDestruct "mut'" as (l' d' ξi') "(>[% %Eq'] & >↦bb & Vo' & Bor')".
  (* let: "a" := !"ba" in let: "b" := !"bb" in *)
  wp_read. wp_let. wp_read. wp_let.
  (* delete [ #1; "ba"];; delete [ #1; "bb"];; *)
  rewrite -!heap_mapsto_vec_singleton !freeable_sz_full.
  wp_apply (wp_delete with "[$↦ba $†ba]"); [done|]. iIntros "_". wp_seq.
  wp_apply (wp_delete with "[$↦bb $†bb]"); [done|]. iIntros "_".
  (* get access to the borrows's contents *)
  iMod (lctx_lft_alive_tok α with "E L") as (q) "([α α₊] & L & ToL)";
    [solve_typing..|].
  iMod (bor_acc with "LFT Bor α") as "[big ToBor]"; [done|].
  iMod (bor_acc with "LFT Bor' α₊") as "[big' ToBor']"; [done|]. wp_seq.
  iDestruct "big" as (vπ dx) "(#⧖ & Pc & %vl & ↦ & ty)".
  iDestruct "big'" as (vπ' dx') "(#⧖' & Pc' & %vl' & ↦' & ty')".
  iDestruct (uniq_agree with "Vo Pc") as %[<-<-].
  iDestruct (uniq_agree with "Vo' Pc'") as %[<-<-].
  (* perform swap *)
  iDestruct (ty_size_eq with "ty") as %?.
  iDestruct (ty_size_eq with "ty'") as %?.
  wp_apply (wp_swap with "[$↦ $↦']"); [lia..|]. iIntros "[↦ ↦']". wp_seq.
  (* perform update *)
  iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|].
  iMod (uniq_update with "UNIQ Vo' Pc'") as "[Vo' Pc']"; [done|].
  (* close borrows and L' *)
  iMod ("ToBor" with "[Pc ↦ ty']") as "[Bor α]".
  { iNext. iExists _, _. iFrame "⧖' Pc". iExists _. iFrame. }
  iMod ("ToBor'" with "[Pc' ↦' ty]") as "[Bor' α₊]".
  { iNext. iExists _, _. iFrame "⧖ Pc'". iExists _. iFrame. }
  iMod ("ToL" with "[$α $α₊] L'") as "L".
  (* wrap up *)
  set qπ := λ π, ((pπ' π).1, (pπ π).2).
  set qπ' := λ π, ((pπ π).1, (pπ' π).2).
  iApply (type_type +[#l ◁ &uniq{α} ty; #l' ◁ &uniq{α} ty] -[qπ; qπ']
    with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
  - iApply type_new; [done|]. intro_subst.
    iApply type_jump; [solve_typing|solve_extract|solve_typing].
  - iSplitL "Vo Bor"; [|iSplitL; [|done]].
    + rewrite (tctx_hasty_val #l). iExists (S d').
      iFrame "⧖' In". iExists d', ξi.
      move: Eq. rewrite (proof_irrel (prval_to_inh (fst ∘ pπ))
        (prval_to_inh (fst ∘ qπ)))=> ?.
      by iFrame.
    + rewrite (tctx_hasty_val #l'). iExists (S d).
      iFrame "⧖ In". iExists d, ξi'.
      move: Eq'. rewrite (proof_irrel (prval_to_inh (fst ∘ pπ'))
        (prval_to_inh (fst ∘ qπ')))=> ?.
      by iFrame.
  - iApply proph_obs_impl; [|done]=>/= π. by case (pπ π), (pπ' π).
Qed.
```

First, you do magical `eapply type_fn; [apply _|]`, and the goal turns into:
```
∀ (α ϝ: lft) (k: val) (wl: *[val; val]),
  ⊢ typed_body ...
```
Here, `α` is the lifetime parameter and `wl` is the list of input low-level values.
So you can introduce the Coq-level values by `intros α ϝ k (w & w' &[])`,
destructing `wl` into `-[w; w']`.
You do `simpl_subst` to substitute the low-level values `k`, `w`, `w'`.

#### **Destruct `typed_body`**

Now the goal is as follows:
```
⊢ typed_body (fp_E ... ϝ) [ϝ ⊑ₗ []]
    [k ◁cont{[ϝ ⊑ₗ []], λ v: vec val 1, +[vhd v ◁ box ()]} tr_ret]
    +[w ◁ box (&uniq{α} ty); w' ◁ box (&uniq{α} ty)]
    (let: "a" := !w in let: "b" := !w' in
      delete [#1; w];; delete [#1; w'];;
      lib.swap.swap ["a"; "b"; #(ty_size ty)];;
      let: "r" := new [#0] in jump: k ["r"])
    (λ (post: () → Prop) '-[(a, a'); (b, b')], a' = b → b' = a → post ())
```
You can destruct `typed_body` by:
```
iIntros (tid (pπ & pπ' &[]) postπ)
  "/= #LFT TIME PROPH #UNIQ #E Na L C (ba & bb &_) #Obs".
```
Here, `pπ` and `pπ'` are the clairvoyant *pair* that represents each of
the two mutable references.
The Iris resources `"ba"` and `"bb"` are items of the input type context.
By `rewrite/= !tctx_hasty_val`, you further update `"ba"` and `"bb"`.

#### **Destruct the box pointers**

Now the goal is as follows.
```
"LFT" : lft_ctx
"UNIQ" : uniq_ctx
"E" : elctx_interp (fp_E ... ϝ)
"Obs" : ⟨π, let '(a, a') := pπ π in let '(b, b') := pπ' π in
              a' = b → b' = a → postπ π ()⟩
--------------------------------------□
"TIME" : time_ctx
"PROPH" : proph_ctx
"Na" : na_own tid ⊤
"L" : llctx_interp [ϝ ⊑ₗ []] 1
"C" : cctx_interp tid postπ [k ◁cont{...} tr_ret]
"ba" : ∃ do, ⧖do ∗ ty_own (box (&uniq{α} ty)) pπ dd tid [w]
"bb" : ∃ do', ⧖do' ∗ ty_own (box (&uniq{α} ty)) pπ' dd' tid [w']
--------------------------------------∗
WP let: "a" := !w in let: "b" := !w' in
    delete [#1; w];; delete [#1; w'];;
    lib.swap.swap ["a"; "b"; #(ty_size ty)];;
    let: "r" := new [#0] in jump: k ["r"] {{ _, True }}
```
Let's destruct the boxes of `"ba"` and `"bb"`.

By `iDestruct "ba" as ([|di]) "[_ box]"; [done|]`,
you can destruct the depth `do` under `"ba"`'s `∃` into `S di` and
take out `ty_own ... [w]` as `"box"`.
(The case `do := 0` is resolved by `done`.)
Similarly, you do `iDestruct "bb" as ([|di']) "[_ box]"; [done|]`.

By `case w as [[|bl|]|]=>//=`, you destruct `w` into `#bl`
for the location `bl: loc`
(the other cases for `w` are resolved by `//`).
Similarly, you do `case w' as [[|bl'|]|]=>//=`.
Now you have "unlocked" the box pointers!
You can further simplify the Iris propositions by `rewrite !split_mt_uniq_bor`.

Now `"box"` and `"box'"` are as follows.
```
"box" : ▷ (α ⊑ ty_lft ty
           ∗ (∃ (l: loc) (d: nat) (ξi: positive), ...))
        ∗ freeable_sz 1 1 bl
"box'" : ▷ (α ⊑ ty_lft ty
            ∗ (∃ (l': loc) (d': nat) (ξi': positive), ...))
         ∗ freeable_sz 1 1 bl'
```
You destruct `"box"` by `iDestruct "box" as "[[#In mut] †ba]"`.
Similarly, you do `iDestruct "box'" as "[[_ mut'] †bb]"`.
You destruct `"mut"` by
`iDestruct "mut" as (l d ξi) "(>[% %Eq] & >↦ba & Vo & Bor)"`.
Similarly, you do
`iDestruct "mut'" as (l' d' ξi') "(>[% %Eq'] & >↦bb & Vo' & Bor')"`.

#### **Execute the preliminary code**

Now the premises are as follows:
```
...
"↦ba" : bl ↦ #l
"Vo" : ▷ .VO[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ)) ξi] (fst ∘ pπ) d
"Bor" : ▷ &{α} ...
"†ba" : freeable_sz 1 1 bl
"↦bb" : bl' ↦ #l'
"Vo'" : ▷ .VO[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ')) ξi'] (fst ∘ pπ') d'
"Bor'" : ▷ &{α} ...
"†bb" : freeable_sz 1 1 bl'
```
By `wp_read` and `wp_let`, you can execute `let: "a" := !"ba" in`.
Similarly, you do `wp_read` and `wp_let` again to execute `let: "b" := !"bb" in`.
The later modality `▷` on `"Vo"`/`"Vo'"` and `"Bor"`/`"Bor'"` disappears
after a program step passes.

Now let's execute `delete [#1; "ba"];; delete [#1; "bb"];;`.
You first do `rewrite -!heap_mapsto_vec_singleton !freeable_sz_full`
to modify `"↦ba"`/`"↦bb"` and `"†ba"`/`"†bb"`.
Now you can execute `delete [#1; "ba"]` by
`wp_apply (wp_delete with "[$↦ba $†ba]"); [done|]` and `iIntros "_"`.
This consumes `"↦ba"` and `"†ba"` (because of framing by `$`).
You execute `#☠;;` by `wp_seq` (where `☠` is the unusable return value of
`delete`).
Similarly you do `wp_apply (wp_delete with "[$↦bb $†bb]"); [done|]` and
`iIntros "_"`.

#### **Get access to the borrows's contents**

Now the goal is as follows.
```
"Vo" : .VO[PrVar (𝔄 ↾ ...) ξi] (fst ∘ pπ) d
"Bor" : &{α} (∃ (vπ: proph (𝔄 ↾ ...)) (dx: nat),
          ⧖(S dx) ∗ .PC[PrVar (𝔄 ↾ ...) ξi] vπ dx ∗
          l ↦∗: ty_own ty vπ dx tid)
"Vo'" : .VO[PrVar (𝔄 ↾ ...) ξi'] (fst ∘ pπ') d'
"Bor'" : &{α} (∃ (vπ': proph (𝔄 ↾ ...)) (dx': nat),
          ⧖(S dx') ∗ .PC[PrVar (𝔄 ↾ ...) ξi'] vπ' dx' ∗
          l' ↦∗: ty_own ty vπ’ dx' tid)
--------------------------------------∗
WP #☠;; lib.swap.swap [#l; #l'; #(ty_size ty)] ;;
  let: "r" := new [#0] in jump: k ["r"] {{ _, True }}
```
You want to get access to the contents of the borrows `"Bor"` and `"Bor'"`.

You first need the *lifetime tokens* for the lifetime `α`.
You can do so by the following tactic, which uses the lemma `lctx_lft_alive_tok`:
```
iMod (lctx_lft_alive_tok α with "E L") as (q) "([α α₊] & L & ToL)";
  [solve_typing..|].
```
Now you get the following:
```
"α" : (q / 2).[α]
"α₊" : (q / 2).[α]
"L'" : llctx_interp [ϝ ⊑ₗ []] q
"ToL" : q.[α] -∗ llctx_interp [ϝ ⊑ₗ []] q ={⊤}=∗ llctx_interp [ϝ ⊑ₗ []] 1
```

You can get access to the borrow `"Bor"`'s contents by the lifetime logic's law
`bor_acc` (in `lifetime/lifetime.v`; called LftL-bor-acc in the paper).
More specifically, you do the following tactic:
```
iMod (bor_acc with "LFT Bor α") as "[big ToBor]"; [done|]`.
```
Out of the full borrow `"Bor" : &{α} P` and the lifetime token `(q / 2).[α]`,
you can get the borrow's content `"big" : ▷ P` and
the resource for closing the borrow `"ToBor" : ▷ P ={⊤}=∗ &{α} P ∗ (q / 2).[α]`.
Similarly, you do
`"iMod (bor_acc with "LFT Bor' α₊") as "[big' ToBor']"; [done|]"`.
You can do `wp_seq` here to execute `#☠;;` and remove the later modality on
`"big"`/`"big'"`.

Now you get the following:
```
"big" : ∃ (vπ: proph (𝔄 ↾ ...)) (dx: nat),
          ⧖(S dx) ∗ .PC[PrVar (𝔄 ↾ ...) ξi] vπ dx ∗
          l ↦∗: ty_own ty vπ dx tid
"ToBor" : ▷ (∃ (vπ: proph (𝔄 ↾ ...)) (dx: nat),
               ⧖(S dx) ∗ .PC[PrVar (𝔄 ↾ ...) ξi] vπ dx ∗
               l ↦∗: ty_own ty vπ dx tid)
          ={⊤}=∗ &{α} (∃ (vπ: proph (𝔄 ↾ ...)) (dx: nat),
                   ⧖(S dx) ∗ .PC[PrVar (𝔄 ↾ ...) ξi] vπ dx ∗
                   l ↦∗: ty_own ty vπ dx tid) ∗
                 (q / 2).[α]
"big'" : ∃ (vπ': proph (𝔄 ↾ ...)) (dx': nat),
           ⧖(S dx') ∗ .PC[PrVar (𝔄 ↾ ...) ξi'] vπ' dx' ∗
           l' ↦∗: ty_own ty vπ’ dx' tid
"ToBor'" : ▷ (∃ (vπ': proph (𝔄 ↾ ...)) (dx': nat),
                ⧖(S dx') ∗ .PC[PrVar (𝔄 ↾ ...) ξi'] vπ' dx' ∗
                l' ↦∗: ty_own ty vπ’ dx' tid)
           ={⊤}=∗ &{α} (∃ (vπ': proph (𝔄 ↾ ...)) (dx': nat),
                    ⧖(S dx') ∗ .PC[PrVar (𝔄 ↾ ...) ξi'] vπ' dx' ∗
                    l' ↦∗: ty_own ty vπ’ dx' tid) ∗
                  (q / 2).[α]
```

Now you destruct `"big"` by
`iDestruct "big" as (vπ dx) "(#⧖ & Pc & %vl & ↦ & ty)"`.
Similarly you do
`iDestruct "big'" as (vπ' dx') "(#⧖' & Pc' & %vl' & ↦' & ty')"`.

By agreement between `"Vo"` and `"Pc"` (by `uniq_agree`),
you can get `fst ∘ pπ = vπ` and `d = dx`,
so you do replacements `vπ -> fst ∘ pπ` and `dx -> d`.
This can be done by the tactic
`iDestruct (uniq_agree with "Vo Pc") as %[<-<-]`.
Similarly, you do
`iDestruct (uniq_agree with "Vo' Pc'") as %[<-<-]`.

Now the goal is as follows.
```
"Pc" : .PC[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ)) ξi]
         (fst ∘ pπ) d
"↦" : l ↦∗ vl
"ty" : ty_own ty (fst ∘ pπ) d tid vl
"ToBor" : ...
"Pc'" : .PC[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ')) ξi']
          (fst ∘ pπ') d'
"↦'" : l' ↦∗ vl'
"ty'" : ty_own ty (fst ∘ pπ') d' tid vl'
"ToBor'" : ...
```

Thanks to `"ty"` and the lemma `ty.(ty_size_eq)`, you can know
`length vl = ty.(ty_size)`, through the tactic
`iDestruct (ty_size_eq with "ty") as %?`.
You similarly do `iDestruct (ty_size_eq with "ty'") as %?`.

#### **Perform swap and update values**

Now you can perform `lang.lib.swap.swap`, simply by
`wp_apply (wp_swap with "[$↦ $↦']"); [lia..|]`.
By `iIntros "[↦ ↦']"` you get the updated points-to tokens.
By `wp_seq` you execute `#☠;;`.

Let's also update the values observed by
`"Vo"`/`"Vo'"` and `"Pc"`/`"Pc'"`.
For that, yoi can use the lemma `uniq_update`.
You do `iMod (uniq_update with "UNIQ Vo Pc") as "[Vo Pc]"; [done|]`
and `iMod (uniq_update with "UNIQ Vo' Pc'") as "[Vo' Pc']"; [done|]`.
Here, the updated values are left to be *evars*, existential
variables in Coq.

#### **Wrap up**

Now you can close `"ToBor"` using `"Pc"`, `"↦"` and `"ty'"` to retrieve
`"Bor"` and `"α"`, by the tactic
`iMod ("ToBor" with "[Pc ↦ ty']") as "[Bor α]"`.
Here, you use `"ty'"` instead of `"ty"`, because the target objects have
been swapped.
The small goal can be resolved by
`{ iNext. iExists _, _. iFrame "⧖' Pc". iExists _. iFrame. }`.
Similarly, you do `iMod ("ToBor'" with "[Pc' ↦' ty]") as "[Bor' α₊]"`
and `{ iNext. iExists _, _. iFrame "⧖ Pc'". iExists _. iFrame. }`.
Now you can close `ToL` to retrieve `L` by
`iMod ("ToL" with "[$α $α₊] L'") as "L"`.

The goal is as follows now:
```
"Vo" : .VO[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ)) ξi] (fst ∘ pπ') d'
"Vo'" : .VO[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ')) ξi'] (fst ∘ pπ) d
"Bor" : &{α} (∃ (vπ': proph (𝔄 ↾ prval_to_inh (fst ∘ pπ))) (dx': nat),
          ⧖(S dx') ∗
          .PC[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ)) ξi] vπ' dx' ∗
          l ↦∗: ty_own ty vπ' dx' tid)
"Bor'" : &{α} (∃ (vπ: proph (𝔄 ↾ prval_to_inh (fst ∘ pπ'))) (dx: nat),
           ⧖(S dx) ∗
           .PC[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ')) ξi'] vπ dx ∗
           l' ↦∗: ty_own ty vπ dx)
"L" : llctx_interp [ϝ ⊑ₗ []] 1
--------------------------------------∗
WP let: "r" := new [#0] in jump: k ["r"] {{ _, True }}
```
You are reaching the end!

Let's do `set qπ := λ π, ((pπ' π).1, (pπ π).2)`
and `set qπ' := λ π, ((pπ π).1, (pπ' π).2)`.
You know that you can wrap up by creating the type context
```
+[#l ◁ &uniq{α} ty; #l' ◁ &uniq{α} ty]
```
with values `-[qπ; qπ']`.
In that case, you perform the following tactic
to call the key lemma `type_type` (`typing/programs.v`).
```
iApply (type_type +[#l ◁ &uniq{α} ty; #l' ◁ &uniq{α} ty] -[qπ; qπ']
  with "[] LFT TIME PROPH UNIQ E Na L C [-] []").
```
The goal divides into three small goals.

The first goal is the `typed_body ...` thing.
Here, you can really use type-spec rules.
First, you do `iApply type_new; [done|]` and `intro_subst`
to perform `let: "r" := new [#0] in`,
getting a box pointer to a unit.
Then you return from the function, executing `jump: k ["r"]`.
The type-spec rule for the jump
*automatically drops up all the unreturned objects*,
and when a mutable reference is dropped
*its prophecy is resolved*!
So the following does the work.
```
iApply type_jump; [solve_typing|solve_extract|solve_typing].
```
Here, `solve_typing` and `solve_extract` do some advanced
*automation* in Coq behind the scene.

The second goal is to actually create the type context,
which consists of the two mutable references.
You can split the goal into the goals for each mutable reference
by the tactic `iSplitL "Vo Bor"; [|iSplitL; [|done]]`.
Let's focus on proof for the first mutable reference,
since proof for the second one just goes similarly.

The goal is as follows.
```
...
"In" : α ⊑ ty_lft ty
"⧖" : ⧖(S d)
"⧖'" : ⧖(S d')
--------------------------------------□
"Vo" : .VO[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ)) ξi] (fst ∘ pπ') d'
"Bor" : &{α} (∃ (vπ': proph (𝔄 ↾ prval_to_inh (fst ∘ pπ))) (dx': nat),
          ⧖(S dx') ∗
          .PC[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ)) ξi] vπ' dx' ∗
          l ↦∗: ty_own ty vπ' dx' tid)
--------------------------------------∗
tctx_elt_interp tid (#l ◁ &uniq{α} ty) qπ
```
By `rewrite (tctx_hasty_val #l)` and `iExists (S d')`,
the main goal turns into:
```
⧖(S d') ∗ ty_own (&uniq{α} ty) qπ (S d') tid [#l]
```
After `iFrame "⧖' In"` and `iExists d', ξi`, the main goal is:
```
⌜(S d' <= S d') ∧
  snd ∘ qπ = (λ π, π (PrVar (𝔄 ↾ prval_to_inh (fst ∘ qπ)) ξi))⌝ ∗
.VO[PrVar (𝔄 ↾ prval_to_inh (fst ∘ qπ)) ξi] (fst ∘ qπ) d' ∗
&{α} (∃ (vπ': proph (𝔄 ↾ prval_to_inh (fst ∘ pπ))) (dx': nat),
  ⧖(S dx') ∗
  .PC[PrVar (𝔄 ↾ prval_to_inh (fst ∘ pπ)) ξi] vπ' dx' ∗
  l ↦∗: ty_own ty vπ' dx' tid)
```
You can end the proof by rewriting
`prval_to_inh (fst ∘ pπ)` into `prval_to_inh (fst ∘ qπ)`!
That is possible using the lemma `proof_irrel` for (axiom-free)
proof irrelevance, because `prval_to_inh ...` is actually a proof
witness of a proposition.
You just need to do
```
move: Eq. rewrite (proof_irrel (prval_to_inh (fst ∘ pπ))
  (prval_to_inh (fst ∘ qπ)))=> ?.
```
Now `by iFrame` ends the proof for the first mutable reference.
As mentioned earlier, proof for the second mutable reference just goes similarly.

Now the remaining goal is:
```
...
"Obs" : ⟨π, let '(a, a') := pπ π in let '(b, b') := pπ' π in
              a' = b → b' = a → postπ π ()⟩
...
--------------------------------------□
⟨π, (pπ π).2 = (pπ' π).1 → (pπ' π).2 = (pπ π).1 → postπ π ()⟩
```
You can directly use `"Obs"` to get the remaining goal.
However, `done` doesn't work because Coq can't turn directly
equate the pattern matching `let '(a, a') := pπ π in`
with `let a = (pπ π).1 in let a' = (pπ π).2 in`.

You can use the lemma `proph_obs_impl` to solve a situation like this.
By `iApply proph_obs_impl; [|done]=>/= π`, the goal turns into:
```
(let '(a, a') := pπ π in let '(b, b') := pπ' π in
  a' = b → b' = a → postπ π ()) →
(pπ π).2 = (pπ' π).1 → (pπ' π).2 = (pπ π).1 → postπ π ()
```
You can end the proof by the tactic `by case (pπ π), (pπ' π)`.

It was a long journey, but now you have proved `swap_type`!
Woo-hoo!
