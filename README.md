# RustHornBelt COQ DEVELOPMENT

This is the Coq development for "RustHornBelt: A Semantic Foundation for
Functional Verification of Rust Programs with Unsafe Code".

## Prerequisites

This version is known to compile with:

- Coq 8.13.0
- A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)
  (the version `dev.2021-03-27.0.f1484b2b`)

## Building from source

When building from source, we recommend to use opam (2.0.0 or newer) for
installing the dependencies. This requires the following two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update, do `git pull`. After an update, the development may fail to compile
because of outdated dependencies. To fix that, please run `opam update`
followed by `make build-dep`.

## Walkthrough

We have a [walkthrough](walkthrough.md) of RustHornBelt's Coq mechanization.

It explains in detail how to verify integer addition, model `Vec`, verify
`Vec::new`, and verify `mem::swap` (featuring mutable borrows).
It focuses on the things you need to know to extend our Coq mechanization.

## Structure

- The folder [util](theories/util) contains utility for basic concepts.
  - [fancy_lists.v](theories/util/fancy_lists.v) contains definitions, notation
    and lemmas for heterogeneous lists and related data types.
- The folder [prophecy](theories/prophecy) contains the prophecy library,
  as well as the library for syntactic types.
- The folder [lifetime](theories/lifetime) proves the rules of the lifetime
  logic, including derived constructions like (non-)atomic persistent borrows.
  - The subfolder [model](theories/lifetime/model) proves the core rules, which
    are then sealed behind a module signature in
    [lifetime.v](theories/lifetime/lifetime.v).
- The folder [lang](theories/lang) contains the formalization of the lambda-Rust
  core language, including the theorem showing that programs with data races get
  stuck.
- The folder [typing](theories/typing) defines the domain of semantic types and
  interpretations of all the judgments and also proves all typing rules.
  - [type.v](theories/typing/type.v) contains the definition of the notion
    of the semantic type.
  - [programs.v](theories/typing/programs.v) defines the typing judgments for
    instructions and function bodies.
  - [soundness.v](theories/typing/soundness.v) contains the main soundness
    (adequacy) theorem of the type system.
  - The subfolder [examples](theories/typing/examples) verifies some example
    Rust programs in Coq to conceptually demonstrate how functional verification
    works under the RustHorn-style translation.
  - The subfolder [lib](theories/typing/lib) contains proofs for some APIs
    with unsafe code from the Rust standard library and some user crates.
    Some libraries are not yet verified, being commented out in `_CoqProject`.

### Key Type-Spec Rules --- from the RustHornBelt Paper

The following table contains the location of every rule mentioned in the
RustHornBelt paper.
The filenames are spread across `theories/typing/examples`, `theories/typing`,
`theories/typing/lib` (and its subfolders), and `theories/prophecy`.

| Proof Rule          | File              | Lemma                    |
| ------------------- | ----------------- | ------------------------ |
| Adequacy            | `soundness.v`     | `type_soundness`         |
| **Basic**           |                   |                          |
| MUTBOR              | `derived_rules.v` | `ty_uniq_bor`            |
| MUTREF-WRITE        | `derived_rules.v` | `ty_uniq_ref_write`      |
| MUTREF-BYE          | `derived_rules.v` | `ty_uniq_ref_bye`        |
| ENDLFT              | `programs.v`      | `type_endlft`            |
| **Prophecies**      |                   |                          |
| PROPH-INTRO         | `prophecy.v`      | `proph_intro`            |
| PROPH-FRACT         | `prophecy.v`      | `proph_tok_fractional`   |
| PROPH-IMPL          | `prophecy.v`      | `proph_obs_impl`         |
| PROPH-MERGE         | `prophecy.v`      | `proph_obs_and`          |
| PROPH-TRUE          | `prophecy.v`      | `proph_obs_true`         |
| PROPH-RESOLVE       | `prophecy.v`      | `proph_resolve`          |
| PROPH-SAT           | `prophecy.v`      | `proph_obs_sat`          |
| **Mutable Borrows** |                   |                          |
| MUT-AGREE           | `uniq_cmra.v`     | `uniq_agree`             |
| MUT-UPDATE          | `uniq_cmra.v`     | `uniq_update`            |
| MUT-INTRO           | `uniq_cmra.v`     | `uniq_intro`             |
| MUT-RESOLVE         | `uniq_cmra.v`     | `uniq_resolve`           |
| **`Vec`**           |                   |                          |
| `push`              | `vec_pushpop.v`   | `vec_push_type`          |
| `pop`               | `vec_pushpop.v`   | `vec_pop_type`           |
| `index_mut`         | `vec_index.v`     | `vec_index_uniq_type`    |
| **`IterMut`**       |                   |                          |
| `iter_mut`          | `vec_slice.v`     | `vec_as_uniq_slice_type` |
| `next`              | `iter.v`          | `iter_uniq_next_type`    |
| `inc_vec`           | `inc_vec.v`       | `inc_vec_type`           |
| **`Cell`**          |                   |                          |
| `new`               | `cell.v`          | `cell_new_type`          |
| `get`               | `cell.v`          | `cell_get_type`          |
| `set`               | `cell.v`          | `cell_set_type`          |
| `inc_cell`          | `inc_cell.v`      | `inc_cell_type`          |
| **`Mutex`**         |                   |                          |
| `new`               | `mutex.v`         | `mutex_new_type`         |
| `get_mut`           | `mutex.v`         | `mutex_get_uniq`         |

### Key Type(-Spec) Rules --- from the RustBelt Paper

The files in [typing](theories/typing) prove semantic versions of the proof
rules given in the _RustBelt_ paper. Notice that mutable borrows are called
"unique borrows" in the Coq development.

| Proof Rule            | File            | Lemma                |
| --------------------- | --------------- | -------------------- |
| T-bor-lft (for shr)   | shr_bor.v       | shr_subtype          |
| T-bor-lft (for mut)   | uniq_bor.v      | uniq_subtype         |
| C-subtype             | type_context.v  | subtype_tctx_incl    |
| C-copy                | type_context.v  | copy_tctx_incl       |
| C-split-bor (for shr) | product_split.v | tctx_split_shr_prod  |
| C-split-bor (for mut) | product_split.v | tctx_split_uniq_prod |
| C-share               | borrow.v        | tctx_share           |
| C-borrow              | borrow.v        | tctx_borrow          |
| C-reborrow            | uniq_bor.v      | tctx_reborrow_uniq   |
| Tread-own-copy        | own.v           | read_own_copy        |
| Tread-own-move        | own.v           | read_own_move        |
| Tread-bor (for shr)   | shr_bor.v       | read_shr             |
| Tread-bor (for mut)   | uniq_bor.v      | read_uniq            |
| Twrite-own            | own.v           | write_own            |
| Twrite-bor            | uniq_bor.v      | write_uniq           |
| S-num                 | int.v           | type_int_instr       |
| S-nat-leq             | int.v           | type_le_instr        |
| S-new                 | own.v           | type_new_instr       |
| S-delete              | own.v           | type_delete_instr    |
| S-deref               | programs.v      | type_deref_instr     |
| S-assign              | programs.v      | type_assign_instr    |
| F-consequence         | programs.v      | typed_body_impl      |
| F-let                 | programs.v      | type_let'            |
| F-letcont             | cont.v          | type_cont            |
| F-jump                | cont.v          | type_jump            |
| F-newlft              | programs.v      | type_newlft          |
| F-endlft              | programs.v      | type_endlft          |
| F-call                | function.v      | type_call            |

Some of these lemmas are called `something'` because the version without the
`'` is a derived, more specialized form used together with our `eauto`-based
`solve_typing` tactic. You can see this tactic in action in the
[examples](theories/typing/examples) subfolder.

### Lifetime Logic Rules

The files in [lifetime](theories/lifetime) prove the lifetime logic, with the
core rules being proven in the [model](theories/lifetime/model) subfolder and
then sealed behind a module signature in
[lifetime.v](theories/lifetime/lifetime.v).

| Proof Rule        | File                | Lemma                |
| ----------------- | ------------------- | -------------------- |
| LftL-begin        | model/creation.v    | lft_create           |
| LftL-tok-fract    | model/primitive.v   | lft_tok_fractional   |
| LftL-not-own-end  | model/primitive.v   | lft_tok_dead         |
| LftL-end-persist  | model/definitions.v | lft_dead_persistent  |
| LftL-borrow       | model/borrow.v      | bor_create           |
| LftL-bor-split    | model/bor_sep.v     | bor_sep              |
| LftL-bor-acc      | lifetime.v          | bor_acc              |
| LftL-bor-shorten  | model/primitive.v   | bor_shorten          |
| LftL-incl-isect   | model/primitive.v   | lft_intersect_incl_l |
| LftL-incl-glb     | model/primitive.v   | lft_incl_glb         |
| LftL-tok-inter    | model/primitive.v   | lft_tok_sep          |
| LftL-end-inter    | model/primitive.v   | lft_dead_or          |
| LftL-tok-unit     | model/primitive.v   | lft_tok_static       |
| LftL-end-unit     | model/primitive.v   | lft_dead_static      |
| LftL-reborrow     | lifetime.v          | rebor                |
| LftL-bor-fracture | frac_borrow.v       | bor_fracture         |
| LftL-fract-acc    | frac_borrow.v       | frac_bor_atomic_acc  |
| LftL-bor-na       | na_borrow.v         | bor_na               |
| LftL-na-acc       | na_borrow.v         | na_bor_acc           |

## For Developers: How to update the Iris dependency

- Do the change in Iris, push it.
- Wait for CI to publish a new Iris version on the opam archive, then run
  `opam update iris-dev`.
- In lambdaRust, change the `opam` file to depend on the new version.
- Run `make build-dep` (in lambdaRust) to install the new version of Iris.
  You may have to do `make clean` as Coq will likely complain about `.vo` file
  mismatches.
