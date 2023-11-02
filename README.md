# RustHornBelt COQ DEVELOPMENT

This is the Coq development for "Formal Specification and Verification Techniques for Mutable References and Advanced Aliasing in Rust".

## Prerequisites

This version is known to compile with:

- Coq 8.15.2
- A development version of [Iris](https://gitlab.mpi-sws.org/iris/iris)
  (the version `dev.2022-04-12.0.a3bed7ea`)

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

## IDE support with VS Code

After building from source (see above) you can install and use the VS Code
extension [VsCoq Legacy](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1)
to explore the proofs.

## Walkthrough

There is a walkthrough ([walkthrough.md](walkthrough.md)) of RustHornBelt's Coq
development.

It explains in detail how to verify integer addition, model `Vec`, verify
`Vec::new`, and verify `mem::swap` (featuring mutable borrows).

It is intended as a hands-on guide to our (huge) Coq development.
In particular, it focuses on the things you need to know to reuse and extend
the Coq development.

## Structure

The [theories](theories) folder, which contains the Coq mechanization,
is structured as follows.
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

## Key Modifications from the THESIS

### Chapter 3 Ghost Unsoundness
 * Level definition: [`syn_type.v`](theories/prophecy/syn_type.v) `ghost_level`
 * Updated resolution requirement: [`prophecy.v`](theories/prophecy/prophecy.v) `proph_resolve`
 * Prophecy Predicate: [`type.v`](theories/typing/type.v) `ty_proph`
 * Updated type requirements: [`type.v`](theories/typing/type.v)  `ty_own_proph`/`ty_shr_proph`/`ty_proph_weaken`
   - All types needed to be updated to defined there prophecy predicate and prove that they meet these new requirements
 * Ghost type ownership/prophecy predicate [`ghost.v`](theories/typing/ghost.v)  `ghost` (`st_own`/`st_proph`)
 * Creating a ghost without consuming [`ghost.v`](theories/typing/ghost.v)  `ghost_new_instr`
 * Ghost can be mapped by a ghost function [`ghost.v`](theories/typing/ghost.v) `logic_fn_ghost_tctx_incl`
 * Basic operations in ghost functions [`ghost_fn.v`](theories/typing/ghost_fn.v)
 * Library operations in ghost functions [`lib_ghost_fn.v`](theories/typing/lib/lib_ghost_fn.v)
 
### Chapter 4 GhostPtrToken
 * `GhostPtrToken` definition [`ghostptrtoken.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken.v) `ghostptrtoken_ty`
   - Note `GhostPtrToken<T>` is internally as an alias for `GhostSeq<PermData<T>`
     - [`permdata.v`](theories/typing/lib/ghostptrtoken/permdata.v) `permdata_ty`
     - [`ghostseq.v`](theories/typing/lib/ghostptrtoken/ghostseq.v) `ghostseq_ty`
   - This breakdown is inspired by how `GhostPtrToken` would be implemented in [Verus](https://arxiv.org/pdf/2303.05491.pdf) and will hopefully make it easier to add similar types
   - The Lemma [`ghostptrtoken.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken.v) `ghostptrtoken_own_alt` proves an equivalent version of the ownership predicate
 * `GhostPtrToken::new`: [`ghostseq_basic.v`](theories/typing/lib/ghostptrtoken/ghostseq_basic.v) `ghostseq_new_type` 
   - Since `GhostPtrToken<T>` is an alias `GhostPtrToken::new` is just `GhostSeq::new`
 * `GhostPtrToken::ptr_from_box`:  [`ghostptrtoken_grow.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_grow.v) `ghostptrtoken_insert_type` 
 * `GhostPtrToken::ptr_to_box`:  [`ghostptrtoken_index.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_index.v) `ghostptrtoken_remove_type`
 * `GhostPtrToken::ptr_as_ref`:  [`ghostptrtoken_index.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_index.v) `ghostptrtoken_borrow_type`
 * `GhostPtrToken::ptr_as_mut`: Not proven since it can be implemented by using `GhostPtrToken::take_mut`
 * `GhostPtrToken::shrink_token_ref`:  [`ghostptrtoken_shrink_shr.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_shrink_shr.v) `ghostptrtoken_merge_type` 
 * `GhostPtrToken::merge`:  [`ghostptrtoken_grow.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_grow.v) `ghostptrtoken_shrink_shr_type` 
 * `GhostPtrToken::take_mut` (With missing spec): [`ghostptrtoken_take_mut.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_take_mut.v) `ghostptrtoken_take_mut_type` 
 * `GhostPtrTokenMut` definition
   - Build using the [`uniq_alt_ty.v`](theories/typing/uniq_alt.v) `uniq_alt_ty` utility for weakening the ownership predicates of mutable references 
   - Ownership predicate is [`ghostptrtoken_mut.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_mut.v) `ghostptrtoken_ty_uniq_alt_base`
 * Creating `GhostPtrTokenMut` [`uniq_alt_ty.v`](theories/typing/uniq_alt.v) `uniq_alt_intro`
 * `GhostPtrTokenMut::deref` [`uniq_alt_borrow.v`](theories/typing/uniq_alt_borrow.v) `alt_type_deref_shr_uniq`
 * `GhostPtrTokenMut::deref_mut` [`uniq_alt_borrow.v`](theories/typing/uniq_alt_borrow.v) `alt_type_deref_uniq_uniq`
 * `GhostPtrTokenMut::resolve` [`uniq_resolve.v`](theories/typing/uniq_resolve.v) `alt_uniq_resolve`
 * `GhostPtrTokenMut::take_mut` [`ghostptrtoken_mut.v`](theories/typing/lib/ghostptrtoken/ghostptrtoken_mut.v) `ghostptrtoken_take_mut_type`

## For Developers: How to update the Iris dependency

- Do the change in Iris, push it.
- Wait for CI to publish a new Iris version on the opam archive, then run
  `opam update iris-dev`.
- In lambdaRust, change the `opam` file to depend on the new version.
- Run `make build-dep` (in lambdaRust) to install the new version of Iris.
  You may have to do `make clean` as Coq will likely complain about `.vo` file
  mismatches.
