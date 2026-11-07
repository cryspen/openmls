# Proofs of the tls_codec impls of OpenMLS

Lean proofs that the tls_codec (de)serializers of `openmls_traits`,
`openmls_basic_credential` and `openmls` satisfy the tls_codec specs (panic
freedom, round trip, ...). The Rust code is extracted with hax (hax -> charon
-> aeneas -> Lean) against the Lean model of tls_codec, the `TlsCodec` Lean
project of the tls_codec fork that the workspace `Cargo.toml` patches tls_codec
to ([cryspen/formats](https://github.com/cryspen/formats), branch
`proofs/lean/tls_codec-aeneas-4.35`).

| Scenario (`hax.toml`)    | Crate                      | Lean project                                         |
|--------------------------|----------------------------|------------------------------------------------------|
| `traits-codec`           | `openmls_traits`           | `traits/proofs/traits-codec/lean` (`TraitsCodec`)     |
| `basic-credential-codec` | `openmls_basic_credential` | `basic_credential/proofs/basic-credential-codec/lean` |
| `openmls-codec`          | `openmls`                  | `openmls/proofs/openmls-codec/lean`                   |

Each Lean project requires TlsCodec from git (same cryspen/formats revision as
the Cargo patch), which brings the aeneas Lean library (cryspen/aeneas
`38960402`), hax-lean and mathlib; the two downstream projects also require
`TraitsCodec` by relative path. Each project has its own `.lake/packages`.

## Requirements

- Rust (rustup) and `cargo-hax` (hax with proof-scenario support, `cargo hax
  extract`), Lean via elan (the toolchain of the projects' `lean-toolchain`).
- To build aeneas: nix, or OCaml / opam with the dependencies of the aeneas
  README.
- `protoc` only for workspace-wide cargo builds (the `interop_client` crate);
  the extraction and the per-crate tests do not need it.

## Replay

All commands run from the repository root.

1. Build the aeneas binary that `hax.toml` points at
   (`.hax-tools/aeneas/bin/aeneas`, git-ignored; charon is downloaded by hax):

       sh proofs/setup.sh

2. Fetch the Lean dependencies of each project (TlsCodec, aeneas, hax, mathlib
   and its build cache). Needed before extracting: the scenarios read
   TlsCodec's `translation.json` from `.lake/packages/TlsCodec`.

       for p in traits/proofs/traits-codec/lean \
                basic_credential/proofs/basic-credential-codec/lean \
                openmls/proofs/openmls-codec/lean; do
         (cd $p && lake exe cache get)
       done

3. Extract, in dependency order (a bare `cargo hax extract` runs the scenarios
   in alphabetical order), then apply the post-extraction fix-up of each
   project:

       cargo hax extract traits-codec basic-credential-codec openmls-codec
       sh traits/proofs/traits-codec/lean/scripts/post_extract.sh
       sh basic_credential/proofs/basic-credential-codec/lean/scripts/post_extract.sh
       sh openmls/proofs/openmls-codec/lean/scripts/post_extract.sh

   The extraction rewrites only the `Extraction/` folders and the
   `translation.json` files; they should be identical to the committed ones:

       git status --short -- '*/proofs/*'

4. Build each project and run its gates, from the project directory:

       lake build                              # the proofs
       lake build TlsCodec.Tools.AxiomGate     # the gate's tool (not imported by the proofs)
       lake env lean scripts/AxiomGate.lean    # axioms vs scripts/axiom_whitelist.txt
       python3 scripts/check_statements.py     # proved statements = generated obligations

   `Verification/AxiomCheck.lean` prints the axioms of each obligation
   (`lake env lean <Project>/Verification/AxiomCheck.lean`).

The Rust side builds and tests as usual (`cargo test -p openmls`); the
codec-related fixes come with their own tests.
