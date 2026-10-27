#!/bin/sh
# WORKAROUND (tooling skew): the installed cargo-hax (hax main 721d1a27) writes
# Lean-module wrappers (`module` / `public import`), but the pinned aeneas and
# TlsCodec are on Lean v4.31 with non-module files, and a `module` cannot import
# a non-module. Strip the module syntax from the three hax-written wrappers.
# Run after every `cargo hax extract openmls-codec`. Undo: delete this script
# once the whole stack (TlsCodec, aeneas, Lean) moves to the module system.
cd "$(dirname "$0")/.." || exit 1
for f in OpenmlsCodec/Extraction.lean OpenmlsCodec/Extraction/FunsExternal.lean OpenmlsCodec/Extraction/TypesExternal.lean; do
  sed -i -e '/^module$/d' -e 's/^public import /import /' "$f"
done

# WORKAROUND (aeneas, cross-crate default methods): the provided lemma methods of the
# tls_codec `spec` traits (`round_trip`, `nonempty`, `round_trip_std`, `round_trip_exact`,
# `nonempty_std`, `same_bytes`) have empty bodies, so TlsCodec's extraction defines their
# `.default` without the unused `Self: Trait` instance parameter, while this extraction
# passes the instance being defined. Drop that argument (the `.default` is `ok ()` either
# way). Undo: delete this block once aeneas agrees on the signature across crates.
perl -0pi -e 's/(tls_codec\.spec\.(?:io\.)?\w+\.\w+\.default)\s+[\w.]+\.Insts\.Tls_codecSpec\w+/$1/g' \
  OpenmlsCodec/Extraction/Funs.lean

# WORKAROUND (aeneas, cross-crate default methods): the lemma methods of
# `DecodersAgree` have no `self`, so TlsCodec's extraction gives their `.default` an
# explicit `Self` type parameter, while this extraction omits it. Pass the impl's
# type (the `.default` is `ok ()` for any). Undo: delete this block once aeneas agrees
# on the signature across crates.
perl -0pi -e 's{(impl_def\s+\S+\s*:\s*tls_codec\.spec\.io\.DecodersAgree\s+)(\S+)(\s*:=\s*\{.*?\n\})}{my ($a, $t, $b) = ($1, $2, $3); $b =~ s/(tls_codec\.spec\.io\.DecodersAgree\.(?:decoders_agree|bytes_prefix_only)\.default)(?!\s+\()/$1 ($t)/g; "$a$t$b"}gse' \
  OpenmlsCodec/Extraction/Funs.lean
