# Retired v7 proof scripts

`ConversionCanonical.agda` (v7) — the canonical views of typed normal
conversions under the v7 rules (`after-seal` on the old tail judgment).
Superseded by `proof/Canonical.agda`, which redoes the shape suite over
the v8 elements; the v7 `after-seal` argument is the model for the
canonicity obligation still open in `proof/Progress.agda`.

2026-09-15: the remaining v7 proof scripts were retired here in bulk
when the v8 mechanization reached preservation.  None were in
`All.agda`; they reference the v7 context layer (anchors, scopes,
stores in terms) and do not compile against v8.  The ones whose
ARGUMENTS survive in v8, under new names, are worth keeping for
reference: `ConversionCanonical` (the `after-seal` argument, now
`proof/ConvCanonicity`), `AnchorWeaken` (the depth-indexed weakening
design), `RevealTyping` (builder typing, still to be redone),
`PreserveBeta`/`PreserveTyBeta` (the case structure), and
`RenameAlgebra` (the renaming-algebra idioms).
