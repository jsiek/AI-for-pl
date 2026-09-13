# Pre-merge probes (2026-09-13)

These three checked under `--safe` against the SPLIT-ENTRY context, where a
source name was its own entry pointing at an anchor by index.  They record
what that representation cost, and why the merged-entry context replaced it.
They do NOT type-check against the current `strong.Ctx`, by design — each
exhibits something the merged representation makes unrepresentable.

* `V7ConvIntermediateProbe.agda` — `conv-cons`'s seam was tied to nothing,
  so `∅` could sit between two ends carrying anchors; `SameTy` matched by
  anchor LEVEL, and two contexts counting anchors differently then gave the
  same level to different anchors, making `id(∀Y.Y) : (∀Y.X) ⇒ (∀Y.Y)`
  derivable.  Merged entries make reveal/conceal length-preserving, so
  `SameAnchor` is index equality and the coincidence cannot arise.

* `V7AnchorPartProbe.agda` — `anchorCount` is the length of the anchor
  PART, and equal counts do not determine it; the part itself is invariant
  along a scope change.  Merged entries make that structural.

* `V7DualScopeProbe.agda` — a conceal removed a name IN PLACE and its dual
  reveal put it back ON TOP, so `dual χ` returned the context only up to
  reordering, blocking `Wrap`.  Merged entries flip a bit, and
  `strong.proof.ScopeDual.χ-invert` now proves the round trip EXACT.

The live statement of the last one is `strong.proof.ScopeDual`; the design
argument is in `notes/DECISIONS.md` (2026-09-13).
