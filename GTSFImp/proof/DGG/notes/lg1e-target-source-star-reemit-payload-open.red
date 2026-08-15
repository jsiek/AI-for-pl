LG-1e open internal M3 reemit blocker: target-source-star payload too weak

Current command:

  agda -i GTSFImp -v0 GTSFImp/proof/DGG/Inversion/TargetChainProof.agda

Current remaining TargetChain failure is in the recursive variable-tag
continuation after the new branch-sensitive `TargetSourceStarAtResult`.

The final branch works:

  target-source-star-final sourcePrem

is consumed by `STC.emit-tagged-transfer` exactly as before.

The full paired branch with partner data is also locally consumable.  It rebuilds
the inner paired square

  P ↓ seal X ★  ⊑  U₀ ↓ seal Y₂ ★

casts both sides to the top tag, then emits a `name-protected-target`
source-only premise for the outer package.

The remaining missing branch is:

  target-source-star-payload x x₁ x₂ x₃ x₄ x₅ x₆

This payload carries only a bare premise under the source/target payloads.  That
is not enough for variable-tag re-emission: to build the needed package premise

  ((P ↓ seal X ★) ⟨ c ⟩) ↓ seal X ★
    ⊑ (U₀ ↓ seal Y₂ ★) ⟨ cᴿ ! ⟩

the proof must first rebuild the inner paired seal square, which requires the
matched partner data.  A bare `P ⊑ U₀` payload cannot target-seal to
`U₀ ↓ seal Y₂ ★` because that would need a `★ ⊑ ＇ Y₂` type-imprecision
witness, which the live relation intentionally does not provide.

Conclusion: the internal target-source-star/reemit result must carry a richer
branch for these residuals.  Weakening to a bare payload loses information and
cannot be consumed by the next re-emission layer.  The next patch should either:

- carry the matched partner data through the residual payload branch with its
  actual target partner, or
- mirror `TargetSealReemitInput` more directly by representing a delayed
  paired/name-protected reemit step rather than a bare `P ⊑ U` premise.

This is not a protected public-surface stop: `TargetWalkDef` and
`TargetChainProof` are M3-internal machinery per the LG-1d supervisor ruling.
