* (Empty.  The color preservation port is COMPLETE — statement approved
  and proof landed 2026-09-21, PR #207.  Two deltas against the reviewed
  material, both flagged on the PR for Jeremy:

    1. `CopyResidual`/`ImageResidual` regained v7's DEPTH INDEX: without
       it, when a β-redex's argument is itself a `crossΛᴹ`-shaped
       wrapper, a depth-1 occurrence can match `image-here` and claim
       the unwrapped source position one `Λ` in — a derivation for which
       the color equation is FALSE.  The index pins the leaf to the
       walk's depth (`Residual.agda` §5's comment).
    2. `ColorPreservation` gained a `WfCtx Δ` premise: the run's
       intermediate terms are re-typed by `preservation`, which is
       conditional on `WfCtx Δ`.  It is the price of stating over any Δ;
       `ColorPreservationClosed` is the v7-faithful closed form without
       it.

  The proof (`proof/ColorPreservation.agda`): `residual-frame`
  constructs the target position's frame derivation per step —
  frame-for-frame everywhere except the three movers, which go through
  `⊢C-ren`, the transport of `Δ ⊢C C ⊣ Δ′` along a representation-only
  renaming built on `interior-ren`/`RepWk`; the minted boundary frames
  read by `instantiate-interior`, `dual-interior`, `rewind-interior`,
  `merged-interior`, `addLock0-interior-ren`, `crossΛ-interior`.
  `residuals-color` composes along `ρ′ ∘ ρ` re-typing by
  `preservation`.  The typing premise is spent at exactly two sites:
  Peel's argument (`bw-binds` of the redex's own `env`, feeding
  `repwk-wkN`) and TyPeelR-⟪⟫ (`instantiate-boundarywf` for the
  refined store's well-formedness).)
