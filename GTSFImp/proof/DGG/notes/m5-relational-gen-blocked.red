M5 relational blocker: `gen-cont`

Date: 2026-08-11

Blocked statement:

  InstRelContinuationSurface.gen-cont

This is the `allv-gen` branch of `InstCatchupRightAt fuel`, after the common
`β-inst` prefix and the catalogued `β-gen` target step.

The direct proof reaches a post-catalog target of the shape:

  (⇑ᵗᵐ V′ ⟨ d ⟩ ↑ 〖 Fin.zero , ★ ↑ B 〗)

To call the smaller extra-cast worker on the outer residual, this term must
be a value and must be related to `M` at the source obligation of the
residual.  The catalog premise supplies only `GenSafe d`; it does not give
an `Inert d` witness in the recursive `safe-inst` and `safe-gen` cases, so
`Value (⇑ᵗᵐ V′ ⟨ d ⟩)` is not generally derivable.

The blocked relational/provenance package is:

  W₂ ∣ γ₂ ⊢² M ⊑ (⇑ᵗᵐ V′ ⟨ d ⟩ ↑ conv) ∶ p₂
  CatchupCast⁻ p₂ (χ ▷ᶜ ↑ᶜ (close-instᶜ c′))
    (ECR.transport⊑ᵂ ext₂ q)

The smallest surface change made in this pass is the new
`InstRelContinuationSurface` record, whose `gen-cont` field leaves this
view-specific continuation explicit.  A real proof needs a continuation for
the `GenSafe` spine that either reduces it to a value or exposes the smaller
catch-up call that does so.
