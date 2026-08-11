M5 relational blocker: `reveal-cont`

Date: 2026-08-11

Blocked statement:

  InstRelContinuationSurface.reveal-cont

This is the `allv-reveal` branch of `InstCatchupRightAt fuel`, after the
common `β-inst` prefix and the catalogued `β-reveal-∀` target step.

The direct proof reaches the post-catalog target:

  (((⇑ᵗᵐ V′ ⦂∀ applyBody (bind D) C [ ＇ Fin.zero ]) ↑ d)
    ↑ 〖 Fin.zero , ★ ↑ B 〗)

The immediate residual-cast route is blocked for the same structural reason
as the `∀` case: the term under the reveals contains a pending type
application, so it is not a `Value` and cannot be passed directly to
`ExtraCastRightAt`.

The missing continuation must derive both:

  W₂ ∣ γ₂ ⊢² M ⊑ post ∶ p₂
  CatchupCast⁻ p₂ (χ ▷ᶜ ↑ᶜ (close-instᶜ c′))
    (ECR.transport⊑ᵂ ext₂ q)

and must then keep reducing the exposed type-application spine to a target
value.  No live stage-1 surface exposes that package from a relation against
a target `V′ ↑ `∀↑ d` value.  The new `InstRelContinuationSurface`
record keeps `reveal-cont` as the explicit per-view obligation instead of
changing the existing `InstCatchupRightAt` statement.
