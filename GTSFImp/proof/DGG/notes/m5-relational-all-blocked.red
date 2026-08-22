M5 relational blocker: `∀-cont`

Date: 2026-08-11

Blocked statement:

  InstRelContinuationSurface.∀-cont

This is the `allv-∀` branch of `InstCatchupRightAt fuel`, after the common
`β-inst` prefix and the catalogued `β-∀` target step.

The direct proof first reaches the post-catalog target:

  ((V′₂ ⦂∀ A₂ [ D₂ ]) ⟨ d₂ [ D₂ ]ᶜ ⟩)
    ↑ 〖 Fin.zero , ★ ↑ B 〗

The immediate residual-cast route is blocked because the term before the
outer residual cast is not a `Value`: `Value` has constructors for `Λ`,
inert casts, reveals, and conceals over values, but no constructor for a
pending type application `V′₂ ⦂∀ A₂ [ D₂ ]`.

The relational subgoal is therefore not just:

  W₂ ∣ γ₂ ⊢² M ⊑ post ∶ p₂

It must also continue reducing the exposed type-application spine until a
target value is available, while preserving the transported source
obligation and minting term-independent provenance for the residual cast:

  CatchupCast⁻ p₂ (χ ▷ᶜ ↑ᶜ (close-instᶜ c′))
    (ECR.transport⊑ᵂ ext₂ q)

No live M4/M6 surface consumes a non-value right term of this shape.  The
smallest surface change made in this pass is the new
`InstRelContinuationSurface` record, whose `∀-cont` field owns the whole
per-view continuation rather than forcing the single catalog step to feed
directly into `ExtraCastRightAt`.
