M5 relational blocker: `conceal-cont`

Date: 2026-08-11

Blocked statement:

  InstRelContinuationSurface.conceal-cont

This is the `allv-conceal` branch of `InstCatchupRightAt fuel`, after the
common `β-inst` prefix and the catalogued `β-conceal-∀` target step.

The direct proof reaches the post-catalog target:

  ((⇑ᵗᵐ V′ ⦂∀ applyBody (bind D) C [ ＇ Fin.zero ] ↓ d)
    ↑ 〖 Fin.zero , ★ ↑ B 〗)

The term contains a pending type application under a conceal/reveal wrapper,
so the smaller extra-cast worker cannot be called immediately: its input
requires a target `Value`.

The blocked continuation has to provide the post-catalog relation and the
residual provenance:

  W₂ ∣ γ₂ ⊢² M ⊑ post ∶ p₂
  CatchupCast⁻ p₂ (χ ▷ᶜ ↑ᶜ (close-instᶜ c′))
    (ECR.transport⊑ᵂ ext₂ q)

and then continue the exposed type-application spine to a value.  The
current stage-1 inversion surfaces do not expose this package for a relation
against `V′ ↓ `∀↓ d`.  The new `InstRelContinuationSurface` record keeps
`conceal-cont` explicit as the smallest statement-level hook without
weakening any existing M4/M5/M6 surface.
