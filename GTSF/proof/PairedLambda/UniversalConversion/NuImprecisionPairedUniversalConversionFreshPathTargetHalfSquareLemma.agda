module
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareLemma
  where

-- File Charter:
--   * Canonically assembles both target fresh-path half-squares from their
--     strict structural half-square lemmas.
--   * Contains no recursive implementation, postulate, hole, permissive
--     option, handler import, or broad simulation import.

open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ
  )
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareProof
  using
  ( paired-universal-conversion-fresh-path-target-conceal-half-square-proofᵀ
  ; paired-universal-conversion-fresh-path-target-reveal-half-square-proofᵀ
  )
open import
  proof.PairedLambda.UniversalConversion.NuImprecisionPairedUniversalConversionFreshPathTargetStructuralHalfSquareLemma
  using
  ( paired-universal-conversion-fresh-path-target-structural-conceal-half-square-lemmaᵀ
  ; paired-universal-conversion-fresh-path-target-structural-reveal-half-square-lemmaᵀ
  )


paired-universal-conversion-fresh-path-target-reveal-half-square-lemmaᵀ :
  PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-reveal-half-square-lemmaᵀ
    {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
    {c′} {η′} {α} {β} {pX} {r} {s}
    correspondence conversion occurs-B b-at e-at =
  paired-universal-conversion-fresh-path-target-reveal-half-square-proofᵀ
    (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {D} {E} {C′} {X} {X′}
        {d′} {η′} {α} {β} {pX} {r} {s}
        correspondence conversion occurs-B b-at e-at →
      paired-universal-conversion-fresh-path-target-structural-reveal-half-square-lemmaᵀ
        {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
        {B = B} {D = D} {E = E} {C′ = C′} {X = X} {X′ = X′}
        {d′ = d′} {η′ = η′} {α = α} {β = β}
        {pX = pX} {r = r} {s = s}
        correspondence conversion occurs-B b-at e-at)
    {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
    {c′ = c′} {η′ = η′} {α = α} {β = β}
    {pX = pX} {r = r} {s = s}
    correspondence conversion occurs-B b-at e-at


paired-universal-conversion-fresh-path-target-conceal-half-square-lemmaᵀ :
  PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ
paired-universal-conversion-fresh-path-target-conceal-half-square-lemmaᵀ
    {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
    {c′} {η′} {α} {β} {pX} {r} {s}
    correspondence conversion occurs-B b-at e-at =
  paired-universal-conversion-fresh-path-target-conceal-half-square-proofᵀ
    (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {D} {E} {C′} {X} {X′}
        {d′} {η′} {α} {β} {pX} {r} {s}
        correspondence conversion occurs-B b-at e-at →
      paired-universal-conversion-fresh-path-target-structural-conceal-half-square-lemmaᵀ
        {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
        {B = B} {D = D} {E = E} {C′ = C′} {X = X} {X′ = X′}
        {d′ = d′} {η′ = η′} {α = α} {β = β}
        {pX = pX} {r = r} {s = s}
        correspondence conversion occurs-B b-at e-at)
    {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
    {c′ = c′} {η′ = η′} {α = α} {β = β}
    {pX = pX} {r = r} {s = s}
    correspondence conversion occurs-B b-at e-at
