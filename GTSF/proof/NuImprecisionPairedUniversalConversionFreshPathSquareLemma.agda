module
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareLemma
  where

-- File Charter:
--   * Canonically assembles the fresh-path square from the strict target
--     reveal and conceal half-square lemmas.
--   * Contains no recursive implementation, postulate, hole, permissive
--     option, handler import, or broad simulation import.

open import
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareDef
  using (PairedUniversalConversionFreshPathSquareᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareProof
  using (paired-universal-conversion-fresh-path-square-proofᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareLemma
  using
  ( paired-universal-conversion-fresh-path-target-conceal-half-square-lemmaᵀ
  ; paired-universal-conversion-fresh-path-target-reveal-half-square-lemmaᵀ
  )


paired-universal-conversion-fresh-path-square-lemmaᵀ :
  PairedUniversalConversionFreshPathSquareᵀ
paired-universal-conversion-fresh-path-square-lemmaᵀ
    {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {c} {c′}
    {r} {s} {p} x-at occurs-B conversion =
  paired-universal-conversion-fresh-path-square-proofᵀ
    (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
        {c′} {η′} {α} {β} {pX} {r} {s}
        correspondence target-reveal occurs-B b-at e-at →
      paired-universal-conversion-fresh-path-target-reveal-half-square-lemmaᵀ
        {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
        {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
        {c′ = c′} {η′ = η′} {α = α} {β = β}
        {pX = pX} {r = r} {s = s}
        correspondence target-reveal occurs-B b-at e-at)
    (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
        {c′} {η′} {α} {β} {pX} {r} {s}
        correspondence target-conceal occurs-B b-at e-at →
      paired-universal-conversion-fresh-path-target-conceal-half-square-lemmaᵀ
        {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
        {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
        {c′ = c′} {η′ = η′} {α = α} {β = β}
        {pX = pX} {r = r} {s = s}
        correspondence target-conceal occurs-B b-at e-at)
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
    {B = B} {B′ = B′} {E = E} {C′ = C′} {c = c} {c′ = c′}
    {r = r} {s = s} {p = p} x-at occurs-B conversion
