module
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingAssemblyProof
  where

-- File Charter:
--   * Connects the complete semantic-handler assembly and shared target-frame
--     capability to the final proof-relevant frame-closing theorem.
--   * Unpacks the reusable twenty-one-capability record once, providing the
--     top-level fit skeleton below DGG catch-up without repeatedly forwarding
--     dependent higher-order arguments through every upper consumer.
--   * Contains no semantic implementation, postulate, hole, permissive
--     option, broad simulation import, or canonical `Lemma` assembly.

open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingCapabilitiesDef
  using
  ( PairedLambdaTargetClosingFrameClosingCapabilities
  ; cap-fresh-path-target-structural-conceal-half-square
  ; cap-fresh-path-target-structural-reveal-half-square
  ; cap-lambda-lambda-structural-conceal
  ; cap-lambda-lambda-structural-reveal
  ; cap-paired-conversion-conceal
  ; cap-paired-conversion-reveal
  ; cap-paired-widening-source-inert-core
  ; cap-paired-widening-target-inert-bridge
  ; cap-source-all-all-index
  ; cap-source-gen-structural-conceal
  ; cap-source-gen-structural-reveal-core
  ; cap-target-conceal
  ; cap-target-id-only-widening
  ; cap-target-narrowing
  ; cap-target-reveal-core
  ; cap-target-widening
  ; cap-up-gen-all-quotient-cast-widening
  ; cap-up-gen-all-quotient-id-widening
  ; cap-up-gen-leaf-all-index
  ; cap-up-id-quotient-cast-widening
  ; cap-up-id-quotient-id-widening
  )
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingHandlersProof
  using (paired-lambda-target-closing-frame-closing-handlers-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingProof
  using (paired-lambda-target-closing-frame-closing-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameCasesDef
  using (PairedLambdaTargetClosingFrameClosingTargetRevealᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameProof
  using (paired-lambda-target-closing-frame-closing-target-frame-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetRevealProof
  using
  (paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationDef
  using (PairedLambdaTargetClosingNuPairedConversionRotationᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingNuPairedConversionRotationProof
  using
  (paired-lambda-target-closing-ν-paired-conversion-rotation-proofᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathCycleDef
  using (PairedUniversalConversionFreshPathCycleᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathCycleProof
  using (paired-universal-conversion-fresh-path-cycle-proofᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareDef
  using (PairedUniversalConversionFreshPathSquareᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathSquareProof
  using (paired-universal-conversion-fresh-path-square-proofᵀ)
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareDef
  using
  ( PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ
  ; PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ
  )
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathTargetHalfSquareProof
  using
  ( paired-universal-conversion-fresh-path-target-conceal-half-square-proofᵀ
  ; paired-universal-conversion-fresh-path-target-reveal-half-square-proofᵀ
  )
open import
  proof.NuImprecisionSourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingDef
  using
  (SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ)


paired-lambda-target-closing-frame-closing-assembly-proofᵀ :
  PairedLambdaTargetClosingFrameClosingCapabilities →
  SourceNuPairedAllConversionPostBetaAllRevealClosingRelationFrameClosingᵀ
paired-lambda-target-closing-frame-closing-assembly-proofᵀ
    record
      { cap-fresh-path-target-structural-reveal-half-square =
          structural-reveal-half
      ; cap-fresh-path-target-structural-conceal-half-square =
          structural-conceal-half
      ; cap-lambda-lambda-structural-reveal = lambda-lambda-reveal
      ; cap-lambda-lambda-structural-conceal = lambda-lambda-conceal
      ; cap-up-gen-leaf-all-index = up-gen-all-index
      ; cap-source-gen-structural-reveal-core = source-gen-reveal
      ; cap-source-gen-structural-conceal = source-gen-conceal
      ; cap-source-all-all-index = source-all-all-index
      ; cap-paired-conversion-reveal = paired-conversion-reveal
      ; cap-paired-conversion-conceal = paired-conversion-conceal
      ; cap-paired-widening-source-inert-core = paired-widening-source-inert
      ; cap-paired-widening-target-inert-bridge =
          paired-widening-target-inert-bridge
      ; cap-up-id-quotient-id-widening = up-id-id
      ; cap-up-id-quotient-cast-widening = up-id-cast
      ; cap-up-gen-all-quotient-id-widening = up-gen-all-id
      ; cap-up-gen-all-quotient-cast-widening = up-gen-all-cast
      ; cap-target-reveal-core = target-reveal-core
      ; cap-target-conceal = target-conceal
      ; cap-target-narrowing = target-narrowing
      ; cap-target-widening = target-widening
      ; cap-target-id-only-widening = target-id-only-widening
      } =
  paired-lambda-target-closing-frame-closing-proofᵀ
    (paired-lambda-target-closing-frame-closing-handlers-proofᵀ
      rotate lambda-lambda-reveal lambda-lambda-conceal up-gen-all-index
      (λ {Φ} {Δᴸ} {Δᴿ} {ρ₀} {ρ} {ρν} {ρ∀}
          {V} {N′} {F} {B} {B′} {A} {C′} {D} {E} {X} {X′}
          {g} {c} {c′} {t} {η} {η′} {θ} {μ} {α} {β}
          {q} {r} {p} {pX}
          vV noV vN′ noN′ relation mode seal h∀F occ-B g⊢ gⁿ
          inner prefix h⇑A final-reveal liftν lift∀ corresponds
          source-reveal target-reveal →
        source-gen-reveal
          {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
          {ρ₀ = ρ₀} {ρ = ρ} {ρν = ρν} {ρ∀ = ρ∀}
          {V = V} {N′ = N′} {F = F} {B = B} {B′ = B′}
          {A = A} {C′ = C′} {D = D} {E = E} {X = X} {X′ = X′}
          {g = g} {c = c} {c′ = c′} {t = t}
          {η = η} {η′ = η′} {θ = θ} {μ = μ} {α = α} {β = β}
          {q = q} {r = r} {p = p} {pX = pX}
          vV noV vN′ noN′ relation mode seal h∀F occ-B g⊢ gⁿ
          inner prefix h⇑A final-reveal liftν lift∀ corresponds
          source-reveal target-reveal)
      source-gen-conceal source-all-all-index
      paired-conversion-reveal paired-conversion-conceal
      paired-widening-source-inert paired-widening-target-inert-bridge
      up-id-id up-id-cast up-gen-all-id up-gen-all-cast)
    (paired-lambda-target-closing-frame-closing-target-frame-proofᵀ
      target-reveal target-conceal target-narrowing target-widening
      target-id-only-widening)
  where
  reveal-half :
    PairedUniversalConversionFreshPathTargetRevealHalfSquareᵀ
  reveal-half
      {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
      {c′} {η′} {α} {β} {pX} {r} {s}
      corresponds target-reveal occ-B fresh-path =
    paired-universal-conversion-fresh-path-target-reveal-half-square-proofᵀ
      (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {D} {E} {C′} {X} {X′}
          {d′} {η′} {α} {β} {pX} {r} {s}
          corresponds target-reveal occ-B fresh-path →
        structural-reveal-half
          {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
          {B = B} {D = D} {E = E} {C′ = C′} {X = X} {X′ = X′}
          {d′ = d′} {η′ = η′} {α = α} {β = β}
          {pX = pX} {r = r} {s = s}
          corresponds target-reveal occ-B fresh-path)
      {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
      {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
      {c′ = c′} {η′ = η′} {α = α} {β = β}
      {pX = pX} {r = r} {s = s}
      corresponds target-reveal occ-B fresh-path

  conceal-half :
    PairedUniversalConversionFreshPathTargetConcealHalfSquareᵀ
  conceal-half
      {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
      {c′} {η′} {α} {β} {pX} {r} {s}
      corresponds target-conceal occ-B fresh-path =
    paired-universal-conversion-fresh-path-target-conceal-half-square-proofᵀ
      (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {D} {E} {C′} {X} {X′}
          {d′} {η′} {α} {β} {pX} {r} {s}
          corresponds target-conceal occ-B fresh-path →
        structural-conceal-half
          {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
          {B = B} {D = D} {E = E} {C′ = C′} {X = X} {X′ = X′}
          {d′ = d′} {η′ = η′} {α = α} {β = β}
          {pX = pX} {r = r} {s = s}
          corresponds target-conceal occ-B fresh-path)
      {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
      {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
      {c′ = c′} {η′ = η′} {α = α} {β = β}
      {pX = pX} {r = r} {s = s}
      corresponds target-conceal occ-B fresh-path

  square : PairedUniversalConversionFreshPathSquareᵀ
  square = paired-universal-conversion-fresh-path-square-proofᵀ
    (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
        {c′} {η′} {α} {β} {pX} {r} {s}
        corresponds target-reveal occ-B fresh-path →
      reveal-half
        {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
        {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
        {c′ = c′} {η′ = η′} {α = α} {β = β}
        {pX = pX} {r = r} {s = s}
        corresponds target-reveal occ-B fresh-path)
    (λ {p} {Φ} {Δᴸ} {Δᴿ} {ρ} {B} {B′} {E} {C′} {X} {X′}
        {c′} {η′} {α} {β} {pX} {r} {s}
        corresponds target-conceal occ-B fresh-path →
      conceal-half
        {p = p} {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ}
        {B = B} {B′ = B′} {E = E} {C′ = C′} {X = X} {X′ = X′}
        {c′ = c′} {η′ = η′} {α = α} {β = β}
        {pX = pX} {r = r} {s = s}
        corresponds target-conceal occ-B fresh-path)

  cycle : PairedUniversalConversionFreshPathCycleᵀ
  cycle = paired-universal-conversion-fresh-path-cycle-proofᵀ square

  rotate : PairedLambdaTargetClosingNuPairedConversionRotationᵀ
  rotate =
    paired-lambda-target-closing-ν-paired-conversion-rotation-proofᵀ cycle

  target-reveal : PairedLambdaTargetClosingFrameClosingTargetRevealᵀ
  target-reveal =
    paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
      cycle target-reveal-core
