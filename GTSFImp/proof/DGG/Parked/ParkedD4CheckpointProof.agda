module proof.DGG.Parked.ParkedD4CheckpointProof where

-- File Charter:
--   * Proves the D4 higher-order-shared-arg parked evolution witness and
--     post-allocation v2 relation checkpoint.
--   * Uses the ParkedWorld/ParkedEvolve interface rather than ad hoc world
--     shape gates.
--   * Contains only total checked definitions and no permissive option.

open import Data.Fin using (zero)
import Data.Fin as Fin
import Data.List as List
open import Relation.Binary.PropositionalEquality using (refl)

import Imprecision as I
open import Reduction using (StoreChanges; keep) renaming (_∷_ to _∷ˢ_)
import Reduction as R
open import TyStore using (Z∋)
open import Primitives using (κℕ)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.Examples2 as Ex2
import proof.DGG.Phase3DeepDives as P3
import proof.DGG.ReachabilityCatalog as RC
open import proof.DGG.Parked.ParkedD4CheckpointDef using
  ( D4-checkpointᵀ
  ; D4-parked-evolve₀₈ᵀ
  ; D4-parked-world₀ᵀ
  ; D4-parked-world₂ᵀ
  )
open import proof.DGG.Parked.ParkedWorldDef using
  ( ParkedEvolve
  ; evolve-both-bind
  ; evolve-keepᴸ
  ; evolve-keepᴿ
  ; evolve-refl
  ; parked-both-bind
  ; parked-initial
  )


D4-callee-rep₂ :
  CTX.StoreRepImp P3.higher-order-shared-arg-world₂ zero zero
D4-callee-rep₂ =
  CTX.store-rep-imp
    (Ex2.ℕ⊑ℕ² {W = P3.higher-order-shared-arg-world₂})


D4-callee-rebase₂ :
  CTX.RebaseAt P3.higher-order-shared-arg-world₂
    P3.higher-order-shared-arg-world₂ zero zero
D4-callee-rebase₂ =
  CTX.sameWorldRebaseAt refl D4-callee-rep₂


D4-parked-world₀-proofᵀ : D4-parked-world₀ᵀ
D4-parked-world₀-proofᵀ = parked-initial {μ = I.idᵐ}


D4-keep-both₁ :
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ′ Δᴿ′ Δ′}
  → ParkedEvolve χsᴸ χsᴿ W W′
  → ParkedEvolve (keep ∷ˢ χsᴸ) (keep ∷ˢ χsᴿ) W W′
D4-keep-both₁ evol = evolve-keepᴸ (evolve-keepᴿ evol)


D4-parked-evolve₀₈-proofᵀ : D4-parked-evolve₀₈ᵀ
D4-parked-evolve₀₈-proofᵀ =
  evolve-both-bind
    (D4-keep-both₁
      (D4-keep-both₁
        (D4-keep-both₁
          (D4-keep-both₁
            (D4-keep-both₁
              (D4-keep-both₁
                (evolve-both-bind evolve-refl)))))))


D4-parked-world₂-proofᵀ : D4-parked-world₂ᵀ
D4-parked-world₂-proofᵀ =
  parked-both-bind
    (Ex2.ℕ⊑ℕ² {W = P3.higher-order-shared-arg-world₁})
    (parked-both-bind
      (P3.symmetric-refl⊑ᵂ
        {W = P3.higher-order-shared-arg-world₀}
        {A = RC.∀X⇒X₀} refl)
      (parked-initial {μ = I.idᵐ}))


D4-checkpoint-proofᵀ : D4-checkpointᵀ
D4-checkpoint-proofᵀ =
  CTI2.·⊑·²
    (CTI2.cast⊑cast² _ _
      (CTI2.cast⊑cast² _ _
        (CTI2.reveal⊑reveal² CTX.impEnvMono-refl
          D4-callee-rebase₂ CTX.same-[]
          (Conv.⊢↑-⇒ˣ Conv.join-both
            (Conv.⊢↓-sealˣ (Z∋ refl))
            (Conv.⊢↑-unsealˣ (Z∋ refl)))
          (Conv.⊢↑-⇒ˣ Conv.join-both
            (Conv.⊢↓-sealˣ (Z∋ refl))
            (Conv.⊢↑-unsealˣ (Z∋ refl)))
          (CTI2.ƛ⊑ƛ²
            {pA = I.X⊑X {X = zero}}
            {pB = I.X⊑X {X = zero}}
            (CTI2.x⊑x² {p = I.X⊑X {X = zero}} CTX.Zʷ))
          (Ex2.ℕ⇒ℕ⊑ℕ⇒ℕ²
            {W = P3.higher-order-shared-arg-world₂}))
        (Ex2.ℕ⇒ℕ⊑ℕ⇒ℕ²
          {W = P3.higher-order-shared-arg-world₂}))
      (Ex2.ℕ⇒ℕ⊑ℕ⇒ℕ²
        {W = P3.higher-order-shared-arg-world₂}))
    (CTI2.cast⊑cast² _ _
      (CTI2.κ⊑κ² (κℕ 5)
        (Ex2.ℕ⊑ℕ² {W = P3.higher-order-shared-arg-world₂}))
      (Ex2.ℕ⊑ℕ² {W = P3.higher-order-shared-arg-world₂}))
