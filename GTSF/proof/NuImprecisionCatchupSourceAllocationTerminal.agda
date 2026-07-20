{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuImprecisionCatchupSourceAllocationTerminal where

-- File Charter:
--   * Freezes the two nonrecursive terminal-value boundaries for source-only
--     allocation catch-up.
--   * Frames an already-computed inner catch-up by `ν A` or `ν ★`, stopping
--     before the allocation step and any subsequent recursive catch-up.
--   * The intended proofs weaken the source conversion evidence across the
--     supplied store prefix, then use the corresponding source frame together
--     with its transport and type-coherence preservation lemmas.
--   * Depends only on the quotiented precision judgment and the stable weak
--     simulation core.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Coercions using (instᵈ)
open import Conversion using (RevealConversion)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTerms using (No•; Value; ν)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (WfTy; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.NuImprecisionSimulationCore using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; sourceResult
  ; weakIndexedResult
  ; catchupIndexedResult
  )

left-silent-indexed-prefix-source-ν-terminal-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ A B B′ C N V′ s μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  WfTy Δᴸ A →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  (catchup : LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} q) →
  let inner = weakIndexedResult (catchupIndexedResult catchup) in
  Value (sourceResult inner) →
  No• (sourceResult inner) →
  LeftSilentIndexedResult
    {N = ν A N s} {V′ = V′} {ρ = ρ⁺} p
left-silent-indexed-prefix-source-ν-terminal-valueᵀ = {!!}

left-silent-indexed-prefix-source-νcast-terminal-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ B B′ C N V′ s μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  (catchup : LeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} q) →
  let inner = weakIndexedResult (catchupIndexedResult catchup) in
  Value (sourceResult inner) →
  No• (sourceResult inner) →
  LeftSilentIndexedResult
    {N = ν ★ N s} {V′ = V′} {ρ = ρ⁺} p
left-silent-indexed-prefix-source-νcast-terminal-valueᵀ = {!!}
