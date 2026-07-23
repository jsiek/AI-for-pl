module proof.Catchup.Core.NuImprecisionCatchupSourceAllocationTerminal where

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

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Coercions using (instᵈ)
open import Conversion using (RevealConversion; weaken-reveal-conversion)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NarrowWiden using (widen-weaken)
open import NuStore using (StoreIncl-cons)
open import NuTerms using (No•; Value; ok-no; ok-ν; ν)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (WfTy; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-one-step-source-ν-frameᵀ
  ; weak-one-step-source-ν-frame-preserves-transportᵀ
  ; weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-νcast-frameᵀ
  ; weak-one-step-source-νcast-frame-preserves-transportᵀ
  ; weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; left-indexed-catchup
  ; left-catchup-invariant
  ; left-silent-invariant
  ; left-silent-indexed
  ; sourceResult
  ; relatedResults
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weak-indexed-result
  ; catchupIndexedResult
  )
open import proof.Core.Properties.StoreProperties using (renameStoreᵗ-incl)
open import proof.Core.Properties.TypePreservation using (seal★-weaken)

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
left-silent-indexed-prefix-source-ν-terminal-valueᵀ
    {p = p} prefix hA c↑
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW =
  left-silent-indexed
    (weak-indexed-result framed (relatedResults framed)
      (weak-one-step-source-ν-frame-preserves-transportᵀ
        hA c↑⁺ p inner (weakIndexedTransport indexed))
      (weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
        hA c↑⁺ p inner (weakIndexedTypeCoherence indexed)))
    (left-silent-invariant refl refl)
    (ok-ν (ok-no noW))
  where
  inner = weakIndexedResult indexed

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  c↑⁺ = weaken-reveal-conversion source-store-incl c↑

  framed = weak-one-step-source-ν-frameᵀ hA c↑⁺ p inner

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
left-silent-indexed-prefix-source-νcast-terminal-valueᵀ
    {p = p} prefix mode seal★ c⊑
    (left-indexed-catchup indexed
      (left-catchup-invariant
        (left-silent-invariant refl refl) final))
    vW noW =
  left-silent-indexed
    (weak-indexed-result framed (relatedResults framed)
      (weak-one-step-source-νcast-frame-preserves-transportᵀ
        mode seal★⁺ c⊑⁺ p inner (weakIndexedTransport indexed))
      (weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
        mode seal★⁺ c⊑⁺ p inner (weakIndexedTypeCoherence indexed)))
    (left-silent-invariant refl refl)
    (ok-ν (ok-no noW))
  where
  inner = weakIndexedResult indexed

  source-store-incl =
    StoreIncl-cons
      (renameStoreᵗ-incl suc (leftStoreⁱ-prefix-inclusion prefix))

  seal★⁺ = seal★-weaken source-store-incl seal★

  c⊑⁺ = widen-weaken ≤-refl source-store-incl c⊑

  framed =
    weak-one-step-source-νcast-frameᵀ mode seal★⁺ c⊑⁺ p inner
