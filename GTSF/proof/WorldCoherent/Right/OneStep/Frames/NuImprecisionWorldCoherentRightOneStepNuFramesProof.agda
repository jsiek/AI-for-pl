module
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepNuFramesProof
  where

-- File Charter:
--   * Implements all six structural ν frames for target-oriented
--     world-coherent one-step simulation.
--   * Reuses exact indexed ν frame outcomes whose continuing result keeps the
--     recursive successor store and contexts definitionally unchanged.
--   * Contains no active allocation root, recursive dispatcher, postulate,
--     hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
import CastImprecisionShape as CastShape
open import Coercions using (Coercion; instᵈ)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; ⇑ᴿᵢ
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  ( StoreChange
  ; applyCoercionUnderTyBinder
  ; applyTy
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; ν)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using
  ( Ty
  ; TyCtx
  ; WfTy
  ; occurs
  ; ★
  ; `∀
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( apply-reveal-under-ty-binders
  ; apply-widen-inst-under-ty-binders
  ; weak-indexed-all-resultᵀ
  ; weak-one-step-matched-ν-frame-preserves-transportᵀ
  ; weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-matched-ν-frameᵀ
  ; weak-one-step-matched-νcast-frame-preserves-transportᵀ
  ; weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
  ; weak-one-step-matched-νcast-frameᵀ
  ; weak-one-step-source-ν-frame-preserves-transportᵀ
  ; weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-ν-frameᵀ
  ; weak-one-step-source-νcast-frame-preserves-transportᵀ
  ; weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
  ; weak-one-step-source-νcast-frameᵀ
  ; weak-one-step-target-ν-frame-preserves-transportᵀ
  ; weak-one-step-target-ν-frame-preserves-type-coherenceᵀ
  ; weak-one-step-target-ν-frameᵀ
  ; weak-one-step-target-νcast-frame-preserves-transportᵀ
  ; weak-one-step-target-νcast-frame-preserves-type-coherenceᵀ
  ; weak-one-step-target-νcast-frameᵀ
  ; weak-result-target-all
  )
open import proof.Store.Core.NuImprecisionStoreLift using
  ( lift-left-store-result
  ; lift-right-store-result
  ; lift-store-result
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( relatedResults
  ; resultStore
  ; source-nu-index
  ; sourceChanges
  ; targetTailChanges
  ; transportSourceNu
  ; weak-indexed-result
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ⊑-lift∀ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (ν-blame-tailᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Frames.NuImprecisionWorldCoherentRightOneStepNuFramesDef
  using (WorldCoherentRightOneStepNuFrames)

world-coherent-right-one-step-nu-frames-proofᵀ :
  WorldCoherentRightOneStepNuFrames
world-coherent-right-one-step-nu-frames-proofᵀ =
  record
    { rightStepMatchedNuFrame = matched-ν-frame
    ; rightStepMatchedNuCastFrame = matched-νcast-frame
    ; rightStepSourceNuFrame = source-ν-frame
    ; rightStepSourceNuCastFrame = source-νcast-frame
    ; rightStepTargetNuFrame = target-ν-frame
    ; rightStepTargetNuCastFrame = target-νcast-frame
    }
  where
  matched-ν-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {N N₁′ : Term} {A A′ B B′ C C′ : Ty}
      {s s′ : Coercion} {μ μ′} {χ : StoreChange}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
      {A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    RevealConversion μ (suc Δᴸ)
      ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
      zero (⇑ᵗ A) s C (⇑ᵗ B) →
    RevealConversion μ′ (suc Δᴿ)
      ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
      zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
    (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    q
      [ zero ↦ ⇑ᵗ A
      ⊑⟨ A⇑⊑A′⇑ ⟩
      ⇑ᵗ A′ ↤ zero ]ᴾ
      ⊑-lift∀ᵢ pB →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N} {N′ = N₁′} {A = `∀ C} {B = `∀ C′}
      {χ = χ} {ρ = ρ} (∀ⁱ q) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = ν A N s}
      {N′ = ν (applyTy χ A′) N₁′
        (applyCoercionUnderTyBinder χ s′)}
      {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
  matched-ν-frame {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
      s↑ s′↑ pA replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      with lift-store-result (resultStore (weakIndexedResult inner))
  matched-ν-frame {χ = χ} s↑ s′↑ pA replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ
      with apply-reveal-under-ty-binders
        {χs = sourceChanges (weakIndexedResult inner)} s↑
         | apply-reveal-under-ty-binders
        {χs = χ ∷ targetTailChanges (weakIndexedResult inner)} s′↑
  matched-ν-frame
      {A⇑⊑A′⇑ = A⇑⊑A′⇑} {pB = pB}
      s↑ s′↑ pA replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ | μᵣ , source↑ | μᵗ , target↑ =
    world-indexed-outcome-related framed-indexed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
    where
    all = weak-indexed-all-resultᵀ inner
    inner-result = weakIndexedResult inner
    inner-coherence = weakIndexedTypeCoherence inner
    framed =
      weak-one-step-matched-ν-frameᵀ
        s↑ s′↑ pA A⇑⊑A′⇑ pB replace all inner-coherence
    framed-indexed =
      weak-indexed-result framed (relatedResults framed)
        (weak-one-step-matched-ν-frame-preserves-transportᵀ
          s↑ s′↑ pA A⇑⊑A′⇑ pB replace all inner-coherence
          (weakIndexedTransport inner))
        (weak-one-step-matched-ν-frame-preserves-type-coherenceᵀ
          s↑ s′↑ pA A⇑⊑A′⇑ pB replace all inner-coherence)
  matched-ν-frame s↑ s′↑ pA replace
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (ν-blame-tailᵀ source↠)

  matched-νcast-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {N N₁′ : Term} {B B′ C C′ : Ty}
      {s s′ : Coercion} {μ μ′} {χ : StoreChange}
      {s-shape s′-shape result-shape : ImprecisionShape}
      {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    CastMode μ →
    SealModeStore★ (instᵈ μ)
      ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
    instᵈ μ ∣ suc Δᴸ
      ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
      ⊢ s ∶ C ⊑ ⇑ᵗ B →
    CastMode μ′ →
    SealModeStore★ (instᵈ μ′)
      ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
    instᵈ μ′ ∣ suc Δᴿ
      ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
      ⊢ s′ ∶ C′ ⊑ ⇑ᵗ B′ →
    CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
    CastShape.widening CastShape.⊢ᶜ s′ ⦂ s′-shape →
    s-shape ； ⌊ pB ⌋ ≋ result-shape →
    ⌊ q ⌋ ； s′-shape ≋ result-shape →
    PairedWideningCompatible
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ) s s′
      q (⊑-lift∀ᵢ pB) s-shape s′-shape →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N} {N′ = N₁′} {A = `∀ C} {B = `∀ C′}
      {χ = χ} {ρ = ρ} (∀ⁱ q) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = ν ★ N s}
      {N′ = ν ★ N₁′ (applyCoercionUnderTyBinder χ s′)}
      {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
  matched-νcast-frame {pB = pB}
      mode seal★ s⊑ mode′ seal★′ s′⊑
      s-shape s′-shape source-comp target-comp compat
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      with lift-store-result (resultStore (weakIndexedResult inner))
  matched-νcast-frame {χ = χ}
      mode seal★ s⊑ mode′ seal★′ s′⊑
      s-shape s′-shape source-comp target-comp compat
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ
      with apply-widen-inst-under-ty-binders
        {χs = sourceChanges (weakIndexedResult inner)}
        mode seal★ s⊑
         | apply-widen-inst-under-ty-binders
        {χs = χ ∷ targetTailChanges (weakIndexedResult inner)}
        mode′ seal★′ s′⊑
  matched-νcast-frame
      {pB = pB}
      mode seal★ s⊑ mode′ seal★′ s′⊑
      s-shape s′-shape source-comp target-comp compat
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ
      | μᵣ , modeᵣ , sealᵣ , source⊑
      | μᵗ , modeᵗ , sealᵗ , target⊑ =
    world-indexed-outcome-related framed-indexed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
    where
    all = weak-indexed-all-resultᵀ inner
    inner-coherence = weakIndexedTypeCoherence inner
    framed =
      weak-one-step-matched-νcast-frameᵀ
        mode seal★ s⊑ mode′ seal★′ s′⊑ pB
        s-shape s′-shape source-comp target-comp compat
        all inner-coherence
    framed-indexed =
      weak-indexed-result framed (relatedResults framed)
        (weak-one-step-matched-νcast-frame-preserves-transportᵀ
          mode seal★ s⊑ mode′ seal★′ s′⊑ pB
          s-shape s′-shape source-comp target-comp compat
          all inner-coherence (weakIndexedTransport inner))
        (weak-one-step-matched-νcast-frame-preserves-type-coherenceᵀ
          mode seal★ s⊑ mode′ seal★′ s′⊑ pB
          s-shape s′-shape source-comp target-comp compat
          all inner-coherence)
  matched-νcast-frame
      mode seal★ s⊑ mode′ seal★′ s′⊑
      s-shape s′-shape source-comp target-comp compat
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (ν-blame-tailᵀ source↠)

  source-ν-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {N N₁′ : Term} {A B B′ C : Ty}
      {s : Coercion} {μ} {χ : StoreChange}
      {occ : occurs zero C ≡ true}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    {{safe : NonVar C}} →
    WfTy Δᴸ A →
    RevealConversion μ (suc Δᴸ)
      ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
      zero (⇑ᵗ A) s C (⇑ᵗ B) →
    q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ pB →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N} {N′ = N₁′} {A = `∀ C} {B = B′}
      {χ = χ} {ρ = ρ} (ν safe occ q) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = ν A N s} {N′ = N₁′}
      {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
  source-ν-frame {occ = occ} {q = q} {pB = pB}
      {{safe = safe}} hA s↑ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      with transportSourceNu (weakIndexedResult inner) safe occ q
  source-ν-frame hA s↑ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | source-nu-index safe′ occ′ q′ shape
      with lift-left-store-result
        (resultStore (weakIndexedResult inner))
  source-ν-frame hA s↑ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | source-nu-index safe′ occ′ q′ shape | ρ′ , liftρ
      with apply-reveal-under-ty-binders
        {χs = sourceChanges (weakIndexedResult inner)} s↑
  source-ν-frame {pB = pB} hA s↑ replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | source-nu-index safe′ occ′ q′ shape | ρ′ , liftρ
      | μ′ , source↑ =
    world-indexed-outcome-related framed-indexed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
    where
    inner-result = weakIndexedResult inner
    framed =
      weak-one-step-source-ν-frameᵀ hA s↑ pB replace inner
    framed-indexed =
      weak-indexed-result framed (relatedResults framed)
        (weak-one-step-source-ν-frame-preserves-transportᵀ
          hA s↑ pB replace inner (weakIndexedTransport inner))
        (weak-one-step-source-ν-frame-preserves-type-coherenceᵀ
          hA s↑ pB replace inner (weakIndexedTypeCoherence inner))
  source-ν-frame hA s↑ replace
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (ν-blame-tailᵀ source↠)

  source-νcast-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {N N₁′ : Term} {B B′ C : Ty}
      {s : Coercion} {μ} {χ : StoreChange}
      {s-shape : ImprecisionShape}
      {occ : occurs zero C ≡ true}
      {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
    {{safe : NonVar C}} →
    CastMode μ →
    SealModeStore★ (instᵈ μ)
      ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
    instᵈ μ ∣ suc Δᴸ
      ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)
      ⊢ s ∶ C ⊑ ⇑ᵗ B →
    CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
    s-shape ； ⌊ pB ⌋ ≋ ⌊ q ⌋ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N} {N′ = N₁′} {A = `∀ C} {B = B′}
      {χ = χ} {ρ = ρ} (ν safe occ q) →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = ν ★ N s} {N′ = N₁′}
      {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
  source-νcast-frame {occ = occ} {q = q} {pB = pB}
      {{safe = safe}}
      mode seal★ s⊑ s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      with transportSourceNu (weakIndexedResult inner) safe occ q
  source-νcast-frame mode seal★ s⊑ s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | source-nu-index safe′ occ′ q′ shape
      with lift-left-store-result
        (resultStore (weakIndexedResult inner))
  source-νcast-frame mode seal★ s⊑ s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | source-nu-index safe′ occ′ q′ shape | ρ′ , liftρ
      with apply-widen-inst-under-ty-binders
        {χs = sourceChanges (weakIndexedResult inner)}
        mode seal★ s⊑
  source-νcast-frame {pB = pB}
      mode seal★ s⊑ s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | source-nu-index safe′ occ′ q′ shape | ρ′ , liftρ
      | μ′ , mode′ , seal★′ , source⊑ =
    world-indexed-outcome-related framed-indexed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
    where
    framed =
      weak-one-step-source-νcast-frameᵀ
        mode seal★ s⊑ pB s-shape comp inner
    framed-indexed =
      weak-indexed-result framed (relatedResults framed)
        (weak-one-step-source-νcast-frame-preserves-transportᵀ
          mode seal★ s⊑ pB s-shape comp inner
          (weakIndexedTransport inner))
        (weak-one-step-source-νcast-frame-preserves-type-coherenceᵀ
          mode seal★ s⊑ pB s-shape comp inner
          (weakIndexedTypeCoherence inner))
  source-νcast-frame mode seal★ s⊑ s-shape comp
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame (ν-blame-tailᵀ source↠)

  target-ν-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {N N₁′ : Term} {A B B′ C′ : Ty}
      {s : Coercion} {μ} {χ : StoreChange}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
    WfTy Δᴿ A →
    RevealConversion μ (suc Δᴿ)
      ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStoreⁱ ρ))
      zero (⇑ᵗ A) s C′ (⇑ᵗ B′) →
    (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
    r [ zero ↦ ⇑ᵗ A ]ᴿ ⊑-target-lift-rightᵢ pB →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N} {N′ = N₁′} {A = B} {B = `∀ C′}
      {χ = χ} {ρ = ρ} q →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N}
      {N′ = ν (applyTy χ A) N₁′
        (applyCoercionUnderTyBinder χ s)}
      {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
  target-ν-frame {χ = χ} {pB = pB} hA s↑ r replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      with lift-right-store-result
        (resultStore (weakIndexedResult inner))
  target-ν-frame {χ = χ} hA s↑ r replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ
      with apply-reveal-under-ty-binders
        {χs = χ ∷ targetTailChanges (weakIndexedResult inner)} s↑
  target-ν-frame hA s↑ r replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ | μ′ , target↑
      with weak-result-target-all (weakIndexedResult inner)
  target-ν-frame {pB = pB} hA s↑ r replace
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ | μ′ , target↑ | q′ , inner-result =
    world-indexed-outcome-related framed-indexed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
    where
    base = weakIndexedResult inner
    base-coherence = weakIndexedTypeCoherence inner
    framed =
      weak-one-step-target-ν-frameᵀ
        hA s↑ pB r replace base base-coherence
    framed-indexed =
      weak-indexed-result framed (relatedResults framed)
        (weak-one-step-target-ν-frame-preserves-transportᵀ
          hA s↑ pB r replace base base-coherence
          (weakIndexedTransport inner))
        (weak-one-step-target-ν-frame-preserves-type-coherenceᵀ
          hA s↑ pB r replace base base-coherence)
  target-ν-frame hA s↑ r replace
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame source↠

  target-νcast-frame :
    ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {N N₁′ : Term} {B B′ C′ : Ty}
      {s : Coercion} {μ} {χ : StoreChange}
      {s-shape : ImprecisionShape}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ} →
    CastMode μ →
    SealModeStore★ (instᵈ μ)
      ((zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)) →
    instᵈ μ ∣ suc Δᴿ
      ∣ (zero , ★) ∷ ⟰ᵗ (rightStoreⁱ ρ)
      ⊢ s ∶ C′ ⊑ ⇑ᵗ B′ →
    (r : ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ suc Δᴿ) →
    CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
    ⌊ r ⌋ ； s-shape ≋ ⌊ pB ⌋ →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N} {N′ = N₁′} {A = B} {B = `∀ C′}
      {χ = χ} {ρ = ρ} q →
    WorldCoherentWeakOneStepIndexedOutcome
      {M = N}
      {N′ = ν ★ N₁′ (applyCoercionUnderTyBinder χ s)}
      {A = B} {B = B′} {χ = χ} {ρ = ρ} pB
  target-νcast-frame {pB = pB}
      mode seal★ s⊑ r s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      with lift-right-store-result
        (resultStore (weakIndexedResult inner))
  target-νcast-frame {χ = χ} mode seal★ s⊑ r s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ
      with apply-widen-inst-under-ty-binders
        {χs = χ ∷ targetTailChanges (weakIndexedResult inner)}
        mode seal★ s⊑
  target-νcast-frame mode seal★ s⊑ r s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ | μ′ , mode′ , seal★′ , target⊑
      with weak-result-target-all (weakIndexedResult inner)
  target-νcast-frame {pB = pB}
      mode seal★ s⊑ r s-shape comp
      (world-indexed-outcome-related
        inner lineage coherent exclusive unique)
      | ρ′ , liftρ | μ′ , mode′ , seal★′ , target⊑
      | q′ , inner-result =
    world-indexed-outcome-related framed-indexed
      (weak-step-store-lineage
        (lineageStore lineage)
        (lineageEmbedding lineage)
        (lineagePrefix lineage))
      coherent exclusive unique
    where
    base = weakIndexedResult inner
    base-coherence = weakIndexedTypeCoherence inner
    framed =
      weak-one-step-target-νcast-frameᵀ
        mode seal★ s⊑ pB r s-shape comp base base-coherence
    framed-indexed =
      weak-indexed-result framed (relatedResults framed)
        (weak-one-step-target-νcast-frame-preserves-transportᵀ
          mode seal★ s⊑ pB r s-shape comp
          base base-coherence (weakIndexedTransport inner))
        (weak-one-step-target-νcast-frame-preserves-type-coherenceᵀ
          mode seal★ s⊑ pB r s-shape comp base base-coherence)
  target-νcast-frame mode seal★ s⊑ r s-shape comp
      (world-indexed-outcome-source-blame source↠) =
    world-indexed-outcome-source-blame source↠
