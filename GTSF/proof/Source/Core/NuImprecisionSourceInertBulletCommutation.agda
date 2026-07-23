module proof.Source.Core.NuImprecisionSourceInertBulletCommutation where

-- File Charter:
--   * Owns source-only inert runtime-bullet commutation at indexed
--     universal catch-up boundaries.
--   * Exports the five `left-catchup-indexed-all-α-*ᵀ` lemmas that prepend a
--     source `β-∀•` or `β-gen•` step through reveal, conceal, narrowing, and
--     widening structure.
--   * Depends on focused allocation-transport, polymorphic-value,
--     catch-up-composition, and source-bullet owners while avoiding unfocused
--     simulation modules.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import Coercions using (`∀; extᵈ; gen; genᵈ)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ImprecisionWf using
  (NonVar; _ˣ⊑★; ⇑ᴸᵢ; ν; ∀ⁱ_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; leftStoreⁱ-lift-left
  ; store-left
  )
open import NuTerms using
  ( No•
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-ext
  ; cast-gen
  )
open import Types using (WfTy; `∀; ⇑ᵗ)
open import proof.Core.Properties.NarrowWidenProperties using
  ( allocate-all-narrowing
  ; allocate-all-widening
  ; allocate-gen-narrowing
  )
open import proof.Catchup.Core.NuImprecisionCatchupComposition using
  (left-catchup-indexed-all-prepend-keepᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (LeftCatchupIndexedAllResult)
open import proof.Source.Core.NuImprecisionSourceBulletBase using
  (left-allocated-bulletᵀ)
open import proof.Source.Core.NuImprecisionSourceLeftAllocationCastTransport using
  ( allocated-left-gen-seal★
  ; allocated-left-relationᵀ
  ; allocated-left-seal★
  ; open-allocated-left-all-conceal
  ; open-allocated-left-all-reveal
  )
open import proof.Source.Core.NuImprecisionSourcePolymorphicValueBase using
  ( post-allocation-β-gen•-bare
  ; post-allocation-β-∀•-bare
  )
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-No•)

left-catchup-indexed-all-α-∀-revealᵀ :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν A C C′ c V V′ occ r q}
    {{safe : NonVar A}}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν _ occ r →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ (`∀ C)) →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-revealᵀ
    {V = V} {q = q}
    vV noV hAν liftρ V⊑V′ c↑ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  post-relation =
    conv↑⊑ᵀ (open-allocated-left-all-reveal liftρ c↑)
      bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-∀-concealᵀ :
  ∀ {Φ Δᴸ Δᴿ μ α X Aν A C C′ c V V′ occ r q}
    {{safe : NonVar A}}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν _ occ r →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X
    (`∀ c) (`∀ A) (`∀ (`∀ C)) →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-concealᵀ
    {V = V} {q = q}
    vV noV hAν liftρ V⊑V′ c↓ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  post-relation =
    conv↓⊑ᵀ (open-allocated-left-all-conceal liftρ c↓)
      bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-∀-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ occ r q}
    {{safe : NonVar A}}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊒ `∀ (`∀ C) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν _ occ r →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-narrowingᵀ
    {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {q = q} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ c∀⊒ V⊑V′ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  body-narrowing :
    extᵈ μ ∣ suc Δᴸ ∣
      (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
      ⊢ c ∶ A ⊒ `∀ C
  body-narrowing =
    subst
      (λ Σ → extᵈ μ ∣ suc Δᴸ ∣ Σ
        ⊢ c ∶ A ⊒ `∀ C)
      (cong ((zero , ⇑ᵗ Aν) ∷_)
        (sym (leftStoreⁱ-lift-left liftρ)))
      (allocate-all-narrowing c∀⊒)

  post-relation =
    cast⊒⊑ᵀ (cast-ext mode)
      (allocated-left-seal★ liftρ seal★)
      body-narrowing bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-∀-wideningᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ occ r q}
    {{safe : NonVar A}}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ `∀ c ∶ `∀ A ⊑ `∀ (`∀ C) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ `∀ A ⊑ `∀ C′ ∶ ν _ occ r →
  LeftCatchupIndexedAllResult
    {N = ((⇑ᵗᵐ V) •) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ `∀ c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-∀-wideningᵀ
    {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {q = q} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ c∀⊑ V⊑V′ catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-∀•-bare vV) post-relation catchup
  where
  bullet-relation =
    left-allocated-bulletᵀ vV noV hAν liftρ V⊑V′

  body-widening :
    extᵈ μ ∣ suc Δᴸ ∣
      (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
      ⊢ c ∶ A ⊑ `∀ C
  body-widening =
    subst
      (λ Σ → extᵈ μ ∣ suc Δᴸ ∣ Σ
        ⊢ c ∶ A ⊑ `∀ C)
      (cong ((zero , ⇑ᵗ Aν) ∷_)
        (sym (leftStoreⁱ-lift-left liftρ)))
      (allocate-all-widening c∀⊑)

  post-relation =
    cast⊑⊑ᵀ (cast-ext mode)
      (allocated-left-seal★ liftρ seal★)
      body-widening bullet-relation (∀ⁱ q)

left-catchup-indexed-all-α-gen-narrowingᵀ :
  ∀ {Φ Δᴸ Δᴿ μ Aν A C C′ c V V′ p q}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ} →
  Value V →
  No• V →
  (hAν : WfTy (suc Δᴸ) (⇑ᵗ Aν)) →
  (mode : CastMode μ) →
  (seal★ : SealModeStore★ μ (leftStoreⁱ ρ)) →
  (liftρ : LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ gen A c ∶ A ⊒ `∀ (`∀ C) →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ []
    ⊢ᴺ ⇑ᵗᵐ V ⊑ V′ ⦂ ⇑ᵗ A ⊑ `∀ C′ ∶ p →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ V) ⟨ c ⟩} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q →
  LeftCatchupIndexedAllResult
    {N = (⇑ᵗᵐ (V ⟨ gen A c ⟩)) •} {V′ = V′}
    {ρ = store-left zero (⇑ᵗ Aν) hAν ∷ ρ′} q
left-catchup-indexed-all-α-gen-narrowingᵀ
    {Δᴸ = Δᴸ} {μ = μ} {Aν = Aν} {A = A} {C = C}
    {c = c} {V = V} {q = q} {ρ′ = ρ′}
    vV noV hAν mode seal★ liftρ cgen⊒ shifted-body catchup =
  left-catchup-indexed-all-prepend-keepᵀ
    (post-allocation-β-gen•-bare vV) post-relation catchup
  where
  body-narrowing :
    genᵈ μ ∣ suc Δᴸ ∣
      (zero , ⇑ᵗ Aν) ∷ leftStoreⁱ ρ′
      ⊢ c ∶ ⇑ᵗ A ⊒ `∀ C
  body-narrowing =
    subst
      (λ Σ → genᵈ μ ∣ suc Δᴸ ∣ Σ
        ⊢ c ∶ ⇑ᵗ A ⊒ `∀ C)
      (cong ((zero , ⇑ᵗ Aν) ∷_)
        (sym (leftStoreⁱ-lift-left liftρ)))
      (allocate-gen-narrowing cgen⊒)

  body-relation =
    allocated-left-relationᵀ hAν liftρ
      (renameᵗᵐ-preserves-No• suc noV) shifted-body

  post-relation =
    cast⊒⊑ᵀ (cast-gen mode)
      (allocated-left-gen-seal★ liftρ seal★)
      body-narrowing body-relation (∀ⁱ q)
