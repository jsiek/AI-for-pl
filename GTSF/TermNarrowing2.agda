module TermNarrowing2 where

-- File Charter:
--   * Experimental replacement term-narrowing relation for the
--     StoreNarrowing/NarrowingEquiv design.
--   * The relation is indexed by a `StoreNarrowing` proof, not a
--     `SealCorr`; its coercion indices are ordinary narrowings homed in
--     the left store.
--   * Cast rules carry explicit composition side conditions using the
--     `NarrowingEquiv` relation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax; ∃-syntax)

open import Types
open import Coercions
open import NarrowWiden using (cross; dualⁿ; dualʷ; _∣_∣_⊢_∶_⊒_)
  renaming (_↦_ to _↦ⁿʷ_)
open import NarrowWidenComposition using (_⊢_⨟ⁿ_)
open import Primitives
open import NuTerms
open import StoreNarrowing
open import NarrowingEquiv
open import TermNarrowingSeparated using
  ( CtxCorrEntry
  ; ctx-entry
  ; CtxCorr
  ; leftCtx
  ; rightCtx
  ; ⇑ᵍᶜ
  )
open import proof.CoercionProperties using
  ( dualActionOk-normal
  ; dualStoreAt-normal
  )
open import proof.NarrowWidenProperties using (dualʷ-flips-typingᵐ)

------------------------------------------------------------------------
-- Coercion helpers
------------------------------------------------------------------------

dualₙ :
  ∀ {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Coercion
dualₙ (_ , cⁿ) = proj₁ (dualⁿ normalᵃ cⁿ)

------------------------------------------------------------------------
-- Function-coercion projections
------------------------------------------------------------------------

fun-narrow-domain-dual :
  ∀ {μ Δ Σ p q A A′ B B′} →
  μ ∣ Δ ∣ Σ ⊢ p ↦ q ∶ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  Coercion
fun-narrow-domain-dual (cast-fun p⊢ q⊢ , cross (pʷ ↦ⁿʷ qⁿ)) =
  proj₁ (dualʷ normalᵃ pʷ)

fun-narrow-domain-dual-typing :
  ∀ {μ ΔL ΔR σ p q A A′ B B′} →
  StoreNarrowing ΔL ΔR σ →
  (p↦q⊒ : μ ∣ ΔL ∣ leftStore σ ⊢ p ↦ q
             ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
  μ ∣ ΔL ∣ leftStore σ ⊢ fun-narrow-domain-dual p↦q⊒ ∶ A ⊒ A′
fun-narrow-domain-dual-typing {μ = μ} σⁿ
    (cast-fun p⊢ q⊢ , cross (pʷ ↦ⁿʷ qⁿ)) =
  dualʷ-flips-typingᵐ
    {μ = μ}
    {η = normalᵃ}
    {ν = μ}
    dualActionOk-normal
    dualStoreAt-normal
    (leftStore-wf σⁿ)
    (p⊢ , pʷ)

fun-narrow-codomain :
  ∀ {μ Δ Σ p q A A′ B B′} →
  μ ∣ Δ ∣ Σ ⊢ p ↦ q ∶ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  μ ∣ Δ ∣ Σ ⊢ q ∶ B ⊒ B′
fun-narrow-codomain (cast-fun p⊢ q⊢ , cross (pʷ ↦ⁿʷ qⁿ)) =
  q⊢ , qⁿ

------------------------------------------------------------------------
-- Right-only term-context shift
------------------------------------------------------------------------

shiftRightCtxNarrowingEntry : CtxCorrEntry → CtxCorrEntry
shiftRightCtxNarrowingEntry (ctx-entry A B p) =
  ctx-entry A (⇑ᵗ B) p

⇑ʳᵍⁿ : CtxCorr → CtxCorr
⇑ʳᵍⁿ = map shiftRightCtxNarrowingEntry

------------------------------------------------------------------------
-- Term narrowing
------------------------------------------------------------------------

infix 4 _∣_⊢_⊒_∶_⦂_⊒_

data _∣_⊢_⊒_∶_⦂_⊒_
    : ∀ {ΔL ΔR σ} →
      StoreNarrowing ΔL ΔR σ → CtxCorr →
      Term → Term → Coercion → Ty → Ty → Set₁ where

  ⊒blameᵗ : ∀ {ΔL ΔR σ γ M p A B μ}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → ΔL ∣ leftStore σ ∣ leftCtx γ ⊢ M ⦂ A
    → μ ∣ ΔL ∣ leftStore σ ⊢ p ∶ A ⊒ B
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ M ⊒ blame ∶ p ⦂ A ⊒ B

  x⊒xᵗ : ∀ {ΔL ΔR σ γ x p A B}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ p ∶ A ⊒ B
    → γ ∋ x ⦂ ctx-entry A B p
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ ` x ⊒ ` x ∶ p ⦂ A ⊒ B

  ƛ⊒ƛᵗ : ∀ {ΔL ΔR σ γ N N′ p q A A′ B B′}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → (p↦q⊒ : tag-or-idᵈ ∣ ΔL ∣ leftStore σ
                 ⊢ p ↦ q ∶ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → σⁿ ∣ ctx-entry A A′ (fun-narrow-domain-dual p↦q⊒) ∷ γ
        ⊢ N ⊒ N′ ∶ q ⦂ B ⊒ B′
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ ƛ N ⊒ ƛ N′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ A′ ⇒ B′

  ·⊒·ᵗ : ∀ {ΔL ΔR σ γ L L′ M M′ p q A A′ B B′}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → (p↦q⊒ : tag-or-idᵈ ∣ ΔL ∣ leftStore σ
                 ⊢ p ↦ q ∶ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → σⁿ ∣ γ ⊢ L ⊒ L′ ∶ p ↦ q ⦂ A ⇒ B ⊒ A′ ⇒ B′
    → σⁿ ∣ γ ⊢ M ⊒ M′ ∶ fun-narrow-domain-dual p↦q⊒ ⦂ A ⊒ A′
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ L · M ⊒ L′ · M′ ∶ q ⦂ B ⊒ B′

  Λ⊒Λᵗ : ∀ {ΔL ΔR σ γ V V′ p A B}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → {σ⇑ⁿ : StoreNarrowing (suc ΔL) (suc ΔR) (⇑ˢ σ)}
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ `∀ p ∶ `∀ A ⊒ `∀ B
    → Value V
    → Value V′
    → σ⇑ⁿ ∣ ⇑ᵍᶜ γ ⊢ V ⊒ V′ ∶ p ⦂ A ⊒ B
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ Λ V ⊒ Λ V′ ∶ `∀ p ⦂ `∀ A ⊒ `∀ B

  ⊒Λᵗ : ∀ {ΔL ΔR σ γ N V′ p A B}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → {σʳⁿ : StoreNarrowing ΔL (suc ΔR)
               ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ʳˢ σ)}
    → ΔL ∣ leftStore σ ∣ leftCtx γ ⊢ N ⦂ A
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ gen A p ∶ A ⊒ `∀ B
    → Value V′
    → σʳⁿ ∣ ⇑ʳᵍⁿ γ ⊢ N ⊒ V′ ∶ p ⦂ A ⊒ B
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ N ⊒ Λ V′ ∶ gen A p ⦂ A ⊒ `∀ B

  ⊒⟨ν⟩ᵗ : ∀ {ΔL ΔR σ γ N V′ p s A B η}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → {σʳⁿ : StoreNarrowing ΔL (suc ΔR)
               ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ʳˢ σ)}
    → ΔL ∣ leftStore σ ∣ leftCtx γ ⊢ N ⦂ A
    → η ∣ suc ΔR ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStore σ)
        ⊢ gen A s ∶ ⇑ᵗ A ⊒ `∀ B
    → ΔR ∣ rightStore σ ∣ rightCtx γ ⊢ V′ ⦂ ⇑ᵗ A
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ gen A p ∶ A ⊒ `∀ B
    → Inert s
    → σʳⁿ ∣ ⇑ʳᵍⁿ γ ⊢ N ⊒ V′ ⟨ s ⟩ ∶ p ⦂ A ⊒ B
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ N ⊒ V′ ⟨ gen A s ⟩ ∶ gen A p ⦂ A ⊒ `∀ B

  α⊒αᵗ : ∀ {ΔL ΔR σ γ L L′ p q A B C D}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → {σqⁿ : StoreNarrowing (suc ΔL) (suc ΔR)
                ((zero ꞉ ⇑ᶜ q ꞉ zero ⦂ ⇑ᵗ B) ∷ ⇑ˢ σ)}
    → Value L
    → No• L
    → Value L′
    → No• L′
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ q ∶ A ⊒ B
    → tag-or-idᵈ ∣ suc ΔL
        ∣ leftStore ((zero ꞉ ⇑ᶜ q ꞉ zero ⦂ ⇑ᵗ B) ∷ ⇑ˢ σ)
        ⊢ p ∶ C ⊒ D
    → σⁿ ∣ γ ⊢ L ⊒ L′ ∶ `∀ p ⦂ `∀ C ⊒ `∀ D
      ------------------------------------------------------
    → σqⁿ ∣ γ ⊢ (⇑ᵗᵐ L) • ⊒ (⇑ᵗᵐ L′) • ∶ p ⦂ C ⊒ D

  ⊒αᵗ : ∀ {ΔL ΔR σ γ L L′ p A B D}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → {σʳⁿ : StoreNarrowing ΔL (suc ΔR)
               ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ʳˢ σ)}
    → Value L′
    → No• L′
    → tag-or-idᵈ ∣ ΔL
        ∣ leftStore ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ʳˢ σ)
        ⊢ p ∶ B ⊒ D
    → σⁿ ∣ γ ⊢ L ⊒ L′ ∶ gen B p ⦂ B ⊒ `∀ D
      ------------------------------------------------------
    → σʳⁿ ∣ γ ⊢ L ⊒ (⇑ᵗᵐ L′) • ∶ p ⦂ B ⊒ D

  ν⊒νᵗ : ∀ {ΔL ΔR σ γ A A′ B B′ C C′ N N′ p q sₗ sᵣ ηL ηR}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → {σqⁿ : StoreNarrowing (suc ΔL) (suc ΔR)
                ((zero ꞉ ⇑ᶜ q ꞉ zero ⦂ ⇑ᵗ A′) ∷ ⇑ˢ σ)}
    → WfTy ΔL A
    → WfTy ΔR A′
    → ΔL ∣ leftStore σ ∣ leftCtx γ ⊢ N ⦂ `∀ C
    → ΔR ∣ rightStore σ ∣ rightCtx γ ⊢ N′ ⦂ `∀ C′
    → ηL ∣ suc ΔL ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStore σ)
        ⊢ sₗ ∶ C ⊒ ⇑ᵗ B
    → ηR ∣ suc ΔR ∣ (zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStore σ)
        ⊢ sᵣ ∶ C′ ⊒ ⇑ᵗ B′
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ p ∶ B ⊒ B′
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ q ∶ A ⊒ A′
    → σqⁿ ∣ ⇑ᵍᶜ γ ⊢ N ⊒ N′ ∶ ⇑ᶜ p ⦂ ⇑ᵗ B ⊒ ⇑ᵗ B′
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ ν A N sₗ ⊒ ν A′ N′ sᵣ ∶ p ⦂ B ⊒ B′

  ⊒νᵗ : ∀ {ΔL ΔR σ γ A B B′ C′ N N′ p s η}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → {σʳⁿ : StoreNarrowing ΔL (suc ΔR)
               ((zero ꞉= ⇑ᵗ A ⊒) ∷ ⇑ʳˢ σ)}
    → ΔL ∣ leftStore σ ∣ leftCtx γ ⊢ N ⦂ B
    → WfTy ΔR A
    → ΔR ∣ rightStore σ ∣ rightCtx γ ⊢ N′ ⦂ `∀ C′
    → η ∣ suc ΔR ∣ (zero , ⇑ᵗ A) ∷ ⟰ᵗ (rightStore σ)
        ⊢ s ∶ C′ ⊒ ⇑ᵗ B′
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ p ∶ B ⊒ B′
    → σʳⁿ ∣ γ ⊢ N ⊒ N′ ∶ p ⦂ B ⊒ ⇑ᵗ B′
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ N ⊒ ν A N′ s ∶ p ⦂ B ⊒ B′

  κ⊒κᵗ : ∀ {ΔL ΔR σ γ} κ
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ
        ⊢ id (constTy κ) ∶ constTy κ ⊒ constTy κ
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ $ κ ⊒ $ κ ∶ id (constTy κ)
        ⦂ constTy κ ⊒ constTy κ

  ⊕⊒⊕ᵗ : ∀ {ΔL ΔR σ γ M M′ N N′}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ
        ⊢ id (‵ `ℕ) ∶ ‵ `ℕ ⊒ ‵ `ℕ
    → σⁿ ∣ γ ⊢ M ⊒ M′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    → σⁿ ∣ γ ⊢ N ⊒ N′ ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ M ⊕[ addℕ ] N ⊒ M′ ⊕[ addℕ ] N′
        ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ

  cast+⊒ᵗ : ∀ {ΔL ΔR σ γ M M′ q r s A B′ C μL}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ r ∶ A ⊒ B′
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ q ∶ C ⊒ B′
    → (s⊒ˡ : μL ∣ ΔL ∣ leftStore σ ⊢ s ∶ A ⊒ C)
    → (q⊒ˡ : μL ∣ ΔL ∣ leftStore σ ⊢ q ∶ C ⊒ B′)
    → proj₁ (leftStore-det σⁿ ⊢ s⊒ˡ ⨟ⁿ q⊒ˡ) ≡ r
    → σⁿ ∣ γ ⊢ M ⊒ M′ ∶ q ⦂ C ⊒ B′
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ M ⟨ dualₙ s⊒ˡ ⟩ ⊒ M′ ∶ r ⦂ A ⊒ B′

  cast-⊒ᵗ : ∀ {ΔL ΔR σ γ M M′ q r s A B′ C μL}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ q ∶ C ⊒ B′
    → (s⊒ˡ : μL ∣ ΔL ∣ leftStore σ ⊢ s ∶ A ⊒ C)
    → (q⊒ˡ : μL ∣ ΔL ∣ leftStore σ ⊢ q ∶ C ⊒ B′)
    → proj₁ (leftStore-det σⁿ ⊢ s⊒ˡ ⨟ⁿ q⊒ˡ) ≡ r
    → σⁿ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ B′
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ M ⟨ s ⟩ ⊒ M′ ∶ q ⦂ C ⊒ B′

  ⊒cast+ᵗ : ∀ {ΔL ΔR σ γ M M′ p pʳ r t A A′ Bˡ B′ Cˡ C′ μR}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → (p≈pʳ : tag-or-idᵈ ∣ μR ∣ ΔL ∣ ΔR ∣ σ
        ⊢ p ≈ pʳ ∶ A ⊒ Cˡ ⦂ A′ ⊒ C′)
    → (t⊒ʳ : μR ∣ ΔR ∣ rightStore σ ⊢ t ∶ C′ ⊒ B′)
    → tag-or-idᵈ ∣ μR ∣ ΔL ∣ ΔR ∣ σ
        ⊢ r ≈ proj₁
            (rightStore-det σⁿ ⊢ ≈-right-typing p≈pʳ ⨟ⁿ t⊒ʳ)
        ∶ A ⊒ Bˡ ⦂ A′ ⊒ B′
    → σⁿ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ B′
      ------------------------------------------------------
    → σⁿ ∣ γ
        ⊢ M ⊒ M′ ⟨ dualₙ t⊒ʳ ⟩ ∶ p ⦂ A ⊒ C′

  ⊒cast-ᵗ : ∀ {ΔL ΔR σ γ M M′ p pʳ r t A A′ Bˡ B′ Cˡ C′ μR}
    → {σⁿ : StoreNarrowing ΔL ΔR σ}
    → (p≈pʳ : tag-or-idᵈ ∣ μR ∣ ΔL ∣ ΔR ∣ σ
        ⊢ p ≈ pʳ ∶ A ⊒ Cˡ ⦂ A′ ⊒ C′)
    → (t⊒ʳ : μR ∣ ΔR ∣ rightStore σ ⊢ t ∶ C′ ⊒ B′)
    → tag-or-idᵈ ∣ μR ∣ ΔL ∣ ΔR ∣ σ
        ⊢ r ≈ proj₁
            (rightStore-det σⁿ ⊢ ≈-right-typing p≈pʳ ⨟ⁿ t⊒ʳ)
        ∶ A ⊒ Bˡ ⦂ A′ ⊒ B′
    → σⁿ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ C′
      ------------------------------------------------------
    → σⁿ ∣ γ ⊢ M ⊒ M′ ⟨ t ⟩ ∶ r ⦂ A ⊒ B′
