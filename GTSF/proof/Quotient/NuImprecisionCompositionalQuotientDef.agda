module proof.Quotient.NuImprecisionCompositionalQuotientDef where

-- File Charter:
--   * Prototypes a compositional presentation of quotiented term imprecision.
--   * Represents any finite paired narrowing cast spine with one constructor.
--   * Closes quotient-related terms under application in both positions.
--   * Separates cast-spine derivations from application derivations so
--     terminal and value arguments can exclude the latter by inversion.
--   * Retains quotient-closing widenings and their hereditary compatibility.
--   * Does not replace the live term-imprecision relation or prove simulation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)

open import CastImprecisionShape using
  ( narrowing
  ; widening
  ; _⊢ᶜ_⦂_
  )
open import Coercions using (Coercion; ModeEnv; id-onlyᵈ)
open import ForallPermutation using
  ( _∣_⊢_⊑ᵖ_⊣_
  ; quotientᵖ
  ; ≈∀-refl
  ; ⊑ᵖ-arrow-components
  )
open import Imprecision using (ImpCtx)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; _⊢_≈∀ˢ_
  ; source-perm-refl
  ; _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( StoreImp
  ; CtxImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; Value; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  )
open import Types using (Ty; TyCtx; Store; _⇒_)

------------------------------------------------------------------------
-- Finite narrowing cast spines
------------------------------------------------------------------------

data SpineCastMode (Σ : Store) : ModeEnv → Set where
  id-only↓ :
    SpineCastMode Σ id-onlyᵈ

  gradual↓ :
    ∀ {μ} →
    CastMode μ →
    SealModeStore★ μ Σ →
    SpineCastMode Σ μ


data NarrowingSpine (Δ : TyCtx) (Σ : Store) :
    Term → Ty → Term → Ty → ImprecisionShape → Set₁ where

  single↓ :
    ∀ {M A B d μ s} →
    SpineCastMode Σ μ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ A ⊒ B →
    narrowing ⊢ᶜ d ⦂ s →
    NarrowingSpine Δ Σ M A (M ⟨ d ⟩) B s

  extend↓ :
    ∀ {M N A B C d μ s t u} →
    NarrowingSpine Δ Σ M A N B s →
    SpineCastMode Σ μ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ B ⊒ C →
    narrowing ⊢ᶜ d ⦂ t →
    t ； s ≋ u →
    NarrowingSpine Δ Σ M A (N ⟨ d ⟩) C u


narrowing-spine-length :
  ∀ {Δ Σ M N A B s} →
  NarrowingSpine Δ Σ M A N B s →
  ℕ
narrowing-spine-length (single↓ mode d⊢ d-shape) = suc zero
narrowing-spine-length
    (extend↓ spine mode d⊢ d-shape comp) =
  suc (narrowing-spine-length spine)

------------------------------------------------------------------------
-- Graded quotient relation
------------------------------------------------------------------------

data QuotientForm : Set where
  cast-spine application : QuotientForm

------------------------------------------------------------------------
-- Hereditary widening compatibility through quotient representatives
------------------------------------------------------------------------

data QuotientWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) :
    (u u′ : Coercion) → {D D′ A A′ : Ty} →
    (q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
    ImprecisionShape → ImprecisionShape → Set where

  compatible-through-representatives :
    ∀ {u u′ D D′ A A′ C C′ r p s s′ t t′}
      {src : D ForallPermutation.≈∀ C}
      {tgt : C′ ForallPermutation.≈∀ D′} →
    src ⊢ s ≈∀ˢ t →
    tgt ⊢ t′ ≈∀ˢ s′ →
    PairedWideningCompatible Φ Δᴸ Δᴿ u u′
      {C} {C′} {A} {A′} r p t t′ →
    QuotientWideningCompatible Φ Δᴸ Δᴿ u u′
      (quotientᵖ src r tgt) p s s′


exact-widening-compatible :
  ∀ {Φ Δᴸ Δᴿ u u′ D D′ A A′ r p s s′} →
  PairedWideningCompatible Φ Δᴸ Δᴿ u u′
    {D} {D′} {A} {A′} r p s s′ →
  QuotientWideningCompatible Φ Δᴸ Δᴿ u u′
    (quotientᵖ ≈∀-refl r ≈∀-refl) p s s′
exact-widening-compatible compatible =
  compatible-through-representatives
    {src = ≈∀-refl} {tgt = ≈∀-refl}
    source-perm-refl source-perm-refl compatible


infix 4 _∣_∣_∣_∣_⊢ᴺᶜ[_]_⊑_⦂_⊑ᵖ_∶_

data _∣_∣_∣_∣_⊢ᴺᶜ[_]_⊑_⦂_⊑ᵖ_∶_
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : StoreImp Φ Δᴸ Δᴿ) (γ : CtxImp Φ Δᴸ Δᴿ) :
    QuotientForm → Term → Term → (A B : Ty) →
    Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ → Set₁ where

  ordinaryᶜ :
    ∀ {M M′ A B p} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ[ cast-spine ] M ⊑ M′
      ⦂ A ⊑ᵖ B ∶ quotientᵖ ≈∀-refl p ≈∀-refl

  paired-spinesᶜ :
    ∀ {M M′ N N′ A A′ D D′ p s s′ q} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    NarrowingSpine Δᴸ (leftStoreⁱ ρ) M A N D s →
    NarrowingSpine Δᴿ (rightStoreⁱ ρ) M′ A′ N′ D′ s′ →
    s ；⌊ p ⌋≋ᵖ q ； s′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ[ cast-spine ] N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ q

  _·ᶜ[_]_ :
    ∀ {L L′ M M′ A A′ B B′ qF qA qB f g} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ[ f ] L ⊑ L′
      ⦂ A ⇒ B ⊑ᵖ A′ ⇒ B′ ∶ qF →
    ⊑ᵖ-arrow-components qF ≡ (qA , qB) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ[ g ] M ⊑ M′ ⦂ A ⊑ᵖ A′ ∶ qA →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ[ application ] L · M ⊑ L′ · M′
      ⦂ B ⊑ᵖ B′ ∶ qB

------------------------------------------------------------------------
-- Returning from the quotient while retaining widening compatibility
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴺᶜ_⊑_⦂_⊑_∶_

data _∣_∣_∣_∣_⊢ᴺᶜ_⊑_⦂_⊑_∶_
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : StoreImp Φ Δᴸ Δᴿ) (γ : CtxImp Φ Δᴸ Δᴿ) :
    Term → Term → (A B : Ty) →
    Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

  ordinary-leafᶜ :
    ∀ {M M′ A B p} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ M ⊑ M′ ⦂ A ⊑ B ∶ p

  closeᶜ :
    ∀ {N N′ D D′ A A′ q p u u′ s s′ f} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ[ f ] N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ q →
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    widening ⊢ᶜ u ⦂ s →
    widening ⊢ᶜ u′ ⦂ s′ →
    s ；⌊ p ⌋≋ᵖ q ； s′ →
    QuotientWideningCompatible Φ Δᴸ Δᴿ u u′ q p s s′ →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ N ⟨ u ⟩ ⊑ N′ ⟨ u′ ⟩ ⦂ A ⊑ A′ ∶ p

  paired-castᶜ :
    ∀ {M M′ A A′ B B′ p q c c′} →
    PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᶜ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

------------------------------------------------------------------------
-- The grade keeps application out of value-only inversion
------------------------------------------------------------------------

application-source-not-value :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B q} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᶜ[ application ] M ⊑ M′ ⦂ A ⊑ᵖ B ∶ q →
  Value M →
  ⊥
application-source-not-value
    (function ·ᶜ[ components ] argument) ()


application-target-not-value :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B q} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴺᶜ[ application ] M ⊑ M′ ⦂ A ⊑ᵖ B ∶ q →
  Value M′ →
  ⊥
application-target-not-value
    (function ·ᶜ[ components ] argument) ()
