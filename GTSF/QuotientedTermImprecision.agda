module QuotientedTermImprecision where

-- File Charter:
--   * Defines mutually recursive ordinary and quotiented Nu-term imprecision
--     judgments independent of the old judgment.
--   * Propagates ordinary imprecision recursively through every related term
--     form.
--   * Keeps quotient indices only across one paired narrowing cast and closes
--     them with a compatible paired widening.
--   * Leaves application and repeated function-cast scheduling to simulation
--     up to reduction instead of encoding finite cast spines in the relation.
--   * Paired reveal/conceal evidence uses store correspondence links, so
--     physical store order need not coincide across permuted allocations.
--   * Factors runtime-bullet instantiation from single-name reveal/conceal
--     conversions and paired conversion imprecision.
--   * Uses one proof-only prefix-extension rule for matched, one-sided, and
--     crossed allocation states.
--   * Relates the terminal result of target-only `inst` allocation through
--     composable embedded creation evidence with a canonical transported
--     imprecision index.
--   * Leaves adjacent-`∀` crossed-body transport admissible, avoiding
--     syntax-specific swap constructors in the term relation.
--   * Relates widening bodies exposed by crossed `inst∀` and `∀inst`
--     coercions in both exact, differently ordered seal-mode orientations.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import Coercions
open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-conversion-typing
  ; reveal-conversion-typing
  ; _∣_∣_⊢_∶_↑ˢ_
  ; _∣_∣_⊢_∶_↓ˢ_
  )
open import ImprecisionWf
open import ForallPermutation using
  ( _∣_⊢_⊑ᵖ_⊣_
  ; quotientᵖ
  ; ≈∀-refl
  )
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_; _；⌊_⌋≋ᵖ_；_)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_; _[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  ; narrow-mode-relax
  ; widen-mode-relax
  )
open import NuTerms using
  ( Closedᵐ
  ; Term
  ; Value
  ; No•
  ; renameᵗᵐ
  ; ⇑ᵗᵐ
  ; `_
  ; ƛ_
  ; _·_
  ; Λ_
  ; _•
  ; ν
  ; $
  ; _⊕[_]_
  ; _⟨_⟩
  ; blame
  )
open import QuotientImprecisionCompatibility using
  ( ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; SpineCastMode
  ; id-only↓
  ; gradual↓
  )
open import Primitives
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.Core.Properties.CastImprecision using
  ( ∀ᵢᶜ
  ; widening⇒⊑ᵢ
  ; ⊑-transʳ-castᵢ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( rename-assm²ᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-source-liftνᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-ext
  ; cast-gen
  ; cast-inst
  ; cast-tag-or-id
  ; forget
  ; _∣_∣_⊢_⦂_
  ; ⊢`
  ; ⊢ƛ
  ; ⊢·
  ; ⊢Λ
  ; ⊢ν↑
  ; ⊢ν⊑
  ; ⊢$
  ; ⊢⊕
  ; ⊢⟨⟩↑
  ; ⊢⟨⟩↓
  ; ⊢⟨⟩⊒
  ; ⊢⟨⟩⊑
  ; ⊢blame
  )
open import NuTermImprecision using
  ( StoreImp
  ; StoreImpEntry
  ; StoreCorresponds
  ; CtxImp
  ; ctx-imp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; leftCtxⁱ
  ; rightCtxⁱ
  ; LiftStoreⁱ
  ; LiftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftLeftCtxⁱ
  ; LiftRightStoreⁱ
  ; LiftRightCtxⁱ
  ; store-matched
  ; store-left
  ; store-right
  ; store-link
  ; right-id-only-compatible
  ; seal★-tag-or-id
  ; leftStoreⁱ-lift
  ; rightStoreⁱ-lift
  ; leftStoreⁱ-lift-left
  ; rightStoreⁱ-lift-left
  ; leftCtxⁱ-lift
  ; rightCtxⁱ-lift
  ; leftCtxⁱ-lift-left
  ; rightCtxⁱ-lift-left
  ; leftStoreⁱ-lift-right
  ; rightStoreⁱ-lift-right
  ; leftCtxⁱ-lift-right
  ; rightCtxⁱ-lift-right
  ; leftCtxⁱ-∋
  ; rightCtxⁱ-∋
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (EmbeddedTargetInstantiationCreation)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-typingᴱ
  ; embedded-creation-target-typingᴱ
  )
open import proof.Core.Properties.NuTermProperties using
  (closed-refined-typing-recontextualize; typing-closedᵐ)

variable
  Φ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  ρ : StoreImp Φ Δᴸ Δᴿ
  γ : CtxImp Φ Δᴸ Δᴿ

------------------------------------------------------------------------
-- Store-imprecision prefix extension
------------------------------------------------------------------------

data StoreImpPrefix {Φ Δᴸ Δᴿ} :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Φ Δᴸ Δᴿ → Set where
  prefix-reflⁱ : ∀ {ρ} → StoreImpPrefix ρ ρ

  prefix-∷ⁱ :
    ∀ {ρ₀ ρ⁺} {entry : StoreImpEntry Φ Δᴸ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    StoreImpPrefix ρ₀ (entry ∷ ρ⁺)

data QuotientWideningPair
    {Φ : ImpCtx} (Δᴸ Δᴿ : TyCtx) (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (u u′ : Coercion) → (D D′ A A′ : Ty) → Set₁ where
  quotient-id-widening :
    ∀ {u u′ D D′ A A′} →
    id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ ⊑ A′ →
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′

  quotient-cast-widening :
    ∀ {μ μ′ u u′ D D′ A A′} →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ ⊑ A′ →
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′

------------------------------------------------------------------------
-- Nu-term imprecision with quotiented hidden cast intermediates
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
infix 4 _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_

mutual
  data _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_ :
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) →
      StoreImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ →
      Term → Term → (A B : Ty) →
      Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

    blame⊑ᵀ : ∀ {M A B p}
      → Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ blame ⊑ M ⦂ A ⊑ B ∶ p

    x⊑xᵀ : ∀ {x A B p}
      → γ ∋ x ⦂ ctx-imp A B p
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ ` x ⊑ ` x ⦂ A ⊑ B ∶ p

    ƛ⊑ƛᵀ : ∀ {N N′ A A′ B B′ pA pB}
      → WfTy Δᴸ A
      → WfTy Δᴿ A′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ γ
          ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ ƛ N ⊑ ƛ N′ ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB

    ·⊑·ᵀ : ∀ {L L′ M M′ A A′ B B′ pA pB}
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ L ⊑ L′
          ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ L · M ⊑ L′ · M′ ⦂ B ⊑ B′ ∶ pB

    closeᵀ :
        ∀ {N N′ A A′ D D′ qD u u′ s s′}
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ qD
      → QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′
      → (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
      → widening ⊢ᶜ u ⦂ s
      → widening ⊢ᶜ u′ ⦂ s′
      → s ；⌊ pA ⌋≋ᵖ qD ； s′
      → ReductionClosedQuotientWideningCompatible
          Φ Δᴸ Δᴿ u u′ qD pA s s′
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ N ⟨ u ⟩ ⊑ N′ ⟨ u′ ⟩ ⦂ A ⊑ A′ ∶ pA

    Λ⊑Λᵀ : ∀ {ρ′ γ′ V V′ A B p}
      → LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′
      → LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
      → Value V
      → Value V′
      → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
          ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ Λ V ⊑ Λ V′ ⦂ `∀ A ⊑ `∀ B ∶ ∀ⁱ p

    Λ⊑ᵀ : ∀ {ρ′ γ′ V N′ A B p}
      → {{safe : NonVar A}}
      → (occ : occurs zero A ≡ true)
      → LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
      → LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
      → Value V
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
          ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ Λ V ⊑ N′ ⦂ `∀ A ⊑ B
          ∶ ν safe occ p

    target-instantiationᵀ :
      ∀ {Φ₀ Θᴸ Θᴿ}
        {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          (suc Θᴸ) (suc Θᴿ)}
        {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
        {W W′ : Term} {B C D : Ty} {s : Coercion}
        {μ : ModeEnv}
        {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ⊢ D ⊑ C ⊣ suc Θᴿ}
        {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
        {body-shape : ImprecisionShape}
        {Ψ : ImpCtx} {Δᴸ′ Δᴿ′ : TyCtx}
        {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ′}
        {γ′ : CtxImp Ψ Δᴸ′ Δᴿ′}
        {V V′ : Term} {c′ : Coercion} {A A′ : Ty}
        {p : Ψ ∣ Δᴸ′ ⊢ `∀ A ⊑ A′ ⊣ Δᴿ′} →
      EmbeddedTargetInstantiationCreation
        {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
        {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
        {W = W} {W′ = W′} {B = B} {C = C} {D = D}
        {s = s} {μ = μ} {r = r} {f = f}
        {body-shape = body-shape}
        (StoreImpPrefix ρ₀ ρ⁺)
        (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
          ⊢ᴺ W ⊑ W′ ⦂ D ⊑ C ∶ r)
        {Ψ = Ψ} {Δᴸ = Δᴸ′} {Δᴿ = Δᴿ′}
        ρ′ (Λ V) (V′ ⟨ c′ ⟩) (`∀ A) A′ p →
      Ψ ∣ Δᴸ′ ∣ Δᴿ′ ∣ ρ′ ∣ γ′
        ⊢ᴺ Λ V ⊑ V′ ⟨ c′ ⟩ ⦂ `∀ A ⊑ A′ ∶ p

    α⊑αᵀ : ∀ {ρ′ γ′ L L′ A B C D p}
      → Value L
      → No• L
      → Value L′
      → No• L′
      → (A⇑⊑B⇑ :
          ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ B ⊣ suc Δᴿ)
      → LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′
      → LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ L ⊑ L′ ⦂ `∀ C ⊑ `∀ D ∶ ∀ⁱ p
      → suc Δᴸ
          ∣ leftStoreⁱ
              (store-matched zero (⇑ᵗ A) zero (⇑ᵗ B)
                A⇑⊑B⇑ ∷ ρ′)
          ∣ leftCtxⁱ γ′ ⊢ (⇑ᵗᵐ L) • ⦂ C
      → suc Δᴿ
          ∣ rightStoreⁱ
              (store-matched zero (⇑ᵗ A) zero (⇑ᵗ B)
                A⇑⊑B⇑ ∷ ρ′)
          ∣ rightCtxⁱ γ′ ⊢ (⇑ᵗᵐ L′) • ⦂ D
        ------------------------------------------------------------
      → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ ∣ suc Δᴿ ∣
          store-matched zero (⇑ᵗ A) zero (⇑ᵗ B) A⇑⊑B⇑ ∷ ρ′
          ∣ γ′
          ⊢ᴺ (⇑ᵗᵐ L) • ⊑ (⇑ᵗᵐ L′) • ⦂ C ⊑ D ∶ p

    α⊑ᵀ :
        ∀ {ρ′ γ′ L N′ A B′ C p occ}
      → {{safe : NonVar C}}
      → Value L
      → No• L
      → (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A))
      → LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
      → LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ L ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ p
      → suc Δᴸ
          ∣ leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
          ∣ leftCtxⁱ γ′ ⊢ (⇑ᵗᵐ L) • ⦂ C
      → Δᴿ
          ∣ rightStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρ′)
          ∣ rightCtxⁱ γ′ ⊢ N′ ⦂ B′
        ------------------------------------------------------------
      → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣
          store-left zero (⇑ᵗ A) h⇑A ∷ ρ′ ∣ γ′
          ⊢ᴺ (⇑ᵗᵐ L) • ⊑ N′ ⦂ C ⊑ B′ ∶ p

    allocation-prefixᵀ : ∀ {ρ₀ M M′ A B p}
      → StoreImpPrefix ρ₀ ρ
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p
      → Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A
      → Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p

    ν⊑νᵀ :
        ∀ {ρ′ γ′ A A′ B B′ C C′ N N′ p q s s′ μ μ′}
      → WfTy Δᴸ A
      → WfTy Δᴿ A′
      → RevealConversion μ (suc Δᴸ)
          ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
          zero (⇑ᵗ A) s C (⇑ᵗ B)
      → RevealConversion μ′ (suc Δᴿ)
          ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
          zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′)
      → Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ
      → (A⇑⊑A′⇑ :
          ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
            ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ)
      → LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′
      → LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ N ⊑ N′
          ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ q
      → q
          [ zero ↦ ⇑ᵗ A
            ⊑⟨ A⇑⊑A′⇑ ⟩
            ⇑ᵗ A′ ↤ zero ]ᴾ
          ⊑-lift∀ᵢ p
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ ν A N s ⊑ ν A′ N′ s′ ⦂ B ⊑ B′ ∶ p

    ν⊑ᵀ : ∀ {ρ′ γ′ A B B′ C N N′ p q s μ occ}
      → {{safe : NonVar C}}
      → WfTy Δᴸ A
      → (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A))
      → RevealConversion μ (suc Δᴸ)
          ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
          zero (⇑ᵗ A) s C (⇑ᵗ B)
      → LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′
      → LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ N ⊑ N′ ⦂ `∀ C ⊑ B′ ∶ ν safe occ q
      → q [ zero ↦ ⇑ᵗ A ]ᴸ ⊑-source-liftνᵢ p
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ ν A N s ⊑ N′ ⦂ B ⊑ B′ ∶ p

    κ⊑κᵀ : ∀ {n}
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ $ (κℕ n) ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι

    ⊕⊑⊕ᵀ : ∀ {L L′ M M′}
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ L ⊑ L′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ L ⊕[ addℕ ] M ⊑ L′ ⊕[ addℕ ] M′
          ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι

    gen⊑groundᵀ : ∀ {V W A B H p c μ}
      → CastMode μ
      → SealModeStore★ μ (leftStoreⁱ ρ)
      → μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ gen A c ∶ A ⊒ `∀ B
      → Ground H
      → Value V
      → Value W
      → Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ W ⦂ H
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ V ⊑ W ⟨ H ! ⟩ ⦂ A ⊑ ★ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ H ⊣ Δᴿ)
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ V ⟨ gen A c ⟩ ⊑ W ⦂ `∀ B ⊑ H ∶ q

    cast⊒⊑ᵀ : ∀ {M M′ A B B′ p c μ s}
      → CastMode μ
      → SealModeStore★ μ (leftStoreⁱ ρ)
      → (c⊒ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B)
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      → narrowing ⊢ᶜ c ⦂ s
      → s ； ⌊ p ⌋ ≋ ⌊ q ⌋
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    cast⊑⊑ᵀ : ∀ {M M′ A B B′ p c μ s}
      → CastMode μ
      → (seal★ : SealModeStore★ μ (leftStoreⁱ ρ))
      → (c⊑ : μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B)
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      → widening ⊢ᶜ c ⦂ s
      → s ； ⌊ q ⌋ ≋ ⌊ p ⌋
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    ⊑cast⊒ᵀ : ∀ {M M′ A A′ B′ p c′ μ′ s}
      → CastMode μ′
      → SealModeStore★ μ′ (rightStoreⁱ ρ)
      → μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ)
      → narrowing ⊢ᶜ c′ ⦂ s
      → ⌊ q ⌋ ； s ≋ ⌊ p ⌋
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    ⊑cast⊑ᵀ : ∀ {M M′ A A′ B′ p c′ μ′ s}
      → CastMode μ′
      → (seal★′ : SealModeStore★ μ′ (rightStoreⁱ ρ))
      → (c′⊑ :
          μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′)
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ)
      → widening ⊢ᶜ c′ ⦂ s
      → ⌊ p ⌋ ； s ≋ ⌊ q ⌋
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    conv↑⊑ᵀ : ∀ {M M′ A B B′ p c μ α X}
      → RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      → p [ α ↦ X ]ᴸ q
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    conv↓⊑ᵀ : ∀ {M M′ A B B′ p c μ α X}
      → ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ)
      → q [ α ↦ X ]ᴸ p
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    ⊑conv↑ᵀ : ∀ {M M′ A A′ B′ p c′ μ′ β X′}
      → RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ)
      → p [ β ↦ X′ ]ᴿ q
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    ⊑conv↓ᵀ : ∀ {M M′ A A′ B′ p c′ μ′ β X′}
      → ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
          β X′ c′ A′ B′
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
      → (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ)
      → q [ β ↦ X′ ]ᴿ p
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    paired-revealᵀ :
      ∀ {M M′ A A′ B B′ p q c c′
          α β X X′ pX μ μ′} →
      StoreCorresponds ρ α X β X′ pX →
      RevealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
      p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

    paired-concealᵀ :
      ∀ {M M′ A A′ B B′ p q c c′
          α β X X′ pX μ μ′} →
      StoreCorresponds ρ α X β X′ pX →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρ) α X c A B →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ) β X′ c′ A′ B′ →
      q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

    paired-wideningᵀ :
      ∀ {M M′ A A′ B B′ p q c c′ μ μ′ s s′ r} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
      widening ⊢ᶜ c ⦂ s →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      widening ⊢ᶜ c′ ⦂ s′ →
      s ； ⌊ q ⌋ ≋ r →
      ⌊ p ⌋ ； s′ ≋ r →
      ReductionClosedPairedWideningCompatible
        Φ Δᴸ Δᴿ c c′ p q s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

  data _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_ :
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) →
      StoreImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ →
      Term → Term → (D D′ : Ty) →
      Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ → Set₁ where

    paired-downᵀ :
        ∀ {M M′ A A′ D D′ p d d′ s s′ q μ μ′}
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
      → SpineCastMode (leftStoreⁱ ρ) μ
      → μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ A ⊒ D
      → narrowing ⊢ᶜ d ⦂ s
      → SpineCastMode (rightStoreⁱ ρ) μ′
      → μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ A′ ⊒ D′
      → narrowing ⊢ᶜ d′ ⦂ s′
      → s ；⌊ p ⌋≋ᵖ q ； s′
        ------------------------------------------------------------
      → Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
          ⊢ᴺᵖ M ⟨ d ⟩ ⊑ M′ ⟨ d′ ⟩ ⦂ D ⊑ᵖ D′ ∶ q

seal★-gen-tag-or-id :
  ∀ {Σ} →
  SealModeStore★ (genᵈ tag-or-idᵈ) Σ
seal★-gen-tag-or-id zero ()
seal★-gen-tag-or-id (suc α) ()

private
  spine-source-cast-typing :
    ∀ {Δ Σ Γ M A B d μ} →
    SpineCastMode Σ μ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ A ⊒ B →
    Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
    Δ ∣ Σ ∣ Γ ⊢ M ⟨ d ⟩ ⦂ B
  spine-source-cast-typing id-only↓ d⊒ M⊢ =
    ⊢⟨⟩⊒ cast-tag-or-id seal★-tag-or-id
      (narrow-mode-relax id-only≤tag-or-idᵈ d⊒) M⊢
  spine-source-cast-typing (gradual↓ mode seal★) d⊒ M⊢ =
    ⊢⟨⟩⊒ mode seal★ d⊒ M⊢

  quotient-widening-source-typing :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {Γ N D D′ A A′ u u′} →
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    Δᴸ ∣ leftStoreⁱ ρ ∣ Γ ⊢ N ⦂ D →
    Δᴸ ∣ leftStoreⁱ ρ ∣ Γ ⊢ N ⟨ u ⟩ ⦂ A
  quotient-widening-source-typing
      (quotient-id-widening u⊑ u′⊑) N⊢ =
    ⊢⟨⟩⊑ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u⊑) N⊢
  quotient-widening-source-typing
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) N⊢ =
    ⊢⟨⟩⊑ mode seal★ u⊑ N⊢

  quotient-widening-target-typing :
    ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
      {Γ N′ D D′ A A′ u u′} →
    QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
    Δᴿ ∣ rightStoreⁱ ρ ∣ Γ ⊢ N′ ⦂ D′ →
    Δᴿ ∣ rightStoreⁱ ρ ∣ Γ ⊢ N′ ⟨ u′ ⟩ ⦂ A′
  quotient-widening-target-typing
      (quotient-id-widening u⊑ u′⊑) N′⊢ =
    ⊢⟨⟩⊑ cast-tag-or-id seal★-tag-or-id
      (widen-mode-relax id-only≤tag-or-idᵈ u′⊑) N′⊢
  quotient-widening-target-typing
      (quotient-cast-widening
        mode seal★ u⊑ mode′ seal★′ u′⊑) N′⊢ =
    ⊢⟨⟩⊑ mode′ seal★′ u′⊑ N′⊢

------------------------------------------------------------------------
-- Typing projections
------------------------------------------------------------------------

mutual
  nu-term-imprecision-source-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A

  nu-term-imprecision-target-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
    Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B

  quotiented-nu-term-imprecision-source-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ D

  quotiented-nu-term-imprecision-target-typing :
    ∀ {Φ Δᴸ Δᴿ ρ γ M M′ D D′}
      {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
      ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
    Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ D′

  nu-term-imprecision-source-typing (blame⊑ᵀ {p = p} M′⊢) =
    ⊢blame (⊑-src-wf p)
  nu-term-imprecision-source-typing (x⊑xᵀ x∈) =
    ⊢` (leftCtxⁱ-∋ x∈)
  nu-term-imprecision-source-typing (ƛ⊑ƛᵀ hA hA′ N⊑N′) =
    ⊢ƛ hA (nu-term-imprecision-source-typing N⊑N′)
  nu-term-imprecision-source-typing (·⊑·ᵀ L⊑L′ M⊑M′) =
    ⊢·
      (nu-term-imprecision-source-typing L⊑L′)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (closeᵀ M⊑M′ widening-pair
        p u-shape u′-shape square compatible) =
    quotient-widening-source-typing widening-pair
      (quotiented-nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (Λ⊑Λᵀ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (leftCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (leftStoreⁱ-lift liftρ)
          (nu-term-imprecision-source-typing V⊑V′)))
  nu-term-imprecision-source-typing
      (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′) =
    ⊢Λ vV
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (leftCtxⁱ-lift-left liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (leftStoreⁱ-lift-left liftρ)
          (nu-term-imprecision-source-typing V⊑N′)))
  nu-term-imprecision-source-typing
      (target-instantiationᵀ embedded) =
    closed-refined-typing-recontextualize
      (typing-closedᵐ
        (forget (embedded-creation-source-typingᴱ embedded)))
      (embedded-creation-source-typingᴱ embedded)
  nu-term-imprecision-source-typing
      (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
        L•⊢ L′•⊢) =
    L•⊢
  nu-term-imprecision-source-typing
      (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢) =
    L•⊢
  nu-term-imprecision-source-typing
      (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) =
    M⊢
  nu-term-imprecision-source-typing
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace) =
    ⊢ν↑ hA (nu-term-imprecision-source-typing N⊑N′)
      (reveal-conversion-typing s↑)
  nu-term-imprecision-source-typing
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) =
    ⊢ν↑ hA (nu-term-imprecision-source-typing N⊑N′)
      (reveal-conversion-typing s↑)
  nu-term-imprecision-source-typing κ⊑κᵀ =
    ⊢$ (κℕ _)
  nu-term-imprecision-source-typing (⊕⊑⊕ᵀ L⊑L′ M⊑M′) =
    ⊢⊕
      (nu-term-imprecision-source-typing L⊑L′)
      addℕ
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q) =
    ⊢⟨⟩⊒ mode seal★ c⊒
      (nu-term-imprecision-source-typing V⊑Wtag)
  nu-term-imprecision-source-typing
      (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊒ mode seal★ c⊒ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊑ mode seal★ c⊑ (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing
      (paired-revealᵀ x∈ c↑ c′↑ replace M⊑M′) =
    ⊢⟨⟩↑ (reveal-conversion-typing c↑)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (paired-concealᵀ x∈ c↓ c′↓ replace M⊑M′) =
    ⊢⟨⟩↓ (conceal-conversion-typing c↓)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left right compat M⊑M′) =
    ⊢⟨⟩⊑ mode seal★ c⊑
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing (conv↑⊑ᵀ c↑ M⊑M′ q replace) =
    ⊢⟨⟩↑ (reveal-conversion-typing c↑)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing (conv↓⊑ᵀ c↓ M⊑M′ q replace) =
    ⊢⟨⟩↓ (conceal-conversion-typing c↓)
      (nu-term-imprecision-source-typing M⊑M′)
  nu-term-imprecision-source-typing
      (⊑conv↑ᵀ c′↑ M⊑M′ q replace) =
    nu-term-imprecision-source-typing M⊑M′
  nu-term-imprecision-source-typing
      (⊑conv↓ᵀ c′↓ M⊑M′ q replace) =
    nu-term-imprecision-source-typing M⊑M′

  nu-term-imprecision-target-typing (blame⊑ᵀ M′⊢) =
    M′⊢
  nu-term-imprecision-target-typing (x⊑xᵀ x∈) =
    ⊢` (rightCtxⁱ-∋ x∈)
  nu-term-imprecision-target-typing (ƛ⊑ƛᵀ hA hA′ N⊑N′) =
    ⊢ƛ hA′ (nu-term-imprecision-target-typing N⊑N′)
  nu-term-imprecision-target-typing (·⊑·ᵀ L⊑L′ M⊑M′) =
    ⊢·
      (nu-term-imprecision-target-typing L⊑L′)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (closeᵀ M⊑M′ widening-pair
        p u-shape u′-shape square compatible) =
    quotient-widening-target-typing widening-pair
      (quotiented-nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (Λ⊑Λᵀ {ρ = ρ} {γ = γ} liftρ liftγ vV vV′ V⊑V′) =
    ⊢Λ vV′
      (subst
        (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
        (rightCtxⁱ-lift liftγ)
        (subst
          (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
          (rightStoreⁱ-lift liftρ)
          (nu-term-imprecision-target-typing V⊑V′)))
  nu-term-imprecision-target-typing
      (Λ⊑ᵀ occ liftρ liftγ vV V⊑N′) =
    subst
      (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
      (rightCtxⁱ-lift-left liftγ)
      (subst
        (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
        (rightStoreⁱ-lift-left liftρ)
        (nu-term-imprecision-target-typing V⊑N′))
  nu-term-imprecision-target-typing
      (target-instantiationᵀ embedded) =
    closed-refined-typing-recontextualize
      (typing-closedᵐ
        (forget (embedded-creation-target-typingᴱ embedded)))
      (embedded-creation-target-typingᴱ embedded)
  nu-term-imprecision-target-typing
      (α⊑αᵀ vL noL vL′ noL′ A⇑⊑B⇑ liftρ liftγ L⊑L′
        L•⊢ L′•⊢) =
    L′•⊢
  nu-term-imprecision-target-typing
      (α⊑ᵀ vL noL h⇑A liftρ liftγ L⊑N′ L•⊢ N′⊢) =
    N′⊢
  nu-term-imprecision-target-typing
      (allocation-prefixᵀ prefix M⊑M′ M⊢ M′⊢) =
    M′⊢
  nu-term-imprecision-target-typing
      (ν⊑νᵀ hA hA′ s↑ s′↑ A⊑A′ A⇑⊑A′⇑
        liftρ liftγ N⊑N′ replace) =
    ⊢ν↑ hA′ (nu-term-imprecision-target-typing N⊑N′)
      (reveal-conversion-typing s′↑)
  nu-term-imprecision-target-typing
      (ν⊑ᵀ hA h⇑A s↑ liftρ liftγ N⊑N′ replace) =
    nu-term-imprecision-target-typing N⊑N′
  nu-term-imprecision-target-typing κ⊑κᵀ =
    ⊢$ (κℕ _)
  nu-term-imprecision-target-typing (⊕⊑⊕ᵀ L⊑L′ M⊑M′) =
    ⊢⊕
      (nu-term-imprecision-target-typing L⊑L′)
      addℕ
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (gen⊑groundᵀ mode seal★ c⊒ gH vV vW W⊢ V⊑Wtag q) =
    W⊢
  nu-term-imprecision-target-typing
      (cast⊒⊑ᵀ mode seal★ c⊒ M⊑M′ q c-shape comp) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (cast⊑⊑ᵀ mode seal★ c⊑ M⊑M′ q c-shape comp) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (⊑cast⊒ᵀ mode′ seal★′ c′⊒ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊒ mode′ seal★′ c′⊒
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (⊑cast⊑ᵀ mode′ seal★′ c′⊑ M⊑M′ q c-shape comp) =
    ⊢⟨⟩⊑ mode′ seal★′ c′⊑
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (paired-revealᵀ x∈ c↑ c′↑ replace M⊑M′) =
    ⊢⟨⟩↑ (reveal-conversion-typing c′↑)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (paired-concealᵀ x∈ c↓ c′↓ replace M⊑M′) =
    ⊢⟨⟩↓ (conceal-conversion-typing c′↓)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (paired-wideningᵀ
        mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
        left right compat M⊑M′) =
    ⊢⟨⟩⊑ mode′ seal★′ c′⊑
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing (conv↑⊑ᵀ c↑ M⊑M′ q replace) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing (conv↓⊑ᵀ c↓ M⊑M′ q replace) =
    nu-term-imprecision-target-typing M⊑M′
  nu-term-imprecision-target-typing
      (⊑conv↑ᵀ c′↑ M⊑M′ q replace) =
    ⊢⟨⟩↑ (reveal-conversion-typing c′↑)
      (nu-term-imprecision-target-typing M⊑M′)
  nu-term-imprecision-target-typing
      (⊑conv↓ᵀ c′↓ M⊑M′ q replace) =
    ⊢⟨⟩↓ (conceal-conversion-typing c′↓)
      (nu-term-imprecision-target-typing M⊑M′)

  quotiented-nu-term-imprecision-source-typing
      (paired-downᵀ
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square) =
    spine-source-cast-typing mode d⊒
      (nu-term-imprecision-source-typing M⊑M′)

  quotiented-nu-term-imprecision-target-typing
      (paired-downᵀ
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square) =
    spine-source-cast-typing mode′ d′⊒
      (nu-term-imprecision-target-typing M⊑M′)

nu-term-imprecision-typing :
  ∀ {Φ Δᴸ Δᴿ ρ γ M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  (Δᴸ ∣ leftStoreⁱ ρ ∣ leftCtxⁱ γ ⊢ M ⦂ A) ×
  (Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B)
nu-term-imprecision-typing M⊑M′ =
  nu-term-imprecision-source-typing M⊑M′ ,
  nu-term-imprecision-target-typing M⊑M′
