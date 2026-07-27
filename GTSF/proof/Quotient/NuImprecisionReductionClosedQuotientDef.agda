module
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  where

-- File Charter:
--   * Defines the smaller quotient-imprecision prototype used to test
--     simulation up to reduction.
--   * Gives the ordinary fragment its own syntax-directed constructors; no
--     constructor embeds or converts from another term-imprecision judgment.
--   * Keeps quotient indices only across one paired narrowing cast and closes
--     them with compatible paired widenings.
--   * Includes the exact residual created by target-only instantiation.
--   * Defines pure-reduction closure for focused simulation experiments.
--   * Does not change or re-export the live term-imprecision relation.

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero; suc)

open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using
  (Coercion; Inert; ModeEnv; id-onlyᵈ; inst)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; _ˣ⊑★; ⇑ᵢ; ⇑ᴸᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_; NonVar; ∀ⁱ_; ν; _↦_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuReduction using
  (StoreChanges; keep; _—↠[_]_)
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; ctx-imp
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; renameᵗᵐ
  ; `_
  ; ƛ_
  ; _·_
  ; Λ_
  ; _⟨_⟩
  ; $
  ; _⊕[_]_
  ; blame
  )
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import Primitives using (Prim; κℕ)
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; WfTy
  ; ★
  ; wf★
  ; _⇒_
  ; `∀
  ; renameᵗ
  ; ⇑ᵗ
  ; occurs
  )
open import
  proof.Quotient.NuImprecisionQuotientBoundarySupport
  using
  ( SpineCastMode
  ; QuotientWideningCompatible
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  (TargetInstantiationCreation)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  ( rename-assm²ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.Core.Properties.TypeProperties
  using (TyRenameWf)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)


variable
  Φ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  ρ : StoreImp Φ Δᴸ Δᴿ
  γ : CtxImp Φ Δᴸ Δᴿ

------------------------------------------------------------------------
-- Store-neutral reduction sequences
------------------------------------------------------------------------

data AllKeep : StoreChanges → Set where
  []ᵏ : AllKeep []
  keep∷ᵏ_ : ∀ {χs} → AllKeep χs → AllKeep (keep ∷ χs)

data QuotientWideningPairᴿ
    {Φ : ImpCtx} (Δᴸ Δᴿ : TyCtx) (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (u u′ : Coercion) → (D D′ A A′ : Ty) → Set₁ where
  quotient-id-wideningᴿ :
    ∀ {u u′ D D′ A A′} →
    id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ ⊑ A′ →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′

  quotient-cast-wideningᴿ :
    ∀ {μ μ′ u u′ D D′ A A′} →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ u ∶ D ⊑ A →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ u′ ∶ D′ ⊑ A′ →
    QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′

------------------------------------------------------------------------
-- Smaller ordinary and quotient relations
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
infix 4 _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_

mutual
  data _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_ :
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) →
      StoreImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ →
      Term → Term → (A B : Ty) →
      Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

    blame⊑ᴿ :
      ∀ {M A B p} →
      Δᴿ ∣ rightStoreⁱ ρ ∣ rightCtxⁱ γ ⊢ M ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ blame ⊑ M ⦂ A ⊑ B ∶ p

    x⊑xᴿ :
      ∀ {x A B p} →
      γ Types.∋ x ⦂ ctx-imp A B p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ ` x ⊑ ` x ⦂ A ⊑ B ∶ p

    ƛ⊑ƛᴿ :
      ∀ {N N′ A A′ B B′ pA pB} →
      WfTy Δᴸ A →
      WfTy Δᴿ A′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ γ
        ⊢ᴿ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ ƛ N ⊑ ƛ N′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB

    _·ᴿ_ :
      ∀ {L L′ M M′ A A′ B B′ pA pB} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊑ L′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L · M ⊑ L′ · M′ ⦂ B ⊑ B′ ∶ pB

    Λ⊑Λᴿ :
      ∀ {ρ′ γ′ V V′ A B p} →
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
      LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ′ →
      Value V →
      Value V′ →
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴿ V ⊑ V′ ⦂ A ⊑ B ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ Λ V ⊑ Λ V′ ⦂ `∀ A ⊑ `∀ B ∶ ∀ⁱ p

    Λ⊑ᴿ :
      ∀ {ρ′ γ′ V N′ A B p} →
      {{safe : NonVar A}} →
      (occ : occurs zero A ≡ true) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ′ →
      Value V →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴿ V ⊑ N′ ⦂ A ⊑ B ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ Λ V ⊑ N′ ⦂ `∀ A ⊑ B ∶ ν safe occ p

    κ⊑κᴿ :
      ∀ {n} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ $ (κℕ n) ⊑ $ (κℕ n)
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι

    _⊕ᴿ[_]_ :
      ∀ {L L′ M M′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊑ L′
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι →
      (op : Prim) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊕[ op ] M ⊑ L′ ⊕[ op ] M′
        ⦂ Types.‵ Types.`ℕ ⊑ Types.‵ Types.`ℕ
        ∶ ImprecisionWf.idι

    cast⊒⊑ᴿ :
      ∀ {M M′ A B B′ p c μ s} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      narrowing ⊢ᶜ c ⦂ s →
      s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    cast⊑⊑ᴿ :
      ∀ {M M′ A B B′ p c μ s} →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
      widening ⊢ᶜ c ⦂ s →
      s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q

    ⊑cast⊒ᴿ :
      ∀ {M M′ A A′ B′ p c′ μ′ s} →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
      narrowing ⊢ᶜ c′ ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    ⊑cast⊑ᴿ :
      ∀ {M M′ A A′ B′ p c′ μ′ s} →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
      widening ⊢ᶜ c′ ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q

    target-instantiationᴿ :
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
        {body-shape : ImprecisionShape} →
      TargetInstantiationCreation
        {Φ = Φ₀} {Δᴸ = Θᴸ} {Δᴿ = Θᴿ}
        {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
        {W = W} {W′ = W′} {B = B} {C = C} {D = D}
        {s = s} {μ = μ} {r = r} {f = f}
        {body-shape = body-shape}
        (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
          ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r) →
      ⇑ᴿᵢ Φ₀
        ∣ Θᴸ ∣ suc Θᴿ
        ∣ store-right zero ★ wf★ ∷ ρᴿ⁺ ∣ []
        ⊢ᴿ Λ W ⊑ W′ ⟨ s ⟩
        ⦂ `∀ D ⊑ ⇑ᵗ B
        ∶ ⊑-target-lift-rightᵢ f

    rename-storeᴿ :
      ∀ {Φ₀ Ψ Θᴸ Θᴿ Δᴸ′ Δᴿ′}
        {ρ₀ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ′}
        {τ σ : Renameᵗ}
        {M M′ : Term} {A B : Ty}
        {p : Φ₀ ∣ Θᴸ ⊢ A ⊑ B ⊣ Θᴿ} →
      (assm :
        ∀ {a : ImpAssm} → a ∈ Φ₀ →
          rename-assm²ᵢ τ σ a ∈ Ψ) →
      (hτ : TyRenameWf Θᴸ Δᴸ′ τ) →
      (hσ : TyRenameWf Θᴿ Δᴿ′ σ) →
      RelStoreEmbeddingⁱ τ σ ρ₀ ρ′ →
      Φ₀ ∣ Θᴸ ∣ Θᴿ ∣ ρ₀ ∣ []
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      Δᴸ′ ∣ leftStoreⁱ ρ′ ∣ []
        ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A →
      Δᴿ′ ∣ rightStoreⁱ ρ′ ∣ []
        ⊢ renameᵗᵐ σ M′ ⦂ renameᵗ σ B →
      Ψ ∣ Δᴸ′ ∣ Δᴿ′ ∣ ρ′ ∣ []
        ⊢ᴿ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
        ⦂ renameᵗ τ A ⊑ renameᵗ σ B
        ∶ ⊑-renameᵗ²ᵢ assm hτ hσ p

    closeᴿ :
      ∀ {N N′ D D′ A A′ q p u u′ s s′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ q →
      QuotientWideningPairᴿ Δᴸ Δᴿ ρ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ s →
      widening ⊢ᶜ u′ ⦂ s′ →
      s ；⌊ p ⌋≋ᵖ q ； s′ →
      QuotientWideningCompatible Φ Δᴸ Δᴿ u u′ q p s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ N ⟨ u ⟩ ⊑ N′ ⟨ u′ ⟩ ⦂ A ⊑ A′ ∶ p

    paired-wideningᴿ :
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
      PairedWideningCompatible
        Φ Δᴸ Δᴿ c c′ p q s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

  data _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_ :
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx) →
      StoreImp Φ Δᴸ Δᴿ → CtxImp Φ Δᴸ Δᴿ →
      Term → Term → (D D′ : Ty) →
      Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ → Set₁ where

    paired-downᴿ :
      ∀ {M M′ A A′ D D′ p d d′ s s′ q μ μ′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      SpineCastMode (leftStoreⁱ ρ) μ →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ A ⊒ D →
      narrowing ⊢ᶜ d ⦂ s →
      SpineCastMode (rightStoreⁱ ρ) μ′ →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ A′ ⊒ D′ →
      narrowing ⊢ᶜ d′ ⦂ s′ →
      s ；⌊ p ⌋≋ᵖ q ； s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿᵖ M ⟨ d ⟩ ⊑ M′ ⟨ d′ ⟩
        ⦂ D ⊑ᵖ D′ ∶ q

------------------------------------------------------------------------
-- Reduction-saturated use of the smaller ordinary relation
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_

record _∣_∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : StoreImp Φ Δᴸ Δᴿ) (γ : CtxImp Φ Δᴸ Δᴿ)
    (M M′ : Term) (A A′ : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) : Set₁ where
  constructor related-after-pure-reduction
  field
    sourceChanges : StoreChanges
    targetChanges : StoreChanges
    sourceChangesKeep : AllKeep sourceChanges
    targetChangesKeep : AllKeep targetChanges
    sourceResult : Term
    targetResult : Term
    sourceReduction : M —↠[ sourceChanges ] sourceResult
    targetReduction : M′ —↠[ targetChanges ] targetResult
    resultImprecision :
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ sourceResult ⊑ targetResult ⦂ A ⊑ A′ ∶ p

open _∣_∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_ public
