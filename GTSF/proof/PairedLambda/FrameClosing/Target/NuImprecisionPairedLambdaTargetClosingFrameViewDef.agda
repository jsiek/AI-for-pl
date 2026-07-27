module proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef where

-- File Charter:
--   * Defines a proof-relevant, world-changing frame spine for the paired
--     lambda target-closing proof.
--   * Keeps paired and quotiented frames atomic, so no unsound one-sided
--     intermediate type-imprecision index is exposed.
--   * Keeps source-only generic closing terminal while representing the
--     outer-`∀ⁱ` generic case as a recursive source frame.
--   * Uses only constructor-form term indices; plugging and frame composition
--     are deliberately absent from the data indices.
--   * Contains no classifier implementation, postulate, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; narrowing; widening)
import Coercions as C
open import Coercions using
  ( Coercion
  ; Inert
  ; ModeEnv
  ; _!
  ; genᵈ
  ; id-onlyᵈ
  ; inst
  ; tag-or-idᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_]ᴸ_; _[_↦_]ᴿ_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_; _；⌊_⌋≋ᵖ_；_)
open import Imprecision using (NonVar; ⇑ᴿᵢ)
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( Closedᵐ
  ; No•
  ; Term
  ; Value
  ; Λ_
  ; _⟨_⟩
  ; renameᵗᵐ
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ)
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (EmbeddedTargetInstantiationCreation)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
open import Types using
  ( Ground
  ; Renameᵗ
  ; Ty
  ; TyCtx
  ; WfTy
  ; renameᵗ
  ; wf★
  ; ★
  ; `∀
  ; occurs
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.DGG.Core.NuProgress using (AllView)


data PairedLambdaTargetClosingLeaf
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    ( ρ : StoreImp Φ Δᴸ Δᴿ) →
    (L L′ : Term) → (A A′ : Ty) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) → Set₁ where

  leaf-ΛΛ :
      ∀ {ρ ρ′ γ′ V V′ A B p} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
    LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] γ′ →
    Value V → No• V →
    Value V′ → No• V′ →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
    PairedLambdaTargetClosingLeaf ρ
      (Λ V) (Λ V′) (`∀ A) (`∀ B) (∀ⁱ p)

  leaf-Λ :
      ∀ {ρ ρ′ γ′ V N′ A B p} →
    {{safe : NonVar A}} →
    (occ : occurs zero A ≡ true) →
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
    LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] γ′ →
    Value V → No• V →
    Value N′ → No• N′ →
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ∣ Δᴿ ∣ ρ′ ∣ γ′
      ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
    PairedLambdaTargetClosingLeaf ρ
      (Λ V) N′ (`∀ A) B (ν safe occ p)

  leaf-target-instantiation :
      ∀ {Φ₀ Θᴸ Θᴿ}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          (suc Θᴸ) (suc Θᴿ)}
        {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
        {W W′ V V′ : Term} {A′ B C D F : Ty}
        {s c′ : Coercion} {μ : ModeEnv} {r}
        {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
        {p : Φ ∣ Δᴸ ⊢ `∀ F ⊑ A′ ⊣ Δᴿ}
        {body-shape : ImprecisionShape} →
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
      {Ψ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      ρ (Λ V) (V′ ⟨ c′ ⟩) (`∀ F) A′ p →
    PairedLambdaTargetClosingLeaf ρ
      (Λ V) (V′ ⟨ c′ ⟩) (`∀ F) A′ p

  leaf-gen-ν :
      ∀ {ρ V N′ A B B′ q c μ c-shape} →
    {{safe : NonVar B}} →
    Value V → No• V →
    Value N′ → No• N′ →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    (hA : WfTy Δᴸ A) →
    (occ : occurs zero B ≡ true) →
    genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
      ⊢ c ∶ ⇑ᵗ A =⇒ B →
    (cⁿ : NW.GenSafe c) →
    narrowing ⊢ᶜ C.gen A c ⦂ c-shape →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B′ ∶ q →
    (occ-r : occurs zero B ≡ true) →
    (r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
    c-shape ； ⌊ q ⌋ ≋ ⌊ ν safe occ-r r ⌋ →
    PairedLambdaTargetClosingLeaf ρ
      (V ⟨ C.gen A c ⟩) N′ (`∀ B) B′ (ν safe occ-r r)

  leaf-gen-ground :
      ∀ {ρ V W A B H p c μ} →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ C.gen A c ∶ A ⊒ `∀ B →
    Ground H →
    Value V → No• V →
    Value W → No• W →
    Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ W ⦂ H →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ V ⊑ W ⟨ H ! ⟩ ⦂ A ⊑ ★ ∶ p →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ H ⊣ Δᴿ) →
    PairedLambdaTargetClosingLeaf ρ
      (V ⟨ C.gen A c ⟩) W (`∀ B) H q

  leaf-up-gen :
      ∀ {ρ M M′ X C′ D D′ B B′ pC
        d d′ u u′ d-shape d′-shape u-shape u′-shape} →
    Value M → No• M →
    Value M′ → No• M′ →
    Inert d′ → Inert u′ →
    genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.gen X d ∶ X ⊒ `∀ D →
    narrowing ⊢ᶜ C.gen X d ⦂ d-shape →
    genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    narrowing ⊢ᶜ d′ ⦂ d′-shape →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ M ⊑ M′ ⦂ X ⊑ C′ ∶ pC →
    (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
    d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρ
      (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
    widening ⊢ᶜ C.`∀ u ⦂ u-shape →
    widening ⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ q ⌋≋ᵖ qD ； u′-shape →
    PairedLambdaTargetClosingLeaf ρ
      ((M ⟨ C.gen X d ⟩) ⟨ C.`∀ u ⟩)
      ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩)
      (`∀ B) B′ q


data PairedLambdaTargetClosingFrames
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ₀ : StoreImp Φ Δᴸ Δᴿ)
    (L L′ : Term) (A A′ : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) :
    ( ρ : StoreImp Φ Δᴸ Δᴿ) →
    (W W′ : Term) → (B B′ : Ty) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) → Set₁ where

  frame-refl :
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ₀ L L′ A A′ p

  frame-prefix :
      ∀ {ρ₁ ρ₂ W W′ B B′ q} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ₁ W W′ B B′ q →
    StoreImpPrefix ρ₁ ρ₂ →
    Δᴸ ∣ leftStoreⁱ ρ₂ ∣ [] ⊢ W ⦂ B →
    Δᴿ ∣ rightStoreⁱ ρ₂ ∣ [] ⊢ W′ ⦂ B′ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ₂ W W′ B B′ q

  frame-cast⊒⊑ :
      ∀ {ρ W W′ B C B′ q c μ c-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ c ∶ `∀ B ⊒ `∀ C →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    narrowing ⊢ᶜ C.`∀ c ⦂ c-shape →
    c-shape ； ⌊ q ⌋ ≋ ⌊ r ⌋ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-cast⊑⊑ :
      ∀ {ρ W W′ B C B′ q c μ c-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    μ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ c ∶ `∀ B ⊑ `∀ C →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    widening ⊢ᶜ C.`∀ c ⦂ c-shape →
    c-shape ； ⌊ r ⌋ ≋ ⌊ q ⌋ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-conv↑⊑ :
      ∀ {ρ W W′ B C B′ q c μ α X} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    RevealConversion μ Δᴸ (leftStoreⁱ ρ)
      α X (C.`∀ c) (`∀ B) (`∀ C) →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    q [ α ↦ X ]ᴸ r →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-conv↓⊑ :
      ∀ {ρ W W′ B C B′ q c μ α X} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    ConcealConversion μ Δᴸ (leftStoreⁱ ρ)
      α X (C.`∀ c) (`∀ B) (`∀ C) →
    (r : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    r [ α ↦ X ]ᴸ q →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) W′ (`∀ C) B′ r

  frame-gen-all :
      ∀ {ρ V N′ F B B′ q c μ c-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ V N′ (`∀ F) (`∀ B′) q →
    CastMode μ →
    SealModeStore★ μ (leftStoreⁱ ρ) →
    (hA : WfTy Δᴸ (`∀ F)) →
    (occ : occurs zero B ≡ true) →
    genᵈ μ ∣ suc Δᴸ ∣ ⟰ᵗ (leftStoreⁱ ρ)
      ⊢ c ∶ ⇑ᵗ (`∀ F) =⇒ B →
    NW.GenSafe c →
    (r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ) →
    narrowing ⊢ᶜ C.gen (`∀ F) c ⦂ c-shape →
    c-shape ； ⌊ q ⌋ ≋ ⌊ ∀ⁱ r ⌋ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (V ⟨ C.gen (`∀ F) c ⟩) N′
      (`∀ B) (`∀ B′) (∀ⁱ r)

  frame-⊑cast⊒ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′ c′-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊒ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    narrowing ⊢ᶜ c′ ⦂ c′-shape →
    ⌊ r ⌋ ； c′-shape ≋ ⌊ q ⌋ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑cast⊑ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′ c′-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    CastMode μ′ →
    SealModeStore★ μ′ (rightStoreⁱ ρ) →
    μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ B′ ⊑ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    widening ⊢ᶜ c′ ⦂ c′-shape →
    ⌊ q ⌋ ； c′-shape ≋ ⌊ r ⌋ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑cast⊑id :
      ∀ {ρ W W′ B B′ C′ q c′ c′-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ c′ ∶ B′ ⊑ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    widening ⊢ᶜ c′ ⦂ c′-shape →
    ⌊ q ⌋ ； c′-shape ≋ ⌊ r ⌋ →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑conv↑ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′ β X′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    q [ β ↦ X′ ]ᴿ r →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-⊑conv↓ :
      ∀ {ρ W W′ B B′ C′ q c′ μ′ β X′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    Inert c′ →
    ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
      β X′ c′ B′ C′ →
    (r : Φ ∣ Δᴸ ⊢ B ⊑ C′ ⊣ Δᴿ) →
    r [ β ↦ X′ ]ᴿ q →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W (W′ ⟨ c′ ⟩) B C′ r

  frame-conv⊑conv :
      ∀ {ρ W W′ B C B′ C′ q r c c′} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ (`∀ B) B′ q →
    Inert c′ →
    PairedCast Φ Δᴸ Δᴿ ρ (C.`∀ c) c′ q r →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ (W ⟨ C.`∀ c ⟩) (W′ ⟨ c′ ⟩) (`∀ C) C′ r

  frame-up-id :
      ∀ {ρ M M′ C C′ D D′ B B′ pC d d′ u u′
        d-shape d′-shape u-shape u′-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ M M′ (`∀ C) C′ pC →
    Inert d′ → Inert u′ →
    id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D →
    narrowing ⊢ᶜ C.`∀ d ⦂ d-shape →
    id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ C′ ⊒ D′ →
    narrowing ⊢ᶜ d′ ⦂ d′-shape →
    (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
    d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρ
      (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
    widening ⊢ᶜ C.`∀ u ⦂ u-shape →
    widening ⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ q ⌋≋ᵖ qD ； u′-shape →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ
      ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
      ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) (`∀ B) B′ q

  frame-up-gen-all :
      ∀ {ρ M M′ C C′ D D′ B B′ pC d d′ u u′
        d-shape d′-shape u-shape u′-shape} →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ M M′ (`∀ C) C′ pC →
    Inert d′ → Inert u′ →
    genᵈ tag-or-idᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ
      ⊢ C.`∀ d ∶ `∀ C ⊒ `∀ D →
    narrowing ⊢ᶜ C.`∀ d ⦂ d-shape →
    genᵈ tag-or-idᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ d′ ∶ C′ ⊒ D′ →
    narrowing ⊢ᶜ d′ ⦂ d′-shape →
    (qD : Φ ∣ Δᴸ ⊢ `∀ D ⊑ᵖ D′ ⊣ Δᴿ) →
    d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
    QuotientWideningPair Δᴸ Δᴿ ρ
      (C.`∀ u) u′ (`∀ D) D′ (`∀ B) B′ →
    (q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ) →
    widening ⊢ᶜ C.`∀ u ⦂ u-shape →
    widening ⊢ᶜ u′ ⦂ u′-shape →
    u-shape ；⌊ q ⌋≋ᵖ qD ； u′-shape →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p ρ
      ((M ⟨ C.`∀ d ⟩) ⟨ C.`∀ u ⟩)
      ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) (`∀ B) B′ q


data PairedLambdaTargetClosingFrameView
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} :
    ( ρ : StoreImp Φ Δᴸ Δᴿ) →
    (W W′ : Term) → (B B′ : Ty) →
    (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) → Set₁ where

  closing-frame-view :
      ∀ {ρ₀ L L′ A A′ p ρ W W′ B B′ q} →
    PairedLambdaTargetClosingLeaf ρ₀ L L′ A A′ p →
    PairedLambdaTargetClosingFrames ρ₀ L L′ A A′ p
      ρ W W′ B B′ q →
    PairedLambdaTargetClosingFrameView ρ W W′ B B′ q


PairedLambdaTargetClosingFrameViewᵀ : Set₁
PairedLambdaTargetClosingFrameViewᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W W′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  AllView W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ A ⊑ B ∶ p →
  PairedLambdaTargetClosingFrameView ρ W W′ A B p
