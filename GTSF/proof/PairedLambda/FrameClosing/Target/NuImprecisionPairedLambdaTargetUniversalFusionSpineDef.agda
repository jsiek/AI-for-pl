module
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetUniversalFusionSpineDef
  where

-- File Charter:
--   * Defines a framed recursive closure of the pure target universal fusion
--     spine without introducing a dependency from target administration back
--     to paired-lambda frame closing.
--   * Permits ordinary paired-lambda frames around the pure base and around
--     every recursively nested target-instantiation fusion step.
--   * States only the fold back to quotiented term imprecision; extraction
--     and non-fusion residual routing remain separate boundaries.
--   * Contains no simulation result, implementation, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import ImprecisionWf using
  ( ImpAssm
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
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
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import
  proof.Core.Properties.TypeProperties
  using (TyRenameWf)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (rename-assm²ᵢ)
open import
  proof.PairedLambda.FrameClosing.Target.NuImprecisionPairedLambdaTargetClosingFrameViewDef
  using (PairedLambdaTargetClosingFrames)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
open import
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineDef
  using (TargetUniversalFusionSpine)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; renameᵗ
  ; wf★
  ; ★
  ; `∀
  ; ⇑ᵗ
  )


data PairedLambdaTargetUniversalFusionSpine
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (M M′ : Term) → (A H : Ty) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ H ⊣ Δᴿ) →
    Set₁ where

  framed-fusion-pure :
      ∀ {ρ₀ L L′ A₀ H₀ p₀ M M′ A H p} →
    TargetUniversalFusionSpine ρ₀ L L′ A₀ H₀ p₀ →
    PairedLambdaTargetClosingFrames
      ρ₀ L L′ A₀ (`∀ H₀) p₀
      ρ M M′ A (`∀ H) p →
    PairedLambdaTargetUniversalFusionSpine ρ M M′ A H p

  framed-fusion-step :
      ∀ {Φ₀ : ImpCtx} {Θᴸ Θᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          (suc Θᴸ) (suc Θᴿ)}
        {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
        {ρ₁ : StoreImp Φ Δᴸ Δᴿ}
        {τ σ : Renameᵗ}
        {W W′ M M′ N N′ : Term}
        {A B D E F H K : Ty}
        {c : C.Coercion} {μ : C.ModeEnv}
        {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          ∣ suc Θᴸ ⊢ D ⊑ `∀ F ⊣ suc Θᴿ}
        {q : Φ ∣ Δᴸ ⊢ B ⊑ `∀ K ⊣ Δᴿ}
        {body-shape : ImprecisionShape} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Θᴿ ∣ rightStoreⁱ ρ₀
      ⊢ C.inst (`∀ E) (C.`∀ c) ∶ `∀ (`∀ F) ⊑ `∀ E →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀) ρ₀ ρ∀ →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ₀) ρ⁺ ρᴿ⁺ →
    Value W →
    No• W →
    Value W′ →
    No• W′ →
    C.Inert (C.`∀ c) →
    PairedLambdaTargetUniversalFusionSpine ρ∀ W W′ D F r →
    (f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ `∀ E ⊣ Θᴿ) →
    widening ⊢ᶜ C.inst (`∀ E) (C.`∀ c) ⦂ νˢ body-shape →
    ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
    (assm :
      ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
        rename-assm²ᵢ τ σ a ∈ Φ) →
    (hτ : TyRenameWf Θᴸ Δᴸ τ) →
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
    RelStoreEmbeddingⁱ τ σ
      (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ₁ →
    renameᵗᵐ τ (Λ W) ≡ M →
    renameᵗᵐ σ (W′ ⟨ C.`∀ c ⟩) ≡ M′ →
    renameᵗ τ (`∀ D) ≡ A →
    renameᵗ σ (⇑ᵗ (`∀ E)) ≡ `∀ H →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ H ⊣ Δᴿ) →
    Value M →
    No• M →
    Closedᵐ M →
    Value M′ →
    No• M′ →
    Closedᵐ M′ →
    Δᴸ ∣ leftStoreⁱ ρ₁ ∣ [] ⊢ M ⦂ A →
    Δᴿ ∣ rightStoreⁱ ρ₁ ∣ [] ⊢ M′ ⦂ `∀ H →
    PairedLambdaTargetClosingFrames
      ρ₁ M M′ A (`∀ H) p
      ρ N N′ B (`∀ K) q →
    PairedLambdaTargetUniversalFusionSpine ρ N N′ B K q


PairedLambdaTargetUniversalFusionSpineRelationᵀ : Set₁
PairedLambdaTargetUniversalFusionSpineRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A H : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ H ⊣ Δᴿ} →
  PairedLambdaTargetUniversalFusionSpine ρ M M′ A H p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ `∀ H ∶ p
