{-# OPTIONS --safe #-}

module proof.DGG.CompilePreservesImprecision where

-- File Charter:
--   * Proves that ordinary compilation preserves gradual term imprecision.
--   * Builds the initial complete-context world directly with initialWorldᶜ
--     and bind-termᶜ; there is no separate context-imprecision runtime layer.
--   * Uses the canonical cast-term imprecision relation and endpoint contexts.

open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Types
open import TyStore using (TyStore; store-lift)
open import TermCtx using (TermCtx; ⇑ᶜ; Z; S)
import TermCtx as T
open import Consistency using
  (_⊢_∼_; _↪ᵗ_; keep; skip; toRenameᵗ; symᶜ)
open import Imprecision
open import GradualTerms using (GTerm)
import GradualTerms as G
import GradualTermImprecision as GTI
open import Compile using (compile; compile-value)
import CastTerms as C
open C using
  (Ctx; Term; Δᵉ; Σᵉ; Γᵉ; ⟨_,_,_⟩; _∋ᵗ_⦂_; _⊢_⦂_)
open import Primitives using
  (Const; Prim; addℕ; and𝔹; constTy; primArgTy; primResultTy;
   constTy-renameᵗ)
import proof.DGG.Elab as Elab
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (refl⊑; rename-⊑; toRenameᵗ-injective; ty-all-injective)
open import proof.TypeInTermSubst using
  (renameᵗ-pointwise-id; toRename-keep-eq;
   rename-openᵗ; rename-occurs)
open import proof.DGG.World
import proof.DGG.CastTermImprecision as CTI
open CTI using (_⊢²_⊑_∶_)


------------------------------------------------------------------------
-- The initial complete-context world
------------------------------------------------------------------------

initial-⊑ : ∀ {Δ} {μ : ImpEnv Δ} {A B : Ty Δ}
  → μ ⊢ A ⊑ B
  → A ⊑ᵀ⟨ initialWorldᶜ μ ⟩ B
initial-⊑ {μ = μ} {A = A} {B = B} A⊑B =
  subst
    (λ Bᶜ → marksᶜ (initialWorldᶜ μ) ⊢
      renameᵗ (toRenameᵗ (ηᴸᶜ (initialWorldᶜ μ))) A ⊑ Bᶜ)
    (cong (λ η → renameᵗ (toRenameᵗ η) B)
      (initialWorld-embeddingsᶜ μ))
    (rename-⊑
      (toRenameᵗ (ηᴸᶜ (initialWorldᶜ μ)))
      (toRenameᵗ-injective (ηᴸᶜ (initialWorldᶜ μ)))
      (λ X eq → trans (initialWorld-markᶜ μ X) eq)
      A⊑B)


mutual
  initialContextWorld : ∀ {Δ} {μ : ImpEnv Δ}
    → (γ : GTI.CtxImp μ)
    → ⟨ Δ , emptyStoreᶜ Δ , GTI.srcCtxⁱ γ ⟩ ⊑ᶜ
      ⟨ Δ , emptyStoreᶜ Δ , GTI.tgtCtxⁱ γ ⟩
  initialContextWorld {μ = μ} [] = initialWorldᶜ μ
  initialContextWorld {μ = μ} (GTI.ctx-imp A B p ∷ γ) =
    bind-termᶜ (initialContextWorld γ) (initialContext-⊑ γ p)

  initialContext-⊑ : ∀ {Δ} {μ : ImpEnv Δ}
      (γ : GTI.CtxImp μ) {A B : Ty Δ}
    → μ ⊢ A ⊑ B
    → A ⊑ᵀ⟨ initialContextWorld γ ⟩ B
  initialContext-⊑ [] A⊑B = initial-⊑ A⊑B
  initialContext-⊑ (e ∷ γ) A⊑B = initialContext-⊑ γ A⊑B


initial-source-lookup : ∀ {Δ} {μ : ImpEnv Δ}
    {γ : GTI.CtxImp μ} {x A B p}
  → γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A B p
  → ⟨ Δ , emptyStoreᶜ Δ , GTI.srcCtxⁱ γ ⟩ ∋ᵗ x ⦂ A
initial-source-lookup GTI.Zⁱ = Z
initial-source-lookup (GTI.Sⁱ x∈) = S (initial-source-lookup x∈)


initial-target-lookup : ∀ {Δ} {μ : ImpEnv Δ}
    {γ : GTI.CtxImp μ} {x A B p}
  → γ GTI.∋ⁱ x ⦂ GTI.ctx-imp A B p
  → ⟨ Δ , emptyStoreᶜ Δ , GTI.tgtCtxⁱ γ ⟩ ∋ᵗ x ⦂ B
initial-target-lookup GTI.Zⁱ = Z
initial-target-lookup (GTI.Sⁱ x∈) = S (initial-target-lookup x∈)


------------------------------------------------------------------------
-- Compile-world geometry
------------------------------------------------------------------------

sourceEmbedding : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
  → centerᶜ γ ≡ Δᵉ Γᴸ
  → Δᵉ Γᴸ ↪ᵗ Δᵉ Γᴸ
sourceEmbedding {Γᴸ = Γᴸ} γ center-eq =
  subst (λ Δ → Δᵉ Γᴸ ↪ᵗ Δ) center-eq (ηᴸᶜ γ)


targetEmbedding : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
  → centerᶜ γ ≡ Δᵉ Γᴸ
  → Δᵉ Γᴿ ↪ᵗ Δᵉ Γᴸ
targetEmbedding {Γᴸ = Γᴸ} {Γᴿ = Γᴿ} γ center-eq =
  subst (λ Δ → Δᵉ Γᴿ ↪ᵗ Δ) center-eq (ηᴿᶜ γ)


SourceId : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
  → (center-eq : centerᶜ γ ≡ Δᵉ Γᴸ)
  → Set
SourceId {Γᴸ = Γᴸ} γ center-eq =
  ∀ X → toRenameᵗ (sourceEmbedding γ center-eq) X ≡ X


TargetId : ∀ {Δ} {Σᴸ Σᴿ : TyStore Δ} {Ψᴸ Ψᴿ : TermCtx Δ}
  → (γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δ , Σᴿ , Ψᴿ ⟩)
  → (center-eq : centerᶜ γ ≡ Δ)
  → Set
TargetId γ center-eq =
  ∀ X → toRenameᵗ (targetEmbedding γ center-eq) X ≡ X


private
  subst-keep : ∀ {m n k} (eq : n ≡ k) (η : m ↪ᵗ n)
    → subst (λ q → Nat.suc m ↪ᵗ q) (cong Nat.suc eq) (keep η)
      ≡ keep (subst (λ q → m ↪ᵗ q) eq η)
  subst-keep refl η = refl


initialWorld-source-id : ∀ {Δ} (μ : ImpEnv Δ)
  → SourceId (initialWorldᶜ μ) (initialWorld-centerᶜ μ)
initialWorld-source-id {Nat.zero} μ ()
initialWorld-source-id {Nat.suc Δ} μ Fin.zero
    rewrite subst-keep
      (initialWorld-centerᶜ (λ Y → μ (Fin.suc Y)))
      (ηᴸᶜ (initialWorldᶜ (λ Y → μ (Fin.suc Y)))) =
  refl
initialWorld-source-id {Nat.suc Δ} μ (Fin.suc X)
    rewrite subst-keep
      (initialWorld-centerᶜ (λ Y → μ (Fin.suc Y)))
      (ηᴸᶜ (initialWorldᶜ (λ Y → μ (Fin.suc Y)))) =
  cong Fin.suc
    (initialWorld-source-id (λ Y → μ (Fin.suc Y)) X)


initialWorld-target-id : ∀ {Δ} (μ : ImpEnv Δ)
  → TargetId (initialWorldᶜ μ) (initialWorld-centerᶜ μ)
initialWorld-target-id {Δ = Δ} μ X =
  trans
    (cong
      (λ η → toRenameᵗ
        (subst (λ q → Δ ↪ᵗ q) (initialWorld-centerᶜ μ) η) X)
      (sym (initialWorld-embeddingsᶜ μ)))
    (initialWorld-source-id μ X)


EnvMatches : ∀ {Γᴸ Γᴿ} (γ : Γᴸ ⊑ᶜ Γᴿ)
  → ImpEnv (Δᵉ Γᴸ)
  → Set
EnvMatches γ μ =
  ∀ X → marksᶜ γ (toRenameᵗ (ηᴸᶜ γ) X) ≡ μ X


initialContext-center : ∀ {Δ} {μ : ImpEnv Δ}
    (δ : GTI.CtxImp μ)
  → centerᶜ (initialContextWorld δ) ≡ Δ
initialContext-center {μ = μ} [] = initialWorld-centerᶜ μ
initialContext-center (e ∷ δ) = initialContext-center δ


initialContext-source-id : ∀ {Δ} {μ : ImpEnv Δ}
    (δ : GTI.CtxImp μ)
  → SourceId (initialContextWorld δ) (initialContext-center δ)
initialContext-source-id {μ = μ} [] = initialWorld-source-id μ
initialContext-source-id (e ∷ δ) = initialContext-source-id δ


initialContext-target-id : ∀ {Δ} {μ : ImpEnv Δ}
    (δ : GTI.CtxImp μ)
  → TargetId (initialContextWorld δ) (initialContext-center δ)
initialContext-target-id {μ = μ} [] = initialWorld-target-id μ
initialContext-target-id (e ∷ δ) = initialContext-target-id δ


initialContext-matches : ∀ {Δ} {μ : ImpEnv Δ}
    (δ : GTI.CtxImp μ)
  → EnvMatches (initialContextWorld δ) μ
initialContext-matches {μ = μ} [] = initialWorld-markᶜ μ
initialContext-matches (e ∷ δ) = initialContext-matches δ


sourceId-liftBoth : ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δᴸ}
  → (v : VarImp)
  → SourceId γ center-eq
  → SourceId (liftBothᶜ v γ) (cong Nat.suc center-eq)
sourceId-liftBoth {γ = γ} {center-eq = center-eq} v sid Fin.zero
    rewrite subst-keep center-eq (ηᴸᶜ γ) =
  refl
sourceId-liftBoth {γ = γ} {center-eq = center-eq} v sid (Fin.suc X)
    rewrite subst-keep center-eq (ηᴸᶜ γ) =
  cong Fin.suc (sid X)


sourceId-liftLeft : ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δᴸ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δᴸ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δᴸ}
  → SourceId γ center-eq
  → SourceId (liftLeftᶜ γ) (cong Nat.suc center-eq)
sourceId-liftLeft {γ = γ} {center-eq = center-eq} sid Fin.zero
    rewrite subst-keep center-eq (ηᴸᶜ γ) =
  refl
sourceId-liftLeft {γ = γ} {center-eq = center-eq} sid (Fin.suc X)
    rewrite subst-keep center-eq (ηᴸᶜ γ) =
  cong Fin.suc (sid X)


matches-liftBoth : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {μ : ImpEnv (Δᵉ Γᴸ)}
  → EnvMatches γ μ
  → EnvMatches (liftBothᶜ X⊑X γ) (extᵐ μ)
matches-liftBoth matches Fin.zero = refl
matches-liftBoth matches (Fin.suc X) = matches X


matches-liftLeft : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {μ : ImpEnv (Δᵉ Γᴸ)}
  → EnvMatches γ μ
  → EnvMatches (liftLeftᶜ γ) (instᵐ μ)
matches-liftLeft matches Fin.zero = refl
matches-liftLeft matches (Fin.suc X) = matches X


embed-imprecision : ∀ {Δ Δᴿ Δᶜ}
    {ηᴸ : Δ ↪ᵗ Δᶜ} {ηᴿ : Δᴿ ↪ᵗ Δᶜ}
    {marks : ImpEnv Δᶜ} {μ : ImpEnv Δ}
    {A Bᶜ : Ty Δ} {B : Ty Δᴿ}
  → (center-eq : Δᶜ ≡ Δ)
  → (∀ X → toRenameᵗ
      (subst (λ Θ → Δ ↪ᵗ Θ) center-eq ηᴸ) X ≡ X)
  → (∀ X → marks (toRenameᵗ ηᴸ X) ≡ μ X)
  → Bᶜ ≡ renameᵗ (toRenameᵗ
      (subst (λ Θ → Δᴿ ↪ᵗ Θ) center-eq ηᴿ)) B
  → μ ⊢ A ⊑ Bᶜ
  → marks ⊢ renameᵗ (toRenameᵗ ηᴸ) A
      ⊑ renameᵗ (toRenameᵗ ηᴿ) B
embed-imprecision refl source-id matches refl A⊑B =
  subst
    (λ B′ → _ ⊢ renameᵗ (toRenameᵗ _) _ ⊑ B′)
    (renameᵗ-pointwise-id _ _ source-id)
    (rename-⊑ (toRenameᵗ _)
      (toRenameᵗ-injective _)
      (λ X eq → trans (matches X) eq)
      A⊑B)


embedded-⊑ : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {μ : ImpEnv (Δᵉ Γᴸ)}
    (center-eq : centerᶜ γ ≡ Δᵉ Γᴸ)
    (source-id : SourceId γ center-eq)
    (matches : EnvMatches γ μ)
    {A Bᶜ : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
  → Bᶜ ≡ renameᵗ (toRenameᵗ (targetEmbedding γ center-eq)) B
  → μ ⊢ A ⊑ Bᶜ
  → A ⊑ᵀ⟨ γ ⟩ B
embedded-⊑ {γ = γ} center-eq source-id matches =
  embed-imprecision center-eq source-id matches


------------------------------------------------------------------------
-- Gradual context entries embedded at the target endpoint
------------------------------------------------------------------------

data EmbeddedCtx {Δ Δᴿ} {Σᴸ : TyStore Δ} {Σᴿ : TyStore Δᴿ}
    {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    (γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩)
    (center-eq : centerᶜ γ ≡ Δ)
    {μ : ImpEnv Δ} (source-id : SourceId γ center-eq)
    (matches : EnvMatches γ μ) :
    GTI.CtxImp μ → TermCtx Δ → TermCtx Δᴿ → Set where

  embedded-[] : EmbeddedCtx γ center-eq source-id matches [] [] []

  embedded-∷ : ∀ {δ Φᴸ Φᴿ A Bᶜ B p}
    → Bᶜ ≡ renameᵗ (toRenameᵗ (targetEmbedding γ center-eq)) B
    → EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ
    → EmbeddedCtx γ center-eq source-id matches
        (GTI.ctx-imp A Bᶜ p ∷ δ) (A ∷ Φᴸ) (B ∷ Φᴿ)


embeddedCtx-source : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {δ Φᴸ Φᴿ}
  → EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ
  → GTI.srcCtxⁱ δ ≡ Φᴸ
embeddedCtx-source embedded-[] = refl
embeddedCtx-source (embedded-∷ eqB rel) =
  cong (_ ∷_) (embeddedCtx-source rel)


embeddedCtx-target : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {δ Φᴸ Φᴿ}
  → EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ
  → GTI.tgtCtxⁱ δ
      ≡ T.renameCtx (toRenameᵗ (targetEmbedding γ center-eq)) Φᴿ
embeddedCtx-target embedded-[] = refl
embeddedCtx-target (embedded-∷ eqB rel) =
  cong₂ _∷_ eqB (embeddedCtx-target rel)


embedded-bind-term : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {A : Ty Δ} {B : Ty Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {represented : A ⊑ᵀ⟨ γ ⟩ B} {δ Φᴸ Φᴿ}
  → EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ
  → EmbeddedCtx (bind-termᶜ γ represented) center-eq source-id matches
      δ Φᴸ Φᴿ
embedded-bind-term embedded-[] = embedded-[]
embedded-bind-term (embedded-∷ eqB rel) =
  embedded-∷ eqB (embedded-bind-term rel)


record EmbeddedLookup {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {δ Φᴸ Φᴿ x A Bᶜ p}
    (rel : EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ)
    (x∈ : δ GTI.∋ⁱ x ⦂ GTI.ctx-imp A Bᶜ p) : Set where
  constructor embedded-lookup
  field
    B : Ty Δᴿ
    eqB : Bᶜ ≡ renameᵗ
      (toRenameᵗ (targetEmbedding γ center-eq)) B
    Φᴸ∋ : Φᴸ T.∋ x ⦂ A
    Φᴿ∋ : Φᴿ T.∋ x ⦂ B

open EmbeddedLookup


embedded-lookup-at : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {δ Φᴸ Φᴿ x A Bᶜ p}
  → (rel : EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ)
  → (x∈ : δ GTI.∋ⁱ x ⦂ GTI.ctx-imp A Bᶜ p)
  → EmbeddedLookup rel x∈
embedded-lookup-at (embedded-∷ {B = B} eqB rel) GTI.Zⁱ =
  embedded-lookup B eqB T.Z T.Z
embedded-lookup-at (embedded-∷ eqB rel) (GTI.Sⁱ x∈)
    with embedded-lookup-at rel x∈
embedded-lookup-at (embedded-∷ eqB rel) (GTI.Sⁱ x∈)
    | embedded-lookup B eqB′ Φᴸ∋ Φᴿ∋ =
  embedded-lookup B eqB′ (T.S Φᴸ∋) (T.S Φᴿ∋)


private
  subst-skip : ∀ {m n k} (eq : n ≡ k) (η : m ↪ᵗ n)
    → subst (λ q → m ↪ᵗ q) (cong Nat.suc eq) (skip η)
      ≡ skip (subst (λ q → m ↪ᵗ q) eq η)
  subst-skip refl η = refl

  rename-keep-shift : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (keep η)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
  rename-keep-shift η A =
    trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq η))
      (renameᵗ-shift (toRenameᵗ η) A)

  rename-skip : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (skip η)) A
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) A)
  rename-skip η A =
    trans (renameᵗ-cong A (λ X → refl))
      (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc A))


targetEmbedding-liftBoth : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    (center-eq : centerᶜ γ ≡ Δ)
  → targetEmbedding (liftBothᶜ X⊑X γ) (cong Nat.suc center-eq)
    ≡ keep (targetEmbedding γ center-eq)
targetEmbedding-liftBoth {γ = γ} center-eq =
  subst-keep center-eq (ηᴿᶜ γ)


targetEmbedding-liftLeft : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    (center-eq : centerᶜ γ ≡ Δ)
  → targetEmbedding (liftLeftᶜ γ) (cong Nat.suc center-eq)
    ≡ skip (targetEmbedding γ center-eq)
targetEmbedding-liftLeft {γ = γ} center-eq =
  subst-skip center-eq (ηᴿᶜ γ)


embedded-liftBoth : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {δ δ′ Φᴸ Φᴿ}
  → EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ
  → GTI.LiftCtxⁱ (extᵐ μ) δ δ′
  → EmbeddedCtx (liftBothᶜ X⊑X γ) (cong Nat.suc center-eq)
      (sourceId-liftBoth {γ = γ} {center-eq = center-eq}
        X⊑X source-id)
      (matches-liftBoth {γ = γ} matches)
      δ′ (⇑ᶜ Φᴸ) (⇑ᶜ Φᴿ)
embedded-liftBoth embedded-[] GTI.lift-[] = embedded-[]
embedded-liftBoth {γ = γ} {center-eq = center-eq}
    {source-id = source-id} {matches = matches}
    (embedded-∷ {B = B} eqB rel) (GTI.lift-∷ liftδ) =
  embedded-∷
    (trans (cong ⇑ᵗ eqB)
      (trans
        (sym (rename-keep-shift (targetEmbedding γ center-eq) B))
        (cong (λ η → renameᵗ (toRenameᵗ η) (⇑ᵗ B))
          (sym (targetEmbedding-liftBoth {γ = γ} center-eq)))))
    (embedded-liftBoth {γ = γ} {center-eq = center-eq}
      {source-id = source-id} {matches = matches} rel liftδ)


embedded-liftLeft : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {δ δ′ Φᴸ Φᴿ}
  → EmbeddedCtx γ center-eq source-id matches δ Φᴸ Φᴿ
  → GTI.LiftCtxⁱ (instᵐ μ) δ δ′
  → EmbeddedCtx (liftLeftᶜ γ) (cong Nat.suc center-eq)
      (sourceId-liftLeft {γ = γ} {center-eq = center-eq} source-id)
      (matches-liftLeft {γ = γ} matches)
      δ′ (⇑ᶜ Φᴸ) Φᴿ
embedded-liftLeft embedded-[] GTI.lift-[] = embedded-[]
embedded-liftLeft {γ = γ} {center-eq = center-eq}
    {source-id = source-id} {matches = matches}
    (embedded-∷ {B = B} eqB rel) (GTI.lift-∷ liftδ) =
  embedded-∷
    (trans (cong ⇑ᵗ eqB)
      (trans
        (sym (rename-skip (targetEmbedding γ center-eq) B))
        (cong (λ η → renameᵗ (toRenameᵗ η) B)
          (sym (targetEmbedding-liftLeft {γ = γ} center-eq)))))
    (embedded-liftLeft {γ = γ} {center-eq = center-eq}
      {source-id = source-id} {matches = matches} rel liftδ)


------------------------------------------------------------------------
-- Elaboration and renaming support
------------------------------------------------------------------------

⊢²-retarget : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)}
    {p q : A ⊑ᵀ⟨ γ ⟩ B}
  → γ ⊢² M ⊑ M′ ∶ p
  → γ ⊢² M ⊑ M′ ∶ q
⊢²-retarget {γ = γ} {M = M} {M′ = M′} {p = p} {q = q} d =
  subst (λ r → γ ⊢² M ⊑ M′ ∶ r) (PI.⊑-unique p q) d


embedded-elab-gradual-typing : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    {center-eq : centerᶜ γ ≡ Δ} {μ : ImpEnv Δ}
    {source-id : SourceId γ center-eq} {matches : EnvMatches γ μ}
    {δ M′ Mᴿ Bᶜ B N}
  → (rel : EmbeddedCtx γ center-eq source-id matches δ Ψᴸ Ψᴿ)
  → M′ ≡ Elab.Grenameᵐ (targetEmbedding γ center-eq) Mᴿ
  → Bᶜ ≡ renameᵗ (toRenameᵗ (targetEmbedding γ center-eq)) B
  → Elab.Elab Σᴿ Ψᴿ Mᴿ N B
  → Δ G.∣ GTI.tgtCtxⁱ δ ⊢ M′ ⦂ Bᶜ
embedded-elab-gradual-typing {Σᴸ = Σᴸ} {γ = γ}
    {center-eq = center-eq} rel eqM eqB Mᴱ =
  subst (λ T′ → _ G.∣ _ ⊢ _ ⦂ T′) (sym eqB)
    (subst (λ M′ → _ G.∣ _ ⊢ M′ ⦂ _) (sym eqM)
      (subst (λ Ψ′ → _ G.∣ Ψ′ ⊢ _ ⦂ _)
        (sym (embeddedCtx-target rel))
        (Elab.elab-gradual-typing
          (Elab.rename-elab {Σ′ = Σᴸ}
            (targetEmbedding γ center-eq) Mᴱ))))


Grenameᵐ-rename : ∀ {Δ₀ Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
    (η : Δ₀ ↪ᵗ Δ) (η′ : Δ₀ ↪ᵗ Δ′)
  → (∀ X → ρ (toRenameᵗ η X) ≡ toRenameᵗ η′ X)
  → (M : GTerm Δ₀)
  → G.renameᵗᴳ ρ (Elab.Grenameᵐ η M) ≡ Elab.Grenameᵐ η′ M
Grenameᵐ-rename ρ η η′ eq (G.` x) = refl
Grenameᵐ-rename ρ η η′ eq (G.ƛ A ⇒ M) =
  cong₂ G.ƛ_⇒_
    (trans (renameᵗ-comp (toRenameᵗ η) ρ A) (renameᵗ-cong A eq))
    (Grenameᵐ-rename ρ η η′ eq M)
Grenameᵐ-rename ρ η η′ eq (L G.·[ ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.·[ ℓ ] M′)
    (Grenameᵐ-rename ρ η η′ eq L)
    (Grenameᵐ-rename ρ η η′ eq M)
Grenameᵐ-rename ρ η η′ eq (G.Λ M) =
  cong G.Λ_ (Grenameᵐ-rename (extᵗ ρ) (keep η) (keep η′) ext-eq M)
  where
  ext-eq : ∀ X
    → extᵗ ρ (toRenameᵗ (keep η) X) ≡ toRenameᵗ (keep η′) X
  ext-eq Fin.zero = refl
  ext-eq (Fin.suc X) = cong Fin.suc (eq X)
Grenameᵐ-rename ρ η η′ eq (M G.`[ A ]) =
  cong₂ G._`[_]
    (Grenameᵐ-rename ρ η η′ eq M)
    (trans (renameᵗ-comp (toRenameᵗ η) ρ A)
      (renameᵗ-cong A eq))
Grenameᵐ-rename ρ η η′ eq (G.$ κ) = refl
Grenameᵐ-rename ρ η η′ eq (L G.⊕[ op at ℓ ] M) =
  cong₂ (λ L′ M′ → L′ G.⊕[ op at ℓ ] M′)
    (Grenameᵐ-rename ρ η η′ eq L)
    (Grenameᵐ-rename ρ η η′ eq M)


Grenameᵐ-skip : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (M : GTerm Δᴿ)
  → G.⇑ᵗᴳ (Elab.Grenameᵐ η M) ≡ Elab.Grenameᵐ (skip η) M
Grenameᵐ-skip η M =
  Grenameᵐ-rename Fin.suc η (skip η) (λ X → refl) M


Grenameᵐ-pointwise-id : ∀ {Δ} (η : Δ ↪ᵗ Δ) (M : GTerm Δ)
  → (∀ X → toRenameᵗ η X ≡ X)
  → Elab.Grenameᵐ η M ≡ M
Grenameᵐ-pointwise-id η (G.` x) eq = refl
Grenameᵐ-pointwise-id η (G.ƛ A ⇒ M) eq =
  cong₂ G.ƛ_⇒_
    (renameᵗ-pointwise-id (toRenameᵗ η) A eq)
    (Grenameᵐ-pointwise-id η M eq)
Grenameᵐ-pointwise-id η (L G.·[ ℓ ] M) eq =
  cong₂ (λ L′ M′ → L′ G.·[ ℓ ] M′)
    (Grenameᵐ-pointwise-id η L eq)
    (Grenameᵐ-pointwise-id η M eq)
Grenameᵐ-pointwise-id η (G.Λ M) eq =
  cong G.Λ_ (Grenameᵐ-pointwise-id (keep η) M keep-eq)
  where
  keep-eq : ∀ X → toRenameᵗ (keep η) X ≡ X
  keep-eq Fin.zero = refl
  keep-eq (Fin.suc X) = cong Fin.suc (eq X)
Grenameᵐ-pointwise-id η (M G.`[ A ]) eq =
  cong₂ G._`[_]
    (Grenameᵐ-pointwise-id η M eq)
    (renameᵗ-pointwise-id (toRenameᵗ η) A eq)
Grenameᵐ-pointwise-id η (G.$ κ) eq = refl
Grenameᵐ-pointwise-id η (L G.⊕[ op at ℓ ] M) eq =
  cong₂ (λ L′ M′ → L′ G.⊕[ op at ℓ ] M′)
    (Grenameᵐ-pointwise-id η L eq)
    (Grenameᵐ-pointwise-id η M eq)


constTy-embedded : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    (center-eq : centerᶜ γ ≡ Δᵉ Γᴸ)
    (source-id : SourceId γ center-eq)
    {μ : ImpEnv (Δᵉ Γᴸ)}
    (matches : EnvMatches γ μ)
    (κ : Const)
  → constTy κ ⊑ᵀ⟨ γ ⟩ constTy κ
constTy-embedded {γ = γ} center-eq source-id matches κ =
  embedded-⊑ {γ = γ} center-eq source-id matches
    {A = constTy κ} {Bᶜ = constTy κ} {B = constTy κ}
    (constTy-renameᵗ
      (toRenameᵗ (targetEmbedding γ center-eq)) κ)
    (GTI.constTy-⊑ _ κ)


primArgTy-target : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    (center-eq : centerᶜ γ ≡ Δᵉ Γᴸ)
    (op : Prim)
  → primArgTy op ≡ renameᵗ
      (toRenameᵗ (targetEmbedding γ center-eq)) (primArgTy op)
primArgTy-target center-eq addℕ = refl
primArgTy-target center-eq and𝔹 = refl


primResultTy-target : ∀ {Γᴸ Γᴿ} {γ : Γᴸ ⊑ᶜ Γᴿ}
    (center-eq : centerᶜ γ ≡ Δᵉ Γᴸ)
    (op : Prim)
  → primResultTy op ≡ renameᵗ
      (toRenameᵗ (targetEmbedding γ center-eq)) (primResultTy op)
primResultTy-target center-eq addℕ = refl
primResultTy-target center-eq and𝔹 = refl


initialEmbeddedCtx : ∀ {Δ} {μ : ImpEnv Δ}
    (δ : GTI.CtxImp μ)
  → EmbeddedCtx (initialContextWorld δ) (initialContext-center δ)
      (initialContext-source-id δ) (initialContext-matches δ)
      δ (GTI.srcCtxⁱ δ) (GTI.tgtCtxⁱ δ)
initialEmbeddedCtx [] = embedded-[]
initialEmbeddedCtx (GTI.ctx-imp A B p ∷ δ) =
  embedded-∷ target-eq (embedded-bind-term (initialEmbeddedCtx δ))
  where
  target-eq = sym (renameᵗ-pointwise-id
    (toRenameᵗ
      (targetEmbedding (initialContextWorld (GTI.ctx-imp A B p ∷ δ))
        (initialContext-center (GTI.ctx-imp A B p ∷ δ))))
    B (initialContext-target-id (GTI.ctx-imp A B p ∷ δ)))


------------------------------------------------------------------------
-- Compilation preserves imprecision inside an embedded context
------------------------------------------------------------------------

compile-preserves-embedded : ∀ {Δ Δᴿ} {Σᴸ : TyStore Δ}
    {Σᴿ : TyStore Δᴿ} {Ψᴸ : TermCtx Δ} {Ψᴿ : TermCtx Δᴿ}
    {γ : ⟨ Δ , Σᴸ , Ψᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Ψᴿ ⟩}
    (center-eq : centerᶜ γ ≡ Δ)
    (source-id : SourceId γ center-eq)
    {μ : ImpEnv Δ} (matches : EnvMatches γ μ)
    {δ : GTI.CtxImp μ} {M M′ : GTerm Δ} {Mᴿ : GTerm Δᴿ}
    {A Bᶜ : Ty Δ} {B : Ty Δᴿ} {p} {N : Term Δᴿ}
  → (rel : EmbeddedCtx γ center-eq source-id matches δ Ψᴸ Ψᴿ)
  → (M⊑M′ : μ GTI.∣ δ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ Bᶜ ∶ p)
  → M′ ≡ Elab.Grenameᵐ (targetEmbedding γ center-eq) Mᴿ
  → (eqB : Bᶜ ≡ renameᵗ
      (toRenameᵗ (targetEmbedding γ center-eq)) B)
  → Elab.Elab Σᴿ Ψᴿ Mᴿ N B
  → γ ⊢²
      proj₁ (compile {Σ = Σᴸ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ N ∶ embedded-⊑ {γ = γ}
        center-eq source-id matches eqB p
compile-preserves-embedded {γ = γ} center-eq source-id matches rel
    d@(GTI.x⊑xᴳ {p = p} x∈) refl eqB (Elab.E-` x∈ᴿ)
    with embedded-lookup-at rel x∈
compile-preserves-embedded {γ = γ} center-eq source-id matches rel
    d@(GTI.x⊑xᴳ {p = p} x∈) refl eqB (Elab.E-` x∈ᴿ)
    | embedded-lookup B eqB′ x∈ᴸ x∈ᴿ′
    with Elab.lookup-uniqueᴳ x∈ᴿ′ x∈ᴿ
compile-preserves-embedded {γ = γ} center-eq source-id matches rel
    d@(GTI.x⊑xᴳ {p = p} x∈) refl eqB (Elab.E-` x∈ᴿ)
    | embedded-lookup B eqB′ x∈ᴸ x∈ᴿ′ | refl =
  ⊢²-retarget
    {q = embedded-⊑ {γ = γ} center-eq source-id matches eqB p}
    (CTI.x⊑x²
      {p = embedded-⊑ {γ = γ} center-eq source-id matches eqB′ p}
      x∈ᴸ x∈ᴿ)

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.ƛ⊑ƛᴳ {pA = pA} N⊑N′) refl refl (Elab.E-ƛ N′ᴱ)
    with compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing N⊑N′)
       | compile-preserves-embedded
      {γ = bind-termᶜ γ
        (embedded-⊑ {γ = γ} center-eq source-id matches refl pA)}
      center-eq source-id matches
      (embedded-∷ {p = pA} refl (embedded-bind-term rel))
      N⊑N′ refl refl N′ᴱ
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.ƛ⊑ƛᴳ {pA = pA} N⊑N′) refl refl (Elab.E-ƛ N′ᴱ)
    | N , N⊢ | N⊑N′² =
  ⊢²-retarget (CTI.ƛ⊑ƛ² N⊑N′²)

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·⊑·ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C A′∼C′)
    refl refl (Elab.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    with Elab.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | Elab.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·⊑·ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C A′∼C′)
    refl refl (Elab.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    | refl | refl
    with compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded center-eq source-id matches rel
      L⊑L′ refl refl L′ᴱ
       | compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded center-eq source-id matches rel
      M⊑M′ refl refl M′ᴱ
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·⊑·ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C A′∼C′)
    refl refl (Elab.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    | refl | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒
          (embedded-⊑ {γ = γ} center-eq source-id matches refl pA)
          (embedded-⊑ {γ = γ} center-eq source-id matches refl pB)}
        L⊑L′²)
      (CTI.cast⊑cast² (symᶜ A∼C) d′ M⊑M′²
        (embedded-⊑ {γ = γ} center-eq source-id matches refl pA)))

compile-preserves-embedded center-eq source-id matches rel
    d@(GTI.·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′)
    refl eqB (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    with Elab.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
compile-preserves-embedded center-eq source-id matches rel
    d@(GTI.·⊑·ᴳ L⊑L′ M⊑M′ A∼C A′∼C′)
    refl eqB (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′) | ()

compile-preserves-embedded center-eq source-id matches rel
    d@(GTI.·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★)
    refl eqB (Elab.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    with Elab.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
compile-preserves-embedded center-eq source-id matches rel
    d@(GTI.·⊑·★ᴳ L⊑L′ M⊑M′ A∼C C′∼★)
    refl eqB (Elab.E-· L′ᴱ M′ᴱ A′∼D′ d′) | ()

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    refl refl (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    with Elab.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    refl refl (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′) | refl
    with compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded center-eq source-id matches rel
      L⊑L′ refl refl L′ᴱ
       | compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded center-eq source-id matches rel
      M⊑M′ refl refl M′ᴱ
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·⊑·★ᴳ {pA = pA} {pB = pB}
      L⊑L′ M⊑M′ A∼C C′∼★)
    refl refl (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒
          (embedded-⊑ {γ = γ} center-eq source-id matches refl pA)
          (embedded-⊑ {γ = γ} center-eq source-id matches refl pB)}
        (CTI.⊑cast² c′ L⊑L′²
          (embedded-⊑ {γ = γ} center-eq source-id matches refl
            (⇒⊑⇒ pA pB))))
      (CTI.cast⊑cast² (symᶜ A∼C) d′ M⊑M′²
        (embedded-⊑ {γ = γ} center-eq source-id matches refl pA)))

compile-preserves-embedded center-eq source-id matches rel
    d@(GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl eqB (Elab.E-· L′ᴱ M′ᴱ A′∼D′ d′)
    with Elab.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
compile-preserves-embedded center-eq source-id matches rel
    d@(GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl eqB (Elab.E-· L′ᴱ M′ᴱ A′∼D′ d′) | ()

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl refl (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    with Elab.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl refl (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′) | refl
    with compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded center-eq source-id matches rel
      L⊑L′ refl refl L′ᴱ
       | compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded center-eq source-id matches rel
      M⊑M′ refl refl M′ᴱ
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.·★⊑·★ᴳ L⊑L′ M⊑M′ C∼★ C′∼★)
    refl refl (Elab.E-·★ L′ᴱ M′ᴱ D′∼★ c′ d′)
    | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI.·⊑·²
      (⊢²-retarget
        {q = ⇒⊑⇒
          (embedded-⊑ {γ = γ} center-eq source-id matches refl ★⊑★)
          (embedded-⊑ {γ = γ} center-eq source-id matches refl ★⊑★)}
        (CTI.cast⊑cast² Elab.dynamic-function-cast c′ L⊑L′²
          (embedded-⊑ {γ = γ} center-eq source-id matches refl
            (⇒⊑⇒ ★⊑★ ★⊑★))))
      (CTI.cast⊑cast² C∼★ d′ M⊑M′²
        (embedded-⊑ {γ = γ} center-eq source-id matches refl ★⊑★)))

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.Λ⊑Λᴳ {p = p} liftδ vV vV′ zero∈A zero∈B V⊑V′)
    refl eqB (Elab.E-Λ zero∈Bᴱ vV′ᴳ vV′ᶜ V′ᴱ)
    rewrite Elab.compile-Λ-term {Σ = Σᴸ}
      {Γ = GTI.srcCtxⁱ _} {zero∈A = zero∈A} vV
      (subst (λ Ψ → _ G.∣ Ψ ⊢ _ ⦂ _)
        (GTI.srcCtxⁱ-lift liftδ)
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      | Elab.compile-context-subst {Σ = store-lift Σᴸ}
      (GTI.srcCtxⁱ-lift liftδ)
      (GTI.gradual-term-imprecision-source-typing V⊑V′) =
  ⊢²-retarget
    (CTI.Λ⊑Λ²
      (compile-value {Σ = store-lift Σᴸ} vV
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      vV′ᶜ body-rel
      (embedded-⊑ {γ = γ} center-eq source-id matches eqB (∀⊑∀ p)))
  where
  center-eq′ = cong Nat.suc center-eq
  source-id′ = sourceId-liftBoth {γ = γ} {center-eq = center-eq}
    X⊑X source-id
  matches′ = matches-liftBoth {γ = γ} matches
  ctx′ = embedded-liftBoth {γ = γ} {center-eq = center-eq}
    {source-id = source-id} {matches = matches} rel liftδ
  target-eq = targetEmbedding-liftBoth {γ = γ} center-eq

  term-eq = cong (λ η → Elab.Grenameᵐ η _)
    (sym target-eq)

  body-eq = trans (ty-all-injective eqB)
    (trans
      (sym (renameᵗ-cong _
        (toRename-keep-eq (targetEmbedding γ center-eq))))
      (cong (λ η → renameᵗ (toRenameᵗ η) _)
        (sym target-eq)))

  body-rel = compile-preserves-embedded center-eq′ source-id′ matches′
    ctx′ V⊑V′ term-eq body-eq V′ᴱ

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.Λ⊑ᴳ {p = p} Anv zero∈A liftδ vV N′⊢ V⊑N′)
    eqM eqB N′ᴱ
    rewrite Elab.compile-Λ-term {Σ = Σᴸ}
      {Γ = GTI.srcCtxⁱ _} {zero∈A = zero∈A} vV
      (subst (λ Ψ → _ G.∣ Ψ ⊢ _ ⦂ _)
        (GTI.srcCtxⁱ-lift liftδ)
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      | Elab.compile-context-subst {Σ = store-lift Σᴸ}
      (GTI.srcCtxⁱ-lift liftδ)
      (GTI.gradual-term-imprecision-source-typing V⊑N′) =
  ⊢²-retarget
    (CTI.Λ⊑² Anv zero∈A
      (compile-value {Σ = store-lift Σᴸ} vV
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      (Elab.elab-cast-typing N′ᴱ) body-rel
      (embedded-⊑ {γ = γ} center-eq source-id matches eqB
        (∀⊑ Anv zero∈A p)))
  where
  center-eq′ = cong Nat.suc center-eq
  source-id′ = sourceId-liftLeft {γ = γ} {center-eq = center-eq}
    source-id
  matches′ = matches-liftLeft {γ = γ} matches
  ctx′ = embedded-liftLeft {γ = γ} {center-eq = center-eq}
    {source-id = source-id} {matches = matches} rel liftδ

  term-eq = trans (cong G.⇑ᵗᴳ eqM)
    (trans
      (Grenameᵐ-skip (targetEmbedding γ center-eq) _)
      (cong (λ η → Elab.Grenameᵐ η _)
        (sym (targetEmbedding-liftLeft {γ = γ} center-eq))))

  type-eq = trans (cong ⇑ᵗ eqB)
    (trans
      (sym (rename-skip (targetEmbedding γ center-eq) _))
      (cong (λ η → renameᵗ (toRenameᵗ η) _)
        (sym (targetEmbedding-liftLeft {γ = γ} center-eq))))

  body-rel = compile-preserves-embedded center-eq′ source-id′ matches′
    ctx′ V⊑N′ term-eq type-eq N′ᴱ

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (Elab.E-[] M′ᴱ eq)
    with Elab.typing-uniqueᴳ
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (Elab.E-[] M′ᴱ eq) | body-eq
    with eq
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (Elab.E-[] M′ᴱ refl) | body-eq | refl
    with compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded center-eq source-id matches rel
      M⊑M′ refl body-eq M′ᴱ
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.[]⊑[]ᴳ {p = p} M⊑M′ q r)
    refl eqB (Elab.E-[] M′ᴱ refl) | body-eq | refl
    | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI.•⊑•²
      (embedded-⊑ {γ = γ} center-eq source-id matches
        body-eq (∀⊑∀ p))
      M⊑M′²
      (embedded-⊑ {γ = γ} center-eq source-id matches refl q)
      (embedded-⊑ {γ = γ} center-eq source-id matches eqB r))

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.[]⊑ᴳ {p = p} {Anv = Anv} {zero∈A = zero∈A}
      M⊑M′ q r)
    eqM eqB M′ᴱ
    with compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded center-eq source-id matches rel
      M⊑M′ eqM eqB M′ᴱ
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.[]⊑ᴳ {p = p} {Anv = Anv} {zero∈A = zero∈A}
      M⊑M′ q r)
    eqM eqB M′ᴱ | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI.•⊑²
      (embedded-⊑ {γ = γ} center-eq source-id matches eqB
        (∀⊑ Anv zero∈A p))
      M⊑M′²
      (embedded-⊑ {γ = γ} center-eq source-id matches refl q)
      (embedded-⊑ {γ = γ} center-eq source-id matches eqB r))

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.κ⊑κᴳ κ) refl eqB (Elab.E-$ .κ) =
  ⊢²-retarget
    {q = embedded-⊑ {γ = γ} center-eq source-id matches eqB
      (GTI.constTy-⊑ _ κ)}
    (CTI.κ⊑κ² κ
      (constTy-embedded {γ = γ} center-eq source-id matches κ))

compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (Elab.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    with Elab.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl L′ᴱ)
      (GTI.gradual-term-imprecision-target-typing L⊑L′)
       | Elab.typing-uniqueᴳ
      (embedded-elab-gradual-typing rel refl refl M′ᴱ)
      (GTI.gradual-term-imprecision-target-typing M⊑M′)
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (Elab.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    | refl | refl
    with compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing L⊑L′)
       | compile-preserves-embedded center-eq source-id matches rel
      L⊑L′ refl refl L′ᴱ
       | compile {Σ = Σᴸ}
      (GTI.gradual-term-imprecision-source-typing M⊑M′)
       | compile-preserves-embedded center-eq source-id matches rel
      M⊑M′ refl refl M′ᴱ
compile-preserves-embedded {Σᴸ = Σᴸ} {γ = γ}
    center-eq source-id matches rel
    (GTI.⊕⊑⊕ᴳ op L⊑L′ A∼arg A′∼arg M⊑M′
      B∼arg B′∼arg)
    refl eqB
    (Elab.E-⊕ .op L′ᴱ A′∼arg′ c′ M′ᴱ B′∼arg′ d′)
    | refl | refl | L , L⊢ | L⊑L′² | M , M⊢ | M⊑M′² =
  ⊢²-retarget
    (CTI.⊕⊑⊕² op
      (CTI.cast⊑cast² A∼arg c′ L⊑L′² argᶜ)
      (CTI.cast⊑cast² B∼arg d′ M⊑M′² argᶜ)
      resultᶜ)
  where
  argᶜ = embedded-⊑ {γ = γ} center-eq source-id matches
    (primArgTy-target {γ = γ} center-eq op)
    (refl⊑ (primArgTy op))

  resultᶜ = embedded-⊑ {γ = γ} center-eq source-id matches
    (primResultTy-target {γ = γ} center-eq op)
    (GTI.primResultTy-⊑ _ op)


------------------------------------------------------------------------
-- Ordinary compilation preserves gradual term imprecision
------------------------------------------------------------------------

compile-preserves-imprecision-statement : Set
compile-preserves-imprecision-statement =
  ∀ {Δ} {μ : ImpEnv Δ} {δ : GTI.CtxImp μ}
    {M M′ : GTerm Δ} {A B p}
  → (M⊑M′ : μ GTI.∣ δ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → initialContextWorld δ ⊢²
      proj₁ (compile {Σ = emptyStoreᶜ Δ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ proj₁ (compile {Σ = emptyStoreᶜ Δ}
        (GTI.gradual-term-imprecision-target-typing M⊑M′))
      ∶ initialContext-⊑ δ p


compile-preserves-imprecision : compile-preserves-imprecision-statement
compile-preserves-imprecision {δ = δ} {M′ = M′} {B = B} {p = p}
    M⊑M′ =
  ⊢²-retarget {q = initialContext-⊑ δ p}
    (compile-preserves-embedded
      {γ = initialContextWorld δ}
      (initialContext-center δ)
      (initialContext-source-id δ)
      (initialContext-matches δ)
      (initialEmbeddedCtx δ)
      M⊑M′ target-term-id target-type-id
      (Elab.compile-elab
        (GTI.gradual-term-imprecision-target-typing M⊑M′)))
  where
  target-id = initialContext-target-id δ

  target-term-id : M′ ≡ Elab.Grenameᵐ
      (targetEmbedding (initialContextWorld δ) (initialContext-center δ)) M′
  target-term-id = sym (Grenameᵐ-pointwise-id
    (targetEmbedding (initialContextWorld δ) (initialContext-center δ))
    M′ target-id)

  target-type-id : B ≡ renameᵗ
      (toRenameᵗ
        (targetEmbedding (initialContextWorld δ)
          (initialContext-center δ))) B
  target-type-id = sym (renameᵗ-pointwise-id
    (toRenameᵗ
      (targetEmbedding (initialContextWorld δ) (initialContext-center δ)))
    B target-id)
