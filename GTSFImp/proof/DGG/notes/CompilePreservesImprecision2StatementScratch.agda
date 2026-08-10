module CompilePreservesImprecision2StatementScratch where

-- Scratch statement check for proof.DGG.CompilePreservesImprecision2.

open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-empty)
open import Consistency using (_↪ᵗ_; id↪ᵗ; toRenameᵗ)
open import Imprecision
open import GradualTerms using (GTerm)
import GradualTerms as G
import GradualTermImprecision as GTI
open import Compile using (compile)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (World; world; _∣_⊢²_⊑_∶_)
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.Imprecision as PI
open import proof.TypeInTermSubst using
  (renameᵗ-pointwise-id; toRename-id-eq)

initialWorld : ∀ {Δ} → ImpEnv Δ → TyStore Δ → World Δ Δ Δ
initialWorld μ Σ = world id↪ᵗ id↪ᵗ μ Σ Σ

initialWorld-ηᴸ : ∀ {Δ} (μ : ImpEnv Δ) (Σ : TyStore Δ)
  → CTI2.ηᴸʷ (initialWorld μ Σ) ≡ id↪ᵗ
initialWorld-ηᴸ μ Σ = refl

initialWorld-ηᴿ : ∀ {Δ} (μ : ImpEnv Δ) (Σ : TyStore Δ)
  → CTI2.ηᴿʷ (initialWorld μ Σ) ≡ id↪ᵗ
initialWorld-ηᴿ μ Σ = refl

initial-embedᴸ : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (A : Ty Δ)
  → CTI2.embedᴸ (initialWorld μ Σ) A ≡ A
initial-embedᴸ A =
  renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq

initial-embedᴿ : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (A : Ty Δ)
  → CTI2.embedᴿ (initialWorld μ Σ) A ≡ A
initial-embedᴿ A =
  renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq

initial-⊑ : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ} {A B : Ty Δ}
  → μ ⊢ A ⊑ B
  → A CTI2.⊑ᵂ⟨ initialWorld μ Σ ⟩ B
initial-⊑ {μ = μ} {Σ = Σ} {A = A} {B = B} p =
  subst≡ (λ L → μ ⊢ L ⊑ CTI2.embedᴿ (initialWorld μ Σ) B)
    (sym (initial-embedᴸ {μ = μ} {Σ = Σ} A))
    (subst≡ (λ R → μ ⊢ A ⊑ R)
      (sym (initial-embedᴿ {μ = μ} {Σ = Σ} B)) p)

initialCtx : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → GTI.CtxImp μ
  → CTI2.CtxImp (initialWorld μ Σ)
initialCtx [] = []
initialCtx {Σ = Σ} (GTI.ctx-imp A B p ∷ γ) =
  CTI2.ctx-imp A B (initial-⊑ {Σ = Σ} p) ∷
    initialCtx {Σ = Σ} γ

compile-preserves-imprecision²-statement : Set
compile-preserves-imprecision²-statement =
  ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
    {γ : GTI.CtxImp μ} {M M′ : GTerm Δ} {A B p}
  → (M⊑M′ : μ GTI.∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → initialWorld μ Σ ∣ initialCtx {Σ = Σ} γ ⊢²
      proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-target-typing M⊑M′))
      ∶ initial-⊑ {Σ = Σ} p

polyIdᴳ : GTerm 0
polyIdᴳ = G.Λ (G.ƛ ＇ 0 ⇒ G.` 0)

polyId⊑polyIdᴳ :
  idᵐ GTI.∣ [] ⊢ᴳ polyIdᴳ ⊑ polyIdᴳ
    ⦂ `∀ Ex.X⇒X ⊑ `∀ Ex.X⇒X ∶ ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)
polyId⊑polyIdᴳ =
  GTI.Λ⊑Λᴳ GTI.lift-[] (G.ƛ ＇ 0 ⇒ G.` 0)
    (G.ƛ ＇ 0 ⇒ G.` 0)
    (∈-fun-left var-∈) (∈-fun-left var-∈)
    (GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ))

polyId-validation :
  initialWorld idᵐ store-empty
    ∣ initialCtx {Σ = store-empty} [] ⊢²
    proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-source-typing polyId⊑polyIdᴳ))
    ⊑ proj₁ (compile {Σ = store-empty}
      (GTI.gradual-term-imprecision-target-typing polyId⊑polyIdᴳ))
    ∶ initial-⊑ {Σ = store-empty} (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))
polyId-validation =
  subst≡
    (λ q → initialWorld idᵐ store-empty ∣ [] ⊢² Ex.polyId
      ⊑ Ex.polyId ∶ q)
    (PI.⊑-unique Ex2.example12-∀⊑∀
      (initial-⊑ {Σ = store-empty}
        (∀⊑∀ (⇒⊑⇒ X⊑X X⊑X))))
    Ex2.polyId-refl²
