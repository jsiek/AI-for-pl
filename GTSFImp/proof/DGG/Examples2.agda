module proof.DGG.Examples2 where

-- File Charter:
--   * Collects the three running DGG version-2 imprecision examples.
--   * Reuses ExampleTerms and OneStep to record reduction traces for each
--     more precise / more imprecise pair.
--   * States the checkpoint obligations showing that the more imprecise side
--     simulates each reduction step of the more precise side under the
--     version-2 cast-term imprecision relation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
import TermCtx as T
open import TermCtx using (TermCtx)
import Consistency as C
open C using
  (_⊢_∼_; _↪ᵗ_; empty; keep; skip; id; _!; ？_; _↦_; gen_;
   renameEnv∼; wk↪ᵗ; idᶜ; genᵐ)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑_; _⊢↓_; id↑; `∀↑_; unseal; seal; _↦↑_;
   _↦↓_; ⊢↑-id; ⊢↑-∀; ⊢↑-unseal; ⊢↑-⇒; ⊢↓-seal; ⊢↓-⇒)
open import Imprecision using
  (ImpEnv; VarImp; _⊢_⊑_; X⊑X; X⊑★; ★⊑★; ι⊑ι; ⇒⊑⇒; ∀⊑∀; ∀⊑; ι⊑★)
open import Primitives using (κℕ)
open import CastTerms
open import Reduction
open import Eval using (step?; value?)
open import proof.ImprecisionConsistency using (refl⊑; toRenameᵗ-injective)
import proof.DGG.ExampleTerms as Ex
import proof.DGG.OneStep as Step
open Step
  using (Δ′; change; next; reduction)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.Example12Worlds as Ex12
open CTX using
  (World;
   emptyʷ;
   lift-bothʷ;
   bind-leftʷ;
   bind-bothʷ;
   bind-both-starʷ;
   _⊑ᵂ⟨_⟩_;
   CtxImp;
   ctx-imp;
   _∋ʷ_⦂_;
   Zʷ;
   Sʷ;
   LiftCtx;
   lift-[];
   lift-∷;
   liftWorldBoth)
open CTI2 using
  (_∣_⊢²_⊑_∶_;
   x⊑x²;
   ƛ⊑ƛ²;
   ·⊑·²;
   Λ⊑Λ²;
   •⊑•²;
   κ⊑κ²;
   cast⊑cast²;
   ⊑cast²;
   reveal⊑reveal²)

------------------------------------------------------------------------
-- Local reflexivity for the version-2 relation
------------------------------------------------------------------------

id↪ᵗ : ∀ {Δ} → Δ ↪ᵗ Δ
id↪ᵗ {zero} = empty
id↪ᵗ {suc Δ} = keep id↪ᵗ

reflWorldWithEmbedding : ∀ {Δ} (Σ : TyStore Δ)
  → Σ[ W ∈ World Δ Δ Δ ] CTX.ηᴸʷ W ≡ CTX.ηᴿʷ W
reflWorldWithEmbedding store-empty = emptyʷ , refl
reflWorldWithEmbedding (store-lift Σ)
    with reflWorldWithEmbedding Σ
reflWorldWithEmbedding (store-lift Σ) | W , aligned =
  lift-bothʷ X⊑X W , cong keep aligned
reflWorldWithEmbedding (store-bind Σ A)
    with reflWorldWithEmbedding Σ
reflWorldWithEmbedding (store-bind Σ A) | W , aligned =
  bind-bothʷ W A A
    (CTX.imprecision-cong refl
      (cong (λ η → renameᵗ (C.toRenameᵗ η) A) aligned)
      (refl⊑ (CTX.embedᴸ W A))) ,
  cong keep aligned

reflWorld : ∀ {Δ} → TyStore Δ → World Δ Δ Δ
reflWorld Σ with reflWorldWithEmbedding Σ
reflWorld Σ | W , aligned = W

reflWorld-η : ∀ {Δ} (Σ : TyStore Δ)
  → CTX.ηᴸʷ (reflWorld Σ) ≡ CTX.ηᴿʷ (reflWorld Σ)
reflWorld-η Σ with reflWorldWithEmbedding Σ
reflWorld-η Σ | W , aligned = aligned

reflTy² : ∀ {Δ} {Σ : TyStore Δ} (A : Ty Δ)
  → A ⊑ᵂ⟨ reflWorld Σ ⟩ A
reflTy² {Σ = Σ} A =
  CTX.imprecision-cong refl
    (cong (λ η → renameᵗ (C.toRenameᵗ η) A) (reflWorld-η Σ))
    (refl⊑ (CTX.embedᴸ (reflWorld Σ) A))

ℕ⊑ℕ² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ)
ℕ⊑ℕ² = ι⊑ι

ℕ⊑★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (‵ `ℕ) ⊑ᵂ⟨ W ⟩ ★
ℕ⊑★² = ι⊑★

ℕ⇒ℕ⊑ℕ⇒ℕ² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → ((‵ `ℕ) ⇒ (‵ `ℕ)) ⊑ᵂ⟨ W ⟩ ((‵ `ℕ) ⇒ (‵ `ℕ))
ℕ⇒ℕ⊑ℕ⇒ℕ² {W = W} = ⇒⊑⇒ (ℕ⊑ℕ² {W = W}) (ℕ⊑ℕ² {W = W})

★⇒★⊑★⇒★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (★ ⇒ ★) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
★⇒★⊑★⇒★² = ⇒⊑⇒ ★⊑★ ★⊑★

ℕ⇒ℕ⊑★⇒★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → ((‵ `ℕ) ⇒ (‵ `ℕ)) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
ℕ⇒ℕ⊑★⇒★² {W = W} = ⇒⊑⇒ (ℕ⊑★² {W = W}) (ℕ⊑★² {W = W})

∀X⇒X⊑★⇒★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → `∀ (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ W ⟩ (★ ⇒ ★)
∀X⇒X⊑★⇒★² =
  ∀⊑ nonvar-fun (∈-fun-left var-∈)
    (⇒⊑⇒ (Imprecision.X⊑★ refl) (Imprecision.X⊑★ refl))

X⊑X-lift² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → ＇ Fin.zero ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ ＇ Fin.zero
X⊑X-lift² = Imprecision.X⊑X {X = Fin.zero}

X⇒X⊑X⇒X-lift² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (＇ Fin.zero ⇒ ＇ Fin.zero)
      ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩
    (＇ Fin.zero ⇒ ＇ Fin.zero)
X⇒X⊑X⇒X-lift² {W = W} =
  ⇒⊑⇒ (X⊑X-lift² {W = W}) (X⊑X-lift² {W = W})

∀X⇒X⊑∀X⇒X² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → `∀ (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ W ⟩
    `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
∀X⇒X⊑∀X⇒X² {W = W} = ∀⊑∀ (X⇒X⊑X⇒X-lift² {W = W})

------------------------------------------------------------------------
-- Example 1: Cambridge26 Example 12
------------------------------------------------------------------------

example12-more-precise : Term 0
example12-more-precise = Ex.example12-left

example12-more-imprecise : Term 0
example12-more-imprecise = Ex.example12-right

example12-more-precise-reduction :
  example12-more-precise —↠[ Ex.left-changes ] Ex.left-final
example12-more-precise-reduction = Ex.example12-left-reduction

example12-more-imprecise-reduction :
  example12-more-imprecise —↠[ Ex.right-changes ] Ex.right-final
example12-more-imprecise-reduction = Ex.example12-right-reduction

example12-∀⊑⇒★ :
  `∀ Ex.X⇒X ⊑ᵂ⟨ reflWorld store-empty ⟩ (★ ⇒ ★)
example12-∀⊑⇒★ =
  ∀⊑ nonvar-fun (∈-fun-left var-∈)
    (⇒⊑⇒ (Imprecision.X⊑★ refl) (Imprecision.X⊑★ refl))

example12-∀⊑∀ :
  `∀ Ex.X⇒X ⊑ᵂ⟨ reflWorld store-empty ⟩ `∀ Ex.X⇒X
example12-∀⊑∀ = ∀⊑∀ (⇒⊑⇒ X⊑X X⊑X)

polyId-var⊑ :
  ＇ Fin.zero ⊑ᵂ⟨ liftWorldBoth X⊑X (reflWorld store-empty) ⟩
    ＇ Fin.zero
polyId-var⊑ = X⊑X

polyId-body⊑ :
  Ex.X⇒X ⊑ᵂ⟨ liftWorldBoth X⊑X (reflWorld store-empty) ⟩ Ex.X⇒X
polyId-body⊑ = ⇒⊑⇒ polyId-var⊑ polyId-var⊑

polyId-body-refl² :
  liftWorldBoth X⊑X (reflWorld store-empty)
    ∣ [] ⊢² ƛ (` 0) ⊑ ƛ (` 0) ∶ polyId-body⊑
polyId-body-refl² = ƛ⊑ƛ² (x⊑x² Zʷ)

polyId-refl² :
  reflWorld store-empty ∣ [] ⊢² Ex.polyId ⊑ Ex.polyId ∶
    example12-∀⊑∀
polyId-refl² =
  Λ⊑Λ² lift-[] (ƛ (` 0)) (ƛ (` 0))
    polyId-body-refl² example12-∀⊑∀

polyId-refl²ʷ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → W ∣ [] ⊢² Λ (ƛ (` 0)) ⊑ Λ (ƛ (` 0)) ∶
      ∀X⇒X⊑∀X⇒X² {W = W}
polyId-refl²ʷ {W = W} =
  Λ⊑Λ² lift-[] (ƛ (` 0)) (ƛ (` 0))
    (ƛ⊑ƛ² {pA = X⊑X-lift² {W = W}}
      {pB = X⊑X-lift² {W = W}}
      (x⊑x² {p = X⊑X-lift² {W = W}} Zʷ))
    (∀X⇒X⊑∀X⇒X² {W = W})

example12-ℕ⇒ℕ⊑ℕ⇒ℕ :
  (Ex.X⇒X [ Ex.ℕᵗ ]ᵗ)
    ⊑ᵂ⟨ reflWorld store-empty ⟩
      (Ex.X⇒X [ Ex.ℕᵗ ]ᵗ)
example12-ℕ⇒ℕ⊑ℕ⇒ℕ =
  ℕ⇒ℕ⊑ℕ⇒ℕ² {W = reflWorld store-empty}

example12-ℕ⊑ℕ₀ :
  (‵ `ℕ) ⊑ᵂ⟨ reflWorld store-empty ⟩ (‵ `ℕ)
example12-ℕ⊑ℕ₀ = ℕ⊑ℕ² {W = reflWorld store-empty}

example12-ℕ⊑ℕ-X :
  (‵ `ℕ) ⊑ᵂ⟨ Ex12.example12-world-X ⟩ (‵ `ℕ)
example12-ℕ⊑ℕ-X = ℕ⊑ℕ² {W = Ex12.example12-world-X}

example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X :
  ((‵ `ℕ) ⇒ (‵ `ℕ)) ⊑ᵂ⟨ Ex12.example12-world-X ⟩
    ((‵ `ℕ) ⇒ (‵ `ℕ))
example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X =
  ℕ⇒ℕ⊑ℕ⇒ℕ² {W = Ex12.example12-world-X}

example12-initial-poly :
  reflWorld store-empty ∣ [] ⊢² Ex.polyId
    ⊑ ((Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩) ⟨ Ex.να-α!→α? ⟩)
    ∶ example12-∀⊑∀
example12-initial-poly =
  ⊑cast² Ex.να-α!→α?
    (⊑cast² Ex.ν̅α-α♯→α♭ polyId-refl² example12-∀⊑⇒★)
    example12-∀⊑∀

example12-checkpoint₀ :
  reflWorld store-empty ∣ [] ⊢² Ex.left₀ ⊑ Ex.right₀ ∶ example12-ℕ⊑ℕ₀
example12-checkpoint₀ =
  ·⊑·²
    (•⊑•² example12-∀⊑∀ example12-initial-poly example12-ℕ⊑ℕ₀
      example12-ℕ⇒ℕ⊑ℕ⇒ℕ)
    (κ⊑κ² (κℕ 7) example12-ℕ⊑ℕ₀)

example12-checkpoint₄ :
  Ex12.example12-world-X ∣ [] ⊢² Ex.left-final ⊑ Ex.right-final ∶
    example12-ℕ⊑ℕ-X
example12-checkpoint₄ = κ⊑κ² (κℕ 7) example12-ℕ⊑ℕ-X

example12-rebase-Z-to-Y :
  CTX.WorldInvariants Ex12.example12-ηᴸ-Y Ex12.example12-ηᴿ
    Ex12.example12-imp-env Ex12.example12-source-store
    Ex12.example12-target-store
  → ⊥
example12-rebase-Z-to-Y =
  Ex12.violates-invariants Ex12.example12-world-Y

example12-target-Y-reveal :
  Conv↑ 3
    (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
    (＇ (Fin.suc (Fin.suc Fin.zero))
      ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
example12-target-Y-reveal =
  seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))) ↦↑
  unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero)))

example12-target-Z-reveal :
  Conv↑ 3
    (＇ (Fin.suc (Fin.suc Fin.zero))
      ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    (★ ⇒ ★)
example12-target-Z-reveal =
  seal (Fin.suc (Fin.suc Fin.zero)) ★ ↦↑
  unseal (Fin.suc (Fin.suc Fin.zero)) ★

example12-source-X-reveal :
  Conv↑ 1 (＇ Fin.zero ⇒ ＇ Fin.zero) (‵ `ℕ ⇒ ‵ `ℕ)
example12-source-X-reveal =
  seal Fin.zero (‵ `ℕ) ↦↑ unseal Fin.zero (‵ `ℕ)

example12-target-X-reveal :
  Conv↑ 3 (＇ Fin.zero ⇒ ＇ Fin.zero) (‵ `ℕ ⇒ ‵ `ℕ)
example12-target-X-reveal =
  seal Fin.zero (‵ `ℕ) ↦↑ unseal Fin.zero (‵ `ℕ)

example12-source-X-seal : Conv↓ 1 (‵ `ℕ) (＇ Fin.zero)
example12-source-X-seal = seal Fin.zero (‵ `ℕ)

example12-target-X-seal : Conv↓ 3 (‵ `ℕ) (＇ Fin.zero)
example12-target-X-seal = seal Fin.zero (‵ `ℕ)

example12-source-X-unseal : Conv↑ 1 (＇ Fin.zero) (‵ `ℕ)
example12-source-X-unseal = unseal Fin.zero (‵ `ℕ)

example12-target-X-unseal : Conv↑ 3 (＇ Fin.zero) (‵ `ℕ)
example12-target-X-unseal = unseal Fin.zero (‵ `ℕ)

example12-target-Z-seal :
  Conv↓ 3 ★ (＇ (Fin.suc (Fin.suc Fin.zero)))
example12-target-Z-seal =
  seal (Fin.suc (Fin.suc Fin.zero)) ★

example12-target-Y-seal :
  Conv↓ 3 (＇ (Fin.suc (Fin.suc Fin.zero))) (＇ (Fin.suc Fin.zero))
example12-target-Y-seal =
  seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero)))

example12-target-Y-unseal :
  Conv↑ 3 (＇ (Fin.suc Fin.zero)) (＇ (Fin.suc (Fin.suc Fin.zero)))
example12-target-Y-unseal =
  unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero)))

example12-target-Z-unseal :
  Conv↑ 3 (＇ (Fin.suc (Fin.suc Fin.zero))) ★
example12-target-Z-unseal =
  unseal (Fin.suc (Fin.suc Fin.zero)) ★

example12-target-Y-reveal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↑[ just (Fin.suc Fin.zero) ]
    example12-target-Y-reveal
example12-target-Y-reveal-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both
    (Conv.⊢↓-sealˣ Ex12.example12-target-Y∋)
    (Conv.⊢↑-unsealˣ Ex12.example12-target-Y∋)

example12-target-Z-reveal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↑[ just (Fin.suc (Fin.suc Fin.zero)) ]
    example12-target-Z-reveal
example12-target-Z-reveal-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both
    (Conv.⊢↓-sealˣ Ex12.example12-target-Z∋)
    (Conv.⊢↑-unsealˣ Ex12.example12-target-Z∋)

example12-source-X-reveal-⊢ :
  Ex12.example12-source-store ⊢↑ example12-source-X-reveal
example12-source-X-reveal-⊢ =
  ⊢↑-⇒ (⊢↓-seal Ex12.example12-source-X∋)
    (⊢↑-unseal Ex12.example12-source-X∋)

example12-target-X-reveal-⊢ :
  Ex12.example12-target-store ⊢↑ example12-target-X-reveal
example12-target-X-reveal-⊢ =
  ⊢↑-⇒ (⊢↓-seal Ex12.example12-target-X∋)
    (⊢↑-unseal Ex12.example12-target-X∋)

example12-source-X-seal-⊢ :
  Ex12.example12-source-store ⊢↓ example12-source-X-seal
example12-source-X-seal-⊢ = ⊢↓-seal Ex12.example12-source-X∋

example12-target-X-seal-⊢ :
  Ex12.example12-target-store ⊢↓ example12-target-X-seal
example12-target-X-seal-⊢ = ⊢↓-seal Ex12.example12-target-X∋

example12-source-X-seal-⊢ˣ :
  Ex12.example12-source-store Conv.⊢↓[ just Fin.zero ] example12-source-X-seal
example12-source-X-seal-⊢ˣ =
  Conv.⊢↓-sealˣ Ex12.example12-source-X∋

example12-target-X-seal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↓[ just Fin.zero ] example12-target-X-seal
example12-target-X-seal-⊢ˣ =
  Conv.⊢↓-sealˣ Ex12.example12-target-X∋

example12-source-X-unseal-⊢ :
  Ex12.example12-source-store ⊢↑ example12-source-X-unseal
example12-source-X-unseal-⊢ = ⊢↑-unseal Ex12.example12-source-X∋

example12-target-X-unseal-⊢ :
  Ex12.example12-target-store ⊢↑ example12-target-X-unseal
example12-target-X-unseal-⊢ = ⊢↑-unseal Ex12.example12-target-X∋

example12-source-X-unseal-⊢ˣ :
  Ex12.example12-source-store Conv.⊢↑[ just Fin.zero ] example12-source-X-unseal
example12-source-X-unseal-⊢ˣ =
  Conv.⊢↑-unsealˣ Ex12.example12-source-X∋

example12-target-X-unseal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↑[ just Fin.zero ] example12-target-X-unseal
example12-target-X-unseal-⊢ˣ =
  Conv.⊢↑-unsealˣ Ex12.example12-target-X∋

example12-source-X-reveal-⊢ˣ :
  Ex12.example12-source-store Conv.⊢↑[ just Fin.zero ] example12-source-X-reveal
example12-source-X-reveal-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both example12-source-X-seal-⊢ˣ
    example12-source-X-unseal-⊢ˣ

example12-target-X-reveal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↑[ just Fin.zero ] example12-target-X-reveal
example12-target-X-reveal-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both example12-target-X-seal-⊢ˣ
    example12-target-X-unseal-⊢ˣ

example12-target-Z-seal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↓[ just (Fin.suc (Fin.suc Fin.zero)) ]
    example12-target-Z-seal
example12-target-Z-seal-⊢ˣ =
  Conv.⊢↓-sealˣ Ex12.example12-target-Z∋

example12-target-Y-seal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↓[ just (Fin.suc Fin.zero) ]
    example12-target-Y-seal
example12-target-Y-seal-⊢ˣ =
  Conv.⊢↓-sealˣ Ex12.example12-target-Y∋

example12-target-Y-unseal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↑[ just (Fin.suc Fin.zero) ]
    example12-target-Y-unseal
example12-target-Y-unseal-⊢ˣ =
  Conv.⊢↑-unsealˣ Ex12.example12-target-Y∋

example12-target-Z-unseal-⊢ˣ :
  Ex12.example12-target-store Conv.⊢↑[ just (Fin.suc (Fin.suc Fin.zero)) ]
    example12-target-Z-unseal
example12-target-Z-unseal-⊢ˣ =
  Conv.⊢↑-unsealˣ Ex12.example12-target-Z∋

example12-X-function-to-star :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ Ex12.example12-world-X ⟩
    (★ ⇒ ★)
example12-X-function-to-star = ⇒⊑⇒ (Imprecision.X⊑★ refl)
  (Imprecision.X⊑★ refl)

example12-target-id★↦id★ :
  renameEnv∼ wk↪ᵗ
    (applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))
    ⊢ (★ ⇒ ★) ∼ (★ ⇒ ★)
example12-target-id★↦id★ = id ★ ↦ id ★

example12-target-X?↦X? :
  genᵐ
    (applyEnv (bind (＇ Fin.zero))
      (applyEnv (bind ★) (idᶜ {Δ = 0})))
    ⊢ (★ ⇒ ★) ∼ (＇ Fin.zero ⇒ ＇ Fin.zero)
example12-target-X?↦X? =
  (id {μ = C.flipᵐ
      (genᵐ
        (applyEnv (bind (＇ Fin.zero))
          (applyEnv (bind ★) (idᶜ {Δ = 0}))))}
    (＇ Fin.zero) !) ↦
  ？_ {μ =
      genᵐ
        (applyEnv (bind (＇ Fin.zero))
          (applyEnv (bind ★) (idᶜ {Δ = 0})))}
    (id (＇ Fin.zero))

example12-target-X! :
  C.flipᵐ
    (genᵐ
      (applyEnv (bind (＇ Fin.zero))
        (applyEnv (bind ★) (idᶜ {Δ = 0}))))
    ⊢ ＇ Fin.zero ∼ ★
example12-target-X! = id (＇ Fin.zero) !

example12-target-id★ :
  renameEnv∼ wk↪ᵗ
    (applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))
    ⊢ ★ ∼ ★
example12-target-id★ = id ★

example12-target-★?X :
  genᵐ
    (applyEnv (bind (＇ Fin.zero))
      (applyEnv (bind ★) (idᶜ {Δ = 0})))
    ⊢ ★ ∼ ＇ Fin.zero
example12-target-★?X = ？ (id (＇ Fin.zero))

-- These intermediate CTI checkpoints record the former re-parking parse.
-- Their two premise worlds are now explicit impossible parameters: the raw
-- snapshots remain regression fixtures, while no invalid World is minted.
module RejectedExample12Intermediate
    (invY : CTX.WorldInvariants Ex12.example12-ηᴸ-Y
      Ex12.example12-ηᴿ Ex12.example12-imp-env
      Ex12.example12-source-store Ex12.example12-target-store)
    (invZ : CTX.WorldInvariants Ex12.example12-ηᴸ-Z
      Ex12.example12-ηᴿ Ex12.example12-imp-env
      Ex12.example12-source-store Ex12.example12-target-store) where

  impossibleY : ⊥
  impossibleY = Ex12.violates-invariants Ex12.example12-world-Y invY

  impossibleZ : ⊥
  impossibleZ = Ex12.violates-invariants Ex12.example12-world-Z invZ

  rejected : ∀ {A : Set} → A
  rejected = ⊥-elim impossibleY

  example12-world-Y : World 1 3 3
  example12-world-Y = ⊥-elim impossibleY

  example12-world-Z : World 1 3 3
  example12-world-Z = ⊥-elim impossibleZ

  example12-Z-representation :
    CTX.StoreRepImp example12-world-Z Fin.zero
      (Fin.suc (Fin.suc Fin.zero))
  example12-Z-representation =
    rejected

  example12-Y-representation :
    CTX.StoreRepImp example12-world-Y Fin.zero (Fin.suc Fin.zero)
  example12-Y-representation =
    rejected

  example12-rebase-X-to-Z-live :
    CTX.RebaseAt Ex12.example12-world-X example12-world-Z
      Fin.zero (Fin.suc (Fin.suc Fin.zero))
  example12-rebase-X-to-Z-live =
    rejected

  example12-rebase-Z-to-Y-live :
    CTX.RebaseAt example12-world-Z example12-world-Y
      Fin.zero (Fin.suc Fin.zero)
  example12-rebase-Z-to-Y-live =
    rejected

  example12-Y-var⊑ :
    ＇ Fin.zero ⊑ᵂ⟨ example12-world-Y ⟩ ＇ (Fin.suc Fin.zero)
  example12-Y-var⊑ = rejected

  example12-Y-function-local :
    (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ example12-world-Y ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
  example12-Y-function-local = rejected

  example12-Z-var⊑ :
    ＇ Fin.zero ⊑ᵂ⟨ example12-world-Z ⟩
      ＇ (Fin.suc (Fin.suc Fin.zero))
  example12-Z-var⊑ = rejected

  example12-Z-function-local :
    (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ example12-world-Z ⟩
      (＇ (Fin.suc (Fin.suc Fin.zero))
        ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
  example12-Z-function-local = rejected

  example12-X-var⊑ :
    ＇ Fin.zero ⊑ᵂ⟨ Ex12.example12-world-X ⟩ ＇ Fin.zero
  example12-X-var⊑ = X⊑X

  example12-X-var-to-star :
    ＇ Fin.zero ⊑ᵂ⟨ Ex12.example12-world-X ⟩ ★
  example12-X-var-to-star = Imprecision.X⊑★ refl

  example12-rebase-X-same :
    CTX.RebaseAt Ex12.example12-world-X Ex12.example12-world-X
      Fin.zero Fin.zero
  example12-rebase-X-same =
    CTX.sameWorldRebaseAt refl Ex12.example12-X-representation

  example12-X-function-local :
    (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ Ex12.example12-world-X ⟩
      (＇ Fin.zero ⇒ ＇ Fin.zero)
  example12-X-function-local = ⇒⊑⇒ example12-X-var⊑ example12-X-var⊑

  example12-lambda-Y :
    example12-world-Y ∣ [] ⊢² ƛ (` 0) ⊑ ƛ (` 0) ∶
      example12-Y-function-local
  example12-lambda-Y =
    rejected

  example12-lambda-Z :
    example12-world-Z ∣ [] ⊢² ƛ (` 0)
      ⊑ (ƛ (` 0)) ↑ example12-target-Y-reveal ∶
        example12-Z-function-local
  example12-lambda-Z =
    rejected

  example12-lambda-star :
    Ex12.example12-world-X ∣ [] ⊢² ƛ (` 0)
      ⊑ ((ƛ (` 0)) ↑ example12-target-Y-reveal)
          ↑ example12-target-Z-reveal ∶
        example12-X-function-to-star
  example12-lambda-star =
    rejected

  example12-lambda-star-id :
    Ex12.example12-world-X ∣ [] ⊢² ƛ (` 0)
      ⊑ (((ƛ (` 0)) ↑ example12-target-Y-reveal)
          ↑ example12-target-Z-reveal)
          ⟨ example12-target-id★↦id★ ⟩ ∶
        example12-X-function-to-star
  example12-lambda-star-id =
    rejected

  example12-lambda-X :
    Ex12.example12-world-X ∣ [] ⊢² ƛ (` 0)
      ⊑ ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
          ↑ example12-target-Z-reveal)
          ⟨ example12-target-id★↦id★ ⟩)
          ⟨ example12-target-X?↦X? ⟩ ∶
        example12-X-function-local
  example12-lambda-X =
    rejected

  example12-function-checkpoint₁ :
    Ex12.example12-world-X ∣ [] ⊢²
      (ƛ (` 0)) ↑ example12-source-X-reveal
      ⊑ (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
          ↑ example12-target-Z-reveal)
          ⟨ example12-target-id★↦id★ ⟩)
          ⟨ example12-target-X?↦X? ⟩)
          ↑ example12-target-X-reveal ∶
        example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X
  example12-function-checkpoint₁ =
    rejected

  example12-checkpoint₁ :
    Ex12.example12-world-X ∣ [] ⊢² Ex.left₁ ⊑ Ex.right₃ ∶
      example12-ℕ⊑ℕ-X
  example12-checkpoint₁ =
    rejected

  example12-sealed-const :
    Ex12.example12-world-X ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ ($ (κℕ 7)) ↓ example12-target-X-seal ∶
        example12-X-var⊑
  example12-sealed-const =
    CTI2.conceal⊑conceal²
      CTX.impEnvMono-refl example12-rebase-X-same CTX.same-[]
      example12-source-X-seal-⊢ˣ example12-target-X-seal-⊢ˣ
      (κ⊑κ² (κℕ 7) example12-ℕ⊑ℕ-X) example12-X-var⊑

  example12-application-checkpoint₂ :
    Ex12.example12-world-X ∣ [] ⊢²
      (ƛ (` 0)) · (($ (κℕ 7)) ↓ example12-source-X-seal)
      ⊑ (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
          ↑ example12-target-Z-reveal)
          ⟨ example12-target-id★↦id★ ⟩)
          ⟨ example12-target-X?↦X? ⟩)
          · (($ (κℕ 7)) ↓ example12-target-X-seal) ∶
        example12-X-var⊑
  example12-application-checkpoint₂ =
    rejected

  example12-checkpoint₂ :
    Ex12.example12-world-X ∣ [] ⊢² Ex.left₂ ⊑ Ex.right₄ ∶
      example12-ℕ⊑ℕ-X
  example12-checkpoint₂ =
    rejected

  example12-target-X!-checkpoint₃ :
    Ex12.example12-world-X ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ (($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩ ∶
        example12-X-var-to-star
  example12-target-X!-checkpoint₃ =
    ⊑cast² example12-target-X! example12-sealed-const
      example12-X-var-to-star

  example12-target-Z-seal-checkpoint₃ :
    example12-world-Z ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ ((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal ∶
        example12-Z-var⊑
  example12-target-Z-seal-checkpoint₃ =
    rejected

  example12-target-Y-seal-checkpoint₃ :
    example12-world-Y ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal)
          ↓ example12-target-Y-seal ∶
        example12-Y-var⊑
  example12-target-Y-seal-checkpoint₃ =
    rejected

  example12-target-Y-unseal-checkpoint₃ :
    example12-world-Z ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal)
          ↓ example12-target-Y-seal
          ↑ example12-target-Y-unseal ∶
        example12-Z-var⊑
  example12-target-Y-unseal-checkpoint₃ =
    rejected

  example12-target-Z-unseal-checkpoint₃ :
    Ex12.example12-world-X ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal)
          ↓ example12-target-Y-seal
          ↑ example12-target-Y-unseal
          ↑ example12-target-Z-unseal ∶
        example12-X-var-to-star
  example12-target-Z-unseal-checkpoint₃ =
    rejected

  example12-target-id★-checkpoint₃ :
    Ex12.example12-world-X ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ (((((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal)
          ↓ example12-target-Y-seal
          ↑ example12-target-Y-unseal)
          ↑ example12-target-Z-unseal)
          ⟨ example12-target-id★ ⟩ ∶
        example12-X-var-to-star
  example12-target-id★-checkpoint₃ =
    rejected

  example12-target-★?X-checkpoint₃ :
    Ex12.example12-world-X ∣ [] ⊢²
      ($ (κℕ 7)) ↓ example12-source-X-seal
      ⊑ ((((((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal)
          ↓ example12-target-Y-seal
          ↑ example12-target-Y-unseal)
          ↑ example12-target-Z-unseal)
          ⟨ example12-target-id★ ⟩)
          ⟨ example12-target-★?X ⟩ ∶
        example12-X-var⊑
  example12-target-★?X-checkpoint₃ =
    rejected

  example12-checkpoint₃ :
    Ex12.example12-world-X ∣ [] ⊢² Ex.left₃ ⊑ Ex.right₁₀ ∶
      example12-ℕ⊑ℕ-X
  example12-checkpoint₃ =
    rejected

------------------------------------------------------------------------
-- Example 2: β-reveal-∀ followed by β-Λ, with a path to ℕ
------------------------------------------------------------------------

nat-chain-more-precise : Term 0
nat-chain-more-precise = Ex12.example12-nat-chain-source

nat-chain-more-imprecise : Term 0
nat-chain-more-imprecise = Ex12.example12-nat-chain-target

nat-chain-more-precise-reduction :
  nat-chain-more-precise —↠[ Ex.left-changes ] Ex.left-final
nat-chain-more-precise-reduction = Ex.example12-left-reduction

nat-target₀ : Term 0
nat-target₀ = nat-chain-more-imprecise

nat-target-store₀ : TyStore 0
nat-target-store₀ = store-empty

nat-target-step₀ : Step.OneStep nat-target-store₀ nat-target₀
nat-target-step₀ =
  Step.from-just-step (step? nat-target-store₀ nat-target₀) refl

nat-target₁ : Term (Δ′ nat-target-step₀)
nat-target₁ = next nat-target-step₀

nat-target-store₁ : TyStore (Δ′ nat-target-step₀)
nat-target-store₁ = Step.store-after nat-target-step₀

nat-target-step₁ : Step.OneStep nat-target-store₁ nat-target₁
nat-target-step₁ =
  Step.from-just-step (step? nat-target-store₁ nat-target₁) refl

nat-target₂ : Term (Δ′ nat-target-step₁)
nat-target₂ = next nat-target-step₁

nat-target-store₂ : TyStore (Δ′ nat-target-step₁)
nat-target-store₂ = Step.store-after nat-target-step₁

nat-target-step₂ : Step.OneStep nat-target-store₂ nat-target₂
nat-target-step₂ =
  Step.from-just-step (step? nat-target-store₂ nat-target₂) refl

nat-target₃ : Term (Δ′ nat-target-step₂)
nat-target₃ = next nat-target-step₂

nat-target-store₃ : TyStore (Δ′ nat-target-step₂)
nat-target-store₃ = Step.store-after nat-target-step₂

nat-target-step₃ : Step.OneStep nat-target-store₃ nat-target₃
nat-target-step₃ =
  Step.from-just-step (step? nat-target-store₃ nat-target₃) refl

nat-target₄ : Term (Δ′ nat-target-step₃)
nat-target₄ = next nat-target-step₃

nat-target-store₄ : TyStore (Δ′ nat-target-step₃)
nat-target-store₄ = Step.store-after nat-target-step₃

nat-target-step₄ : Step.OneStep nat-target-store₄ nat-target₄
nat-target-step₄ =
  Step.from-just-step (step? nat-target-store₄ nat-target₄) refl

nat-target₅ : Term (Δ′ nat-target-step₄)
nat-target₅ = next nat-target-step₄

nat-target-store₅ : TyStore (Δ′ nat-target-step₄)
nat-target-store₅ = Step.store-after nat-target-step₄

nat-target-step₅ : Step.OneStep nat-target-store₅ nat-target₅
nat-target-step₅ =
  Step.from-just-step (step? nat-target-store₅ nat-target₅) refl

nat-target₆ : Term (Δ′ nat-target-step₅)
nat-target₆ = next nat-target-step₅

nat-target-store₆ : TyStore (Δ′ nat-target-step₅)
nat-target-store₆ = Step.store-after nat-target-step₅

nat-target-step₆ : Step.OneStep nat-target-store₆ nat-target₆
nat-target-step₆ =
  Step.from-just-step (step? nat-target-store₆ nat-target₆) refl

nat-target₇ : Term (Δ′ nat-target-step₆)
nat-target₇ = next nat-target-step₆

nat-target-store₇ : TyStore (Δ′ nat-target-step₆)
nat-target-store₇ = Step.store-after nat-target-step₆

nat-target-step₇ : Step.OneStep nat-target-store₇ nat-target₇
nat-target-step₇ =
  Step.from-just-step (step? nat-target-store₇ nat-target₇) refl

nat-target-final : Term (Δ′ nat-target-step₇)
nat-target-final = next nat-target-step₇

nat-target-changes : StoreChanges 0 (Δ′ nat-target-step₇)
nat-target-changes =
  change nat-target-step₀ ∷ change nat-target-step₁ ∷
  change nat-target-step₂ ∷ change nat-target-step₃ ∷
  change nat-target-step₄ ∷ change nat-target-step₅ ∷
  change nat-target-step₆ ∷ change nat-target-step₇ ∷ []

nat-chain-more-imprecise-reduction :
  nat-chain-more-imprecise —↠[ nat-target-changes ] nat-target-final
nat-chain-more-imprecise-reduction =
  nat-target₀
  —→[ change nat-target-step₀ ]⟨ reduction nat-target-step₀ ⟩
  nat-target₁
  —→[ change nat-target-step₁ ]⟨ reduction nat-target-step₁ ⟩
  nat-target₂
  —→[ change nat-target-step₂ ]⟨ reduction nat-target-step₂ ⟩
  nat-target₃
  —→[ change nat-target-step₃ ]⟨ reduction nat-target-step₃ ⟩
  nat-target₄
  —→[ change nat-target-step₄ ]⟨ reduction nat-target-step₄ ⟩
  nat-target₅
  —→[ change nat-target-step₅ ]⟨ reduction nat-target-step₅ ⟩
  nat-target₆
  —→[ change nat-target-step₆ ]⟨ reduction nat-target-step₆ ⟩
  nat-target₇
  —→[ change nat-target-step₇ ]⟨ reduction nat-target-step₇ ⟩
  nat-target-final ∎[]

nat-chain-ℕ⊑ℕ₀ :
  (‵ `ℕ) ⊑ᵂ⟨ reflWorld store-empty ⟩ (‵ `ℕ)
nat-chain-ℕ⊑ℕ₀ = ℕ⊑ℕ² {W = reflWorld store-empty}

-- The natural-number-chain re-parking checkpoints are likewise retained
-- under their now-refuted world-validity assumptions.
module RejectedNatChainIntermediate
    (invX : CTX.WorldInvariants Ex12.example12-nat-chain-ηᴸ-X
      Ex12.example12-nat-chain-ηᴿ Ex12.example12-nat-chain-imp-env
      Ex12.example12-nat-chain-source-store
      Ex12.example12-nat-chain-target-store)
    (invY : CTX.WorldInvariants Ex12.example12-nat-chain-ηᴸ-Y
      Ex12.example12-nat-chain-ηᴿ Ex12.example12-nat-chain-imp-env
      Ex12.example12-nat-chain-source-store
      Ex12.example12-nat-chain-target-store) where

  impossibleX : ⊥
  impossibleX =
    Ex12.violates-invariants Ex12.example12-nat-chain-world-X invX

  impossibleY : ⊥
  impossibleY =
    Ex12.violates-invariants Ex12.example12-nat-chain-world-Y invY

  rejected : ∀ {A : Set} → A
  rejected = ⊥-elim impossibleX

  nat-chain-world-X : World 1 2 2
  nat-chain-world-X = ⊥-elim impossibleX

  nat-chain-world-Y : World 1 2 2
  nat-chain-world-Y = ⊥-elim impossibleY

  nat-chain-X-representation :
    CTX.StoreRepImp nat-chain-world-X Fin.zero (Fin.suc Fin.zero)
  nat-chain-X-representation =
    rejected

  nat-chain-Y-representation :
    CTX.StoreRepImp nat-chain-world-Y Fin.zero Fin.zero
  nat-chain-Y-representation =
    rejected

  nat-chain-rebase-X-to-Y :
    CTX.RebaseAt nat-chain-world-X nat-chain-world-Y Fin.zero Fin.zero
  nat-chain-rebase-X-to-Y =
    rejected

  nat-chain-ℕ⊑ℕ-X :
    (‵ `ℕ) ⊑ᵂ⟨ nat-chain-world-X ⟩ (‵ `ℕ)
  nat-chain-ℕ⊑ℕ-X = ℕ⊑ℕ² {W = nat-chain-world-X}

  nat-chain-ℕ⇒ℕ⊑ℕ⇒ℕ-X :
    ((‵ `ℕ) ⇒ (‵ `ℕ)) ⊑ᵂ⟨ nat-chain-world-X ⟩
      ((‵ `ℕ) ⇒ (‵ `ℕ))
  nat-chain-ℕ⇒ℕ⊑ℕ⇒ℕ-X =
    ℕ⇒ℕ⊑ℕ⇒ℕ² {W = nat-chain-world-X}

  nat-chain-source-X-seal : Conv↓ 1 (‵ `ℕ) (＇ Fin.zero)
  nat-chain-source-X-seal = seal Fin.zero (‵ `ℕ)

  nat-chain-source-X-unseal : Conv↑ 1 (＇ Fin.zero) (‵ `ℕ)
  nat-chain-source-X-unseal = unseal Fin.zero (‵ `ℕ)

  nat-chain-source-X-reveal :
    Conv↑ 1 (＇ Fin.zero ⇒ ＇ Fin.zero) (‵ `ℕ ⇒ ‵ `ℕ)
  nat-chain-source-X-reveal =
    nat-chain-source-X-seal ↦↑ nat-chain-source-X-unseal

  nat-chain-target-X-seal :
    Conv↓ 2 (‵ `ℕ) (＇ (Fin.suc Fin.zero))
  nat-chain-target-X-seal = seal (Fin.suc Fin.zero) (‵ `ℕ)

  nat-chain-target-X-unseal :
    Conv↑ 2 (＇ (Fin.suc Fin.zero)) (‵ `ℕ)
  nat-chain-target-X-unseal = unseal (Fin.suc Fin.zero) (‵ `ℕ)

  nat-chain-target-X-reveal :
    Conv↑ 2
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
      (‵ `ℕ ⇒ ‵ `ℕ)
  nat-chain-target-X-reveal =
    nat-chain-target-X-seal ↦↑ nat-chain-target-X-unseal

  nat-chain-target-Y-seal :
    Conv↓ 2 (＇ (Fin.suc Fin.zero)) (＇ Fin.zero)
  nat-chain-target-Y-seal = seal Fin.zero (＇ (Fin.suc Fin.zero))

  nat-chain-target-Y-unseal :
    Conv↑ 2 (＇ Fin.zero) (＇ (Fin.suc Fin.zero))
  nat-chain-target-Y-unseal = unseal Fin.zero (＇ (Fin.suc Fin.zero))

  nat-chain-target-Y-reveal :
    Conv↑ 2
      (＇ Fin.zero ⇒ ＇ Fin.zero)
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
  nat-chain-target-Y-reveal =
    nat-chain-target-Y-seal ↦↑ nat-chain-target-Y-unseal

  nat-chain-target-id-X-reveal :
    Conv↑ 2
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
  nat-chain-target-id-X-reveal =
    id↑ (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))

  nat-chain-source-X-seal-⊢ :
    Ex12.example12-nat-chain-source-store ⊢↓ nat-chain-source-X-seal
  nat-chain-source-X-seal-⊢ =
    ⊢↓-seal Ex12.example12-nat-chain-source-X∋

  nat-chain-source-X-seal-⊢ˣ :
    Ex12.example12-nat-chain-source-store Conv.⊢↓[ just Fin.zero ]
      nat-chain-source-X-seal
  nat-chain-source-X-seal-⊢ˣ =
    Conv.⊢↓-sealˣ Ex12.example12-nat-chain-source-X∋

  nat-chain-source-X-unseal-⊢ :
    Ex12.example12-nat-chain-source-store ⊢↑ nat-chain-source-X-unseal
  nat-chain-source-X-unseal-⊢ =
    ⊢↑-unseal Ex12.example12-nat-chain-source-X∋

  nat-chain-source-X-unseal-⊢ˣ :
    Ex12.example12-nat-chain-source-store Conv.⊢↑[ just Fin.zero ]
      nat-chain-source-X-unseal
  nat-chain-source-X-unseal-⊢ˣ =
    Conv.⊢↑-unsealˣ Ex12.example12-nat-chain-source-X∋

  nat-chain-source-X-reveal-⊢ :
    Ex12.example12-nat-chain-source-store ⊢↑ nat-chain-source-X-reveal
  nat-chain-source-X-reveal-⊢ =
    ⊢↑-⇒ nat-chain-source-X-seal-⊢ nat-chain-source-X-unseal-⊢

  nat-chain-source-X-reveal-⊢ˣ :
    Ex12.example12-nat-chain-source-store Conv.⊢↑[ just Fin.zero ]
      nat-chain-source-X-reveal
  nat-chain-source-X-reveal-⊢ˣ =
    Conv.⊢↑-⇒ˣ Conv.join-both nat-chain-source-X-seal-⊢ˣ
      nat-chain-source-X-unseal-⊢ˣ

  nat-chain-target-X-seal-⊢ :
    Ex12.example12-nat-chain-target-store ⊢↓ nat-chain-target-X-seal
  nat-chain-target-X-seal-⊢ =
    ⊢↓-seal Ex12.example12-nat-chain-target-X∋

  nat-chain-target-X-seal-⊢ˣ :
    Ex12.example12-nat-chain-target-store Conv.⊢↓[ just (Fin.suc Fin.zero) ]
      nat-chain-target-X-seal
  nat-chain-target-X-seal-⊢ˣ =
    Conv.⊢↓-sealˣ Ex12.example12-nat-chain-target-X∋

  nat-chain-target-X-unseal-⊢ :
    Ex12.example12-nat-chain-target-store ⊢↑ nat-chain-target-X-unseal
  nat-chain-target-X-unseal-⊢ =
    ⊢↑-unseal Ex12.example12-nat-chain-target-X∋

  nat-chain-target-X-unseal-⊢ˣ :
    Ex12.example12-nat-chain-target-store Conv.⊢↑[ just (Fin.suc Fin.zero) ]
      nat-chain-target-X-unseal
  nat-chain-target-X-unseal-⊢ˣ =
    Conv.⊢↑-unsealˣ Ex12.example12-nat-chain-target-X∋

  nat-chain-target-X-reveal-⊢ :
    Ex12.example12-nat-chain-target-store ⊢↑ nat-chain-target-X-reveal
  nat-chain-target-X-reveal-⊢ =
    ⊢↑-⇒ nat-chain-target-X-seal-⊢ nat-chain-target-X-unseal-⊢

  nat-chain-target-X-reveal-⊢ˣ :
    Ex12.example12-nat-chain-target-store Conv.⊢↑[ just (Fin.suc Fin.zero) ]
      nat-chain-target-X-reveal
  nat-chain-target-X-reveal-⊢ˣ =
    Conv.⊢↑-⇒ˣ Conv.join-both nat-chain-target-X-seal-⊢ˣ
      nat-chain-target-X-unseal-⊢ˣ

  nat-chain-target-Y-reveal-⊢ˣ :
    Ex12.example12-nat-chain-target-store Conv.⊢↑[ just Fin.zero ]
      nat-chain-target-Y-reveal
  nat-chain-target-Y-reveal-⊢ˣ =
    Conv.⊢↑-⇒ˣ Conv.join-both
      (Conv.⊢↓-sealˣ Ex12.example12-nat-chain-target-Y∋)
      (Conv.⊢↑-unsealˣ Ex12.example12-nat-chain-target-Y∋)

  nat-chain-X-var⊑ :
    ＇ Fin.zero ⊑ᵂ⟨ nat-chain-world-X ⟩
      ＇ (Fin.suc Fin.zero)
  nat-chain-X-var⊑ = rejected

  nat-chain-rebase-X-same :
    CTX.RebaseAt nat-chain-world-X
      nat-chain-world-X Fin.zero (Fin.suc Fin.zero)
  nat-chain-rebase-X-same =
    rejected

  nat-chain-Y-var⊑ :
    ＇ Fin.zero ⊑ᵂ⟨ nat-chain-world-Y ⟩ ＇ Fin.zero
  nat-chain-Y-var⊑ = rejected

  nat-chain-X-function-local :
    (＇ Fin.zero ⇒ ＇ Fin.zero)
      ⊑ᵂ⟨ nat-chain-world-X ⟩
        (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
  nat-chain-X-function-local =
    rejected

  nat-chain-Y-function-local :
    (＇ Fin.zero ⇒ ＇ Fin.zero)
      ⊑ᵂ⟨ nat-chain-world-Y ⟩
        (＇ Fin.zero ⇒ ＇ Fin.zero)
  nat-chain-Y-function-local =
    rejected

  nat-chain-polyId-target-reveal :
    reflWorld store-empty ∣ [] ⊢² Ex.polyId
      ⊑ Ex.polyId ↑ Ex12.example12-nat-chain-reveal ∶
        example12-∀⊑∀
  nat-chain-polyId-target-reveal =
    CTI2.⊑reveal² CTX.impEnvMono-refl CTX.rebase-idᴿ CTX.same-[]
      Ex12.example12-nat-chain-reveal-⊢ˣ polyId-refl²
      example12-∀⊑∀

  nat-chain-checkpoint₀ :
    reflWorld store-empty ∣ [] ⊢² nat-chain-more-precise
      ⊑ nat-chain-more-imprecise ∶ nat-chain-ℕ⊑ℕ₀
  nat-chain-checkpoint₀ =
    ·⊑·²
      (•⊑•² example12-∀⊑∀ nat-chain-polyId-target-reveal
        nat-chain-ℕ⊑ℕ₀ example12-ℕ⇒ℕ⊑ℕ⇒ℕ)
      (κ⊑κ² (κℕ 7) nat-chain-ℕ⊑ℕ₀)

  nat-chain-lambda-Y :
    nat-chain-world-Y ∣ [] ⊢² ƛ (` 0) ⊑ ƛ (` 0) ∶
      nat-chain-Y-function-local
  nat-chain-lambda-Y =
    rejected

  nat-chain-lambda-X :
    nat-chain-world-X ∣ [] ⊢² ƛ (` 0)
      ⊑ (ƛ (` 0)) ↑ nat-chain-target-Y-reveal ∶
        nat-chain-X-function-local
  nat-chain-lambda-X =
    rejected

  nat-chain-lambda-X-id :
    nat-chain-world-X ∣ [] ⊢² ƛ (` 0)
      ⊑ ((ƛ (` 0)) ↑ nat-chain-target-Y-reveal)
          ↑ nat-chain-target-id-X-reveal ∶
        nat-chain-X-function-local
  nat-chain-lambda-X-id =
    rejected

  nat-chain-function-checkpoint₁ :
    nat-chain-world-X ∣ [] ⊢²
      (ƛ (` 0)) ↑ nat-chain-source-X-reveal
      ⊑ (((ƛ (` 0)) ↑ nat-chain-target-Y-reveal)
          ↑ nat-chain-target-id-X-reveal)
          ↑ nat-chain-target-X-reveal ∶
        nat-chain-ℕ⇒ℕ⊑ℕ⇒ℕ-X
  nat-chain-function-checkpoint₁ =
    rejected

  nat-chain-checkpoint₁ :
    nat-chain-world-X ∣ [] ⊢² Ex.left₁
      ⊑ nat-target₂ ∶ nat-chain-ℕ⊑ℕ-X
  nat-chain-checkpoint₁ =
    rejected

  nat-chain-sealed-const-X :
    nat-chain-world-X ∣ [] ⊢²
      ($ (κℕ 7)) ↓ nat-chain-source-X-seal
      ⊑ ($ (κℕ 7)) ↓ nat-chain-target-X-seal ∶
        nat-chain-X-var⊑
  nat-chain-sealed-const-X =
    rejected

  nat-chain-application-checkpoint₂ :
    nat-chain-world-X ∣ [] ⊢²
      (ƛ (` 0)) · (($ (κℕ 7)) ↓ nat-chain-source-X-seal)
      ⊑ ((ƛ (` 0)) ↑ nat-chain-target-Y-reveal)
          · (($ (κℕ 7)) ↓ nat-chain-target-X-seal) ∶
        nat-chain-X-var⊑
  nat-chain-application-checkpoint₂ =
    rejected

  nat-chain-checkpoint₂ :
    nat-chain-world-X ∣ [] ⊢² Ex.left₂
      ⊑ nat-target₄ ∶ nat-chain-ℕ⊑ℕ-X
  nat-chain-checkpoint₂ =
    rejected

  nat-chain-checkpoint₃ :
    nat-chain-world-X ∣ [] ⊢² Ex.left₃
      ⊑ nat-target₇ ∶ nat-chain-ℕ⊑ℕ-X
  nat-chain-checkpoint₃ =
    rejected

  nat-chain-checkpoint₄ :
    nat-chain-world-X ∣ [] ⊢² Ex.left-final
      ⊑ nat-target-final ∶ nat-chain-ℕ⊑ℕ-X
  nat-chain-checkpoint₄ = rejected

------------------------------------------------------------------------
-- Example 3: representation path on the left
------------------------------------------------------------------------

left-path-more-precise : Term 0
left-path-more-precise = Ex12.example12-left-path-source

left-path-more-imprecise : Term 0
left-path-more-imprecise = Ex12.example12-left-path-target

left-path-more-precise-reduction :
  left-path-more-precise —↠[ Ex.right-changes ] Ex.right-final
left-path-more-precise-reduction = Ex.example12-right-reduction

left-path-target₀ : Term 0
left-path-target₀ = left-path-more-imprecise

left-path-target-store₀ : TyStore 0
left-path-target-store₀ = store-empty

left-path-target-step₀ :
  Step.OneStep left-path-target-store₀ left-path-target₀
left-path-target-step₀ =
  Step.from-just-step (step? left-path-target-store₀ left-path-target₀) refl

left-path-target₁ : Term (Δ′ left-path-target-step₀)
left-path-target₁ = next left-path-target-step₀

left-path-target-store₁ : TyStore (Δ′ left-path-target-step₀)
left-path-target-store₁ = Step.store-after left-path-target-step₀

left-path-target-step₁ :
  Step.OneStep left-path-target-store₁ left-path-target₁
left-path-target-step₁ =
  Step.from-just-step (step? left-path-target-store₁ left-path-target₁) refl

left-path-target₂ : Term (Δ′ left-path-target-step₁)
left-path-target₂ = next left-path-target-step₁

left-path-target-store₂ : TyStore (Δ′ left-path-target-step₁)
left-path-target-store₂ = Step.store-after left-path-target-step₁

left-path-target-step₂ :
  Step.OneStep left-path-target-store₂ left-path-target₂
left-path-target-step₂ =
  Step.from-just-step (step? left-path-target-store₂ left-path-target₂) refl

left-path-target₃ : Term (Δ′ left-path-target-step₂)
left-path-target₃ = next left-path-target-step₂

left-path-target-store₃ : TyStore (Δ′ left-path-target-step₂)
left-path-target-store₃ = Step.store-after left-path-target-step₂

left-path-target-step₃ :
  Step.OneStep left-path-target-store₃ left-path-target₃
left-path-target-step₃ =
  Step.from-just-step (step? left-path-target-store₃ left-path-target₃) refl

left-path-target₄ : Term (Δ′ left-path-target-step₃)
left-path-target₄ = next left-path-target-step₃

left-path-target-store₄ : TyStore (Δ′ left-path-target-step₃)
left-path-target-store₄ = Step.store-after left-path-target-step₃

left-path-target-step₄ :
  Step.OneStep left-path-target-store₄ left-path-target₄
left-path-target-step₄ =
  Step.from-just-step (step? left-path-target-store₄ left-path-target₄) refl

left-path-target₅ : Term (Δ′ left-path-target-step₄)
left-path-target₅ = next left-path-target-step₄

left-path-target-store₅ : TyStore (Δ′ left-path-target-step₄)
left-path-target-store₅ = Step.store-after left-path-target-step₄

left-path-target-step₅ :
  Step.OneStep left-path-target-store₅ left-path-target₅
left-path-target-step₅ =
  Step.from-just-step (step? left-path-target-store₅ left-path-target₅) refl

left-path-target₆ : Term (Δ′ left-path-target-step₅)
left-path-target₆ = next left-path-target-step₅

left-path-target-store₆ : TyStore (Δ′ left-path-target-step₅)
left-path-target-store₆ = Step.store-after left-path-target-step₅

left-path-target-step₆ :
  Step.OneStep left-path-target-store₆ left-path-target₆
left-path-target-step₆ =
  Step.from-just-step (step? left-path-target-store₆ left-path-target₆) refl

left-path-target₇ : Term (Δ′ left-path-target-step₆)
left-path-target₇ = next left-path-target-step₆

left-path-target-store₇ : TyStore (Δ′ left-path-target-step₆)
left-path-target-store₇ = Step.store-after left-path-target-step₆

left-path-target-step₇ :
  Step.OneStep left-path-target-store₇ left-path-target₇
left-path-target-step₇ =
  Step.from-just-step (step? left-path-target-store₇ left-path-target₇) refl

left-path-target₈ : Term (Δ′ left-path-target-step₇)
left-path-target₈ = next left-path-target-step₇

left-path-target-store₈ : TyStore (Δ′ left-path-target-step₇)
left-path-target-store₈ = Step.store-after left-path-target-step₇

left-path-target-step₈ :
  Step.OneStep left-path-target-store₈ left-path-target₈
left-path-target-step₈ =
  Step.from-just-step (step? left-path-target-store₈ left-path-target₈) refl

left-path-target₉ : Term (Δ′ left-path-target-step₈)
left-path-target₉ = next left-path-target-step₈

left-path-target-store₉ : TyStore (Δ′ left-path-target-step₈)
left-path-target-store₉ = Step.store-after left-path-target-step₈

left-path-target-step₉ :
  Step.OneStep left-path-target-store₉ left-path-target₉
left-path-target-step₉ =
  Step.from-just-step (step? left-path-target-store₉ left-path-target₉) refl

left-path-target-final : Term (Δ′ left-path-target-step₉)
left-path-target-final = next left-path-target-step₉

left-path-target-store-final : TyStore (Δ′ left-path-target-step₉)
left-path-target-store-final = Step.store-after left-path-target-step₉

left-path-target-final-value : Value left-path-target-final
left-path-target-final-value =
  Step.from-just-value (value? left-path-target-final) refl

left-path-target-changes : StoreChanges 0 (Δ′ left-path-target-step₉)
left-path-target-changes =
  change left-path-target-step₀ ∷ change left-path-target-step₁ ∷
  change left-path-target-step₂ ∷ change left-path-target-step₃ ∷
  change left-path-target-step₄ ∷ change left-path-target-step₅ ∷
  change left-path-target-step₆ ∷ change left-path-target-step₇ ∷
  change left-path-target-step₈ ∷ change left-path-target-step₉ ∷ []

left-path-more-imprecise-reduction :
  left-path-more-imprecise —↠[ left-path-target-changes ]
    left-path-target-final
left-path-more-imprecise-reduction =
  left-path-target₀
  —→[ change left-path-target-step₀ ]⟨ reduction left-path-target-step₀ ⟩
  left-path-target₁
  —→[ change left-path-target-step₁ ]⟨ reduction left-path-target-step₁ ⟩
  left-path-target₂
  —→[ change left-path-target-step₂ ]⟨ reduction left-path-target-step₂ ⟩
  left-path-target₃
  —→[ change left-path-target-step₃ ]⟨ reduction left-path-target-step₃ ⟩
  left-path-target₄
  —→[ change left-path-target-step₄ ]⟨ reduction left-path-target-step₄ ⟩
  left-path-target₅
  —→[ change left-path-target-step₅ ]⟨ reduction left-path-target-step₅ ⟩
  left-path-target₆
  —→[ change left-path-target-step₆ ]⟨ reduction left-path-target-step₆ ⟩
  left-path-target₇
  —→[ change left-path-target-step₇ ]⟨ reduction left-path-target-step₇ ⟩
  left-path-target₈
  —→[ change left-path-target-step₈ ]⟨ reduction left-path-target-step₈ ⟩
  left-path-target₉
  —→[ change left-path-target-step₉ ]⟨ reduction left-path-target-step₉ ⟩
  left-path-target-final ∎[]

left-path-target-ηᴿ-YZ : 2 ↪ᵗ 3
left-path-target-ηᴿ-YZ = skip id↪ᵗ

left-path-target-ηᴿ-XZ : 2 ↪ᵗ 3
left-path-target-ηᴿ-XZ = keep (skip (keep empty))

left-path-imp-env-XZ : ImpEnv 3
left-path-imp-env-XZ Fin.zero = X⊑★
left-path-imp-env-XZ (Fin.suc Fin.zero) = X⊑★
left-path-imp-env-XZ (Fin.suc (Fin.suc Fin.zero)) = X⊑X

left-path-imp-env-YZ : ImpEnv 3
left-path-imp-env-YZ Fin.zero = X⊑★
left-path-imp-env-YZ (Fin.suc Fin.zero) = X⊑★
left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) = X⊑X

-- The XZ checkpoints align source X and Z directly.  Their target fixture
-- therefore exposes literal dynamic entries at both aligned cells instead of
-- retaining the reduction trace's intermediate Y-to-Z alias.

left-path-target-store-XZ : TyStore 2
left-path-target-store-XZ = store-bind (store-bind store-empty ★) ★

left-path-world₁ :
  World (Δ′ Ex.right-step₀) (Δ′ left-path-target-step₀)
    (Δ′ Ex.right-step₀)
left-path-world₁ =
  reflWorld Ex.right-store₁

left-path-world₂ :
  World (Δ′ Ex.right-step₁) (Δ′ left-path-target-step₁)
    (Δ′ Ex.right-step₁)
left-path-world₂ =
  reflWorld Ex.right-store₂

left-path-world₃-invariants :
  CTX.WorldInvariants id↪ᵗ left-path-target-ηᴿ-XZ
    left-path-imp-env-XZ Ex.right-store₃ left-path-target-store-XZ
left-path-world₃-invariants =
  CTX.world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → left-path-imp-env-XZ (C.toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 2 ]
        C.toRenameᵗ left-path-target-ηᴿ-XZ Xᴿ
          ≡ C.toRenameᵗ id↪ᵗ Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) mark =
    Fin.suc Fin.zero , refl

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 2}
    → C.toRenameᵗ id↪ᵗ Xᴸ
        ≡ C.toRenameᵗ left-path-target-ηᴿ-XZ Xᴿ
    → left-path-imp-env-XZ ⊢
        renameᵗ (C.toRenameᵗ id↪ᵗ)
          (TyStore.lookupStore Ex.right-store₃ Xᴸ)
        ⊑ renameᵗ (C.toRenameᵗ left-path-target-ηᴿ-XZ)
          (TyStore.lookupStore left-path-target-store-XZ Xᴿ)
  reps {Fin.zero} {Fin.zero} refl = ι⊑★
  reps {Fin.zero} {Fin.suc Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.suc Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.suc Fin.zero} refl = ★⊑★

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → C.toRenameᵗ id↪ᵗ Xᴸ
          ≢ C.toRenameᵗ left-path-target-ηᴿ-XZ Xᴿ)
    → TyStore.lookupStore left-path-target-store-XZ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
          (TyStore.lookupStore left-path-target-store-XZ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → C.toRenameᵗ id↪ᵗ Xᴸ
              ≢ C.toRenameᵗ left-path-target-ηᴿ-XZ Yᴿ)
  unmatched Fin.zero no-source = ⊥-elim (no-source Fin.zero refl)
  unmatched (Fin.suc Fin.zero) no-source =
    ⊥-elim (no-source (Fin.suc (Fin.suc Fin.zero)) refl)

  unoccupied : ∀ Xᴸ
    → left-path-imp-env-XZ (C.toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑★
    → TyStore.lookupStore Ex.right-store₃ Xᴸ ≡ ★
    → ∀ Xᴿ
    → C.toRenameᵗ left-path-target-ηᴿ-XZ Xᴿ
      ≢ C.toRenameᵗ id↪ᵗ Xᴸ
  unoccupied Fin.zero mark () Xᴿ aligned
  unoccupied (Fin.suc Fin.zero) mark () Xᴿ aligned
  unoccupied (Fin.suc (Fin.suc Fin.zero)) () entry Xᴿ aligned

left-path-world₃ :
  World (Δ′ Ex.right-step₂) (Δ′ left-path-target-step₂)
    (Δ′ Ex.right-step₂)
left-path-world₃ =
  bind-both-starʷ
    (bind-leftʷ (bind-bothʷ emptyʷ ★ ★ ★⊑★) (＇ Fin.zero))
    (‵ `ℕ) ★ ι⊑★ (λ ())

left-path-world₄ :
  World (Δ′ Ex.right-step₃) (Δ′ left-path-target-step₃)
    (Δ′ Ex.right-step₃)
left-path-world₄ =
  left-path-world₃

left-path-world₅ :
  World (Δ′ Ex.right-step₄) (Δ′ left-path-target-step₄)
    (Δ′ Ex.right-step₄)
left-path-world₅ =
  left-path-world₃

left-path-world₃-YZ-invariants :
  CTX.WorldInvariants id↪ᵗ left-path-target-ηᴿ-YZ
    left-path-imp-env-YZ Ex.right-store₃ left-path-target-store₃
left-path-world₃-YZ-invariants =
  CTX.world-invariants precise reps unmatched unoccupied
  where
  precise : ∀ Xᴸ
    → left-path-imp-env-YZ (C.toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑X
    → Σ[ Xᴿ ∈ TyVar 2 ]
        C.toRenameᵗ left-path-target-ηᴿ-YZ Xᴿ
          ≡ C.toRenameᵗ id↪ᵗ Xᴸ
  precise Fin.zero ()
  precise (Fin.suc Fin.zero) ()
  precise (Fin.suc (Fin.suc Fin.zero)) mark =
    Fin.suc Fin.zero , refl

  reps : ∀ {Xᴸ : TyVar 3} {Xᴿ : TyVar 2}
    → C.toRenameᵗ id↪ᵗ Xᴸ
        ≡ C.toRenameᵗ left-path-target-ηᴿ-YZ Xᴿ
    → left-path-imp-env-YZ ⊢
        renameᵗ (C.toRenameᵗ id↪ᵗ)
          (TyStore.lookupStore Ex.right-store₃ Xᴸ)
        ⊑ renameᵗ (C.toRenameᵗ left-path-target-ηᴿ-YZ)
          (TyStore.lookupStore left-path-target-store₃ Xᴿ)
  reps {Fin.zero} {Fin.zero} ()
  reps {Fin.zero} {Fin.suc Fin.zero} ()
  reps {Fin.suc Fin.zero} {Fin.zero} refl = X⊑X
  reps {Fin.suc Fin.zero} {Fin.suc Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.zero} ()
  reps {Fin.suc (Fin.suc Fin.zero)} {Fin.suc Fin.zero} refl = ★⊑★

  unmatched : ∀ Xᴿ
    → (∀ Xᴸ
        → C.toRenameᵗ id↪ᵗ Xᴸ
          ≢ C.toRenameᵗ left-path-target-ηᴿ-YZ Xᴿ)
    → TyStore.lookupStore left-path-target-store₃ Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
          (TyStore.lookupStore left-path-target-store₃ Xᴿ ≡ ＇ Yᴿ)
        × (∀ Xᴸ
            → C.toRenameᵗ id↪ᵗ Xᴸ
              ≢ C.toRenameᵗ left-path-target-ηᴿ-YZ Yᴿ)
  unmatched Fin.zero no-source =
    ⊥-elim (no-source (Fin.suc Fin.zero) refl)
  unmatched (Fin.suc Fin.zero) no-source =
    ⊥-elim (no-source (Fin.suc (Fin.suc Fin.zero)) refl)

  unoccupied : ∀ Xᴸ
    → left-path-imp-env-YZ (C.toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑★
    → TyStore.lookupStore Ex.right-store₃ Xᴸ ≡ ★
    → ∀ Xᴿ
    → C.toRenameᵗ left-path-target-ηᴿ-YZ Xᴿ
      ≢ C.toRenameᵗ id↪ᵗ Xᴸ
  unoccupied Fin.zero mark () Xᴿ aligned
  unoccupied (Fin.suc Fin.zero) mark () Xᴿ aligned
  unoccupied (Fin.suc (Fin.suc Fin.zero)) () entry Xᴿ aligned

left-path-world₃-YZ :
  World (Δ′ Ex.right-step₂) (Δ′ left-path-target-step₂)
    (Δ′ Ex.right-step₂)
left-path-world₃-YZ =
  bind-leftʷ
    (bind-both-starʷ (bind-bothʷ emptyʷ ★ ★ ★⊑★)
      (＇ Fin.zero) (＇ Fin.zero) X⊑X (λ ()))
    (‵ `ℕ)

left-path-world₄-YZ :
  World (Δ′ Ex.right-step₃) (Δ′ left-path-target-step₃)
    (Δ′ Ex.right-step₃)
left-path-world₄-YZ =
  left-path-world₃-YZ

left-path-ℕ⊑★₀ :
  (‵ `ℕ) ⊑ᵂ⟨ reflWorld store-empty ⟩ ★
left-path-ℕ⊑★₀ = ℕ⊑★² {W = reflWorld store-empty}

left-path-ℕ⊑★₁ :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₁ ⟩ ★
left-path-ℕ⊑★₁ = ℕ⊑★² {W = left-path-world₁}

left-path-ℕ⊑★₂ :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₂ ⟩ ★
left-path-ℕ⊑★₂ = ℕ⊑★² {W = left-path-world₂}

left-path-ℕ⊑★₃ :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₃ ⟩ ★
left-path-ℕ⊑★₃ = ℕ⊑★² {W = left-path-world₃}

left-path-ℕ⊑★₄ :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₄ ⟩ ★
left-path-ℕ⊑★₄ = ℕ⊑★² {W = left-path-world₄}

left-path-ℕ⊑★₅ :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₅ ⟩ ★
left-path-ℕ⊑★₅ = ℕ⊑★² {W = left-path-world₅}

left-path-ℕ!₁ :
  renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}) ⊢ (‵ `ℕ) ∼ ★
left-path-ℕ!₁ = C.↑ᶜ Ex12.example12-ℕ!

left-path-ℕ!₂ :
  renameEnv∼ (skip id↪ᵗ) (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))
    ⊢ (‵ `ℕ) ∼ ★
left-path-ℕ!₂ = C.renameᵐᶜ (skip id↪ᵗ) left-path-ℕ!₁

left-path-id★↦id★₁-source :
  renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}) ⊢ (★ ⇒ ★) ∼ (★ ⇒ ★)
left-path-id★↦id★₁-source = id ★ ↦ id ★

left-path-id★↦id★₁-target :
  renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}) ⊢ (★ ⇒ ★) ∼ (★ ⇒ ★)
left-path-id★↦id★₁-target =
  C.↑ᶜ C.close-instᶜ (Ex.X?-inst-domain ↦ Ex.X!)

left-path-id★↦id★₂-source :
  applyEnv (bind (＇ Fin.zero)) (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))
    ⊢ (★ ⇒ ★) ∼ (★ ⇒ ★)
left-path-id★↦id★₂-source = id ★ ↦ id ★

left-path-id★↦id★₂-target :
  applyEnv (bind (＇ Fin.zero)) (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))
    ⊢ (★ ⇒ ★) ∼ (★ ⇒ ★)
left-path-id★↦id★₂-target =
  applyConsistency (bind (＇ Fin.zero)) left-path-id★↦id★₁-target

left-path-X⇒X₁ : Ty 2
left-path-X⇒X₁ = ＇ Fin.zero ⇒ ＇ Fin.zero

left-path-X⇒X₂ : Ty 3
left-path-X⇒X₂ = ＇ Fin.zero ⇒ ＇ Fin.zero

left-path-gen₁ :
  C.extᵐ (idᶜ {Δ = 0}) ⊢ (★ ⇒ ★) ∼ `∀ left-path-X⇒X₁
left-path-gen₁ =
  gen_ ⦃ z∈B = ∈-fun-left var-∈ ⦄
    ((id {μ = C.flipᵐ (genᵐ (C.extᵐ (idᶜ {Δ = 0})))}
        (＇ Fin.zero) !)
      ↦
     (？_ {μ = genᵐ (C.extᵐ (idᶜ {Δ = 0}))}
        (id (＇ Fin.zero))))
    (λ ())

left-path-gen₂ :
  C.extᵐ (C.extᵐ (idᶜ {Δ = 0})) ⊢ (★ ⇒ ★) ∼
    `∀ left-path-X⇒X₂
left-path-gen₂ =
  gen_ ⦃ z∈B = ∈-fun-left var-∈ ⦄
    ((id {μ = C.flipᵐ
        (genᵐ (C.extᵐ (C.extᵐ (idᶜ {Δ = 0}))))}
        (＇ Fin.zero) !)
      ↦
     (？_ {μ = genᵐ (C.extᵐ (C.extᵐ (idᶜ {Δ = 0})))}
        (id (＇ Fin.zero))))
    (λ ())

left-path-reveal★₁ : Conv↑ 1 (＇ Fin.zero ⇒ ＇ Fin.zero) (★ ⇒ ★)
left-path-reveal★₁ = seal Fin.zero ★ ↦↑ unseal Fin.zero ★

left-path-source-U∋₁ : Ex.right-store₁ ∋ Fin.zero ⦂ ★
left-path-source-U∋₁ = Z∋ refl

left-path-target-U∋₁ : left-path-target-store₁ ∋ Fin.zero ⦂ ★
left-path-target-U∋₁ = Z∋ refl

left-path-U-rep₁ :
  CTX.StoreRepImp left-path-world₁ Fin.zero Fin.zero
left-path-U-rep₁ = CTX.store-rep-imp ★⊑★

left-path-rebase-U₁ :
  CTX.RebaseAt left-path-world₁ left-path-world₁ Fin.zero Fin.zero
left-path-rebase-U₁ =
  CTX.sameWorldRebaseAt refl left-path-U-rep₁

left-path-reveal★₁-source-⊢ : Ex.right-store₁ ⊢↑ left-path-reveal★₁
left-path-reveal★₁-source-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-source-U∋₁)
    (⊢↑-unseal left-path-source-U∋₁)

left-path-reveal★₁-target-⊢ :
  left-path-target-store₁ ⊢↑ left-path-reveal★₁
left-path-reveal★₁-target-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-target-U∋₁)
    (⊢↑-unseal left-path-target-U∋₁)

left-path-reveal★₁-source-⊢ˣ :
  Ex.right-store₁ Conv.⊢↑[ just Fin.zero ] left-path-reveal★₁
left-path-reveal★₁-source-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-U∋₁)
    (Conv.⊢↑-unsealˣ left-path-source-U∋₁)

left-path-reveal★₁-target-⊢ˣ :
  left-path-target-store₁ Conv.⊢↑[ just Fin.zero ] left-path-reveal★₁
left-path-reveal★₁-target-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-target-U∋₁)
    (Conv.⊢↑-unsealˣ left-path-target-U∋₁)

left-path-Y-reveal₂ :
  Conv↑ 2 (＇ Fin.zero ⇒ ＇ Fin.zero)
    (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Y-reveal₂ =
  seal Fin.zero (＇ (Fin.suc Fin.zero)) ↦↑
  unseal Fin.zero (＇ (Fin.suc Fin.zero))

left-path-Z-reveal₂ :
  Conv↑ 2 (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero)) (★ ⇒ ★)
left-path-Z-reveal₂ =
  seal (Fin.suc Fin.zero) ★ ↦↑ unseal (Fin.suc Fin.zero) ★

left-path-source-Y∋₂ :
  Ex.right-store₂ ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
left-path-source-Y∋₂ = Z∋ refl

left-path-source-Z∋₂ :
  Ex.right-store₂ ∋ Fin.suc Fin.zero ⦂ ★
left-path-source-Z∋₂ = S-bind∋ (Z∋ refl) refl

left-path-target-Y∋₂ :
  left-path-target-store₂ ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
left-path-target-Y∋₂ = Z∋ refl

left-path-target-Z∋₂ :
  left-path-target-store₂ ∋ Fin.suc Fin.zero ⦂ ★
left-path-target-Z∋₂ = S-bind∋ (Z∋ refl) refl

left-path-Y-rep₂ :
  CTX.StoreRepImp left-path-world₂ Fin.zero Fin.zero
left-path-Y-rep₂ = CTX.store-rep-imp ★⊑★

left-path-Z-rep₂ :
  CTX.StoreRepImp left-path-world₂
    (Fin.suc Fin.zero) (Fin.suc Fin.zero)
left-path-Z-rep₂ = CTX.store-rep-imp ★⊑★

left-path-rebase-Y₂ :
  CTX.RebaseAt left-path-world₂ left-path-world₂
    Fin.zero Fin.zero
left-path-rebase-Y₂ =
  CTX.sameWorldRebaseAt refl left-path-Y-rep₂

left-path-rebase-Z₂ :
  CTX.RebaseAt left-path-world₂ left-path-world₂
    (Fin.suc Fin.zero) (Fin.suc Fin.zero)
left-path-rebase-Z₂ =
  CTX.sameWorldRebaseAt refl left-path-Z-rep₂

left-path-Y-reveal₂-source-⊢ : Ex.right-store₂ ⊢↑ left-path-Y-reveal₂
left-path-Y-reveal₂-source-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-source-Y∋₂)
    (⊢↑-unseal left-path-source-Y∋₂)

left-path-Y-reveal₂-target-⊢ :
  left-path-target-store₂ ⊢↑ left-path-Y-reveal₂
left-path-Y-reveal₂-target-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-target-Y∋₂)
    (⊢↑-unseal left-path-target-Y∋₂)

left-path-Z-reveal₂-source-⊢ : Ex.right-store₂ ⊢↑ left-path-Z-reveal₂
left-path-Z-reveal₂-source-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-source-Z∋₂)
    (⊢↑-unseal left-path-source-Z∋₂)

left-path-Z-reveal₂-target-⊢ :
  left-path-target-store₂ ⊢↑ left-path-Z-reveal₂
left-path-Z-reveal₂-target-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-target-Z∋₂)
    (⊢↑-unseal left-path-target-Z∋₂)

left-path-Y-reveal₂-source-⊢ˣ :
  Ex.right-store₂ Conv.⊢↑[ just Fin.zero ] left-path-Y-reveal₂
left-path-Y-reveal₂-source-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-Y∋₂)
    (Conv.⊢↑-unsealˣ left-path-source-Y∋₂)

left-path-Y-reveal₂-target-⊢ˣ :
  left-path-target-store₂ Conv.⊢↑[ just Fin.zero ] left-path-Y-reveal₂
left-path-Y-reveal₂-target-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-target-Y∋₂)
    (Conv.⊢↑-unsealˣ left-path-target-Y∋₂)

left-path-Z-reveal₂-source-⊢ˣ :
  Ex.right-store₂ Conv.⊢↑[ just (Fin.suc Fin.zero) ] left-path-Z-reveal₂
left-path-Z-reveal₂-source-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-Z∋₂)
    (Conv.⊢↑-unsealˣ left-path-source-Z∋₂)

left-path-Z-reveal₂-target-⊢ˣ :
  left-path-target-store₂ Conv.⊢↑[ just (Fin.suc Fin.zero) ] left-path-Z-reveal₂
left-path-Z-reveal₂-target-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-target-Z∋₂)
    (Conv.⊢↑-unsealˣ left-path-target-Z∋₂)

left-path-X⇒X⊑X⇒X₁ :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ left-path-world₁ ⟩
    (＇ Fin.zero ⇒ ＇ Fin.zero)
left-path-X⇒X⊑X⇒X₁ = ⇒⊑⇒ X⊑X X⊑X

left-path-X⇒X⊑X⇒X₂ :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ left-path-world₂ ⟩
    (＇ Fin.zero ⇒ ＇ Fin.zero)
left-path-X⇒X⊑X⇒X₂ = ⇒⊑⇒ X⊑X X⊑X

left-path-Z⇒Z⊑Z⇒Z₂ :
  (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₂ ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z₂ = ⇒⊑⇒ X⊑X X⊑X

left-path-initial-upcast :
  reflWorld store-empty ∣ [] ⊢²
    Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩
    ⊑ Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩ ∶
      ★⇒★⊑★⇒★² {W = reflWorld store-empty}
left-path-initial-upcast =
  cast⊑cast²
    {C = `∀ Ex.X⇒X} {C′ = `∀ Ex.X⇒X}
    {A = ★ ⇒ ★} {A′ = ★ ⇒ ★}
    Ex.ν̅α-α♯→α♭ Ex.ν̅α-α♯→α♭ polyId-refl²
    (★⇒★⊑★⇒★² {W = reflWorld store-empty})

left-path-initial-poly-to-star :
  reflWorld store-empty ∣ [] ⊢²
    (Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩) ⟨ Ex.να-α!→α? ⟩
    ⊑ Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩ ∶
      ∀X⇒X⊑★⇒★² {W = reflWorld store-empty}
left-path-initial-poly-to-star =
  CTI2.cast⊑²
    {A = ★ ⇒ ★} {A′ = `∀ Ex.X⇒X} {B = ★ ⇒ ★}
    Ex.να-α!→α? left-path-initial-upcast
    (∀X⇒X⊑★⇒★² {W = reflWorld store-empty})

left-path-initial-function :
  reflWorld store-empty ∣ [] ⊢²
    ((Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩) ⟨ Ex.να-α!→α? ⟩)
      ⦂∀ Ex.X⇒X [ Ex.ℕᵗ ]
    ⊑ Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩ ∶
      ℕ⇒ℕ⊑★⇒★² {W = reflWorld store-empty}
left-path-initial-function =
  CTI2.•⊑²
    {C = Ex.X⇒X} {A = Ex.ℕᵗ} {B = ★ ⇒ ★}
    (∀X⇒X⊑★⇒★² {W = reflWorld store-empty})
    left-path-initial-poly-to-star left-path-ℕ⊑★₀
    (ℕ⇒ℕ⊑★⇒★² {W = reflWorld store-empty})

left-path-argument₀ :
  reflWorld store-empty ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ Ex12.example12-ℕ! ⟩ ∶ left-path-ℕ⊑★₀
left-path-argument₀ =
  ⊑cast² Ex12.example12-ℕ!
    (κ⊑κ² (κℕ 7) (ℕ⊑ℕ² {W = reflWorld store-empty}))
    left-path-ℕ⊑★₀

left-path-base₁ :
  left-path-world₁ ∣ [] ⊢²
    (((Λ (ƛ (` 0))) ⦂∀ left-path-X⇒X₁ [ ＇ Fin.zero ])
      ↑ left-path-reveal★₁)
      ⟨ left-path-id★↦id★₁-source ⟩
    ⊑ (((Λ (ƛ (` 0))) ⦂∀ left-path-X⇒X₁ [ ＇ Fin.zero ])
      ↑ left-path-reveal★₁)
      ⟨ left-path-id★↦id★₁-target ⟩ ∶
        ★⇒★⊑★⇒★² {W = left-path-world₁}
left-path-base₁ =
  cast⊑cast² left-path-id★↦id★₁-source left-path-id★↦id★₁-target
    (reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-U₁ CTX.same-[]
      left-path-reveal★₁-source-⊢ˣ left-path-reveal★₁-target-⊢ˣ
      (•⊑•²
        {C = left-path-X⇒X₁} {C′ = left-path-X⇒X₁}
        {A = ＇ Fin.zero} {A′ = ＇ Fin.zero}
        (∀X⇒X⊑∀X⇒X² {W = left-path-world₁})
        polyId-refl²ʷ
        (Imprecision.X⊑X {X = Fin.zero})
        left-path-X⇒X⊑X⇒X₁)
      (★⇒★⊑★⇒★² {W = left-path-world₁}))
    (★⇒★⊑★⇒★² {W = left-path-world₁})

left-path-function₁ :
  left-path-world₁ ∣ [] ⊢²
    ((((Λ (ƛ (` 0))) ⦂∀ left-path-X⇒X₁ [ ＇ Fin.zero ])
      ↑ left-path-reveal★₁)
      ⟨ left-path-id★↦id★₁-source ⟩
      ⟨ left-path-gen₁ ⟩)
      ⦂∀ left-path-X⇒X₁ [ ‵ `ℕ ]
    ⊑ (((Λ (ƛ (` 0))) ⦂∀ left-path-X⇒X₁ [ ＇ Fin.zero ])
      ↑ left-path-reveal★₁)
      ⟨ left-path-id★↦id★₁-target ⟩ ∶
        ℕ⇒ℕ⊑★⇒★² {W = left-path-world₁}
left-path-function₁ =
  CTI2.•⊑²
    {C = left-path-X⇒X₁} {A = ‵ `ℕ} {B = ★ ⇒ ★}
    (∀X⇒X⊑★⇒★² {W = left-path-world₁})
    (CTI2.cast⊑²
      {A = ★ ⇒ ★} {A′ = `∀ left-path-X⇒X₁} {B = ★ ⇒ ★}
      left-path-gen₁ left-path-base₁
      (∀X⇒X⊑★⇒★² {W = left-path-world₁}))
    left-path-ℕ⊑★₁
    (ℕ⇒ℕ⊑★⇒★² {W = left-path-world₁})

left-path-argument₁ :
  left-path-world₁ ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₁ ⟩ ∶ left-path-ℕ⊑★₁
left-path-argument₁ =
  ⊑cast² left-path-ℕ!₁
    (κ⊑κ² (κℕ 7) (ℕ⊑ℕ² {W = left-path-world₁}))
    left-path-ℕ⊑★₁

left-path-lambda₂ :
  left-path-world₂ ∣ [] ⊢² ƛ (` 0) ⊑ ƛ (` 0) ∶
    left-path-X⇒X⊑X⇒X₂
left-path-lambda₂ =
  ƛ⊑ƛ²
    {A = ＇ Fin.zero} {A′ = ＇ Fin.zero}
    {B = ＇ Fin.zero} {B′ = ＇ Fin.zero}
    {pA = X⊑X} {pB = X⊑X}
    (x⊑x² {p = X⊑X} Zʷ)

left-path-base₂ :
  left-path-world₂ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ left-path-Y-reveal₂)
      ↑ left-path-Z-reveal₂)
      ⟨ left-path-id★↦id★₂-source ⟩
    ⊑ (((ƛ (` 0)) ↑ left-path-Y-reveal₂)
      ↑ left-path-Z-reveal₂)
      ⟨ left-path-id★↦id★₂-target ⟩ ∶
        ★⇒★⊑★⇒★² {W = left-path-world₂}
left-path-base₂ =
  cast⊑cast² left-path-id★↦id★₂-source left-path-id★↦id★₂-target
    (reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Z₂ CTX.same-[]
      left-path-Z-reveal₂-source-⊢ˣ left-path-Z-reveal₂-target-⊢ˣ
      (reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Y₂ CTX.same-[]
        left-path-Y-reveal₂-source-⊢ˣ left-path-Y-reveal₂-target-⊢ˣ
        left-path-lambda₂
        left-path-Z⇒Z⊑Z⇒Z₂)
      (★⇒★⊑★⇒★² {W = left-path-world₂}))
    (★⇒★⊑★⇒★² {W = left-path-world₂})

left-path-function₂ :
  left-path-world₂ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ left-path-Y-reveal₂)
      ↑ left-path-Z-reveal₂)
      ⟨ left-path-id★↦id★₂-source ⟩
      ⟨ left-path-gen₂ ⟩)
      ⦂∀ left-path-X⇒X₂ [ ‵ `ℕ ]
    ⊑ (((ƛ (` 0)) ↑ left-path-Y-reveal₂)
      ↑ left-path-Z-reveal₂)
      ⟨ left-path-id★↦id★₂-target ⟩ ∶
        ℕ⇒ℕ⊑★⇒★² {W = left-path-world₂}
left-path-function₂ =
  CTI2.•⊑²
    {C = left-path-X⇒X₂} {A = ‵ `ℕ} {B = ★ ⇒ ★}
    (∀X⇒X⊑★⇒★² {W = left-path-world₂})
    (CTI2.cast⊑²
      {A = ★ ⇒ ★} {A′ = `∀ left-path-X⇒X₂} {B = ★ ⇒ ★}
      left-path-gen₂ left-path-base₂
      (∀X⇒X⊑★⇒★² {W = left-path-world₂}))
    left-path-ℕ⊑★₂
    (ℕ⇒ℕ⊑★⇒★² {W = left-path-world₂})

left-path-argument₂ :
  left-path-world₂ ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩ ∶ left-path-ℕ⊑★₂
left-path-argument₂ =
  ⊑cast² left-path-ℕ!₂
    (κ⊑κ² (κℕ 7) (ℕ⊑ℕ² {W = left-path-world₂}))
    left-path-ℕ⊑★₂

left-path-checkpoint₀ :
  reflWorld store-empty ∣ [] ⊢² left-path-more-precise
    ⊑ left-path-more-imprecise ∶ left-path-ℕ⊑★₀
left-path-checkpoint₀ =
  ·⊑·² left-path-initial-function left-path-argument₀

left-path-checkpoint₁ :
  left-path-world₁ ∣ [] ⊢² Ex.right₁
    ⊑ left-path-target₁ ∶ left-path-ℕ⊑★₁
left-path-checkpoint₁ =
  ·⊑·² left-path-function₁ left-path-argument₁

left-path-checkpoint₂ :
  left-path-world₂ ∣ [] ⊢² Ex.right₂
    ⊑ left-path-target₂ ∶ left-path-ℕ⊑★₂
left-path-checkpoint₂ =
  ·⊑·² left-path-function₂ left-path-argument₂

left-path-source-X∋₃ : Ex.right-store₃ ∋ Fin.zero ⦂ ‵ `ℕ
left-path-source-X∋₃ = Z∋ refl

left-path-source-Y∋₃ :
  Ex.right-store₃ ∋ Fin.suc Fin.zero ⦂ ＇ (Fin.suc (Fin.suc Fin.zero))
left-path-source-Y∋₃ = S-bind∋ (Z∋ refl) refl

left-path-source-Z∋₃ :
  Ex.right-store₃ ∋ Fin.suc (Fin.suc Fin.zero) ⦂ ★
left-path-source-Z∋₃ = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

left-path-target-Y∋₃ :
  left-path-target-store₃ ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
left-path-target-Y∋₃ = Z∋ refl

left-path-target-Z∋₃ :
  left-path-target-store₃ ∋ Fin.suc Fin.zero ⦂ ★
left-path-target-Z∋₃ = S-bind∋ (Z∋ refl) refl

left-path-source-X-rep₃ :
  CTX.StoreRepImp left-path-world₃ Fin.zero Fin.zero
left-path-source-X-rep₃ =
  CTX.store-rep-imp (ℕ⊑★² {W = left-path-world₃})

left-path-source-Z-rep₃ :
  CTX.StoreRepImp left-path-world₃
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-source-Z-rep₃ = CTX.store-rep-imp ★⊑★

left-path-source-Y-rep₃-YZ :
  CTX.StoreRepImp left-path-world₃-YZ (Fin.suc Fin.zero) Fin.zero
left-path-source-Y-rep₃-YZ = CTX.store-rep-imp ★⊑★

left-path-source-Z-rep₃-YZ :
  CTX.StoreRepImp left-path-world₃-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-source-Z-rep₃-YZ = CTX.store-rep-imp ★⊑★

left-path-rebase-Y-YZ₃ :
  CTX.RebaseAt left-path-world₃-YZ left-path-world₃-YZ
    (Fin.suc Fin.zero) Fin.zero
left-path-rebase-Y-YZ₃ =
  CTX.sameWorldRebaseAt refl left-path-source-Y-rep₃-YZ

left-path-rebase-Z-YZ₃ :
  CTX.RebaseAt left-path-world₃-YZ left-path-world₃-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-Z-YZ₃ =
  CTX.sameWorldRebaseAt refl left-path-source-Z-rep₃-YZ

left-path-rebase-X-YZ₃ᴸ :
  CTX.RebaseAtᴸ left-path-world₃-YZ left-path-world₃-YZ
    (just Fin.zero)
left-path-rebase-X-YZ₃ᴸ =
  CTX.rebase-onlyᴸ refl
    (λ { Fin.zero (); (Fin.suc Fin.zero) () })
    (ℕ⊑★² {W = left-path-world₃-YZ})

left-path-rebase-XZ-Z₃ :
  CTX.RebaseAt left-path-world₃ left-path-world₃
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-XZ-Z₃ =
  CTX.sameWorldRebaseAt refl left-path-source-Z-rep₃

left-path-rebase-XZ-X₃ :
  CTX.RebaseAt left-path-world₃ left-path-world₃
    Fin.zero Fin.zero
left-path-rebase-XZ-X₃ =
  CTX.sameWorldRebaseAt refl left-path-source-X-rep₃

left-path-source-Y-reveal₃-⊢ : Ex.right-store₃ ⊢↑ example12-target-Y-reveal
left-path-source-Y-reveal₃-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-source-Y∋₃)
    (⊢↑-unseal left-path-source-Y∋₃)

left-path-target-Y-reveal₃-⊢ :
  left-path-target-store₃ ⊢↑ left-path-Y-reveal₂
left-path-target-Y-reveal₃-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-target-Y∋₃)
    (⊢↑-unseal left-path-target-Y∋₃)

left-path-source-Y-reveal₃-⊢ˣ :
  Ex.right-store₃ Conv.⊢↑[ just (Fin.suc Fin.zero) ] example12-target-Y-reveal
left-path-source-Y-reveal₃-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-Y∋₃)
    (Conv.⊢↑-unsealˣ left-path-source-Y∋₃)

left-path-target-Y-reveal₃-⊢ˣ :
  left-path-target-store₃ Conv.⊢↑[ just Fin.zero ] left-path-Y-reveal₂
left-path-target-Y-reveal₃-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-target-Y∋₃)
    (Conv.⊢↑-unsealˣ left-path-target-Y∋₃)

left-path-source-Z-reveal₃-⊢ˣ :
  Ex.right-store₃ Conv.⊢↑[ just (Fin.suc (Fin.suc Fin.zero)) ]
    example12-target-Z-reveal
left-path-source-Z-reveal₃-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-Z∋₃)
    (Conv.⊢↑-unsealˣ left-path-source-Z∋₃)

left-path-target-Z-reveal₃-⊢ˣ :
  left-path-target-store₃ Conv.⊢↑[ just (Fin.suc Fin.zero) ] left-path-Z-reveal₂
left-path-target-Z-reveal₃-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-target-Z∋₃)
    (Conv.⊢↑-unsealˣ left-path-target-Z∋₃)

left-path-source-X-reveal₃-⊢ˣ :
  Ex.right-store₃ Conv.⊢↑[ just Fin.zero ] example12-target-X-reveal
left-path-source-X-reveal₃-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-X∋₃)
    (Conv.⊢↑-unsealˣ left-path-source-X∋₃)

left-path-Y-var⊑YZ₃ :
  ＇ (Fin.suc Fin.zero) ⊑ᵂ⟨ left-path-world₃-YZ ⟩ ＇ Fin.zero
left-path-Y-var⊑YZ₃ = Imprecision.X⊑X {X = Fin.suc Fin.zero}

left-path-Z-var⊑XZ₃ :
  ＇ (Fin.suc (Fin.suc Fin.zero)) ⊑ᵂ⟨ left-path-world₃ ⟩
    ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑XZ₃ =
  Imprecision.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}

left-path-Y⇒Y⊑Y⇒Y-YZ₃ :
  (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₃-YZ ⟩ (＇ Fin.zero ⇒ ＇ Fin.zero)
left-path-Y⇒Y⊑Y⇒Y-YZ₃ =
  ⇒⊑⇒ left-path-Y-var⊑YZ₃ left-path-Y-var⊑YZ₃

left-path-Z⇒Z⊑Z⇒Z-XZ₃ :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ left-path-world₃ ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-XZ₃ =
  ⇒⊑⇒ left-path-Z-var⊑XZ₃ left-path-Z-var⊑XZ₃

left-path-Z-var⊑YZ₃ :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₃-YZ ⟩ ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑YZ₃ =
  Imprecision.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}

left-path-Z⇒Z⊑Z⇒Z-YZ₃ :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ left-path-world₃-YZ ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-YZ₃ =
  ⇒⊑⇒ left-path-Z-var⊑YZ₃ left-path-Z-var⊑YZ₃

left-path-Z-var⊑★-YZ₃ :
  left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★ → ⊥
left-path-Z-var⊑★-YZ₃ ()

left-path-Z⇒Z⊑★⇒★-YZ₃ :
  left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★ → ⊥
left-path-Z⇒Z⊑★⇒★-YZ₃ ()

left-path-X-var⊑★-XZ₃ :
  ＇ Fin.zero ⊑ᵂ⟨ left-path-world₃ ⟩ ★
left-path-X-var⊑★-XZ₃ = Imprecision.X⊑★ {X = Fin.zero} refl

left-path-X-var⊑★-YZ₃ :
  ＇ Fin.zero ⊑ᵂ⟨ left-path-world₃-YZ ⟩ ★
left-path-X-var⊑★-YZ₃ = Imprecision.X⊑★ {X = Fin.zero} refl

left-path-X⇒X⊑★⇒★-XZ₃ :
  (＇ Fin.zero ⇒ ＇ Fin.zero) ⊑ᵂ⟨ left-path-world₃ ⟩ (★ ⇒ ★)
left-path-X⇒X⊑★⇒★-XZ₃ =
  ⇒⊑⇒ left-path-X-var⊑★-XZ₃ left-path-X-var⊑★-XZ₃

left-path-X⇒X⊑★⇒★-YZ₃ :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ left-path-world₃-YZ ⟩ (★ ⇒ ★)
left-path-X⇒X⊑★⇒★-YZ₃ =
  ⇒⊑⇒ left-path-X-var⊑★-YZ₃ left-path-X-var⊑★-YZ₃

left-path-target-lambda₃ : Term (Δ′ left-path-target-step₂)
left-path-target-lambda₃ = ƛ renameᵗᵐ (keep wk↪ᵗ) (` 0)

left-path-lambda₃-YZ :
  left-path-world₃-YZ ∣ [] ⊢² ƛ (` 0) ⊑ left-path-target-lambda₃ ∶
    left-path-Y⇒Y⊑Y⇒Y-YZ₃
left-path-lambda₃-YZ =
  ƛ⊑ƛ²
    {A = ＇ (Fin.suc Fin.zero)} {A′ = ＇ Fin.zero}
    {B = ＇ (Fin.suc Fin.zero)} {B′ = ＇ Fin.zero}
    {pA = left-path-Y-var⊑YZ₃} {pB = left-path-Y-var⊑YZ₃}
    (x⊑x² {p = left-path-Y-var⊑YZ₃} Zʷ)

left-path-Y-revealed₃-YZ :
  left-path-world₃-YZ ∣ [] ⊢²
    (ƛ (` 0)) ↑ example12-target-Y-reveal
    ⊑ left-path-target-lambda₃ ↑ left-path-Y-reveal₂ ∶
      left-path-Z⇒Z⊑Z⇒Z-YZ₃
left-path-Y-revealed₃-YZ =
  reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Y-YZ₃ CTX.same-[]
    left-path-source-Y-reveal₃-⊢ˣ left-path-target-Y-reveal₃-⊢ˣ
    left-path-lambda₃-YZ left-path-Z⇒Z⊑Z⇒Z-YZ₃

left-path-target-Z-revealed₃-YZ :
  left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★ → ⊥
left-path-target-Z-revealed₃-YZ ()

left-path-both-Z-revealed₃-YZ :
  left-path-world₃-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂ ∶
      ★⇒★⊑★⇒★² {W = left-path-world₃-YZ}
left-path-both-Z-revealed₃-YZ =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl
    left-path-rebase-Z-YZ₃ CTX.same-[]
    left-path-source-Z-reveal₃-⊢ˣ left-path-target-Z-reveal₃-⊢ˣ
    left-path-Y-revealed₃-YZ
    (★⇒★⊑★⇒★² {W = left-path-world₃-YZ})

left-path-source-id₃-YZ :
  left-path-world₃-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂ ∶
      ★⇒★⊑★⇒★² {W = left-path-world₃-YZ}
left-path-source-id₃-YZ =
  CTI2.cast⊑² example12-target-id★↦id★
    left-path-both-Z-revealed₃-YZ
    (★⇒★⊑★⇒★² {W = left-path-world₃-YZ})

left-path-source-X?₃-YZ :
  left-path-world₃-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩)
      ⟨ example12-target-X?↦X? ⟩
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂ ∶
      left-path-X⇒X⊑★⇒★-YZ₃
left-path-source-X?₃-YZ =
  CTI2.cast⊑² example12-target-X?↦X? left-path-source-id₃-YZ
    left-path-X⇒X⊑★⇒★-YZ₃

left-path-function₃ :
  left-path-world₃-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩)
      ⟨ example12-target-X?↦X? ⟩)
      ↑ example12-target-X-reveal
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂ ∶
      ℕ⇒ℕ⊑★⇒★² {W = left-path-world₃-YZ}
left-path-function₃ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₃ᴸ
    CTX.same-[] left-path-source-X-reveal₃-⊢ˣ
    left-path-source-X?₃-YZ
    (ℕ⇒ℕ⊑★⇒★² {W = left-path-world₃-YZ})

left-path-target-id★₃ :
  renameEnv∼ (skip id↪ᵗ) (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))
    ⊢ ★ ∼ ★
left-path-target-id★₃ =
  C.renameᵐᶜ (skip id↪ᵗ) (C.↑ᶜ (C.close-instᶜ Ex.X!))

left-path-target-result-id★₃ :
  applyEnv (bind (＇ Fin.zero)) (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))
    ⊢ ★ ∼ ★
left-path-target-result-id★₃ =
  applyConsistency (bind (＇ Fin.zero)) (C.↑ᶜ (C.close-instᶜ Ex.X!))

left-path-argument₃ :
  left-path-world₃-YZ ∣ [] ⊢² $ (κℕ 7)
    ⊑ ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ C.sym∼ left-path-target-result-id★₃ ⟩ ∶
      ℕ⊑★² {W = left-path-world₃-YZ}
left-path-argument₃ =
  ⊑cast² (C.sym∼ left-path-target-result-id★₃)
    (⊑cast² left-path-ℕ!₂
      (κ⊑κ² (κℕ 7) (ℕ⊑ℕ² {W = left-path-world₃-YZ}))
      (ℕ⊑★² {W = left-path-world₃-YZ}))
    (ℕ⊑★² {W = left-path-world₃-YZ})

left-path-checkpoint₃ :
  left-path-world₃-YZ ∣ [] ⊢² Ex.right₃
    ⊑ left-path-target₃ ∶ ℕ⊑★² {W = left-path-world₃-YZ}
left-path-checkpoint₃ =
  ⊑cast² left-path-target-result-id★₃
    (·⊑·² left-path-function₃ left-path-argument₃)
    (ℕ⊑★² {W = left-path-world₃-YZ})

left-path-source-X∋₄ : Ex.right-store₄ ∋ Fin.zero ⦂ ‵ `ℕ
left-path-source-X∋₄ = Z∋ refl

left-path-target-Y∋₄ :
  left-path-target-store₄ ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
left-path-target-Y∋₄ = Z∋ refl

left-path-target-Z∋₄ :
  left-path-target-store₄ ∋ Fin.suc Fin.zero ⦂ ★
left-path-target-Z∋₄ = S-bind∋ (Z∋ refl) refl

left-path-source-X-rep₄ :
  CTX.StoreRepImp left-path-world₄ Fin.zero Fin.zero
left-path-source-X-rep₄ =
  CTX.store-rep-imp (ℕ⊑★² {W = left-path-world₄})

left-path-rebase-XZ-X₄ :
  CTX.RebaseAt left-path-world₄ left-path-world₄ Fin.zero Fin.zero
left-path-rebase-XZ-X₄ =
  CTX.sameWorldRebaseAt refl left-path-source-X-rep₄

left-path-source-X-seal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↓[ just Fin.zero ] example12-target-X-seal
left-path-source-X-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ left-path-source-X∋₄

left-path-source-X-unseal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↑[ just Fin.zero ] example12-target-X-unseal
left-path-source-X-unseal₄-⊢ˣ =
  Conv.⊢↑-unsealˣ left-path-source-X∋₄

left-path-ℕ⊑★₄-YZ :
  (‵ `ℕ) ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ★
left-path-ℕ⊑★₄-YZ = ℕ⊑★² {W = left-path-world₄-YZ}

left-path-X-var⊑★-YZ₄ :
  ＇ Fin.zero ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ★
left-path-X-var⊑★-YZ₄ = Imprecision.X⊑★ {X = Fin.zero} refl

left-path-rebase-X-YZ₄ᴸ :
  CTX.RebaseAtᴸ left-path-world₄-YZ left-path-world₄-YZ
    (just Fin.zero)
left-path-rebase-X-YZ₄ᴸ =
  CTX.rebase-onlyᴸ refl
    (λ { Fin.zero (); (Fin.suc Fin.zero) () })
    (ℕ⊑★² {W = left-path-world₄-YZ})

left-path-tag-rebase-X-YZ₄ᴸ :
  CTX.TagRebaseAtᴸ left-path-world₄-YZ left-path-world₄-YZ
    (just Fin.zero) nothing
left-path-tag-rebase-X-YZ₄ᴸ =
  CTX.tag-rebase-onlyᴸ refl
    (λ { Fin.zero (); (Fin.suc Fin.zero) () })
    (ℕ⊑★² {W = left-path-world₄-YZ})

left-path-source-X?₄-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩)
      ⟨ example12-target-X?↦X? ⟩
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂ ∶
      ⇒⊑⇒ left-path-X-var⊑★-YZ₄ left-path-X-var⊑★-YZ₄
left-path-source-X?₄-YZ = left-path-source-X?₃-YZ

left-path-argument₄-base :
  left-path-world₄-YZ ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩ ∶ left-path-ℕ⊑★₄-YZ
left-path-argument₄-base =
  ⊑cast² left-path-ℕ!₂
    (κ⊑κ² (κℕ 7) (ℕ⊑ℕ² {W = left-path-world₄-YZ}))
    left-path-ℕ⊑★₄-YZ

left-path-argument₄ :
  left-path-world₄-YZ ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩ ∶
      left-path-ℕ⊑★₄-YZ
left-path-argument₄ = left-path-argument₄-base

left-path-argument₄-sealed :
  left-path-world₄-YZ ∣ [] ⊢²
    ($ (κℕ 7)) ↓ example12-target-X-seal
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-argument₄-sealed =
  CTI2.conceal⊑² CTX.impEnvMono-refl left-path-tag-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-seal₄-⊢ˣ
    left-path-argument₄ left-path-X-var⊑★-YZ₄

left-path-application₄ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩)
      ⟨ example12-target-X?↦X? ⟩)
      · (($ (κℕ 7)) ↓ example12-target-X-seal)
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-application₄ =
  ⊑cast² left-path-target-result-id★₃
    (·⊑·² left-path-source-X?₄-YZ left-path-argument₄-sealed)
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₄ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₄
    ⊑ left-path-target₄ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₄ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-application₄ left-path-ℕ⊑★₄-YZ

left-path-source-id₄-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂ ∶
      ★⇒★⊑★⇒★² {W = left-path-world₄-YZ}
left-path-source-id₄-YZ = left-path-source-id₃-YZ

left-path-source-X!₄ :
  left-path-world₄-YZ ∣ [] ⊢²
    (($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩ ∶
      ★⊑★
left-path-source-X!₄ =
  CTI2.cast⊑² example12-target-X! left-path-argument₄-sealed ★⊑★

left-path-application₅-base :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩)
      · ((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩) ∶
      ★⊑★
left-path-application₅-base =
  ·⊑·² left-path-source-id₄-YZ left-path-source-X!₄

left-path-application₅-target-id :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩)
      · ((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-application₅-target-id =
  ⊑cast² left-path-target-result-id★₃ left-path-application₅-base ★⊑★

left-path-source-result-?X₅ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      ⟨ example12-target-id★↦id★ ⟩)
      · ((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩))
      ⟨ example12-target-★?X ⟩
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₅ =
  CTI2.cast⊑² example12-target-★?X left-path-application₅-target-id
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₅ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₅
    ⊑ left-path-target₄ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₅ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₅ left-path-ℕ⊑★₄-YZ

left-path-source-bare-Z₄-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂ ∶
      ★⇒★⊑★⇒★² {W = left-path-world₄-YZ}
left-path-source-bare-Z₄-YZ = left-path-both-Z-revealed₃-YZ

left-path-source-arg-id★₆ :
  C.flipᵐ
    (renameEnv∼ (skip id↪ᵗ)
      (applyEnv (bind (＇ Fin.zero))
        (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))))
    ⊢ ★ ∼ ★
left-path-source-arg-id★₆ = id ★

left-path-source-result-id★₆ :
  renameEnv∼ (skip id↪ᵗ)
    (applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))
    ⊢ ★ ∼ ★
left-path-source-result-id★₆ = id ★

left-path-source-X!-id₆ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ⟨ left-path-source-arg-id★₆ ⟩
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩ ∶
      ★⊑★
left-path-source-X!-id₆ =
  CTI2.cast⊑² left-path-source-arg-id★₆ left-path-source-X!₄ ★⊑★

left-path-application₆-base :
  left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      · (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ⟨ left-path-source-arg-id★₆ ⟩)
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩) ∶
      ★⊑★
left-path-application₆-base =
  ·⊑·² left-path-source-bare-Z₄-YZ left-path-source-X!-id₆

left-path-source-result-id₆ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      · (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ⟨ left-path-source-arg-id★₆ ⟩))
      ⟨ left-path-source-result-id★₆ ⟩
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₆ =
  cast⊑cast² left-path-source-result-id★₆ left-path-target-result-id★₃
    left-path-application₆-base ★⊑★

left-path-source-result-?X₆ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      · (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ⟨ left-path-source-arg-id★₆ ⟩))
      ⟨ left-path-source-result-id★₆ ⟩)
      ⟨ example12-target-★?X ⟩
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₆ =
  CTI2.cast⊑² example12-target-★?X left-path-source-result-id₆
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₆ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₆
    ⊑ left-path-target₄ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₆ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₆ left-path-ℕ⊑★₄-YZ

left-path-application₇-base :
  left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      · ((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩) ∶
      ★⊑★
left-path-application₇-base =
  ·⊑·² left-path-source-bare-Z₄-YZ left-path-source-X!₄

left-path-source-result-id₇ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      · ((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩))
      ⟨ left-path-source-result-id★₆ ⟩
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₇ =
  cast⊑cast² left-path-source-result-id★₆ left-path-target-result-id★₃
    left-path-application₇-base ★⊑★

left-path-source-result-?X₇ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      ↑ example12-target-Z-reveal)
      · ((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩))
      ⟨ left-path-source-result-id★₆ ⟩)
      ⟨ example12-target-★?X ⟩
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        ↑ left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₇ =
  CTI2.cast⊑² example12-target-★?X left-path-source-result-id₇
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₇ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₇
    ⊑ left-path-target₄ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₇ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₇ left-path-ℕ⊑★₄-YZ

left-path-source-Y∋₄ :
  Ex.right-store₄ ∋ Fin.suc Fin.zero ⦂ ＇ (Fin.suc (Fin.suc Fin.zero))
left-path-source-Y∋₄ = S-bind∋ (Z∋ refl) refl

left-path-source-Z∋₄ :
  Ex.right-store₄ ∋ Fin.suc (Fin.suc Fin.zero) ⦂ ★
left-path-source-Z∋₄ = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

left-path-source-Y-rep₄-YZ :
  CTX.StoreRepImp left-path-world₄-YZ (Fin.suc Fin.zero) Fin.zero
left-path-source-Y-rep₄-YZ = CTX.store-rep-imp ★⊑★

left-path-source-Z-rep₄-XZ :
  CTX.StoreRepImp left-path-world₄
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-source-Z-rep₄-XZ = CTX.store-rep-imp ★⊑★

left-path-source-Z-rep₄-YZ :
  CTX.StoreRepImp left-path-world₄-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-source-Z-rep₄-YZ = CTX.store-rep-imp ★⊑★

left-path-rebase-Y-YZ₄ :
  CTX.RebaseAt left-path-world₄-YZ left-path-world₄-YZ
    (Fin.suc Fin.zero) Fin.zero
left-path-rebase-Y-YZ₄ =
  CTX.sameWorldRebaseAt refl left-path-source-Y-rep₄-YZ

left-path-rebase-XZ-Z₄ :
  CTX.RebaseAt left-path-world₄ left-path-world₄
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-XZ-Z₄ =
  CTX.sameWorldRebaseAt refl left-path-source-Z-rep₄-XZ

left-path-rebase-Z-YZ₄ :
  CTX.RebaseAt left-path-world₄-YZ left-path-world₄-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-Z-YZ₄ =
  CTX.sameWorldRebaseAt refl left-path-source-Z-rep₄-YZ

left-path-source-Y-reveal₄-⊢ :
  Ex.right-store₄ ⊢↑ example12-target-Y-reveal
left-path-source-Y-reveal₄-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-source-Y∋₄)
    (⊢↑-unseal left-path-source-Y∋₄)

left-path-target-Y-reveal₄-⊢ :
  left-path-target-store₄ ⊢↑ left-path-Y-reveal₂
left-path-target-Y-reveal₄-⊢ =
  ⊢↑-⇒ (⊢↓-seal left-path-target-Y∋₄)
    (⊢↑-unseal left-path-target-Y∋₄)

left-path-source-Y-reveal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↑[ just (Fin.suc Fin.zero) ] example12-target-Y-reveal
left-path-source-Y-reveal₄-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-Y∋₄)
    (Conv.⊢↑-unsealˣ left-path-source-Y∋₄)

left-path-target-Y-reveal₄-⊢ˣ :
  left-path-target-store₄ Conv.⊢↑[ just Fin.zero ] left-path-Y-reveal₂
left-path-target-Y-reveal₄-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-target-Y∋₄)
    (Conv.⊢↑-unsealˣ left-path-target-Y∋₄)

left-path-source-Z-reveal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↑[ just (Fin.suc (Fin.suc Fin.zero)) ]
    example12-target-Z-reveal
left-path-source-Z-reveal₄-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-source-Z∋₄)
    (Conv.⊢↑-unsealˣ left-path-source-Z∋₄)

left-path-target-Z-reveal₄-⊢ˣ :
  left-path-target-store₄ Conv.⊢↑[ just (Fin.suc Fin.zero) ] left-path-Z-reveal₂
left-path-target-Z-reveal₄-⊢ˣ =
  Conv.⊢↑-⇒ˣ Conv.join-both (Conv.⊢↓-sealˣ left-path-target-Z∋₄)
    (Conv.⊢↑-unsealˣ left-path-target-Z∋₄)

left-path-target-Z-seal₂ : Conv↓ 2 ★ (＇ (Fin.suc Fin.zero))
left-path-target-Z-seal₂ = seal (Fin.suc Fin.zero) ★

left-path-target-Z-unseal₂ : Conv↑ 2 (＇ (Fin.suc Fin.zero)) ★
left-path-target-Z-unseal₂ = unseal (Fin.suc Fin.zero) ★

left-path-target-Y-seal₂ :
  Conv↓ 2 (＇ (Fin.suc Fin.zero)) (＇ Fin.zero)
left-path-target-Y-seal₂ =
  seal Fin.zero (＇ (Fin.suc Fin.zero))

left-path-target-Y-unseal₂ :
  Conv↑ 2 (＇ Fin.zero) (＇ (Fin.suc Fin.zero))
left-path-target-Y-unseal₂ =
  unseal Fin.zero (＇ (Fin.suc Fin.zero))

left-path-source-Z-unseal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↑[ just (Fin.suc (Fin.suc Fin.zero)) ]
    example12-target-Z-unseal
left-path-source-Z-unseal₄-⊢ˣ =
  Conv.⊢↑-unsealˣ left-path-source-Z∋₄

left-path-source-Z-unseal₄-⊢ :
  Ex.right-store₄ ⊢↑ example12-target-Z-unseal
left-path-source-Z-unseal₄-⊢ =
  ⊢↑-unseal left-path-source-Z∋₄

left-path-target-Z-unseal₄-⊢ˣ :
  left-path-target-store₄ Conv.⊢↑[ just (Fin.suc Fin.zero) ]
    left-path-target-Z-unseal₂
left-path-target-Z-unseal₄-⊢ˣ =
  Conv.⊢↑-unsealˣ left-path-target-Z∋₄

left-path-target-Z-unseal₄-⊢ :
  left-path-target-store₄ ⊢↑ left-path-target-Z-unseal₂
left-path-target-Z-unseal₄-⊢ =
  ⊢↑-unseal left-path-target-Z∋₄

left-path-source-Z-seal₄-⊢ :
  Ex.right-store₄ ⊢↓ example12-target-Z-seal
left-path-source-Z-seal₄-⊢ =
  ⊢↓-seal left-path-source-Z∋₄

left-path-source-Z-seal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↓[ just (Fin.suc (Fin.suc Fin.zero)) ]
    example12-target-Z-seal
left-path-source-Z-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ left-path-source-Z∋₄

left-path-target-Z-seal₄-⊢ :
  left-path-target-store₄ ⊢↓ left-path-target-Z-seal₂
left-path-target-Z-seal₄-⊢ =
  ⊢↓-seal left-path-target-Z∋₄

left-path-target-Z-seal₄-⊢ˣ :
  left-path-target-store₄ Conv.⊢↓[ just (Fin.suc Fin.zero) ]
    left-path-target-Z-seal₂
left-path-target-Z-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ left-path-target-Z∋₄

left-path-source-Y-seal₄-⊢ :
  Ex.right-store₄ ⊢↓ example12-target-Y-seal
left-path-source-Y-seal₄-⊢ =
  ⊢↓-seal left-path-source-Y∋₄

left-path-source-Y-seal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↓[ just (Fin.suc Fin.zero) ] example12-target-Y-seal
left-path-source-Y-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ left-path-source-Y∋₄

left-path-target-Y-seal₄-⊢ :
  left-path-target-store₄ ⊢↓ left-path-target-Y-seal₂
left-path-target-Y-seal₄-⊢ =
  ⊢↓-seal left-path-target-Y∋₄

left-path-target-Y-seal₄-⊢ˣ :
  left-path-target-store₄ Conv.⊢↓[ just Fin.zero ] left-path-target-Y-seal₂
left-path-target-Y-seal₄-⊢ˣ =
  Conv.⊢↓-sealˣ left-path-target-Y∋₄

left-path-source-Y-unseal₄-⊢ :
  Ex.right-store₄ ⊢↑ example12-target-Y-unseal
left-path-source-Y-unseal₄-⊢ =
  ⊢↑-unseal left-path-source-Y∋₄

left-path-source-Y-unseal₄-⊢ˣ :
  Ex.right-store₄ Conv.⊢↑[ just (Fin.suc Fin.zero) ] example12-target-Y-unseal
left-path-source-Y-unseal₄-⊢ˣ =
  Conv.⊢↑-unsealˣ left-path-source-Y∋₄

left-path-target-Y-unseal₄-⊢ :
  left-path-target-store₄ ⊢↑ left-path-target-Y-unseal₂
left-path-target-Y-unseal₄-⊢ =
  ⊢↑-unseal left-path-target-Y∋₄

left-path-target-Y-unseal₄-⊢ˣ :
  left-path-target-store₄ Conv.⊢↑[ just Fin.zero ] left-path-target-Y-unseal₂
left-path-target-Y-unseal₄-⊢ˣ =
  Conv.⊢↑-unsealˣ left-path-target-Y∋₄

left-path-Y-var⊑YZ₄ :
  ＇ (Fin.suc Fin.zero) ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ Fin.zero
left-path-Y-var⊑YZ₄ = Imprecision.X⊑X {X = Fin.suc Fin.zero}

left-path-Z-var⊑XZ₄ :
  ＇ (Fin.suc (Fin.suc Fin.zero)) ⊑ᵂ⟨ left-path-world₄ ⟩
    ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑XZ₄ =
  Imprecision.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}

left-path-Z-var⊑YZ₄ :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ left-path-world₄-YZ ⟩ ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑YZ₄ =
  Imprecision.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}

left-path-Z-var⊑★-YZ₄ :
  left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★ → ⊥
left-path-Z-var⊑★-YZ₄ ()

left-path-Z⇒Z⊑Z⇒Z-XZ₄ :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ left-path-world₄ ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-XZ₄ =
  ⇒⊑⇒ left-path-Z-var⊑XZ₄ left-path-Z-var⊑XZ₄

left-path-Z⇒Z⊑Z⇒Z-YZ₄ :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ left-path-world₄-YZ ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-YZ₄ =
  ⇒⊑⇒ left-path-Z-var⊑YZ₄ left-path-Z-var⊑YZ₄

left-path-lambda₄-YZ :
  left-path-world₄-YZ ∣ [] ⊢² ƛ (` 0) ⊑ left-path-target-lambda₃ ∶
    ⇒⊑⇒ left-path-Y-var⊑YZ₄ left-path-Y-var⊑YZ₄
left-path-lambda₄-YZ =
  ƛ⊑ƛ²
    {A = ＇ (Fin.suc Fin.zero)} {A′ = ＇ Fin.zero}
    {B = ＇ (Fin.suc Fin.zero)} {B′ = ＇ Fin.zero}
    {pA = left-path-Y-var⊑YZ₄} {pB = left-path-Y-var⊑YZ₄}
    (x⊑x² {p = left-path-Y-var⊑YZ₄} Zʷ)

left-path-Y-revealed₄-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    (ƛ (` 0)) ↑ example12-target-Y-reveal
    ⊑ left-path-target-lambda₃ ↑ left-path-Y-reveal₂ ∶
      left-path-Z⇒Z⊑Z⇒Z-YZ₄
left-path-Y-revealed₄-YZ =
  reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Y-YZ₄ CTX.same-[]
    left-path-source-Y-reveal₄-⊢ˣ left-path-target-Y-reveal₄-⊢ˣ
    left-path-lambda₄-YZ left-path-Z⇒Z⊑Z⇒Z-YZ₄

left-path-argument-Z₈-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal
    ⊑ ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂ ∶
      left-path-Z-var⊑YZ₄
left-path-argument-Z₈-YZ =
  CTI2.conceal⊑conceal²
    CTX.impEnvMono-refl left-path-rebase-Z-YZ₄
    CTX.same-[]
    left-path-source-Z-seal₄-⊢ˣ left-path-target-Z-seal₄-⊢ˣ
    left-path-source-X!₄ left-path-Z-var⊑YZ₄

left-path-application₈-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal)
    ⊑ (left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
            ↓ left-path-target-Z-seal₂) ∶
      left-path-Z-var⊑YZ₄
left-path-application₈-YZ =
  ·⊑·² left-path-Y-revealed₄-YZ left-path-argument-Z₈-YZ

left-path-target-Z-revealed₈-YZ :
  left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★ → ⊥
left-path-target-Z-revealed₈-YZ ()

left-path-both-Z-revealed₈-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal))
      ↑ example12-target-Z-unseal
    ⊑ ((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
            ↓ left-path-target-Z-seal₂))
        ↑ left-path-target-Z-unseal₂ ∶
      ★⊑★
left-path-both-Z-revealed₈-YZ =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Z-YZ₄
    CTX.same-[] left-path-source-Z-unseal₄-⊢ˣ
    left-path-target-Z-unseal₄-⊢ˣ left-path-application₈-YZ ★⊑★

left-path-source-result-id₈ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal))
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩
    ⊑ (((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
            ↓ left-path-target-Z-seal₂))
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₈ =
  cast⊑cast² left-path-source-result-id★₆ left-path-target-result-id★₃
    left-path-both-Z-revealed₈-YZ ★⊑★

left-path-source-result-?X₈ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ example12-target-X-seal)
          ⟨ example12-target-X! ⟩)
          ↓ example12-target-Z-seal))
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩)
      ⟨ example12-target-★?X ⟩
    ⊑ (((left-path-target-lambda₃ ↑ left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
            ↓ left-path-target-Z-seal₂))
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₈ =
  CTI2.cast⊑² example12-target-★?X left-path-source-result-id₈
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₈ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₈
    ⊑ left-path-target₅ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₈ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₈ left-path-ℕ⊑★₄-YZ

left-path-argument-Y₉-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↓ example12-target-Y-seal)
    ⊑ ((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↓ left-path-target-Y-seal₂) ∶
      left-path-Y-var⊑YZ₄
left-path-argument-Y₉-YZ =
  CTI2.conceal⊑conceal²
    CTX.impEnvMono-refl left-path-rebase-Y-YZ₄
    CTX.same-[] left-path-source-Y-seal₄-⊢ˣ
    left-path-target-Y-seal₄-⊢ˣ
    left-path-argument-Z₈-YZ left-path-Y-var⊑YZ₄

left-path-application₉-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    (ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ example12-target-X-seal)
        ⟨ example12-target-X! ⟩)
        ↓ example12-target-Z-seal)
        ↓ example12-target-Y-seal)
    ⊑ left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
          ↓ left-path-target-Z-seal₂)
          ↓ left-path-target-Y-seal₂) ∶
      left-path-Y-var⊑YZ₄
left-path-application₉-YZ =
  ·⊑·² left-path-lambda₄-YZ left-path-argument-Y₉-YZ

left-path-Y-unsealed₉-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ example12-target-X-seal)
        ⟨ example12-target-X! ⟩)
        ↓ example12-target-Z-seal)
        ↓ example12-target-Y-seal))
      ↑ example12-target-Y-unseal
    ⊑ (left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
          ↓ left-path-target-Z-seal₂)
          ↓ left-path-target-Y-seal₂))
        ↑ left-path-target-Y-unseal₂ ∶
      left-path-Z-var⊑YZ₄
left-path-Y-unsealed₉-YZ =
  reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Y-YZ₄ CTX.same-[]
    left-path-source-Y-unseal₄-⊢ˣ left-path-target-Y-unseal₄-⊢ˣ
    left-path-application₉-YZ left-path-Z-var⊑YZ₄

left-path-target-Z-unsealed₉-YZ :
  left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★ → ⊥
left-path-target-Z-unsealed₉-YZ ()

left-path-both-Z-unsealed₉-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ example12-target-X-seal)
        ⟨ example12-target-X! ⟩)
        ↓ example12-target-Z-seal)
        ↓ example12-target-Y-seal))
      ↑ example12-target-Y-unseal)
      ↑ example12-target-Z-unseal
    ⊑ ((left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
          ↓ left-path-target-Z-seal₂)
          ↓ left-path-target-Y-seal₂))
        ↑ left-path-target-Y-unseal₂)
        ↑ left-path-target-Z-unseal₂ ∶
      ★⊑★
left-path-both-Z-unsealed₉-YZ =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Z-YZ₄
    CTX.same-[] left-path-source-Z-unseal₄-⊢ˣ
    left-path-target-Z-unseal₄-⊢ˣ left-path-Y-unsealed₉-YZ ★⊑★

left-path-source-result-id₉ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ example12-target-X-seal)
        ⟨ example12-target-X! ⟩)
        ↓ example12-target-Z-seal)
        ↓ example12-target-Y-seal))
      ↑ example12-target-Y-unseal)
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩
    ⊑ (((left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
          ↓ left-path-target-Z-seal₂)
          ↓ left-path-target-Y-seal₂))
        ↑ left-path-target-Y-unseal₂)
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₉ =
  cast⊑cast² left-path-source-result-id★₆ left-path-target-result-id★₃
    left-path-both-Z-unsealed₉-YZ ★⊑★

left-path-source-result-?X₉ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ example12-target-X-seal)
        ⟨ example12-target-X! ⟩)
        ↓ example12-target-Z-seal)
        ↓ example12-target-Y-seal))
      ↑ example12-target-Y-unseal)
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩)
      ⟨ example12-target-★?X ⟩
    ⊑ (((left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
          ↓ left-path-target-Z-seal₂)
          ↓ left-path-target-Y-seal₂))
        ↑ left-path-target-Y-unseal₂)
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₉ =
  CTI2.cast⊑² example12-target-★?X left-path-source-result-id₉
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₉ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₉
    ⊑ left-path-target₆ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₉ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₉ left-path-ℕ⊑★₄-YZ

left-path-Y-unsealed₁₀-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↓ example12-target-Y-seal)
      ↑ example12-target-Y-unseal)
    ⊑ (((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↓ left-path-target-Y-seal₂)
        ↑ left-path-target-Y-unseal₂) ∶
      left-path-Z-var⊑YZ₄
left-path-Y-unsealed₁₀-YZ =
  reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Y-YZ₄ CTX.same-[]
    left-path-source-Y-unseal₄-⊢ˣ left-path-target-Y-unseal₄-⊢ˣ
    left-path-argument-Y₉-YZ left-path-Z-var⊑YZ₄

left-path-target-Z-unsealed₁₀-YZ :
  left-path-imp-env-YZ (Fin.suc (Fin.suc Fin.zero)) ≡ X⊑★ → ⊥
left-path-target-Z-unsealed₁₀-YZ ()

left-path-both-Z-unsealed₁₀-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↓ example12-target-Y-seal)
      ↑ example12-target-Y-unseal)
      ↑ example12-target-Z-unseal)
    ⊑ ((((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↓ left-path-target-Y-seal₂)
        ↑ left-path-target-Y-unseal₂)
        ↑ left-path-target-Z-unseal₂) ∶
      ★⊑★
left-path-both-Z-unsealed₁₀-YZ =
  CTI2.reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Z-YZ₄
    CTX.same-[] left-path-source-Z-unseal₄-⊢ˣ
    left-path-target-Z-unseal₄-⊢ˣ left-path-Y-unsealed₁₀-YZ ★⊑★

left-path-source-result-id₁₀ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↓ example12-target-Y-seal)
      ↑ example12-target-Y-unseal)
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩)
    ⊑ (((((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↓ left-path-target-Y-seal₂)
        ↑ left-path-target-Y-unseal₂)
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩) ∶
      ★⊑★
left-path-source-result-id₁₀ =
  cast⊑cast² left-path-source-result-id★₆ left-path-target-result-id★₃
    left-path-both-Z-unsealed₁₀-YZ ★⊑★

left-path-source-result-?X₁₀ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↓ example12-target-Y-seal)
      ↑ example12-target-Y-unseal)
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩)
      ⟨ example12-target-★?X ⟩
    ⊑ (((((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↓ left-path-target-Y-seal₂)
        ↑ left-path-target-Y-unseal₂)
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩) ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₁₀ =
  CTI2.cast⊑² example12-target-★?X left-path-source-result-id₁₀
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₁₀ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₁₀
    ⊑ left-path-target₇ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₁₀ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₁₀ left-path-ℕ⊑★₄-YZ

left-path-both-Z-unsealed₁₁-YZ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↑ example12-target-Z-unseal
    ⊑ ((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↑ left-path-target-Z-unseal₂) ∶
      ★⊑★
left-path-both-Z-unsealed₁₁-YZ =
  reveal⊑reveal² CTX.impEnvMono-refl left-path-rebase-Z-YZ₄ CTX.same-[]
    left-path-source-Z-unseal₄-⊢ˣ left-path-target-Z-unseal₄-⊢ˣ
    left-path-argument-Z₈-YZ ★⊑★

left-path-source-result-id₁₁ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩)
    ⊑ (((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩) ∶
      ★⊑★
left-path-source-result-id₁₁ =
  cast⊑cast² left-path-source-result-id★₆ left-path-target-result-id★₃
    left-path-both-Z-unsealed₁₁-YZ ★⊑★

left-path-source-result-?X₁₁ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ↓ example12-target-Z-seal)
      ↑ example12-target-Z-unseal)
      ⟨ left-path-source-result-id★₆ ⟩)
      ⟨ example12-target-★?X ⟩)
    ⊑ (((($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ↓ left-path-target-Z-seal₂)
        ↑ left-path-target-Z-unseal₂)
        ⟨ left-path-target-result-id★₃ ⟩) ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₁₁ =
  CTI2.cast⊑² example12-target-★?X left-path-source-result-id₁₁
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₁₁ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₁₁
    ⊑ left-path-target₈ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₁₁ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₁₁ left-path-ℕ⊑★₄-YZ

left-path-source-result-id₁₂ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ⟨ left-path-source-result-id★₆ ⟩)
    ⊑ ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₁₂ =
  cast⊑cast² left-path-source-result-id★₆ left-path-target-result-id★₃
    left-path-source-X!₄ ★⊑★

left-path-source-result-?X₁₂ :
  left-path-world₄-YZ ∣ [] ⊢²
    ((((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ⟨ left-path-source-result-id★₆ ⟩)
      ⟨ example12-target-★?X ⟩)
    ⊑ ($ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩)
        ⟨ left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₁₂ =
  CTI2.cast⊑² example12-target-★?X left-path-source-result-id₁₂
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₁₂ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₁₂
    ⊑ left-path-target₉ ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₁₂ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₁₂ left-path-ℕ⊑★₄-YZ

left-path-source-result-?X₁₃ :
  left-path-world₄-YZ ∣ [] ⊢²
    (((($ (κℕ 7)) ↓ example12-target-X-seal)
      ⟨ example12-target-X! ⟩)
      ⟨ example12-target-★?X ⟩)
    ⊑ $ (κℕ 7) ⟨ left-path-ℕ!₂ ⟩ ∶
      left-path-X-var⊑★-YZ₄
left-path-source-result-?X₁₃ =
  CTI2.cast⊑² example12-target-★?X left-path-source-X!₄
    left-path-X-var⊑★-YZ₄

left-path-checkpoint₁₃ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₁₃
    ⊑ left-path-target-final ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₁₃ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₁₃ left-path-ℕ⊑★₄-YZ

left-path-checkpoint₁₄ :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right₁₄
    ⊑ left-path-target-final ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint₁₄ =
  CTI2.reveal⊑² CTX.impEnvMono-refl left-path-rebase-X-YZ₄ᴸ
    CTX.same-[] left-path-source-X-unseal₄-⊢ˣ
    left-path-argument₄-sealed
    left-path-ℕ⊑★₄-YZ
left-path-checkpoint-final :
  left-path-world₄-YZ ∣ [] ⊢² Ex.right-final
    ⊑ left-path-target-final ∶ left-path-ℕ⊑★₄-YZ
left-path-checkpoint-final = left-path-argument₄-base
