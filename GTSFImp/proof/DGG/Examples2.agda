module proof.DGG.Examples2 where

-- File Charter:
--   * Collects the three running DGG version-2 imprecision examples.
--   * Reuses the executable reduction machinery from Examples.agda and records
--     reduction traces for each more precise / more imprecise pair.
--   * States the checkpoint obligations showing that the more imprecise side
--     simulates each reduction step of the more precise side under the
--     version-2 cast-term imprecision relation.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (zero; suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-empty; store-lift; store-bind)
import TermCtx as T
open import TermCtx using (TermCtx)
import Consistency as C
open C using (_↪ᵗ_; empty; keep; skip; id; _!; ？_; _↦_)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑_; _⊢↓_; id↑; `∀↑_; unseal; seal; _↦↑_;
   _↦↓_; ⊢↑-id; ⊢↑-∀; ⊢↑-unseal; ⊢↑-⇒; ⊢↓-seal; ⊢↓-⇒)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; ★⊑★; ι⊑ι; ⇒⊑⇒; ∀⊑∀; ∀⊑; ι⊑★)
open import Primitives using (κℕ)
open import CastTerms
open import Reduction
open import Eval using (step?; value?)
open import proof.ImprecisionConsistency using (refl⊑)
import proof.DGG.Examples as Ex
open Ex.OneStep
  using (Δ′; change; next; reduction)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; world; _⊑ᵂ⟨_⟩_; CtxImp; ctx-imp; _∣_⊢²_⊑_∶_;
   _∋ʷ_⦂_; Zʷ; Sʷ; LiftCtx; lift-[]; lift-∷; liftWorldBoth;
   x⊑x²; ƛ⊑ƛ²; ·⊑·²; Λ⊑Λ²; •⊑•²; κ⊑κ²; cast⊑cast²;
   ⊑cast²; reveal⊑reveal²; conceal⊑conceal²)

------------------------------------------------------------------------
-- Local reflexivity for the version-2 relation
------------------------------------------------------------------------

id↪ᵗ : ∀ {Δ} → Δ ↪ᵗ Δ
id↪ᵗ {zero} = empty
id↪ᵗ {suc Δ} = keep id↪ᵗ

reflWorld : ∀ {Δ} → TyStore Δ → World Δ Δ Δ
reflWorld Σ = world id↪ᵗ id↪ᵗ Imprecision.idᵐ Σ Σ

reflTy² : ∀ {Δ} {Σ : TyStore Δ} (A : Ty Δ)
  → A ⊑ᵂ⟨ reflWorld Σ ⟩ A
reflTy² {Σ = Σ} A = refl⊑ (CTI2.embedᴸ (reflWorld Σ) A)

ℕ⊑ℕ² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ)
ℕ⊑ℕ² = ι⊑ι

ℕ⊑★² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → (‵ `ℕ) ⊑ᵂ⟨ W ⟩ ★
ℕ⊑★² = ι⊑★

ℕ⇒ℕ⊑ℕ⇒ℕ² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → ((‵ `ℕ) ⇒ (‵ `ℕ)) ⊑ᵂ⟨ W ⟩ ((‵ `ℕ) ⇒ (‵ `ℕ))
ℕ⇒ℕ⊑ℕ⇒ℕ² {W = W} = ⇒⊑⇒ (ℕ⊑ℕ² {W = W}) (ℕ⊑ℕ² {W = W})

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
  (‵ `ℕ) ⊑ᵂ⟨ CTI2.example12-world-X ⟩ (‵ `ℕ)
example12-ℕ⊑ℕ-X = ℕ⊑ℕ² {W = CTI2.example12-world-X}

example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X :
  ((‵ `ℕ) ⇒ (‵ `ℕ)) ⊑ᵂ⟨ CTI2.example12-world-X ⟩
    ((‵ `ℕ) ⇒ (‵ `ℕ))
example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X =
  ℕ⇒ℕ⊑ℕ⇒ℕ² {W = CTI2.example12-world-X}

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
  CTI2.example12-world-X ∣ [] ⊢² Ex.left-final ⊑ Ex.right-final ∶
    example12-ℕ⊑ℕ-X
example12-checkpoint₄ = κ⊑κ² (κℕ 7) example12-ℕ⊑ℕ-X

postulate
  example12-checkpoint₁ :
    CTI2.example12-world-X ∣ [] ⊢² Ex.left₁ ⊑ Ex.right₃ ∶
      example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X

  example12-checkpoint₂ :
    CTI2.example12-world-X ∣ [] ⊢² Ex.left₂ ⊑ Ex.right₄ ∶
      example12-ℕ⊑ℕ-X

  example12-checkpoint₃ :
    CTI2.example12-world-X ∣ [] ⊢² Ex.left₃ ⊑ Ex.right₁₀ ∶
      example12-ℕ⊑ℕ-X

------------------------------------------------------------------------
-- Example 2: β-reveal-∀ followed by β-Λ, with a path to ℕ
------------------------------------------------------------------------

nat-chain-more-precise : Term 0
nat-chain-more-precise = CTI2.example12-nat-chain-source

nat-chain-more-imprecise : Term 0
nat-chain-more-imprecise = CTI2.example12-nat-chain-target

nat-chain-more-precise-reduction :
  nat-chain-more-precise —↠[ Ex.left-changes ] Ex.left-final
nat-chain-more-precise-reduction = Ex.example12-left-reduction

nat-target₀ : Term 0
nat-target₀ = nat-chain-more-imprecise

nat-target-store₀ : TyStore 0
nat-target-store₀ = store-empty

nat-target-step₀ : Ex.OneStep nat-target-store₀ nat-target₀
nat-target-step₀ = Ex.from-just-step (step? nat-target-store₀ nat-target₀) refl

nat-target₁ : Term (Δ′ nat-target-step₀)
nat-target₁ = next nat-target-step₀

nat-target-store₁ : TyStore (Δ′ nat-target-step₀)
nat-target-store₁ = Ex.store-after nat-target-step₀

nat-target-step₁ : Ex.OneStep nat-target-store₁ nat-target₁
nat-target-step₁ = Ex.from-just-step (step? nat-target-store₁ nat-target₁) refl

nat-target₂ : Term (Δ′ nat-target-step₁)
nat-target₂ = next nat-target-step₁

nat-target-store₂ : TyStore (Δ′ nat-target-step₁)
nat-target-store₂ = Ex.store-after nat-target-step₁

nat-target-step₂ : Ex.OneStep nat-target-store₂ nat-target₂
nat-target-step₂ = Ex.from-just-step (step? nat-target-store₂ nat-target₂) refl

nat-target₃ : Term (Δ′ nat-target-step₂)
nat-target₃ = next nat-target-step₂

nat-target-store₃ : TyStore (Δ′ nat-target-step₂)
nat-target-store₃ = Ex.store-after nat-target-step₂

nat-target-step₃ : Ex.OneStep nat-target-store₃ nat-target₃
nat-target-step₃ = Ex.from-just-step (step? nat-target-store₃ nat-target₃) refl

nat-target₄ : Term (Δ′ nat-target-step₃)
nat-target₄ = next nat-target-step₃

nat-target-store₄ : TyStore (Δ′ nat-target-step₃)
nat-target-store₄ = Ex.store-after nat-target-step₃

nat-target-step₄ : Ex.OneStep nat-target-store₄ nat-target₄
nat-target-step₄ = Ex.from-just-step (step? nat-target-store₄ nat-target₄) refl

nat-target-final : Term (Δ′ nat-target-step₄)
nat-target-final = next nat-target-step₄

nat-target-changes : StoreChanges 0 (Δ′ nat-target-step₄)
nat-target-changes =
  change nat-target-step₀ ∷ change nat-target-step₁ ∷
  change nat-target-step₂ ∷ change nat-target-step₃ ∷
  change nat-target-step₄ ∷ []

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
  nat-target-final ∎[]

nat-chain-ℕ⊑ℕ₀ :
  (‵ `ℕ) ⊑ᵂ⟨ reflWorld store-empty ⟩ (‵ `ℕ)
nat-chain-ℕ⊑ℕ₀ = ℕ⊑ℕ² {W = reflWorld store-empty}

nat-chain-ℕ⊑ℕ-X :
  (‵ `ℕ) ⊑ᵂ⟨ CTI2.example12-nat-chain-world-X ⟩ (‵ `ℕ)
nat-chain-ℕ⊑ℕ-X = ℕ⊑ℕ² {W = CTI2.example12-nat-chain-world-X}

nat-chain-ℕ⇒ℕ⊑ℕ⇒ℕ-X :
  ((‵ `ℕ) ⇒ (‵ `ℕ)) ⊑ᵂ⟨ CTI2.example12-nat-chain-world-X ⟩
    ((‵ `ℕ) ⇒ (‵ `ℕ))
nat-chain-ℕ⇒ℕ⊑ℕ⇒ℕ-X =
  ℕ⇒ℕ⊑ℕ⇒ℕ² {W = CTI2.example12-nat-chain-world-X}

postulate
  nat-chain-checkpoint₀ :
    reflWorld store-empty ∣ [] ⊢² nat-chain-more-precise
      ⊑ nat-chain-more-imprecise ∶ nat-chain-ℕ⊑ℕ₀

  nat-chain-checkpoint₁ :
    CTI2.example12-nat-chain-world-X ∣ [] ⊢² Ex.left₁
      ⊑ nat-target₂ ∶ nat-chain-ℕ⇒ℕ⊑ℕ⇒ℕ-X

  nat-chain-checkpoint₂ :
    CTI2.example12-nat-chain-world-X ∣ [] ⊢² Ex.left₂
      ⊑ nat-target₃ ∶ nat-chain-ℕ⊑ℕ-X

  nat-chain-checkpoint₃ :
    CTI2.example12-nat-chain-world-X ∣ [] ⊢² Ex.left₃
      ⊑ nat-target₄ ∶ nat-chain-ℕ⊑ℕ-X

  nat-chain-checkpoint₄ :
    CTI2.example12-nat-chain-world-X ∣ [] ⊢² Ex.left-final
      ⊑ nat-target-final ∶ nat-chain-ℕ⊑ℕ-X

------------------------------------------------------------------------
-- Example 3: representation path on the left
------------------------------------------------------------------------

left-path-more-precise : Term 0
left-path-more-precise = CTI2.example12-left-path-source

left-path-more-imprecise : Term 0
left-path-more-imprecise = CTI2.example12-left-path-target

left-path-more-precise-reduction :
  left-path-more-precise —↠[ Ex.right-changes ] Ex.right-final
left-path-more-precise-reduction = Ex.example12-right-reduction

left-path-target₀ : Term 0
left-path-target₀ = left-path-more-imprecise

left-path-target-store₀ : TyStore 0
left-path-target-store₀ = store-empty

left-path-target-step₀ : Ex.OneStep left-path-target-store₀ left-path-target₀
left-path-target-step₀ =
  Ex.from-just-step (step? left-path-target-store₀ left-path-target₀) refl

left-path-target₁ : Term (Δ′ left-path-target-step₀)
left-path-target₁ = next left-path-target-step₀

left-path-target-store₁ : TyStore (Δ′ left-path-target-step₀)
left-path-target-store₁ = Ex.store-after left-path-target-step₀

left-path-target-step₁ : Ex.OneStep left-path-target-store₁ left-path-target₁
left-path-target-step₁ =
  Ex.from-just-step (step? left-path-target-store₁ left-path-target₁) refl

left-path-target₂ : Term (Δ′ left-path-target-step₁)
left-path-target₂ = next left-path-target-step₁

left-path-target-store₂ : TyStore (Δ′ left-path-target-step₁)
left-path-target-store₂ = Ex.store-after left-path-target-step₁

left-path-target-step₂ : Ex.OneStep left-path-target-store₂ left-path-target₂
left-path-target-step₂ =
  Ex.from-just-step (step? left-path-target-store₂ left-path-target₂) refl

left-path-target₃ : Term (Δ′ left-path-target-step₂)
left-path-target₃ = next left-path-target-step₂

left-path-target-store₃ : TyStore (Δ′ left-path-target-step₂)
left-path-target-store₃ = Ex.store-after left-path-target-step₂

left-path-target-step₃ : Ex.OneStep left-path-target-store₃ left-path-target₃
left-path-target-step₃ =
  Ex.from-just-step (step? left-path-target-store₃ left-path-target₃) refl

left-path-target₄ : Term (Δ′ left-path-target-step₃)
left-path-target₄ = next left-path-target-step₃

left-path-target-store₄ : TyStore (Δ′ left-path-target-step₃)
left-path-target-store₄ = Ex.store-after left-path-target-step₃

left-path-target-step₄ : Ex.OneStep left-path-target-store₄ left-path-target₄
left-path-target-step₄ =
  Ex.from-just-step (step? left-path-target-store₄ left-path-target₄) refl

left-path-target-final : Term (Δ′ left-path-target-step₄)
left-path-target-final = next left-path-target-step₄

left-path-target-changes : StoreChanges 0 (Δ′ left-path-target-step₄)
left-path-target-changes =
  change left-path-target-step₀ ∷ change left-path-target-step₁ ∷
  change left-path-target-step₂ ∷ change left-path-target-step₃ ∷
  change left-path-target-step₄ ∷ []

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
  left-path-target-final ∎[]

postulate
  left-path-world₁ :
    World (Δ′ Ex.right-step₀) (Δ′ left-path-target-step₀)
      (Δ′ Ex.right-step₀)

  left-path-world₂ :
    World (Δ′ Ex.right-step₁) (Δ′ left-path-target-step₁)
      (Δ′ Ex.right-step₁)

  left-path-world₃ :
    World (Δ′ Ex.right-step₂) (Δ′ left-path-target-step₂)
      (Δ′ Ex.right-step₂)

  left-path-world₄ :
    World (Δ′ Ex.right-step₃) (Δ′ left-path-target-step₃)
      (Δ′ Ex.right-step₃)

  left-path-world₅ :
    World (Δ′ Ex.right-step₄) (Δ′ left-path-target-step₄)
      (Δ′ Ex.right-step₄)

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

postulate
  left-path-checkpoint₀ :
    reflWorld store-empty ∣ [] ⊢² left-path-more-precise
      ⊑ left-path-more-imprecise ∶ left-path-ℕ⊑★₀

  left-path-checkpoint₁ :
    left-path-world₁ ∣ [] ⊢² Ex.right₁
      ⊑ left-path-target₁ ∶ left-path-ℕ⊑★₁

  left-path-checkpoint₂ :
    left-path-world₂ ∣ [] ⊢² Ex.right₂
      ⊑ left-path-target₂ ∶ left-path-ℕ⊑★₂

  left-path-checkpoint₃ :
    left-path-world₃ ∣ [] ⊢² Ex.right₃
      ⊑ left-path-target₃ ∶ left-path-ℕ⊑★₃

  left-path-checkpoint₄ :
    left-path-world₄ ∣ [] ⊢² Ex.right₄
      ⊑ left-path-target₄ ∶ left-path-ℕ⊑★₄

  left-path-checkpoint-final :
    left-path-world₅ ∣ [] ⊢² Ex.right₅
      ⊑ left-path-target-final ∶ left-path-ℕ⊑★₅
