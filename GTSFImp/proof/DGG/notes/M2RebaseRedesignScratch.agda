module M2RebaseRedesignScratch where

-- Scratch validation for the M2 rebase redesign.  This file deliberately
-- lives at the repository root and imports the live DGG development without
-- changing it.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong)

open import Types
import Consistency as C
open import Consistency using (_↪ᵗ_; toRenameᵗ)
open import CastTerms
open import Primitives using (κℕ)
import Conversion
open import Imprecision
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.Example12Worlds as Ex12
import proof.DGG.CenterRename as CR
import proof.DGG.CenterCrossingProbe as CCP
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.DGG.WorldDecay as WD

open CTX using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Restricted rebase surface
------------------------------------------------------------------------

TargetFrozen : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
  → Set
TargetFrozen W W′ =
  ∀ Y → toRenameᵗ (CTX.ηᴿʷ W) Y ≡ toRenameᵗ (CTX.ηᴿʷ W′) Y

record RebaseAtᵣ {Δᴸ Δᴿ Δ} (W W′ : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ) (Xᴿ : TyVar Δᴿ) : Set where
  constructor rebase-atᵣ
  field
    base : CTX.RebaseAt W W′ Xᴸ Xᴿ
    target-frozen : TargetFrozen W W′

open RebaseAtᵣ

sameWorldRebaseAtᵣ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → toRenameᵗ (CTX.ηᴸʷ W) Xᴸ ≡ toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
  → CTX.StoreRepImp W Xᴸ Xᴿ
  → RebaseAtᵣ W W Xᴸ Xᴿ
sameWorldRebaseAtᵣ aligned reps =
  rebase-atᵣ (CTX.sameWorldRebaseAt aligned reps) (λ _ → refl)

data RebaseAtᴸᵣ {Δᴸ Δᴿ Δ} :
    World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴸ) → Set where
  rebase-idᴸᵣ : ∀ {W}
    → RebaseAtᴸᵣ W W nothing

  rebase-varᴸᵣ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAtᵣ W W′ Xᴸ Xᴿ
    → RebaseAtᴸᵣ W W′ (just Xᴸ)

  rebase-onlyᴸᵣ : ∀ {W} {Xᴸ : TyVar Δᴸ}
    → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    → (∀ (Xᴿ : TyVar Δᴿ)
        → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
          ≢ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)
    → CTX.resolveVar (CTX.sourceStoreʷ W) Xᴸ ⊑ᵂ⟨ W ⟩ ★
    → RebaseAtᴸᵣ W W (just Xᴸ)

data RebaseAtᴿᵣ {Δᴸ Δᴿ Δ} :
    World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ
    → Maybe (TyVar Δᴿ) → Set where
  rebase-idᴿᵣ : ∀ {W}
    → RebaseAtᴿᵣ W W nothing

  rebase-varᴿᵣ : ∀ {W W′ Xᴸ Xᴿ}
    → RebaseAtᵣ W W′ Xᴸ Xᴿ
    → RebaseAtᴿᵣ W W′ (just Xᴿ)

forgetᴸ : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ} {Xᴸ?}
  → RebaseAtᴸᵣ W W′ Xᴸ?
  → CTX.RebaseAtᴸ W W′ Xᴸ?
forgetᴸ rebase-idᴸᵣ = CTX.rebase-idᴸ
forgetᴸ (rebase-varᴸᵣ rb) = CTX.rebase-varᴸ (base rb)
forgetᴸ (rebase-onlyᴸᵣ to-star disaligned represented) =
  CTX.rebase-onlyᴸ to-star disaligned represented

forgetᴿ : ∀ {Δᴸ Δᴿ Δ} {W W′ : World Δᴸ Δᴿ Δ} {Xᴿ?}
  → RebaseAtᴿᵣ W W′ Xᴿ?
  → CTX.RebaseAtᴿ W W′ Xᴿ?
forgetᴿ rebase-idᴿᵣ = CTX.rebase-idᴿ
forgetᴿ (rebase-varᴿᵣ rb) = CTX.rebase-varᴿ (base rb)

⊑reveal²ᵣ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {γ′ : CTX.CtxImp W′}
    {M M′ A B B′ Xᴿ?}
    {p : A CTX.⊑ᵂ⟨ W′ ⟩ B} {c′ : Conversion.Conv↑ Δᴿ B B′}
  → CTX.ImpEnvMono W W′
  → RebaseAtᴿᵣ W W′ Xᴿ?
  → CTX.SameCtx γ γ′
  → CTX.targetStoreʷ W Conv.⊢↑[ Xᴿ? ] c′
  → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
  → (q : A CTX.⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q
⊑reveal²ᵣ mono rb sc c′⊢ D q =
  CTI2.⊑reveal² mono (forgetᴿ rb) sc c′⊢ D q

reveal⊑reveal²ᵣ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M M′ A A′ B B′ Xᴸ Xᴿ}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ A′}
    {c : Conversion.Conv↑ Δᴸ A B}
    {c′ : Conversion.Conv↑ Δᴿ A′ B′}
  → CTX.ImpEnvMono W Wᵖ
  → RebaseAtᵣ W Wᵖ Xᴸ Xᴿ
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↑[ just Xᴸ ] c
  → CTX.targetStoreʷ W Conv.⊢↑[ just Xᴿ ] c′
  → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : B CTX.⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢² M ↑ c ⊑ M′ ↑ c′ ∶ q
reveal⊑reveal²ᵣ mono rb sc c⊢ c′⊢ D q =
  CTI2.reveal⊑reveal² mono (base rb) sc c⊢ c′⊢ D q

⊑conceal²ᵣ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {γ′ : CTX.CtxImp W′}
    {M M′ A B B′ Xᴿ?}
    {p : A CTX.⊑ᵂ⟨ W′ ⟩ B} {c′ : Conversion.Conv↓ Δᴿ B B′}
  → CTX.ImpEnvMono W W′
  → RebaseAtᴿᵣ W′ W Xᴿ?
  → CTX.SameCtx γ γ′
  → CTX.targetStoreʷ W Conv.⊢↓[ Xᴿ? ] c′
  → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
  → (q : A CTX.⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢² M ⊑ M′ ↓ c′ ∶ q
⊑conceal²ᵣ mono rb sc c′⊢ D q =
  CTI2.⊑conceal² mono (forgetᴿ rb) sc c′⊢ D q

reveal⊑²ᵣ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {γ′ : CTX.CtxImp W′}
    {M M′ A A′ B Xᴸ?}
    {p : A CTX.⊑ᵂ⟨ W′ ⟩ B} {c : Conversion.Conv↑ Δᴸ A A′}
  → CTX.ImpEnvMono W W′
  → RebaseAtᴸᵣ W W′ Xᴸ?
  → CTX.SameCtx γ γ′
  → CTX.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c
  → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
  → (q : A′ CTX.⊑ᵂ⟨ W ⟩ B)
  → W ∣ γ ⊢² M ↑ c ⊑ M′ ∶ q
reveal⊑²ᵣ mono rb sc c⊢ D q =
  CTI2.reveal⊑² mono (forgetᴸ rb) sc c⊢ D q

conceal⊑²ᵣ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {γ′ : CTX.CtxImp W′}
    {M M′ A A′ B Xᴸ?}
    {p : A CTX.⊑ᵂ⟨ W′ ⟩ B} {c : Conversion.Conv↓ Δᴸ A A′}
  → CTX.ImpEnvMono W W′
  → RebaseAtᴸᵣ W′ W Xᴸ?
  → CTX.SameCtx γ γ′
  → CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
  → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
  → (q : A′ CTX.⊑ᵂ⟨ W ⟩ B)
  → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
conceal⊑²ᵣ mono rb sc c⊢ D q =
  CTI2.conceal⊑² mono (forgetᴸ rb) sc c⊢ D q

conceal⊑conceal²ᵣ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M M′ A A′ B B′ Xᴸ Xᴿ}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ A′}
    {c : Conversion.Conv↓ Δᴸ A B}
    {c′ : Conversion.Conv↓ Δᴿ A′ B′}
  → CTX.ImpEnvMono W Wᵖ
  → RebaseAtᵣ Wᵖ W Xᴸ Xᴿ
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ just Xᴸ ] c
  → CTX.targetStoreʷ W Conv.⊢↓[ just Xᴿ ] c′
  → Wᵖ ∣ γᵖ ⊢² M ⊑ M′ ∶ p
  → (q : B CTX.⊑ᵂ⟨ W ⟩ B′)
  → W ∣ γ ⊢² M ↓ c ⊑ M′ ↓ c′ ∶ q
conceal⊑conceal²ᵣ mono rb sc c⊢ c′⊢ D q =
  CTI2.conceal⊑conceal² mono (base rb) sc c⊢ c′⊢ D q

targetFrozen-decay : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ W′ W′ᵈ : World Δᴸ Δᴿ Δ}
  → WD.EnvDecay W Wᵈ
  → WD.EnvDecay W′ W′ᵈ
  → TargetFrozen W W′
  → TargetFrozen Wᵈ W′ᵈ
targetFrozen-decay
    (WD.env-decay refl refl refl refl mono)
    (WD.env-decay refl refl refl refl mono′) frozen = frozen

targetFrozen-rename : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W W′ : World Δᴸ Δᴿ Δ}
  → (π : Δ ↪ᵗ Δ′)
  → TargetFrozen W W′
  → TargetFrozen (CR.renameWorld π W) (CR.renameWorld π W′)
targetFrozen-rename π frozen Y = CR.rename-embedding-eq π (frozen Y)

targetFrozen-liftBoth : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {v}
  → TargetFrozen W W′
  → TargetFrozen (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v W′)
targetFrozen-liftBoth frozen Fin.zero = refl
targetFrozen-liftBoth frozen (Fin.suc Y) = cong Fin.suc (frozen Y)

------------------------------------------------------------------------
-- Example 12: source re-parking with frozen target centers
------------------------------------------------------------------------

example12-rebase-Z-to-Yᵣ :
  RebaseAtᵣ Ex12.example12-world-Z Ex12.example12-world-Y
    Fin.zero (Fin.suc Fin.zero)
example12-rebase-Z-to-Yᵣ =
  rebase-atᵣ Ex2.example12-rebase-Z-to-Y (λ _ → refl)

example12-rebase-X-to-Zᵣ :
  RebaseAtᵣ Ex12.example12-world-X Ex12.example12-world-Z
    Fin.zero (Fin.suc (Fin.suc Fin.zero))
example12-rebase-X-to-Zᵣ =
  rebase-atᵣ Ex12.example12-rebase-X-to-Z (λ _ → refl)

example12-rebase-X-sameᵣ :
  RebaseAtᵣ Ex12.example12-world-X Ex12.example12-world-X
    Fin.zero Fin.zero
example12-rebase-X-sameᵣ =
  rebase-atᵣ Ex2.example12-rebase-X-same (λ _ → refl)

example12-lambda-Zᵣ :
  Ex12.example12-world-Z ∣ [] ⊢² ƛ (` 0)
    ⊑ (ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal ∶
      Ex2.example12-Z-function-local
example12-lambda-Zᵣ =
  ⊑reveal²ᵣ (λ _ eq → eq)
    (rebase-varᴿᵣ example12-rebase-Z-to-Yᵣ) CTX.same-[]
    Ex2.example12-target-Y-reveal-⊢ˣ Ex2.example12-lambda-Y
    Ex2.example12-Z-function-local

example12-lambda-starᵣ :
  Ex12.example12-world-X ∣ [] ⊢² ƛ (` 0)
    ⊑ ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
        ↑ Ex2.example12-target-Z-reveal ∶
      Ex2.example12-X-function-to-star
example12-lambda-starᵣ =
  ⊑reveal²ᵣ (λ _ eq → eq)
    (rebase-varᴿᵣ example12-rebase-X-to-Zᵣ) CTX.same-[]
    Ex2.example12-target-Z-reveal-⊢ˣ example12-lambda-Zᵣ
    Ex2.example12-X-function-to-star

example12-lambda-star-idᵣ :
  Ex12.example12-world-X ∣ [] ⊢² ƛ (` 0)
    ⊑ (((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
        ↑ Ex2.example12-target-Z-reveal)
        ⟨ Ex2.example12-target-id★↦id★ ⟩ ∶
      Ex2.example12-X-function-to-star
example12-lambda-star-idᵣ =
  CTI2.⊑cast² Ex2.example12-target-id★↦id★
    example12-lambda-starᵣ Ex2.example12-X-function-to-star

example12-lambda-Xᵣ :
  Ex12.example12-world-X ∣ [] ⊢² ƛ (` 0)
    ⊑ ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
        ↑ Ex2.example12-target-Z-reveal)
        ⟨ Ex2.example12-target-id★↦id★ ⟩)
        ⟨ Ex2.example12-target-X?↦X? ⟩ ∶
      Ex2.example12-X-function-local
example12-lambda-Xᵣ =
  CTI2.⊑cast² Ex2.example12-target-X?↦X?
    example12-lambda-star-idᵣ Ex2.example12-X-function-local

example12-function-checkpoint₁ᵣ :
  Ex12.example12-world-X ∣ [] ⊢²
    (ƛ (` 0)) ↑ Ex2.example12-source-X-reveal
    ⊑ (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
        ↑ Ex2.example12-target-Z-reveal)
        ⟨ Ex2.example12-target-id★↦id★ ⟩)
        ⟨ Ex2.example12-target-X?↦X? ⟩)
        ↑ Ex2.example12-target-X-reveal ∶
      Ex2.example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X
example12-function-checkpoint₁ᵣ =
  reveal⊑reveal²ᵣ (λ _ eq → eq) example12-rebase-X-sameᵣ
    CTX.same-[] Ex2.example12-source-X-reveal-⊢ˣ
    Ex2.example12-target-X-reveal-⊢ˣ example12-lambda-Xᵣ
    Ex2.example12-ℕ⇒ℕ⊑ℕ⇒ℕ-X

------------------------------------------------------------------------
-- Left path: parked rebuild of the step-3 XZ-to-YZ checkpoint
------------------------------------------------------------------------

left-path-ℕ⊑★₃-YZᵣ :
  (‵ `ℕ) ⊑ᵂ⟨ Ex2.left-path-world₃-YZ ⟩ ★
left-path-ℕ⊑★₃-YZᵣ =
  Ex2.ℕ⊑★² {W = Ex2.left-path-world₃-YZ}

left-path-Z-var⊑YZ₃ᵣ :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ Ex2.left-path-world₃-YZ ⟩ ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑YZ₃ᵣ =
  Imprecision.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}

left-path-Z-var⊑★-YZ₃ᵣ :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ Ex2.left-path-world₃-YZ ⟩ ★
left-path-Z-var⊑★-YZ₃ᵣ =
  Imprecision.X⊑★ {X = Fin.suc (Fin.suc Fin.zero)} refl

left-path-X-var⊑★-YZ₃ᵣ :
  ＇ Fin.zero ⊑ᵂ⟨ Ex2.left-path-world₃-YZ ⟩ ★
left-path-X-var⊑★-YZ₃ᵣ =
  Imprecision.X⊑★ {X = Fin.zero} refl

left-path-Z⇒Z⊑Z⇒Z-YZ₃ᵣ :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ Ex2.left-path-world₃-YZ ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-YZ₃ᵣ =
  ⇒⊑⇒ left-path-Z-var⊑YZ₃ᵣ left-path-Z-var⊑YZ₃ᵣ

left-path-Z⇒Z⊑★⇒★-YZ₃ᵣ :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ Ex2.left-path-world₃-YZ ⟩ (★ ⇒ ★)
left-path-Z⇒Z⊑★⇒★-YZ₃ᵣ =
  ⇒⊑⇒ left-path-Z-var⊑★-YZ₃ᵣ left-path-Z-var⊑★-YZ₃ᵣ

left-path-X⇒X⊑★⇒★-YZ₃ᵣ :
  (＇ Fin.zero ⇒ ＇ Fin.zero)
    ⊑ᵂ⟨ Ex2.left-path-world₃-YZ ⟩ (★ ⇒ ★)
left-path-X⇒X⊑★⇒★-YZ₃ᵣ =
  ⇒⊑⇒ left-path-X-var⊑★-YZ₃ᵣ left-path-X-var⊑★-YZ₃ᵣ

left-path-source-Z-rep₃-YZᵣ :
  CTX.StoreRepImp Ex2.left-path-world₃-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-source-Z-rep₃-YZᵣ = CTX.store-rep-imp ★⊑★

left-path-rebase-Y-YZ₃ᵣ :
  RebaseAtᵣ Ex2.left-path-world₃-YZ Ex2.left-path-world₃-YZ
    (Fin.suc Fin.zero) Fin.zero
left-path-rebase-Y-YZ₃ᵣ =
  sameWorldRebaseAtᵣ refl Ex2.left-path-source-Y-rep₃-YZ

left-path-rebase-Z-YZ₃ᵣ :
  RebaseAtᵣ Ex2.left-path-world₃-YZ Ex2.left-path-world₃-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-Z-YZ₃ᵣ =
  sameWorldRebaseAtᵣ refl left-path-source-Z-rep₃-YZᵣ

left-path-rebase-X-YZ₃ᴸᵣ :
  RebaseAtᴸᵣ Ex2.left-path-world₃-YZ Ex2.left-path-world₃-YZ
    (just Fin.zero)
left-path-rebase-X-YZ₃ᴸᵣ =
  rebase-onlyᴸᵣ refl
    (λ { Fin.zero (); (Fin.suc Fin.zero) () })
    (Ex2.ℕ⊑★² {W = Ex2.left-path-world₃-YZ})

left-path-Y-revealed₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    (ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal
    ⊑ Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂ ∶
      left-path-Z⇒Z⊑Z⇒Z-YZ₃ᵣ
left-path-Y-revealed₃-YZᵣ =
  reveal⊑reveal²ᵣ (λ _ eq → eq) left-path-rebase-Y-YZ₃ᵣ
    CTX.same-[] Ex2.left-path-source-Y-reveal₃-⊢ˣ
    Ex2.left-path-target-Y-reveal₃-⊢ˣ Ex2.left-path-lambda₃-YZ
    left-path-Z⇒Z⊑Z⇒Z-YZ₃ᵣ

left-path-target-Z-revealed₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    (ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      left-path-Z⇒Z⊑★⇒★-YZ₃ᵣ
left-path-target-Z-revealed₃-YZᵣ =
  ⊑reveal²ᵣ (λ _ eq → eq)
    (rebase-varᴿᵣ left-path-rebase-Z-YZ₃ᵣ) CTX.same-[]
    Ex2.left-path-target-Z-reveal₃-⊢ˣ left-path-Y-revealed₃-YZᵣ
    left-path-Z⇒Z⊑★⇒★-YZ₃ᵣ

left-path-both-Z-revealed₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.★⇒★⊑★⇒★² {W = Ex2.left-path-world₃-YZ}
left-path-both-Z-revealed₃-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq)
    (rebase-varᴸᵣ left-path-rebase-Z-YZ₃ᵣ) CTX.same-[]
    Ex2.left-path-source-Z-reveal₃-⊢ˣ
    left-path-target-Z-revealed₃-YZᵣ
    (Ex2.★⇒★⊑★⇒★² {W = Ex2.left-path-world₃-YZ})

left-path-source-id₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.★⇒★⊑★⇒★² {W = Ex2.left-path-world₃-YZ}
left-path-source-id₃-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-id★↦id★
    left-path-both-Z-revealed₃-YZᵣ
    (Ex2.★⇒★⊑★⇒★² {W = Ex2.left-path-world₃-YZ})

left-path-source-X?₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      ⟨ Ex2.example12-target-X?↦X? ⟩
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      left-path-X⇒X⊑★⇒★-YZ₃ᵣ
left-path-source-X?₃-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-X?↦X? left-path-source-id₃-YZᵣ
    left-path-X⇒X⊑★⇒★-YZ₃ᵣ

left-path-function₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      ⟨ Ex2.example12-target-X?↦X? ⟩)
      ↑ Ex2.example12-target-X-reveal
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.ℕ⇒ℕ⊑★⇒★² {W = Ex2.left-path-world₃-YZ}
left-path-function₃-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₃ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-reveal₃-⊢ˣ
    left-path-source-X?₃-YZᵣ
    (Ex2.ℕ⇒ℕ⊑★⇒★² {W = Ex2.left-path-world₃-YZ})

left-path-argument₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢² $ (κℕ 7)
    ⊑ ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ C.sym∼ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-ℕ⊑★₃-YZᵣ
left-path-argument₃-YZᵣ =
  CTI2.⊑cast² (C.sym∼ Ex2.left-path-target-result-id★₃)
    (CTI2.⊑cast² Ex2.left-path-ℕ!₂
      (CTI2.κ⊑κ² (κℕ 7)
        (Ex2.ℕ⊑ℕ² {W = Ex2.left-path-world₃-YZ}))
      left-path-ℕ⊑★₃-YZᵣ)
    left-path-ℕ⊑★₃-YZᵣ

left-path-checkpoint₃-YZᵣ :
  Ex2.left-path-world₃-YZ ∣ [] ⊢² Ex.right₃
    ⊑ Ex2.left-path-target₃ ∶ left-path-ℕ⊑★₃-YZᵣ
left-path-checkpoint₃-YZᵣ =
  CTI2.⊑cast² Ex2.left-path-target-result-id★₃
    (CTI2.·⊑·² left-path-function₃-YZᵣ left-path-argument₃-YZᵣ)
    left-path-ℕ⊑★₃-YZᵣ

------------------------------------------------------------------------
-- Left path: parked rebuilds of checkpoints 4--7
------------------------------------------------------------------------

left-path-ℕ⊑★₄-YZᵣ :
  (‵ `ℕ) ⊑ᵂ⟨ Ex2.left-path-world₄-YZ ⟩ ★
left-path-ℕ⊑★₄-YZᵣ =
  Ex2.ℕ⊑★² {W = Ex2.left-path-world₄-YZ}

left-path-X-var⊑★-YZ₄ᵣ :
  ＇ Fin.zero ⊑ᵂ⟨ Ex2.left-path-world₄-YZ ⟩ ★
left-path-X-var⊑★-YZ₄ᵣ =
  Imprecision.X⊑★ {X = Fin.zero} refl

left-path-Z-var⊑YZ₄ᵣ :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ Ex2.left-path-world₄-YZ ⟩ ＇ (Fin.suc Fin.zero)
left-path-Z-var⊑YZ₄ᵣ =
  Imprecision.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}

left-path-Z-var⊑★-YZ₄ᵣ :
  ＇ (Fin.suc (Fin.suc Fin.zero))
    ⊑ᵂ⟨ Ex2.left-path-world₄-YZ ⟩ ★
left-path-Z-var⊑★-YZ₄ᵣ =
  Imprecision.X⊑★ {X = Fin.suc (Fin.suc Fin.zero)} refl

left-path-Z⇒Z⊑Z⇒Z-YZ₄ᵣ :
  (＇ (Fin.suc (Fin.suc Fin.zero))
    ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
    ⊑ᵂ⟨ Ex2.left-path-world₄-YZ ⟩
      (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
left-path-Z⇒Z⊑Z⇒Z-YZ₄ᵣ =
  ⇒⊑⇒ left-path-Z-var⊑YZ₄ᵣ left-path-Z-var⊑YZ₄ᵣ

left-path-source-Z-rep₄-YZᵣ :
  CTX.StoreRepImp Ex2.left-path-world₄-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-source-Z-rep₄-YZᵣ = CTX.store-rep-imp ★⊑★

left-path-rebase-Y-YZ₄ᵣ :
  RebaseAtᵣ Ex2.left-path-world₄-YZ Ex2.left-path-world₄-YZ
    (Fin.suc Fin.zero) Fin.zero
left-path-rebase-Y-YZ₄ᵣ =
  sameWorldRebaseAtᵣ refl Ex2.left-path-source-Y-rep₄-YZ

left-path-rebase-Z-YZ₄ᵣ :
  RebaseAtᵣ Ex2.left-path-world₄-YZ Ex2.left-path-world₄-YZ
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc Fin.zero)
left-path-rebase-Z-YZ₄ᵣ =
  sameWorldRebaseAtᵣ refl left-path-source-Z-rep₄-YZᵣ

left-path-rebase-X-YZ₄ᴸᵣ :
  RebaseAtᴸᵣ Ex2.left-path-world₄-YZ Ex2.left-path-world₄-YZ
    (just Fin.zero)
left-path-rebase-X-YZ₄ᴸᵣ =
  rebase-onlyᴸᵣ refl
    (λ { Fin.zero (); (Fin.suc Fin.zero) () })
    (Ex2.ℕ⊑★² {W = Ex2.left-path-world₄-YZ})

left-path-source-X?₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      ⟨ Ex2.example12-target-X?↦X? ⟩
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      ⇒⊑⇒ left-path-X-var⊑★-YZ₄ᵣ left-path-X-var⊑★-YZ₄ᵣ
left-path-source-X?₄-YZᵣ = left-path-source-X?₃-YZᵣ

left-path-argument₄-base-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      left-path-ℕ⊑★₄-YZᵣ
left-path-argument₄-base-YZᵣ =
  CTI2.⊑cast² Ex2.left-path-ℕ!₂
    (CTI2.κ⊑κ² (κℕ 7)
      (Ex2.ℕ⊑ℕ² {W = Ex2.left-path-world₄-YZ}))
    left-path-ℕ⊑★₄-YZᵣ

left-path-argument₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ($ (κℕ 7)) ↓ Ex2.example12-target-X-seal
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-argument₄-YZᵣ =
  conceal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-seal₄-⊢ˣ
    left-path-argument₄-base-YZᵣ left-path-X-var⊑★-YZ₄ᵣ

left-path-application₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      ⟨ Ex2.example12-target-X?↦X? ⟩)
      · (($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-application₄-YZᵣ =
  CTI2.⊑cast² Ex2.left-path-target-result-id★₃
    (CTI2.·⊑·² left-path-source-X?₄-YZᵣ
      left-path-argument₄-YZᵣ)
    left-path-X-var⊑★-YZ₄ᵣ

left-path-checkpoint₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₄
    ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-YZᵣ
left-path-checkpoint₄-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-unseal₄-⊢ˣ
    left-path-application₄-YZᵣ left-path-ℕ⊑★₄-YZᵣ

left-path-source-id₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.★⇒★⊑★⇒★² {W = Ex2.left-path-world₄-YZ}
left-path-source-id₄-YZᵣ = left-path-source-id₃-YZᵣ

left-path-source-X!₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      ★⊑★
left-path-source-X!₄-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-X! left-path-argument₄-YZᵣ ★⊑★

left-path-application₅-base-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      · ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩) ∶
      ★⊑★
left-path-application₅-base-YZᵣ =
  CTI2.·⊑·² left-path-source-id₄-YZᵣ left-path-source-X!₄-YZᵣ

left-path-application₅-target-id-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      · ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-application₅-target-id-YZᵣ =
  CTI2.⊑cast² Ex2.left-path-target-result-id★₃
    left-path-application₅-base-YZᵣ ★⊑★

left-path-source-result-?X₅-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      ⟨ Ex2.example12-target-id★↦id★ ⟩)
      · ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩))
      ⟨ Ex2.example12-target-★?X ⟩
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-source-result-?X₅-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-★?X
    left-path-application₅-target-id-YZᵣ left-path-X-var⊑★-YZ₄ᵣ

left-path-checkpoint₅-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₅
    ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-YZᵣ
left-path-checkpoint₅-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₅-YZᵣ left-path-ℕ⊑★₄-YZᵣ

left-path-source-bare-Z₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂ ∶
      Ex2.★⇒★⊑★⇒★² {W = Ex2.left-path-world₄-YZ}
left-path-source-bare-Z₄-YZᵣ = left-path-both-Z-revealed₃-YZᵣ

left-path-source-X!-id₆-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ⟨ Ex2.left-path-source-arg-id★₆ ⟩
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      ★⊑★
left-path-source-X!-id₆-YZᵣ =
  CTI2.cast⊑² Ex2.left-path-source-arg-id★₆
    left-path-source-X!₄-YZᵣ ★⊑★

left-path-application₆-base-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ⟨ Ex2.left-path-source-arg-id★₆ ⟩)
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩) ∶
      ★⊑★
left-path-application₆-base-YZᵣ =
  CTI2.·⊑·² left-path-source-bare-Z₄-YZᵣ
    left-path-source-X!-id₆-YZᵣ

left-path-source-result-id₆-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ⟨ Ex2.left-path-source-arg-id★₆ ⟩))
      ⟨ Ex2.left-path-source-result-id★₆ ⟩
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₆-YZᵣ =
  CTI2.cast⊑cast² Ex2.left-path-source-result-id★₆
    Ex2.left-path-target-result-id★₃ left-path-application₆-base-YZᵣ
    ★⊑★

left-path-source-result-?X₆-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ⟨ Ex2.left-path-source-arg-id★₆ ⟩))
      ⟨ Ex2.left-path-source-result-id★₆ ⟩)
      ⟨ Ex2.example12-target-★?X ⟩
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-source-result-?X₆-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-★?X
    left-path-source-result-id₆-YZᵣ left-path-X-var⊑★-YZ₄ᵣ

left-path-checkpoint₆-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₆
    ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-YZᵣ
left-path-checkpoint₆-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₆-YZᵣ left-path-ℕ⊑★₄-YZᵣ

left-path-application₇-base-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      · ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩) ∶
      ★⊑★
left-path-application₇-base-YZᵣ =
  CTI2.·⊑·² left-path-source-bare-Z₄-YZᵣ
    left-path-source-X!₄-YZᵣ

left-path-source-result-id₇-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      · ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩))
      ⟨ Ex2.left-path-source-result-id★₆ ⟩
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₇-YZᵣ =
  CTI2.cast⊑cast² Ex2.left-path-source-result-id★₆
    Ex2.left-path-target-result-id★₃ left-path-application₇-base-YZᵣ
    ★⊑★

left-path-source-result-?X₇-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      ↑ Ex2.example12-target-Z-reveal)
      · ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩))
      ⟨ Ex2.left-path-source-result-id★₆ ⟩)
      ⟨ Ex2.example12-target-★?X ⟩
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        ↑ Ex2.left-path-Z-reveal₂)
        · ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-source-result-?X₇-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-★?X
    left-path-source-result-id₇-YZᵣ left-path-X-var⊑★-YZ₄ᵣ

left-path-checkpoint₇-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₇
    ⊑ Ex2.left-path-target₄ ∶ left-path-ℕ⊑★₄-YZᵣ
left-path-checkpoint₇-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₇-YZᵣ left-path-ℕ⊑★₄-YZᵣ

------------------------------------------------------------------------
-- Left path: parked rebuilds of checkpoints 8--10
------------------------------------------------------------------------

left-path-Y-revealed₄-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal
    ⊑ Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂ ∶
      left-path-Z⇒Z⊑Z⇒Z-YZ₄ᵣ
left-path-Y-revealed₄-YZᵣ =
  reveal⊑reveal²ᵣ (λ _ eq → eq) left-path-rebase-Y-YZ₄ᵣ
    CTX.same-[] Ex2.left-path-source-Y-reveal₄-⊢ˣ
    Ex2.left-path-target-Y-reveal₄-⊢ˣ Ex2.left-path-lambda₄-YZ
    left-path-Z⇒Z⊑Z⇒Z-YZ₄ᵣ

left-path-argument-Z₈-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ↓ Ex2.example12-target-Z-seal
    ⊑ ($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ Ex2.left-path-target-Z-seal₂ ∶
      left-path-Z-var⊑YZ₄ᵣ
left-path-argument-Z₈-YZᵣ =
  conceal⊑conceal²ᵣ (λ _ eq → eq) left-path-rebase-Z-YZ₄ᵣ
    CTX.same-[] Ex2.left-path-source-Z-seal₄-⊢ˣ
    Ex2.left-path-target-Z-seal₄-⊢ˣ left-path-source-X!₄-YZᵣ
    left-path-Z-var⊑YZ₄ᵣ

left-path-application₈-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ↓ Ex2.example12-target-Z-seal)
    ⊑ (Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
            ↓ Ex2.left-path-target-Z-seal₂) ∶
      left-path-Z-var⊑YZ₄ᵣ
left-path-application₈-YZᵣ =
  CTI2.·⊑·² left-path-Y-revealed₄-YZᵣ
    left-path-argument-Z₈-YZᵣ

left-path-target-Z-revealed₈-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ↓ Ex2.example12-target-Z-seal)
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
            ↓ Ex2.left-path-target-Z-seal₂))
        ↑ Ex2.left-path-target-Z-unseal₂ ∶
      left-path-Z-var⊑★-YZ₄ᵣ
left-path-target-Z-revealed₈-YZᵣ =
  ⊑reveal²ᵣ (λ _ eq → eq)
    (rebase-varᴿᵣ left-path-rebase-Z-YZ₄ᵣ) CTX.same-[]
    Ex2.left-path-target-Z-unseal₄-⊢ˣ left-path-application₈-YZᵣ
    left-path-Z-var⊑★-YZ₄ᵣ

left-path-both-Z-revealed₈-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ↓ Ex2.example12-target-Z-seal))
      ↑ Ex2.example12-target-Z-unseal
    ⊑ ((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
            ↓ Ex2.left-path-target-Z-seal₂))
        ↑ Ex2.left-path-target-Z-unseal₂ ∶
      ★⊑★
left-path-both-Z-revealed₈-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq)
    (rebase-varᴸᵣ left-path-rebase-Z-YZ₄ᵣ) CTX.same-[]
    Ex2.left-path-source-Z-unseal₄-⊢ˣ
    left-path-target-Z-revealed₈-YZᵣ ★⊑★

left-path-source-result-id₈-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ↓ Ex2.example12-target-Z-seal))
      ↑ Ex2.example12-target-Z-unseal)
      ⟨ Ex2.left-path-source-result-id★₆ ⟩
    ⊑ (((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
            ↓ Ex2.left-path-target-Z-seal₂))
        ↑ Ex2.left-path-target-Z-unseal₂)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₈-YZᵣ =
  CTI2.cast⊑cast² Ex2.left-path-source-result-id★₆
    Ex2.left-path-target-result-id★₃ left-path-both-Z-revealed₈-YZᵣ
    ★⊑★

left-path-source-result-?X₈-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ↑ Ex2.example12-target-Y-reveal)
      · (((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
          ⟨ Ex2.example12-target-X! ⟩)
          ↓ Ex2.example12-target-Z-seal))
      ↑ Ex2.example12-target-Z-unseal)
      ⟨ Ex2.left-path-source-result-id★₆ ⟩)
      ⟨ Ex2.example12-target-★?X ⟩
    ⊑ (((Ex2.left-path-target-lambda₃ ↑ Ex2.left-path-Y-reveal₂)
        · (($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
            ↓ Ex2.left-path-target-Z-seal₂))
        ↑ Ex2.left-path-target-Z-unseal₂)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-source-result-?X₈-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-★?X
    left-path-source-result-id₈-YZᵣ left-path-X-var⊑★-YZ₄ᵣ

left-path-checkpoint₈-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₈
    ⊑ Ex2.left-path-target₅ ∶ left-path-ℕ⊑★₄-YZᵣ
left-path-checkpoint₈-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₈-YZᵣ left-path-ℕ⊑★₄-YZᵣ

left-path-argument-Y₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ↓ Ex2.example12-target-Z-seal)
      ↓ Ex2.example12-target-Y-seal)
    ⊑ ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ Ex2.left-path-target-Z-seal₂)
        ↓ Ex2.left-path-target-Y-seal₂) ∶
      Ex2.left-path-Y-var⊑YZ₄
left-path-argument-Y₉-YZᵣ =
  conceal⊑conceal²ᵣ (λ _ eq → eq) left-path-rebase-Y-YZ₄ᵣ
    CTX.same-[] Ex2.left-path-source-Y-seal₄-⊢ˣ
    Ex2.left-path-target-Y-seal₄-⊢ˣ left-path-argument-Z₈-YZᵣ
    Ex2.left-path-Y-var⊑YZ₄

left-path-application₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal)
        ↓ Ex2.example12-target-Y-seal)
    ⊑ Ex2.left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ Ex2.left-path-target-Z-seal₂)
          ↓ Ex2.left-path-target-Y-seal₂) ∶
      Ex2.left-path-Y-var⊑YZ₄
left-path-application₉-YZᵣ =
  CTI2.·⊑·² Ex2.left-path-lambda₄-YZ
    left-path-argument-Y₉-YZᵣ

left-path-Y-unsealed₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal)
        ↓ Ex2.example12-target-Y-seal))
      ↑ Ex2.example12-target-Y-unseal
    ⊑ (Ex2.left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ Ex2.left-path-target-Z-seal₂)
          ↓ Ex2.left-path-target-Y-seal₂))
        ↑ Ex2.left-path-target-Y-unseal₂ ∶
      left-path-Z-var⊑YZ₄ᵣ
left-path-Y-unsealed₉-YZᵣ =
  reveal⊑reveal²ᵣ (λ _ eq → eq) left-path-rebase-Y-YZ₄ᵣ
    CTX.same-[] Ex2.left-path-source-Y-unseal₄-⊢ˣ
    Ex2.left-path-target-Y-unseal₄-⊢ˣ left-path-application₉-YZᵣ
    left-path-Z-var⊑YZ₄ᵣ

left-path-target-Z-unsealed₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal)
        ↓ Ex2.example12-target-Y-seal))
      ↑ Ex2.example12-target-Y-unseal
    ⊑ ((Ex2.left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ Ex2.left-path-target-Z-seal₂)
          ↓ Ex2.left-path-target-Y-seal₂))
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂ ∶
      left-path-Z-var⊑★-YZ₄ᵣ
left-path-target-Z-unsealed₉-YZᵣ =
  ⊑reveal²ᵣ (λ _ eq → eq)
    (rebase-varᴿᵣ left-path-rebase-Z-YZ₄ᵣ) CTX.same-[]
    Ex2.left-path-target-Z-unseal₄-⊢ˣ left-path-Y-unsealed₉-YZᵣ
    left-path-Z-var⊑★-YZ₄ᵣ

left-path-both-Z-unsealed₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal)
        ↓ Ex2.example12-target-Y-seal))
      ↑ Ex2.example12-target-Y-unseal)
      ↑ Ex2.example12-target-Z-unseal
    ⊑ ((Ex2.left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ Ex2.left-path-target-Z-seal₂)
          ↓ Ex2.left-path-target-Y-seal₂))
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂ ∶
      ★⊑★
left-path-both-Z-unsealed₉-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq)
    (rebase-varᴸᵣ left-path-rebase-Z-YZ₄ᵣ) CTX.same-[]
    Ex2.left-path-source-Z-unseal₄-⊢ˣ
    left-path-target-Z-unsealed₉-YZᵣ ★⊑★

left-path-source-result-id₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal)
        ↓ Ex2.example12-target-Y-seal))
      ↑ Ex2.example12-target-Y-unseal)
      ↑ Ex2.example12-target-Z-unseal)
      ⟨ Ex2.left-path-source-result-id★₆ ⟩
    ⊑ (((Ex2.left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ Ex2.left-path-target-Z-seal₂)
          ↓ Ex2.left-path-target-Y-seal₂))
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      ★⊑★
left-path-source-result-id₉-YZᵣ =
  CTI2.cast⊑cast² Ex2.left-path-source-result-id★₆
    Ex2.left-path-target-result-id★₃ left-path-both-Z-unsealed₉-YZᵣ
    ★⊑★

left-path-source-result-?X₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((ƛ (` 0)) ·
      ((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
        ⟨ Ex2.example12-target-X! ⟩)
        ↓ Ex2.example12-target-Z-seal)
        ↓ Ex2.example12-target-Y-seal))
      ↑ Ex2.example12-target-Y-unseal)
      ↑ Ex2.example12-target-Z-unseal)
      ⟨ Ex2.left-path-source-result-id★₆ ⟩)
      ⟨ Ex2.example12-target-★?X ⟩
    ⊑ (((Ex2.left-path-target-lambda₃ ·
        ((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
          ↓ Ex2.left-path-target-Z-seal₂)
          ↓ Ex2.left-path-target-Y-seal₂))
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩ ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-source-result-?X₉-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-★?X
    left-path-source-result-id₉-YZᵣ left-path-X-var⊑★-YZ₄ᵣ

left-path-checkpoint₉-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₉
    ⊑ Ex2.left-path-target₆ ∶ left-path-ℕ⊑★₄-YZᵣ
left-path-checkpoint₉-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₉-YZᵣ left-path-ℕ⊑★₄-YZᵣ

left-path-Y-unsealed₁₀-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ↓ Ex2.example12-target-Z-seal)
      ↓ Ex2.example12-target-Y-seal)
      ↑ Ex2.example12-target-Y-unseal)
    ⊑ (((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ Ex2.left-path-target-Z-seal₂)
        ↓ Ex2.left-path-target-Y-seal₂)
        ↑ Ex2.left-path-target-Y-unseal₂) ∶
      left-path-Z-var⊑YZ₄ᵣ
left-path-Y-unsealed₁₀-YZᵣ =
  reveal⊑reveal²ᵣ (λ _ eq → eq) left-path-rebase-Y-YZ₄ᵣ
    CTX.same-[] Ex2.left-path-source-Y-unseal₄-⊢ˣ
    Ex2.left-path-target-Y-unseal₄-⊢ˣ left-path-argument-Y₉-YZᵣ
    left-path-Z-var⊑YZ₄ᵣ

left-path-target-Z-unsealed₁₀-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ↓ Ex2.example12-target-Z-seal)
      ↓ Ex2.example12-target-Y-seal)
      ↑ Ex2.example12-target-Y-unseal)
    ⊑ ((((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ Ex2.left-path-target-Z-seal₂)
        ↓ Ex2.left-path-target-Y-seal₂)
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂) ∶
      left-path-Z-var⊑★-YZ₄ᵣ
left-path-target-Z-unsealed₁₀-YZᵣ =
  ⊑reveal²ᵣ (λ _ eq → eq)
    (rebase-varᴿᵣ left-path-rebase-Z-YZ₄ᵣ) CTX.same-[]
    Ex2.left-path-target-Z-unseal₄-⊢ˣ left-path-Y-unsealed₁₀-YZᵣ
    left-path-Z-var⊑★-YZ₄ᵣ

left-path-both-Z-unsealed₁₀-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    ((((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ↓ Ex2.example12-target-Z-seal)
      ↓ Ex2.example12-target-Y-seal)
      ↑ Ex2.example12-target-Y-unseal)
      ↑ Ex2.example12-target-Z-unseal)
    ⊑ ((((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ Ex2.left-path-target-Z-seal₂)
        ↓ Ex2.left-path-target-Y-seal₂)
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂) ∶
      ★⊑★
left-path-both-Z-unsealed₁₀-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq)
    (rebase-varᴸᵣ left-path-rebase-Z-YZ₄ᵣ) CTX.same-[]
    Ex2.left-path-source-Z-unseal₄-⊢ˣ
    left-path-target-Z-unsealed₁₀-YZᵣ ★⊑★

left-path-source-result-id₁₀-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ↓ Ex2.example12-target-Z-seal)
      ↓ Ex2.example12-target-Y-seal)
      ↑ Ex2.example12-target-Y-unseal)
      ↑ Ex2.example12-target-Z-unseal)
      ⟨ Ex2.left-path-source-result-id★₆ ⟩)
    ⊑ (((((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ Ex2.left-path-target-Z-seal₂)
        ↓ Ex2.left-path-target-Y-seal₂)
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩) ∶
      ★⊑★
left-path-source-result-id₁₀-YZᵣ =
  CTI2.cast⊑cast² Ex2.left-path-source-result-id★₆
    Ex2.left-path-target-result-id★₃ left-path-both-Z-unsealed₁₀-YZᵣ
    ★⊑★

left-path-source-result-?X₁₀-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢²
    (((((((($ (κℕ 7)) ↓ Ex2.example12-target-X-seal)
      ⟨ Ex2.example12-target-X! ⟩)
      ↓ Ex2.example12-target-Z-seal)
      ↓ Ex2.example12-target-Y-seal)
      ↑ Ex2.example12-target-Y-unseal)
      ↑ Ex2.example12-target-Z-unseal)
      ⟨ Ex2.left-path-source-result-id★₆ ⟩)
      ⟨ Ex2.example12-target-★?X ⟩
    ⊑ (((((($ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩)
        ↓ Ex2.left-path-target-Z-seal₂)
        ↓ Ex2.left-path-target-Y-seal₂)
        ↑ Ex2.left-path-target-Y-unseal₂)
        ↑ Ex2.left-path-target-Z-unseal₂)
        ⟨ Ex2.left-path-target-result-id★₃ ⟩) ∶
      left-path-X-var⊑★-YZ₄ᵣ
left-path-source-result-?X₁₀-YZᵣ =
  CTI2.cast⊑² Ex2.example12-target-★?X
    left-path-source-result-id₁₀-YZᵣ left-path-X-var⊑★-YZ₄ᵣ

left-path-checkpoint₁₀-YZᵣ :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² Ex.right₁₀
    ⊑ Ex2.left-path-target₇ ∶ left-path-ℕ⊑★₄-YZᵣ
left-path-checkpoint₁₀-YZᵣ =
  reveal⊑²ᵣ (λ _ eq → eq) left-path-rebase-X-YZ₄ᴸᵣ
    CTX.same-[] Ex2.left-path-source-X-unseal₄-⊢ˣ
    left-path-source-result-?X₁₀-YZᵣ left-path-ℕ⊑★₄-YZᵣ

------------------------------------------------------------------------
-- Center-crossing: moved old target centers have no restricted rule
------------------------------------------------------------------------

zero₃ : Fin.Fin 3
zero₃ = Fin.zero

one₃ : Fin.Fin 3
one₃ = Fin.suc Fin.zero

one≢zero₃ : one₃ ≢ zero₃
one≢zero₃ ()

no-center-crossing-pairedᵣ :
  RebaseAtᵣ CCP.W′ CCP.W Fin.zero Fin.zero
  → ⊥
no-center-crossing-pairedᵣ rb =
  one≢zero₃ (target-frozen rb Fin.zero)

no-center-crossing-outerᴿᵣ :
  RebaseAtᴿᵣ CCP.W′ CCP.W (just Fin.zero)
  → ⊥
no-center-crossing-outerᴿᵣ (rebase-varᴿᵣ rb) =
  one≢zero₃ (target-frozen rb Fin.zero)

------------------------------------------------------------------------
-- Compile monotonicity gate surface
------------------------------------------------------------------------

compile-preserves-imprecision²-gate :
  CPI2.compile-preserves-imprecision²-statement
compile-preserves-imprecision²-gate =
  CPI2.compile-preserves-imprecision²
