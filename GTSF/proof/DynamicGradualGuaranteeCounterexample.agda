module proof.DynamicGradualGuaranteeCounterexample where

-- File Charter:
--   * Documents and mechanizes the counterexample shape for the current
--     `dynamicGradualGuarantee` statement.
--   * The obstruction is syntactic: right-hand `ν-step` produces a runtime
--     bullet target, but `TermNarrowing` has no constructor whose conclusion
--     can introduce such a target.
--   * No postulates are introduced here.

open import Data.Empty using (⊥)
open import Data.Nat using (zero)

open import Coercions
open import NuTerms
open import TermNarrowing
open import Types

data RuntimeBulletTarget : Term → Set where
  bullet-target : ∀ {V} → RuntimeBulletTarget (V •)
  cast-target : ∀ {V c} → RuntimeBulletTarget ((V •) ⟨ c ⟩)

runtimeBulletTarget-⇑ᵗᵐ :
  ∀ {M} →
  RuntimeBulletTarget M →
  RuntimeBulletTarget (⇑ᵗᵐ M)
runtimeBulletTarget-⇑ᵗᵐ bullet-target = bullet-target
runtimeBulletTarget-⇑ᵗᵐ cast-target = cast-target

no-runtime-bullet-target :
  ∀ {Δ σ γ M M′ p} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
  RuntimeBulletTarget M′ →
  ⊥
no-runtime-bullet-target (extend qᶜ pαᶜ M⊒N′) target =
  no-runtime-bullet-target M⊒N′ target
no-runtime-bullet-target (split qᶜ pαᶜ N⊒N′) target =
  no-runtime-bullet-target N⊒N′ target
no-runtime-bullet-target (⊒blame pᶜ) ()
no-runtime-bullet-target (x⊒x pᶜ x∋p) ()
no-runtime-bullet-target (ƛ⊒ƛ p↦qᶜ N⊒N′) ()
no-runtime-bullet-target (·⊒· qᶜ L⊒L′ M⊒M′) ()
no-runtime-bullet-target (Λ⊒Λ allᶜ vV V⊒V′) ()
no-runtime-bullet-target (⊒Λ pᶜ N⊒V′) ()
no-runtime-bullet-target (⊒⟨ν⟩ pᶜ sᵢ N⊒V′) cast-target =
  no-runtime-bullet-target N⊒V′ cast-target
no-runtime-bullet-target (α⊒α qᶜ pαᶜ L⊒L′) ()
no-runtime-bullet-target (⊒α pαᶜ L⊒L′) ()
no-runtime-bullet-target (ν⊒ν pᶜ qᶜ N⊒N′) ()
no-runtime-bullet-target (⊒ν pᶜ N⊒N′) ()
no-runtime-bullet-target (ν⊒ pᶜ N⊒N′) target =
  no-runtime-bullet-target N⊒N′ (runtimeBulletTarget-⇑ᵗᵐ target)
no-runtime-bullet-target (κ⊒κ κ) ()
no-runtime-bullet-target (⊕⊒⊕ M⊒M′ N⊒N′) ()
no-runtime-bullet-target (⊒cast+ qᶜ q⨟s≈r M⊒M′) cast-target =
  no-runtime-bullet-target M⊒M′ bullet-target
no-runtime-bullet-target (⊒cast- qᶜ q⨟s≈r M⊒M′) cast-target =
  no-runtime-bullet-target M⊒M′ bullet-target
no-runtime-bullet-target (cast+⊒ pᶜ r≈t⨟p M⊒M′) target =
  no-runtime-bullet-target M⊒M′ target
no-runtime-bullet-target (cast-⊒ pᶜ r≈t⨟p M⊒M′) target =
  no-runtime-bullet-target M⊒M′ target

α⊒α-ν-step-target-impossible :
  ∀ {Δ σ γ M L′ p} →
  Δ ∣ σ ∣ γ ⊢ M ⊒ ((⇑ᵗᵐ L′) •) ⟨ id (＇ zero) ⟩ ∶ p →
  ⊥
α⊒α-ν-step-target-impossible M⊒ν-target =
  no-runtime-bullet-target M⊒ν-target cast-target
