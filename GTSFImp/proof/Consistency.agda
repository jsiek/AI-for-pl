module proof.Consistency where

-- File Charter:
--   * Proves that every closed type is consistent with the dynamic type.
--   * Derives the result from closed-type imprecision and the common-lower
--     characterization of consistency.
--   * Supplies consistency-side safety facts for polymorphic generated casts.
--   * Hosts proof-only consistency renaming conveniences and the structural
--     cast-size measure used by the DGG value catch-up foundation.
--   * Depends on proof.Imprecision and proof.ImprecisionConsistency.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; subst; sym; trans)
open import Relation.Nullary using (no; yes)

open import Types
open import Consistency
open SubstEnv∼
import CastTerms as CT
open import CastTerms using (GenSafe; safe-⇒; safe-∀; safe-inst; safe-gen)
open import proof.Imprecision using (imprecise-star; ∈ᵗ-unique)
open import proof.ImprecisionConsistency
  using (common-lower-consistent; refl⊑; nonstar-from-≢★;
    consistency-target-occurs-source)

------------------------------------------------------------------------
-- Renaming conveniences for proof code
------------------------------------------------------------------------

renameGroundᵐ : ∀ {Δ Δ′} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → Ground G
  → Ground (renameᵗ (toRenameᵗ ρ) G)
renameGroundᵐ ρ = renameGround (toRenameᵗ ρ)

rename∼★ᵐ : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → μ ⊢ G ∼★
  → renameEnv∼ ρ μ ⊢ renameᵗ (toRenameᵗ ρ) G ∼★
rename∼★ᵐ {μ = μ} ρ = rename∼★ (toRenameᵗ ρ)
  (renameEnv∼-preserves ρ μ)

rename★∼ᵐ : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → μ ⊢★∼ G
  → renameEnv∼ ρ μ ⊢★∼ renameᵗ (toRenameᵗ ρ) G
rename★∼ᵐ {μ = μ} ρ = rename★∼ (toRenameᵗ ρ)
  (renameEnv∼-preserves ρ μ)

renameᵐᶜ-idᵍ : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → (Gᵍ : Ground G)
  → renameᵐᶜ {μ = μ} ρ (idᵍ Gᵍ) ≡ idᵍ (renameGroundᵐ ρ Gᵍ)
renameᵐᶜ-idᵍ ρ ★⇒★ = refl
renameᵐᶜ-idᵍ ρ (‵ ι) = refl
renameᵐᶜ-idᵍ ρ (＇ X) = refl
renameᵐᶜ-idᵍ ρ ∀★ = refl

renameᵐᶜ-idᵍ! : ∀ {Δ Δ′} {μ : Env∼ Δ} {G : Ty Δ}
    {G∼★ : μ ⊢ G ∼★} {Gns : NonStar G}
  → (ρ : Δ ↪ᵗ Δ′)
  → (Gᵍ : Ground G)
  → renameᵐᶜ ρ (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (idᵍ Gᵍ) ⦃ Gns ⦄)
      ≡ _! ⦃ renameGroundᵐ ρ Gᵍ ⦄ ⦃ rename∼★ᵐ ρ G∼★ ⦄
          (idᵍ (renameGroundᵐ ρ Gᵍ))
          ⦃ renameNonStar (toRenameᵗ ρ) Gns ⦄
renameᵐᶜ-idᵍ! {G∼★ = ⇒∼★} ρ ★⇒★ = refl
renameᵐᶜ-idᵍ! {G∼★ = ι∼★} ρ (‵ ι) = refl
renameᵐᶜ-idᵍ! {G∼★ = X∼★ᵍ eq} ρ (＇ X) = refl
renameᵐᶜ-idᵍ! {G∼★ = X∼★ᶜ eq} ρ (＇ X) = refl
renameᵐᶜ-idᵍ! {G∼★ = ∀∼★} ρ ∀★ = refl

------------------------------------------------------------------------
-- Structural size of consistency proofs -- measure for the DGG value
-- catch-up driver (M6)
------------------------------------------------------------------------

castSize : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B
  → ℕ
castSize (id a) = suc zero
castSize (c ↦ d) = suc (castSize c + castSize d)
castSize (∀ᶜ c) = suc (castSize c)
castSize (_! c) = suc (castSize c)
castSize (？ c) = suc (castSize c)
castSize (inst_ c B≢★) = suc (castSize c)
castSize (gen_ c A≢★) = suc (castSize c)
castSize bot-elim = suc zero
castSize bot-intro = suc zero

castSize-subst-left-∼ : ∀ {Δ} {μ : Env∼ Δ}
    {A A′ B : Ty Δ}
  → (eq : A ≡ A′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-left-∼ eq c) ≡ castSize c
castSize-subst-left-∼ refl c = refl

castSize-subst-right-∼ : ∀ {Δ} {μ : Env∼ Δ}
    {A B B′ : Ty Δ}
  → (eq : B ≡ B′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-right-∼ eq c) ≡ castSize c
castSize-subst-right-∼ refl c = refl

castSize-rename∼ : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (eq : ∀ X → μ′ (ρ X) ≡ μ X)
  → (c : μ ⊢ A ∼ B)
  → castSize (rename∼ {μ = μ} {μ′ = μ′} ρ eq c) ≡ castSize c
castSize-rename∼ ρ eq (id ★) = refl
castSize-rename∼ ρ eq (id (‵ ι)) = refl
castSize-rename∼ ρ eq (id (＇ X)) = refl
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (c ↦ d) =
  cong₂ (λ m n → suc (m + n))
    (castSize-rename∼ {μ = flipᵐ μ} {μ′ = flipᵐ μ′} ρ
      (flip-rename-env {μ = μ} {μ′ = μ′} ρ eq) c)
    (castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq d)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (∀ᶜ c) =
  cong suc
    (castSize-rename∼ {μ = extᵐ μ} {μ′ = extᵐ μ′}
      (extᵗ ρ) (extᵐ-rename ρ eq) c)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (_! c) =
  cong suc (castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq c)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq (？ c) =
  cong suc (castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq c)
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq
    (inst_ {B = B} c B≢★) =
  cong suc
    (trans
      (castSize-subst-right-∼ (renameᵗ-shift ρ B)
        (rename∼ {μ = instᵐ μ} {μ′ = instᵐ μ′}
          (extᵗ ρ) (instᵐ-rename ρ eq) c))
      (castSize-rename∼ {μ = instᵐ μ} {μ′ = instᵐ μ′}
        (extᵗ ρ) (instᵐ-rename ρ eq) c))
castSize-rename∼ {μ = μ} {μ′ = μ′} ρ eq
    (gen_ {A = A} c A≢★) =
  cong suc
    (trans
      (castSize-subst-left-∼ (renameᵗ-shift ρ A)
        (rename∼ {μ = genᵐ μ} {μ′ = genᵐ μ′}
          (extᵗ ρ) (genᵐ-rename ρ eq) c))
      (castSize-rename∼ {μ = genᵐ μ} {μ′ = genᵐ μ′}
        (extᵗ ρ) (genᵐ-rename ρ eq) c))
castSize-rename∼ ρ eq bot-elim = refl
castSize-rename∼ ρ eq bot-intro = refl

castSize-renameEnvᶜ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
    {A B : Ty Δ}
  → (ρ : Δ ⇒ʳ Δ′)
  → (eq : ∀ X → ν (ρ X) ≡ μ X)
  → (c : μ ⊢ A ∼ B)
  → castSize (renameEnvᶜ {μ = μ} {ν = ν} ρ eq c) ≡ castSize c
castSize-renameEnvᶜ {μ = μ} {ν = ν} ρ eq c =
  castSize-rename∼ {μ = μ} {μ′ = ν} ρ eq c

castSize-renameᵐᶜ : ∀ {Δ Δ′} {μ : Env∼ Δ}
    {A B : Ty Δ}
  → (ρ : Δ ↪ᵗ Δ′)
  → (c : μ ⊢ A ∼ B)
  → castSize (renameᵐᶜ ρ c) ≡ castSize c
castSize-renameᵐᶜ {μ = μ} ρ c =
  castSize-rename∼ {μ = μ} {μ′ = renameEnv∼ ρ μ}
    (toRenameᵗ ρ) (renameEnv∼-preserves ρ μ) c

castSize-↑ᶜ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → castSize (↑ᶜ c) ≡ castSize c
castSize-↑ᶜ = castSize-renameᵐᶜ wk↪ᵗ

castSize-subst-left-∼-≤ : ∀ {Δ} {μ : Env∼ Δ}
    {A A′ B : Ty Δ}
  → (eq : A ≡ A′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-left-∼ eq c) ≤ castSize c
castSize-subst-left-∼-≤ refl c = ≤-refl

castSize-subst-right-∼-≤ : ∀ {Δ} {μ : Env∼ Δ}
    {A B B′ : Ty Δ}
  → (eq : B ≡ B′)
  → (c : μ ⊢ A ∼ B)
  → castSize (subst-right-∼ eq c) ≤ castSize c
castSize-subst-right-∼-≤ refl c = ≤-refl

castSize-transport-env∼ : ∀ {Δ} {μ ν : Env∼ Δ} {A B : Ty Δ}
  → (eq : μ ≡ ν)
  → (c : μ ⊢ A ∼ B)
  → castSize (transport-env∼ eq c) ≡ castSize c
castSize-transport-env∼ refl c = refl

castSize-sym∼ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → castSize (sym∼ c) ≡ castSize c
castSize-sym∼ (id ★) = refl
castSize-sym∼ (id (‵ ι)) = refl
castSize-sym∼ (id (＇ X)) = refl
castSize-sym∼ (c ↦ d) =
  cong₂ (λ m n → suc (m + n)) (castSize-sym∼ c)
    (castSize-sym∼ d)
castSize-sym∼ (∀ᶜ c) =
  cong suc
    (trans (castSize-transport-env∼ flip-extᵐ (sym∼ c))
      (castSize-sym∼ c))
castSize-sym∼ (_! c) = cong suc (castSize-sym∼ c)
castSize-sym∼ (？ c) = cong suc (castSize-sym∼ c)
castSize-sym∼ (inst_ c B≢★) =
  cong suc
    (trans (castSize-transport-env∼ flip-instᵐ (sym∼ c))
      (castSize-sym∼ c))
castSize-sym∼ (gen_ c A≢★) =
  cong suc
    (trans (castSize-transport-env∼ flip-genᵐ (sym∼ c))
      (castSize-sym∼ c))
castSize-sym∼ bot-elim = refl
castSize-sym∼ bot-intro = refl

private

  record SubstEnvSize≤ {Δ Δ′ : TyCtx} {μ : Env∼ Δ}
      {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′}
      (s : SubstEnv∼ μ ν σ) : Set where
    constructor subst-env-size≤
    field
      self≤ : ∀ X → castSize (self s X) ≤ suc zero
      to-★≤ : ∀ X eq → castSize (to-★ s X eq) ≤ suc (suc zero)
      from-★≤ : ∀ X eq → castSize (from-★ s X eq) ≤ suc (suc zero)
      cross-to-★≤ :
        ∀ X eq → castSize (cross-to-★ s X eq) ≤ suc (suc zero)
      cross-from-★≤ :
        ∀ X eq → castSize (cross-from-★ s X eq) ≤ suc (suc zero)

  open SubstEnvSize≤

  ext-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (ext-SubstEnv∼ s)
  ext-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (ext-SubstEnv∼ s) X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X)
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (self s X) =
        self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (ext-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    to-★≤′ zero ()
    to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (to-★ s X eq) =
        to-★≤ bounds X eq

    from-★≤′ : ∀ X eq
      → castSize (from-★ (ext-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    from-★≤′ zero ()
    from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (from-★ s X eq) =
        from-★≤ bounds X eq

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (ext-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl) (cross-to-★ s X eq) =
        cross-to-★≤ bounds X eq

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (ext-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = extᵐ ν}
        suc (λ Y → refl)
        (cross-from-★ s X eq) =
          cross-from-★≤ bounds X eq

  inst-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (inst-SubstEnv∼ s)
  inst-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (inst-SubstEnv∼ s) X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X)
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (self s X) =
        self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (inst-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    to-★≤′ zero eq = ≤-refl
    to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (to-★ s X eq) =
        to-★≤ bounds X eq

    from-★≤′ : ∀ X eq
      → castSize (from-★ (inst-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    from-★≤′ zero ()
    from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (from-★ s X eq) =
        from-★≤ bounds X eq

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (inst-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl) (cross-to-★ s X eq) =
        cross-to-★≤ bounds X eq

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (inst-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = instᵐ ν}
        suc (λ Y → refl)
        (cross-from-★ s X eq) =
          cross-from-★≤ bounds X eq

  gen-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (gen-SubstEnv∼ s)
  gen-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (gen-SubstEnv∼ s) X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X)
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (self s X) =
        self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (gen-SubstEnv∼ s) X eq) ≤ suc (suc zero)
    to-★≤′ zero ()
    to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (to-★ s X eq) =
        to-★≤ bounds X eq

    from-★≤′ : ∀ X eq
      → castSize (from-★ (gen-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    from-★≤′ zero eq = ≤-refl
    from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (from-★ s X eq) =
        from-★≤ bounds X eq

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (gen-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl) (cross-to-★ s X eq) =
        cross-to-★≤ bounds X eq

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (gen-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq
      rewrite castSize-rename∼ {μ = ν} {μ′ = genᵐ ν}
        suc (λ Y → refl)
        (cross-from-★ s X eq) =
          cross-from-★≤ bounds X eq

  flip-SubstEnvSize≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → SubstEnvSize≤ (flip-SubstEnv∼ s)
  flip-SubstEnvSize≤ {μ = μ} {ν = ν} s bounds =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ X
      → castSize (self (flip-SubstEnv∼ s) X) ≤ suc zero
    self≤′ X rewrite castSize-sym∼ (self s X) = self≤ bounds X

    to-★≤′ : ∀ X eq
      → castSize (to-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    to-★≤′ X eq
      rewrite castSize-sym∼ (from-★ s X (flipVar∼-to-X∼★ eq)) =
        from-★≤ bounds X (flipVar∼-to-X∼★ eq)

    from-★≤′ : ∀ X eq
      → castSize (from-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    from-★≤′ X eq
      rewrite castSize-sym∼ (to-★ s X (flipVar∼-to-★∼X eq)) =
        to-★≤ bounds X (flipVar∼-to-★∼X eq)

    cross-to-★≤′ : ∀ X eq
      → castSize (cross-to-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ X eq
      rewrite castSize-sym∼
        (cross-from-★ s X (flipVar∼-to-★∼X∼★ eq)) =
          cross-from-★≤ bounds X (flipVar∼-to-★∼X∼★ eq)

    cross-from-★≤′ : ∀ X eq
      → castSize (cross-from-★ (flip-SubstEnv∼ s) X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ X eq
      rewrite castSize-sym∼
        (cross-to-★ s X (flipVar∼-to-★∼X∼★ eq)) =
          cross-to-★≤ bounds X (flipVar∼-to-★∼X∼★ eq)

  castSize-factor-inst-star-≤ :
      ∀ {Δ} {μ : Env∼ Δ} {A : Ty (suc Δ)}
    → (c : instᵐ μ ⊢ A ∼ ★)
    → (Anv : NonVar A)
    → (z∈A : zero ∈ᵗ A)
    → castSize (factor-inst-star c Anv z∈A) ≤ suc (castSize c)
  castSize-factor-inst-star-≤ (id ★) Anv ()
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄)
      Anv z∈A =
    ⊥-elim (inst-to-var-occurs-impossible c eq Anv z∈A)
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ zero ⦄ ⦃ G∼★ = X∼★ᶜ () ⦄ c ⦃ Ans ⦄)
      Anv z∈A
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ suc X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄
          c ⦃ Ans ⦄)
      Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ G∼★ = X∼★ᶜ eq ⦄ c ⦃ Ans ⦄)
      Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤
      (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) Anv z∈A = ≤-refl
  castSize-factor-inst-star-≤ (？_ ⦃ g ⦄ c ⦃ Bns ⦄) Anv ()
  castSize-factor-inst-star-≤
      (inst_ ⦃ Anv′ ⦄ ⦃ z∈A′ ⦄ c ★≢★) Anv z∈A =
    ⊥-elim (★≢★ refl)

  castSize-factor-gen-star-≤ :
      ∀ {Δ} {μ : Env∼ Δ} {B : Ty (suc Δ)}
    → (c : genᵐ μ ⊢ ★ ∼ B)
    → (Bnv : NonVar B)
    → (z∈B : zero ∈ᵗ B)
    → castSize (factor-gen-star c Bnv z∈B) ≤ suc (castSize c)
  castSize-factor-gen-star-≤ (id ★) Bnv ()
  castSize-factor-gen-star-≤ (_! ⦃ g ⦄ c ⦃ () ⦄) Bnv z∈B
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ zero ⦄
          ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B =
    ⊥-elim (gen-from-var-occurs-impossible c eq Bnv z∈B)
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ zero ⦄
          ⦃ ★∼G = ★∼Xᶜ () ⦄ c ⦃ Bns ⦄)
      Bnv z∈B
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ＇ suc X ⦄
          ⦃ ★∼G = ★∼Xᶜ eq ⦄ c ⦃ Bns ⦄)
      Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) Bnv z∈B = ≤-refl
  castSize-factor-gen-star-≤
      (gen_ ⦃ Bnv′ ⦄ ⦃ z∈B′ ⦄ c ★≢★) Bnv z∈B =
    ⊥-elim (★≢★ refl)

  castSize-subst-to-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
        {σ : Δ ⇒ˢ Δ′} {A : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ A ∼ ＇ X)
    → (eq : μ X ≡ X∼★)
    → (Ans : NonStar A)
    → castSize (subst-to-star-var s c eq Ans) ≤ suc (castSize c)
  castSize-subst-to-star-var-≤ s bounds (id (＇ X)) eq Ans =
    to-★≤ bounds X eq
  castSize-subst-to-star-var-≤ s bounds (？_ c ⦃ Bns ⦄) eq ()
  castSize-subst-to-star-var-≤ s bounds
      c@(inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) eq Ans =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all Ans)

  castSize-subst-cross-to-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
        {σ : Δ ⇒ˢ Δ′} {A : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ A ∼ ＇ X)
    → (eq : μ X ≡ ★∼X∼★)
    → (Ans : NonStar A)
    → castSize (subst-cross-to-star-var s c eq Ans)
      ≤ suc (castSize c)
  castSize-subst-cross-to-star-var-≤ s bounds (id (＇ X)) eq Ans =
    cross-to-★≤ bounds X eq
  castSize-subst-cross-to-star-var-≤ s bounds
      (？_ c ⦃ Bns ⦄) eq ()
  castSize-subst-cross-to-star-var-≤ s bounds
      c@(inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ d B≢★) eq Ans =
    ⊥-elim (nonstar-nonvar-to-var-impossible c nonvar-all Ans)

  castSize-subst-from-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
        {σ : Δ ⇒ˢ Δ′} {B : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ ＇ X ∼ B)
    → (eq : μ X ≡ ★∼X)
    → (Bns : NonStar B)
    → castSize (subst-from-star-var s c eq Bns) ≤ suc (castSize c)
  castSize-subst-from-star-var-≤ s bounds (id (＇ X)) eq Bns =
    from-★≤ bounds X eq
  castSize-subst-from-star-var-≤ s bounds (_! c ⦃ Ans ⦄) eq ()
  castSize-subst-from-star-var-≤ s bounds
      c@(gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) eq Bns =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all Bns)

  castSize-subst-cross-from-star-var-≤ :
      ∀ {Δ Δ′} {μ : Env∼ Δ}
        {ν : Env∼ Δ′} {σ : Δ ⇒ˢ Δ′} {B : Ty Δ} {X}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ ＇ X ∼ B)
    → (eq : μ X ≡ ★∼X∼★)
    → (Bns : NonStar B)
    → castSize (subst-cross-from-star-var s c eq Bns)
      ≤ suc (castSize c)
  castSize-subst-cross-from-star-var-≤ s bounds (id (＇ X)) eq Bns =
    cross-from-★≤ bounds X eq
  castSize-subst-cross-from-star-var-≤ s bounds
      (_! c ⦃ Ans ⦄) eq ()
  castSize-subst-cross-from-star-var-≤ s bounds
      c@(gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ d A≢★) eq Bns =
    ⊥-elim (var-to-nonstar-nonvar-impossible c nonvar-all Bns)

  castSize-subst∼-≤ : ∀ {Δ Δ′} {μ : Env∼ Δ} {ν : Env∼ Δ′}
      {σ : Δ ⇒ˢ Δ′} {A B : Ty Δ}
    → (s : SubstEnv∼ μ ν σ)
    → SubstEnvSize≤ s
    → (c : μ ⊢ A ∼ B)
    → castSize (subst∼ s c) ≤ castSize c
  castSize-subst∼-≤ s bounds (id ★) = ≤-refl
  castSize-subst∼-≤ s bounds (id (‵ ι)) = ≤-refl
  castSize-subst∼-≤ s bounds (id (＇ X)) = self≤ bounds X
  castSize-subst∼-≤ s bounds (c ↦ d) =
    s≤s (+-mono-≤
      (castSize-subst∼-≤ (flip-SubstEnv∼ s)
        (flip-SubstEnvSize≤ s bounds) c)
      (castSize-subst∼-≤ s bounds d))
  castSize-subst∼-≤ s bounds (∀ᶜ c) =
    s≤s (castSize-subst∼-≤ (ext-SubstEnv∼ s)
      (ext-SubstEnvSize≤ s bounds) c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (_! ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Ans ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (_! ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Ans ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ s bounds
      (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᵍ eq ⦄ c ⦃ Ans ⦄) =
    castSize-subst-to-star-var-≤ s bounds c eq Ans
  castSize-subst∼-≤ s bounds
      (_! ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = X∼★ᶜ eq ⦄ c ⦃ Ans ⦄) =
    castSize-subst-cross-to-star-var-≤ s bounds c eq Ans
  castSize-subst∼-≤ {σ = σ} s bounds
      (_! ⦃ Gᵍ = ∀★ ⦄ c ⦃ Ans ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (？_ ⦃ Gᵍ = ★⇒★ ⦄ c ⦃ Bns ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (？_ ⦃ Gᵍ = ‵ ι ⦄ c ⦃ Bns ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ s bounds
      (？_ ⦃ Gᵍ = ＇ X ⦄
          ⦃ ★∼G = ★∼Xᵍ eq ⦄ c ⦃ Bns ⦄) =
    castSize-subst-from-star-var-≤ s bounds c eq Bns
  castSize-subst∼-≤ s bounds
      (？_ ⦃ Gᵍ = ＇ X ⦄
          ⦃ ★∼G = ★∼Xᶜ eq ⦄ c ⦃ Bns ⦄) =
    castSize-subst-cross-from-star-var-≤ s bounds c eq Bns
  castSize-subst∼-≤ {σ = σ} s bounds
      (？_ ⦃ Gᵍ = ∀★ ⦄ c ⦃ Bns ⦄) =
    s≤s (castSize-subst∼-≤ s bounds c)
  castSize-subst∼-≤ {σ = σ} s bounds
      (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
      with substᵗ σ B ≟Ty ★
  castSize-subst∼-≤ {σ = σ} s bounds
      (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
      | no Bσ≢★ =
    s≤s (≤-trans
      (castSize-subst-right-∼-≤ (substᵗ-shift σ B)
        (subst∼ (inst-SubstEnv∼ s) c))
      (castSize-subst∼-≤ (inst-SubstEnv∼ s)
        (inst-SubstEnvSize≤ s bounds) c))
  castSize-subst∼-≤ {σ = σ} s bounds
      (inst_ {B = B} ⦃ A-nonvar ⦄ ⦃ zero∈A ⦄ c B≢★)
      | yes Bσ≡★ =
    ≤-trans
      (castSize-subst-right-∼-≤ (sym Bσ≡★)
        (factor-inst-star
          (subst-right-∼
            (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
            (subst∼ (inst-SubstEnv∼ s) c))
          (substNonVar (extsᵗ σ) A-nonvar)
          (subst-∈ᵗ zero∈A var-∈)))
      (≤-trans
      (castSize-factor-inst-star-≤
        (subst-right-∼
          (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
          (subst∼ (inst-SubstEnv∼ s) c))
        (substNonVar (extsᵗ σ) A-nonvar)
        (subst-∈ᵗ zero∈A var-∈))
      (s≤s (≤-trans
        (castSize-subst-right-∼-≤
          (trans (substᵗ-shift σ B) (cong (renameᵗ suc) Bσ≡★))
          (subst∼ (inst-SubstEnv∼ s) c))
        (castSize-subst∼-≤ (inst-SubstEnv∼ s)
          (inst-SubstEnvSize≤ s bounds) c))))
  castSize-subst∼-≤ {σ = σ} s bounds
      (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
      with substᵗ σ A ≟Ty ★
  castSize-subst∼-≤ {σ = σ} s bounds
      (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
      | no Aσ≢★ =
    s≤s (≤-trans
      (castSize-subst-left-∼-≤ (substᵗ-shift σ A)
        (subst∼ (gen-SubstEnv∼ s) c))
      (castSize-subst∼-≤ (gen-SubstEnv∼ s)
        (gen-SubstEnvSize≤ s bounds) c))
  castSize-subst∼-≤ {σ = σ} s bounds
      (gen_ {A = A} ⦃ B-nonvar ⦄ ⦃ zero∈B ⦄ c A≢★)
      | yes Aσ≡★ =
    ≤-trans
      (castSize-subst-left-∼-≤ (sym Aσ≡★)
        (factor-gen-star
          (subst-left-∼
            (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
            (subst∼ (gen-SubstEnv∼ s) c))
          (substNonVar (extsᵗ σ) B-nonvar)
          (subst-∈ᵗ zero∈B var-∈)))
      (≤-trans
      (castSize-factor-gen-star-≤
        (subst-left-∼
          (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
          (subst∼ (gen-SubstEnv∼ s) c))
        (substNonVar (extsᵗ σ) B-nonvar)
        (subst-∈ᵗ zero∈B var-∈))
      (s≤s (≤-trans
        (castSize-subst-left-∼-≤
          (trans (substᵗ-shift σ A) (cong (renameᵗ suc) Aσ≡★))
          (subst∼ (gen-SubstEnv∼ s) c))
        (castSize-subst∼-≤ (gen-SubstEnv∼ s)
          (gen-SubstEnvSize≤ s bounds) c))))
  castSize-subst∼-≤ s bounds bot-elim = ≤-refl
  castSize-subst∼-≤ s bounds bot-intro = ≤-refl

  close-inst-SubstEnvSize≤ : ∀ {Δ} {μ : Env∼ Δ}
    → SubstEnvSize≤
        (subst-env∼ (close-inst-self {μ = μ}) close-inst-to-★
          close-inst-from-★ close-inst-cross-to-★
          close-inst-cross-from-★)
  close-inst-SubstEnvSize≤ =
    subst-env-size≤ self≤′ to-★≤′ from-★≤′ cross-to-★≤′
      cross-from-★≤′
    where
    self≤′ : ∀ {Δ} {μ : Env∼ Δ} X
      → castSize (close-inst-self {μ = μ} X) ≤ suc zero
    self≤′ zero = ≤-refl
    self≤′ (suc X) = ≤-refl

    to-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-to-★ {μ = μ} X eq) ≤ suc (suc zero)
    to-★≤′ zero eq = s≤s z≤n
    to-★≤′ (suc X) eq = ≤-refl

    from-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-from-★ {μ = μ} X eq)
        ≤ suc (suc zero)
    from-★≤′ zero ()
    from-★≤′ (suc X) eq = ≤-refl

    cross-to-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-cross-to-★ {μ = μ} X eq)
        ≤ suc (suc zero)
    cross-to-★≤′ zero ()
    cross-to-★≤′ (suc X) eq = ≤-refl

    cross-from-★≤′ : ∀ {Δ} {μ : Env∼ Δ} X eq
      → castSize (close-inst-cross-from-★ {μ = μ} X eq)
        ≤ suc (suc zero)
    cross-from-★≤′ zero ()
    cross-from-★≤′ (suc X) eq = ≤-refl

castSize-close-inst-≤ : ∀ {Δ} {μ : Env∼ Δ}
    {A : Ty (suc Δ)} {B : Ty Δ}
  → (c : instᵐ μ ⊢ A ∼ ⇑ᵗ B)
  → castSize (↑ᶜ (close-instᶜ c)) ≤ castSize c
castSize-close-inst-≤ {B = B} c
  rewrite castSize-↑ᶜ (close-instᶜ c) =
    ≤-trans
      (castSize-subst-right-∼-≤ (shift-openᵗ B ★)
        (subst∼
          (subst-env∼ close-inst-self close-inst-to-★
            close-inst-from-★ close-inst-cross-to-★
            close-inst-cross-from-★)
          c))
      (castSize-subst∼-≤
        (subst-env∼ close-inst-self close-inst-to-★ close-inst-from-★
          close-inst-cross-to-★ close-inst-cross-from-★)
        close-inst-SubstEnvSize≤ c)

consistent-star : ∀ (A : Ty 0) → A ∼ ★
consistent-star A = common-lower-consistent
  (A , refl⊑ A , imprecise-star A)

------------------------------------------------------------------------
-- Polymorphic generated cast safety
------------------------------------------------------------------------

data Preimage {Δ Δ′ : TyCtx} (ρ : Δ ⇒ʳ Δ′) (Y : TyVar Δ′)
    (A : Ty Δ) : Set where
  found : (X : TyVar Δ) → ρ X ≡ Y → X ∈ᵗ A → Preimage ρ Y A

rename-preimage : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {Y : TyVar Δ′}
    {A : Ty Δ}
  → Y ∈ᵗ renameᵗ ρ A
  → Preimage ρ Y A
rename-preimage {A = ＇ X} var-∈ = found X refl var-∈
rename-preimage {A = ‵ ι} ()
rename-preimage {A = ★} ()
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    with rename-preimage Y∈A
rename-preimage {A = A ⇒ B} (∈-fun-left Y∈A)
    | found X eq X∈A =
  found X eq (∈-fun-left X∈A)
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    with rename-preimage Y∈B
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | found X eq X∈B with occurs? X A
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | found X eq X∈B | present X∈A =
  found X eq (∈-fun-left X∈A)
rename-preimage {A = A ⇒ B} (∈-fun-right Y∉A Y∈B)
    | found X eq X∈B | absent X∉A =
  found X eq (∈-fun-right X∉A X∈B)
rename-preimage {A = `∀ A} (∈-all Y∈A)
    with rename-preimage Y∈A
rename-preimage {A = `∀ A} (∈-all Y∈A)
    | found Fin.zero () X∈A
rename-preimage {A = `∀ A} (∈-all Y∈A)
    | found (Fin.suc X) refl X∈A =
  found X refl (∈-all X∈A)

zero-not-shift : ∀ {Δ} {A : Ty Δ} → Fin.zero ∈ᵗ ⇑ᵗ A → ⊥
zero-not-shift z∈ with rename-preimage z∈
zero-not-shift z∈ | found X () X∈A

shift-star-injective : ∀ {Δ} {A : Ty Δ}
  → ⇑ᵗ A ≡ ★
  → A ≡ ★
shift-star-injective {A = ＇ X} ()
shift-star-injective {A = ‵ ι} ()
shift-star-injective {A = ★} refl = refl
shift-star-injective {A = A ⇒ B} ()
shift-star-injective {A = `∀ A} ()

gen-safe′ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
    {C B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ C ∼ B)
  → C ≡ ⇑ᵗ A
  → A ≢ ★
  → NonVar B
  → Fin.zero ∈ᵗ B
  → GenSafe c
gen-safe′ (id a) refl A≢★ Bnv z∈B =
  ⊥-elim (zero-not-shift z∈B)
gen-safe′ (c ↦ d) eq A≢★ Bnv z∈B = safe-⇒
gen-safe′ (∀ᶜ c) eq A≢★ Bnv z∈B = safe-∀
gen-safe′ (_! ⦃ g ⦄ c ⦃ Ans ⦄) eq A≢★ Bnv ()
gen-safe′ (？_ ⦃ g ⦄ c ⦃ Bns ⦄)
    eq A≢★ Bnv z∈B =
  ⊥-elim (A≢★ (shift-star-injective (sym eq)))
gen-safe′ (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) eq A≢★ Bnv z∈B =
  safe-inst B≢★
gen-safe′ (gen_ {A = C} ⦃ Cnv ⦄ ⦃ z∈C ⦄ c C≢★)
    eq A≢★ Bnv z∈B =
  safe-gen C≢★ (gen-safe′ c refl C≢★ Cnv z∈C)
gen-safe′ bot-elim eq A≢★ Bnv (∈-all ())
gen-safe′ bot-intro eq A≢★ Bnv (∈-all ())

gen-safe : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ} {B : Ty (suc Δ)}
  → (c : genᵐ μ ⊢ ⇑ᵗ A ∼ B)
  → A ≢ ★
  → NonVar B
  → Fin.zero ∈ᵗ B
  → GenSafe c
gen-safe c A≢★ Bnv z∈B = gen-safe′ c refl A≢★ Bnv z∈B

strict-safe : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ} {A B : Ty Δ}
  → μ X ≡ X∼X
  → (c : μ ⊢ A ∼ B)
  → NonVar B
  → X ∈ᵗ B
  → GenSafe c
strict-safe same (id (‵ ι)) nonvar-base ()
strict-safe same (id ★) nonvar-star ()
strict-safe same (id (＇ X)) () X∈B
strict-safe same (c ↦ d) Bnv X∈B = safe-⇒
strict-safe same (∀ᶜ c) Bnv X∈B = safe-∀
strict-safe same (_! ⦃ g ⦄ c ⦃ Ans ⦄) Bnv ()
strict-safe same c@(？_ ⦃ g ⦄ d ⦃ Bns ⦄) Bnv X∈B
    with consistency-target-occurs-source same c X∈B
strict-safe same c@(？_ ⦃ g ⦄ d ⦃ Bns ⦄) Bnv X∈B | ()
strict-safe same (inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) Bnv X∈B =
  safe-inst B≢★
strict-safe same (gen_ ⦃ Bnv′ ⦄ ⦃ z∈B′ ⦄ c A≢★) Bnv X∈B =
  safe-gen A≢★ (gen-safe c A≢★ Bnv′ z∈B′)
strict-safe same bot-elim Bnv (∈-all ())
strict-safe same bot-intro Bnv (∈-all ())

ext-safe : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
  → (c : extᵐ μ ⊢ A ∼ B)
  → NonVar B
  → Fin.zero ∈ᵗ B
  → GenSafe c
ext-safe = strict-safe refl

data GenSafeView {Δ : TyCtx} {μ : Env∼ Δ} :
    ∀ {A B : Ty Δ} {c : μ ⊢ A ∼ B} → GenSafe c → Set where
  gen-safe-inert : ∀ {A B : Ty Δ} {c : μ ⊢ A ∼ B}
      {safe : GenSafe c}
    → CT.Inert c
    → GenSafeView safe

  gen-safe-inst : ∀ {A₀ : Ty (suc Δ)} {B₀ : Ty Δ}
      {d : instᵐ μ ⊢ A₀ ∼ ⇑ᵗ B₀}
      ⦃ A₀nv : NonVar A₀ ⦄ ⦃ z∈A₀ : Fin.zero ∈ᵗ A₀ ⦄
    → (B₀≢★ : B₀ ≢ ★)
    → GenSafeView {A = `∀ A₀} {B = B₀}
        {c = (inst d) B₀≢★} (safe-inst B₀≢★)

gen-safe-view : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (safe : GenSafe c)
  → GenSafeView safe
gen-safe-view safe-⇒ = gen-safe-inert CT.fun
gen-safe-view safe-∀ = gen-safe-inert CT.all
gen-safe-view (safe-inst B≢★) = gen-safe-inst B≢★
gen-safe-view (safe-gen A≢★ safe) =
  gen-safe-inert (CT.genᵥ A≢★ safe)

rename-occursᶜ : ∀ {Δ Δ′} {X : TyVar Δ} {A : Ty Δ}
  → (rho : Δ ⇒ʳ Δ′)
  → X ∈ᵗ A
  → rho X ∈ᵗ renameᵗ rho A
rename-occursᶜ rho var-∈ = var-∈
rename-occursᶜ rho (∈-fun-left X∈A) =
  ∈-fun-left (rename-occursᶜ rho X∈A)
rename-occursᶜ {X = X} {A = A ⇒ B} rho (∈-fun-right X∉A X∈B)
    with occurs? (rho X) (renameᵗ rho A)
rename-occursᶜ {X = X} {A = A ⇒ B} rho (∈-fun-right X∉A X∈B)
    | present rhoX∈A = ∈-fun-left rhoX∈A
rename-occursᶜ {X = X} {A = A ⇒ B} rho (∈-fun-right X∉A X∈B)
    | absent rhoX∉A =
  ∈-fun-right rhoX∉A (rename-occursᶜ rho X∈B)
rename-occursᶜ rho (∈-all X∈A) =
  ∈-all (rename-occursᶜ (extᵗ rho) X∈A)
subst-left-gen-safe : ∀ {Δ} {μ : Env∼ Δ} {A A′ B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (eq : A ≡ A′)
  → GenSafe c
  → GenSafe (subst-left-∼ eq c)
subst-left-gen-safe refl safe = safe
renameGenSafe : ∀ {Δ Δ′} {μ : Env∼ Δ} {μ′ : Env∼ Δ′}
    {A B : Ty Δ} {c : μ ⊢ A ∼ B}
  → (rho : Δ ⇒ʳ Δ′)
  → (eq : ∀ X → μ′ (rho X) ≡ μ X)
  → GenSafe c
  → GenSafe (rename∼ {μ = μ} {μ′ = μ′} rho eq c)
renameGenSafe rho eq safe-⇒ = safe-⇒
renameGenSafe rho eq safe-∀ = safe-∀
renameGenSafe {μ = μ} {μ′ = μ′} rho eq
    (safe-inst {A = A} {B = B} {c = c}
      ⦃ Anv ⦄ ⦃ z∈A ⦄ B≢★) =
  subst
    (λ z → GenSafe
      (inst_ ⦃ renameNonVar (extᵗ rho) Anv ⦄
        ⦃ z ⦄ c′ B′≢★))
    (∈ᵗ-unique (rename-occursᶜ (extᵗ rho) z∈A) _)
    (safe-inst
      ⦃ renameNonVar (extᵗ rho) Anv ⦄
      ⦃ rename-occursᶜ (extᵗ rho) z∈A ⦄
      B′≢★)
  where
  c′ = subst-right-∼ (renameᵗ-shift rho B)
    (rename∼ {μ = instᵐ μ} {μ′ = instᵐ μ′}
      (extᵗ rho) (instᵐ-rename rho eq) c)
  B′≢★ = nonStar≢★
    (renameNonStar rho (nonstar-from-≢★ B≢★))
renameGenSafe {μ = μ} {μ′ = μ′} rho eq
    (safe-gen {A = A} {B = B} {c = c}
      ⦃ Bnv ⦄ ⦃ z∈B ⦄ A≢★ safe) =
  subst
    (λ z → GenSafe
      (gen_ ⦃ renameNonVar (extᵗ rho) Bnv ⦄
        ⦃ z ⦄ c′ A′≢★))
    (∈ᵗ-unique (rename-occursᶜ (extᵗ rho) z∈B) _)
    (safe-gen
      ⦃ renameNonVar (extᵗ rho) Bnv ⦄
      ⦃ rename-occursᶜ (extᵗ rho) z∈B ⦄
      A′≢★
      (subst-left-gen-safe (renameᵗ-shift rho _)
        (renameGenSafe {μ′ = genᵐ μ′} (extᵗ rho)
          (genᵐ-rename rho eq) safe)))
  where
  c′ = subst-left-∼ (renameᵗ-shift rho A)
    (rename∼ {μ = genᵐ μ} {μ′ = genᵐ μ′}
      (extᵗ rho) (genᵐ-rename rho eq) c)
  A′≢★ = nonStar≢★
    (renameNonStar rho (nonstar-from-≢★ A≢★))
