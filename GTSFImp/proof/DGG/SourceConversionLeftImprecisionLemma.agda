{-# OPTIONS --safe #-}

module proof.DGG.SourceConversionLeftImprecisionLemma where

-- File Charter:
--   * Proves the exact type-level move needed before structurally descending
--     through a source-only conceal in target-instantiation catch-up.
--   * Keeps the target type fixed and absent from the generated source pivot.
--   * Proves reveal/conceal directions mutually, following the conversion
--     typing derivation rather than adding a pending-spine classifier.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; subst)

open import Types
import Imprecision as I
open import TyStore using (TyStore; store-lift)
import Conversion as Conv
open import CastTerms using (Ctx)
import CastTerms as CT
open import proof.DGG.ConvImp using
  ( conv↑-zero-pre; conv↑-nonvar-post-zero
  ; conv↓-zero-post; conv↓-nonvar-pre-zero
  )
open import proof.Imprecision using (imprecision-to-fresh)
open import proof.ImprecisionConsistency using
  ( ext-injective; fin-suc-injective; rename-⊑; rename-occurs
  ; shift-not-occurs; unrename-occurs
  )
open import proof.DGG.World


renamed-type-absent-from-disaligned : ∀ {Δ Δ′}
    {ρ : Δ ⇒ʳ Δ′} {X : TyVar Δ′} {A : Ty Δ}
  → (∀ Y → ρ Y ≢ X)
  → X ∉ᵗ renameᵗ ρ A
renamed-type-absent-from-disaligned {A = ＇ Y} disaligned =
  ∉-var (≢→≢ᶠ (λ eq → disaligned Y (sym eq)))
renamed-type-absent-from-disaligned {A = ‵ ι} disaligned = ∉-base
renamed-type-absent-from-disaligned {A = ★} disaligned = ∉-star
renamed-type-absent-from-disaligned {A = A ⇒ B} disaligned =
  ∉-fun (renamed-type-absent-from-disaligned {A = A} disaligned)
    (renamed-type-absent-from-disaligned {A = B} disaligned)
renamed-type-absent-from-disaligned {ρ = ρ} {X = X} {A = `∀ A}
    disaligned =
  ∉-all (renamed-type-absent-from-disaligned {A = A} disaligned⁺)
  where
  disaligned⁺ : ∀ Y → extᵗ ρ Y ≢ Fin.suc X
  disaligned⁺ Fin.zero ()
  disaligned⁺ (Fin.suc Y) eq = disaligned Y (fin-suc-injective eq)


unrename-nonvar : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {A : Ty Δ}
  → NonVar (renameᵗ ρ A)
  → NonVar A
unrename-nonvar {A = ＇ X} ()
unrename-nonvar {A = ‵ ι} nonvar = nonvar-base
unrename-nonvar {A = ★} nonvar = nonvar-star
unrename-nonvar {A = A ⇒ B} nonvar = nonvar-fun
unrename-nonvar {A = `∀ A} nonvar = nonvar-all


shift-representation : ∀ {Δ} {μ : I.ImpEnv Δ} {R : Ty Δ}
  → μ I.⊢ R ⊑ ★
  → I.extᵐ μ I.⊢ ⇑ᵗ R ⊑ ★
shift-representation =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)


shift-inst-representation : ∀ {Δ} {μ : I.ImpEnv Δ} {R : Ty Δ}
  → μ I.⊢ R ⊑ ★
  → I.instᵐ μ I.⊢ ⇑ᵗ R ⊑ ★
shift-inst-representation =
  rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq)


lift-renamed-representation : ∀ {Δᴸ Δᶜ} {ρ : Δᴸ ⇒ʳ Δᶜ}
    {μ : I.ImpEnv Δᶜ} {R : Ty Δᴸ}
  → μ I.⊢ renameᵗ ρ R ⊑ ★
  → I.extᵐ μ I.⊢ renameᵗ (extᵗ ρ) (⇑ᵗ R) ⊑ ★
lift-renamed-representation {ρ = ρ} {R = R} represented =
  subst (λ T → I.extᵐ _ I.⊢ T ⊑ ★)
    (sym (renameᵗ-shift ρ R)) (shift-representation represented)


inst-renamed-representation : ∀ {Δᴸ Δᶜ} {ρ : Δᴸ ⇒ʳ Δᶜ}
    {μ : I.ImpEnv Δᶜ} {R : Ty Δᴸ}
  → μ I.⊢ renameᵗ ρ R ⊑ ★
  → I.instᵐ μ I.⊢ renameᵗ (extᵗ ρ) (⇑ᵗ R) ⊑ ★
inst-renamed-representation {ρ = ρ} {R = R} represented =
  subst (λ T → I.instᵐ _ I.⊢ T ⊑ ★)
    (sym (renameᵗ-shift ρ R)) (shift-inst-representation represented)


wrap-universal-star : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty (Nat.suc Δ)}
  → I.extᵐ μ I.⊢ A ⊑ ★
  → μ I.⊢ `∀ A ⊑ ★
wrap-universal-star {A = ＇ X} prem = I.∀⊑★ nonstar-X prem
wrap-universal-star {A = ‵ ι} prem = I.∀⊑★ nonstar-ι prem
wrap-universal-star {A = ★} prem = I.∀★⊑★
wrap-universal-star {A = A ⇒ B} prem = I.∀⊑★ nonstar-⇒ prem
wrap-universal-star {A = `∀ A} prem = I.∀⊑★ nonstar-∀ prem


mutual
  source-reveal-left-imprecision : ∀ {Δᴸ Δᶜ} {Σ : TyStore Δᴸ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv.Conv↑ Δᴸ A A′} {ρ : Δᴸ ⇒ʳ Δᶜ}
      {μ : I.ImpEnv Δᶜ} {E : Ty Δᶜ}
    → Σ Conv.⊢↑[ X ⦂ R ] c
    → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    → μ (ρ X) ≡ I.X⊑★
    → ρ X ∉ᵗ E
    → μ I.⊢ renameᵗ ρ R ⊑ ★
    → μ I.⊢ renameᵗ ρ A ⊑ E
    → μ I.⊢ renameᵗ ρ A′ ⊑ E

  source-reveal-universal-imprecision : ∀ {Δᴸ Δᶜ}
      {Σ : TyStore Δᴸ} {X : TyVar Δᴸ} {R : Ty Δᴸ}
      {A A′ : Ty (Nat.suc Δᴸ)}
      {c : Conv.Conv↑ (Nat.suc Δᴸ) A A′} {ρ : Δᴸ ⇒ʳ Δᶜ}
      {μ : I.ImpEnv Δᶜ} {S : Ty (Nat.suc Δᶜ)} {E : Ty Δᶜ}
    → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ ⇑ᵗ R ] c
    → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    → S ≡ renameᵗ (extᵗ ρ) A
    → μ (ρ X) ≡ I.X⊑★
    → ρ X ∉ᵗ E
    → μ I.⊢ renameᵗ ρ R ⊑ ★
    → μ I.⊢ `∀ S ⊑ E
    → μ I.⊢ `∀ (renameᵗ (extᵗ ρ) A′) ⊑ E

  source-conceal-universal-imprecision : ∀ {Δᴸ Δᶜ}
      {Σ : TyStore Δᴸ} {X : TyVar Δᴸ} {R : Ty Δᴸ}
      {A A′ : Ty (Nat.suc Δᴸ)}
      {c : Conv.Conv↓ (Nat.suc Δᴸ) A A′} {ρ : Δᴸ ⇒ʳ Δᶜ}
      {μ : I.ImpEnv Δᶜ} {S : Ty (Nat.suc Δᶜ)} {E : Ty Δᶜ}
    → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ ⇑ᵗ R ] c
    → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    → S ≡ renameᵗ (extᵗ ρ) A′
    → μ (ρ X) ≡ I.X⊑★
    → ρ X ∉ᵗ E
    → μ I.⊢ renameᵗ ρ R ⊑ ★
    → μ I.⊢ `∀ S ⊑ E
    → μ I.⊢ `∀ (renameᵗ (extᵗ ρ) A) ⊑ E

  source-reveal-left-imprecision (Conv.⊢↑-unseal member) injective
      mark fresh represented (I.X⊑X) =
    ⊥-elim (absent-to-not-equal fresh refl)
    where
    absent-to-not-equal : ∀ {Xᶜ : TyVar _}
      → Xᶜ ∉ᵗ ＇ Xᶜ
      → Xᶜ ≢ Xᶜ
    absent-to-not-equal (∉-var X≢X) = ≢ᶠ→≢ X≢X
  source-reveal-left-imprecision (Conv.⊢↑-unseal member) injective
      mark ∉-star represented (I.X⊑★ eq) = represented

  source-reveal-left-imprecision (Conv.⊢↑-⇒ left right) injective
      mark (∉-fun absent-domain absent-codomain) represented
      (I.⇒⊑⇒ domain codomain) =
    I.⇒⊑⇒
      (source-conceal-left-imprecision left injective mark absent-domain
        represented domain)
      (source-reveal-left-imprecision right injective mark absent-codomain
        represented codomain)
  source-reveal-left-imprecision (Conv.⊢↑-⇒ left right) injective
      mark ∉-star represented (I.⇒⊑★ domain codomain) =
    I.⇒⊑★
      (source-conceal-left-imprecision left injective mark ∉-star
        represented domain)
      (source-reveal-left-imprecision right injective mark ∉-star
        represented codomain)

  source-reveal-left-imprecision (Conv.⊢↑-∀ refl body) injective
      mark fresh represented prem =
    source-reveal-universal-imprecision body injective refl mark fresh
      represented prem

  source-reveal-left-imprecision (Conv.⊢↑-id-var member X≠Y) injective
      mark fresh represented prem = prem
  source-reveal-left-imprecision (Conv.⊢↑-id-base member) injective
      mark fresh represented prem = prem
  source-reveal-left-imprecision (Conv.⊢↑-id-star member) injective
      mark fresh represented prem = prem


  source-conceal-left-imprecision : ∀ {Δᴸ Δᶜ} {Σ : TyStore Δᴸ}
      {X : TyVar Δᴸ} {R : Ty Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv.Conv↓ Δᴸ A A′} {ρ : Δᴸ ⇒ʳ Δᶜ}
      {μ : I.ImpEnv Δᶜ} {E : Ty Δᶜ}
    → Σ Conv.⊢↓[ X ⦂ R ] c
    → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    → μ (ρ X) ≡ I.X⊑★
    → ρ X ∉ᵗ E
    → μ I.⊢ renameᵗ ρ R ⊑ ★
    → μ I.⊢ renameᵗ ρ A′ ⊑ E
    → μ I.⊢ renameᵗ ρ A ⊑ E

  source-conceal-left-imprecision (Conv.⊢↓-seal member) injective
      mark fresh represented I.X⊑X =
    ⊥-elim (absent-to-not-equal fresh refl)
    where
    absent-to-not-equal : ∀ {Xᶜ : TyVar _}
      → Xᶜ ∉ᵗ ＇ Xᶜ
      → Xᶜ ≢ Xᶜ
    absent-to-not-equal (∉-var X≢X) = ≢ᶠ→≢ X≢X
  source-conceal-left-imprecision (Conv.⊢↓-seal member) injective
      mark ∉-star represented (I.X⊑★ eq) = represented

  source-conceal-left-imprecision (Conv.⊢↓-⇒ left right) injective
      mark (∉-fun absent-domain absent-codomain) represented
      (I.⇒⊑⇒ domain codomain) =
    I.⇒⊑⇒
      (source-reveal-left-imprecision left injective mark absent-domain
        represented domain)
      (source-conceal-left-imprecision right injective mark absent-codomain
        represented codomain)
  source-conceal-left-imprecision (Conv.⊢↓-⇒ left right) injective
      mark ∉-star represented (I.⇒⊑★ domain codomain) =
    I.⇒⊑★
      (source-reveal-left-imprecision left injective mark ∉-star
        represented domain)
      (source-conceal-left-imprecision right injective mark ∉-star
        represented codomain)

  source-conceal-left-imprecision (Conv.⊢↓-∀ refl body) injective
      mark fresh represented prem =
    source-conceal-universal-imprecision body injective refl mark fresh
      represented prem

  source-conceal-left-imprecision (Conv.⊢↓-id-var member X≠Y) injective
      mark fresh represented prem = prem
  source-conceal-left-imprecision (Conv.⊢↓-id-base member) injective
      mark fresh represented prem = prem
  source-conceal-left-imprecision (Conv.⊢↓-id-star member) injective
      mark fresh represented prem = prem


  source-reveal-universal-imprecision {ρ = ρ}
      body injective source-eq mark (∉-all fresh) represented
      (I.∀⊑∀ prem) =
    I.∀⊑∀
      (source-reveal-left-imprecision body (ext-injective injective)
        mark fresh (lift-renamed-representation represented)
        (subst (λ T → I.extᵐ _ I.⊢ T ⊑ _) source-eq prem))
  source-reveal-universal-imprecision {ρ = ρ}
      body injective source-eq mark fresh represented
      (I.∀⊑ nonvar zero-occurs prem) =
    I.∀⊑
      (renameNonVar (extᵗ ρ)
        (conv↑-nonvar-post-zero body endpoint-nonvar
          endpoint-zero-post))
      (rename-occurs (extᵗ ρ) (ext-injective injective)
        endpoint-zero-post)
      (source-reveal-left-imprecision body (ext-injective injective) mark
        (shift-not-occurs fresh)
        (inst-renamed-representation represented)
        (subst (λ T → I.instᵐ _ I.⊢ T ⊑ _)
          source-eq prem))
    where
    endpoint-nonvar = unrename-nonvar
      (subst NonVar source-eq nonvar)
    endpoint-zero = unrename-occurs (extᵗ ρ)
      (ext-injective injective)
      (subst (Fin.zero ∈ᵗ_) source-eq zero-occurs)
    endpoint-zero-post = conv↑-zero-pre body endpoint-zero
  source-reveal-universal-imprecision body injective source-eq mark
      ∉-star represented I.∀★⊑★ =
    wrap-universal-star
      (source-reveal-left-imprecision body (ext-injective injective)
        mark ∉-star (lift-renamed-representation represented)
        (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ★)
          source-eq I.★⊑★))
  source-reveal-universal-imprecision
      body injective source-eq mark ∉-star represented
      (I.∀⊑★ nonstar prem) =
    wrap-universal-star
      (source-reveal-left-imprecision body (ext-injective injective)
        mark ∉-star (lift-renamed-representation represented)
        (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ★) source-eq prem))
  source-reveal-universal-imprecision
      body injective source-eq mark (∉-all fresh) represented I.bot-elim =
    subst (λ T → _ I.⊢ `∀ T ⊑ `∀ ★)
      (sym (imprecision-to-fresh output-prem)) I.bot-elim
    where
    output-prem = source-reveal-left-imprecision body
      (ext-injective injective) mark (∉-var fin-suc≢zero)
      (lift-renamed-representation represented)
      (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ＇ Fin.zero)
        source-eq I.X⊑X)
  source-reveal-universal-imprecision
      body injective source-eq mark ∉-star represented I.bot⊑★ =
    subst (λ T → _ I.⊢ `∀ T ⊑ ★)
      (sym (imprecision-to-fresh output-prem)) I.bot⊑★
    where
    output-prem = source-reveal-left-imprecision body
      (ext-injective injective) mark (∉-var fin-suc≢zero)
      (lift-renamed-representation represented)
      (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ＇ Fin.zero)
        source-eq I.X⊑X)


  source-conceal-universal-imprecision {ρ = ρ}
      body injective source-eq mark (∉-all fresh) represented
      (I.∀⊑∀ prem) =
    I.∀⊑∀
      (source-conceal-left-imprecision body (ext-injective injective)
        mark fresh (lift-renamed-representation represented)
        (subst (λ T → I.extᵐ _ I.⊢ T ⊑ _) source-eq prem))
  source-conceal-universal-imprecision {ρ = ρ}
      body injective source-eq mark fresh represented
      (I.∀⊑ nonvar zero-occurs prem) =
    I.∀⊑
      (renameNonVar (extᵗ ρ)
        (conv↓-nonvar-pre-zero body endpoint-nonvar
          endpoint-zero-pre))
      (rename-occurs (extᵗ ρ) (ext-injective injective)
        endpoint-zero-pre)
      (source-conceal-left-imprecision body (ext-injective injective) mark
        (shift-not-occurs fresh)
        (inst-renamed-representation represented)
        (subst (λ T → I.instᵐ _ I.⊢ T ⊑ _)
          source-eq prem))
    where
    endpoint-nonvar = unrename-nonvar
      (subst NonVar source-eq nonvar)
    endpoint-zero-post = unrename-occurs (extᵗ ρ)
      (ext-injective injective)
      (subst (Fin.zero ∈ᵗ_) source-eq zero-occurs)
    endpoint-zero-pre = conv↓-zero-post body endpoint-zero-post
  source-conceal-universal-imprecision body injective source-eq mark
      ∉-star represented I.∀★⊑★ =
    wrap-universal-star
      (source-conceal-left-imprecision body (ext-injective injective)
        mark ∉-star (lift-renamed-representation represented)
        (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ★)
          source-eq I.★⊑★))
  source-conceal-universal-imprecision
      body injective source-eq mark ∉-star represented
      (I.∀⊑★ nonstar prem) =
    wrap-universal-star
      (source-conceal-left-imprecision body (ext-injective injective)
        mark ∉-star (lift-renamed-representation represented)
        (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ★) source-eq prem))
  source-conceal-universal-imprecision
      body injective source-eq mark (∉-all fresh) represented I.bot-elim =
    subst (λ T → _ I.⊢ `∀ T ⊑ `∀ ★)
      (sym (imprecision-to-fresh output-prem)) I.bot-elim
    where
    output-prem = source-conceal-left-imprecision body
      (ext-injective injective) mark (∉-var fin-suc≢zero)
      (lift-renamed-representation represented)
      (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ＇ Fin.zero)
        source-eq I.X⊑X)
  source-conceal-universal-imprecision
      body injective source-eq mark ∉-star represented I.bot⊑★ =
    subst (λ T → _ I.⊢ `∀ T ⊑ ★)
      (sym (imprecision-to-fresh output-prem)) I.bot⊑★
    where
    output-prem = source-conceal-left-imprecision body
      (ext-injective injective) mark (∉-var fin-suc≢zero)
      (lift-renamed-representation represented)
      (subst (λ T → I.extᵐ _ I.⊢ T ⊑ ＇ Fin.zero)
        source-eq I.X⊑X)


source-conceal-input-imprecisionᵀ : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {Xᴸ : TyVar (CT.Δᵉ Γᴸ)}
    {Rᴸ A A′ : Ty (CT.Δᵉ Γᴸ)} {B : Ty (CT.Δᵉ Γᴿ)}
    {c : Conv.Conv↓ (CT.Δᵉ Γᴸ) A A′}
  → CT.Σᵉ Γᴸ Conv.⊢↓[ Xᴸ ⦂ Rᴸ ] c
  → marksᶜ γ (toRenameⁱ (ηᴸᶜ γ) Xᴸ) ≡ I.X⊑★
  → (∀ Xᴿ → toRenameⁱ (ηᴿᶜ γ) Xᴿ
      ≢ toRenameⁱ (ηᴸᶜ γ) Xᴸ)
  → Rᴸ ⊑ᵀ⟨ γ ⟩ ★
  → A′ ⊑ᵀ⟨ γ ⟩ B
  → A ⊑ᵀ⟨ γ ⟩ B
source-conceal-input-imprecisionᵀ {γ = γ} c⊢ mark no-target
    represented q =
  source-conceal-left-imprecision c⊢
    (toRenameⁱ-injective (ηᴸᶜ γ)) mark
    (renamed-type-absent-from-disaligned no-target) represented q
