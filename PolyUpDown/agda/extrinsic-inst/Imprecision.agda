module Imprecision where

-- File Charter:
--   * Store-free type imprecision for extrinsic-inst PolyUpDown.
--   * Defines unindexed imprecision evidence over `Ty` (and dual direction).
--   * This relation is intended to align with `Cast` (not full `UpDown`
--   * cast typing).
--   * FIXME: the concrete-seal rule below is too permissive. It should require
--     the same seal on both sides, as `Cast.⊑ᶜ-seal` and
--     `ImprecisionIndexed.⊑ᵢ-｀` now do.

open import Types
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z<s; s<s; s≤s; s≤s⁻¹)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-suc; +-mono-≤; m≤m+n; m≤n+m; n≤1+n)
open import TypeProperties
  using (renameˢ-ground; substᵗ-ground; renameˢ-ext-⇑ˢ; renameˢ-ν-src;
         substᵗ-⇑ˢ; substᵗ-ν-src; substᵗ-id; liftSubstˢ; substᵗ-cong; substˢᵗ-cong;
         renameˢ-preserves-WfTy; substᵗ-preserves-WfTy; SealRenameWf-suc)

------------------------------------------------------------------------
-- Type imprecision
------------------------------------------------------------------------

infix 4 _⊑_ _⊒_

data _⊑_ : Ty → Ty → Set where
  ⊑-★★ : ★ ⊑ ★
  ⊑-★ : (A G : Ty) → Ground G → A ⊑ G → A ⊑ ★
  ⊑-＇ : (X : TyVar) → ＇ X ⊑ ＇ X
  ⊑-｀ : (αˡ αʳ : Seal) → ｀ αˡ ⊑ ｀ αʳ
  ⊑-‵ : (ι : Base) → ‵ ι ⊑ ‵ ι
  ⊑-⇒ : (A A′ B B′ : Ty)
    → A ⊑ A′
    → B ⊑ B′
    → (A ⇒ B) ⊑ (A′ ⇒ B′)
  ⊑-∀ : (A B : Ty)
    → A ⊑ B
    → (`∀ A) ⊑ (`∀ B)
  ⊑-ν : (A B : Ty)
    → ((⇑ˢ A) [ α₀ ]ᵗ) ⊑ ⇑ˢ B
    → (`∀ A) ⊑ B

_⊒_ : Ty → Ty → Set
B ⊒ A = A ⊑ B

⊑-refl : ∀ {A} → A ⊑ A
⊑-refl {＇ X} = ⊑-＇ X
⊑-refl {｀ α} = ⊑-｀ α α
⊑-refl {‵ ι} = ⊑-‵ ι
⊑-refl {★} = ⊑-★★
⊑-refl {A ⇒ B} = ⊑-⇒ A A B B ⊑-refl ⊑-refl
⊑-refl {`∀ A} = ⊑-∀ A A ⊑-refl

⊒-refl : ∀ {A} → A ⊒ A
⊒-refl = ⊑-refl 

cast-⊑ :
  ∀ {A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  A ⊑ B →
  A′ ⊑ B′
cast-⊑ refl refl p = p

substᵗ-id-on-wf :
  ∀ {Δ Ψ T} {σ : Substᵗ} →
  (∀ {X} → X < Δ → σ X ≡ ＇ X) →
  WfTy Δ Ψ T →
  substᵗ σ T ≡ T
substᵗ-id-on-wf hσ (wfVar X<Δ) = hσ X<Δ
substᵗ-id-on-wf hσ (wfSeal α<Ψ) = refl
substᵗ-id-on-wf hσ wfBase = refl
substᵗ-id-on-wf hσ wf★ = refl
substᵗ-id-on-wf hσ (wf⇒ hA hB) =
  cong₂ _⇒_ (substᵗ-id-on-wf hσ hA) (substᵗ-id-on-wf hσ hB)
substᵗ-id-on-wf {Δ = Δ} {σ = σ} hσ (wf∀ hA) =
  cong `∀ (substᵗ-id-on-wf hσ-ext hA)
  where
    hσ-ext : ∀ {X} → X < suc Δ → extsᵗ σ X ≡ ＇ X
    hσ-ext {zero} z<s = refl
    hσ-ext {suc X} (s<s X<Δ) = cong (renameᵗ suc) (hσ X<Δ)

substᵗ-closed-id : ∀ {Ψ T} → WfTy 0 Ψ T → (σ : Substᵗ) → substᵗ σ T ≡ T
substᵗ-closed-id hT σ = substᵗ-id-on-wf (λ ()) hT

renameᵗ-id-on-wf :
  ∀ {Δ Ψ T} {ρ : Renameᵗ} →
  (∀ {X} → X < Δ → ρ X ≡ X) →
  WfTy Δ Ψ T →
  renameᵗ ρ T ≡ T
renameᵗ-id-on-wf hρ (wfVar X<Δ) = cong ＇_ (hρ X<Δ)
renameᵗ-id-on-wf hρ (wfSeal α<Ψ) = refl
renameᵗ-id-on-wf hρ wfBase = refl
renameᵗ-id-on-wf hρ wf★ = refl
renameᵗ-id-on-wf hρ (wf⇒ hA hB) =
  cong₂ _⇒_ (renameᵗ-id-on-wf hρ hA) (renameᵗ-id-on-wf hρ hB)
renameᵗ-id-on-wf {Δ = Δ} {ρ = ρ} hρ (wf∀ hA) =
  cong `∀ (renameᵗ-id-on-wf hρ-ext hA)
  where
    hρ-ext : ∀ {X} → X < suc Δ → extᵗ ρ X ≡ X
    hρ-ext {zero} z<s = refl
    hρ-ext {suc X} (s<s X<Δ) = cong suc (hρ X<Δ)

renameᵗ-closed-id : ∀ {Ψ T} → WfTy 0 Ψ T → renameᵗ suc T ≡ T
renameᵗ-closed-id hT = renameᵗ-id-on-wf (λ ()) hT

tySize : Ty → ℕ
tySize (＇ X) = suc zero
tySize (｀ α) = suc zero
tySize (‵ ι) = suc zero
tySize ★ = suc zero
tySize (A ⇒ B) = suc (tySize A + tySize B)
tySize (`∀ A) = suc (tySize A)

tySize-renameᵗ : ∀ ρ A → tySize (renameᵗ ρ A) ≡ tySize A
tySize-renameᵗ ρ (＇ X) = refl
tySize-renameᵗ ρ (｀ α) = refl
tySize-renameᵗ ρ (‵ ι) = refl
tySize-renameᵗ ρ ★ = refl
tySize-renameᵗ ρ (A ⇒ B) = cong₂ (λ a b → suc (a + b)) (tySize-renameᵗ ρ A) (tySize-renameᵗ ρ B)
tySize-renameᵗ ρ (`∀ A) = cong suc (tySize-renameᵗ (extᵗ ρ) A)

tySize-renameˢ : ∀ ρ A → tySize (renameˢ ρ A) ≡ tySize A
tySize-renameˢ ρ (＇ X) = refl
tySize-renameˢ ρ (｀ α) = refl
tySize-renameˢ ρ (‵ ι) = refl
tySize-renameˢ ρ ★ = refl
tySize-renameˢ ρ (A ⇒ B) = cong₂ (λ a b → suc (a + b)) (tySize-renameˢ ρ A) (tySize-renameˢ ρ B)
tySize-renameˢ ρ (`∀ A) = cong suc (tySize-renameˢ ρ A)

tySize-substᵗ-unit : ∀ σ → (∀ X → tySize (σ X) ≡ suc zero) → ∀ A → tySize (substᵗ σ A) ≡ tySize A
tySize-substᵗ-unit σ hσ (＇ X) = hσ X
tySize-substᵗ-unit σ hσ (｀ α) = refl
tySize-substᵗ-unit σ hσ (‵ ι) = refl
tySize-substᵗ-unit σ hσ ★ = refl
tySize-substᵗ-unit σ hσ (A ⇒ B) =
  cong₂ (λ a b → suc (a + b)) (tySize-substᵗ-unit σ hσ A) (tySize-substᵗ-unit σ hσ B)
tySize-substᵗ-unit σ hσ (`∀ A) = cong suc (tySize-substᵗ-unit (extsᵗ σ) hσ-ext A)
  where
    hσ-ext : ∀ X → tySize (extsᵗ σ X) ≡ suc zero
    hσ-ext zero = refl
    hσ-ext (suc X) = trans (tySize-renameᵗ suc (σ X)) (hσ X)

tySize-open-shift : ∀ A → tySize ((⇑ˢ A) [ α₀ ]ᵗ) ≡ tySize A
tySize-open-shift A =
  trans
    (tySize-substᵗ-unit (singleTyEnv α₀) hσ (renameˢ suc A))
    (tySize-renameˢ suc A)
  where
    hσ : ∀ X → tySize (singleTyEnv α₀ X) ≡ suc zero
    hσ zero = refl
    hσ (suc X) = refl

open-shift-preserves-WfTy :
  ∀ {Ψ A} →
  WfTy (suc zero) Ψ A →
  WfTy zero (suc Ψ) ((⇑ˢ A) [ α₀ ]ᵗ)
open-shift-preserves-WfTy hA =
  substᵗ-preserves-WfTy
    (renameˢ-preserves-WfTy hA SealRenameWf-suc)
    hσ
  where
    hσ : ∀ {X} → X < suc zero → WfTy zero (suc _) (singleTyEnv α₀ X)
    hσ {zero} z<s = wfSeal z<s
    hσ {suc X} (s<s ())

closed-⊑-★-fuel : ∀ n {Ψ T} → WfTy 0 Ψ T → tySize T ≤ n → T ⊑ ★
closed-⊑-★-fuel zero {T = ＇ X} (wfVar ())
closed-⊑-★-fuel zero {T = ｀ α} (wfSeal α<Ψ) ()
closed-⊑-★-fuel zero {T = ‵ ι} wfBase ()
closed-⊑-★-fuel zero {T = ★} wf★ ()
closed-⊑-★-fuel zero {T = A ⇒ B} (wf⇒ hA hB) ()
closed-⊑-★-fuel zero {T = `∀ A} (wf∀ hA) ()
closed-⊑-★-fuel (suc n) {T = ｀ α} (wfSeal α<Ψ) h =
  ⊑-★ (｀ α) (｀ α) (｀ α) (⊑-｀ α α)
closed-⊑-★-fuel (suc n) {T = ‵ ι} wfBase h =
  ⊑-★ (‵ ι) (‵ ι) (‵ ι) (⊑-‵ ι)
closed-⊑-★-fuel (suc n) {T = ★} wf★ h = ⊑-★★
closed-⊑-★-fuel (suc n) {T = A ⇒ B} (wf⇒ hA hB) h =
  ⊑-★ (A ⇒ B) (★ ⇒ ★) ★⇒★
    (⊑-⇒ A ★ B ★
      (closed-⊑-★-fuel n hA hA≤n)
      (closed-⊑-★-fuel n hB hB≤n))
  where
    hAB≤n : tySize A + tySize B ≤ n
    hAB≤n = s≤s⁻¹ h

    hA≤n : tySize A ≤ n
    hA≤n = ≤-trans (m≤m+n (tySize A) (tySize B)) hAB≤n

    hB≤n : tySize B ≤ n
    hB≤n = ≤-trans (m≤n+m (tySize B) (tySize A)) hAB≤n
closed-⊑-★-fuel (suc n) {T = `∀ A} (wf∀ hA) h =
  ⊑-ν A ★ (closed-⊑-★-fuel n (open-shift-preserves-WfTy hA) hA≤n)
  where
    hA≤n : tySize ((⇑ˢ A) [ α₀ ]ᵗ) ≤ n
    hA≤n = subst (λ m → m ≤ n) (sym (tySize-open-shift A)) (s≤s⁻¹ h)

closed-⊑-★ : ∀ {Ψ T} → WfTy 0 Ψ T → T ⊑ ★
closed-⊑-★ {T = T} hT = closed-⊑-★-fuel (tySize T) hT ≤-refl

------------------------------------------------------------------------
-- Seal substitution for imprecision
------------------------------------------------------------------------

mutual
  renameˢ-⊑ :
    (ρ : Renameˢ) →
    ∀ {A B} →
    A ⊑ B →
    renameˢ ρ A ⊑ renameˢ ρ B
  renameˢ-⊑ ρ ⊑-★★ = ⊑-★★
  renameˢ-⊑ ρ (⊑-★ A G g p) =
    ⊑-★ (renameˢ ρ A) (renameˢ ρ G) (renameˢ-ground ρ g) (renameˢ-⊑ ρ p)
  renameˢ-⊑ ρ (⊑-＇ X) = ⊑-＇ X
  renameˢ-⊑ ρ (⊑-｀ αˡ αʳ) = ⊑-｀ (ρ αˡ) (ρ αʳ)
  renameˢ-⊑ ρ (⊑-‵ ι) = ⊑-‵ ι
  renameˢ-⊑ ρ (⊑-⇒ A A′ B B′ p q) =
    ⊑-⇒ (renameˢ ρ A) (renameˢ ρ A′) (renameˢ ρ B) (renameˢ ρ B′)
      (renameˢ-⊑ ρ p) (renameˢ-⊑ ρ q)
  renameˢ-⊑ ρ (⊑-∀ A B p) =
    ⊑-∀ (renameˢ ρ A) (renameˢ ρ B) (renameˢ-⊑ ρ p)
  renameˢ-⊑ ρ (⊑-ν A B p) =
    ⊑-ν (renameˢ ρ A) (renameˢ ρ B)
      (cast-⊑
        (renameˢ-ν-src ρ A)
        (renameˢ-ext-⇑ˢ ρ B)
        (renameˢ-⊑ (extˢ ρ) p))

  substᵗ-⊑ :
    (σ : Substᵗ) →
    ∀ {A B} →
    A ⊑ B →
    substᵗ σ A ⊑ substᵗ σ B
  substᵗ-⊑ σ ⊑-★★ = ⊑-★★
  substᵗ-⊑ σ (⊑-★ A G g p) =
    ⊑-★ (substᵗ σ A) (substᵗ σ G) (substᵗ-ground σ g) (substᵗ-⊑ σ p)
  substᵗ-⊑ σ (⊑-＇ X) = ⊑-refl
  substᵗ-⊑ σ (⊑-｀ αˡ αʳ) = ⊑-｀ αˡ αʳ
  substᵗ-⊑ σ (⊑-‵ ι) = ⊑-‵ ι
  substᵗ-⊑ σ (⊑-⇒ A A′ B B′ p q) =
    ⊑-⇒ (substᵗ σ A) (substᵗ σ A′) (substᵗ σ B) (substᵗ σ B′)
      (substᵗ-⊑ σ p) (substᵗ-⊑ σ q)
  substᵗ-⊑ σ (⊑-∀ A B p) =
    ⊑-∀ (substᵗ (extsᵗ σ) A) (substᵗ (extsᵗ σ) B) (substᵗ-⊑ (extsᵗ σ) p)
  substᵗ-⊑ σ (⊑-ν A B p) =
    ⊑-ν (substᵗ (extsᵗ σ) A) (substᵗ σ B)
      (cast-⊑
        (substᵗ-ν-src σ A)
        (substᵗ-⇑ˢ σ B)
        (substᵗ-⊑ (liftSubstˢ σ) p))

------------------------------------------------------------------------
-- Proof of transitivity
------------------------------------------------------------------------

size⊑ : ∀ {A B} → A ⊑ B → ℕ
size⊑ ⊑-★★ = zero
size⊑ (⊑-★ A G g p) = suc (size⊑ p)
size⊑ (⊑-＇ X) = zero
size⊑ (⊑-｀ αˡ αʳ) = zero
size⊑ (⊑-‵ ι) = zero
size⊑ (⊑-⇒ A A′ B B′ p q) = suc (size⊑ p + size⊑ q)
size⊑ (⊑-∀ A B p) = suc (size⊑ p)
size⊑ (⊑-ν A B p) = suc (size⊑ p)

size-cast-⊑ :
  ∀ {A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (p : A ⊑ B) →
  size⊑ (cast-⊑ eqA eqB p) ≡ size⊑ p
size-cast-⊑ refl refl p = refl

size-renameˢ-⊑ :
  (ρ : Renameˢ) →
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (renameˢ-⊑ ρ p) ≡ size⊑ p
size-renameˢ-⊑ ρ ⊑-★★ = refl
size-renameˢ-⊑ ρ (⊑-★ A G g p) = cong suc (size-renameˢ-⊑ ρ p)
size-renameˢ-⊑ ρ (⊑-＇ X) = refl
size-renameˢ-⊑ ρ (⊑-｀ αˡ αʳ) = refl
size-renameˢ-⊑ ρ (⊑-‵ ι) = refl
size-renameˢ-⊑ ρ (⊑-⇒ A A′ B B′ p q) =
  cong suc (cong₂ _+_ (size-renameˢ-⊑ ρ p) (size-renameˢ-⊑ ρ q))
size-renameˢ-⊑ ρ (⊑-∀ A B p) = cong suc (size-renameˢ-⊑ ρ p)
size-renameˢ-⊑ ρ (⊑-ν A B p) =
  cong
    suc
    (trans
      (size-cast-⊑
        (renameˢ-ν-src ρ A)
        (renameˢ-ext-⇑ˢ ρ B)
        (renameˢ-⊑ (extˢ ρ) p))
      (size-renameˢ-⊑ (extˢ ρ) p))

data LeafTy : Ty → Set where
  leaf-＇ : ∀ {X} → LeafTy (＇ X)
  leaf-｀ : ∀ {α} → LeafTy (｀ α)
  leaf-‵ : ∀ {ι} → LeafTy (‵ ι)
  leaf-★ : LeafTy ★

LeafSubst : Substᵗ → Set
LeafSubst σ = ∀ X → LeafTy (σ X)

leaf-renameᵗ :
  (ρ : Renameᵗ) →
  ∀ {A} →
  LeafTy A →
  LeafTy (renameᵗ ρ A)
leaf-renameᵗ ρ leaf-＇ = leaf-＇
leaf-renameᵗ ρ leaf-｀ = leaf-｀
leaf-renameᵗ ρ leaf-‵ = leaf-‵
leaf-renameᵗ ρ leaf-★ = leaf-★

leaf-renameˢ :
  (ρ : Renameˢ) →
  ∀ {A} →
  LeafTy A →
  LeafTy (renameˢ ρ A)
leaf-renameˢ ρ leaf-＇ = leaf-＇
leaf-renameˢ ρ leaf-｀ = leaf-｀
leaf-renameˢ ρ leaf-‵ = leaf-‵
leaf-renameˢ ρ leaf-★ = leaf-★

extsᵗ-leaf :
  ∀ {σ} →
  LeafSubst σ →
  LeafSubst (extsᵗ σ)
extsᵗ-leaf leafσ zero = leaf-＇
extsᵗ-leaf leafσ (suc X) = leaf-renameᵗ suc (leafσ X)

liftSubstˢ-leaf :
  ∀ {σ} →
  LeafSubst σ →
  LeafSubst (liftSubstˢ σ)
liftSubstˢ-leaf leafσ X = leaf-renameˢ suc (leafσ X)

size-⊑-refl-leaf :
  ∀ {A} →
  LeafTy A →
  size⊑ (⊑-refl {A = A}) ≡ zero
size-⊑-refl-leaf leaf-＇ = refl
size-⊑-refl-leaf leaf-｀ = refl
size-⊑-refl-leaf leaf-‵ = refl
size-⊑-refl-leaf leaf-★ = refl

size-substᵗ-⊑-leaf :
  (σ : Substᵗ) →
  LeafSubst σ →
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (substᵗ-⊑ σ p) ≡ size⊑ p
size-substᵗ-⊑-leaf σ leafσ ⊑-★★ = refl
size-substᵗ-⊑-leaf σ leafσ (⊑-★ A G g p) =
  cong suc (size-substᵗ-⊑-leaf σ leafσ p)
size-substᵗ-⊑-leaf σ leafσ {A = ＇ X} (⊑-＇ X) =
  size-⊑-refl-leaf (leafσ X)
size-substᵗ-⊑-leaf σ leafσ (⊑-｀ αˡ αʳ) = refl
size-substᵗ-⊑-leaf σ leafσ (⊑-‵ ι) = refl
size-substᵗ-⊑-leaf σ leafσ (⊑-⇒ A A′ B B′ p q) =
  cong suc
    (cong₂
      _+_
      (size-substᵗ-⊑-leaf σ leafσ p)
      (size-substᵗ-⊑-leaf σ leafσ q))
size-substᵗ-⊑-leaf σ leafσ (⊑-∀ A B p) =
  cong suc (size-substᵗ-⊑-leaf (extsᵗ σ) (extsᵗ-leaf leafσ) p)
size-substᵗ-⊑-leaf σ leafσ (⊑-ν A B p) =
  cong
    suc
    (trans
      (size-cast-⊑
        (substᵗ-ν-src σ A)
        (substᵗ-⇑ˢ σ B)
        (substᵗ-⊑ (liftSubstˢ σ) p))
      (size-substᵗ-⊑-leaf (liftSubstˢ σ) (liftSubstˢ-leaf leafσ) p))

leaf-singleTyEnv-α₀ : LeafSubst (singleTyEnv α₀)
leaf-singleTyEnv-α₀ zero = leaf-｀
leaf-singleTyEnv-α₀ (suc X) = leaf-＇

shift-⊑ :
  ∀ {A B} →
  A ⊑ B →
  ⇑ˢ A ⊑ ⇑ˢ B
shift-⊑ = renameˢ-⊑ suc

size-shift-⊑ :
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (shift-⊑ p) ≡ size⊑ p
size-shift-⊑ p = size-renameˢ-⊑ suc p

open-shift-⊑ :
  ∀ {A B} →
  A ⊑ B →
  ((⇑ˢ A) [ α₀ ]ᵗ) ⊑ ((⇑ˢ B) [ α₀ ]ᵗ)
open-shift-⊑ p = substᵗ-⊑ (singleTyEnv α₀) (shift-⊑ p)

size-open-shift-⊑ :
  ∀ {A B} →
  (p : A ⊑ B) →
  size⊑ (open-shift-⊑ p) ≡ size⊑ p
size-open-shift-⊑ p =
  trans
    (size-substᵗ-⊑-leaf
      (singleTyEnv α₀)
      leaf-singleTyEnv-α₀
      (shift-⊑ p))
    (size-shift-⊑ p)

step-≤ :
  ∀ {m n} →
  m ≤ n →
  suc m ≤ suc n
step-≤ = s≤s

pred-★-bound :
  ∀ {a b n} →
  a + suc b ≤ suc n →
  a + b ≤ n
pred-★-bound {a} {b} {n} h =
  s≤s⁻¹
    (subst
      (λ x → x ≤ suc n)
      (+-suc a b)
      h)

left-rec-⇒-bound :
  ∀ {a b c d n} →
  suc (a + b) + suc (c + d) ≤ suc n →
  a + c ≤ n
left-rec-⇒-bound {a} {b} {c} {d} h =
  ≤-trans
    (≤-trans
      (+-mono-≤ (m≤m+n a b) (m≤m+n c d))
      (subst
        (λ x → a + b + (c + d) ≤ x)
        (sym (+-suc (a + b) (c + d)))
        (n≤1+n (a + b + (c + d)))))
    (s≤s⁻¹ h)

right-rec-⇒-bound :
  ∀ {a b c d n} →
  suc (a + b) + suc (c + d) ≤ suc n →
  b + d ≤ n
right-rec-⇒-bound {a} {b} {c} {d} h =
  ≤-trans
    (≤-trans
      (+-mono-≤ (m≤n+m b a) (m≤n+m d c))
      (subst
        (λ x → (a + b) + (c + d) ≤ x)
        (sym (+-suc (a + b) (c + d)))
        (n≤1+n ((a + b) + (c + d)))))
    (s≤s⁻¹ h)

ν-rec-bound :
  ∀ {a b n} →
  suc a + b ≤ suc n →
  a + b ≤ n
ν-rec-bound h = s≤s⁻¹ h

∀ν-rec-bound :
  ∀ {a b n} →
  suc a + suc b ≤ suc n →
  a + b ≤ n
∀ν-rec-bound {a} {b} {n} h =
  ≤-trans
    (≤-trans
      (n≤1+n (a + b))
      (subst
        (λ x → suc (a + b) ≤ x)
        (sym (+-suc a b))
        ≤-refl))
    (s≤s⁻¹ h)

⊑-trans-fuel :
  ∀ {n A B C} →
  (p : A ⊑ B) →
  (q : B ⊑ C) →
  size⊑ p + size⊑ q ≤ n →
  A ⊑ C
⊑-trans-fuel {n = zero} p ⊑-★★ h = p
⊑-trans-fuel {n = zero} ⊑-★★ (⊑-★ A G g q) ()
⊑-trans-fuel {n = zero} (⊑-★ A G g p) (⊑-★ A₁ G₁ g₁ q) ()
⊑-trans-fuel {n = zero} (⊑-＇ X) (⊑-★ A G g q) ()
⊑-trans-fuel {n = zero} (⊑-｀ αˡ αʳ) (⊑-★ A G g q) ()
⊑-trans-fuel {n = zero} (⊑-‵ ι) (⊑-★ A G g q) ()
⊑-trans-fuel {n = zero} (⊑-⇒ A A′ B B′ p₁ p₂) (⊑-★ A₁ G g q) ()
⊑-trans-fuel {n = zero} (⊑-∀ A B p) (⊑-★ A₁ G g q) ()
⊑-trans-fuel {n = zero} (⊑-ν A B p) (⊑-★ A₁ G g q) ()
⊑-trans-fuel {n = zero} p (⊑-＇ X) h = p
⊑-trans-fuel {n = zero} (⊑-｀ α αˡ) (⊑-｀ αˡ αʳ) h = ⊑-｀ α αʳ
⊑-trans-fuel {n = zero} p (⊑-‵ ι) h = p
⊑-trans-fuel {n = zero} (⊑-⇒ A A′ B B′ p₁ p₂) (⊑-⇒ A₁ A″ B₁ B″ q₁ q₂) ()
⊑-trans-fuel {n = zero} (⊑-∀ A B p) (⊑-∀ A₁ B₁ q) ()
⊑-trans-fuel {n = zero} (⊑-∀ A B p) (⊑-ν A₁ B₁ q) ()
⊑-trans-fuel {n = zero} (⊑-ν A B p) q ()
⊑-trans-fuel {n = suc n} p ⊑-★★ h = p
⊑-trans-fuel {n = suc n} p (⊑-★ B G g q) h =
  ⊑-★ _ G g (⊑-trans-fuel p q (pred-★-bound h))
⊑-trans-fuel {n = suc n} p (⊑-＇ X) h = p
⊑-trans-fuel {n = suc n} (⊑-｀ α αˡ) (⊑-｀ αˡ αʳ) h = ⊑-｀ α αʳ
⊑-trans-fuel {n = suc n} p (⊑-‵ ι) h = p
⊑-trans-fuel {n = suc n} (⊑-⇒ A A′ B B′ p₁ p₂) (⊑-⇒ A₁ A″ B₁ B″ q₁ q₂) h =
  ⊑-⇒ A A″ B B″
    (⊑-trans-fuel
      p₁
      q₁
      (left-rec-⇒-bound
        {a = size⊑ p₁} {b = size⊑ p₂}
        {c = size⊑ q₁} {d = size⊑ q₂}
        h))
    (⊑-trans-fuel
      p₂
      q₂
      (right-rec-⇒-bound
        {a = size⊑ p₁} {b = size⊑ p₂}
        {c = size⊑ q₁} {d = size⊑ q₂}
        h))
⊑-trans-fuel {n = suc n} (⊑-ν A B p) q h =
  ⊑-ν A _
    (⊑-trans-fuel
      p
      (shift-⊑ q)
      (subst
        (λ x → size⊑ p + x ≤ n)
        (sym (size-shift-⊑ q))
        (ν-rec-bound {a = size⊑ p} {b = size⊑ q} h)))
⊑-trans-fuel {n = suc n} (⊑-∀ A B p) (⊑-∀ B₁ C q) h =
  ⊑-∀ A C
    (⊑-trans-fuel
      p
      q
      (∀ν-rec-bound {a = size⊑ p} {b = size⊑ q} h))
⊑-trans-fuel {n = suc n} (⊑-∀ A B p) (⊑-ν B₁ C q) h =
  ⊑-ν A C
    (⊑-trans-fuel
      (open-shift-⊑ p)
      q
      (subst
        (λ x → x + size⊑ q ≤ n)
        (sym (size-open-shift-⊑ p))
        (∀ν-rec-bound {a = size⊑ p} {b = size⊑ q} h)))

⊑-trans : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
⊑-trans p q = ⊑-trans-fuel p q ≤-refl

⊒-trans : ∀ {A B C} → A ⊒ B → B ⊒ C → A ⊒ C
⊒-trans p q = ⊑-trans q p

singleSealTyEnv-ext-closed : ∀ {Ψ T} → WfTy 0 Ψ T → ∀ α → extsˢᵗ (singleSealTyEnv T) α ≡ singleSealTyEnv T α
singleSealTyEnv-ext-closed hT zero = renameᵗ-closed-id hT
singleSealTyEnv-ext-closed hT (suc α) = refl

substˢᵗ-single-renameᵗ :
  ∀ {Ψ T} →
  WfTy 0 Ψ T →
  ∀ ρ A →
  substˢᵗ (singleSealTyEnv T) (renameᵗ ρ A) ≡
  renameᵗ ρ (substˢᵗ (singleSealTyEnv T) A)
substˢᵗ-single-renameᵗ hT ρ (＇ X) = refl
substˢᵗ-single-renameᵗ {T = T} hT ρ (｀ zero) = sym (renameᵗ-id-on-wf (λ ()) hT)
substˢᵗ-single-renameᵗ hT ρ (｀ suc α) = refl
substˢᵗ-single-renameᵗ hT ρ (‵ ι) = refl
substˢᵗ-single-renameᵗ hT ρ ★ = refl
substˢᵗ-single-renameᵗ hT ρ (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-single-renameᵗ hT ρ A) (substˢᵗ-single-renameᵗ hT ρ B)
substˢᵗ-single-renameᵗ hT ρ (`∀ A) =
  cong `∀
    (trans
      (substˢᵗ-cong (singleSealTyEnv-ext-closed hT) (renameᵗ (extᵗ ρ) A))
      (trans
        (substˢᵗ-single-renameᵗ hT (extᵗ ρ) A)
        (cong (renameᵗ (extᵗ ρ)) (sym (substˢᵗ-cong (singleSealTyEnv-ext-closed hT) A)))))

substˢᵗ-single-substᵗ :
  ∀ {Ψ T} →
  WfTy 0 Ψ T →
  ∀ σ A →
  substˢᵗ (singleSealTyEnv T) (substᵗ σ A) ≡
  substᵗ (λ X → substˢᵗ (singleSealTyEnv T) (σ X)) (substˢᵗ (singleSealTyEnv T) A)
substˢᵗ-single-substᵗ {T = T} hT σ (＇ X) = refl
substˢᵗ-single-substᵗ {T = T} hT σ (｀ zero) = sym (substᵗ-closed-id hT _)
substˢᵗ-single-substᵗ {T = T} hT σ (｀ suc α) = refl
substˢᵗ-single-substᵗ {T = T} hT σ (‵ ι) = refl
substˢᵗ-single-substᵗ {T = T} hT σ ★ = refl
substˢᵗ-single-substᵗ {T = T} hT σ (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-single-substᵗ hT σ A) (substˢᵗ-single-substᵗ hT σ B)
substˢᵗ-single-substᵗ {T = T} hT σ (`∀ A) =
  cong `∀
    (trans
      (substˢᵗ-cong (singleSealTyEnv-ext-closed hT) (substᵗ (extsᵗ σ) A))
      (trans
        (substˢᵗ-single-substᵗ hT (extsᵗ σ) A)
        (trans
          (substᵗ-cong env (substˢᵗ (singleSealTyEnv T) A))
          (cong (substᵗ (extsᵗ (λ X → substˢᵗ (singleSealTyEnv T) (σ X))))
            (sym (substˢᵗ-cong (singleSealTyEnv-ext-closed hT) A))))))
  where
    env : ∀ X →
      substˢᵗ (singleSealTyEnv T) (extsᵗ σ X) ≡
      extsᵗ (λ Y → substˢᵗ (singleSealTyEnv T) (σ Y)) X
    env zero = refl
    env (suc X) = substˢᵗ-single-renameᵗ hT suc (σ X)

substˢᵗ-single-⇑ˢ-id : ∀ {Ψ T} → WfTy 0 Ψ T → ∀ A → substˢᵗ (singleSealTyEnv T) (⇑ˢ A) ≡ A
substˢᵗ-single-⇑ˢ-id hT (＇ X) = refl
substˢᵗ-single-⇑ˢ-id hT (｀ α) = refl
substˢᵗ-single-⇑ˢ-id hT (‵ ι) = refl
substˢᵗ-single-⇑ˢ-id hT ★ = refl
substˢᵗ-single-⇑ˢ-id hT (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-single-⇑ˢ-id hT A) (substˢᵗ-single-⇑ˢ-id hT B)
substˢᵗ-single-⇑ˢ-id hT (`∀ A) =
  cong `∀
    (trans
      (substˢᵗ-cong (singleSealTyEnv-ext-closed hT) (⇑ˢ A))
      (substˢᵗ-single-⇑ˢ-id hT A))

substˢᵗ-single-ν-src : ∀ {Ψ T} → WfTy 0 Ψ T → ∀ A →
  substˢᵗ (singleSealTyEnv T) ((⇑ˢ A) [ α₀ ]ᵗ) ≡ A [ T ]ᵗ
substˢᵗ-single-ν-src {T = T} hT A =
  trans
    (substˢᵗ-single-substᵗ hT (singleTyEnv α₀) (⇑ˢ A))
    (trans
      (substᵗ-cong env (substˢᵗ (singleSealTyEnv T) (⇑ˢ A)))
      (cong (substᵗ (singleTyEnv T)) (substˢᵗ-single-⇑ˢ-id hT A)))
  where
    env : ∀ X → substˢᵗ (singleSealTyEnv T) (singleTyEnv α₀ X) ≡ singleTyEnv T X
    env zero = refl
    env (suc X) = refl

ground-substˢ-WfTy :
  ∀ {Ψ T G} →
  WfTy 0 Ψ T →
  Ground G →
  Σ[ Ψ′ ∈ SealCtx ] WfTy 0 Ψ′ (substˢᵗ (singleSealTyEnv T) G)
ground-substˢ-WfTy {T = T} hT (｀ zero) = _ , hT
ground-substˢ-WfTy (hT) (｀ suc α) = suc α , wfSeal ≤-refl
ground-substˢ-WfTy hT (‵ ι) = zero , wfBase
ground-substˢ-WfTy hT ★⇒★ = zero , wf⇒ wf★ wf★

SealSubstClosed : Substˢᵗ → Set
SealSubstClosed τ = ∀ α → Σ[ Ψ ∈ SealCtx ] WfTy 0 Ψ (τ α)

extsˢᵗ-closed : ∀ {τ} → SealSubstClosed τ → ∀ α → extsˢᵗ τ α ≡ τ α
extsˢᵗ-closed hτ α = renameᵗ-closed-id (proj₂ (hτ α))

keepFreshˢ : Substˢᵗ → Substˢᵗ
keepFreshˢ τ zero = ｀ zero
keepFreshˢ τ (suc α) = renameˢ suc (τ α)

keepFreshˢ-closed : ∀ {τ} → SealSubstClosed τ → SealSubstClosed (keepFreshˢ τ)
keepFreshˢ-closed hτ zero = suc zero , wfSeal z<s
keepFreshˢ-closed hτ (suc α) =
  let Ψ , hA = hτ α in suc Ψ , renameˢ-preserves-WfTy hA SealRenameWf-suc

ground-substˢ-WfTy-gen :
  ∀ {τ G} →
  SealSubstClosed τ →
  Ground G →
  Σ[ Ψ ∈ SealCtx ] WfTy 0 Ψ (substˢᵗ τ G)
ground-substˢ-WfTy-gen hτ (｀ α) = hτ α
ground-substˢ-WfTy-gen hτ (‵ ι) = zero , wfBase
ground-substˢ-WfTy-gen hτ ★⇒★ = zero , wf⇒ wf★ wf★

substˢᵗ-renameᵗ-closed :
  ∀ {τ} →
  SealSubstClosed τ →
  ∀ ρ A →
  substˢᵗ τ (renameᵗ ρ A) ≡ renameᵗ ρ (substˢᵗ τ A)
substˢᵗ-renameᵗ-closed hτ ρ (＇ X) = refl
substˢᵗ-renameᵗ-closed hτ ρ (｀ α) = sym (renameᵗ-id-on-wf (λ ()) (proj₂ (hτ α)))
substˢᵗ-renameᵗ-closed hτ ρ (‵ ι) = refl
substˢᵗ-renameᵗ-closed hτ ρ ★ = refl
substˢᵗ-renameᵗ-closed hτ ρ (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-renameᵗ-closed hτ ρ A) (substˢᵗ-renameᵗ-closed hτ ρ B)
substˢᵗ-renameᵗ-closed hτ ρ (`∀ A) =
  cong `∀
    (trans
      (substˢᵗ-cong (extsˢᵗ-closed hτ) (renameᵗ (extᵗ ρ) A))
      (trans
        (substˢᵗ-renameᵗ-closed hτ (extᵗ ρ) A)
        (cong (renameᵗ (extᵗ ρ)) (sym (substˢᵗ-cong (extsˢᵗ-closed hτ) A)))))

substˢᵗ-substᵗ-closed :
  ∀ {τ} →
  SealSubstClosed τ →
  ∀ σ A →
  substˢᵗ τ (substᵗ σ A) ≡ substᵗ (λ X → substˢᵗ τ (σ X)) (substˢᵗ τ A)
substˢᵗ-substᵗ-closed hτ σ (＇ X) = refl
substˢᵗ-substᵗ-closed hτ σ (｀ α) = sym (substᵗ-closed-id (proj₂ (hτ α)) _)
substˢᵗ-substᵗ-closed hτ σ (‵ ι) = refl
substˢᵗ-substᵗ-closed hτ σ ★ = refl
substˢᵗ-substᵗ-closed hτ σ (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-substᵗ-closed hτ σ A) (substˢᵗ-substᵗ-closed hτ σ B)
substˢᵗ-substᵗ-closed {τ = τ} hτ σ (`∀ A) =
  cong `∀
    (trans
      (substˢᵗ-cong (extsˢᵗ-closed hτ) (substᵗ (extsᵗ σ) A))
      (trans
        (substˢᵗ-substᵗ-closed hτ (extsᵗ σ) A)
        (trans
          (substᵗ-cong env (substˢᵗ τ A))
          (cong (substᵗ (extsᵗ (λ X → substˢᵗ τ (σ X))))
            (sym (substˢᵗ-cong (extsˢᵗ-closed hτ) A))))))
  where
    env : ∀ X → substˢᵗ τ (extsᵗ σ X) ≡ extsᵗ (λ Y → substˢᵗ τ (σ Y)) X
    env zero = refl
    env (suc X) = substˢᵗ-renameᵗ-closed hτ suc (σ X)

substˢᵗ-keepFresh-⇑ˢ :
  ∀ {τ} →
  SealSubstClosed τ →
  ∀ A →
  substˢᵗ (keepFreshˢ τ) (⇑ˢ A) ≡ ⇑ˢ (substˢᵗ τ A)
substˢᵗ-keepFresh-⇑ˢ hτ (＇ X) = refl
substˢᵗ-keepFresh-⇑ˢ hτ (｀ α) = refl
substˢᵗ-keepFresh-⇑ˢ hτ (‵ ι) = refl
substˢᵗ-keepFresh-⇑ˢ hτ ★ = refl
substˢᵗ-keepFresh-⇑ˢ hτ (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-keepFresh-⇑ˢ hτ A) (substˢᵗ-keepFresh-⇑ˢ hτ B)
substˢᵗ-keepFresh-⇑ˢ hτ (`∀ A) =
  cong `∀
    (trans
      (substˢᵗ-cong (extsˢᵗ-closed (keepFreshˢ-closed hτ)) (renameˢ suc A))
      (trans
        (substˢᵗ-keepFresh-⇑ˢ hτ A)
        (cong (renameˢ suc) (sym (substˢᵗ-cong (extsˢᵗ-closed hτ) A)))))

substˢᵗ-keepFresh-ν-src :
  ∀ {τ} →
  SealSubstClosed τ →
  ∀ A →
  substˢᵗ (keepFreshˢ τ) ((⇑ˢ A) [ α₀ ]ᵗ) ≡ (⇑ˢ (substˢᵗ τ A)) [ α₀ ]ᵗ
substˢᵗ-keepFresh-ν-src hτ A =
  trans
    (substˢᵗ-substᵗ-closed (keepFreshˢ-closed hτ) (singleTyEnv α₀) (⇑ˢ A))
    (trans
      (substᵗ-cong env (substˢᵗ (keepFreshˢ τ) (⇑ˢ A)))
      (cong (substᵗ (singleTyEnv α₀)) (substˢᵗ-keepFresh-⇑ˢ hτ A)))
  where
    τ = _
    env : ∀ X → substˢᵗ (keepFreshˢ τ) (singleTyEnv α₀ X) ≡ singleTyEnv α₀ X
    env zero = refl
    env (suc X) = refl

postulate
  substˢ-⊑-closed-seal :
    ∀ {τ αˡ αʳ} →
    SealSubstClosed τ →
    substˢᵗ τ (｀ αˡ) ⊑ substˢᵗ τ (｀ αʳ)

substˢ-⊑-closed-gen :
  ∀ {τ A B} →
  SealSubstClosed τ →
  A ⊑ B →
  substˢᵗ τ A ⊑ substˢᵗ τ B
substˢ-⊑-closed-gen hτ ⊑-★★ = ⊑-★★
substˢ-⊑-closed-gen hτ (⊑-★ A G g p) =
  ⊑-trans (substˢ-⊑-closed-gen hτ p) (closed-⊑-★ (proj₂ (ground-substˢ-WfTy-gen hτ g)))
substˢ-⊑-closed-gen hτ (⊑-＇ X) = ⊑-＇ X
substˢ-⊑-closed-gen hτ (⊑-｀ αˡ αʳ) = substˢ-⊑-closed-seal hτ
substˢ-⊑-closed-gen hτ (⊑-‵ ι) = ⊑-‵ ι
substˢ-⊑-closed-gen {τ = τ} hτ (⊑-⇒ A A′ B B′ p q) =
  ⊑-⇒
    (substˢᵗ τ A)
    (substˢᵗ τ A′)
    (substˢᵗ τ B)
    (substˢᵗ τ B′)
    (substˢ-⊑-closed-gen hτ p)
    (substˢ-⊑-closed-gen hτ q)
substˢ-⊑-closed-gen {τ = τ} hτ (⊑-∀ A B p) =
  cast-⊑
    (cong `∀ (sym (substˢᵗ-cong (extsˢᵗ-closed hτ) A)))
    (cong `∀ (sym (substˢᵗ-cong (extsˢᵗ-closed hτ) B)))
    (⊑-∀ (substˢᵗ τ A) (substˢᵗ τ B) (substˢ-⊑-closed-gen hτ p))
substˢ-⊑-closed-gen {τ = τ} hτ (⊑-ν A B p) =
  cast-⊑
    (cong `∀ (sym (substˢᵗ-cong (extsˢᵗ-closed hτ) A)))
    refl
    (⊑-ν (substˢᵗ τ A) (substˢᵗ τ B)
      (cast-⊑
        (substˢᵗ-keepFresh-ν-src hτ A)
        (substˢᵗ-keepFresh-⇑ˢ hτ B)
        (substˢ-⊑-closed-gen (keepFreshˢ-closed hτ) p)))

substˢ-⊑-closed :
  ∀ {Ψ T A B} →
  WfTy 0 Ψ T →
  A ⊑ B →
  substˢᵗ (singleSealTyEnv T) A ⊑ substˢᵗ (singleSealTyEnv T) B
substˢ-⊑-closed hT p = substˢ-⊑-closed-gen (λ α → ground-substˢ-WfTy hT (｀ α)) p

------------------------------------------------------------------------
-- Dynamic-right inversion (Peter-style, flipped orientation)
------------------------------------------------------------------------

data DynRightInv (A : Ty) : Set where
  inv-★★ : A ≡ ★ → DynRightInv A
  inv-★ : ∀ {G} → Ground G → A ⊑ G → DynRightInv A
  inv-ν★ :
    ∀ {B} →
    A ⊑ `∀ B →
    ((⇑ˢ B) [ α₀ ]ᵗ) ⊑ ★ →
    DynRightInv A

dyn-right-inv : ∀ {A} → A ⊑ ★ → DynRightInv A
dyn-right-inv ⊑-★★ = inv-★★ refl
dyn-right-inv (⊑-★ A G g p) = inv-★ g p
dyn-right-inv (⊑-ν A B p) = inv-ν★ (⊑-∀ A A (⊑-refl {A = A})) p
