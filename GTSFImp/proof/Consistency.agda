module proof.Consistency where

-- File Charter:
--   * Proves that every closed type is consistent with the dynamic type.
--   * Derives the result from closed-type imprecision and the common-lower
--     characterization of consistency.
--   * Supplies consistency-side safety facts for polymorphic generated casts.
--   * Depends on proof.Imprecision and proof.ImprecisionConsistency.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

open import Types
open import Consistency
open import CastTerms using (GenSafe; safe-⇒; safe-∀; safe-inst; safe-gen)
open import proof.Imprecision using (imprecise-star)
open import proof.ImprecisionConsistency
  using (common-lower-consistent; refl⊑)

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
