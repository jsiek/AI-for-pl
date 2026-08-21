module proof.DGG.TagTransport where

-- File Charter:
--   * Transports ground-tag imprecision obligations across universal-shaped
--     generator-indexed reveal and conceal conversions.
--   * Refutes base and variable obligations that cannot survive those
--     conversions.
--   * Uses binder-occurrence transport and lifted-store freshness to invert
--     the universal wrappers without changing the imprecision relation.
--   * Handles generated identity roots directly, including the bottom and
--     shifted-variable branches of transport to `∀ ★`.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore; store-lift; S-lift∋)
import Conversion as Conv
open import Conversion using (Conv↑; Conv↓)
open import Imprecision
open import proof.DGG.ConvImp using
  (occurs-absent-⊥; conv↑-zero-pre; conv↑-zero-post;
   conv↓-zero-pre; conv↓-zero-post)
open import proof.DGG.WorldDecay using (⊑-env-mono)
open import proof.ImprecisionConsistency using
  (rename-occurs; unrename-occurs; rename-not-occurs;
   source-occurs-target; ext-injective; zero-absent-shift)

------------------------------------------------------------------------
-- Environment and universal-body helpers
------------------------------------------------------------------------

⊑-extᵐ-instᵐ : ∀ {Δ} {μ : ImpEnv Δ} {A B : Ty (Nat.suc Δ)}
  → extᵐ μ ⊢ A ⊑ B
  → instᵐ μ ⊢ A ⊑ B
⊑-extᵐ-instᵐ p = ⊑-env-mono cond p
  where
  cond : ∀ Z → extᵐ _ Z ≡ X⊑★ → instᵐ _ Z ≡ X⊑★
  cond Fin.zero ()
  cond (Fin.suc Z) eq = eq

∀⊑★-body-no0 : ∀ {Δ} {μ : ImpEnv Δ} {A : Ty (Nat.suc Δ)}
  → μ ⊢ `∀ A ⊑ ★
  → Fin.zero ∉ᵗ A
  → extᵐ μ ⊢ A ⊑ ★
∀⊑★-body-no0 (∀⊑ Anv z∈A p) z∉A =
  ⊥-elim (occurs-absent-⊥ z∈A z∉A)
∀⊑★-body-no0 ∀★⊑★ z∉A = ★⊑★
∀⊑★-body-no0 (∀⊑★ Ans p) z∉A = p
∀⊑★-body-no0 bot⊑★ z∉A =
  ⊥-elim (occurs-absent-⊥ var-∈ z∉A)

------------------------------------------------------------------------
-- Reveal transport
------------------------------------------------------------------------

transport↑-∀-fun : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ} {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↑ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Z} → ρ′ Y ≡ ρ′ Z → Y ≡ Z)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ (★ ⇒ ★)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ (★ ⇒ ★)
transport↑-∀-fun
    (Conv.⊢↑-unseal (S-lift∋ ∋X refl)) inj′ inj
    (∀⊑★ Ans pb) (∀⊑ Anv z∈′ qb) =
  ⊥-elim
    (occurs-absent-⊥
      (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)
      (zero-absent-shift _))
transport↑-∀-fun
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ (⇒⊑⇒ qA qB)) =
  ∀⊑ nonvar-fun
    (rename-occurs (extᵗ _) (ext-injective inj′)
      (conv↑-zero-post (Conv.⊢↑-⇒ ⊢a ⊢b)
        (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
    (⇒⊑⇒ (⊑-extᵐ-instᵐ pA) (⊑-extᵐ-instᵐ pB))
transport↑-∀-fun
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ (⇒⊑⇒ qA qB)) =
  ∀⊑ nonvar-fun z∈p (⇒⊑⇒ pA pB)
transport↑-∀-fun
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb)
    with source-occurs-target refl pb
      (rename-occurs (extᵗ _) (ext-injective inj′)
        (conv↑-zero-post (Conv.⊢↑-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
transport↑-∀-fun
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb) | ()
transport↑-∀-fun
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  ∀⊑ nonvar-all z∈p
    (transport↑-∀-fun ⊢c₂ (ext-injective inj′)
      (ext-injective inj) pb qb)

transport↑-∀-all : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ} {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↑ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Z} → ρ′ Y ≡ ρ′ Z → Y ≡ Z)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ `∀ ★
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ `∀ ★
transport↑-∀-all
    (Conv.⊢↑-unseal (S-lift∋ ∋X refl)) inj′ inj
    (∀⊑★ Ans pb) q =
  ∀⊑∀ pb
transport↑-∀-all
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans pb) q =
  ∀⊑∀ pb
transport↑-∀-all
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p pb) (∀⊑∀ qb)
    with source-occurs-target refl qb
      (rename-occurs (extᵗ _) (ext-injective inj)
        (conv↑-zero-pre (Conv.⊢↑-⇒ ⊢a ⊢b)
          (unrename-occurs (extᵗ _) (ext-injective inj′) z∈p)))
transport↑-∀-all
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p pb) (∀⊑∀ qb) | ()
transport↑-∀-all
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p pb) (∀⊑ Anv z∈′ ())
transport↑-∀-all
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb) q =
  ∀⊑∀ pb
transport↑-∀-all
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑∀ qb)
    with source-occurs-target refl qb
      (rename-occurs (extᵗ _) (ext-injective inj)
        (conv↑-zero-pre (Conv.⊢↑-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj′) z∈p)))
transport↑-∀-all
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑∀ qb) | ()
transport↑-∀-all
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  ∀⊑ nonvar-all z∈p
    (transport↑-∀-all ⊢c₂ (ext-injective inj′)
      (ext-injective inj) pb qb)
transport↑-∀-all
    (Conv.⊢↑-id-var {Y = Y} X∈ X≢Y) inj′ inj p q with Y
transport↑-∀-all
    (Conv.⊢↑-id-var {Y = Y} X∈ X≢Y) inj′ inj p q
    | Fin.zero =
  bot-elim
transport↑-∀-all
    (Conv.⊢↑-id-var {Y = Y} X∈ X≢Y) inj′ inj p q
    | Fin.suc Y′ =
  ∀⊑∀
    (∀⊑★-body-no0 p (zero-absent-shift _))
transport↑-∀-all
    (Conv.⊢↑-id-base X∈) inj′ inj (∀⊑★ Ans pb) q =
  ∀⊑∀ pb
transport↑-∀-all
    (Conv.⊢↑-id-star X∈) inj′ inj ∀★⊑★ q =
  ∀⊑∀ ★⊑★

transport↑-∀-ι-⊥ : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ}
    {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↑ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc} {ι : Base}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Z} → ρ′ Y ≡ ρ′ Z → Y ≡ Z)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ ‵ ι
  → ⊥
transport↑-∀-ι-⊥
    (Conv.⊢↑-unseal (S-lift∋ ∋X refl)) inj′ inj
    (∀⊑★ Ans pb) (∀⊑ Anv z∈′ qb) =
  ⊥-elim
    (occurs-absent-⊥
      (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)
      (zero-absent-shift _))
transport↑-∀-ι-⊥
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans (⇒⊑★ pA pB)) (∀⊑ Anv z∈′ ())
transport↑-∀-ι-⊥
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ ())
transport↑-∀-ι-⊥
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb)
    with source-occurs-target refl pb
      (rename-occurs (extᵗ _) (ext-injective inj′)
        (conv↑-zero-post (Conv.⊢↑-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
transport↑-∀-ι-⊥
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb) | ()
transport↑-∀-ι-⊥
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  transport↑-∀-ι-⊥ ⊢c₂ (ext-injective inj′)
    (ext-injective inj) pb qb

transport↑-∀-var-⊥ : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ}
    {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↑ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc}
    {Z : TyVar Δc}
  → store-lift Σ Conv.⊢↑[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Y′} → ρ′ Y ≡ ρ′ Y′ → Y ≡ Y′)
  → (∀ {Y Y′} → ρ Y ≡ ρ Y′ → Y ≡ Y′)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ ＇ Z
  → ⊥
transport↑-∀-var-⊥
    (Conv.⊢↑-unseal (S-lift∋ ∋X refl)) inj′ inj
    (∀⊑★ Ans pb) (∀⊑ Anv z∈′ qb) =
  ⊥-elim
    (occurs-absent-⊥
      (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)
      (zero-absent-shift _))
transport↑-∀-var-⊥
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans (⇒⊑★ pA pB)) (∀⊑ Anv z∈′ ())
transport↑-∀-var-⊥
    (Conv.⊢↑-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ ())
transport↑-∀-var-⊥
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb)
    with source-occurs-target refl pb
      (rename-occurs (extᵗ _) (ext-injective inj′)
        (conv↑-zero-post (Conv.⊢↑-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
transport↑-∀-var-⊥
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb) | ()
transport↑-∀-var-⊥
    (Conv.⊢↑-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  transport↑-∀-var-⊥ ⊢c₂ (ext-injective inj′)
    (ext-injective inj) pb qb

------------------------------------------------------------------------
-- Conceal transport
------------------------------------------------------------------------

transport↓-∀-fun : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ} {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↓ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Z} → ρ′ Y ≡ ρ′ Z → Y ≡ Z)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ (★ ⇒ ★)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ (★ ⇒ ★)
transport↓-∀-fun
    (Conv.⊢↓-seal (S-lift∋ ∋X refl)) inj′ inj p₀
    (∀⊑ () z∈′ qb)
transport↓-∀-fun
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ (⇒⊑⇒ qA qB)) =
  ∀⊑ nonvar-fun
    (rename-occurs (extᵗ _) (ext-injective inj′)
      (conv↓-zero-post (Conv.⊢↓-⇒ ⊢a ⊢b)
        (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
    (⇒⊑⇒ (⊑-extᵐ-instᵐ pA) (⊑-extᵐ-instᵐ pB))
transport↓-∀-fun
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ (⇒⊑⇒ qA qB)) =
  ∀⊑ nonvar-fun z∈p (⇒⊑⇒ pA pB)
transport↓-∀-fun
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb)
    with source-occurs-target refl pb
      (rename-occurs (extᵗ _) (ext-injective inj′)
        (conv↓-zero-post (Conv.⊢↓-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
transport↓-∀-fun
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb) | ()
transport↓-∀-fun
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  ∀⊑ nonvar-all z∈p
    (transport↓-∀-fun ⊢c₂ (ext-injective inj′)
      (ext-injective inj) pb qb)

transport↓-∀-all : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ} {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↓ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Z} → ρ′ Y ≡ ρ′ Z → Y ≡ Z)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ `∀ ★
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ `∀ ★
transport↓-∀-all
    (Conv.⊢↓-seal (S-lift∋ ∋X refl)) inj′ inj p₀ (∀⊑∀ qb) =
  ∀⊑∀
    (∀⊑★-body-no0 p₀
      (rename-not-occurs (extᵗ _) (ext-injective inj′)
        (zero-absent-shift _)))
transport↓-∀-all
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans pb) q =
  ∀⊑∀ pb
transport↓-∀-all
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p pb) (∀⊑∀ qb)
    with source-occurs-target refl qb
      (rename-occurs (extᵗ _) (ext-injective inj)
        (conv↓-zero-pre (Conv.⊢↓-⇒ ⊢a ⊢b)
          (unrename-occurs (extᵗ _) (ext-injective inj′) z∈p)))
transport↓-∀-all
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p pb) (∀⊑∀ qb) | ()
transport↓-∀-all
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p pb) (∀⊑ Anv z∈′ ())
transport↓-∀-all
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb) q =
  ∀⊑∀ pb
transport↓-∀-all
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑∀ qb)
    with source-occurs-target refl qb
      (rename-occurs (extᵗ _) (ext-injective inj)
        (conv↓-zero-pre (Conv.⊢↓-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj′) z∈p)))
transport↓-∀-all
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑∀ qb) | ()
transport↓-∀-all
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  ∀⊑ nonvar-all z∈p
    (transport↓-∀-all ⊢c₂ (ext-injective inj′)
      (ext-injective inj) pb qb)
transport↓-∀-all
    (Conv.⊢↓-id-var {Y = Y} X∈ X≢Y) inj′ inj p q with Y
transport↓-∀-all
    (Conv.⊢↓-id-var {Y = Y} X∈ X≢Y) inj′ inj p q
    | Fin.zero =
  bot-elim
transport↓-∀-all
    (Conv.⊢↓-id-var {Y = Y} X∈ X≢Y) inj′ inj p q
    | Fin.suc Y′ =
  ∀⊑∀
    (∀⊑★-body-no0 p (zero-absent-shift _))
transport↓-∀-all
    (Conv.⊢↓-id-base X∈) inj′ inj (∀⊑★ Ans pb) q =
  ∀⊑∀ pb
transport↓-∀-all
    (Conv.⊢↓-id-star X∈) inj′ inj ∀★⊑★ q =
  ∀⊑∀ ★⊑★

transport↓-∀-ι-⊥ : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ}
    {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↓ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc} {ι : Base}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Z} → ρ′ Y ≡ ρ′ Z → Y ≡ Z)
  → (∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ ‵ ι
  → ⊥
transport↓-∀-ι-⊥
    (Conv.⊢↓-seal (S-lift∋ ∋X refl)) inj′ inj p₀
    (∀⊑ () z∈′ qb)
transport↓-∀-ι-⊥
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans (⇒⊑★ pA pB)) (∀⊑ Anv z∈′ ())
transport↓-∀-ι-⊥
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ ())
transport↓-∀-ι-⊥
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb)
    with source-occurs-target refl pb
      (rename-occurs (extᵗ _) (ext-injective inj′)
        (conv↓-zero-post (Conv.⊢↓-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
transport↓-∀-ι-⊥
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb) | ()
transport↓-∀-ι-⊥
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  transport↓-∀-ι-⊥ ⊢c₂ (ext-injective inj′)
    (ext-injective inj) pb qb

transport↓-∀-var-⊥ : ∀ {Δᴸ Δc} {Σ : TyStore Δᴸ}
    {X : TyVar Δᴸ}
    {R : Ty (Nat.suc Δᴸ)}
    {A₁ B₁ : Ty (Nat.suc Δᴸ)} {c₁ : Conv↓ (Nat.suc Δᴸ) A₁ B₁}
    {ρ′ ρ : Δᴸ ⇒ʳ Δc} {μ′ μ : ImpEnv Δc}
    {Z : TyVar Δc}
  → store-lift Σ Conv.⊢↓[ Fin.suc X ⦂ R ] c₁
  → (∀ {Y Y′} → ρ′ Y ≡ ρ′ Y′ → Y ≡ Y′)
  → (∀ {Y Y′} → ρ Y ≡ ρ Y′ → Y ≡ Y′)
  → μ′ ⊢ renameᵗ ρ′ (`∀ A₁) ⊑ ★
  → μ ⊢ renameᵗ ρ (`∀ B₁) ⊑ ＇ Z
  → ⊥
transport↓-∀-var-⊥
    (Conv.⊢↓-seal (S-lift∋ ∋X refl)) inj′ inj p₀
    (∀⊑ () z∈′ qb)
transport↓-∀-var-⊥
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑★ Ans (⇒⊑★ pA pB)) (∀⊑ Anv z∈′ ())
transport↓-∀-var-⊥
    (Conv.⊢↓-⇒ ⊢a ⊢b) inj′ inj
    (∀⊑ nonvar-fun z∈p (⇒⊑★ pA pB))
    (∀⊑ Anv z∈′ ())
transport↓-∀-var-⊥
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb)
    with source-occurs-target refl pb
      (rename-occurs (extᵗ _) (ext-injective inj′)
        (conv↓-zero-post (Conv.⊢↓-∀ repEq ⊢c₂)
          (unrename-occurs (extᵗ _) (ext-injective inj) z∈′)))
transport↓-∀-var-⊥
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj (∀⊑★ Ans pb)
    (∀⊑ Anv z∈′ qb) | ()
transport↓-∀-var-⊥
    (Conv.⊢↓-∀ repEq ⊢c₂) inj′ inj
    (∀⊑ nonvar-all z∈p pb) (∀⊑ Anv z∈′ qb) =
  transport↓-∀-var-⊥ ⊢c₂ (ext-injective inj′)
    (ext-injective inj) pb qb
