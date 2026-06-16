-- File Charter:
--   * Definition of the GTSF type-consistency relation `~`.
--   * Introduce the judgment only; transport/proof lemmas live in
--     `ConsistencyProperties.agda`.
--   * No coercion synthesis here.

module Consistency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Fin.Subset using (Subset; Side; inside; outside; _∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec using ([]; _∷_; here; there)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; inspect; [_])
  renaming (subst to substEq)

open import Types
open import Label using (Label; push)
-- open import TypeSubst
-- open import TypePrecision

------------------------------------------------------------------------
-- Type Precision
------------------------------------------------------------------------

infix 5 _∣_⊢_~_

data has★ {Δ : TyCtx} {Ψ : Subset Δ} : Ty Δ → Set where

  has★-★ : has★ `★

  has★-⇒ˡ : ∀ {A B : Ty Δ} → has★ {Δ}{Ψ} A → has★ (A ⇒ B)

  has★-⇒ʳ : ∀ {A B : Ty Δ} → has★ {Δ}{Ψ} B → has★ (A ⇒ B)

  has*-∀  : ∀ {A : Ty (suc Δ)} → has★ {suc Δ}{outside ∷ Ψ} A → has★ (`∀ A)

has★-rename :
  ∀ {Δ Δ′}{Ψ : Subset Δ}{Ψ′ : Subset Δ′}
    (ρ : Renameᵗ Δ Δ′) {A : Ty Δ} →
  has★ {Δ}{Ψ} A →
  has★ {Δ′}{Ψ′} (renameᵗ ρ A)
has★-rename ρ has★-★ = has★-★
has★-rename ρ (has★-⇒ˡ A★) = has★-⇒ˡ (has★-rename ρ A★)
has★-rename ρ (has★-⇒ʳ B★) = has★-⇒ʳ (has★-rename ρ B★)
has★-rename ρ (has*-∀ A★) = has*-∀ (has★-rename (extᵗ ρ) A★)

has★-rename-inv :
  ∀ {Δ Δ′}{Ψ : Subset Δ}{Ψ′ : Subset Δ′}
    (ρ : Renameᵗ Δ Δ′) {A : Ty Δ} →
  has★ {Δ′}{Ψ′} (renameᵗ ρ A) →
  has★ {Δ}{Ψ} A
has★-rename-inv ρ {A = ＇ X} ()
has★-rename-inv ρ {A = ‵ ι} ()
has★-rename-inv ρ {A = `★} has★-★ = has★-★
has★-rename-inv ρ {A = A ⇒ B} (has★-⇒ˡ A★) =
  has★-⇒ˡ (has★-rename-inv ρ A★)
has★-rename-inv ρ {A = A ⇒ B} (has★-⇒ʳ B★) =
  has★-⇒ʳ (has★-rename-inv ρ B★)
has★-rename-inv ρ {A = `∀ A} (has*-∀ A★) =
  has*-∀ (has★-rename-inv (extᵗ ρ) A★)

has★-ctx : ∀ {Δ}{Ψ Ψ′ : Subset Δ}{A : Ty Δ} →
  has★ {Δ}{Ψ} A →
  has★ {Δ}{Ψ′} A
has★-ctx has★-★ = has★-★
has★-ctx (has★-⇒ˡ A★) = has★-⇒ˡ (has★-ctx A★)
has★-ctx (has★-⇒ʳ B★) = has★-⇒ʳ (has★-ctx B★)
has★-ctx (has*-∀ A★) = has*-∀ (has★-ctx A★)

has★-wkTy : ∀ {Δ}{Ψ : Subset Δ}{A : Ty Δ} →
  has★ {Δ}{Ψ} A →
  has★ {suc Δ}{inside ∷ Ψ} (wkTy A)
has★-wkTy = has★-rename Sᵗ

has★-subst :
  ∀ {Δ Δ′}{Ψ : Subset Δ}{Ψ′ : Subset Δ′}
    (σ : Substᵗ Δ Δ′) {A : Ty Δ} →
  has★ {Δ}{Ψ} A →
  has★ {Δ′}{Ψ′} (substᵗ σ A)
has★-subst σ has★-★ = has★-★
has★-subst σ (has★-⇒ˡ A★) = has★-⇒ˡ (has★-subst σ A★)
has★-subst σ (has★-⇒ʳ B★) = has★-⇒ʳ (has★-subst σ B★)
has★-subst σ (has*-∀ A★) = has*-∀ (has★-subst (extsᵗ σ) A★)

has★? : ∀ {Δ}{Ψ : Subset Δ} (A : Ty Δ) → Dec (has★ {Δ}{Ψ} A)
has★? (＇ X) = no λ ()
has★? (‵ ι) = no λ ()
has★? `★ = yes has★-★
has★? (A ⇒ B) with has★? A
has★? (A ⇒ B) | yes A★ = yes (has★-⇒ˡ A★)
has★? (A ⇒ B) | no A≁★ with has★? B
has★? (A ⇒ B) | no A≁★ | yes B★ = yes (has★-⇒ʳ B★)
has★? (A ⇒ B) | no A≁★ | no B≁★ =
  no λ { (has★-⇒ˡ A★) → A≁★ A★
       ; (has★-⇒ʳ B★) → B≁★ B★ }
has★? {Ψ = Ψ} (`∀ A) with has★? {Ψ = outside ∷ Ψ} A
has★? {Ψ = Ψ} (`∀ A) | yes A★ = yes (has*-∀ A★)
has★? {Ψ = Ψ} (`∀ A) | no A≁★ =
  no λ { (has*-∀ A★) → A≁★ A★ }

data _∣_⊢_~_ {Δ : TyCtx} (Ψ : Subset Δ) (ℓ : Label) :
    Ty Δ → Ty Δ → Set where

    X~X : ∀{X : TyVar Δ} → Ψ ∣ ℓ ⊢ ＇ X ~ ＇ X

    α~✯ : ∀{X : TyVar Δ}
      → tyVarToFin X ∈ Ψ
      → Ψ ∣ ℓ ⊢ ＇ X ~ `★

    ✯~α : ∀{X : TyVar Δ}
      → tyVarToFin X ∈ Ψ
      → Ψ ∣ ℓ ⊢ `★ ~ ＇ X

    ι~ι : ∀{ι : Base}
      → Ψ ∣ ℓ ⊢ ‵ ι ~ ‵ ι

    ★~★ : Ψ ∣ ℓ ⊢ `★ ~ `★

    ★~ι : ∀{ι : Base}
      → Ψ ∣ ℓ ⊢ `★ ~ ‵ ι

    ι~★ : ∀{ι : Base}
      → Ψ ∣ ℓ ⊢ ‵ ι ~ `★

    -- ★~G : ∀{G : Ty Δ}
    --   → Ground G
    --   → Ψ ∣ ℓ ⊢ `★ ~ G

    -- G~★ : ∀{G : Ty Δ}
    --   → Ground G
    --   → Ψ ∣ ℓ ⊢ G ~ `★

    ★~⇒ : ∀{A B : Ty Δ}
      → Ψ ∣ push zero ℓ ⊢ A ~ `★
      → Ψ ∣ push (suc zero) ℓ ⊢ `★ ~ B
      → Ψ ∣ ℓ ⊢ `★ ~ (A ⇒ B)

    ⇒~★ : ∀{A B : Ty Δ}
      → Ψ ∣ push zero ℓ ⊢ `★ ~ A
      → Ψ ∣ push (suc zero) ℓ ⊢ B ~ `★
      → Ψ ∣ ℓ ⊢ (A ⇒ B) ~ `★

    ⇒~⇒ : ∀{A A′ B B′ : Ty Δ}
      → Ψ ∣ push zero ℓ ⊢ A′ ~ A
      → Ψ ∣ push (suc zero) ℓ ⊢ B ~ B′
      → Ψ ∣ ℓ ⊢ (A ⇒ B) ~ (A′ ⇒ B′)

    ∀~∀ : ∀{A B : Ty (suc Δ)}
      → (outside ∷ Ψ) ∣ ℓ ⊢ A ~ B
      → Ψ ∣ ℓ ⊢ (`∀ A) ~ (`∀ B)

    ∀~ : ∀{A : Ty (suc Δ)}{B : Ty Δ}
      → has★ {suc Δ} {inside ∷ Ψ} (wkTy B)
      → (inside ∷ Ψ) ∣ ℓ ⊢ A ~ wkTy B
      → Ψ ∣ ℓ ⊢ (`∀ A) ~ B

    ~∀ : ∀{A : Ty Δ}{B : Ty (suc Δ)}
      → has★ {suc Δ} {inside ∷ Ψ} (wkTy A)
      → (inside ∷ Ψ) ∣ ℓ ⊢ wkTy A ~ B
      → Ψ ∣ ℓ ⊢ A ~ (`∀ B)

~-refl : ∀ {Δ}{Ψ}{ℓ} {A : Ty Δ} → Ψ ∣ ℓ ⊢ A ~ A
~-refl {A = ＇ X} = X~X
~-refl {A = ‵ x} = ι~ι
~-refl {A = `★} = ★~★
~-refl {A = A ⇒ B} = ⇒~⇒ ~-refl ~-refl
~-refl {A = `∀ A} = ∀~∀ ~-refl

~-sym : ∀ {Δ}{Ψ}{ℓ} {A B : Ty Δ} → Ψ ∣ ℓ ⊢ A ~ B →  Ψ ∣ ℓ ⊢ B ~ A
~-sym X~X = X~X
~-sym (α~✯ X∈Ψ) = ✯~α X∈Ψ
~-sym (✯~α X∈Ψ) = α~✯ X∈Ψ
~-sym ι~ι = ι~ι
~-sym ★~★ = ★~★
~-sym ★~ι = ι~★
~-sym ι~★ = ★~ι
~-sym (★~⇒ A~★ ★~B) = ⇒~★ (~-sym A~★) (~-sym ★~B)
~-sym (⇒~★ ★~A B~★) = ★~⇒ (~-sym ★~A) (~-sym B~★)
~-sym (⇒~⇒ A′~A B~B′) = ⇒~⇒ (~-sym A′~A) (~-sym B~B′)
~-sym (∀~∀ A~B) = ∀~∀ (~-sym A~B)
~-sym (∀~ B★ A~B) = ~∀ B★ (~-sym A~B)
~-sym (~∀ A★ A~B) = ∀~ A★ (~-sym A~B)

_≟TyVar_ : ∀ {Δ} (X Y : TyVar Δ) → Dec (X ≡ Y)
Zᵗ ≟TyVar Zᵗ = yes refl
Zᵗ ≟TyVar Sᵗ Y = no (λ ())
Sᵗ X ≟TyVar Zᵗ = no (λ ())
Sᵗ X ≟TyVar Sᵗ Y with X ≟TyVar Y
Sᵗ X ≟TyVar Sᵗ Y | yes refl = yes refl
Sᵗ X ≟TyVar Sᵗ Y | no X≢Y = no λ { refl → X≢Y refl }

{-# TERMINATING #-}
A~B? : ∀ {Δ}{Ψ}{ℓ} (A B : Ty Δ) → Dec (Ψ ∣ ℓ ⊢ A ~ B)
A~B? {Ψ = Ψ} (＇ X) (＇ Y) with X ≟TyVar Y
A~B? {Ψ = Ψ} (＇ X) (＇ Y) | yes refl = yes X~X
A~B? {Ψ = Ψ} (＇ X) (＇ Y) | no X≢Y =
  no λ { X~X → X≢Y refl }
A~B? (＇ X) (‵ ι) = no λ ()
A~B? {Ψ = Ψ} (＇ X) `★ with tyVarToFin X ∈? Ψ
A~B? {Ψ = Ψ} (＇ X) `★ | yes X∈Ψ = yes (α~✯ X∈Ψ)
A~B? {Ψ = Ψ} (＇ X) `★ | no X∉Ψ =
  no λ { (α~✯ X∈Ψ) → X∉Ψ X∈Ψ }
A~B? (＇ X) (B₁ ⇒ B₂) = no λ ()
A~B? (＇ X) (`∀ B) = no λ { (~∀ () _) }
A~B? (‵ ι) (＇ X) = no λ ()
A~B? (‵ ι) (‵ ι′) with ι ≟Base ι′
A~B? (‵ ι) (‵ ι′) | yes refl = yes ι~ι
A~B? (‵ ι) (‵ ι′) | no ι≢ι′ =
  no λ { ι~ι → ι≢ι′ refl }
A~B? (‵ ι) `★ = yes ι~★
A~B? (‵ ι) (B₁ ⇒ B₂) = no λ ()
A~B? (‵ ι) (`∀ B) = no λ { (~∀ () _) }
A~B? {Ψ = Ψ} `★ (＇ X) with tyVarToFin X ∈? Ψ
A~B? {Ψ = Ψ} `★ (＇ X) | yes X∈Ψ = yes (✯~α X∈Ψ)
A~B? {Ψ = Ψ} `★ (＇ X) | no X∉Ψ =
  no λ { (✯~α X∈Ψ) → X∉Ψ X∈Ψ }
A~B? `★ (‵ ι) = yes ★~ι
A~B? `★ `★ = yes ★~★
A~B? {Ψ = Ψ} {ℓ = ℓ} `★ (B₁ ⇒ B₂)
  with A~B? {Ψ = Ψ} {ℓ = push zero ℓ} B₁ `★
     | A~B? {Ψ = Ψ} {ℓ = push (suc zero) ℓ} `★ B₂
A~B? {Ψ = Ψ} {ℓ = ℓ} `★ (B₁ ⇒ B₂) | yes B₁~★ | yes ★~B₂ =
  yes (★~⇒ B₁~★ ★~B₂)
A~B? {Ψ = Ψ} {ℓ = ℓ} `★ (B₁ ⇒ B₂) | no B₁≁★ | _ =
  no λ { (★~⇒ B₁~★ _) → B₁≁★ B₁~★ }
A~B? {Ψ = Ψ} {ℓ = ℓ} `★ (B₁ ⇒ B₂) | yes _ | no ★≁B₂ =
  no λ { (★~⇒ _ ★~B₂) → ★≁B₂ ★~B₂ }
A~B? {Ψ = Ψ} `★ (`∀ B) with A~B? {Ψ = inside ∷ Ψ} (wkTy `★) B
A~B? {Ψ = Ψ} `★ (`∀ B) | yes ★~B = yes (~∀ has★-★ ★~B)
A~B? {Ψ = Ψ} `★ (`∀ B) | no ★≁B =
  no λ { (~∀ _ ★~B) → ★≁B ★~B }
A~B? (A₁ ⇒ A₂) (＇ X) = no λ ()
A~B? (A₁ ⇒ A₂) (‵ ι) = no λ ()
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) `★
  with A~B? {Ψ = Ψ} {ℓ = push zero ℓ} `★ A₁
     | A~B? {Ψ = Ψ} {ℓ = push (suc zero) ℓ} A₂ `★
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) `★ | yes ★~A₁ | yes A₂~★ =
  yes (⇒~★ ★~A₁ A₂~★)
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) `★ | no ★≁A₁ | _ =
  no λ { (⇒~★ ★~A₁ _) → ★≁A₁ ★~A₁ }
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) `★ | yes _ | no A₂≁★ =
  no λ { (⇒~★ _ A₂~★) → A₂≁★ A₂~★ }
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) (B₁ ⇒ B₂)
  with A~B? {Ψ = Ψ} {ℓ = push zero ℓ} B₁ A₁
     | A~B? {Ψ = Ψ} {ℓ = push (suc zero) ℓ} A₂ B₂
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) (B₁ ⇒ B₂) | yes B₁~A₁ | yes A₂~B₂ =
  yes (⇒~⇒ B₁~A₁ A₂~B₂)
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) (B₁ ⇒ B₂) | no B₁≁A₁ | _ =
  no λ { (⇒~⇒ B₁~A₁ _) → B₁≁A₁ B₁~A₁ }
A~B? {Ψ = Ψ} {ℓ = ℓ} (A₁ ⇒ A₂) (B₁ ⇒ B₂) | yes _ | no A₂≁B₂ =
  no λ { (⇒~⇒ _ A₂~B₂) → A₂≁B₂ A₂~B₂ }
A~B? {Ψ = Ψ} (A₁ ⇒ A₂) (`∀ B)
  with has★? {Ψ = inside ∷ Ψ} (wkTy (A₁ ⇒ A₂))
A~B? {Ψ = Ψ} (A₁ ⇒ A₂) (`∀ B) | yes A★
  with A~B? {Ψ = inside ∷ Ψ} (wkTy (A₁ ⇒ A₂)) B
A~B? {Ψ = Ψ} (A₁ ⇒ A₂) (`∀ B) | yes A★ | yes A~B =
  yes (~∀ A★ A~B)
A~B? {Ψ = Ψ} (A₁ ⇒ A₂) (`∀ B) | yes A★ | no A≁B =
  no λ { (~∀ _ A~B) → A≁B A~B }
A~B? {Ψ = Ψ} (A₁ ⇒ A₂) (`∀ B) | no A≁★ =
  no λ { (~∀ A★ _) → A≁★ A★ }
A~B? (`∀ A) (＇ X) = no λ { (∀~ () _) }
A~B? (`∀ A) (‵ ι) = no λ { (∀~ () _) }
A~B? {Ψ = Ψ} (`∀ A) `★ with A~B? {Ψ = inside ∷ Ψ} A (wkTy `★)
A~B? {Ψ = Ψ} (`∀ A) `★ | yes A~★ = yes (∀~ has★-★ A~★)
A~B? {Ψ = Ψ} (`∀ A) `★ | no A≁★ =
  no λ { (∀~ _ A~★) → A≁★ A~★ }
A~B? {Ψ = Ψ} (`∀ A) (B₁ ⇒ B₂)
  with has★? {Ψ = inside ∷ Ψ} (wkTy (B₁ ⇒ B₂))
A~B? {Ψ = Ψ} (`∀ A) (B₁ ⇒ B₂) | yes B★
  with A~B? {Ψ = inside ∷ Ψ} A (wkTy (B₁ ⇒ B₂))
A~B? {Ψ = Ψ} (`∀ A) (B₁ ⇒ B₂) | yes B★ | yes A~B =
  yes (∀~ B★ A~B)
A~B? {Ψ = Ψ} (`∀ A) (B₁ ⇒ B₂) | yes B★ | no A≁B =
  no λ { (∀~ _ A~B) → A≁B A~B }
A~B? {Ψ = Ψ} (`∀ A) (B₁ ⇒ B₂) | no B≁★ =
  no λ { (∀~ B★ _) → B≁★ B★ }
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) with A~B? {Ψ = outside ∷ Ψ} A B
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | yes A~B = yes (∀~∀ A~B)
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B
  with has★? {Ψ = inside ∷ Ψ} (wkTy (`∀ B))
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | yes B★
  with A~B? {Ψ = inside ∷ Ψ} A (wkTy (`∀ B))
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | yes B★ | yes A~∀B =
  yes (∀~ B★ A~∀B)
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | yes B★ | no A≁∀B
  with has★? {Ψ = inside ∷ Ψ} (wkTy (`∀ A))
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | yes B★ | no A≁∀B
  | yes A★
  with A~B? {Ψ = inside ∷ Ψ} (wkTy (`∀ A)) B
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | yes B★ | no A≁∀B
  | yes A★ | yes ∀A~B =
  yes (~∀ A★ ∀A~B)
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | yes B★ | no A≁∀B
  | yes A★ | no ∀A≁B =
  no λ
    { (∀~∀ A~B) → A≁B A~B
    ; (∀~ _ A~∀B) → A≁∀B A~∀B
    ; (~∀ _ ∀A~B) → ∀A≁B ∀A~B
    }
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | yes B★ | no A≁∀B
  | no A≁★ =
  no λ
    { (∀~∀ A~B) → A≁B A~B
    ; (∀~ _ A~∀B) → A≁∀B A~∀B
    ; (~∀ A★ _) → A≁★ A★
    }
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | no B≁★
  with has★? {Ψ = inside ∷ Ψ} (wkTy (`∀ A))
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | no B≁★ | yes A★
  with A~B? {Ψ = inside ∷ Ψ} (wkTy (`∀ A)) B
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | no B≁★ | yes A★
  | yes ∀A~B =
  yes (~∀ A★ ∀A~B)
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | no B≁★ | yes A★
  | no ∀A≁B =
  no λ
    { (∀~∀ A~B) → A≁B A~B
    ; (∀~ B★ _) → B≁★ B★
    ; (~∀ _ ∀A~B) → ∀A≁B ∀A~B
    }
A~B? {Ψ = Ψ} (`∀ A) (`∀ B) | no A≁B | no B≁★ | no A≁★ =
  no λ
    { (∀~∀ A~B) → A≁B A~B
    ; (∀~ B★ _) → B≁★ B★
    ; (~∀ A★ _) → A≁★ A★
    }

close★ : ∀ {Δ} → Ty (suc Δ) → Ty Δ
close★ A = A [ `★ ]ᵗ

has★-close★ :
  ∀ {Δ}{Ψ : Subset Δ}{A : Ty (suc Δ)} →
  has★ {suc Δ}{inside ∷ Ψ} A →
  has★ {Δ}{Ψ} (close★ A)
has★-close★ A★ = has★-subst (singleTyEnv `★) A★

close★-under-∀ : ∀ {Δ} → Ty (suc (suc Δ)) → Ty (suc Δ)
close★-under-∀ A = substᵗ (extsᵗ (singleTyEnv `★)) A

starAt : ∀ {Δ} → TyVar Δ → Substᵗ Δ Δ
starAt Zᵗ Zᵗ = `★
starAt Zᵗ (Sᵗ Y) = ＇ Sᵗ Y
starAt (Sᵗ X) Zᵗ = ＇ Zᵗ
starAt (Sᵗ X) (Sᵗ Y) = renameᵗ Sᵗ (starAt X Y)

starAt-not-∀ :
  ∀ {Δ} (X Y : TyVar Δ) {A : Ty (suc Δ)} →
  starAt X Y ≡ `∀ A →
  ⊥
starAt-not-∀ Zᵗ Zᵗ ()
starAt-not-∀ Zᵗ (Sᵗ Y) ()
starAt-not-∀ (Sᵗ X) Zᵗ ()
starAt-not-∀ (Sᵗ X) (Sᵗ Y) eq with starAt X Y | inspect (starAt X) Y
starAt-not-∀ (Sᵗ X) (Sᵗ Y) () | ＇ Y′ | _
starAt-not-∀ (Sᵗ X) (Sᵗ Y) () | ‵ x | _
starAt-not-∀ (Sᵗ X) (Sᵗ Y) () | `★ | _
starAt-not-∀ (Sᵗ X) (Sᵗ Y) () | A ⇒ B | _
starAt-not-∀ (Sᵗ X) (Sᵗ Y) eq | `∀ A | [ eq′ ] =
  starAt-not-∀ X Y eq′

starAt-not-base :
  ∀ {Δ} (X Y : TyVar Δ) {ι : Base} →
  starAt X Y ≡ ‵ ι →
  ⊥
starAt-not-base Zᵗ Zᵗ ()
starAt-not-base Zᵗ (Sᵗ Y) ()
starAt-not-base (Sᵗ X) Zᵗ ()
starAt-not-base (Sᵗ X) (Sᵗ Y) eq with starAt X Y | inspect (starAt X) Y
starAt-not-base (Sᵗ X) (Sᵗ Y) () | ＇ Y′ | _
starAt-not-base (Sᵗ X) (Sᵗ Y) eq | ‵ x | [ eq′ ] =
  starAt-not-base X Y eq′
starAt-not-base (Sᵗ X) (Sᵗ Y) () | `★ | _
starAt-not-base (Sᵗ X) (Sᵗ Y) () | A ⇒ B | _
starAt-not-base (Sᵗ X) (Sᵗ Y) () | `∀ A | _

starAt-not-⇒ :
  ∀ {Δ} (X Y : TyVar Δ) {A B : Ty Δ} →
  starAt X Y ≡ A ⇒ B →
  ⊥
starAt-not-⇒ Zᵗ Zᵗ ()
starAt-not-⇒ Zᵗ (Sᵗ Y) ()
starAt-not-⇒ (Sᵗ X) Zᵗ ()
starAt-not-⇒ (Sᵗ X) (Sᵗ Y) eq with starAt X Y | inspect (starAt X) Y
starAt-not-⇒ (Sᵗ X) (Sᵗ Y) () | ＇ Y′ | _
starAt-not-⇒ (Sᵗ X) (Sᵗ Y) () | ‵ x | _
starAt-not-⇒ (Sᵗ X) (Sᵗ Y) () | `★ | _
starAt-not-⇒ (Sᵗ X) (Sᵗ Y) eq | A ⇒ B | [ eq′ ] =
  starAt-not-⇒ X Y eq′
starAt-not-⇒ (Sᵗ X) (Sᵗ Y) () | `∀ A | _

starAt-exts : ∀ {Δ} (X : TyVar Δ) (Y : TyVar (suc Δ)) →
  starAt (Sᵗ X) Y ≡ extsᵗ (starAt X) Y
starAt-exts X Zᵗ = refl
starAt-exts X (Sᵗ Y) = refl

renameᵗ-cong-env :
  ∀ {Δ Δ′}{ρ τ : Renameᵗ Δ Δ′} →
  (∀ X → ρ X ≡ τ X) →
  (A : Ty Δ) →
  renameᵗ ρ A ≡ renameᵗ τ A
renameᵗ-cong-env ρ≡τ (＇ X) = cong ＇_ (ρ≡τ X)
renameᵗ-cong-env ρ≡τ (‵ x) = refl
renameᵗ-cong-env ρ≡τ `★ = refl
renameᵗ-cong-env ρ≡τ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-cong-env ρ≡τ A) (renameᵗ-cong-env ρ≡τ B)
renameᵗ-cong-env ρ≡τ (`∀ A) =
  cong `∀ (renameᵗ-cong-env (λ { Zᵗ → refl ; (Sᵗ X) →
    cong Sᵗ (ρ≡τ X) }) A)

renameᵗ-comp :
  ∀ {Δ Δ′ Δ″}
    (ρ : Renameᵗ Δ′ Δ″) (τ : Renameᵗ Δ Δ′) (A : Ty Δ) →
  renameᵗ ρ (renameᵗ τ A) ≡ renameᵗ (λ X → ρ (τ X)) A
renameᵗ-comp ρ τ (＇ X) = refl
renameᵗ-comp ρ τ (‵ x) = refl
renameᵗ-comp ρ τ `★ = refl
renameᵗ-comp ρ τ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-comp ρ τ A) (renameᵗ-comp ρ τ B)
renameᵗ-comp ρ τ (`∀ A) =
  cong `∀ (trans (renameᵗ-comp (extᵗ ρ) (extᵗ τ) A)
                 (renameᵗ-cong-env (λ { Zᵗ → refl ; (Sᵗ X) → refl }) A))

substᵗ-cong-env :
  ∀ {Δ Δ′}{σ τ : Substᵗ Δ Δ′} →
  (∀ X → σ X ≡ τ X) →
  (A : Ty Δ) →
  substᵗ σ A ≡ substᵗ τ A
substᵗ-cong-env σ≡τ (＇ X) = σ≡τ X
substᵗ-cong-env σ≡τ (‵ x) = refl
substᵗ-cong-env σ≡τ `★ = refl
substᵗ-cong-env σ≡τ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-cong-env σ≡τ A) (substᵗ-cong-env σ≡τ B)
substᵗ-cong-env σ≡τ (`∀ A) =
  cong `∀ (substᵗ-cong-env (λ { Zᵗ → refl ; (Sᵗ X) →
    cong (renameᵗ Sᵗ) (σ≡τ X) }) A)

substᵗ-rename :
  ∀ {Δ Δ′ Δ″}
    (ρ : Renameᵗ Δ Δ′) (σ : Substᵗ Δ′ Δ″) (A : Ty Δ) →
  substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
substᵗ-rename ρ σ (＇ X) = refl
substᵗ-rename ρ σ (‵ x) = refl
substᵗ-rename ρ σ `★ = refl
substᵗ-rename ρ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-rename ρ σ A) (substᵗ-rename ρ σ B)
substᵗ-rename ρ σ (`∀ A) =
  cong `∀ (trans (substᵗ-rename (extᵗ ρ) (extsᵗ σ) A)
                 (substᵗ-cong-env (λ { Zᵗ → refl ; (Sᵗ X) → refl }) A))

renameᵗ-subst :
  ∀ {Δ Δ′ Δ″}
    (ρ : Renameᵗ Δ′ Δ″) (σ : Substᵗ Δ Δ′) (A : Ty Δ) →
  renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ X → renameᵗ ρ (σ X)) A
renameᵗ-subst ρ σ (＇ X) = refl
renameᵗ-subst ρ σ (‵ x) = refl
renameᵗ-subst ρ σ `★ = refl
renameᵗ-subst ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-subst ρ σ A) (renameᵗ-subst ρ σ B)
renameᵗ-subst ρ σ (`∀ A) =
  cong `∀ (trans (renameᵗ-subst (extᵗ ρ) (extsᵗ σ) A)
                 (substᵗ-cong-env env-eq A))
  where
  env-eq : ∀ X →
    renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡
    extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
  env-eq Zᵗ = refl
  env-eq (Sᵗ X) =
    trans (renameᵗ-comp (extᵗ ρ) Sᵗ (σ X))
          (sym (renameᵗ-comp Sᵗ ρ (σ X)))

substᵗ-wkTy :
  ∀ {Δ Δ′} (σ : Substᵗ Δ Δ′) (A : Ty Δ) →
  substᵗ (extsᵗ σ) (wkTy A) ≡ wkTy (substᵗ σ A)
substᵗ-wkTy σ A =
  trans (substᵗ-rename Sᵗ (extsᵗ σ) A)
        (sym (renameᵗ-subst Sᵗ σ A))

starAt-exts-subst :
  ∀ {Δ} (X : TyVar Δ) (A : Ty (suc Δ)) →
  substᵗ (starAt (Sᵗ X)) A ≡ substᵗ (extsᵗ (starAt X)) A
starAt-exts-subst X A = substᵗ-cong-env (starAt-exts X) A

wk-starAt-right-var :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{s X Y} →
  Ψ ∣ ℓ ⊢ ＇ Y ~ starAt X Y →
  (s ∷ Ψ) ∣ ℓ ⊢ ＇ Sᵗ Y ~ renameᵗ Sᵗ (starAt X Y)
wk-starAt-right-var {X = X} {Y = Y} h
  with starAt X Y | inspect (starAt X) Y
wk-starAt-right-var {X = X} {Y = Y} X~X | ＇ .Y | _ = X~X
wk-starAt-right-var {X = X} {Y = Y} (α~✯ Y∈Ψ) | `★ | _ =
  α~✯ (there Y∈Ψ)
wk-starAt-right-var {X = X} {Y = Y} h | `∀ A | [ eq ] =
  ⊥-elim (starAt-not-∀ X Y eq)

wk-starAt-left-var :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{s X Y} →
  Ψ ∣ ℓ ⊢ starAt X Y ~ ＇ Y →
  (s ∷ Ψ) ∣ ℓ ⊢ renameᵗ Sᵗ (starAt X Y) ~ ＇ Sᵗ Y
wk-starAt-left-var {X = X} {Y = Y} h
  with starAt X Y | inspect (starAt X) Y
wk-starAt-left-var {X = X} {Y = Y} X~X | ＇ .Y | _ = X~X
wk-starAt-left-var {X = X} {Y = Y} (✯~α Y∈Ψ) | `★ | _ =
  ✯~α (there Y∈Ψ)
wk-starAt-left-var {X = X} {Y = Y} h | `∀ A | [ eq ] =
  ⊥-elim (starAt-not-∀ X Y eq)

wk-starAt-left-★ :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{s X Y} →
  Ψ ∣ ℓ ⊢ starAt X Y ~ `★ →
  (s ∷ Ψ) ∣ ℓ ⊢ renameᵗ Sᵗ (starAt X Y) ~ `★
wk-starAt-left-★ {X = X} {Y = Y} h
  with starAt X Y | inspect (starAt X) Y
wk-starAt-left-★ {X = X} {Y = Y} (α~✯ Y∈Ψ) | ＇ Y′ | _ =
  α~✯ (there Y∈Ψ)
wk-starAt-left-★ {X = X} {Y = Y} h | ‵ x | [ eq ] =
  ⊥-elim (starAt-not-base X Y eq)
wk-starAt-left-★ {X = X} {Y = Y} ★~★ | `★ | _ = ★~★
wk-starAt-left-★ {X = X} {Y = Y} h | A ⇒ B | [ eq ] =
  ⊥-elim (starAt-not-⇒ X Y eq)
wk-starAt-left-★ {X = X} {Y = Y} h | `∀ A | [ eq ] =
  ⊥-elim (starAt-not-∀ X Y eq)

wk-starAt-right-★ :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{s X Y} →
  Ψ ∣ ℓ ⊢ `★ ~ starAt X Y →
  (s ∷ Ψ) ∣ ℓ ⊢ `★ ~ renameᵗ Sᵗ (starAt X Y)
wk-starAt-right-★ {X = X} {Y = Y} h
  with starAt X Y | inspect (starAt X) Y
wk-starAt-right-★ {X = X} {Y = Y} (✯~α Y∈Ψ) | ＇ Y′ | _ =
  ✯~α (there Y∈Ψ)
wk-starAt-right-★ {X = X} {Y = Y} h | ‵ x | [ eq ] =
  ⊥-elim (starAt-not-base X Y eq)
wk-starAt-right-★ {X = X} {Y = Y} ★~★ | `★ | _ = ★~★
wk-starAt-right-★ {X = X} {Y = Y} h | A ⇒ B | [ eq ] =
  ⊥-elim (starAt-not-⇒ X Y eq)
wk-starAt-right-★ {X = X} {Y = Y} h | `∀ A | [ eq ] =
  ⊥-elim (starAt-not-∀ X Y eq)

starAt-right-var :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{X : TyVar Δ} →
  tyVarToFin X ∈ Ψ →
  (Y : TyVar Δ) →
  Ψ ∣ ℓ ⊢ ＇ Y ~ starAt X Y
starAt-right-var {X = Zᵗ} X∈Ψ Zᵗ = α~✯ X∈Ψ
starAt-right-var {X = Zᵗ} X∈Ψ (Sᵗ Y) = X~X
starAt-right-var {Ψ = s ∷ Ψ} {X = Sᵗ X} (there X∈Ψ) Zᵗ = X~X
starAt-right-var {Ψ = s ∷ Ψ} {X = Sᵗ X} (there X∈Ψ) (Sᵗ Y) =
  wk-starAt-right-var {Ψ = Ψ} {s = s} {X = X} {Y = Y}
                      (starAt-right-var {Ψ = Ψ} {X = X} X∈Ψ Y)

starAt-left-var :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{X : TyVar Δ} →
  tyVarToFin X ∈ Ψ →
  (Y : TyVar Δ) →
  Ψ ∣ ℓ ⊢ starAt X Y ~ ＇ Y
starAt-left-var {X = Zᵗ} X∈Ψ Zᵗ = ✯~α X∈Ψ
starAt-left-var {X = Zᵗ} X∈Ψ (Sᵗ Y) = X~X
starAt-left-var {Ψ = s ∷ Ψ} {X = Sᵗ X} (there X∈Ψ) Zᵗ = X~X
starAt-left-var {Ψ = s ∷ Ψ} {X = Sᵗ X} (there X∈Ψ) (Sᵗ Y) =
  wk-starAt-left-var {Ψ = Ψ} {s = s} {X = X} {Y = Y}
                     (starAt-left-var {Ψ = Ψ} {X = X} X∈Ψ Y)

mutual
  starAt-subst-left :
    ∀ {Δ}{Ψ : Subset Δ}{ℓ}{X : TyVar Δ}{A B : Ty Δ} →
    tyVarToFin X ∈ Ψ →
    Ψ ∣ ℓ ⊢ A ~ B →
    Ψ ∣ ℓ ⊢ substᵗ (starAt X) A ~ B
  starAt-subst-left X∈Ψ X~X = starAt-left-var X∈Ψ _
  starAt-subst-left X∈Ψ (α~✯ Y∈Ψ) =
    starAt-subst-left-★ X∈Ψ Y∈Ψ
  starAt-subst-left X∈Ψ (✯~α Y∈Ψ) = ✯~α Y∈Ψ
  starAt-subst-left X∈Ψ ι~ι = ι~ι
  starAt-subst-left X∈Ψ ★~★ = ★~★
  starAt-subst-left X∈Ψ ★~ι = ★~ι
  starAt-subst-left X∈Ψ ι~★ = ι~★
  starAt-subst-left X∈Ψ (★~⇒ A~★ ★~B) = ★~⇒ A~★ ★~B
  starAt-subst-left X∈Ψ (⇒~★ ★~A B~★) =
    ⇒~★ (starAt-subst-right X∈Ψ ★~A)
         (starAt-subst-left X∈Ψ B~★)
  starAt-subst-left X∈Ψ (⇒~⇒ A′~A B~B′) =
    ⇒~⇒ (starAt-subst-right X∈Ψ A′~A)
        (starAt-subst-left X∈Ψ B~B′)
  starAt-subst-left {ℓ = ℓ} {X = X} X∈Ψ
                    (∀~∀ {A = A} {B = B} A~B) =
    ∀~∀ (substEq (λ T → _ ∣ ℓ ⊢ T ~ B)
                 (starAt-exts-subst X A)
                 (starAt-subst-left (there X∈Ψ) A~B))
  starAt-subst-left {ℓ = ℓ} {X = X} X∈Ψ
                    (∀~ {A = A} {B = B} B★ A~B) =
    ∀~ B★ (substEq (λ T → _ ∣ ℓ ⊢ T ~ wkTy B)
                   (starAt-exts-subst X A)
                   (starAt-subst-left (there X∈Ψ) A~B))
  starAt-subst-left {ℓ = ℓ} {X = X} X∈Ψ
                    (~∀ {A = A} {B = B} A★ A~B) =
    ~∀ (substEq (λ T → has★ T)
                (trans (starAt-exts-subst X (wkTy A))
                       (substᵗ-wkTy (starAt X) A))
                (has★-subst (starAt (Sᵗ X)) A★))
        (substEq (λ T → _ ∣ ℓ ⊢ T ~ B)
                 (trans (starAt-exts-subst X (wkTy A))
                        (substᵗ-wkTy (starAt X) A))
                 (starAt-subst-left (there X∈Ψ) A~B))

  starAt-subst-right :
    ∀ {Δ}{Ψ : Subset Δ}{ℓ}{X : TyVar Δ}{A B : Ty Δ} →
    tyVarToFin X ∈ Ψ →
    Ψ ∣ ℓ ⊢ A ~ B →
    Ψ ∣ ℓ ⊢ A ~ substᵗ (starAt X) B
  starAt-subst-right X∈Ψ X~X = starAt-right-var X∈Ψ _
  starAt-subst-right X∈Ψ (α~✯ Y∈Ψ) = α~✯ Y∈Ψ
  starAt-subst-right X∈Ψ (✯~α Y∈Ψ) =
    starAt-subst-right-★ X∈Ψ Y∈Ψ
  starAt-subst-right X∈Ψ ι~ι = ι~ι
  starAt-subst-right X∈Ψ ★~★ = ★~★
  starAt-subst-right X∈Ψ ★~ι = ★~ι
  starAt-subst-right X∈Ψ ι~★ = ι~★
  starAt-subst-right X∈Ψ (★~⇒ A~★ ★~B) =
    ★~⇒ (starAt-subst-left X∈Ψ A~★)
         (starAt-subst-right X∈Ψ ★~B)
  starAt-subst-right X∈Ψ (⇒~★ ★~A B~★) = ⇒~★ ★~A B~★
  starAt-subst-right X∈Ψ (⇒~⇒ A′~A B~B′) =
    ⇒~⇒ (starAt-subst-left X∈Ψ A′~A)
        (starAt-subst-right X∈Ψ B~B′)
  starAt-subst-right {ℓ = ℓ} {X = X} X∈Ψ
                     (∀~∀ {A = A} {B = B} A~B) =
    ∀~∀ (substEq (λ T → _ ∣ ℓ ⊢ A ~ T)
                 (starAt-exts-subst X B)
                 (starAt-subst-right (there X∈Ψ) A~B))
  starAt-subst-right {ℓ = ℓ} {X = X} X∈Ψ
                     (∀~ {A = A} {B = B} B★ A~B) =
    ∀~ (substEq (λ T → has★ T)
                (trans (starAt-exts-subst X (wkTy B))
                       (substᵗ-wkTy (starAt X) B))
                (has★-subst (starAt (Sᵗ X)) B★))
        (substEq (λ T → _ ∣ ℓ ⊢ A ~ T)
                 (trans (starAt-exts-subst X (wkTy B))
                        (substᵗ-wkTy (starAt X) B))
                 (starAt-subst-right (there X∈Ψ) A~B))
  starAt-subst-right {ℓ = ℓ} {X = X} X∈Ψ
                     (~∀ {A = A} {B = B} A★ A~B) =
    ~∀ A★ (substEq (λ T → _ ∣ ℓ ⊢ wkTy A ~ T)
                   (starAt-exts-subst X B)
                   (starAt-subst-right (there X∈Ψ) A~B))

  starAt-subst-left-★ :
    ∀ {Δ}{Ψ : Subset Δ}{ℓ}{X Y : TyVar Δ} →
    tyVarToFin X ∈ Ψ →
    tyVarToFin Y ∈ Ψ →
    Ψ ∣ ℓ ⊢ starAt X Y ~ `★
  starAt-subst-left-★ {X = Zᵗ} {Y = Zᵗ} X∈Ψ Y∈Ψ = ★~★
  starAt-subst-left-★ {X = Zᵗ} {Y = Sᵗ Y} X∈Ψ Y∈Ψ = α~✯ Y∈Ψ
  starAt-subst-left-★ {X = Sᵗ X} {Y = Zᵗ} X∈Ψ Y∈Ψ = α~✯ Y∈Ψ
  starAt-subst-left-★ {Ψ = s ∷ Ψ} {X = Sᵗ X} {Y = Sᵗ Y}
                      (there X∈Ψ) (there Y∈Ψ) =
    wk-starAt-left-★ {Ψ = Ψ} {s = s} {X = X} {Y = Y}
                     (starAt-subst-left-★ {Ψ = Ψ} {X = X} {Y = Y}
                                          X∈Ψ Y∈Ψ)

  starAt-subst-right-★ :
    ∀ {Δ}{Ψ : Subset Δ}{ℓ}{X Y : TyVar Δ} →
    tyVarToFin X ∈ Ψ →
    tyVarToFin Y ∈ Ψ →
    Ψ ∣ ℓ ⊢ `★ ~ starAt X Y
  starAt-subst-right-★ {X = Zᵗ} {Y = Zᵗ} X∈Ψ Y∈Ψ = ★~★
  starAt-subst-right-★ {X = Zᵗ} {Y = Sᵗ Y} X∈Ψ Y∈Ψ = ✯~α Y∈Ψ
  starAt-subst-right-★ {X = Sᵗ X} {Y = Zᵗ} X∈Ψ Y∈Ψ = ✯~α Y∈Ψ
  starAt-subst-right-★ {Ψ = s ∷ Ψ} {X = Sᵗ X} {Y = Sᵗ Y}
                       (there X∈Ψ) (there Y∈Ψ) =
    wk-starAt-right-★ {Ψ = Ψ} {s = s} {X = X} {Y = Y}
                      (starAt-subst-right-★ {Ψ = Ψ} {X = X} {Y = Y}
                                            X∈Ψ Y∈Ψ)

starAt-close★ :
  ∀ {Δ} (A : Ty (suc Δ)) →
  substᵗ (starAt Zᵗ) A ≡ wkTy (close★ A)
starAt-close★ A =
  trans (substᵗ-cong-env (λ { Zᵗ → refl ; (Sᵗ X) → refl }) A)
        (sym (renameᵗ-subst Sᵗ (singleTyEnv `★) A))

close★-right :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{A B : Ty (suc Δ)} →
  (inside ∷ Ψ) ∣ ℓ ⊢ A ~ B →
  (inside ∷ Ψ) ∣ ℓ ⊢ A ~ wkTy (close★ B)
close★-right {Ψ = Ψ} {ℓ = ℓ} {A = A} {B = B} h =
  substEq (λ C → (inside ∷ Ψ) ∣ ℓ ⊢ A ~ C) (starAt-close★ B)
          (starAt-subst-right {Ψ = inside ∷ Ψ} {X = Zᵗ} here h)

has★-close★-right :
  ∀ {Δ}{Ψ : Subset Δ}{A : Ty (suc Δ)} →
  has★ {suc Δ}{inside ∷ Ψ} A →
  has★ {suc Δ}{inside ∷ Ψ} (wkTy (close★ A))
has★-close★-right {A = A} A★ =
  substEq (λ B → has★ B) (starAt-close★ A)
          (has★-subst (starAt Zᵗ) A★)

close★-func :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{A T U : Ty (suc Δ)} →
  (inside ∷ Ψ) ∣ ℓ ⊢ A ~ (T ⇒ U) →
  (inside ∷ Ψ) ∣ ℓ ⊢ A ~ wkTy (close★ T ⇒ close★ U)
close★-func h = close★-right h

close★-poly :
  ∀ {Δ}{Ψ : Subset Δ}{ℓ}{A : Ty (suc Δ)}{B : Ty (suc (suc Δ))} →
  (inside ∷ Ψ) ∣ ℓ ⊢ A ~ (`∀ B) →
  (inside ∷ Ψ) ∣ ℓ ⊢ A ~ wkTy (`∀ (close★-under-∀ B))
close★-poly h = close★-right h

~-star :
  ∀ {Δ}{Ψ}{ℓ} (A : Ty Δ) →
  Dec (∃[ B ] (has★ {Ψ = Ψ} B × (Ψ ∣ ℓ ⊢ A ~ B)))
~-star {Ψ = Ψ} (＇ X) with tyVarToFin X ∈? Ψ
~-star {Ψ = Ψ} (＇ X) | yes X∈Ψ =
  yes (`★ , has★-★ , α~✯ X∈Ψ)
~-star {Ψ = Ψ} (＇ X) | no X∉Ψ =
  no λ { (.(＇ X) , () , X~X)
       ; (`★ , has★-★ , α~✯ X∈Ψ) → X∉Ψ X∈Ψ
       ; (`∀ B , B★ , ~∀ () _) }
~-star (‵ ι) = yes (`★ , has★-★ , ι~★)
~-star `★ = yes (`★ , has★-★ , ★~★)
~-star {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) with has★? {Ψ = Ψ} (A ⇒ B)
~-star {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | yes A⇒B★ =
  yes (A ⇒ B , A⇒B★ , ~-refl)
~-star {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★
  with ~-star {Ψ = Ψ} {ℓ = push zero ℓ} A
~-star {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★
  | yes (A′ , A′★ , A~A′) =
  yes (A′ ⇒ B , has★-⇒ˡ A′★ , ⇒~⇒ (~-sym A~A′) ~-refl)
~-star {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★ | no A≁★
  with ~-star {Ψ = Ψ} {ℓ = push (suc zero) ℓ} B
~-star {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★ | no A≁★
  | yes (B′ , B′★ , B~B′) =
  yes (A ⇒ B′ , has★-⇒ʳ B′★ , ⇒~⇒ ~-refl B~B′)
~-star {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★ | no A≁★
  | no B≁★ =
  no λ
    { (`★ , has★-★ , ⇒~★ ★~A _) →
        A≁★ (`★ , has★-★ , ~-sym ★~A)
    ; (A′ ⇒ B′ , has★-⇒ˡ A′★ , ⇒~⇒ A′~A _) →
        A≁★ (_ , A′★ , ~-sym A′~A)
    ; (A′ ⇒ B′ , has★-⇒ʳ B′★ , ⇒~⇒ _ B~B′) →
        B≁★ (_ , B′★ , B~B′)
    ; (`∀ C , C★ , ~∀ A⇒B★ _) →
        A⇒B≁★ (has★-rename-inv Sᵗ A⇒B★)
    }
~-star {Ψ = Ψ} (`∀ A) with has★? {Ψ = Ψ} (`∀ A)
~-star {Ψ = Ψ} (`∀ A) | yes ∀A★ =
  yes (`∀ A , ∀A★ , ~-refl)
~-star {Ψ = Ψ} (`∀ A) | no ∀A≁★
  with ~-star {Ψ = outside ∷ Ψ} A
~-star {Ψ = Ψ} (`∀ A) | no ∀A≁★ | yes (B , B★ , A~B) =
  yes (`∀ B , has*-∀ B★ , ∀~∀ A~B)
~-star {Ψ = Ψ} (`∀ A) | no ∀A≁★ | no A≁★out
  with ~-star {Ψ = inside ∷ Ψ} A
~-star {Ψ = Ψ} (`∀ A) | no ∀A≁★ | no A≁★out
  | yes (B , B★ , A~B) =
  yes (close★ B , has★-close★ B★ ,
       ∀~ (has★-wkTy (has★-close★ B★)) (close★-right A~B))
~-star {Ψ = Ψ} (`∀ A) | no ∀A≁★ | no A≁★out | no A≁★in =
  no λ
    { (`∀ B , has*-∀ B★ , ∀~∀ A~B) →
        A≁★out (B , B★ , A~B)
    ; (B , B★ , ∀~ _ A~B) →
        A≁★in (wkTy B , has★-wkTy B★ , A~B)
    ; (`∀ B , B★ , ~∀ ∀A★ _) →
        ∀A≁★ (has★-rename-inv Sᵗ ∀A★)
    }

~-poly★ :
  ∀ {Δ}{Ψ}{ℓ} (A : Ty Δ) →
  Dec (∃[ B ] (has★ {Δ}{Ψ} (`∀ B) × (Ψ ∣ ℓ ⊢ A ~ (`∀ B))))
~-poly★ (＇ X) = no λ { (B , _ , ~∀ () _) }
~-poly★ (‵ ι) = no λ { (B , _ , ~∀ () _) }
~-poly★ `★ = yes (wkTy `★ , has*-∀ has★-★ , ~∀ has★-★ ~-refl)
~-poly★ {Ψ = Ψ} (A ⇒ B) with has★? {Ψ = inside ∷ Ψ} (wkTy (A ⇒ B))
~-poly★ {Ψ = Ψ} (A ⇒ B) | yes A⇒B★ =
  yes (wkTy (A ⇒ B) , has*-∀ (has★-ctx A⇒B★) , ~∀ A⇒B★ ~-refl)
~-poly★ {Ψ = Ψ} (A ⇒ B) | no A⇒B≁★ =
  no λ { (C , _ , ~∀ A⇒B★ _) → A⇒B≁★ A⇒B★ }
~-poly★ {Ψ = Ψ} (`∀ A) with ~-star {Ψ = outside ∷ Ψ} A
~-poly★ {Ψ = Ψ} (`∀ A) | yes (B , B★ , A~B) =
  yes (B , has*-∀ B★ , ∀~∀ A~B)
~-poly★ {Ψ = Ψ} (`∀ A) | no A≁★out
  with ~-poly★ {Ψ = inside ∷ Ψ} A
~-poly★ {Ψ = Ψ} (`∀ A) | no A≁★out | yes (B , ∀B★ , A~∀B) =
  yes (close★-under-∀ B , has★-close★ ∀B★ ,
       ∀~ (has★-close★-right ∀B★) (close★-poly A~∀B))
~-poly★ {Ψ = Ψ} (`∀ A) | no A≁★out | no A≁∀★in
  with has★? {Ψ = inside ∷ Ψ} (wkTy (`∀ A))
~-poly★ {Ψ = Ψ} (`∀ A) | no A≁★out | no A≁∀★in | yes ∀A★ =
  yes (wkTy (`∀ A) , has*-∀ (has★-ctx ∀A★) , ~∀ ∀A★ ~-refl)
~-poly★ {Ψ = Ψ} (`∀ A) | no A≁★out | no A≁∀★in | no ∀A≁★ =
  no λ
    { (B , has*-∀ B★ , ∀~∀ A~B) →
        A≁★out (B , B★ , A~B)
    ; (B , _ , ∀~ ∀B★ A~∀B) →
        A≁∀★in (renameᵗ (extᵗ Sᵗ) B , ∀B★ , A~∀B)
    ; (B , _ , ~∀ ∀A★ _) →
        ∀A≁★ ∀A★
    }

~-func★ :
  ∀ {Δ}{Ψ}{ℓ} (A : Ty Δ) →
  Dec (∃[ T ] ∃[ U ]
       (has★ {Ψ = Ψ} (T ⇒ U) × (Ψ ∣ ℓ ⊢ A ~ (T ⇒ U))))
~-func★ (＇ X) = no λ ()
~-func★ (‵ ι) = no λ ()
~-func★ `★ =
  yes (`★ , `★ , has★-⇒ˡ has★-★ , ★~⇒ ★~★ ★~★)
~-func★ {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) with has★? {Ψ = Ψ} (A ⇒ B)
~-func★ {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | yes A⇒B★ =
  yes (A , B , A⇒B★ , ~-refl)
~-func★ {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★
  with ~-star {Ψ = Ψ} {ℓ = push zero ℓ} A
~-func★ {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★
  | yes (A′ , A′★ , A~A′) =
  yes (A′ , B , has★-⇒ˡ A′★ , ⇒~⇒ (~-sym A~A′) ~-refl)
~-func★ {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★ | no A≁★
  with ~-star {Ψ = Ψ} {ℓ = push (suc zero) ℓ} B
~-func★ {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★ | no A≁★
  | yes (B′ , B′★ , B~B′) =
  yes (A , B′ , has★-⇒ʳ B′★ , ⇒~⇒ ~-refl B~B′)
~-func★ {Ψ = Ψ} {ℓ = ℓ} (A ⇒ B) | no A⇒B≁★ | no A≁★
  | no B≁★ =
  no λ
    { (T , U , has★-⇒ˡ T★ , ⇒~⇒ T~A _) →
        A≁★ (T , T★ , ~-sym T~A)
    ; (T , U , has★-⇒ʳ U★ , ⇒~⇒ _ B~U) →
        B≁★ (U , U★ , B~U)
    }
~-func★ {Ψ = Ψ} (`∀ A) with ~-func★ {Ψ = inside ∷ Ψ} A
~-func★ {Ψ = Ψ} (`∀ A) | yes (T , U , T⇒U★ , A~T⇒U) =
  yes (close★ T , close★ U , has★-close★ T⇒U★ ,
       ∀~ (has★-wkTy (has★-close★ T⇒U★)) (close★-func A~T⇒U))
~-func★ {Ψ = Ψ} (`∀ A) | no A≁⇒★ =
  no λ { (T , U , T⇒U★ , ∀~ T⇒Uwk★ A~T⇒U) →
           A≁⇒★ (wkTy T , wkTy U , T⇒Uwk★ , A~T⇒U) }

~-func : ∀ {Δ}{Ψ}{ℓ} (A : Ty Δ) → Dec (∃[ T ] ∃[ U ] (Ψ ∣ ℓ ⊢ A ~ (T ⇒ U)))
~-func (＇ X) = no λ ()
~-func (‵ ι) = no λ ()
~-func `★ = yes (`★ , `★ , ★~⇒ ★~★ ★~★)
~-func (A ⇒ B) = yes (A , B , ~-refl)
~-func {Ψ = Ψ} (`∀ A) with ~-func★ {Ψ = inside ∷ Ψ} A
~-func {Ψ = Ψ} (`∀ A) | yes (T , U , T⇒U★ , A~T⇒U) =
  yes (close★ T , close★ U ,
       ∀~ (has★-wkTy (has★-close★ T⇒U★)) (close★-func A~T⇒U))
~-func {Ψ = Ψ} (`∀ A) | no A≁⇒★ =
  no λ { (T , U , ∀~ T⇒U★ A~wkT⇒U) →
           A≁⇒★ (wkTy T , wkTy U , T⇒U★ , A~wkT⇒U) }

~-poly : ∀ {Δ}{Ψ}{ℓ} (A : Ty Δ) → Dec (∃[ B ] (Ψ ∣ ℓ ⊢ A ~ (`∀ B)))
~-poly {Ψ = Ψ} (`∀ A) with ~-poly★ {Ψ = inside ∷ Ψ} A
~-poly {Ψ = Ψ} (`∀ A) | yes (B , ∀B★ , A~∀B) =
  yes (close★-under-∀ B ,
       ∀~ (has★-close★-right ∀B★) (close★-poly A~∀B))
~-poly {Ψ = Ψ} (`∀ A) | no _ = yes (A , ∀~∀ ~-refl)
~-poly (＇ X) = no λ { (B , ~∀ () _) }
~-poly (‵ ι) = no λ { (B , ~∀ () _) }
~-poly `★ = yes (wkTy `★ , ~∀ has★-★ ~-refl)
~-poly {Ψ = Ψ} (A ⇒ B) with has★? {Ψ = inside ∷ Ψ} (wkTy (A ⇒ B))
~-poly {Ψ = Ψ} (A ⇒ B) | yes A⇒B★ =
  yes (wkTy (A ⇒ B) , ~∀ A⇒B★ ~-refl)
~-poly {Ψ = Ψ} (A ⇒ B) | no A⇒B≁★ =
  no λ { (B , ~∀ A⇒B★ _) → A⇒B≁★ A⇒B★ }
