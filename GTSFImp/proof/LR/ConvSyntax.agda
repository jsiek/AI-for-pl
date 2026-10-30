module proof.LR.ConvSyntax where

-- File Charter:
--   * Syntactic facts about the generated reveal and conceal conversions
--     `〖 X , R ↑ B 〗` and `makeConceal X R B`, for the conversion lemma
--     of the logical relation (notes/logrel-dgg.md, Section 6.9, item 5).
--   * Conversions with different endpoints are compared packed with
--     their endpoints (`⟪ c ⟫↑`, `⟪ c ⟫↓`), using `_≡_`.
--   * Renaming a generated conversion along an injective renaming
--     generates the conversion of the renamed variable, representation
--     and type.
--   * `replaceTy` commutes with substitution; at a variable it gives the
--     representation, or leaves another variable alone, and so the
--     generated conversions there are `unseal`/`seal` or the identity.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_; suc-injective)
open import Data.Nat using (ℕ) renaming (suc to sucℕ)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Types
open import Conversion
open import CastTerms using (Term; _↑_; _↓_)

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Packed conversions
------------------------------------------------------------------------

Conv↑ᵖ : TyCtx → Set
Conv↑ᵖ Δ = Σ[ A ∈ Ty Δ ] Σ[ B ∈ Ty Δ ] Conv↑ Δ A B

Conv↓ᵖ : TyCtx → Set
Conv↓ᵖ Δ = Σ[ A ∈ Ty Δ ] Σ[ B ∈ Ty Δ ] Conv↓ Δ A B

⟪_⟫↑ : ∀ {A B} → Conv↑ Δ A B → Conv↑ᵖ Δ
⟪ c ⟫↑ = _ , _ , c

⟪_⟫↓ : ∀ {A B} → Conv↓ Δ A B → Conv↓ᵖ Δ
⟪ c ⟫↓ = _ , _ , c

pk-↦↑ : ∀ {A A′ B B′ C C′ D D′}
    {c : Conv↓ Δ A′ A} {c′ : Conv↓ Δ C′ C}
    {d : Conv↑ Δ B B′} {d′ : Conv↑ Δ D D′}
  → ⟪ c ⟫↓ ≡ ⟪ c′ ⟫↓ → ⟪ d ⟫↑ ≡ ⟪ d′ ⟫↑ → ⟪ c ↦↑ d ⟫↑ ≡ ⟪ c′ ↦↑ d′ ⟫↑
pk-↦↑ refl refl = refl

pk-↦↓ : ∀ {A A′ B B′ C C′ D D′}
    {c : Conv↑ Δ A′ A} {c′ : Conv↑ Δ C′ C}
    {d : Conv↓ Δ B B′} {d′ : Conv↓ Δ D D′}
  → ⟪ c ⟫↑ ≡ ⟪ c′ ⟫↑ → ⟪ d ⟫↓ ≡ ⟪ d′ ⟫↓ → ⟪ c ↦↓ d ⟫↓ ≡ ⟪ c′ ↦↓ d′ ⟫↓
pk-↦↓ refl refl = refl

pk-∀↑ : ∀ {A B C D} {c : Conv↑ (sucℕ Δ) A B} {c′ : Conv↑ (sucℕ Δ) C D}
  → ⟪ c ⟫↑ ≡ ⟪ c′ ⟫↑ → ⟪ `∀↑ c ⟫↑ ≡ ⟪ `∀↑ c′ ⟫↑
pk-∀↑ refl = refl

pk-∀↓ : ∀ {A B C D} {c : Conv↓ (sucℕ Δ) A B} {c′ : Conv↓ (sucℕ Δ) C D}
  → ⟪ c ⟫↓ ≡ ⟪ c′ ⟫↓ → ⟪ `∀↓ c ⟫↓ ≡ ⟪ `∀↓ c′ ⟫↓
pk-∀↓ refl = refl

-- equal packed conversions make equal terms and have equal endpoints
↑-pk : ∀ {M : Term Δ} {A B C D} {c : Conv↑ Δ A B} {c′ : Conv↑ Δ C D}
  → ⟪ c ⟫↑ ≡ ⟪ c′ ⟫↑ → M ↑ c ≡ M ↑ c′
↑-pk refl = refl

↓-pk : ∀ {M : Term Δ} {A B C D} {c : Conv↓ Δ A B} {c′ : Conv↓ Δ C D}
  → ⟪ c ⟫↓ ≡ ⟪ c′ ⟫↓ → M ↓ c ≡ M ↓ c′
↓-pk refl = refl

src↑ : ∀ {A B C D} {c : Conv↑ Δ A B} {c′ : Conv↑ Δ C D}
  → ⟪ c ⟫↑ ≡ ⟪ c′ ⟫↑ → A ≡ C
src↑ refl = refl

tgt↑ : ∀ {A B C D} {c : Conv↑ Δ A B} {c′ : Conv↑ Δ C D}
  → ⟪ c ⟫↑ ≡ ⟪ c′ ⟫↑ → B ≡ D
tgt↑ refl = refl

------------------------------------------------------------------------
-- Renaming generated conversions
------------------------------------------------------------------------

Injective : (Δ ⇒ʳ Δ′) → Set
Injective ρ = ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y

ext-injective : ∀ {ρ : Δ ⇒ʳ Δ′} → Injective ρ → Injective (extᵗ ρ)
ext-injective inj {zero} {zero} eq = refl
ext-injective inj {zero} {suc Y} ()
ext-injective inj {suc X} {zero} ()
ext-injective inj {suc X} {suc Y} eq = cong suc (inj (suc-injective eq))

suc-inj : Injective {Δ = Δ} suc
suc-inj = suc-injective

mutual
  〖〗-rename : (ρ : Δ ⇒ʳ Δ′) → Injective ρ → ∀ X R B
    → ⟪ rename↑ ρ 〖 X , R ↑ B 〗 ⟫↑
      ≡ ⟪ 〖 ρ X , renameᵗ ρ R ↑ renameᵗ ρ B 〗 ⟫↑
  〖〗-rename ρ inj X R (＇ Y) with X ≟ Y | ρ X ≟ ρ Y
  〖〗-rename ρ inj X R (＇ .X) | yes refl | yes refl = refl
  〖〗-rename ρ inj X R (＇ .X) | yes refl | no ne = ⊥-elim (ne refl)
  〖〗-rename ρ inj X R (＇ Y) | no ne | yes eq = ⊥-elim (ne (inj eq))
  〖〗-rename ρ inj X R (＇ Y) | no ne | no ne′ = refl
  〖〗-rename ρ inj X R (‵ ι) = refl
  〖〗-rename ρ inj X R ★ = refl
  〖〗-rename ρ inj X R (A ⇒ B) =
    pk-↦↑ (makeConceal-rename ρ inj X R A) (〖〗-rename ρ inj X R B)
  〖〗-rename ρ inj X R (`∀ A) =
    pk-∀↑ (trans (〖〗-rename (extᵗ ρ) (ext-injective inj) (suc X) (⇑ᵗ R) A)
      (cong (λ R′ → ⟪ 〖 suc (ρ X) , R′ ↑ renameᵗ (extᵗ ρ) A 〗 ⟫↑)
        (renameᵗ-shift ρ R)))

  makeConceal-rename : (ρ : Δ ⇒ʳ Δ′) → Injective ρ → ∀ X R B
    → ⟪ rename↓ ρ (makeConceal X R B) ⟫↓
      ≡ ⟪ makeConceal (ρ X) (renameᵗ ρ R) (renameᵗ ρ B) ⟫↓
  makeConceal-rename ρ inj X R (＇ Y) with X ≟ Y | ρ X ≟ ρ Y
  makeConceal-rename ρ inj X R (＇ .X) | yes refl | yes refl = refl
  makeConceal-rename ρ inj X R (＇ .X) | yes refl | no ne = ⊥-elim (ne refl)
  makeConceal-rename ρ inj X R (＇ Y) | no ne | yes eq = ⊥-elim (ne (inj eq))
  makeConceal-rename ρ inj X R (＇ Y) | no ne | no ne′ = refl
  makeConceal-rename ρ inj X R (‵ ι) = refl
  makeConceal-rename ρ inj X R ★ = refl
  makeConceal-rename ρ inj X R (A ⇒ B) =
    pk-↦↓ (〖〗-rename ρ inj X R A) (makeConceal-rename ρ inj X R B)
  makeConceal-rename ρ inj X R (`∀ A) =
    pk-∀↓ (trans
      (makeConceal-rename (extᵗ ρ) (ext-injective inj) (suc X) (⇑ᵗ R) A)
      (cong (λ R′ → ⟪ makeConceal (suc (ρ X)) R′ (renameᵗ (extᵗ ρ) A) ⟫↓)
        (renameᵗ-shift ρ R)))

replaceTy-rename : (ρ : Δ ⇒ʳ Δ′) → Injective ρ → ∀ X R B
  → renameᵗ ρ (replaceTy X R B) ≡ replaceTy (ρ X) (renameᵗ ρ R) (renameᵗ ρ B)
replaceTy-rename ρ inj X R B = tgt↑ (〖〗-rename ρ inj X R B)

------------------------------------------------------------------------
-- `replaceTy` at variables and under substitution
------------------------------------------------------------------------

replaceTy-self : ∀ (X : TyVar Δ) R → replaceTy X R (＇ X) ≡ R
replaceTy-self X R with X ≟ X
replaceTy-self X R | yes refl = refl
replaceTy-self X R | no ne = ⊥-elim (ne refl)

replaceTy-other : ∀ {X Y : TyVar Δ} R → Y ≢ X → replaceTy X R (＇ Y) ≡ ＇ Y
replaceTy-other {X = X} {Y} R ne with X ≟ Y
replaceTy-other {X = X} {.X} R ne | yes refl = ⊥-elim (ne refl)
replaceTy-other {X = X} {Y} R ne | no ne′ = refl

replaceTy-subst : ∀ (X : TyVar Δ′) R (σ : Δ ⇒ˢ Δ′) A
  → replaceTy X R (substᵗ σ A) ≡ substᵗ (λ Z → replaceTy X R (σ Z)) A
replaceTy-subst X R σ (＇ Z) = refl
replaceTy-subst X R σ (‵ ι) = refl
replaceTy-subst X R σ ★ = refl
replaceTy-subst X R σ (A ⇒ B) =
  cong₂ _⇒_ (replaceTy-subst X R σ A) (replaceTy-subst X R σ B)
replaceTy-subst X R σ (`∀ A) =
  cong `∀ (trans (replaceTy-subst (suc X) (⇑ᵗ R) (extsᵗ σ) A)
    (substᵗ-cong A eq))
  where
  eq : ∀ Z → replaceTy (suc X) (⇑ᵗ R) (extsᵗ σ Z)
    ≡ extsᵗ (λ Z′ → replaceTy X R (σ Z′)) Z
  eq zero = replaceTy-other {X = suc X} (⇑ᵗ R) (λ ())
  eq (suc Z) = sym (replaceTy-rename suc suc-inj X R (σ Z))

------------------------------------------------------------------------
-- The generated conversions at a variable
------------------------------------------------------------------------

〖〗-self : ∀ (X : TyVar Δ) R {T} → T ≡ ＇ X
  → ⟪ 〖 X , R ↑ T 〗 ⟫↑ ≡ ⟪ unseal X R ⟫↑
〖〗-self X R refl with X ≟ X
〖〗-self X R refl | yes refl = refl
〖〗-self X R refl | no ne = ⊥-elim (ne refl)

〖〗-other : ∀ {X Y : TyVar Δ} R {T} → T ≡ ＇ Y → Y ≢ X
  → ⟪ 〖 X , R ↑ T 〗 ⟫↑ ≡ ⟪ id↑ (＇ Y) ⟫↑
〖〗-other {X = X} {Y} R refl ne with X ≟ Y
〖〗-other {X = X} {.X} R refl ne | yes refl = ⊥-elim (ne refl)
〖〗-other {X = X} {Y} R refl ne | no ne′ = refl

makeConceal-self : ∀ (X : TyVar Δ) R {T} → T ≡ ＇ X
  → ⟪ makeConceal X R T ⟫↓ ≡ ⟪ seal X R ⟫↓
makeConceal-self X R refl with X ≟ X
makeConceal-self X R refl | yes refl = refl
makeConceal-self X R refl | no ne = ⊥-elim (ne refl)

makeConceal-other : ∀ {X Y : TyVar Δ} R {T} → T ≡ ＇ Y → Y ≢ X
  → ⟪ makeConceal X R T ⟫↓ ≡ ⟪ id↓ (＇ Y) ⟫↓
makeConceal-other {X = X} {Y} R refl ne with X ≟ Y
makeConceal-other {X = X} {.X} R refl ne | yes refl = ⊥-elim (ne refl)
makeConceal-other {X = X} {Y} R refl ne | no ne′ = refl
