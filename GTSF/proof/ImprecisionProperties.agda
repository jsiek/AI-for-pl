module proof.ImprecisionProperties where

-- File Charter:
--   * Basic metatheory for GTSF type imprecision.
--   * Defines well-formed imprecision-assumption contexts, endpoint
--     well-formedness for imprecision derivations, and symmetry/reflexivity
--     helpers for consistency-as-common-lower-bound.
--   * Heavier maximal-lower-bound search/proofs belong in a separate module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (_≟_; m<n⇒m<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Imprecision
open import proof.TypeProperties using (occurs-zero-rename-ext; WfTy-un⇑ᵗ)

------------------------------------------------------------------------
-- Well-formed imprecision assumption contexts
------------------------------------------------------------------------

WfImpAssm : TyCtx → ImpAssm → Set
WfImpAssm Δ (X ˣ⊑★) = X < Δ
WfImpAssm Δ (X ˣ⊑ˣ Y) = X < Δ × Y < Δ

WfImpCtx : TyCtx → ImpCtx → Set
WfImpCtx Δ Φ = ∀ {a} → a ∈ Φ → WfImpAssm Δ a

WfImpAssm² : TyCtx → TyCtx → ImpAssm → Set
WfImpAssm² Δᴸ Δᴿ (X ˣ⊑★) = X < Δᴸ
WfImpAssm² Δᴸ Δᴿ (X ˣ⊑ˣ Y) = X < Δᴸ × Y < Δᴿ

WfImpCtx² : TyCtx → TyCtx → ImpCtx → Set
WfImpCtx² Δᴸ Δᴿ Φ = ∀ {a} → a ∈ Φ → WfImpAssm² Δᴸ Δᴿ a

WfImpCtx-to² :
  ∀ {Δ Φ} →
  WfImpCtx Δ Φ →
  WfImpCtx² Δ Δ Φ
WfImpCtx-to² hΦ {a = X ˣ⊑★} a∈ = hΦ a∈
WfImpCtx-to² hΦ {a = X ˣ⊑ˣ Y} a∈ = hΦ a∈

⇑ᵢ-∈ :
  ∀ {Φ a} →
  a ∈ Φ →
  ⇑ᵢₐ a ∈ ⇑ᵢ Φ
⇑ᵢ-∈ {Φ = (a ∷ Φ)} (here refl) = here refl
⇑ᵢ-∈ {Φ = (b ∷ Φ)} (there a∈) = there (⇑ᵢ-∈ a∈)

⇑ᴸᵢ-∈ :
  ∀ {Φ a} →
  a ∈ Φ →
  ⇑ᴸᵢₐ a ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-∈ {Φ = (a ∷ Φ)} (here refl) = here refl
⇑ᴸᵢ-∈ {Φ = (b ∷ Φ)} (there a∈) = there (⇑ᴸᵢ-∈ a∈)

⇑ᵢ-wf :
  ∀ {Δ Φ} →
  WfImpCtx Δ Φ →
  WfImpCtx (suc Δ) (⇑ᵢ Φ)
⇑ᵢ-wf {Φ = []} hΦ ()
⇑ᵢ-wf {Φ = (X ˣ⊑★) ∷ Φ} hΦ (here refl) =
  s<s (hΦ (here refl))
⇑ᵢ-wf {Φ = (X ˣ⊑★) ∷ Φ} hΦ (there a∈) =
  ⇑ᵢ-wf (λ b∈ → hΦ (there b∈)) a∈
⇑ᵢ-wf {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (here refl) =
  s<s (proj₁ (hΦ (here refl))) , s<s (proj₂ (hΦ (here refl)))
⇑ᵢ-wf {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (there a∈) =
  ⇑ᵢ-wf (λ b∈ → hΦ (there b∈)) a∈

⇑ᴸᵢ-wf :
  ∀ {Δ Φ} →
  WfImpCtx Δ Φ →
  WfImpCtx (suc Δ) (⇑ᴸᵢ Φ)
⇑ᴸᵢ-wf {Φ = []} hΦ ()
⇑ᴸᵢ-wf {Φ = (X ˣ⊑★) ∷ Φ} hΦ (here refl) =
  s<s (hΦ (here refl))
⇑ᴸᵢ-wf {Φ = (X ˣ⊑★) ∷ Φ} hΦ (there a∈) =
  ⇑ᴸᵢ-wf (λ b∈ → hΦ (there b∈)) a∈
⇑ᴸᵢ-wf {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (here refl) =
  s<s (proj₁ (hΦ (here refl))) ,
  m<n⇒m<1+n (proj₂ (hΦ (here refl)))
⇑ᴸᵢ-wf {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (there a∈) =
  ⇑ᴸᵢ-wf (λ b∈ → hΦ (there b∈)) a∈

∀ᵢ-wf :
  ∀ {Δ Φ} →
  WfImpCtx Δ Φ →
  WfImpCtx (suc Δ) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ᵢ-wf hΦ (here refl) = z<s , z<s
∀ᵢ-wf hΦ (there a∈) = ⇑ᵢ-wf hΦ a∈

νᵢ-wf :
  ∀ {Δ Φ} →
  WfImpCtx Δ Φ →
  WfImpCtx (suc Δ) ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
νᵢ-wf hΦ (here refl) = z<s
νᵢ-wf hΦ (there a∈) = ⇑ᵢ-wf hΦ a∈

⇑ᵢ-wf² :
  ∀ {Δᴸ Δᴿ Φ} →
  WfImpCtx² Δᴸ Δᴿ Φ →
  WfImpCtx² (suc Δᴸ) (suc Δᴿ) (⇑ᵢ Φ)
⇑ᵢ-wf² {Φ = []} hΦ ()
⇑ᵢ-wf² {Φ = (X ˣ⊑★) ∷ Φ} hΦ (here refl) =
  s<s (hΦ (here refl))
⇑ᵢ-wf² {Φ = (X ˣ⊑★) ∷ Φ} hΦ (there a∈) =
  ⇑ᵢ-wf² (λ b∈ → hΦ (there b∈)) a∈
⇑ᵢ-wf² {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (here refl) =
  s<s (proj₁ (hΦ (here refl))) , s<s (proj₂ (hΦ (here refl)))
⇑ᵢ-wf² {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (there a∈) =
  ⇑ᵢ-wf² (λ b∈ → hΦ (there b∈)) a∈

⇑ᴸᵢ-wf² :
  ∀ {Δᴸ Δᴿ Φ} →
  WfImpCtx² Δᴸ Δᴿ Φ →
  WfImpCtx² (suc Δᴸ) Δᴿ (⇑ᴸᵢ Φ)
⇑ᴸᵢ-wf² {Φ = []} hΦ ()
⇑ᴸᵢ-wf² {Φ = (X ˣ⊑★) ∷ Φ} hΦ (here refl) =
  s<s (hΦ (here refl))
⇑ᴸᵢ-wf² {Φ = (X ˣ⊑★) ∷ Φ} hΦ (there a∈) =
  ⇑ᴸᵢ-wf² (λ b∈ → hΦ (there b∈)) a∈
⇑ᴸᵢ-wf² {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (here refl) =
  s<s (proj₁ (hΦ (here refl))) , proj₂ (hΦ (here refl))
⇑ᴸᵢ-wf² {Φ = (X ˣ⊑ˣ Y) ∷ Φ} hΦ (there a∈) =
  ⇑ᴸᵢ-wf² (λ b∈ → hΦ (there b∈)) a∈

∀ᵢ-wf² :
  ∀ {Δᴸ Δᴿ Φ} →
  WfImpCtx² Δᴸ Δᴿ Φ →
  WfImpCtx² (suc Δᴸ) (suc Δᴿ) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
∀ᵢ-wf² hΦ (here refl) = z<s , z<s
∀ᵢ-wf² hΦ (there a∈) = ⇑ᵢ-wf² hΦ a∈

νᵢ-wf² :
  ∀ {Δᴸ Δᴿ Φ} →
  WfImpCtx² Δᴸ Δᴿ Φ →
  WfImpCtx² (suc Δᴸ) (suc Δᴿ) ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
νᵢ-wf² hΦ (here refl) = z<s
νᵢ-wf² hΦ (there a∈) = ⇑ᵢ-wf² hΦ a∈

idᵢ-wf :
  ∀ Δ →
  WfImpCtx Δ (idᵢ Δ)
idᵢ-wf zero ()
idᵢ-wf (suc Δ) (here refl) = z<s , z<s
idᵢ-wf (suc Δ) (there a∈) = ⇑ᵢ-wf (idᵢ-wf Δ) a∈

idᵢ-lookup :
  ∀ {Δ X} →
  X < Δ →
  (X ˣ⊑ˣ X) ∈ idᵢ Δ
idᵢ-lookup {Δ = zero} ()
idᵢ-lookup {Δ = suc Δ} {X = zero} z<s = here refl
idᵢ-lookup {Δ = suc Δ} {X = suc X} (s<s X<Δ) =
  there (⇑ᵢ-∈ (idᵢ-lookup X<Δ))

⇑ᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ
⇑ᵢ-ˣ∈ {Φ = []} ()
⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᵢ-ˣ∈ x∈)
⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᵢ-ˣ∈ x∈)

⇑ᵢ-★∈ :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᵢ Φ
⇑ᵢ-★∈ {Φ = []} ()
⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (⇑ᵢ-★∈ x∈)
⇑ᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (⇑ᵢ-★∈ x∈)

un⇑ᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᵢ-ˣ∈ {Φ = []} ()
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-ˣ∈ x∈)
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-ˣ∈ x∈)

un⇑ᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᵢ-★∈ {Φ = []} ()
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-★∈ x∈)
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᵢ-★∈ x∈)

no-⇑ᵢ-zero-left :
  ∀ {Φ X} →
  (zero ˣ⊑ˣ X) ∈ ⇑ᵢ Φ →
  ⊥
no-⇑ᵢ-zero-left {Φ = []} ()
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-left x∈
no-⇑ᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-left x∈

no-⇑ᵢ-zero-right :
  ∀ {Φ X} →
  (X ˣ⊑ˣ zero) ∈ ⇑ᵢ Φ →
  ⊥
no-⇑ᵢ-zero-right {Φ = []} ()
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-right x∈
no-⇑ᵢ-zero-right {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-right x∈

no-⇑ᵢ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᵢ Φ →
  ⊥
no-⇑ᵢ-zero-star {Φ = []} ()
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-star x∈
no-⇑ᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᵢ-zero-star x∈

idᵢ-var-identity :
  ∀ {Δ X Y} →
  (X ˣ⊑ˣ Y) ∈ idᵢ Δ →
  X ≡ Y
idᵢ-var-identity {Δ = zero} ()
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero} (here refl) =
  refl
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
idᵢ-var-identity {Δ = suc Δ} {X = zero} {Y = suc Y} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-left x∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = zero} (there x∈) =
  ⊥-elim (no-⇑ᵢ-zero-right x∈)
idᵢ-var-identity {Δ = suc Δ} {X = suc X} {Y = suc Y} (there x∈) =
  cong suc (idᵢ-var-identity (un⇑ᵢ-ˣ∈ x∈))

idᵢ-no-star :
  ∀ {Δ X} →
  (X ˣ⊑★) ∈ idᵢ Δ →
  ⊥
idᵢ-no-star {Δ = zero} ()
idᵢ-no-star {Δ = suc Δ} {X = zero} (there x∈) =
  no-⇑ᵢ-zero-star x∈
idᵢ-no-star {Δ = suc Δ} {X = suc X} (there x∈) =
  idᵢ-no-star (un⇑ᵢ-★∈ x∈)

------------------------------------------------------------------------
-- Deciding imprecision
------------------------------------------------------------------------

occurs-zero? : (A : Ty) → Dec (occurs zero A ≡ true)
occurs-zero? A with occurs zero A
occurs-zero? A | false = no (λ ())
occurs-zero? A | true = yes refl

nonVar? : (A : Ty) → Dec (NonVar A)
nonVar? (＇ X) = no (λ ())
nonVar? (‵ ι) = yes nonvar-base
nonVar? ★ = yes nonvar-star
nonVar? (A ⇒ B) = yes nonvar-fun
nonVar? (`∀ A) = yes nonvar-all

infix 4 _≟ImpAssm_
_≟ImpAssm_ : (a b : ImpAssm) → Dec (a ≡ b)
(x ˣ⊑★) ≟ImpAssm (y ˣ⊑★) with x ≟ y
(x ˣ⊑★) ≟ImpAssm (.x ˣ⊑★) | yes refl = yes refl
(x ˣ⊑★) ≟ImpAssm (y ˣ⊑★) | no x≢y =
  no (λ { refl → x≢y refl })
(x ˣ⊑★) ≟ImpAssm (y ˣ⊑ˣ z) = no (λ ())
(x ˣ⊑ˣ y) ≟ImpAssm (z ˣ⊑★) = no (λ ())
(x ˣ⊑ˣ y) ≟ImpAssm (z ˣ⊑ˣ w) with x ≟ z | y ≟ w
(x ˣ⊑ˣ y) ≟ImpAssm (.x ˣ⊑ˣ .y) | yes refl | yes refl =
  yes refl
(x ˣ⊑ˣ y) ≟ImpAssm (z ˣ⊑ˣ w) | no x≢z | _ =
  no (λ { refl → x≢z refl })
(x ˣ⊑ˣ y) ≟ImpAssm (.x ˣ⊑ˣ w) | yes refl | no y≢w =
  no (λ { refl → y≢w refl })

infix 4 _∈ᵢ?_
_∈ᵢ?_ : (a : ImpAssm) → (Φ : ImpCtx) → Dec (a ∈ Φ)
a ∈ᵢ? [] = no (λ ())
a ∈ᵢ? (b ∷ Φ) with a ≟ImpAssm b
a ∈ᵢ? (b ∷ Φ) | yes refl = yes (here refl)
a ∈ᵢ? (b ∷ Φ) | no a≢b with a ∈ᵢ? Φ
... | yes a∈Φ = yes (there a∈Φ)
... | no a∉Φ =
  no λ
    { (here refl) → a≢b refl
    ; (there a∈Φ) → a∉Φ a∈Φ
    }

mutual
  imp? : (Φ : ImpCtx) (A B : Ty) → Dec (Φ ⊢ A ⊑ B)
  imp? Φ (＇ X) (＇ Y) with (X ˣ⊑ˣ Y) ∈ᵢ? Φ
  ... | yes x⊑y = yes (idˣ x⊑y)
  ... | no x⋢y = no λ { (idˣ x⊑y) → x⋢y x⊑y }
  imp? Φ (＇ X) (‵ ι) = no (λ ())
  imp? Φ (＇ X) ★ with (X ˣ⊑★) ∈ᵢ? Φ
  ... | yes x⊑★ = yes (tagˣ x⊑★)
  ... | no x⋢★ = no λ { (tagˣ x⊑★) → x⋢★ x⊑★ }
  imp? Φ (＇ X) (B₁ ⇒ B₂) = no (λ ())
  imp? Φ (＇ X) (`∀ B) = no (λ ())
  imp? Φ (‵ ι) (＇ X) = no (λ ())
  imp? Φ (‵ ι) (‵ κ) with ι ≟Base κ
  ... | yes refl = yes idι
  ... | no ι≢κ = no λ { idι → ι≢κ refl }
  imp? Φ (‵ ι) ★ = yes (tag ι)
  imp? Φ (‵ ι) (B₁ ⇒ B₂) = no (λ ())
  imp? Φ (‵ ι) (`∀ B) = no (λ ())
  imp? Φ ★ (＇ X) = no (λ ())
  imp? Φ ★ (‵ ι) = no (λ ())
  imp? Φ ★ ★ = yes id★
  imp? Φ ★ (B₁ ⇒ B₂) = no (λ ())
  imp? Φ ★ (`∀ B) = no (λ ())
  imp? Φ (A₁ ⇒ A₂) (＇ X) = no (λ ())
  imp? Φ (A₁ ⇒ A₂) (‵ ι) = no (λ ())
  imp? Φ (A₁ ⇒ A₂) ★ with imp? Φ A₁ ★ | imp? Φ A₂ ★
  ... | yes A₁⊑★ | yes A₂⊑★ = yes (tag_⇛_ A₁⊑★ A₂⊑★)
  ... | no A₁⋢★ | _ =
    no λ { (tag_⇛_ A₁⊑★ A₂⊑★) → A₁⋢★ A₁⊑★ }
  ... | yes A₁⊑★ | no A₂⋢★ =
    no λ { (tag_⇛_ A₁⊑★ A₂⊑★) → A₂⋢★ A₂⊑★ }
  imp? Φ (A₁ ⇒ A₂) (B₁ ⇒ B₂) with imp? Φ A₁ B₁ | imp? Φ A₂ B₂
  ... | yes A₁⊑B₁ | yes A₂⊑B₂ = yes (A₁⊑B₁ ↦ A₂⊑B₂)
  ... | no A₁⋢B₁ | _ = no λ { (A₁⊑B₁ ↦ A₂⊑B₂) → A₁⋢B₁ A₁⊑B₁ }
  ... | yes A₁⊑B₁ | no A₂⋢B₂ =
    no λ { (A₁⊑B₁ ↦ A₂⊑B₂) → A₂⋢B₂ A₂⊑B₂ }
  imp? Φ (A₁ ⇒ A₂) (`∀ B) = no (λ ())
  imp? Φ (`∀ A) (＇ X) with nonVar? A
  imp? Φ (`∀ A) (＇ X) | no ¬safe =
    no λ { (ν safe occ A⊑X) → ¬safe safe }
  imp? Φ (`∀ A) (＇ X) | yes safe with occurs-zero? A
  imp? Φ (`∀ A) (＇ X) | yes safe | no ¬occA =
    no λ { (ν nonvar occ A⊑X) → ¬occA occ }
  imp? Φ (`∀ A) (＇ X) | yes safe | yes occA
      with imp? ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A (⇑ᵗ (＇ X))
  imp? Φ (`∀ A) (＇ X) | yes safe | yes occA | yes A⊑X =
    yes (ν safe occA A⊑X)
  imp? Φ (`∀ A) (＇ X) | yes safe | yes occA | no A⋢X =
    no λ { (ν nonvar occ A⊑X) → A⋢X A⊑X }
  imp? Φ (`∀ A) (‵ ι) with nonVar? A
  imp? Φ (`∀ A) (‵ ι) | no ¬safe =
    no λ { (ν safe occ A⊑ι) → ¬safe safe }
  imp? Φ (`∀ A) (‵ ι) | yes safe with occurs-zero? A
  imp? Φ (`∀ A) (‵ ι) | yes safe | no ¬occA =
    no λ { (ν nonvar occ A⊑ι) → ¬occA occ }
  imp? Φ (`∀ A) (‵ ι) | yes safe | yes occA
      with imp? ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A (⇑ᵗ (‵ ι))
  imp? Φ (`∀ A) (‵ ι) | yes safe | yes occA | yes A⊑ι =
    yes (ν safe occA A⊑ι)
  imp? Φ (`∀ A) (‵ ι) | yes safe | yes occA | no A⋢ι =
    no λ { (ν nonvar occ A⊑ι) → A⋢ι A⊑ι }
  imp? Φ (`∀ A) ★ with nonVar? A
  imp? Φ (`∀ A) ★ | no ¬safe =
    no λ { (ν safe occ A⊑★) → ¬safe safe }
  imp? Φ (`∀ A) ★ | yes safe with occurs-zero? A
  imp? Φ (`∀ A) ★ | yes safe | no ¬occA =
    no λ { (ν nonvar occ A⊑★) → ¬occA occ }
  imp? Φ (`∀ A) ★ | yes safe | yes occA
      with imp? ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A (⇑ᵗ ★)
  imp? Φ (`∀ A) ★ | yes safe | yes occA | yes A⊑★ =
    yes (ν safe occA A⊑★)
  imp? Φ (`∀ A) ★ | yes safe | yes occA | no A⋢★ =
    no λ { (ν nonvar occ A⊑★) → A⋢★ A⊑★ }
  imp? Φ (`∀ A) (B₁ ⇒ B₂) with nonVar? A
  imp? Φ (`∀ A) (B₁ ⇒ B₂) | no ¬safe =
    no λ { (ν safe occ A⊑B) → ¬safe safe }
  imp? Φ (`∀ A) (B₁ ⇒ B₂) | yes safe with occurs-zero? A
  imp? Φ (`∀ A) (B₁ ⇒ B₂) | yes safe | no ¬occA =
    no λ { (ν nonvar occ A⊑B) → ¬occA occ }
  imp? Φ (`∀ A) (B₁ ⇒ B₂) | yes safe | yes occA
      with imp? ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A (⇑ᵗ (B₁ ⇒ B₂))
  imp? Φ (`∀ A) (B₁ ⇒ B₂) | yes safe | yes occA | yes A⊑B =
    yes (ν safe occA A⊑B)
  imp? Φ (`∀ A) (B₁ ⇒ B₂) | yes safe | yes occA | no A⋢B =
    no λ { (ν nonvar occ A⊑B) → A⋢B A⊑B }
  imp? Φ (`∀ A) (`∀ B)
      with imp? ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) A B
  imp? Φ (`∀ A) (`∀ B) | yes A⊑B = yes (∀ⁱ A⊑B)
  imp? Φ (`∀ A) (`∀ B) | no A⋢B with nonVar? A
  imp? Φ (`∀ A) (`∀ B) | no A⋢B | no ¬safe =
    no λ
      { (∀ⁱ A⊑B) → A⋢B A⊑B
      ; (ν safe occ A⊑∀B) → ¬safe safe
      }
  imp? Φ (`∀ A) (`∀ B) | no A⋢B | yes safe
      with occurs-zero? A
  imp? Φ (`∀ A) (`∀ B) | no A⋢B | yes safe | no ¬occA =
    no λ
      { (∀ⁱ A⊑B) → A⋢B A⊑B
      ; (ν nonvar occ A⊑∀B) → ¬occA occ
      }
  imp? Φ (`∀ A) (`∀ B) | no A⋢B | yes safe | yes occA
      with imp? ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) A (⇑ᵗ (`∀ B))
  imp? Φ (`∀ A) (`∀ B) | no A⋢B | yes safe | yes occA
      | yes A⊑∀B =
    yes (ν safe occA A⊑∀B)
  imp? Φ (`∀ A) (`∀ B) | no A⋢B | yes safe | yes occA
      | no A⋢∀B =
    no λ
      { (∀ⁱ A⊑B) → A⋢B A⊑B
      ; (ν nonvar occ A⊑∀B) → A⋢∀B A⊑∀B
      }

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

mutual
  ⊑-src-wf² :
    ∀ {Δᴸ Δᴿ Φ A B} →
    WfImpCtx² Δᴸ Δᴿ Φ →
    Φ ⊢ A ⊑ B →
    WfTy Δᴸ A

  ⊑-tgt-wf² :
    ∀ {Δᴸ Δᴿ Φ A B} →
    WfImpCtx² Δᴸ Δᴿ Φ →
    Φ ⊢ A ⊑ B →
    WfTy Δᴿ B

  ⊑-src-wf² hΦ id★ = wf★
  ⊑-src-wf² hΦ (idˣ X⊑Y∈) = wfVar (proj₁ (hΦ X⊑Y∈))
  ⊑-src-wf² hΦ idι = wfBase
  ⊑-src-wf² hΦ (p ↦ q) =
    wf⇒ (⊑-src-wf² hΦ p) (⊑-src-wf² hΦ q)
  ⊑-src-wf² hΦ (∀ⁱ p) =
    wf∀ (⊑-src-wf² (∀ᵢ-wf² hΦ) p)
  ⊑-src-wf² hΦ (tag ι) = wfBase
  ⊑-src-wf² hΦ (tag_⇛_ p q) =
    wf⇒ (⊑-src-wf² hΦ p) (⊑-src-wf² hΦ q)
  ⊑-src-wf² hΦ (tagˣ X⊑★∈) = wfVar (hΦ X⊑★∈)
  ⊑-src-wf² hΦ (ν nonvar occA p) =
    wf∀ (⊑-src-wf² (νᵢ-wf² hΦ) p)

  ⊑-tgt-wf² hΦ id★ = wf★
  ⊑-tgt-wf² hΦ (idˣ X⊑Y∈) = wfVar (proj₂ (hΦ X⊑Y∈))
  ⊑-tgt-wf² hΦ idι = wfBase
  ⊑-tgt-wf² hΦ (p ↦ q) =
    wf⇒ (⊑-tgt-wf² hΦ p) (⊑-tgt-wf² hΦ q)
  ⊑-tgt-wf² hΦ (∀ⁱ p) =
    wf∀ (⊑-tgt-wf² (∀ᵢ-wf² hΦ) p)
  ⊑-tgt-wf² hΦ (tag ι) = wf★
  ⊑-tgt-wf² hΦ (tag_⇛_ p q) = wf★
  ⊑-tgt-wf² hΦ (tagˣ X⊑★∈) = wf★
  ⊑-tgt-wf² hΦ (ν nonvar occA p) =
    WfTy-un⇑ᵗ (⊑-tgt-wf² (νᵢ-wf² hΦ) p)

⊑-src-wf :
  ∀ {Δ Φ A B} →
  WfImpCtx Δ Φ →
  Φ ⊢ A ⊑ B →
  WfTy Δ A
⊑-src-wf hΦ p = ⊑-src-wf² (WfImpCtx-to² hΦ) p

⊑-tgt-wf :
  ∀ {Δ Φ A B} →
  WfImpCtx Δ Φ →
  Φ ⊢ A ⊑ B →
  WfTy Δ B
⊑-tgt-wf hΦ p = ⊑-tgt-wf² (WfImpCtx-to² hΦ) p

⊑-src-wf-idᵢ :
  ∀ {Δ A B} →
  idᵢ Δ ⊢ A ⊑ B →
  WfTy Δ A
⊑-src-wf-idᵢ {Δ = Δ} = ⊑-src-wf (idᵢ-wf Δ)

⊑-tgt-wf-idᵢ :
  ∀ {Δ A B} →
  idᵢ Δ ⊢ A ⊑ B →
  WfTy Δ B
⊑-tgt-wf-idᵢ {Δ = Δ} = ⊑-tgt-wf (idᵢ-wf Δ)

------------------------------------------------------------------------
-- Target-shape inversion under the identity imprecision context
------------------------------------------------------------------------

true≢false : true ≡ false → ⊥
true≢false ()

⊑-to-base-occurs-false :
  ∀ {Φ C ι} X →
  Φ ⊢ C ⊑ ‵ ι →
  occurs X C ≡ false
⊑-to-base-occurs-false X idι = refl
⊑-to-base-occurs-false X (ν nonvar occ p) =
  ⊑-to-base-occurs-false (suc X) p

NoVarLeft : ImpCtx → TyVar → Set
NoVarLeft Φ X = ∀ {Y} → (X ˣ⊑ˣ Y) ∈ Φ → ⊥

un⇑ᴸᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᴸᵢ-ˣ∈ {Φ = []} ()
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-ˣ∈ x∈)
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  there (un⇑ᴸᵢ-ˣ∈ x∈)

no-⇑ᴸᵢ-zero-left :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-left {Φ = []} ()
no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈
no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈

νctx-no-var-left-zero :
  ∀ {Φ} →
  NoVarLeft ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) zero
νctx-no-var-left-zero (there x∈) = no-⇑ᵢ-zero-left x∈

νctx-no-var-left-suc :
  ∀ {Φ X} →
  NoVarLeft Φ X →
  NoVarLeft ((zero ˣ⊑★) ∷ ⇑ᵢ Φ) (suc X)
νctx-no-var-left-suc noX {Y = zero} (there x∈) =
  no-⇑ᵢ-zero-right x∈
νctx-no-var-left-suc noX {Y = suc Y} (there x∈) =
  noX (un⇑ᵢ-ˣ∈ x∈)

⊑-to-var-occurs-false :
  ∀ {Φ C X} Y →
  NoVarLeft Φ Y →
  Φ ⊢ C ⊑ ＇ X →
  occurs Y C ≡ false
⊑-to-var-occurs-false Y noY (idˣ {X = z} x∈) with Y ≟ z
⊑-to-var-occurs-false Y noY (idˣ {X = .Y} x∈) | yes refl =
  ⊥-elim (noY x∈)
⊑-to-var-occurs-false Y noY (idˣ {X = z} x∈) | no Y≢z = refl
⊑-to-var-occurs-false Y noY (ν nonvar occ p) =
  ⊑-to-var-occurs-false (suc Y) (νctx-no-var-left-suc noY) p

⊑-base-inv-idᵢ :
  ∀ {Δ C ι} →
  idᵢ Δ ⊢ C ⊑ ‵ ι →
  C ≡ ‵ ι
⊑-base-inv-idᵢ idι = refl
⊑-base-inv-idᵢ (ν nonvar occ p) =
  ⊥-elim (true≢false (trans (sym occ)
    (⊑-to-base-occurs-false zero p)))

⊑-var-inv-idᵢ :
  ∀ {Δ C X} →
  idᵢ Δ ⊢ C ⊑ ＇ X →
  C ≡ ＇ X
⊑-var-inv-idᵢ (idˣ x∈) rewrite idᵢ-var-identity x∈ = refl
⊑-var-inv-idᵢ (ν nonvar occ p) =
  ⊥-elim (true≢false (trans (sym occ)
    (⊑-to-var-occurs-false zero νctx-no-var-left-zero p)))

⊑-base-base-inv-idᵢ :
  ∀ {Δ ι κ} →
  idᵢ Δ ⊢ ‵ ι ⊑ ‵ κ →
  ι ≡ κ
⊑-base-base-inv-idᵢ p with ⊑-base-inv-idᵢ p
⊑-base-base-inv-idᵢ p | refl = refl

⊑-var-var-inv-idᵢ :
  ∀ {Δ X Y} →
  idᵢ Δ ⊢ ＇ X ⊑ ＇ Y →
  X ≡ Y
⊑-var-var-inv-idᵢ p with ⊑-var-inv-idᵢ p
⊑-var-var-inv-idᵢ p | refl = refl

data ArrowTargetInv (Δ : TyCtx) : Ty → Ty → Ty → Set where
  arrow-target-↦ :
    ∀ {A B C D} →
    idᵢ Δ ⊢ C ⊑ A →
    idᵢ Δ ⊢ D ⊑ B →
    ArrowTargetInv Δ (C ⇒ D) A B

  arrow-target-ν :
    ∀ {A B C} →
    NonVar C →
    (occ : occurs zero C ≡ true) →
    (zero ˣ⊑★) ∷ ⇑ᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (A ⇒ B) →
    ArrowTargetInv Δ (`∀ C) A B

⊑-arrow-inv-idᵢ :
  ∀ {Δ C A B} →
  idᵢ Δ ⊢ C ⊑ A ⇒ B →
  ArrowTargetInv Δ C A B
⊑-arrow-inv-idᵢ (p ↦ q) = arrow-target-↦ p q
⊑-arrow-inv-idᵢ (ν nonvar occ p) = arrow-target-ν nonvar occ p

data ForallTargetInv (Δ : TyCtx) : Ty → Ty → Set where
  forall-target-∀ⁱ :
    ∀ {A C} →
    (zero ˣ⊑ˣ zero) ∷ ⇑ᵢ (idᵢ Δ) ⊢ C ⊑ A →
    ForallTargetInv Δ (`∀ C) A

  forall-target-ν :
    ∀ {A C} →
    NonVar C →
    (occ : occurs zero C ≡ true) →
    (zero ˣ⊑★) ∷ ⇑ᵢ (idᵢ Δ) ⊢ C ⊑ ⇑ᵗ (`∀ A) →
    ForallTargetInv Δ (`∀ C) A

⊑-forall-inv-idᵢ :
  ∀ {Δ C A} →
  idᵢ Δ ⊢ C ⊑ `∀ A →
  ForallTargetInv Δ C A
⊑-forall-inv-idᵢ (∀ⁱ p) = forall-target-∀ⁱ p
⊑-forall-inv-idᵢ (ν nonvar occ p) =
  forall-target-ν nonvar occ p

⊑-base-var-⊥ :
  ∀ {Δ ι X} →
  idᵢ Δ ⊢ ‵ ι ⊑ ＇ X →
  ⊥
⊑-base-var-⊥ ()

⊑-var-base-⊥ :
  ∀ {Δ X ι} →
  idᵢ Δ ⊢ ＇ X ⊑ ‵ ι →
  ⊥
⊑-var-base-⊥ ()

⊑-base-arrow-⊥ :
  ∀ {Δ ι A B} →
  idᵢ Δ ⊢ ‵ ι ⊑ A ⇒ B →
  ⊥
⊑-base-arrow-⊥ ()

⊑-arrow-base-⊥ :
  ∀ {Δ A B ι} →
  idᵢ Δ ⊢ A ⇒ B ⊑ ‵ ι →
  ⊥
⊑-arrow-base-⊥ ()

⊑-base-forall-⊥ :
  ∀ {Δ ι A} →
  idᵢ Δ ⊢ ‵ ι ⊑ `∀ A →
  ⊥
⊑-base-forall-⊥ ()

⊑-forall-base-⊥ :
  ∀ {Δ A ι} →
  idᵢ Δ ⊢ `∀ A ⊑ ‵ ι →
  ⊥
⊑-forall-base-⊥ p with ⊑-base-inv-idᵢ p
⊑-forall-base-⊥ p | ()

⊑-var-arrow-⊥ :
  ∀ {Δ X A B} →
  idᵢ Δ ⊢ ＇ X ⊑ A ⇒ B →
  ⊥
⊑-var-arrow-⊥ ()

⊑-arrow-var-⊥ :
  ∀ {Δ A B X} →
  idᵢ Δ ⊢ A ⇒ B ⊑ ＇ X →
  ⊥
⊑-arrow-var-⊥ ()

⊑-var-forall-⊥ :
  ∀ {Δ X A} →
  idᵢ Δ ⊢ ＇ X ⊑ `∀ A →
  ⊥
⊑-var-forall-⊥ ()

⊑-forall-var-⊥ :
  ∀ {Δ A X} →
  idᵢ Δ ⊢ `∀ A ⊑ ＇ X →
  ⊥
⊑-forall-var-⊥ p with ⊑-var-inv-idᵢ p
⊑-forall-var-⊥ p | ()

⊑-arrow-forall-⊥ :
  ∀ {Δ A B C} →
  idᵢ Δ ⊢ A ⇒ B ⊑ `∀ C →
  ⊥
⊑-arrow-forall-⊥ ()

⊑-var-star-⊥ :
  ∀ {Δ X} →
  idᵢ Δ ⊢ ＇ X ⊑ ★ →
  ⊥
⊑-var-star-⊥ (tagˣ x∈) = idᵢ-no-star x∈

⊑-star-base-⊥ :
  ∀ {Δ ι} →
  idᵢ Δ ⊢ ★ ⊑ ‵ ι →
  ⊥
⊑-star-base-⊥ ()

⊑-star-var-⊥ :
  ∀ {Δ X} →
  idᵢ Δ ⊢ ★ ⊑ ＇ X →
  ⊥
⊑-star-var-⊥ ()

⊑-star-arrow-⊥ :
  ∀ {Δ A B} →
  idᵢ Δ ⊢ ★ ⊑ A ⇒ B →
  ⊥
⊑-star-arrow-⊥ ()

------------------------------------------------------------------------
-- Reflexivity and consistency
------------------------------------------------------------------------

⊑-refl-idᵢ :
  ∀ {Δ A} →
  WfTy Δ A →
  idᵢ Δ ⊢ A ⊑ A
⊑-refl-idᵢ (wfVar X<Δ) = idˣ (idᵢ-lookup X<Δ)
⊑-refl-idᵢ wfBase = idι
⊑-refl-idᵢ wf★ = id★
⊑-refl-idᵢ (wf⇒ hA hB) = ⊑-refl-idᵢ hA ↦ ⊑-refl-idᵢ hB
⊑-refl-idᵢ (wf∀ hA) = ∀ⁱ (⊑-refl-idᵢ hA)

~-sym :
  ∀ {Δ A B} →
  Δ ⊢ A ~ B →
  Δ ⊢ B ~ A
~-sym (C , C⊑A , C⊑B) = C , C⊑B , C⊑A

~-refl :
  ∀ {Δ A} →
  WfTy Δ A →
  Δ ⊢ A ~ A
~-refl {A = A} hA = A , ⊑-refl-idᵢ hA , ⊑-refl-idᵢ hA

~-left-wf :
  ∀ {Δ A B} →
  Δ ⊢ A ~ B →
  WfTy Δ A
~-left-wf (C , C⊑A , C⊑B) = ⊑-tgt-wf-idᵢ C⊑A

~-right-wf :
  ∀ {Δ A B} →
  Δ ⊢ A ~ B →
  WfTy Δ B
~-right-wf (C , C⊑A , C⊑B) = ⊑-tgt-wf-idᵢ C⊑B

~-lower-wf :
  ∀ {Δ A B C} →
  idᵢ Δ ⊢ C ⊑ A →
  idᵢ Δ ⊢ C ⊑ B →
  WfTy Δ C
~-lower-wf C⊑A C⊑B = ⊑-src-wf-idᵢ C⊑A
