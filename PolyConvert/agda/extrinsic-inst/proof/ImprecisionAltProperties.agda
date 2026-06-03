module proof.ImprecisionAltProperties where

-- File Charter:
--   * Properties of the alternative type-imprecision relation.
--   * Reflexivity under contexts that contain in-bounds reflexive
--     variable imprecision assumptions, plus closed reflexivity.
--   * Transitivity (under construction)

open import Types
open import ImprecisionAlt

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (false; true; _∨_)
open import Data.List using ([]; length; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (≤-antisym; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; refl; subst; sym; trans)

------------------------------------------------------------------------
-- Reflexive
------------------------------------------------------------------------

length-⇑ᵢ : ∀ Φ → length (⇑ᵢ Φ) ≡ length Φ
length-⇑ᵢ [] = refl
length-⇑ᵢ (_ ∷ Φ) = cong suc (length-⇑ᵢ Φ)

length-⇑ᴸᵢ : ∀ Φ → length (⇑ᴸᵢ Φ) ≡ length Φ
length-⇑ᴸᵢ [] = refl
length-⇑ᴸᵢ (_ ∷ Φ) = cong suc (length-⇑ᴸᵢ Φ)

⇑ᵢ-refl∈ :
  ∀ {Φ X} →
  (X ˣ⊑ˣ X) ∈ Φ →
  (suc X ˣ⊑ˣ suc X) ∈ ⇑ᵢ Φ
⇑ᵢ-refl∈ (here refl) = here refl
⇑ᵢ-refl∈ (there X⊑X∈) = there (⇑ᵢ-refl∈ X⊑X∈)

⇑ᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ
⇑ᵢ-ˣ∈ (here refl) = here refl
⇑ᵢ-ˣ∈ (there X⊑Y∈) = there (⇑ᵢ-ˣ∈ X⊑Y∈)

⇑ᵢ-★∈ :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᵢ Φ
⇑ᵢ-★∈ (here refl) = here refl
⇑ᵢ-★∈ (there X⊑★∈) = there (⇑ᵢ-★∈ X⊑★∈)

un⇑ᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ suc Y) ∈ ⇑ᵢ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᵢ-ˣ∈ {Φ = []} ()
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there X⊑Y∈) =
  there (un⇑ᵢ-ˣ∈ X⊑Y∈)
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X⊑Y∈) =
  there (un⇑ᵢ-ˣ∈ X⊑Y∈)

un⇑ᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᵢ-★∈ {Φ = []} ()
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there X⊑★∈) =
  there (un⇑ᵢ-★∈ X⊑★∈)
un⇑ᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X⊑★∈) =
  there (un⇑ᵢ-★∈ X⊑★∈)

⇑ᴸᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-ˣ∈ (here refl) = here refl
⇑ᴸᵢ-ˣ∈ (there X⊑Y∈) = there (⇑ᴸᵢ-ˣ∈ X⊑Y∈)

⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (X ˣ⊑★) ∈ Φ →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢ-★∈ (here refl) = here refl
⇑ᴸᵢ-★∈ (there X⊑★∈) = there (⇑ᴸᵢ-★∈ X⊑★∈)

un⇑ᴸᵢ-ˣ∈ :
  ∀ {Φ X Y} →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ
un⇑ᴸᵢ-ˣ∈ {Φ = []} ()
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there X⊑Y∈) =
  there (un⇑ᴸᵢ-ˣ∈ X⊑Y∈)
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-ˣ∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X⊑Y∈) =
  there (un⇑ᴸᵢ-ˣ∈ X⊑Y∈)

un⇑ᴸᵢ-★∈ :
  ∀ {Φ X} →
  (suc X ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  (X ˣ⊑★) ∈ Φ
un⇑ᴸᵢ-★∈ {Φ = []} ()
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (here refl) = here refl
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑★) ∷ Φ} (there X⊑★∈) =
  there (un⇑ᴸᵢ-★∈ X⊑★∈)
un⇑ᴸᵢ-★∈ {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there X⊑★∈) =
  there (un⇑ᴸᵢ-★∈ X⊑★∈)

no-⇑ᵢ-zero-left :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ Y) ∈ ⇑ᵢ Φ →
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

no-⇑ᴸᵢ-zero-left :
  ∀ {Φ Y} →
  (zero ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-left {Φ = []} ()
no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈
no-⇑ᴸᵢ-zero-left {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-left x∈

no-⇑ᴸᵢ-zero-star :
  ∀ {Φ} →
  (zero ˣ⊑★) ∈ ⇑ᴸᵢ Φ →
  ⊥
no-⇑ᴸᵢ-zero-star {Φ = []} ()
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑★) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈
no-⇑ᴸᵢ-zero-star {Φ = (_ ˣ⊑ˣ _) ∷ Φ} (there x∈) =
  no-⇑ᴸᵢ-zero-star x∈

ReflImpCtx : ImpCtx → Set
ReflImpCtx Φ = ∀ {X} → X < length Φ → (X ˣ⊑ˣ X) ∈ Φ

⊑-refl :
  ∀ {Ψ Φ A} →
  ReflImpCtx Φ →
  WfTy (length Φ) Ψ A →
  Ψ ∣ Φ ⊢ A ⊑ A
⊑-refl reflΦ (wfVar {X = X} X<Φ) = idˣ (reflΦ {X = X} X<Φ)
⊑-refl reflΦ (wfSeal α<Ψ) = idα (wfSeal α<Ψ)
⊑-refl reflΦ wfBase = idι
⊑-refl reflΦ wf★ = id★
⊑-refl reflΦ (wf⇒ wfA wfB) = ⊑-refl reflΦ wfA ↦ ⊑-refl reflΦ wfB
⊑-refl {Ψ = Ψ} {Φ = Φ} {A = `∀ A} reflΦ (wf∀ wfA) =
  ∀ⁱ ⊑-refl reflΦ′ wfA′
  where
  reflΦ′ : ReflImpCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)
  reflΦ′ {zero} z<s = here refl
  reflΦ′ {suc X} (s<s X<⇑Φ) =
    there
      (⇑ᵢ-refl∈
        (reflΦ (subst (λ n → X < n) (length-⇑ᵢ Φ) X<⇑Φ)))

  wfA′ : WfTy (length ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)) Ψ A
  wfA′ = subst (λ n → WfTy n Ψ A) (sym (cong suc (length-⇑ᵢ Φ))) wfA

ReflImpCtx-[] : ReflImpCtx []
ReflImpCtx-[] ()

⊑-refl-closed :
  ∀ {Ψ A} →
  WfTy 0 Ψ A →
  Ψ ∣ [] ⊢ A ⊑ A
⊑-refl-closed = ⊑-refl ReflImpCtx-[]

------------------------------------------------------------------------
-- Imprecision to ★
------------------------------------------------------------------------

StarImpCtx : ImpCtx → Set
StarImpCtx Φ = ∀ {X} → X < length Φ → (X ˣ⊑★) ∈ Φ

StarImpCtx-[] : StarImpCtx []
StarImpCtx-[] ()

StarImpCtx-ν :
  ∀ {Φ} →
  StarImpCtx Φ →
  StarImpCtx ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
StarImpCtx-ν starΦ {zero} z<s = here refl
StarImpCtx-ν {Φ = Φ} starΦ {suc X} (s<s X<⇑Φ) =
  there
    (⇑ᴸᵢ-★∈
      (starΦ (subst (λ n → X < n) (length-⇑ᴸᵢ Φ) X<⇑Φ)))

⊑★ :
  ∀ {Φ A} →
  StarImpCtx Φ →
  WfTy (length Φ) 0 A →
  0 ∣ Φ ⊢ A ⊑ ★
⊑★ starΦ (wfVar X<Φ) = tagˣ (starΦ X<Φ)
⊑★ starΦ (wfSeal ())
⊑★ starΦ wfBase = tag _
⊑★ starΦ wf★ = id★
⊑★ starΦ (wf⇒ wfA wfB) =
  tag_⇒_ (⊑★ starΦ wfA) (⊑★ starΦ wfB)
⊑★ {Φ = Φ} {A = `∀ A} starΦ (wf∀ {occ = occA} wfA) =
  ν occA (⊑★ (StarImpCtx-ν starΦ) wfA′)
  where
  wfA′ : WfTy (length ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ)) 0 A
  wfA′ =
    subst (λ n → WfTy n 0 A)
      (sym (cong suc (length-⇑ᴸᵢ Φ))) wfA

------------------------------------------------------------------------
-- Context closure for transitivity
------------------------------------------------------------------------

record ImpCtxClosed (Φ : ImpCtx) : Set where
  field
    transˣ :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Φ →
      (Y ˣ⊑ˣ Z) ∈ Φ →
      (X ˣ⊑ˣ Z) ∈ Φ

    starˣ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φ →
      (Y ˣ⊑★) ∈ Φ →
      (X ˣ⊑★) ∈ Φ

open ImpCtxClosed public

ImpCtxClosed-[] : ImpCtxClosed []
ImpCtxClosed-[] .transˣ ()
ImpCtxClosed-[] .starˣ ()

record ComposeCtx (Δ Φ : ImpCtx) : Set where
  field
    transˣᶜ :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Δ →
      (Y ˣ⊑ˣ Z) ∈ Φ →
      (X ˣ⊑ˣ Z) ∈ Δ

    starˣᶜ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Δ →
      (Y ˣ⊑★) ∈ Φ →
      (X ˣ⊑★) ∈ Δ

open ComposeCtx public

compose-refl : ∀ {Φ} → ImpCtxClosed Φ → ComposeCtx Φ Φ
compose-refl closed .transˣᶜ = ImpCtxClosed.transˣ closed
compose-refl closed .starˣᶜ = ImpCtxClosed.starˣ closed

⇑ᴸᵢ-trans∈ :
  ∀ {Δ Φ X Y Z} →
  ComposeCtx Δ Φ →
  (X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Δ →
  (Y ˣ⊑ˣ Z) ∈ Φ →
  (X ˣ⊑ˣ Z) ∈ ⇑ᴸᵢ Δ
⇑ᴸᵢ-trans∈ {X = zero} R x⊑y y⊑z =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
⇑ᴸᵢ-trans∈ {X = suc X} R x⊑y y⊑z =
  ⇑ᴸᵢ-ˣ∈ (transˣᶜ R (un⇑ᴸᵢ-ˣ∈ x⊑y) y⊑z)

⇑ᴸᵢ-star∈ :
  ∀ {Δ Φ X Y} →
  ComposeCtx Δ Φ →
  (X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Δ →
  (Y ˣ⊑★) ∈ Φ →
  (X ˣ⊑★) ∈ ⇑ᴸᵢ Δ
⇑ᴸᵢ-star∈ {X = zero} R x⊑y y⊑★ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
⇑ᴸᵢ-star∈ {X = suc X} R x⊑y y⊑★ =
  ⇑ᴸᵢ-★∈ (starˣᶜ R (un⇑ᴸᵢ-ˣ∈ x⊑y) y⊑★)

compose-ν :
  ∀ {Δ Φ} →
  ComposeCtx Δ Φ →
  ComposeCtx ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Δ) Φ
compose-ν R .transˣᶜ (here ())
compose-ν R .transˣᶜ (there x⊑y) y⊑z =
  there (⇑ᴸᵢ-trans∈ R x⊑y y⊑z)
compose-ν R .starˣᶜ (here ())
compose-ν R .starˣᶜ (there x⊑y) y⊑★ =
  there (⇑ᴸᵢ-star∈ R x⊑y y⊑★)

compose-∀ :
  ∀ {Δ Φ} →
  ComposeCtx Δ Φ →
  ComposeCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Δ) ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)
compose-∀ R .transˣᶜ (here refl) (here refl) = here refl
compose-∀ R .transˣᶜ (here refl) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-left y⊑z)
compose-∀ R .transˣᶜ (there x⊑y) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
compose-∀ R .transˣᶜ {Z = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right y⊑z)
compose-∀ R .transˣᶜ {Y = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
compose-∀ R .transˣᶜ {X = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
compose-∀ R .transˣᶜ
    {X = suc x} {Y = suc y} {Z = suc z}
    (there x⊑y) (there y⊑z) =
  there (⇑ᵢ-ˣ∈ (transˣᶜ R (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᵢ-ˣ∈ y⊑z)))
compose-∀ R .starˣᶜ (here refl) (there y⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star y⊑★)
compose-∀ R .starˣᶜ {Y = zero} (there x⊑y) (there y⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
compose-∀ R .starˣᶜ {X = zero} (there x⊑y) (there y⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
compose-∀ R .starˣᶜ
    {X = suc x} {Y = suc y}
    (there x⊑y) (there y⊑★) =
  there (⇑ᵢ-★∈ (starˣᶜ R (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᵢ-★∈ y⊑★)))

false≢true : false ≡ true → ⊥
false≢true ()

∨-trueˡ :
  ∀ {b c} →
  b ≡ true →
  b ∨ c ≡ true
∨-trueˡ {b = true} refl = refl
∨-trueˡ {b = false} ()

∨-trueʳ :
  ∀ {b c} →
  c ≡ true →
  b ∨ c ≡ true
∨-trueʳ {b = true} refl = refl
∨-trueʳ {b = false} eq = eq

∨-falseˡ :
  ∀ {b c} →
  b ≡ false →
  b ∨ c ≡ true →
  c ≡ true
∨-falseˡ {b = false} refl eq = eq
∨-falseˡ {b = true} () eq

occurs-same : ∀ X → occurs X (＇ X) ≡ true
occurs-same X with X ≟ X
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)

record Focus (Φ : ImpCtx) (X Y : TyVar) : Set where
  field
    hit : (X ˣ⊑ˣ Y) ∈ Φ
    unique : ∀ {Z} → (Z ˣ⊑ˣ Y) ∈ Φ → Z ≡ X

open Focus public

focus-plain-zero :
  ∀ {Φ} →
  Focus ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ) 0 0
focus-plain-zero .hit = here refl
focus-plain-zero .unique (here refl) = refl
focus-plain-zero .unique (there z⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right z⊑0)

focus-∀ :
  ∀ {Φ X Y} →
  Focus Φ X Y →
  Focus ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ) (suc X) (suc Y)
focus-∀ f .hit = there (⇑ᵢ-ˣ∈ (hit f))
focus-∀ f .unique (here ())
focus-∀ f .unique {Z = zero} (there z⊑sucY) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑sucY)
focus-∀ f .unique {Z = suc z} (there z⊑sucY)
  rewrite unique f (un⇑ᵢ-ˣ∈ z⊑sucY) =
  refl

focus-ν :
  ∀ {Φ X Y} →
  Focus Φ X Y →
  Focus ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc X) Y
focus-ν f .hit = there (⇑ᴸᵢ-ˣ∈ (hit f))
focus-ν f .unique {Z = zero} (there z⊑Y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left z⊑Y)
focus-ν f .unique {Z = suc z} (there z⊑Y)
  rewrite unique f (un⇑ᴸᵢ-ˣ∈ z⊑Y) =
  refl

target-occurs-source-focus :
  ∀ {Ψ Φ X Y A B} →
  Focus Φ X Y →
  Ψ ∣ Φ ⊢ A ⊑ B →
  occurs Y B ≡ true →
  occurs X A ≡ true
target-occurs-source-focus f id★ ()
target-occurs-source-focus {X = X} {Y = Y} f
    (idˣ {X = X′} {Y = Y′} x′⊑y′) occ
    with Y ≟ Y′
... | yes refl
    rewrite unique f x′⊑y′ =
  occurs-same X
... | no neq = ⊥-elim (false≢true occ)
target-occurs-source-focus f idι ()
target-occurs-source-focus f (idα wfα) ()
target-occurs-source-focus {X = X} {Y = Y} f
    (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} p q) occ
    with occurs X A in occXA | occurs X B in occXB | occurs Y A′ in occYA′
... | true | _ | _ = refl
... | false | true | _ = refl
... | false | false | true =
  ⊥-elim
    (false≢true
      (trans (sym occXA) (target-occurs-source-focus f p occYA′)))
... | false | false | false =
  ⊥-elim
    (false≢true
      (trans
        (sym occXB)
        (target-occurs-source-focus f q occ)))
target-occurs-source-focus f (∀ⁱ p) occ =
  target-occurs-source-focus (focus-∀ f) p occ
target-occurs-source-focus f (tag ι) ()
target-occurs-source-focus f (tag_⇒_ p q) ()
target-occurs-source-focus f (tagˣ x⊑★) ()
target-occurs-source-focus f (ν occA p) occ =
  target-occurs-source-focus (focus-ν f) p occ

plainν-target-occurs-source :
  ∀ {Ψ Φ A B} →
  Ψ ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B →
  occurs zero B ≡ true →
  occurs zero A ≡ true
plainν-target-occurs-source =
  target-occurs-source-focus focus-plain-zero

------------------------------------------------------------------------
-- Generic transitivity into an output context
------------------------------------------------------------------------

record TransCtx (Λ Ρ Ω : ImpCtx) : Set where
  field
    transˣᵗ :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Λ →
      (Y ˣ⊑ˣ Z) ∈ Ρ →
      (X ˣ⊑ˣ Z) ∈ Ω

    starˣᵗ :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Λ →
      (Y ˣ⊑★) ∈ Ρ →
      (X ˣ⊑★) ∈ Ω

    star-mapᵗ :
      ∀ {X} →
      (X ˣ⊑★) ∈ Λ →
      (X ˣ⊑★) ∈ Ω

    lengthᵗ : length Λ ≡ length Ω

open TransCtx public

TransCtx-compose : ∀ {Δ Φ} → ComposeCtx Δ Φ → TransCtx Δ Φ Δ
TransCtx-compose R .transˣᵗ = transˣᶜ R
TransCtx-compose R .starˣᵗ = starˣᶜ R
TransCtx-compose R .star-mapᵗ x⊑★ = x⊑★
TransCtx-compose R .lengthᵗ = refl

wf-lengthᵗ :
  ∀ {Ψ Λ Ρ Ω A} →
  TransCtx Λ Ρ Ω →
  WfTy (length Λ) Ψ A →
  WfTy (length Ω) Ψ A
wf-lengthᵗ T wfA = subst (λ n → WfTy n _ _) (lengthᵗ T) wfA

lift-left-νᵗ :
  ∀ {Λ Ρ Ω} →
  TransCtx Λ Ρ Ω →
  TransCtx ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Λ) Ρ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Ω)
lift-left-νᵗ T .transˣᵗ (here ()) y⊑z
lift-left-νᵗ T .transˣᵗ {X = zero} (there x⊑y) y⊑z =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
lift-left-νᵗ T .transˣᵗ {X = suc x} (there x⊑y) y⊑z =
  there (⇑ᴸᵢ-ˣ∈ (transˣᵗ T (un⇑ᴸᵢ-ˣ∈ x⊑y) y⊑z))
lift-left-νᵗ T .starˣᵗ (here ()) y⊑★
lift-left-νᵗ T .starˣᵗ {X = zero} (there x⊑y) y⊑★ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
lift-left-νᵗ T .starˣᵗ {X = suc x} (there x⊑y) y⊑★ =
  there (⇑ᴸᵢ-★∈ (starˣᵗ T (un⇑ᴸᵢ-ˣ∈ x⊑y) y⊑★))
lift-left-νᵗ T .star-mapᵗ (here refl) = here refl
lift-left-νᵗ T .star-mapᵗ {X = zero} (there x⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x⊑★)
lift-left-νᵗ T .star-mapᵗ {X = suc x} (there x⊑★) =
  there (⇑ᴸᵢ-★∈ (star-mapᵗ T (un⇑ᴸᵢ-★∈ x⊑★)))
lift-left-νᵗ {Λ = Λ} {Ω = Ω} T .lengthᵗ =
  cong suc
    (trans (length-⇑ᴸᵢ Λ) (trans (lengthᵗ T) (sym (length-⇑ᴸᵢ Ω))))

lift-∀ᵗ :
  ∀ {Λ Ρ Ω} →
  TransCtx Λ Ρ Ω →
  TransCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Λ)
           ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Ρ)
           ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Ω)
lift-∀ᵗ T .transˣᵗ (here refl) (here refl) = here refl
lift-∀ᵗ T .transˣᵗ (here refl) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-left y⊑z)
lift-∀ᵗ T .transˣᵗ (there x⊑y) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
lift-∀ᵗ T .transˣᵗ {Z = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right y⊑z)
lift-∀ᵗ T .transˣᵗ {Y = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
lift-∀ᵗ T .transˣᵗ {X = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
lift-∀ᵗ T .transˣᵗ
    {X = suc x} {Y = suc y} {Z = suc z}
    (there x⊑y) (there y⊑z) =
  there (⇑ᵢ-ˣ∈ (transˣᵗ T (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᵢ-ˣ∈ y⊑z)))
lift-∀ᵗ T .starˣᵗ (here refl) (there y⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star y⊑★)
lift-∀ᵗ T .starˣᵗ {Y = zero} (there x⊑y) (there y⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
lift-∀ᵗ T .starˣᵗ {X = zero} (there x⊑y) (there y⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
lift-∀ᵗ T .starˣᵗ
    {X = suc x} {Y = suc y}
    (there x⊑y) (there y⊑★) =
  there (⇑ᵢ-★∈ (starˣᵗ T (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᵢ-★∈ y⊑★)))
lift-∀ᵗ T .star-mapᵗ {X = zero} (there x⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star x⊑★)
lift-∀ᵗ T .star-mapᵗ {X = suc x} (there x⊑★) =
  there (⇑ᵢ-★∈ (star-mapᵗ T (un⇑ᵢ-★∈ x⊑★)))
lift-∀ᵗ {Λ = Λ} {Ω = Ω} T .lengthᵗ =
  cong suc
    (trans (length-⇑ᵢ Λ) (trans (lengthᵗ T) (sym (length-⇑ᵢ Ω))))

lift-∀νᵗ :
  ∀ {Λ Ρ Ω} →
  TransCtx Λ Ρ Ω →
  TransCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Λ)
           ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Ρ)
           ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Ω)
lift-∀νᵗ T .transˣᵗ (here refl) (there y⊑z) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left y⊑z)
lift-∀νᵗ T .transˣᵗ (there x⊑y) (here ())
lift-∀νᵗ T .transˣᵗ {Y = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
lift-∀νᵗ T .transˣᵗ {X = zero} (there x⊑y) (there y⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
lift-∀νᵗ T .transˣᵗ
    {X = suc x} {Y = suc y}
    (there x⊑y) (there y⊑z) =
  there (⇑ᴸᵢ-ˣ∈ (transˣᵗ T (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-ˣ∈ y⊑z)))
lift-∀νᵗ T .starˣᵗ (here refl) (here refl) = here refl
lift-∀νᵗ T .starˣᵗ (here refl) (there y⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star y⊑★)
lift-∀νᵗ T .starˣᵗ {Y = zero} (there x⊑y) y⊑★ =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
lift-∀νᵗ T .starˣᵗ {X = zero} (there x⊑y) y⊑★ =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
lift-∀νᵗ T .starˣᵗ
    {X = suc x} {Y = suc y}
    (there x⊑y) (there y⊑★) =
  there (⇑ᴸᵢ-★∈ (starˣᵗ T (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-★∈ y⊑★)))
lift-∀νᵗ T .star-mapᵗ {X = zero} (there x⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star x⊑★)
lift-∀νᵗ T .star-mapᵗ {X = suc x} (there x⊑★) =
  there (⇑ᴸᵢ-★∈ (star-mapᵗ T (un⇑ᵢ-★∈ x⊑★)))
lift-∀νᵗ {Λ = Λ} {Ω = Ω} T .lengthᵗ =
  cong suc
    (trans (length-⇑ᵢ Λ) (trans (lengthᵗ T) (sym (length-⇑ᴸᵢ Ω))))

mutual
  transport-to-starᵗ :
    ∀ {Ψ Λ Ρ Ω A} →
    TransCtx Λ Ρ Ω →
    Ψ ∣ Λ ⊢ A ⊑ ★ →
    Ψ ∣ Ω ⊢ A ⊑ ★
  transport-to-starᵗ T id★ = id★
  transport-to-starᵗ T (tag ι) = tag ι
  transport-to-starᵗ T (tag_⇒_ p q) =
    tag_⇒_ (transport-to-starᵗ T p) (transport-to-starᵗ T q)
  transport-to-starᵗ T (tagˣ x⊑★) = tagˣ (star-mapᵗ T x⊑★)
  transport-to-starᵗ T (ν occA p) =
    ν occA (transport-to-starᵗ (lift-left-νᵗ T) p)

  transport-to-groundᵗ :
    ∀ {Ψ Λ Ρ Ω A G} →
    TransCtx Λ Ρ Ω →
    Ground G →
    Ψ ∣ Λ ⊢ A ⊑ G →
    Ψ ∣ Ω ⊢ A ⊑ G
  transport-to-groundᵗ T (｀ α) (idα wfα) =
    idα (wf-lengthᵗ T wfα)
  transport-to-groundᵗ T (‵ ι) idι = idι
  transport-to-groundᵗ T ★⇒★ (p ↦ q) =
    transport-to-starᵗ T p ↦ transport-to-starᵗ T q
  transport-to-groundᵗ T g (ν occA p) =
    ν occA (transport-to-groundᵗ (lift-left-νᵗ T) g p)

  ⊑-trans-target-varᵗ :
    ∀ {Ψ Λ Ρ Ω A Y Z} →
    TransCtx Λ Ρ Ω →
    Ψ ∣ Λ ⊢ A ⊑ ＇ Y →
    (Y ˣ⊑ˣ Z) ∈ Ρ →
    Ψ ∣ Ω ⊢ A ⊑ ＇ Z
  ⊑-trans-target-varᵗ T (idˣ x⊑y) y⊑z =
    idˣ (transˣᵗ T x⊑y y⊑z)
  ⊑-trans-target-varᵗ T (ν occA p) y⊑z =
    ν occA (⊑-trans-target-varᵗ (lift-left-νᵗ T) p y⊑z)

  ⊑-trans-target-starᵗ :
    ∀ {Ψ Λ Ρ Ω A Y} →
    TransCtx Λ Ρ Ω →
    Ψ ∣ Λ ⊢ A ⊑ ＇ Y →
    (Y ˣ⊑★) ∈ Ρ →
    Ψ ∣ Ω ⊢ A ⊑ ★
  ⊑-trans-target-starᵗ T (idˣ x⊑y) y⊑★ =
    tagˣ (starˣᵗ T x⊑y y⊑★)
  ⊑-trans-target-starᵗ T (ν occA p) y⊑★ =
    ν occA (⊑-trans-target-starᵗ (lift-left-νᵗ T) p y⊑★)

  ⊑-trans-withᵗ :
    ∀ {Ψ Λ Ρ Ω A B C} →
    TransCtx Λ Ρ Ω →
    Ψ ∣ Λ ⊢ A ⊑ B →
    Ψ ∣ Ρ ⊢ B ⊑ C →
    Ψ ∣ Ω ⊢ A ⊑ C
  ⊑-trans-withᵗ T (ν occA p) q =
    ν occA (⊑-trans-withᵗ (lift-left-νᵗ T) p q)
  ⊑-trans-withᵗ T p id★ = transport-to-starᵗ T p
  ⊑-trans-withᵗ T p (idˣ y⊑z) =
    ⊑-trans-target-varᵗ T p y⊑z
  ⊑-trans-withᵗ T p idι =
    transport-to-groundᵗ T (‵ _) p
  ⊑-trans-withᵗ T p (idα wfα) =
    transport-to-groundᵗ T (｀ _) p
  ⊑-trans-withᵗ T (p₁ ↦ p₂) (q₁ ↦ q₂) =
    ⊑-trans-withᵗ T p₁ q₁ ↦ ⊑-trans-withᵗ T p₂ q₂
  ⊑-trans-withᵗ T (∀ⁱ p) (∀ⁱ q) =
    ∀ⁱ ⊑-trans-withᵗ (lift-∀ᵗ T) p q
  ⊑-trans-withᵗ T idι (tag ι) = tag ι
  ⊑-trans-withᵗ T (p₁ ↦ p₂) (tag_⇒_ q₁ q₂) =
    tag_⇒_ (⊑-trans-withᵗ T p₁ q₁) (⊑-trans-withᵗ T p₂ q₂)
  ⊑-trans-withᵗ T p (tagˣ y⊑★) =
    ⊑-trans-target-starᵗ T p y⊑★
  ⊑-trans-withᵗ T (∀ⁱ p) (ν occB q) =
    ν (plainν-target-occurs-source p occB)
      (⊑-trans-withᵗ (lift-∀νᵗ T) p q)

mutual
  ⊑-trans-target-var :
    ∀ {Ψ Δ Φ A Y Z} →
    ComposeCtx Δ Φ →
    Ψ ∣ Δ ⊢ A ⊑ ＇ Y →
    (Y ˣ⊑ˣ Z) ∈ Φ →
    Ψ ∣ Δ ⊢ A ⊑ ＇ Z
  ⊑-trans-target-var R (idˣ x⊑y) y⊑z =
    idˣ (transˣᶜ R x⊑y y⊑z)
  ⊑-trans-target-var R (ν occA p) y⊑z =
    ν occA (⊑-trans-target-var (compose-ν R) p y⊑z)

  ⊑-trans-target-star :
    ∀ {Ψ Δ Φ A Y} →
    ComposeCtx Δ Φ →
    Ψ ∣ Δ ⊢ A ⊑ ＇ Y →
    (Y ˣ⊑★) ∈ Φ →
    Ψ ∣ Δ ⊢ A ⊑ ★
  ⊑-trans-target-star R (idˣ x⊑y) y⊑★ =
    tagˣ (starˣᶜ R x⊑y y⊑★)
  ⊑-trans-target-star R (ν occA p) y⊑★ =
    ν occA (⊑-trans-target-star (compose-ν R) p y⊑★)

  ⊑-trans-compose :
    ∀ {Ψ Δ Φ A B C} →
    ComposeCtx Δ Φ →
    Ψ ∣ Δ ⊢ A ⊑ B →
    Ψ ∣ Φ ⊢ B ⊑ C →
    Ψ ∣ Δ ⊢ A ⊑ C
  ⊑-trans-compose R (ν occA p) q =
    ν occA (⊑-trans-compose (compose-ν R) p q)
  ⊑-trans-compose R p id★ = p
  ⊑-trans-compose R p (idˣ y⊑z) =
    ⊑-trans-target-var R p y⊑z
  ⊑-trans-compose R p idι = p
  ⊑-trans-compose R p (idα wfα) = p
  ⊑-trans-compose R (p₁ ↦ p₂) (q₁ ↦ q₂) =
    ⊑-trans-compose R p₁ q₁ ↦ ⊑-trans-compose R p₂ q₂
  ⊑-trans-compose R (∀ⁱ p) (∀ⁱ q) =
    ∀ⁱ ⊑-trans-compose (compose-∀ R) p q
  ⊑-trans-compose R idι (tag ι) = tag ι
  ⊑-trans-compose R (p₁ ↦ p₂) (tag_⇒_ q₁ q₂) =
    tag_⇒_ (⊑-trans-compose R p₁ q₁) (⊑-trans-compose R p₂ q₂)
  ⊑-trans-compose R p (tagˣ y⊑★) =
    ⊑-trans-target-star R p y⊑★
  ⊑-trans-compose R (∀ⁱ p) (ν occB q) =
    ν (plainν-target-occurs-source p occB)
      (⊑-trans-withᵗ (lift-∀νᵗ (TransCtx-compose R)) p q)

⊑-trans :
  ∀ {Ψ Φ A B C} →
  ImpCtxClosed Φ →
  Ψ ∣ Φ ⊢ A ⊑ B →
  Ψ ∣ Φ ⊢ B ⊑ C →
  Ψ ∣ Φ ⊢ A ⊑ C
⊑-trans closed = ⊑-trans-compose (compose-refl closed)

⊑-trans-closed :
  ∀ {Ψ A B C} →
  Ψ ∣ [] ⊢ A ⊑ B →
  Ψ ∣ [] ⊢ B ⊑ C →
  Ψ ∣ [] ⊢ A ⊑ C
⊑-trans-closed = ⊑-trans ImpCtxClosed-[]

------------------------------------------------------------------------
-- Antisymmetry
------------------------------------------------------------------------

DownwardImpCtx : ImpCtx → Set
DownwardImpCtx Φ = ∀ {X Y} → (X ˣ⊑ˣ Y) ∈ Φ → Y ≤ X

≤-sucʳ :
  ∀ {m n} →
  m ≤ n →
  m ≤ suc n
≤-sucʳ z≤n = z≤n
≤-sucʳ (s≤s m≤n) = s≤s (≤-sucʳ m≤n)

suc≰ :
  ∀ {X} →
  suc X ≤ X →
  ⊥
suc≰ {zero} ()
suc≰ {suc X} (s≤s sucX≤X) = suc≰ sucX≤X

DownwardImpCtx-[] : DownwardImpCtx []
DownwardImpCtx-[] ()

DownwardImpCtx-∀ :
  ∀ {Φ} →
  DownwardImpCtx Φ →
  DownwardImpCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)
DownwardImpCtx-∀ downΦ (here refl) = z≤n
DownwardImpCtx-∀ downΦ {zero} (there x⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
DownwardImpCtx-∀ downΦ {suc X} {zero} (there x⊑y) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
DownwardImpCtx-∀ downΦ {suc X} {suc Y} (there x⊑y) =
  s≤s (downΦ (un⇑ᵢ-ˣ∈ x⊑y))

DownwardImpCtx-ν :
  ∀ {Φ} →
  DownwardImpCtx Φ →
  DownwardImpCtx ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
DownwardImpCtx-ν downΦ (here ())
DownwardImpCtx-ν downΦ {zero} (there x⊑y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
DownwardImpCtx-ν downΦ {suc X} (there x⊑y) =
  ≤-sucʳ (downΦ (un⇑ᴸᵢ-ˣ∈ x⊑y))

DownwardImpCtx-antisymˣ :
  ∀ {Φ X Y} →
  DownwardImpCtx Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (Y ˣ⊑ˣ X) ∈ Φ →
  X ≡ Y
DownwardImpCtx-antisymˣ downΦ x⊑y y⊑x =
  ≤-antisym (downΦ y⊑x) (downΦ x⊑y)

DownwardImpCtx-no-ν-cycle :
  ∀ {Φ X Y} →
  DownwardImpCtx Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  (Y ˣ⊑ˣ suc X) ∈ Φ →
  ⊥
DownwardImpCtx-no-ν-cycle downΦ x⊑y y⊑sucX =
  suc≰ (≤-trans (downΦ y⊑sucX) (downΦ x⊑y))

DownwardImpCtx-no-ν-cross :
  ∀ {Φ X Y} →
  DownwardImpCtx Φ →
  (suc X ˣ⊑ˣ Y) ∈ ⇑ᴸᵢ Φ →
  (Y ˣ⊑ˣ suc X) ∈ Φ →
  ⊥
DownwardImpCtx-no-ν-cross downΦ sx⊑y y⊑sx =
  DownwardImpCtx-no-ν-cycle downΦ (un⇑ᴸᵢ-ˣ∈ sx⊑y) y⊑sx

leading∀ : Ty → ℕ
leading∀ (`∀ A) = suc (leading∀ A)
leading∀ _ = zero

⊑-leading∀ :
  ∀ {Ψ Φ A B} →
  Ψ ∣ Φ ⊢ A ⊑ B →
  leading∀ B ≤ leading∀ A
⊑-leading∀ id★ = z≤n
⊑-leading∀ (idˣ _) = z≤n
⊑-leading∀ idι = z≤n
⊑-leading∀ (idα _) = z≤n
⊑-leading∀ (_ ↦ _) = z≤n
⊑-leading∀ (∀ⁱ p) = s≤s (⊑-leading∀ p)
⊑-leading∀ (tag _) = z≤n
⊑-leading∀ (tag_⇒_ _ _) = z≤n
⊑-leading∀ (tagˣ _) = z≤n
⊑-leading∀ (ν _ p) = ≤-sucʳ (⊑-leading∀ p)

ν-antisym-⊥ :
  ∀ {Ψ Φ A B} →
  Ψ ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ ⊢ A ⊑ B →
  Ψ ∣ Φ ⊢ B ⊑ `∀ A →
  ⊥
ν-antisym-⊥ p q =
  suc≰ (≤-trans (⊑-leading∀ q) (⊑-leading∀ p))

⊑-antisym-down :
  ∀ {Ψ Φ A B} →
  DownwardImpCtx Φ →
  WfTy (length Φ) Ψ A →
  WfTy (length Φ) Ψ B →
  Ψ ∣ Φ ⊢ A ⊑ B →
  Ψ ∣ Φ ⊢ B ⊑ A →
  A ≡ B
⊑-antisym-down downΦ (wf∀ wfA) wfB (ν _ p) q =
  ⊥-elim (ν-antisym-⊥ p q)
⊑-antisym-down downΦ wfA (wf∀ wfB) p (ν _ q) =
  ⊥-elim (ν-antisym-⊥ q p)
⊑-antisym-down downΦ wf★ wf★ id★ id★ = refl
⊑-antisym-down downΦ (wfVar _) (wfVar _) (idˣ x⊑y) (idˣ y⊑x) =
  cong ＇_ (DownwardImpCtx-antisymˣ downΦ x⊑y y⊑x)
⊑-antisym-down downΦ wfBase wfBase idι idι = refl
⊑-antisym-down downΦ (wfSeal _) (wfSeal _) (idα _) (idα _) = refl
⊑-antisym-down downΦ (wf⇒ wfA₁ wfA₂) (wf⇒ wfB₁ wfB₂)
    (p₁ ↦ p₂) (q₁ ↦ q₂) =
  cong₂ _⇒_
    (⊑-antisym-down downΦ wfA₁ wfB₁ p₁ q₁)
    (⊑-antisym-down downΦ wfA₂ wfB₂ p₂ q₂)
⊑-antisym-down {Ψ = Ψ} {Φ = Φ} {A = `∀ A} {B = `∀ B} downΦ
    (wf∀ wfA) (wf∀ wfB) (∀ⁱ p) (∀ⁱ q) =
  cong `∀
    (⊑-antisym-down (DownwardImpCtx-∀ downΦ) wfA′ wfB′ p q)
  where
  wfA′ : WfTy (length ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)) Ψ A
  wfA′ =
    subst (λ n → WfTy n Ψ A) (sym (cong suc (length-⇑ᵢ Φ))) wfA

  wfB′ : WfTy (length ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)) Ψ B
  wfB′ =
    subst (λ n → WfTy n Ψ B) (sym (cong suc (length-⇑ᵢ Φ))) wfB
⊑-antisym-down downΦ wfBase wf★ (tag _) ()
⊑-antisym-down downΦ (wf⇒ _ _) wf★ (tag_⇒_ _ _) ()
⊑-antisym-down downΦ (wfVar _) wf★ (tagˣ _) ()
⊑-antisym-down downΦ wf★ wfBase () (tag _)
⊑-antisym-down downΦ wf★ (wf⇒ _ _) () (tag_⇒_ _ _)
⊑-antisym-down downΦ wf★ (wfVar _) () (tagˣ _)

⊑-antisym-closed :
  ∀ {Ψ A B} →
  WfTy 0 Ψ A →
  WfTy 0 Ψ B →
  Ψ ∣ [] ⊢ A ⊑ B →
  Ψ ∣ [] ⊢ B ⊑ A →
  A ≡ B
⊑-antisym-closed = ⊑-antisym-down DownwardImpCtx-[]

------------------------------------------------------------------------
-- Properties of Greatest Lower Bound (_⊢_＝_⊓_)
------------------------------------------------------------------------

⊓-lowerˡ :
  ∀ {Ψ A B C} →
  Ψ ⊢ A ＝ B ⊓ C →
  Ψ ∣ [] ⊢ A ⊑ B
⊓-lowerˡ = proj₁

⊓-lowerʳ :
  ∀ {Ψ A B C} →
  Ψ ⊢ A ＝ B ⊓ C →
  Ψ ∣ [] ⊢ A ⊑ C
⊓-lowerʳ glb = proj₁ (proj₂ glb)

⊓-greatest :
  ∀ {Ψ A B C} →
  Ψ ⊢ A ＝ B ⊓ C →
  ∀ A′ →
  Ψ ∣ [] ⊢ A′ ⊑ B →
  Ψ ∣ [] ⊢ A′ ⊑ C →
  Ψ ∣ [] ⊢ A′ ⊑ A
⊓-greatest glb = proj₂ (proj₂ glb)

⊓-intro :
  ∀ {Ψ A B C} →
  Ψ ∣ [] ⊢ A ⊑ B →
  Ψ ∣ [] ⊢ A ⊑ C →
  (∀ A′ →
   Ψ ∣ [] ⊢ A′ ⊑ B →
   Ψ ∣ [] ⊢ A′ ⊑ C →
   Ψ ∣ [] ⊢ A′ ⊑ A) →
  Ψ ⊢ A ＝ B ⊓ C
⊓-intro A⊑B A⊑C greatest = A⊑B , A⊑C , greatest

-- commutative

⊓-comm :
  ∀ {Ψ A B C} →
  Ψ ⊢ A ＝ B ⊓ C →
  Ψ ⊢ A ＝ C ⊓ B
⊓-comm glb =
  ⊓-intro (⊓-lowerʳ glb) (⊓-lowerˡ glb)
    (λ A′ A′⊑C A′⊑B → ⊓-greatest glb A′ A′⊑B A′⊑C)

-- idempotent

⊓-idempotent :
  ∀ {Ψ A} →
  WfTy 0 Ψ A →
  Ψ ⊢ A ＝ A ⊓ A
⊓-idempotent wfA =
  ⊓-intro (⊑-refl-closed wfA) (⊑-refl-closed wfA)
    (λ A′ A′⊑A _ → A′⊑A)

-- A ⊑ B iff A = A ⊓ B

⊑⇒⊓ :
  ∀ {Ψ A B} →
  WfTy 0 Ψ A →
  Ψ ∣ [] ⊢ A ⊑ B →
  Ψ ⊢ A ＝ A ⊓ B
⊑⇒⊓ wfA A⊑B =
  ⊓-intro (⊑-refl-closed wfA) A⊑B
    (λ A′ A′⊑A _ → A′⊑A)

⊓⇒⊑ :
  ∀ {Ψ A B} →
  Ψ ⊢ A ＝ A ⊓ B →
  Ψ ∣ [] ⊢ A ⊑ B
⊓⇒⊑ = ⊓-lowerʳ

⊑-iff-⊓ :
  ∀ {Ψ A B} →
  WfTy 0 Ψ A →
  (Ψ ∣ [] ⊢ A ⊑ B → Ψ ⊢ A ＝ A ⊓ B) ×
  (Ψ ⊢ A ＝ A ⊓ B → Ψ ∣ [] ⊢ A ⊑ B)
⊑-iff-⊓ wfA = ⊑⇒⊓ wfA , ⊓⇒⊑

-- A = A ⊓ ★

⊓-top :
  ∀ {A} →
  WfTy 0 0 A →
  0 ⊢ A ＝ A ⊓ ★
⊓-top wfA = ⊑⇒⊓ wfA (⊑★ StarImpCtx-[] wfA)

-- unique

⊓-unique :
  ∀ {Ψ A A′ B C} →
  WfTy 0 Ψ A →
  WfTy 0 Ψ A′ →
  Ψ ⊢ A ＝ B ⊓ C →
  Ψ ⊢ A′ ＝ B ⊓ C →
  A ≡ A′
⊓-unique wfA wfA′ glb glb′ =
  ⊑-antisym-closed wfA wfA′
    (⊓-greatest glb′ _ (⊓-lowerˡ glb) (⊓-lowerʳ glb))
    (⊓-greatest glb _ (⊓-lowerˡ glb′) (⊓-lowerʳ glb′))

-- associative

⊓-assoc-rebracket :
  ∀ {Ψ A B C AB BC ABC} →
  Ψ ⊢ AB ＝ A ⊓ B →
  Ψ ⊢ ABC ＝ AB ⊓ C →
  Ψ ⊢ BC ＝ B ⊓ C →
  Ψ ⊢ ABC ＝ A ⊓ BC
⊓-assoc-rebracket AB⊓B ABC⊓C BC⊓C =
  ⊓-intro
    (⊑-trans-closed (⊓-lowerˡ ABC⊓C) (⊓-lowerˡ AB⊓B))
    (⊓-greatest BC⊓C _
      (⊑-trans-closed (⊓-lowerˡ ABC⊓C) (⊓-lowerʳ AB⊓B))
      (⊓-lowerʳ ABC⊓C))
    (λ A′ A′⊑A A′⊑BC →
      ⊓-greatest ABC⊓C A′
        (⊓-greatest AB⊓B A′ A′⊑A
          (⊑-trans-closed A′⊑BC (⊓-lowerˡ BC⊓C)))
        (⊑-trans-closed A′⊑BC (⊓-lowerʳ BC⊓C)))

⊓-assoc :
  ∀ {Ψ A B C AB BC ABC ABC′} →
  WfTy 0 Ψ ABC →
  WfTy 0 Ψ ABC′ →
  Ψ ⊢ AB ＝ A ⊓ B →
  Ψ ⊢ ABC ＝ AB ⊓ C →
  Ψ ⊢ BC ＝ B ⊓ C →
  Ψ ⊢ ABC′ ＝ A ⊓ BC →
  ABC ≡ ABC′
⊓-assoc wfABC wfABC′ AB⊓B ABC⊓C BC⊓C ABC′⊓ =
  ⊓-unique wfABC wfABC′
    (⊓-assoc-rebracket AB⊓B ABC⊓C BC⊓C)
    ABC′⊓
