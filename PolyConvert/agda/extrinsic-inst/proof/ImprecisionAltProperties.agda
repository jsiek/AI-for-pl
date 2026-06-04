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
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
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

ReflImpCtx-∀ :
  ∀ {Φ} →
  ReflImpCtx Φ →
  ReflImpCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)
ReflImpCtx-∀ reflΦ {zero} z<s = here refl
ReflImpCtx-∀ {Φ = Φ} reflΦ {suc X} (s<s X<⇑Φ) =
  there
    (⇑ᵢ-refl∈
      (reflΦ (subst (λ n → X < n) (length-⇑ᵢ Φ) X<⇑Φ)))

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

data ∀Lower (Φ : ImpCtx) : Ty → Ty → Set where
  via-∀ :
    ∀ {A B} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B →
    ∀Lower Φ (`∀ A) B

  via-ν :
    ∀ {A B} →
    occurs zero A ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ ⊢ A ⊑ `∀ B →
    ∀Lower Φ (`∀ A) B

∀-lower-inv :
  ∀ {Φ A B} →
  0 ∣ Φ ⊢ A ⊑ `∀ B →
  ∀Lower Φ A B
∀-lower-inv (∀ⁱ p) = via-∀ p
∀-lower-inv (ν occA p) = via-ν occA p

data ∀SourceLower (Φ : ImpCtx) : Ty → Ty → Set where
  source-∀ :
    ∀ {A B} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B →
    ∀SourceLower Φ A (`∀ B)

  source-ν :
    ∀ {A B} →
    occurs zero A ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ ⊢ A ⊑ B →
    ∀SourceLower Φ A B

∀-source-lower-inv :
  ∀ {Φ A B} →
  0 ∣ Φ ⊢ `∀ A ⊑ B →
  ∀SourceLower Φ A B
∀-source-lower-inv (∀ⁱ p) = source-∀ p
∀-source-lower-inv (ν occA p) = source-ν occA p

data ∀Lower² (Φᴸ Φᴿ : ImpCtx) : Ty → Ty → Ty → Set where
  via-∀∀ :
    ∀ {A B C} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C ⊑ A →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C ⊑ B →
    ∀Lower² Φᴸ Φᴿ (`∀ C) A B

  via-∀ν :
    ∀ {A B C} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C ⊑ A →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C ⊑ `∀ B →
    ∀Lower² Φᴸ Φᴿ (`∀ C) A B

  via-ν∀ :
    ∀ {A B C} →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C ⊑ `∀ A →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C ⊑ B →
    ∀Lower² Φᴸ Φᴿ (`∀ C) A B

  via-νν :
    ∀ {A B C} →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C ⊑ `∀ A →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C ⊑ `∀ B →
    ∀Lower² Φᴸ Φᴿ (`∀ C) A B

∀∀-lower²-inv :
  ∀ {Φᴸ Φᴿ A B C} →
  0 ∣ Φᴸ ⊢ C ⊑ `∀ A →
  0 ∣ Φᴿ ⊢ C ⊑ `∀ B →
  ∀Lower² Φᴸ Φᴿ C A B
∀∀-lower²-inv (∀ⁱ p) (∀ⁱ q) = via-∀∀ p q
∀∀-lower²-inv (∀ⁱ p) (ν occC q) = via-∀ν p occC q
∀∀-lower²-inv (ν occC p) (∀ⁱ q) = via-ν∀ occC p q
∀∀-lower²-inv (ν occC p) (ν _ q) = via-νν occC p q

data ∀νLower² (Φᴸ Φᴿ : ImpCtx) : Ty → Ty → Ty → Set where
  via-∀∀ʳ :
    ∀ {A B C} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C ⊑ A →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C ⊑ B →
    ∀νLower² Φᴸ Φᴿ (`∀ C) A (`∀ B)

  via-∀νʳ :
    ∀ {A B C} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C ⊑ A →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C ⊑ B →
    ∀νLower² Φᴸ Φᴿ (`∀ C) A B

  via-νˡ :
    ∀ {A B C} →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C ⊑ `∀ A →
    0 ∣ Φᴿ ⊢ `∀ C ⊑ B →
    ∀νLower² Φᴸ Φᴿ (`∀ C) A B

∀ν-lower²-inv :
  ∀ {Φᴸ Φᴿ A B C} →
  0 ∣ Φᴸ ⊢ C ⊑ `∀ A →
  0 ∣ Φᴿ ⊢ C ⊑ B →
  ∀νLower² Φᴸ Φᴿ C A B
∀ν-lower²-inv (∀ⁱ p) q with ∀-source-lower-inv q
∀ν-lower²-inv (∀ⁱ p) q | source-∀ r = via-∀∀ʳ p r
∀ν-lower²-inv (∀ⁱ p) q | source-ν occC r = via-∀νʳ p occC r
∀ν-lower²-inv (ν occC p) q = via-νˡ occC p q

data ν∀Lower² (Φᴸ Φᴿ : ImpCtx) : Ty → Ty → Ty → Set where
  via-∀∀ˡ :
    ∀ {A B C} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C ⊑ A →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C ⊑ B →
    ν∀Lower² Φᴸ Φᴿ (`∀ C) (`∀ A) B

  via-ν∀ˡ :
    ∀ {A B C} →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C ⊑ A →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C ⊑ B →
    ν∀Lower² Φᴸ Φᴿ (`∀ C) A B

  via-νʳ :
    ∀ {A B C} →
    occurs zero C ≡ true →
    0 ∣ Φᴸ ⊢ `∀ C ⊑ A →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C ⊑ `∀ B →
    ν∀Lower² Φᴸ Φᴿ (`∀ C) A B

ν∀-lower²-inv :
  ∀ {Φᴸ Φᴿ A B C} →
  0 ∣ Φᴸ ⊢ C ⊑ A →
  0 ∣ Φᴿ ⊢ C ⊑ `∀ B →
  ν∀Lower² Φᴸ Φᴿ C A B
ν∀-lower²-inv p (∀ⁱ q) with ∀-source-lower-inv p
ν∀-lower²-inv p (∀ⁱ q) | source-∀ r = via-∀∀ˡ r q
ν∀-lower²-inv p (∀ⁱ q) | source-ν occC r = via-ν∀ˡ occC r q
ν∀-lower²-inv p (ν occC q) = via-νʳ occC p q

record Glbᶜ (Φᴸ Φᴿ Φᴼ : ImpCtx) (C A B : Ty) : Set where
  field
    lowerˡᶜ : 0 ∣ Φᴸ ⊢ C ⊑ A
    lowerʳᶜ : 0 ∣ Φᴿ ⊢ C ⊑ B
    greatestᶜ :
      ∀ C′ →
      0 ∣ Φᴸ ⊢ C′ ⊑ A →
      0 ∣ Φᴿ ⊢ C′ ⊑ B →
      0 ∣ Φᴼ ⊢ C′ ⊑ C

open Glbᶜ public

glbᶜ-intro :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  0 ∣ Φᴸ ⊢ C ⊑ A →
  0 ∣ Φᴿ ⊢ C ⊑ B →
  (∀ C′ →
   0 ∣ Φᴸ ⊢ C′ ⊑ A →
   0 ∣ Φᴿ ⊢ C′ ⊑ B →
   0 ∣ Φᴼ ⊢ C′ ⊑ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ C A B
glbᶜ-intro C⊑A C⊑B greatest .lowerˡᶜ = C⊑A
glbᶜ-intro C⊑A C⊑B greatest .lowerʳᶜ = C⊑B
glbᶜ-intro C⊑A C⊑B greatest .greatestᶜ = greatest

glbᶜ⇒common-lowerᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  Glbᶜ Φᴸ Φᴿ Φᴼ C A B →
  CommonLowerᶜ Φᴸ Φᴿ C A B
glbᶜ⇒common-lowerᶜ glb = lowerˡᶜ glb , lowerʳᶜ glb

record GlbCtx (Φᴸ Φᴿ Φᴼ : ImpCtx) : Set where
  field
    glb-var-var :
      ∀ {W X Y} →
      (W ˣ⊑ˣ X) ∈ Φᴸ →
      (W ˣ⊑ˣ Y) ∈ Φᴿ →
      (Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ)))

    glb-var-star :
      ∀ {W X} →
      (W ˣ⊑ˣ X) ∈ Φᴸ →
      (W ˣ⊑★) ∈ Φᴿ →
      (Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑★) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ)))

    glb-star-var :
      ∀ {W Y} →
      (W ˣ⊑★) ∈ Φᴸ →
      (W ˣ⊑ˣ Y) ∈ Φᴿ →
      (Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑★) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ)))

    glb-star-star :
      ∀ {W} →
      (W ˣ⊑★) ∈ Φᴸ →
      (W ˣ⊑★) ∈ Φᴿ →
      (W ˣ⊑★) ∈ Φᴼ

open GlbCtx public

GlbCtx-[] : GlbCtx [] [] []
GlbCtx-[] .glb-var-var ()
GlbCtx-[] .glb-var-star ()
GlbCtx-[] .glb-star-var ()
GlbCtx-[] .glb-star-star ()

GlbCtx-∀∀ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  GlbCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
         ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
         ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
GlbCtx-∀∀ {Φᴸ} {Φᴿ} {Φᴼ} G .glb-var-var (here refl) (here refl) =
  zero , here refl , here refl , greatest
  where
  greatest :
    ∀ {W} →
    (W ˣ⊑ˣ zero) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W ˣ⊑ˣ zero) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W ˣ⊑ˣ zero) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest (here refl) (here refl) = here refl
  greatest (here refl) (there w⊑0) =
    ⊥-elim (no-⇑ᵢ-zero-left w⊑0)
  greatest (there w⊑0) _ =
    ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀∀ G .glb-var-var (here refl) (there w⊑Y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑Y)
GlbCtx-∀∀ G .glb-var-var (there w⊑X) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑X)
GlbCtx-∀∀ G .glb-var-var {W = zero} (there w⊑X) _ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑X)
GlbCtx-∀∀ G .glb-var-var {W = suc W} {X = zero}
    (there w⊑0) _ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀∀ G .glb-var-var {W = suc W} {Y = zero}
    _ (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀∀ {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-var-var {W = suc W} {X = suc X} {Y = suc Y}
    (there w⊑X) (there w⊑Y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-var-var G (un⇑ᵢ-ˣ∈ w⊑X) (un⇑ᵢ-ˣ∈ w⊑Y)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑ˣ suc X) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W′ ˣ⊑ˣ suc Y) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑X) _ =
    ⊥-elim (no-⇑ᵢ-zero-left w′⊑X)
  greatest′ {W′ = suc W′} (there w′⊑X) (there w′⊑Y) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᵢ-ˣ∈ w′⊑X)
          (un⇑ᵢ-ˣ∈ w′⊑Y)))
GlbCtx-∀∀ G .glb-var-star (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
GlbCtx-∀∀ G .glb-var-star (there w⊑X) (here ())
GlbCtx-∀∀ G .glb-var-star {W = zero} (there w⊑X) _ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑X)
GlbCtx-∀∀ G .glb-var-star {W = suc W} {X = zero}
    (there w⊑0) _ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀∀ {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-var-star {W = suc W} {X = suc X}
    (there w⊑X) (there w⊑★) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑★) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-var-star G (un⇑ᵢ-ˣ∈ w⊑X) (un⇑ᵢ-★∈ w⊑★)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑ˣ suc X) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑X) _ =
    ⊥-elim (no-⇑ᵢ-zero-left w′⊑X)
  greatest′ {W′ = suc W′} (there w′⊑X) (there w′⊑★) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᵢ-ˣ∈ w′⊑X)
          (un⇑ᵢ-★∈ w′⊑★)))
GlbCtx-∀∀ G .glb-star-var (here ()) _
GlbCtx-∀∀ G .glb-star-var (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
GlbCtx-∀∀ G .glb-star-var {W = zero} (there w⊑★) _ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
GlbCtx-∀∀ G .glb-star-var {W = suc W} {Y = zero}
    _ (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀∀ {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-star-var {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑Y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑★) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-star-var G (un⇑ᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑Y)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W′ ˣ⊑ˣ suc Y) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑★) _ =
    ⊥-elim (no-⇑ᵢ-zero-star w′⊑★)
  greatest′ {W′ = suc W′} (there w′⊑★) (there w′⊑Y) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᵢ-★∈ w′⊑★)
          (un⇑ᵢ-ˣ∈ w′⊑Y)))
GlbCtx-∀∀ G .glb-star-star (here ()) _
GlbCtx-∀∀ G .glb-star-star {W = zero} (there w⊑★) _ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
GlbCtx-∀∀ G .glb-star-star {W = suc W} (there w⊑★ᴸ) (there w⊑★ᴿ) =
  there
    (⇑ᵢ-★∈
      (glb-star-star G (un⇑ᵢ-★∈ w⊑★ᴸ) (un⇑ᵢ-★∈ w⊑★ᴿ)))

GlbCtx-∀ν :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  GlbCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
         ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
         ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
GlbCtx-∀ν G .glb-var-var (here refl) (there w⊑Y) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑Y)
GlbCtx-∀ν G .glb-var-var (there w⊑X) (here ())
GlbCtx-∀ν G .glb-var-var {W = zero} (there w⊑X) _ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑X)
GlbCtx-∀ν G .glb-var-var {W = suc W} {X = zero}
    (there w⊑0) _ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀ν {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-var-var {W = suc W} {X = suc X}
    (there w⊑X) (there w⊑Y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑ˣ _) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑ˣ _) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-var-var G (un⇑ᵢ-ˣ∈ w⊑X) (un⇑ᴸᵢ-ˣ∈ w⊑Y)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑ˣ suc X) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W′ ˣ⊑ˣ _) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑X) _ =
    ⊥-elim (no-⇑ᵢ-zero-left w′⊑X)
  greatest′ {W′ = suc W′} (there w′⊑X) (there w′⊑Y) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᵢ-ˣ∈ w′⊑X)
          (un⇑ᴸᵢ-ˣ∈ w′⊑Y)))
GlbCtx-∀ν {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-var-star (here refl) (here refl) =
  zero , here refl , here refl , greatest
  where
  greatest :
    ∀ {W′} →
    (W′ ˣ⊑ˣ zero) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ →
    (W′ ˣ⊑ˣ zero) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest (here refl) (here refl) = here refl
  greatest (here refl) (there w⊑★) =
    ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
  greatest (there w⊑0) _ =
    ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀ν G .glb-var-star (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
GlbCtx-∀ν G .glb-var-star (there w⊑X) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑X)
GlbCtx-∀ν G .glb-var-star {W = zero} (there w⊑X) _ =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑X)
GlbCtx-∀ν G .glb-var-star {W = suc W} {X = zero}
    (there w⊑0) _ =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-∀ν {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-var-star {W = suc W} {X = suc X}
    (there w⊑X) (there w⊑★) =
  suc (proj₁ r) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᴸᵢ-★∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ X) ∈ Φᴸ →
          (W′ ˣ⊑★) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-var-star G (un⇑ᵢ-ˣ∈ w⊑X) (un⇑ᴸᵢ-★∈ w⊑★)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑ˣ suc X) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑X) _ =
    ⊥-elim (no-⇑ᵢ-zero-left w′⊑X)
  greatest′ {W′ = suc W′} (there w′⊑X) (there w′⊑★) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᵢ-ˣ∈ w′⊑X)
          (un⇑ᴸᵢ-★∈ w′⊑★)))
GlbCtx-∀ν G .glb-star-var (here ()) _
GlbCtx-∀ν G .glb-star-var _ (here ())
GlbCtx-∀ν G .glb-star-var {W = zero} (there w⊑★) _ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
GlbCtx-∀ν {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-star-var {W = suc W} (there w⊑★) (there w⊑Y) =
  suc (proj₁ r) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ r))) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ _) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑★) ∈ Φᴸ →
          (W′ ˣ⊑ˣ _) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-star-var G (un⇑ᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑Y)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ →
    (W′ ˣ⊑ˣ _) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑★) _ =
    ⊥-elim (no-⇑ᵢ-zero-star w′⊑★)
  greatest′ {W′ = suc W′} (there w′⊑★) (there w′⊑Y) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᵢ-★∈ w′⊑★)
          (un⇑ᴸᵢ-ˣ∈ w′⊑Y)))
GlbCtx-∀ν G .glb-star-star (here ()) _
GlbCtx-∀ν G .glb-star-star {W = zero} (there w⊑★) _ =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
GlbCtx-∀ν G .glb-star-star {W = suc W} (there w⊑★ᴸ) (there w⊑★ᴿ) =
  there
    (⇑ᵢ-★∈
      (glb-star-star G (un⇑ᵢ-★∈ w⊑★ᴸ) (un⇑ᴸᵢ-★∈ w⊑★ᴿ)))

GlbCtx-ν∀ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  GlbCtx ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
         ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
         ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
GlbCtx-ν∀ G .glb-var-var (here ()) _
GlbCtx-ν∀ G .glb-var-var (there w⊑X) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑X)
GlbCtx-ν∀ G .glb-var-var {W = zero} (there w⊑X) _ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑X)
GlbCtx-ν∀ G .glb-var-var {W = suc W} {Y = zero}
    _ (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-ν∀ {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-var-var {W = suc W} {Y = suc Y}
    (there w⊑X) (there w⊑Y) =
  suc (proj₁ r) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ _) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ _) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-var-var G (un⇑ᴸᵢ-ˣ∈ w⊑X) (un⇑ᵢ-ˣ∈ w⊑Y)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑ˣ _) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ →
    (W′ ˣ⊑ˣ suc Y) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑X) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑X)
  greatest′ {W′ = suc W′} (there w′⊑X) (there w′⊑Y) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᴸᵢ-ˣ∈ w′⊑X)
          (un⇑ᵢ-ˣ∈ w′⊑Y)))
GlbCtx-ν∀ G .glb-var-star (here ()) _
GlbCtx-ν∀ G .glb-var-star _ (here ())
GlbCtx-ν∀ G .glb-var-star {W = zero} (there w⊑X) _ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑X)
GlbCtx-ν∀ {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-var-star {W = suc W} (there w⊑X) (there w⊑★) =
  suc (proj₁ r) ,
  there (⇑ᴸᵢ-ˣ∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-★∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑ˣ _) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑ˣ _) ∈ Φᴸ →
          (W′ ˣ⊑★) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-var-star G (un⇑ᴸᵢ-ˣ∈ w⊑X) (un⇑ᵢ-★∈ w⊑★)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑ˣ _) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (there w′⊑X) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-left w′⊑X)
  greatest′ {W′ = suc W′} (there w′⊑X) (there w′⊑★) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᴸᵢ-ˣ∈ w′⊑X)
          (un⇑ᵢ-★∈ w′⊑★)))
GlbCtx-ν∀ {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-star-var (here refl) (here refl) =
  zero , here refl , here refl , greatest
  where
  greatest :
    ∀ {W′} →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ →
    (W′ ˣ⊑ˣ zero) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W′ ˣ⊑ˣ zero) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest (here refl) (here refl) = here refl
  greatest (here refl) (there w⊑0) =
    ⊥-elim (no-⇑ᵢ-zero-left w⊑0)
  greatest {W′ = zero} (there w⊑★) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
  greatest {W′ = suc W′} _ (there w⊑0) =
    ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-ν∀ G .glb-star-var (here refl) (there w⊑Y) =
  ⊥-elim (no-⇑ᵢ-zero-left w⊑Y)
GlbCtx-ν∀ G .glb-star-var (there w⊑★) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
GlbCtx-ν∀ G .glb-star-var {W = zero} (there w⊑★) _ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
GlbCtx-ν∀ G .glb-star-var {W = suc W} {Y = zero}
    _ (there w⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right w⊑0)
GlbCtx-ν∀ {Φᴸ} {Φᴿ} {Φᴼ} G
    .glb-star-var {W = suc W} {Y = suc Y}
    (there w⊑★) (there w⊑Y) =
  suc (proj₁ r) ,
  there (⇑ᴸᵢ-★∈ (proj₁ (proj₂ r))) ,
  there (⇑ᵢ-ˣ∈ (proj₁ (proj₂ (proj₂ r)))) ,
  greatest′
  where
  r : Σ[ Z ∈ TyVar ]
        ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ ×
         (∀ {W′} →
          (W′ ˣ⊑★) ∈ Φᴸ →
          (W′ ˣ⊑ˣ Y) ∈ Φᴿ →
          (W′ ˣ⊑ˣ Z) ∈ Φᴼ))
  r = glb-star-var G (un⇑ᴸᵢ-★∈ w⊑★) (un⇑ᵢ-ˣ∈ w⊑Y)

  greatest′ :
    ∀ {W′} →
    (W′ ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ →
    (W′ ˣ⊑ˣ suc Y) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ →
    (W′ ˣ⊑ˣ suc (proj₁ r)) ∈ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ
  greatest′ {W′ = zero} (here refl) (there w′⊑Y) =
    ⊥-elim (no-⇑ᵢ-zero-left w′⊑Y)
  greatest′ {W′ = zero} (there w′⊑★) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-star w′⊑★)
  greatest′ {W′ = suc W′} (there w′⊑★) (there w′⊑Y) =
    there
      (⇑ᵢ-ˣ∈
        (proj₂ (proj₂ (proj₂ r))
          (un⇑ᴸᵢ-★∈ w′⊑★)
          (un⇑ᵢ-ˣ∈ w′⊑Y)))
GlbCtx-ν∀ G .glb-star-star _ (here ())
GlbCtx-ν∀ G .glb-star-star {W = zero} (here refl) (there w⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star w⊑★)
GlbCtx-ν∀ G .glb-star-star {W = zero} (there w⊑★) _ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
GlbCtx-ν∀ G .glb-star-star {W = suc W} (there w⊑★ᴸ) (there w⊑★ᴿ) =
  there
    (⇑ᵢ-★∈
      (glb-star-star G (un⇑ᴸᵢ-★∈ w⊑★ᴸ) (un⇑ᵢ-★∈ w⊑★ᴿ)))

greatest-var-varᵍ :
  ∀ {Φᴸ Φᴿ Φᴼ X Y Z} →
  (∀ {W} →
   (W ˣ⊑ˣ X) ∈ Φᴸ →
   (W ˣ⊑ˣ Y) ∈ Φᴿ →
   (W ˣ⊑ˣ Z) ∈ Φᴼ) →
  ∀ {D} →
  0 ∣ Φᴸ ⊢ D ⊑ ＇ X →
  0 ∣ Φᴿ ⊢ D ⊑ ＇ Y →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ Z
greatest-var-varᵍ g (idˣ d⊑x) (idˣ d⊑y) =
  idˣ (g d⊑x d⊑y)
greatest-var-varᵍ {Φᴸ = phiL} {Φᴿ = phiR} {Φᴼ = phiO} {X = x}
    {Y = y} {Z = z}
    g (ν occD d⊑x) (ν _ d⊑y) =
  ν occD (greatest-var-varᵍ gν d⊑x d⊑y)
  where
  gν :
    ∀ {W} →
    (W ˣ⊑ˣ x) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiL →
    (W ˣ⊑ˣ y) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiR →
    (W ˣ⊑ˣ z) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiO
  gν {W = zero} (there w⊑x) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
  gν {W = suc W} (there w⊑x) (there w⊑y) =
    there (⇑ᴸᵢ-ˣ∈ (g (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-ˣ∈ w⊑y)))

greatest-var-starᵍ :
  ∀ {Φᴸ Φᴿ Φᴼ X Z} →
  (∀ {W} →
   (W ˣ⊑ˣ X) ∈ Φᴸ →
   (W ˣ⊑★) ∈ Φᴿ →
   (W ˣ⊑ˣ Z) ∈ Φᴼ) →
  ∀ {D} →
  0 ∣ Φᴸ ⊢ D ⊑ ＇ X →
  0 ∣ Φᴿ ⊢ D ⊑ ★ →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ Z
greatest-var-starᵍ g (idˣ d⊑x) (tagˣ d⊑★) =
  idˣ (g d⊑x d⊑★)
greatest-var-starᵍ {Φᴸ = phiL} {Φᴿ = phiR} {Φᴼ = phiO} {X = x}
    {Z = z}
    g (ν occD d⊑x) (ν _ d⊑★) =
  ν occD (greatest-var-starᵍ gν d⊑x d⊑★)
  where
  gν :
    ∀ {W} →
    (W ˣ⊑ˣ x) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiL →
    (W ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiR →
    (W ˣ⊑ˣ z) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiO
  gν {W = zero} (there w⊑x) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑x)
  gν {W = suc W} (there w⊑x) (there w⊑★) =
    there (⇑ᴸᵢ-ˣ∈ (g (un⇑ᴸᵢ-ˣ∈ w⊑x) (un⇑ᴸᵢ-★∈ w⊑★)))

greatest-star-varᵍ :
  ∀ {Φᴸ Φᴿ Φᴼ Y Z} →
  (∀ {W} →
   (W ˣ⊑★) ∈ Φᴸ →
   (W ˣ⊑ˣ Y) ∈ Φᴿ →
   (W ˣ⊑ˣ Z) ∈ Φᴼ) →
  ∀ {D} →
  0 ∣ Φᴸ ⊢ D ⊑ ★ →
  0 ∣ Φᴿ ⊢ D ⊑ ＇ Y →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ Z
greatest-star-varᵍ g (tagˣ d⊑★) (idˣ d⊑y) =
  idˣ (g d⊑★ d⊑y)
greatest-star-varᵍ {Φᴸ = phiL} {Φᴿ = phiR} {Φᴼ = phiO} {Y = y}
    {Z = z}
    g (ν occD d⊑★) (ν _ d⊑y) =
  ν occD (greatest-star-varᵍ gν d⊑★ d⊑y)
  where
  gν :
    ∀ {W} →
    (W ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiL →
    (W ˣ⊑ˣ y) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiR →
    (W ˣ⊑ˣ z) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiO
  gν {W = zero} (here refl) (there w⊑y) =
    ⊥-elim (no-⇑ᴸᵢ-zero-left w⊑y)
  gν {W = zero} (there w⊑★) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
  gν {W = suc W} (there w⊑★) (there w⊑y) =
    there (⇑ᴸᵢ-ˣ∈ (g (un⇑ᴸᵢ-★∈ w⊑★) (un⇑ᴸᵢ-ˣ∈ w⊑y)))

greatest-star-starᵍ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  (∀ {W} →
   (W ˣ⊑★) ∈ Φᴸ →
   (W ˣ⊑★) ∈ Φᴿ →
   (W ˣ⊑★) ∈ Φᴼ) →
  ∀ {D} →
  0 ∣ Φᴸ ⊢ D ⊑ ★ →
  0 ∣ Φᴿ ⊢ D ⊑ ★ →
  0 ∣ Φᴼ ⊢ D ⊑ ★
greatest-star-starᵍ g id★ id★ = id★
greatest-star-starᵍ g (tag ι) (tag .ι) = tag ι
greatest-star-starᵍ g (tag_⇒_ p₁ p₂) (tag_⇒_ q₁ q₂) =
  tag_⇒_ (greatest-star-starᵍ g p₁ q₁) (greatest-star-starᵍ g p₂ q₂)
greatest-star-starᵍ g (tagˣ d⊑★ᴸ) (tagˣ d⊑★ᴿ) =
  tagˣ (g d⊑★ᴸ d⊑★ᴿ)
greatest-star-starᵍ {Φᴸ = phiL} {Φᴿ = phiR} {Φᴼ = phiO}
    g (ν occD d⊑★ᴸ) (ν _ d⊑★ᴿ) =
  ν occD (greatest-star-starᵍ gν d⊑★ᴸ d⊑★ᴿ)
  where
  gν :
    ∀ {W} →
    (W ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiL →
    (W ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiR →
    (W ˣ⊑★) ∈ (0 ˣ⊑★) ∷ ⇑ᴸᵢ phiO
  gν {W = zero} (here refl) _ = here refl
  gν {W = zero} (there w⊑★) _ =
    ⊥-elim (no-⇑ᴸᵢ-zero-star w⊑★)
  gν {W = suc W} (there w⊑★ᴸ) (there w⊑★ᴿ) =
    there (⇑ᴸᵢ-★∈ (g (un⇑ᴸᵢ-★∈ w⊑★ᴸ) (un⇑ᴸᵢ-★∈ w⊑★ᴿ)))

greatest-base-baseᵍ :
  ∀ {Φᴸ Φᴿ Φᴼ ι D} →
  0 ∣ Φᴸ ⊢ D ⊑ ‵ ι →
  0 ∣ Φᴿ ⊢ D ⊑ ‵ ι →
  0 ∣ Φᴼ ⊢ D ⊑ ‵ ι
greatest-base-baseᵍ idι idι = idι
greatest-base-baseᵍ (ν occD d⊑ιᴸ) (ν _ d⊑ιᴿ) =
  ν occD (greatest-base-baseᵍ d⊑ιᴸ d⊑ιᴿ)

greatest-base-starᵍ :
  ∀ {Φᴸ Φᴿ Φᴼ ι D} →
  0 ∣ Φᴸ ⊢ D ⊑ ‵ ι →
  0 ∣ Φᴿ ⊢ D ⊑ ★ →
  0 ∣ Φᴼ ⊢ D ⊑ ‵ ι
greatest-base-starᵍ idι (tag ι) = idι
greatest-base-starᵍ (ν occD d⊑ι) (ν _ d⊑★) =
  ν occD (greatest-base-starᵍ d⊑ι d⊑★)

greatest-star-baseᵍ :
  ∀ {Φᴸ Φᴿ Φᴼ ι D} →
  0 ∣ Φᴸ ⊢ D ⊑ ★ →
  0 ∣ Φᴿ ⊢ D ⊑ ‵ ι →
  0 ∣ Φᴼ ⊢ D ⊑ ‵ ι
greatest-star-baseᵍ (tag ι) idι = idι
greatest-star-baseᵍ (ν occD d⊑★) (ν _ d⊑ι) =
  ν occD (greatest-star-baseᵍ d⊑★ d⊑ι)

glbᶜ-star-star :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  Glbᶜ Φᴸ Φᴿ Φᴼ ★ ★ ★
glbᶜ-star-star G =
  glbᶜ-intro id★ id★
    (λ D D⊑★ᴸ D⊑★ᴿ →
      greatest-star-starᵍ (glb-star-star G) D⊑★ᴸ D⊑★ᴿ)

glbᶜ-base-base :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ ι) (‵ ι) (‵ ι)
glbᶜ-base-base =
  glbᶜ-intro idι idι
    (λ D D⊑ιᴸ D⊑ιᴿ → greatest-base-baseᵍ D⊑ιᴸ D⊑ιᴿ)

glbᶜ-base-star :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ ι) (‵ ι) ★
glbᶜ-base-star =
  glbᶜ-intro idι (tag _)
    (λ D D⊑ι D⊑★ → greatest-base-starᵍ D⊑ι D⊑★)

glbᶜ-star-base :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ ι) ★ (‵ ι)
glbᶜ-star-base =
  glbᶜ-intro (tag _) idι
    (λ D D⊑★ D⊑ι → greatest-star-baseᵍ D⊑★ D⊑ι)

glbᶜ-var-var :
  ∀ {Φᴸ Φᴿ Φᴼ X Y W} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑ˣ X) ∈ Φᴸ →
  (W ˣ⊑ˣ Y) ∈ Φᴿ →
  Σ[ Z ∈ TyVar ] Glbᶜ Φᴸ Φᴿ Φᴼ (＇ Z) (＇ X) (＇ Y)
glbᶜ-var-var G w⊑x w⊑y =
  proj₁ r ,
  glbᶜ-intro
    (idˣ (proj₁ (proj₂ r)))
    (idˣ (proj₁ (proj₂ (proj₂ r))))
    (λ D D⊑x D⊑y →
      greatest-var-varᵍ (proj₂ (proj₂ (proj₂ r))) D⊑x D⊑y)
  where
  r = glb-var-var G w⊑x w⊑y

glbᶜ-var-star :
  ∀ {Φᴸ Φᴿ Φᴼ X W} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑ˣ X) ∈ Φᴸ →
  (W ˣ⊑★) ∈ Φᴿ →
  Σ[ Z ∈ TyVar ] Glbᶜ Φᴸ Φᴿ Φᴼ (＇ Z) (＇ X) ★
glbᶜ-var-star G w⊑x w⊑★ =
  proj₁ r ,
  glbᶜ-intro
    (idˣ (proj₁ (proj₂ r)))
    (tagˣ (proj₁ (proj₂ (proj₂ r))))
    (λ D D⊑x D⊑★ →
      greatest-var-starᵍ (proj₂ (proj₂ (proj₂ r))) D⊑x D⊑★)
  where
  r = glb-var-star G w⊑x w⊑★

glbᶜ-star-var :
  ∀ {Φᴸ Φᴿ Φᴼ Y W} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  (W ˣ⊑★) ∈ Φᴸ →
  (W ˣ⊑ˣ Y) ∈ Φᴿ →
  Σ[ Z ∈ TyVar ] Glbᶜ Φᴸ Φᴿ Φᴼ (＇ Z) ★ (＇ Y)
glbᶜ-star-var G w⊑★ w⊑y =
  proj₁ r ,
  glbᶜ-intro
    (tagˣ (proj₁ (proj₂ r)))
    (idˣ (proj₁ (proj₂ (proj₂ r))))
    (λ D D⊑★ D⊑y →
      greatest-star-varᵍ (proj₂ (proj₂ (proj₂ r))) D⊑★ D⊑y)
  where
  r = glb-star-var G w⊑★ w⊑y

glbᶜ-idempotent :
  ∀ {Φ A} →
  ReflImpCtx Φ →
  WfTy (length Φ) 0 A →
  Glbᶜ Φ Φ Φ A A A
glbᶜ-idempotent reflΦ wfA =
  glbᶜ-intro (⊑-refl reflΦ wfA) (⊑-refl reflΦ wfA)
    (λ C′ C′⊑A _ → C′⊑A)

glbᶜ-topʳ :
  ∀ {Φ A} →
  ReflImpCtx Φ →
  StarImpCtx Φ →
  WfTy (length Φ) 0 A →
  Glbᶜ Φ Φ Φ A A ★
glbᶜ-topʳ reflΦ starΦ wfA =
  glbᶜ-intro (⊑-refl reflΦ wfA) (⊑★ starΦ wfA)
    (λ C′ C′⊑A _ → C′⊑A)

glbᶜ-topˡ :
  ∀ {Φ B} →
  ReflImpCtx Φ →
  StarImpCtx Φ →
  WfTy (length Φ) 0 B →
  Glbᶜ Φ Φ Φ B ★ B
glbᶜ-topˡ reflΦ starΦ wfB =
  glbᶜ-intro (⊑★ starΦ wfB) (⊑-refl reflΦ wfB)
    (λ C′ _ C′⊑B → C′⊑B)

glbᶜ-greatest-∀∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C′ ⊑ A →
  0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C′ ⊑ B →
  0 ∣ Φᴼ ⊢ `∀ C′ ⊑ `∀ C
glbᶜ-greatest-∀∀ glb C′⊑A C′⊑B =
  ∀ⁱ greatestᶜ glb _ C′⊑A C′⊑B

glbᶜ-greatest-∀ν :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C′ ⊑ A →
  0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C′ ⊑ B →
  0 ∣ Φᴼ ⊢ `∀ C′ ⊑ `∀ C
glbᶜ-greatest-∀ν glb C′⊑A C′⊑B =
  ∀ⁱ greatestᶜ glb _ C′⊑A C′⊑B

glbᶜ-greatest-ν∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C′ ⊑ A →
  0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C′ ⊑ B →
  0 ∣ Φᴼ ⊢ `∀ C′ ⊑ `∀ C
glbᶜ-greatest-ν∀ glb C′⊑A C′⊑B =
  ∀ⁱ greatestᶜ glb _ C′⊑A C′⊑B

glbᶜ-greatest-∀∀-dispatch :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  ∀Lower² Φᴸ Φᴿ C′ A B →
  (∀ {D} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C
glbᶜ-greatest-∀∀-dispatch glb (via-∀∀ p q) _ _ _ =
  glbᶜ-greatest-∀∀ glb p q
glbᶜ-greatest-∀∀-dispatch glb (via-∀ν p occD q) k∀ν _ _ =
  k∀ν p occD q
glbᶜ-greatest-∀∀-dispatch glb (via-ν∀ occD p q) _ kν∀ _ =
  kν∀ occD p q
glbᶜ-greatest-∀∀-dispatch glb (via-νν occD p q) _ _ kνν =
  kνν occD p q

glbᶜ-greatest-∀∀-open :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  0 ∣ Φᴸ ⊢ C′ ⊑ `∀ A →
  0 ∣ Φᴿ ⊢ C′ ⊑ `∀ B →
  (∀ {D} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C
glbᶜ-greatest-∀∀-open glb C′⊑∀A C′⊑∀B k∀ν kν∀ kνν =
  glbᶜ-greatest-∀∀-dispatch glb
    (∀∀-lower²-inv C′⊑∀A C′⊑∀B)
    k∀ν kν∀ kνν

glbᶜ-greatest-∀ν-dispatch :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  ∀νLower² Φᴸ Φᴿ C′ A B →
  (∀ {D B′} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B′ →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ Φᴿ ⊢ `∀ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C
glbᶜ-greatest-∀ν-dispatch glb (via-∀∀ʳ p q) k∀∀ʳ _ =
  k∀∀ʳ p q
glbᶜ-greatest-∀ν-dispatch glb (via-∀νʳ p occD q) _ _ =
  glbᶜ-greatest-∀ν glb p q
glbᶜ-greatest-∀ν-dispatch glb (via-νˡ occD p q) _ kνˡ =
  kνˡ occD p q

glbᶜ-greatest-∀ν-open :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  0 ∣ Φᴸ ⊢ C′ ⊑ `∀ A →
  0 ∣ Φᴿ ⊢ C′ ⊑ B →
  (∀ {D B′} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B′ →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ Φᴿ ⊢ `∀ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C
glbᶜ-greatest-∀ν-open glb C′⊑∀A C′⊑B k∀∀ʳ kνˡ =
  glbᶜ-greatest-∀ν-dispatch glb
    (∀ν-lower²-inv C′⊑∀A C′⊑B)
    k∀∀ʳ kνˡ

glbᶜ-greatest-ν∀-dispatch :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  ν∀Lower² Φᴸ Φᴿ C′ A B →
  (∀ {D A′} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A′ →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ Φᴸ ⊢ `∀ D ⊑ A →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C
glbᶜ-greatest-ν∀-dispatch glb (via-∀∀ˡ p q) k∀∀ˡ _ =
  k∀∀ˡ p q
glbᶜ-greatest-ν∀-dispatch glb (via-ν∀ˡ occD p q) _ _ =
  glbᶜ-greatest-ν∀ glb p q
glbᶜ-greatest-ν∀-dispatch glb (via-νʳ occD p q) _ kνʳ =
  kνʳ occD p q

glbᶜ-greatest-ν∀-open :
  ∀ {Φᴸ Φᴿ Φᴼ A B C C′} →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  0 ∣ Φᴸ ⊢ C′ ⊑ A →
  0 ∣ Φᴿ ⊢ C′ ⊑ `∀ B →
  (∀ {D A′} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A′ →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ Φᴸ ⊢ `∀ D ⊑ A →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C
glbᶜ-greatest-ν∀-open glb C′⊑A C′⊑∀B k∀∀ˡ kνʳ =
  glbᶜ-greatest-ν∀-dispatch glb
    (ν∀-lower²-inv C′⊑A C′⊑∀B)
    k∀∀ˡ kνʳ

glbᶜ-lift-lower-∀∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  CommonLowerᶜ Φᴸ Φᴿ (`∀ C) (`∀ A) (`∀ B)
glbᶜ-lift-lower-∀∀ glb =
  ∀ⁱ lowerˡᶜ glb , ∀ⁱ lowerʳᶜ glb

glbᶜ-lift-lower-∀ν :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero A ≡ true →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  CommonLowerᶜ Φᴸ Φᴿ (`∀ C) (`∀ A) B
glbᶜ-lift-lower-∀ν occA glb =
  ∀ⁱ lowerˡᶜ glb ,
  ν (plainν-target-occurs-source (lowerˡᶜ glb) occA) (lowerʳᶜ glb)

glbᶜ-lift-lower-ν∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero B ≡ true →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  CommonLowerᶜ Φᴸ Φᴿ (`∀ C) A (`∀ B)
glbᶜ-lift-lower-ν∀ occB glb =
  ν (plainν-target-occurs-source (lowerʳᶜ glb) occB) (lowerˡᶜ glb) ,
  ∀ⁱ lowerʳᶜ glb

glbᶜ-lift-lower-νν :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero C ≡ true →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴼ)
       C A B →
  CommonLowerᶜ Φᴸ Φᴿ (`∀ C) A B
glbᶜ-lift-lower-νν occC glb =
  ν occC (lowerˡᶜ glb) , ν occC (lowerʳᶜ glb)

glbᶜ-lift-∀∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  (∀ C′ →
   0 ∣ Φᴸ ⊢ C′ ⊑ `∀ A →
   0 ∣ Φᴿ ⊢ C′ ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (`∀ C) (`∀ A) (`∀ B)
glbᶜ-lift-∀∀ glb greatest =
  glbᶜ-intro
    (proj₁ (glbᶜ-lift-lower-∀∀ glb))
    (proj₂ (glbᶜ-lift-lower-∀∀ glb))
    greatest

glbᶜ-lift-∀ν :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero A ≡ true →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  (∀ C′ →
   0 ∣ Φᴸ ⊢ C′ ⊑ `∀ A →
   0 ∣ Φᴿ ⊢ C′ ⊑ B →
   0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (`∀ C) (`∀ A) B
glbᶜ-lift-∀ν occA glb greatest =
  glbᶜ-intro
    (proj₁ (glbᶜ-lift-lower-∀ν occA glb))
    (proj₂ (glbᶜ-lift-lower-∀ν occA glb))
    greatest

glbᶜ-lift-ν∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero B ≡ true →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  (∀ C′ →
   0 ∣ Φᴸ ⊢ C′ ⊑ A →
   0 ∣ Φᴿ ⊢ C′ ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (`∀ C) A (`∀ B)
glbᶜ-lift-ν∀ occB glb greatest =
  glbᶜ-intro
    (proj₁ (glbᶜ-lift-lower-ν∀ occB glb))
    (proj₂ (glbᶜ-lift-lower-ν∀ occB glb))
    greatest

glbᶜ-lift-νν :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero C ≡ true →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴼ)
       C A B →
  (∀ C′ →
   0 ∣ Φᴸ ⊢ C′ ⊑ A →
   0 ∣ Φᴿ ⊢ C′ ⊑ B →
   0 ∣ Φᴼ ⊢ C′ ⊑ `∀ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (`∀ C) A B
glbᶜ-lift-νν occC glb greatest =
  glbᶜ-intro
    (proj₁ (glbᶜ-lift-lower-νν occC glb))
    (proj₂ (glbᶜ-lift-lower-νν occC glb))
    greatest

glbᶜ-lift-∀∀-open :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  (∀ {D} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (`∀ C) (`∀ A) (`∀ B)
glbᶜ-lift-∀∀-open glb k∀ν kν∀ kνν =
  glbᶜ-lift-∀∀ glb
    (λ C′ C′⊑∀A C′⊑∀B →
      glbᶜ-greatest-∀∀-open glb C′⊑∀A C′⊑∀B k∀ν kν∀ kνν)

glbᶜ-lift-∀ν-open :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero A ≡ true →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  (∀ {D B′} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B′ →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
   0 ∣ Φᴿ ⊢ `∀ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (`∀ C) (`∀ A) B
glbᶜ-lift-∀ν-open occA glb k∀∀ʳ kνˡ =
  glbᶜ-lift-∀ν occA glb
    (λ C′ C′⊑∀A C′⊑B →
      glbᶜ-greatest-∀ν-open glb C′⊑∀A C′⊑B k∀∀ʳ kνˡ)

glbᶜ-lift-ν∀-open :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero B ≡ true →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  (∀ {D A′} →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A′ →
   0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  (∀ {D} →
   occurs zero D ≡ true →
   0 ∣ Φᴸ ⊢ `∀ D ⊑ A →
   0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
   0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (`∀ C) A (`∀ B)
glbᶜ-lift-ν∀-open occB glb k∀∀ˡ kνʳ =
  glbᶜ-lift-ν∀ occB glb
    (λ C′ C′⊑A C′⊑∀B →
      glbᶜ-greatest-ν∀-open glb C′⊑A C′⊑∀B k∀∀ˡ kνʳ)

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

⊓⇒common-lower :
  ∀ {A B C} →
  0 ⊢ C ＝ A ⊓ B →
  CommonLower A B
⊓⇒common-lower glb = _ , ⊓-lowerˡ glb , ⊓-lowerʳ glb

glb-exists⇒common-lower :
  ∀ {A B} →
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ A ⊓ B →
  CommonLower A B
glb-exists⇒common-lower (_ , glb) = ⊓⇒common-lower glb

⊓⇒glbᶜ-closed :
  ∀ {A B C} →
  0 ⊢ C ＝ A ⊓ B →
  Glbᶜ [] [] [] C A B
⊓⇒glbᶜ-closed glb .lowerˡᶜ = ⊓-lowerˡ glb
⊓⇒glbᶜ-closed glb .lowerʳᶜ = ⊓-lowerʳ glb
⊓⇒glbᶜ-closed glb .greatestᶜ = ⊓-greatest glb

glbᶜ-closed⇒⊓ :
  ∀ {A B C} →
  Glbᶜ [] [] [] C A B →
  0 ⊢ C ＝ A ⊓ B
glbᶜ-closed⇒⊓ glb =
  lowerˡᶜ glb , lowerʳᶜ glb , greatestᶜ glb

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

common-lower-topʳ⇒glb :
  ∀ {A} →
  WfTy 0 0 A →
  CommonLower A ★ →
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ A ⊓ ★
common-lower-topʳ⇒glb wfA _ = _ , ⊓-top wfA

common-lower-topˡ⇒glb :
  ∀ {B} →
  WfTy 0 0 B →
  CommonLower ★ B →
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ ★ ⊓ B
common-lower-topˡ⇒glb wfB _ = _ , ⊓-comm (⊓-top wfB)

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
