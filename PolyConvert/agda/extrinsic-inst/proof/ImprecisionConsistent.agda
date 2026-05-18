module proof.ImprecisionConsistent where

-- File Charter:
--   * Properties that involve Imprecisoin and Consistency

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Imprecision
open import Consistency
open import Types
open import proof.ConsistencyProperties
  using (length-leftICtx; length-rightICtx; drop-neither-~)

leftICtx-boths[] : ∀ Δ → leftICtx (boths Δ []) ≡ plains Δ []
leftICtx-boths[] zero = refl
leftICtx-boths[] (suc Δ) = cong (X⊑X ∷_) (leftICtx-boths[] Δ)

rightICtx-boths[] : ∀ Δ → rightICtx (boths Δ []) ≡ plains Δ []
rightICtx-boths[] zero = refl
rightICtx-boths[] (suc Δ) = cong (X⊑X ∷_) (rightICtx-boths[] Δ)

left-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ left →
  leftICtx Γ ∋ X ∶ X⊑X
left-lookup-left here = here
left-lookup-left (there x∈) = there (left-lookup-left x∈)

right-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ left →
  rightICtx Γ ∋ X ∶ X⊑★
right-lookup-left here = here
right-lookup-left (there x∈) = there (right-lookup-left x∈)

left-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ right →
  leftICtx Γ ∋ X ∶ X⊑★
left-lookup-right here = here
left-lookup-right (there x∈) = there (left-lookup-right x∈)

right-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ right →
  rightICtx Γ ∋ X ∶ X⊑X
right-lookup-right here = here
right-lookup-right (there x∈) = there (right-lookup-right x∈)

left-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ both →
  leftICtx Γ ∋ X ∶ X⊑X
left-lookup-both here = here
left-lookup-both (there x∈) = there (left-lookup-both x∈)

right-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ both →
  rightICtx Γ ∋ X ∶ X⊑X
right-lookup-both here = here
right-lookup-both (there x∈) = there (right-lookup-both x∈)

left-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑X →
  rightICtx Γ ∋ X ∶ X⊑X →
  Γ ∋ᶜ X ∶ both
left-right-plain {Γ = left ∷ Γ} here ()
left-right-plain {Γ = left ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = right ∷ Γ} () here
left-right-plain {Γ = right ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = both ∷ Γ} here here = here
left-right-plain {Γ = both ∷ Γ} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)
left-right-plain {Γ = neither ∷ Γ} {X = zero} () ()
left-right-plain {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-right-plain x∈ y∈)

left-ν-right-plain :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑★ →
  rightICtx Γ ∋ X ∶ X⊑X →
  Γ ∋ᶜ X ∶ right
left-ν-right-plain {Γ = left ∷ Γ} {X = zero} ()
left-ν-right-plain {Γ = left ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = right ∷ Γ} here here = here
left-ν-right-plain {Γ = right ∷ Γ} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = both ∷ Γ} {X = zero} () here
left-ν-right-plain {Γ = both ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)
left-ν-right-plain {Γ = neither ∷ Γ} {X = zero} here ()
left-ν-right-plain {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-ν-right-plain x∈ y∈)

left-plain-right-ν :
  ∀ {Γ X} →
  leftICtx Γ ∋ X ∶ X⊑X →
  rightICtx Γ ∋ X ∶ X⊑★ →
  Γ ∋ᶜ X ∶ left
left-plain-right-ν {Γ = left ∷ Γ} here here = here
left-plain-right-ν {Γ = left ∷ Γ} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = right ∷ Γ} {X = zero} () ()
left-plain-right-ν {Γ = right ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = both ∷ Γ} {X = zero} here ()
left-plain-right-ν {Γ = both ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)
left-plain-right-ν {Γ = neither ∷ Γ} {X = zero} () here
left-plain-right-ν {Γ = neither ∷ Γ} {X = suc X} (there x∈) (there y∈) =
  there (left-plain-right-ν x∈ y∈)

lower-bounds-consistentᶜ :
  ∀ {Γ A B C p q} →
  0 ∣ leftICtx Γ ⊢ p ⦂ A ⊑ B →
  0 ∣ rightICtx Γ ⊢ q ⦂ A ⊑ C →
  Γ ⊢ B ~ C
lower-bounds-consistentᶜ (⊢A-⊑-★ g p⊢) q⊢ =
  ★-~-B g (lower-bounds-consistentᶜ p⊢ q⊢)
lower-bounds-consistentᶜ p⊢ (⊢A-⊑-★ g q⊢) =
  A-~-★ g (lower-bounds-consistentᶜ p⊢ q⊢)
lower-bounds-consistentᶜ ⊢★-⊑-★ ⊢★-⊑-★ = ★-~-★
lower-bounds-consistentᶜ (⊢X-⊑-★ xν) (⊢X-⊑-★ yν) = ★-~-★
lower-bounds-consistentᶜ (⊢X-⊑-★ xν) (⊢X-⊑-X y∈) =
  ★-~-νX (left-ν-right-plain xν y∈)
lower-bounds-consistentᶜ (⊢X-⊑-X x∈) (⊢X-⊑-★ yν) =
  νX-~-★ (left-plain-right-ν x∈ yν)
lower-bounds-consistentᶜ (⊢X-⊑-X x∈) (⊢X-⊑-X y∈) =
  X-~-X (left-right-plain x∈ y∈)
lower-bounds-consistentᶜ (⊢α-⊑-α (wfSeal ())) q⊢
lower-bounds-consistentᶜ ⊢ι-⊑-ι ⊢ι-⊑-ι = ι-~-ι
lower-bounds-consistentᶜ (⊢A⇒B-⊑-A′⇒B′ p₁⊢ p₂⊢) (⊢A⇒B-⊑-A′⇒B′ q₁⊢ q₂⊢) =
  ⇒-~-⇒ (lower-bounds-consistentᶜ p₁⊢ q₁⊢)
         (lower-bounds-consistentᶜ p₂⊢ q₂⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-∀B q⊢) =
  ∀-~-∀ (lower-bounds-consistentᶜ {Γ = both ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {C = C} (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-B wfC q⊢) =
  ∀-~-B
    (subst (λ n → WfTy n 0 C) (length-rightICtx Γ) wfC)
    (lower-bounds-consistentᶜ {Γ = left ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} {B = B} (⊢∀A-⊑-B wfB p⊢) (⊢∀A-⊑-∀B q⊢) =
  A-~-∀
    (subst (λ n → WfTy n 0 B) (length-leftICtx Γ) wfB)
    (lower-bounds-consistentᶜ {Γ = right ∷ Γ} p⊢ q⊢)
lower-bounds-consistentᶜ {Γ = Γ} (⊢∀A-⊑-B wfB p⊢) (⊢∀A-⊑-B wfC q⊢) =
  drop-neither-~ (lower-bounds-consistentᶜ {Γ = neither ∷ Γ} p⊢ q⊢)

lower-bounds-consistent :
  ∀ {Δ A B C p q} →
  0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ plains Δ [] ⊢ q ⦂ A ⊑ C →
  boths Δ [] ⊢ B ~ C
lower-bounds-consistent
    {Δ = Δ} {A = A} {B = B} {C = C} {p = p} {q = q} p⊢ q⊢ =
  lower-bounds-consistentᶜ {Γ = boths Δ []}
    (subst (λ Φ → 0 ∣ Φ ⊢ p ⦂ A ⊑ B) (sym (leftICtx-boths[] Δ)) p⊢)
    (subst (λ Φ → 0 ∣ Φ ⊢ q ⦂ A ⊑ C) (sym (rightICtx-boths[] Δ)) q⊢)
