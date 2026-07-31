module proof.LeftWideningTagInversionCounterexample where

-- File Charter:
--   * Tests Left Widening Tag Inversion against the quotient close rule.
--   * Builds paired function-cast values related at dynamic identity.
--   * Shows that stripping only the left tag has no type-level index.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Types
open import Coercions hiding (_↦_)
open import Coercions using () renaming (_↦_ to _↦ᶜ_)
open import Terms
open import NarrowWiden hiding (_↦_)
open import NarrowWiden using () renaming (_↦_ to _↦ⁱ_)
open import EnvironmentNarrowing
open import ImprecisionTheorems hiding (_↦_)
open import ImprecisionTheorems using () renaming (_↦_ to _↦ᵇ_)
open import TermNarrowing

id★ⁿ : idᵢ zero ∣ zero ⊢ id ⦂ ★ ⊒ ★ ⊣ zero
id★ⁿ = idᵃ ★ ★ wf★ wf★ tt

id★ʷ : idᵢ zero ∣ zero ⊢ id ⦂ ★ ⊑ ★ ⊣ zero
id★ʷ = idᵃ ★ ★ wf★ wf★ tt

id⇒ⁿ : idᵢ zero ∣ zero
  ⊢ id ↦ᶜ id ⦂ ★ ⇒ ★ ⊒ ★ ⇒ ★ ⊣ zero
id⇒ⁿ = id★ʷ ↦ⁱ id★ⁿ

id⇒⊢ : tag-or-idᵈ ∣ zero ∣ []
  ⊢ id ↦ᶜ id ∶ ★ ⇒ ★ =⇒ ★ ⇒ ★
id⇒⊢ = cast-fun (cast-id wf★) (cast-id wf★)

tag⇒⊢ : tag-or-idᵈ ∣ zero ∣ []
  ⊢ ★⇒★ ! ∶ ★ ⇒ ★ =⇒ ★
tag⇒⊢ = cast-tag wf★⇒★ refl tag-fun

F : Term
F = ƛ blame

vF : Value F
vF = ƛ blame

F⊒F : []ᵢ ∣ zero ∣ zero ∣ []ˢ ∣ []ᵍ
  ⊢ᴺ F ⊒ F ⦂ ★ ⇒ ★ ⊒ ★ ⇒ ★ ∶
    ((id , id★ʷ) ↦ᵇ (id , id★ⁿ))
F⊒F =
  ƛ⊒ƛ wf★ wf★ (⊒blame (⊢blame wf★))

downF⊒downF : []ᵢ ∣ zero ∣ zero ∣ []ˢ ∣ []ᵍ
  ⊢ᴺᵖ F ⟨ id ↦ᶜ id ⟩ ⊒ F ⟨ id ↦ᶜ id ⟩
    ⦂ ★ ⇒ ★ ⊒ᵖ ★ ⇒ ★ ∶ (id ↦ᶜ id , id⇒ⁿ)
downF⊒downF =
  down⊒down {d⊒ = id⇒ⁿ} {d′⊒ = id⇒ⁿ}
    F⊒F left-id-one-sidedᵢ
    right-id-one-sidedᵢ id⇒⊢ id⇒⊢ refl

taggedF⊒taggedF : []ᵢ ∣ zero ∣ zero ∣ []ˢ ∣ []ᵍ
  ⊢ᴺ F ⟨ id ↦ᶜ id ⟩ ⟨ ★⇒★ ! ⟩
    ⊒ F ⟨ id ↦ᶜ id ⟩ ⟨ ★⇒★ ! ⟩
    ⦂ ★ ⊒ ★ ∶ (id , id★ⁿ)
taggedF⊒taggedF =
  up⊒up {u⊑ = tag★⇒★} {u′⊑ = tag★⇒★}
    downF⊒downF left-id-one-sidedᵢ
    right-id-one-sidedᵢ tag⇒⊢ tag⇒⊢ refl

no-function-to-dynamic : ∀ {c}
  → []ᵢ ∣ zero ⊢ c ⦂ ★ ⇒ ★ ⊒ ★ ⊣ zero
  → ⊥
no-function-to-dynamic (idᵃ () b hA hB a⊒b)

LeftWideningTagInversion : Set₁
LeftWideningTagInversion =
  ∀ {V V′ B}
    {r : []ᵢ ∣ zero ⊢ ★ ⊒ B ⊣ zero}
  → Value V
  → Value V′
  → []ᵢ ∣ zero ∣ zero ∣ []ˢ ∣ []ᵍ
      ⊢ᴺ V ⟨ ★⇒★ ! ⟩ ⊒ V′ ⦂ ★ ⊒ B ∶ r
  → Σ[ p ∈ ([]ᵢ ∣ zero ⊢ (★ ⇒ ★) ⊒ B ⊣ zero) ]
      (dualʷ (★⇒★ ! , tag★⇒★)
        ⨟ˡⁿ[ left-id-one-sidedᵢ ] p ≐ⁿ r)
    × ([]ᵢ ∣ zero ∣ zero ∣ []ˢ ∣ []ᵍ
        ⊢ᴺ V ⊒ V′ ⦂ ★ ⇒ ★ ⊒ B ∶ p)

left-widening-tag-inversion-impossible :
  ¬ LeftWideningTagInversion
left-widening-tag-inversion-impossible invert =
  no-function-to-dynamic
    (proj₂
      (proj₁
        (invert
        (vF ⟨ id ↦ᶜ id ⟩)
        (vF ⟨ id ↦ᶜ id ⟩ ⟨ ★⇒★ ! ⟩)
        taggedF⊒taggedF)))
