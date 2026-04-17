module ReductionFresh where

-- File Charter:
--   * Alternative dynamic semantics for extrinsic-inst PolyUpDown terms.
--   * Fresh seals are allocated as `length Σ` (no global seal shifting),
--   * so store steps are not indexed by seal renamings.
--   * Includes one-step and multi-step reduction plus basic store invariants.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (length; []; _∷_)
open import Data.Nat using (ℕ; _+_; zero)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import TypeProperties
open import Store
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermProperties using (_[_]; _[_]ᵀ)
open import Reduction public
  using
    ( UpValue
    ; DownValue
    ; Value
    ; tag
    ; seal
    ; _↦_
    ; ∀ᵖ
    ; ν_
    ; ƛ_⇒_
    ; $
    ; Λ_
    ; _up_
    ; _down_
    ; _—→_
    ; β
    ; β-up-∀
    ; β-up-↦
    ; β-down-↦
    ; id-up
    ; id-down
    ; seal-unseal
    ; tag-untag-ok
    ; tag-untag-bad
    ; β-up-；
    ; β-down-；
    ; δ-⊕
    ; blame-·₁
    ; blame-·₂
    ; blame-·α
    ; blame-up
    ; blame-down
    ; blame-⊕₁
    ; blame-⊕₂
    )

------------------------------------------------------------------------
-- Raw values and raw one-step reduction are shared with `Reduction`
------------------------------------------------------------------------


infix 2 _∣_—→_∣_
data _∣_—→_∣_ :
  Store → Term → Store → Term → Set where

  id-step : ∀ {Σ : Store} {M M′ : Term} →
    M —→ M′ →
    Σ ∣ M —→ Σ ∣ M′

  -- Σ | (ΛX.V[X]) • A —→ (length Σ , A) :: Σ | V[α] up (B[α] ⇒ B[A])
  β-Λ : ∀ {Σ : Store} {A B : Ty} {V : Term} →
    Σ ∣ ((Λ V) ⦂∀ B [ A ]) —→ ((length Σ , A) ∷ Σ) ∣
      (((V [ ｀ (length Σ) ]ᵀ) up (instCast⊑ {A = A} {B = B} {α = length Σ})))

  β-down-∀ : ∀ {Σ : Store} {A B : Ty} {V : Term} {p : Down} →
    Value V →
    Σ ∣ ((V down (∀ᵖ p)) ⦂∀ B [ A ]) —→ ((length Σ , A) ∷ Σ) ∣
      ((((V ⦂∀ (down-src (⟰ᵗ Σ) p) [ ｀ (length Σ) ]) down (p [ ｀ (length Σ) ]↓))
         up (instCast⊑ {A = A} {B = down-tgt (⟰ᵗ Σ) p} {α = length Σ})))

  -- (V @- να.p[α]) • A —→ V @- p[length Σ] @+ (B[α] ⇒ B[A])
  β-down-ν : ∀ {Σ : Store} {A B : Ty} {V : Term} {p : Down} →
    Value V →
    Σ ∣ ((V down (ν p)) ⦂∀ B [ A ]) —→ ((length Σ , A) ∷ Σ) ∣
      (((V down (p [ length Σ ]⊒)) up (instCast⊑ {A = A} {B = B} {α = length Σ})))

  β-up-ν : ∀ {Σ : Store} {V : Term} {p : Up} →
    Value V →
    Σ ∣ (V up (ν p)) —→ ((length Σ , ★) ∷ Σ) ∣
      (((V ⦂∀
          (up-src ((length Σ , ★) ∷ Σ) (rename⊑ˢ (singleSealEnv (length Σ)) p))
          [ ｀ (length Σ) ])
         up (p [ length Σ ]⊑)))

  ξ-·₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} →
    Σ ∣ L —→ Σ′ ∣ L′ →
    Σ ∣ (L · M) —→ Σ′ ∣ (L′ · M)

  ξ-·₂ : ∀ {Σ Σ′ : Store} {V M M′ : Term} →
    Value V →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (V · M) —→ Σ′ ∣ (V · M′)

  ξ-·α : ∀ {Σ Σ′ : Store} {M M′ : Term} {B T : Ty} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M ⦂∀ B [ T ]) —→ Σ′ ∣ (M′ ⦂∀ B [ T ])

  ξ-up : ∀ {Σ Σ′ : Store} {p : Up} {M M′ : Term} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M up p) —→ Σ′ ∣ (M′ up p)

  ξ-down : ∀ {Σ Σ′ : Store} {p : Down} {M M′ : Term} →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (M down p) —→ Σ′ ∣ (M′ down p)

  ξ-⊕₁ : ∀ {Σ Σ′ : Store} {L M L′ : Term} {op : Prim} →
    Σ ∣ L —→ Σ′ ∣ L′ →
    Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L′ ⊕[ op ] M)

  ξ-⊕₂ : ∀ {Σ Σ′ : Store} {L M M′ : Term} {op : Prim} →
    Value L →
    Σ ∣ M —→ Σ′ ∣ M′ →
    Σ ∣ (L ⊕[ op ] M) —→ Σ′ ∣ (L ⊕[ op ] M′)

------------------------------------------------------------------------
-- Store growth witness extracted from one step
------------------------------------------------------------------------

store-growth :
  ∀ {Σ Σ′ : Store}{M M′ : Term} →
  Σ ∣ M —→ Σ′ ∣ M′ →
  Σ ⊆ˢ Σ′
store-growth (id-step red) = ⊆ˢ-refl
store-growth β-Λ = drop ⊆ˢ-refl
store-growth (β-down-∀ vV) = drop ⊆ˢ-refl
store-growth (β-down-ν vV) = drop ⊆ˢ-refl
store-growth (β-up-ν vV) = drop ⊆ˢ-refl
store-growth (ξ-·₁ red) = store-growth red
store-growth (ξ-·₂ v red) = store-growth red
store-growth (ξ-·α red) = store-growth red
store-growth (ξ-up red) = store-growth red
store-growth (ξ-down red) = store-growth red
store-growth (ξ-⊕₁ red) = store-growth red
store-growth (ξ-⊕₂ v red) = store-growth red

unique-store-step :
  ∀ {Σ Σ′ : Store}{M M′ : Term} →
  Uniqueˢ Σ →
  length Σ ∉domˢ Σ →
  Σ ∣ M —→ Σ′ ∣ M′ →
  Uniqueˢ Σ′
unique-store-step uΣ fresh (id-step red) = uΣ
unique-store-step uΣ fresh (β-Λ {A = A}) = uniq∷_ fresh uΣ
unique-store-step uΣ fresh (β-down-∀ {A = A} vV) = uniq∷_ fresh uΣ
unique-store-step uΣ fresh (β-down-ν {A = A} vV) = uniq∷_ fresh uΣ
unique-store-step uΣ fresh (β-up-ν {V = V} vV) = uniq∷_ fresh uΣ
unique-store-step uΣ fresh (ξ-·₁ red) = unique-store-step uΣ fresh red
unique-store-step uΣ fresh (ξ-·₂ v red) = unique-store-step uΣ fresh red
unique-store-step uΣ fresh (ξ-·α red) = unique-store-step uΣ fresh red
unique-store-step uΣ fresh (ξ-up red) = unique-store-step uΣ fresh red
unique-store-step uΣ fresh (ξ-down red) = unique-store-step uΣ fresh red
unique-store-step uΣ fresh (ξ-⊕₁ red) = unique-store-step uΣ fresh red
unique-store-step uΣ fresh (ξ-⊕₂ v red) = unique-store-step uΣ fresh red

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

infix 2 _∣_—↠_∣_
infix 3 _∎
infixr 2 _—→⟨_⟩_
infixr 2 _—↠⟨_⟩_

data _∣_—↠_∣_ :
  Store → Term → Store → Term → Set where
  _∎ : ∀ {Σ : Store} (M : Term) →
    Σ ∣ M —↠ Σ ∣ M

  _—→⟨_⟩_ :
    ∀ {Σ Σ′ Σ″ : Store} {M N : Term} →
    (L : Term) →
    Σ ∣ L —→ Σ′ ∣ M →
    Σ′ ∣ M —↠ Σ″ ∣ N →
    Σ ∣ L —↠ Σ″ ∣ N

multi-trans :
  ∀ {Σ Σ′ Σ″ : Store}
    {L M N : Term} →
  Σ ∣ L —↠ Σ′ ∣ M →
  Σ′ ∣ M —↠ Σ″ ∣ N →
  Σ ∣ L —↠ Σ″ ∣ N
multi-trans (_ ∎) M—↠N = M—↠N
multi-trans (_ —→⟨ L—→M ⟩ M—↠N) N—↠P =
  _ —→⟨ L—→M ⟩ multi-trans M—↠N N—↠P

_—↠⟨_⟩_ :
  ∀ {Σ Σ′ Σ″ : Store}
    (L : Term)
    {M N : Term} →
  Σ ∣ L —↠ Σ′ ∣ M →
  Σ′ ∣ M —↠ Σ″ ∣ N →
  Σ ∣ L —↠ Σ″ ∣ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N
