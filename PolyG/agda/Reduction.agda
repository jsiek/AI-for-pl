module Reduction where

-- File Charter:
--   * Values, evaluation frames and the reduction relation of PolyCν
--     (thesis Fig. 10.11), ∀ν fragment.
--   * Frames are call-by-value: the right frame of an application
--     requires a value on the left, so reduction is deterministic.
--   * A configuration is a store Σ (the types of the seals created so
--     far) and a term.  The only rule that changes the store is
--     instantiation, which creates the seal `length Σ`.

open import Data.List using (List; []; _∷_; length; _++_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Terms

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : Term → Set where
  V-true  : Value true
  V-false : Value false
  V-ƛ     : ∀ {A M} → Value (ƛ A M)
  V-Λν    : ∀ {cs M} → Value (Λν cs M)
  V-seal  : ∀ {α V} → Value V → Value (seal α V)
  V-inj   : ∀ {G V} → Value V → Value (inj G V)
  V-cast⇒ : ∀ {d p q V} → Value V → Value (cast d (p ⇒⊑ q) V)

------------------------------------------------------------------------
-- Frames
------------------------------------------------------------------------

data Frame : Set where
  if□     : Term → Term → Frame
  □·_     : Term → Frame
  app□    : (V : Term) → Value V → Frame
  letv□   : Term → Frame
  seal□   : Name → Frame
  unseal□ : Name → Frame
  is□     : Ground → Frame
  inj□    : Ground → Frame
  cast□   : Dir → Prec → Frame
  inst□   : Ty → Prec → Term → Frame

plug : Frame → Term → Term
plug (if□ M N) L = if L M N
plug (□· M) L = L · M
plug (app□ V v) M = V · M
plug (letv□ N) M = letv M N
plug (seal□ α) M = seal α M
plug (unseal□ α) M = unseal α M
plug (is□ G) M = is G M
plug (inj□ G) M = inj G M
plug (cast□ d p) M = cast d p M
plug (inst□ B ℓ N) M = inst M B ℓ N

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

-- the precision derivations whose casts are the identity
data Atomic : Prec → Set where
  at★ : Atomic ★⊑
  at𝔹 : Atomic 𝔹⊑
  at‵ : ∀ {α} → Atomic (‵⊑ α)

infix 2 _▷_—→_▷_

data _▷_—→_▷_ : Store → Term → Store → Term → Set where
  ξξ : ∀ {Σ Σ′ M N M′ N′} (F : Frame) →
    M′ ≡ plug F M →
    N′ ≡ plug F N →
    Σ ▷ M —→ Σ′ ▷ N →
    Σ ▷ M′ —→ Σ′ ▷ N′

  ξξ-℧ : ∀ {Σ M′} (F : Frame) →
    M′ ≡ plug F ℧ →
    Σ ▷ M′ —→ Σ ▷ ℧

  β-letv : ∀ {Σ V N} →
    Value V →
    Σ ▷ letv V N —→ Σ ▷ N [ V ]

  β-unseal : ∀ {Σ α V} →
    Value V →
    Σ ▷ unseal α (seal α V) —→ Σ ▷ V

  β-is-yes : ∀ {Σ G V} →
    Value V →
    Σ ▷ is G (inj G V) —→ Σ ▷ true

  β-is-no : ∀ {Σ G H V} →
    Value V →
    G ≢ H →
    Σ ▷ is G (inj H V) —→ Σ ▷ false

  β-if-true : ∀ {Σ M N} →
    Σ ▷ if true M N —→ Σ ▷ M

  β-if-false : ∀ {Σ M N} →
    Σ ▷ if false M N —→ Σ ▷ N

  β-ƛ : ∀ {Σ A M V} →
    Value V →
    Σ ▷ ƛ A M · V —→ Σ ▷ M [ V ]

  β-cast⇒ : ∀ {Σ d p q V W} →
    Value V →
    Value W →
    Σ ▷ cast d (p ⇒⊑ q) V · W —→ Σ ▷ cast d q (V · cast (flip d) p W)

  -- instantiation creates the seal `length Σ` with type B and label ℓ
  β-inst : ∀ {Σ cs M B ℓ N} →
    Σ ▷ inst (Λν cs M) B ℓ N
      —→ (Σ ++ ((B , ℓ) ∷ [])) ▷
         letv (stack cs M [ tseal (length Σ) ]ᵀ) (N [ tseal (length Σ) ]ᵀ)

  β-id : ∀ {Σ d p V} →
    Atomic p →
    Value V →
    Σ ▷ cast d p V —→ Σ ▷ V

  β-tag-up : ∀ {Σ G p V} →
    Value V →
    Σ ▷ cast up (tag G p) V —→ Σ ▷ inj G (cast up p V)

  β-tag-down : ∀ {Σ G p V} →
    Value V →
    Σ ▷ cast down (tag G p) (inj G V) —→ Σ ▷ cast down p V

  β-tag-down-℧ : ∀ {Σ G H p V} →
    Value V →
    G ≢ H →
    Σ ▷ cast down (tag G p) (inj H V) —→ Σ ▷ ℧

  -- a ∀ν cast on a proxy pushes its body cast onto the stack
  β-cast∀ : ∀ {Σ d p cs M} →
    Σ ▷ cast d (∀⊑ p) (Λν cs M) —→ Σ ▷ Λν ((d , p) ∷ cs) M

pattern ξ F M→N = ξξ F refl refl M→N
pattern ξ-℧ F = ξξ-℧ F refl

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

infix 2 _▷_—↠_▷_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _▷_—↠_▷_ : Store → Term → Store → Term → Set where
  _∎ : ∀ {Σ} M → Σ ▷ M —↠ Σ ▷ M
  _—→⟨_⟩_ : ∀ {Σ Σ′ Σ″} L {M N} →
    Σ ▷ L —→ Σ′ ▷ M →
    Σ′ ▷ M —↠ Σ″ ▷ N →
    Σ ▷ L —↠ Σ″ ▷ N
