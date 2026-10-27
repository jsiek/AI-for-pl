module proof.DenotRelation where

-- File Charter:
--   * The two relations between denotations used for the denotational proof
--     of the dynamic gradual guarantee (GTLC/notes/denotational-gg.md):
--       p ⊢ d ◃ D′   a left (less precise) element justified by a right set
--                    (preservation: the right side does it too, or blames);
--       p ⊢ D ▹ d′   a right (more precise) element justified by a left set
--                    (reflection: the left side does it too).
--   * Each is defined by recursion on its element; functions are related
--     through application to whole argument sets.
--   * Basic lemmas: monotonicity, convergence transfer, and restriction of
--     the set side to its values.

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Polymorphic using () renaming (⊥ to ⊥₁)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤₁; tt to tt₁)
import Level
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import GraphModel
open import proof.DenotProps using (⌊⌋-mono; ⌊⌋-⊆)

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

Lift₁ : Set → Set₁
Lift₁ = Lift (Level.suc Level.zero)

tag⊑ : (t : Tag) → tagTy t ⊑ tagTy t
tag⊑ ℕᵗ = ⊑-ℕ
tag⊑ ⇒ᵗ = ⊑-⇒ ⊑-★ ⊑-★

------------------------------------------------------------------------
-- Preservation: a left element justified by a right set
------------------------------------------------------------------------

infix 4 _⊢_◃_ _⊢_◃ᵛ_ _⊢_◃*_

mutual
  _⊢_◃_ : ∀ {A A′} → A ⊑ A′ → Val → 𝒫 → Set₁
  p ⊢ d ◃ D′ = Lift₁ (ω ∈ D′) ⊎ p ⊢ d ◃ᵛ D′

  _⊢_◃ᵛ_ : ∀ {A A′} → A ⊑ A′ → Val → 𝒫 → Set₁
  ⊑-ℕ ⊢ nat n ◃ᵛ D′ = Lift₁ (nat n ∈ D′)
  ⊑-ℕ ⊢ V ⟼ w ◃ᵛ D′ = ⊥₁
  ⊑-ℕ ⊢ ν ◃ᵛ D′ = ⊥₁
  ⊑-ℕ ⊢ ω ◃ᵛ D′ = ⊥₁
  ⊑-ℕ ⊢ tag t u ◃ᵛ D′ = ⊥₁
  (⊑-★ {★}) ⊢ nat n ◃ᵛ D′ = ⊥₁
  (⊑-★ {★}) ⊢ V ⟼ w ◃ᵛ D′ = ⊥₁
  (⊑-★ {★}) ⊢ ν ◃ᵛ D′ = ⊥₁
  (⊑-★ {★}) ⊢ ω ◃ᵛ D′ = ⊥₁
  (⊑-★ {★}) ⊢ tag t u ◃ᵛ D′ = tag⊑ t ⊢ u ◃ᵛ untag t D′
  (⊑-★ {ℕ}) ⊢ nat n ◃ᵛ D′ = ⊥₁
  (⊑-★ {ℕ}) ⊢ V ⟼ w ◃ᵛ D′ = ⊥₁
  (⊑-★ {ℕ}) ⊢ ν ◃ᵛ D′ = ⊥₁
  (⊑-★ {ℕ}) ⊢ ω ◃ᵛ D′ = ⊥₁
  (⊑-★ {ℕ}) ⊢ tag ℕᵗ u ◃ᵛ D′ = ⊑-ℕ ⊢ u ◃ᵛ D′
  (⊑-★ {ℕ}) ⊢ tag ⇒ᵗ u ◃ᵛ D′ = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ nat n ◃ᵛ D′ = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ V ⟼ w ◃ᵛ D′ = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ ν ◃ᵛ D′ = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ ω ◃ᵛ D′ = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ tag ℕᵗ u ◃ᵛ D′ = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ tag ⇒ᵗ u ◃ᵛ D′ = ⊑-⇒ (⊑-★ {A}) (⊑-★ {B}) ⊢ u ◃ᵛ D′
  ⊑-⇒ p q ⊢ nat n ◃ᵛ D′ = ⊥₁
  ⊑-⇒ p q ⊢ U ⟼ w ◃ᵛ D′ =
    Lift₁ (ν ∈ D′)
    × (∀ E′ → ValSet E′ → p ⊢ U ◃* E′ → q ⊢ w ◃ (⌊ D′ ⌋ ● E′))
  ⊑-⇒ p q ⊢ ν ◃ᵛ D′ = Lift₁ (ν ∈ D′)
  ⊑-⇒ p q ⊢ ω ◃ᵛ D′ = ⊥₁
  ⊑-⇒ p q ⊢ tag t u ◃ᵛ D′ = ⊥₁

  _⊢_◃*_ : ∀ {A A′} → A ⊑ A′ → List Val → 𝒫 → Set₁
  p ⊢ [] ◃* D′ = ⊤₁
  p ⊢ (u ∷ U) ◃* D′ = p ⊢ u ◃ D′ × p ⊢ U ◃* D′

------------------------------------------------------------------------
-- Reflection: a right element justified by a left set
------------------------------------------------------------------------

infix 4 _⊢_▹_ _⊢_▹ᵛ_ _⊢_▹*_

mutual
  _⊢_▹_ : ∀ {A A′} → A ⊑ A′ → 𝒫 → Val → Set₁
  p ⊢ D ▹ d′ = Lift₁ (d′ ≡ ω) ⊎ p ⊢ D ▹ᵛ d′

  _⊢_▹ᵛ_ : ∀ {A A′} → A ⊑ A′ → 𝒫 → Val → Set₁
  ⊑-ℕ ⊢ D ▹ᵛ nat n = Lift₁ (nat n ∈ D)
  ⊑-ℕ ⊢ D ▹ᵛ V′ ⟼ w′ = ⊥₁
  ⊑-ℕ ⊢ D ▹ᵛ ν = ⊥₁
  ⊑-ℕ ⊢ D ▹ᵛ ω = ⊥₁
  ⊑-ℕ ⊢ D ▹ᵛ tag t u′ = ⊥₁
  (⊑-★ {★}) ⊢ D ▹ᵛ nat n = ⊥₁
  (⊑-★ {★}) ⊢ D ▹ᵛ V′ ⟼ w′ = ⊥₁
  (⊑-★ {★}) ⊢ D ▹ᵛ ν = ⊥₁
  (⊑-★ {★}) ⊢ D ▹ᵛ ω = ⊥₁
  (⊑-★ {★}) ⊢ D ▹ᵛ tag t u′ = tag⊑ t ⊢ untag t D ▹ᵛ u′
  (⊑-★ {ℕ}) ⊢ D ▹ᵛ nat n = Lift₁ (tag ℕᵗ (nat n) ∈ D)
  (⊑-★ {ℕ}) ⊢ D ▹ᵛ V′ ⟼ w′ = ⊥₁
  (⊑-★ {ℕ}) ⊢ D ▹ᵛ ν = ⊥₁
  (⊑-★ {ℕ}) ⊢ D ▹ᵛ ω = ⊥₁
  (⊑-★ {ℕ}) ⊢ D ▹ᵛ tag t u′ = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ D ▹ᵛ nat n = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ D ▹ᵛ V′ ⟼ w′ =
    Lift₁ (tag ⇒ᵗ ν ∈ D)
    × (∀ E → ValSet E → ⊑-★ {A} ⊢ E ▹* V′
         → ⊑-★ {B} ⊢ (⌊ untag ⇒ᵗ D ⌋ ● E) ▹ w′)
  (⊑-★ {A ⇒ B}) ⊢ D ▹ᵛ ν = Lift₁ (tag ⇒ᵗ ν ∈ D)
  (⊑-★ {A ⇒ B}) ⊢ D ▹ᵛ ω = ⊥₁
  (⊑-★ {A ⇒ B}) ⊢ D ▹ᵛ tag t u′ = ⊥₁
  ⊑-⇒ p q ⊢ D ▹ᵛ nat n = ⊥₁
  ⊑-⇒ p q ⊢ D ▹ᵛ V′ ⟼ w′ =
    Lift₁ (ν ∈ D)
    × (∀ E → ValSet E → p ⊢ E ▹* V′ → q ⊢ (⌊ D ⌋ ● E) ▹ w′)
  ⊑-⇒ p q ⊢ D ▹ᵛ ν = Lift₁ (ν ∈ D)
  ⊑-⇒ p q ⊢ D ▹ᵛ ω = ⊥₁
  ⊑-⇒ p q ⊢ D ▹ᵛ tag t u′ = ⊥₁

  _⊢_▹*_ : ∀ {A A′} → A ⊑ A′ → 𝒫 → List Val → Set₁
  p ⊢ E ▹* [] = ⊤₁
  p ⊢ E ▹* (v′ ∷ V′) = p ⊢ E ▹ v′ × p ⊢ E ▹* V′

------------------------------------------------------------------------
-- Sets
------------------------------------------------------------------------

infix 4 _⊢_◃ˢ_ _⊢_▹ˢ_

_⊢_◃ˢ_ : ∀ {A A′} → A ⊑ A′ → 𝒫 → 𝒫 → Set₁
p ⊢ D ◃ˢ D′ = ∀ d → d ∈ D → p ⊢ d ◃ D′

_⊢_▹ˢ_ : ∀ {A A′} → A ⊑ A′ → 𝒫 → 𝒫 → Set₁
p ⊢ D ▹ˢ D′ = ∀ d′ → d′ ∈ D′ → p ⊢ D ▹ d′

------------------------------------------------------------------------
-- Set lemmas
------------------------------------------------------------------------

⌊⌋-idem : ∀ {D} → ⌊ D ⌋ ⊆ ⌊ ⌊ D ⌋ ⌋
⌊⌋-idem d (d∈ , d≢) = (d∈ , d≢) , d≢

●-monoˡ : ∀ {D D′ E} → D ⊆ D′ → (D ● E) ⊆ (D′ ● E)
●-monoˡ sub w (V , e∈ , V⊆ , V≢) = V , sub _ e∈ , V⊆ , V≢

●-monoʳ : ∀ {D E E′} → E ⊆ E′ → (D ● E) ⊆ (D ● E′)
●-monoʳ sub w (V , e∈ , V⊆ , V≢) =
  V , e∈ , (λ d d∈ → sub d (V⊆ d d∈)) , V≢

untag-⌊⌋ : ∀ {t D} → untag t D ⊆ untag t ⌊ D ⌋
untag-⌊⌋ v v∈ = v∈ , λ ()

------------------------------------------------------------------------
-- Monotonicity in the set side
------------------------------------------------------------------------

mutual
  ◃-mono : ∀ {A A′} (p : A ⊑ A′) d {D′ D″}
    → D′ ⊆ D″ → p ⊢ d ◃ D′ → p ⊢ d ◃ D″
  ◃-mono p d sub (inj₁ (lift ω∈)) = inj₁ (lift (sub ω ω∈))
  ◃-mono p d sub (inj₂ r) = inj₂ (◃ᵛ-mono p d sub r)

  ◃ᵛ-mono : ∀ {A A′} (p : A ⊑ A′) d {D′ D″}
    → D′ ⊆ D″ → p ⊢ d ◃ᵛ D′ → p ⊢ d ◃ᵛ D″
  ◃ᵛ-mono ⊑-ℕ (nat n) sub (lift m) = lift (sub _ m)
  ◃ᵛ-mono ⊑-ℕ (V ⟼ w) sub ()
  ◃ᵛ-mono ⊑-ℕ ν sub ()
  ◃ᵛ-mono ⊑-ℕ ω sub ()
  ◃ᵛ-mono ⊑-ℕ (tag t u) sub ()
  ◃ᵛ-mono (⊑-★ {★}) (nat n) sub ()
  ◃ᵛ-mono (⊑-★ {★}) (V ⟼ w) sub ()
  ◃ᵛ-mono (⊑-★ {★}) ν sub ()
  ◃ᵛ-mono (⊑-★ {★}) ω sub ()
  ◃ᵛ-mono (⊑-★ {★}) (tag t u) sub r =
    ◃ᵛ-mono (tag⊑ t) u (λ v → sub (tag t v)) r
  ◃ᵛ-mono (⊑-★ {ℕ}) (nat n) sub ()
  ◃ᵛ-mono (⊑-★ {ℕ}) (V ⟼ w) sub ()
  ◃ᵛ-mono (⊑-★ {ℕ}) ν sub ()
  ◃ᵛ-mono (⊑-★ {ℕ}) ω sub ()
  ◃ᵛ-mono (⊑-★ {ℕ}) (tag ℕᵗ u) sub r = ◃ᵛ-mono ⊑-ℕ u sub r
  ◃ᵛ-mono (⊑-★ {ℕ}) (tag ⇒ᵗ u) sub ()
  ◃ᵛ-mono (⊑-★ {A ⇒ B}) (nat n) sub ()
  ◃ᵛ-mono (⊑-★ {A ⇒ B}) (V ⟼ w) sub ()
  ◃ᵛ-mono (⊑-★ {A ⇒ B}) ν sub ()
  ◃ᵛ-mono (⊑-★ {A ⇒ B}) ω sub ()
  ◃ᵛ-mono (⊑-★ {A ⇒ B}) (tag ℕᵗ u) sub ()
  ◃ᵛ-mono (⊑-★ {A ⇒ B}) (tag ⇒ᵗ u) sub r =
    ◃ᵛ-mono (⊑-⇒ (⊑-★ {A}) (⊑-★ {B})) u sub r
  ◃ᵛ-mono (⊑-⇒ p q) (nat n) sub ()
  ◃ᵛ-mono (⊑-⇒ p q) (U ⟼ w) sub (lift ν∈ , f) =
    lift (sub ν ν∈)
    , λ E′ vE′ rU → ◃-mono q w (●-monoˡ (⌊⌋-mono sub)) (f E′ vE′ rU)
  ◃ᵛ-mono (⊑-⇒ p q) ν sub (lift ν∈) = lift (sub ν ν∈)
  ◃ᵛ-mono (⊑-⇒ p q) ω sub ()
  ◃ᵛ-mono (⊑-⇒ p q) (tag t u) sub ()

mutual
  ▹-mono : ∀ {A A′} (p : A ⊑ A′) d′ {D D″}
    → D ⊆ D″ → p ⊢ D ▹ d′ → p ⊢ D″ ▹ d′
  ▹-mono p d′ sub (inj₁ eq) = inj₁ eq
  ▹-mono p d′ sub (inj₂ r) = inj₂ (▹ᵛ-mono p d′ sub r)

  ▹ᵛ-mono : ∀ {A A′} (p : A ⊑ A′) d′ {D D″}
    → D ⊆ D″ → p ⊢ D ▹ᵛ d′ → p ⊢ D″ ▹ᵛ d′
  ▹ᵛ-mono ⊑-ℕ (nat n) sub (lift m) = lift (sub _ m)
  ▹ᵛ-mono ⊑-ℕ (V ⟼ w) sub ()
  ▹ᵛ-mono ⊑-ℕ ν sub ()
  ▹ᵛ-mono ⊑-ℕ ω sub ()
  ▹ᵛ-mono ⊑-ℕ (tag t u) sub ()
  ▹ᵛ-mono (⊑-★ {★}) (nat n) sub ()
  ▹ᵛ-mono (⊑-★ {★}) (V ⟼ w) sub ()
  ▹ᵛ-mono (⊑-★ {★}) ν sub ()
  ▹ᵛ-mono (⊑-★ {★}) ω sub ()
  ▹ᵛ-mono (⊑-★ {★}) (tag t u) sub r =
    ▹ᵛ-mono (tag⊑ t) u (λ v → sub (tag t v)) r
  ▹ᵛ-mono (⊑-★ {ℕ}) (nat n) sub (lift m) = lift (sub _ m)
  ▹ᵛ-mono (⊑-★ {ℕ}) (V ⟼ w) sub ()
  ▹ᵛ-mono (⊑-★ {ℕ}) ν sub ()
  ▹ᵛ-mono (⊑-★ {ℕ}) ω sub ()
  ▹ᵛ-mono (⊑-★ {ℕ}) (tag t u) sub ()
  ▹ᵛ-mono (⊑-★ {A ⇒ B}) (nat n) sub ()
  ▹ᵛ-mono (⊑-★ {A ⇒ B}) (V ⟼ w) sub (lift m , f) =
    lift (sub _ m)
    , λ E vE rV → ▹-mono (⊑-★ {B}) w
        (●-monoˡ (⌊⌋-mono (λ v → sub (tag ⇒ᵗ v)))) (f E vE rV)
  ▹ᵛ-mono (⊑-★ {A ⇒ B}) ν sub (lift m) = lift (sub _ m)
  ▹ᵛ-mono (⊑-★ {A ⇒ B}) ω sub ()
  ▹ᵛ-mono (⊑-★ {A ⇒ B}) (tag t u) sub ()
  ▹ᵛ-mono (⊑-⇒ p q) (nat n) sub ()
  ▹ᵛ-mono (⊑-⇒ p q) (V ⟼ w) sub (lift m , f) =
    lift (sub _ m)
    , λ E vE rV → ▹-mono q w (●-monoˡ (⌊⌋-mono sub)) (f E vE rV)
  ▹ᵛ-mono (⊑-⇒ p q) ν sub (lift m) = lift (sub _ m)
  ▹ᵛ-mono (⊑-⇒ p q) ω sub ()
  ▹ᵛ-mono (⊑-⇒ p q) (tag t u) sub ()

------------------------------------------------------------------------
-- Convergence transfer
------------------------------------------------------------------------

◃ᵛ-conv : ∀ {A A′} (p : A ⊑ A′) d {D′} → p ⊢ d ◃ᵛ D′ → Conv D′
◃ᵛ-conv ⊑-ℕ (nat n) (lift m) = nat n , m , λ ()
◃ᵛ-conv ⊑-ℕ (V ⟼ w) ()
◃ᵛ-conv ⊑-ℕ ν ()
◃ᵛ-conv ⊑-ℕ ω ()
◃ᵛ-conv ⊑-ℕ (tag t u) ()
◃ᵛ-conv (⊑-★ {★}) (nat n) ()
◃ᵛ-conv (⊑-★ {★}) (V ⟼ w) ()
◃ᵛ-conv (⊑-★ {★}) ν ()
◃ᵛ-conv (⊑-★ {★}) ω ()
◃ᵛ-conv (⊑-★ {★}) (tag t u) r
    with ◃ᵛ-conv (tag⊑ t) u r
... | v , m , _ = tag t v , m , λ ()
◃ᵛ-conv (⊑-★ {ℕ}) (nat n) ()
◃ᵛ-conv (⊑-★ {ℕ}) (V ⟼ w) ()
◃ᵛ-conv (⊑-★ {ℕ}) ν ()
◃ᵛ-conv (⊑-★ {ℕ}) ω ()
◃ᵛ-conv (⊑-★ {ℕ}) (tag ℕᵗ u) r = ◃ᵛ-conv ⊑-ℕ u r
◃ᵛ-conv (⊑-★ {ℕ}) (tag ⇒ᵗ u) ()
◃ᵛ-conv (⊑-★ {A ⇒ B}) (nat n) ()
◃ᵛ-conv (⊑-★ {A ⇒ B}) (V ⟼ w) ()
◃ᵛ-conv (⊑-★ {A ⇒ B}) ν ()
◃ᵛ-conv (⊑-★ {A ⇒ B}) ω ()
◃ᵛ-conv (⊑-★ {A ⇒ B}) (tag ℕᵗ u) ()
◃ᵛ-conv (⊑-★ {A ⇒ B}) (tag ⇒ᵗ u) r =
  ◃ᵛ-conv (⊑-⇒ (⊑-★ {A}) (⊑-★ {B})) u r
◃ᵛ-conv (⊑-⇒ p q) (nat n) ()
◃ᵛ-conv (⊑-⇒ p q) (U ⟼ w) (lift ν∈ , _) = ν , ν∈ , λ ()
◃ᵛ-conv (⊑-⇒ p q) ν (lift ν∈) = ν , ν∈ , λ ()
◃ᵛ-conv (⊑-⇒ p q) ω ()
◃ᵛ-conv (⊑-⇒ p q) (tag t u) ()

▹ᵛ-conv : ∀ {A A′} (p : A ⊑ A′) d′ {D} → p ⊢ D ▹ᵛ d′ → Conv D
▹ᵛ-conv ⊑-ℕ (nat n) (lift m) = nat n , m , λ ()
▹ᵛ-conv ⊑-ℕ (V ⟼ w) ()
▹ᵛ-conv ⊑-ℕ ν ()
▹ᵛ-conv ⊑-ℕ ω ()
▹ᵛ-conv ⊑-ℕ (tag t u) ()
▹ᵛ-conv (⊑-★ {★}) (nat n) ()
▹ᵛ-conv (⊑-★ {★}) (V ⟼ w) ()
▹ᵛ-conv (⊑-★ {★}) ν ()
▹ᵛ-conv (⊑-★ {★}) ω ()
▹ᵛ-conv (⊑-★ {★}) (tag t u) r
    with ▹ᵛ-conv (tag⊑ t) u r
... | v , m , _ = tag t v , m , λ ()
▹ᵛ-conv (⊑-★ {ℕ}) (nat n) (lift m) = tag ℕᵗ (nat n) , m , λ ()
▹ᵛ-conv (⊑-★ {ℕ}) (V ⟼ w) ()
▹ᵛ-conv (⊑-★ {ℕ}) ν ()
▹ᵛ-conv (⊑-★ {ℕ}) ω ()
▹ᵛ-conv (⊑-★ {ℕ}) (tag t u) ()
▹ᵛ-conv (⊑-★ {A ⇒ B}) (nat n) ()
▹ᵛ-conv (⊑-★ {A ⇒ B}) (V ⟼ w) (lift m , _) = tag ⇒ᵗ ν , m , λ ()
▹ᵛ-conv (⊑-★ {A ⇒ B}) ν (lift m) = tag ⇒ᵗ ν , m , λ ()
▹ᵛ-conv (⊑-★ {A ⇒ B}) ω ()
▹ᵛ-conv (⊑-★ {A ⇒ B}) (tag t u) ()
▹ᵛ-conv (⊑-⇒ p q) (nat n) ()
▹ᵛ-conv (⊑-⇒ p q) (V ⟼ w) (lift m , _) = ν , m , λ ()
▹ᵛ-conv (⊑-⇒ p q) ν (lift m) = ν , m , λ ()
▹ᵛ-conv (⊑-⇒ p q) ω ()
▹ᵛ-conv (⊑-⇒ p q) (tag t u) ()

------------------------------------------------------------------------
-- Only the values of the set side matter
------------------------------------------------------------------------

◃ᵛ-vals : ∀ {A A′} (p : A ⊑ A′) d {D′}
  → p ⊢ d ◃ᵛ D′ → p ⊢ d ◃ᵛ ⌊ D′ ⌋
◃ᵛ-vals ⊑-ℕ (nat n) (lift m) = lift (m , λ ())
◃ᵛ-vals ⊑-ℕ (V ⟼ w) ()
◃ᵛ-vals ⊑-ℕ ν ()
◃ᵛ-vals ⊑-ℕ ω ()
◃ᵛ-vals ⊑-ℕ (tag t u) ()
◃ᵛ-vals (⊑-★ {★}) (nat n) ()
◃ᵛ-vals (⊑-★ {★}) (V ⟼ w) ()
◃ᵛ-vals (⊑-★ {★}) ν ()
◃ᵛ-vals (⊑-★ {★}) ω ()
◃ᵛ-vals (⊑-★ {★}) (tag t u) {D′} r =
  ◃ᵛ-mono (tag⊑ t) u (untag-⌊⌋ {t} {D′}) r
◃ᵛ-vals (⊑-★ {ℕ}) (nat n) ()
◃ᵛ-vals (⊑-★ {ℕ}) (V ⟼ w) ()
◃ᵛ-vals (⊑-★ {ℕ}) ν ()
◃ᵛ-vals (⊑-★ {ℕ}) ω ()
◃ᵛ-vals (⊑-★ {ℕ}) (tag ℕᵗ u) r = ◃ᵛ-vals ⊑-ℕ u r
◃ᵛ-vals (⊑-★ {ℕ}) (tag ⇒ᵗ u) ()
◃ᵛ-vals (⊑-★ {A ⇒ B}) (nat n) ()
◃ᵛ-vals (⊑-★ {A ⇒ B}) (V ⟼ w) ()
◃ᵛ-vals (⊑-★ {A ⇒ B}) ν ()
◃ᵛ-vals (⊑-★ {A ⇒ B}) ω ()
◃ᵛ-vals (⊑-★ {A ⇒ B}) (tag ℕᵗ u) ()
◃ᵛ-vals (⊑-★ {A ⇒ B}) (tag ⇒ᵗ u) r =
  ◃ᵛ-vals (⊑-⇒ (⊑-★ {A}) (⊑-★ {B})) u r
◃ᵛ-vals (⊑-⇒ p q) (nat n) ()
◃ᵛ-vals (⊑-⇒ p q) (U ⟼ w) {D′} (lift ν∈ , f) =
  lift (ν∈ , λ ())
  , λ E′ vE′ rU → ◃-mono q w (●-monoˡ (⌊⌋-idem {D′})) (f E′ vE′ rU)
◃ᵛ-vals (⊑-⇒ p q) ν (lift ν∈) = lift (ν∈ , λ ())
◃ᵛ-vals (⊑-⇒ p q) ω ()
◃ᵛ-vals (⊑-⇒ p q) (tag t u) ()

▹ᵛ-vals : ∀ {A A′} (p : A ⊑ A′) d′ {D}
  → p ⊢ D ▹ᵛ d′ → p ⊢ ⌊ D ⌋ ▹ᵛ d′
▹ᵛ-vals ⊑-ℕ (nat n) (lift m) = lift (m , λ ())
▹ᵛ-vals ⊑-ℕ (V ⟼ w) ()
▹ᵛ-vals ⊑-ℕ ν ()
▹ᵛ-vals ⊑-ℕ ω ()
▹ᵛ-vals ⊑-ℕ (tag t u) ()
▹ᵛ-vals (⊑-★ {★}) (nat n) ()
▹ᵛ-vals (⊑-★ {★}) (V ⟼ w) ()
▹ᵛ-vals (⊑-★ {★}) ν ()
▹ᵛ-vals (⊑-★ {★}) ω ()
▹ᵛ-vals (⊑-★ {★}) (tag t u) {D} r =
  ▹ᵛ-mono (tag⊑ t) u (untag-⌊⌋ {t} {D}) r
▹ᵛ-vals (⊑-★ {ℕ}) (nat n) (lift m) = lift (m , λ ())
▹ᵛ-vals (⊑-★ {ℕ}) (V ⟼ w) ()
▹ᵛ-vals (⊑-★ {ℕ}) ν ()
▹ᵛ-vals (⊑-★ {ℕ}) ω ()
▹ᵛ-vals (⊑-★ {ℕ}) (tag t u) ()
▹ᵛ-vals (⊑-★ {A ⇒ B}) (nat n) ()
▹ᵛ-vals (⊑-★ {A ⇒ B}) (V ⟼ w) {D} (lift m , f) =
  lift (m , λ ())
  , λ E vE rV → ▹-mono (⊑-★ {B}) w
      (●-monoˡ (⌊⌋-mono (untag-⌊⌋ {⇒ᵗ} {D}))) (f E vE rV)
▹ᵛ-vals (⊑-★ {A ⇒ B}) ν (lift m) = lift (m , λ ())
▹ᵛ-vals (⊑-★ {A ⇒ B}) ω ()
▹ᵛ-vals (⊑-★ {A ⇒ B}) (tag t u) ()
▹ᵛ-vals (⊑-⇒ p q) (nat n) ()
▹ᵛ-vals (⊑-⇒ p q) (V ⟼ w) {D} (lift m , f) =
  lift (m , λ ())
  , λ E vE rV → ▹-mono q w (●-monoˡ (⌊⌋-idem {D})) (f E vE rV)
▹ᵛ-vals (⊑-⇒ p q) ν (lift m) = lift (m , λ ())
▹ᵛ-vals (⊑-⇒ p q) ω ()
▹ᵛ-vals (⊑-⇒ p q) (tag t u) ()

------------------------------------------------------------------------
-- Errors, lists, and finite escapes
------------------------------------------------------------------------

◃ᵛ-ω : ∀ {A A′} (p : A ⊑ A′) {D′} → p ⊢ ω ◃ᵛ D′ → ⊥
◃ᵛ-ω ⊑-ℕ ()
◃ᵛ-ω (⊑-★ {★}) ()
◃ᵛ-ω (⊑-★ {ℕ}) ()
◃ᵛ-ω (⊑-★ {A ⇒ B}) ()
◃ᵛ-ω (⊑-⇒ p q) ()

-- a left error is justified only by a right error
◃-ω : ∀ {A A′} (p : A ⊑ A′) {D′} → p ⊢ ω ◃ D′ → ω ∈ D′
◃-ω p (inj₁ (lift ω∈)) = ω∈
◃-ω p (inj₂ r) = ⊥-elim (◃ᵛ-ω p r)

-- against a value set, preservation has no escape
◃-val : ∀ {A A′} (p : A ⊑ A′) d {D′}
  → ValSet D′ → p ⊢ d ◃ D′ → p ⊢ d ◃ᵛ D′
◃-val p d vD′ (inj₁ (lift ω∈)) = ⊥-elim (vD′ ω∈)
◃-val p d vD′ (inj₂ r) = r

-- a right value needs a left value
▹-val : ∀ {A A′} (p : A ⊑ A′) d′ {D}
  → d′ ≢ ω → p ⊢ D ▹ d′ → p ⊢ D ▹ᵛ d′
▹-val p d′ d′≢ (inj₁ (lift eq)) = ⊥-elim (d′≢ eq)
▹-val p d′ d′≢ (inj₂ r) = r

◃*-∈ : ∀ {A A′} (p : A ⊑ A′) {U D′}
  → p ⊢ U ◃* D′ → ∀ u → u ⋵ U → p ⊢ u ◃ D′
◃*-∈ p {u ∷ U} (r , rs) .u (here refl) = r
◃*-∈ p {u ∷ U} (r , rs) u′ (there u′∈) = ◃*-∈ p rs u′ u′∈

◃*-intro : ∀ {A A′} (p : A ⊑ A′) U {D′}
  → (∀ u → u ⋵ U → p ⊢ u ◃ D′) → p ⊢ U ◃* D′
◃*-intro p [] f = tt₁
◃*-intro p (u ∷ U) f =
  f u (here refl) , ◃*-intro p U (λ u′ u′∈ → f u′ (there u′∈))

▹*-∈ : ∀ {A A′} (p : A ⊑ A′) {E V′}
  → p ⊢ E ▹* V′ → ∀ v′ → v′ ⋵ V′ → p ⊢ E ▹ v′
▹*-∈ p {V′ = v′ ∷ V′} (r , rs) .v′ (here refl) = r
▹*-∈ p {V′ = v′ ∷ V′} (r , rs) u (there u∈) = ▹*-∈ p rs u u∈

▹*-intro : ∀ {A A′} (p : A ⊑ A′) {E} V′
  → (∀ v′ → v′ ⋵ V′ → p ⊢ E ▹ v′) → p ⊢ E ▹* V′
▹*-intro p [] f = tt₁
▹*-intro p (v′ ∷ V′) f =
  f v′ (here refl) , ▹*-intro p V′ (λ u u∈ → f u (there u∈))

-- every element of a finite list is justified against the values of D′,
-- or D′ errs
all◃ : ∀ {A A′} (p : A ⊑ A′) U {D′}
  → (∀ u → u ⋵ U → p ⊢ u ◃ D′)
  → Lift₁ (ω ∈ D′) ⊎ p ⊢ U ◃* ⌊ D′ ⌋
all◃ p [] f = inj₂ tt₁
all◃ p (u ∷ U) f with f u (here refl)
... | inj₁ e = inj₁ e
... | inj₂ r with all◃ p U (λ u′ u′∈ → f u′ (there u′∈))
...   | inj₁ e = inj₁ e
...   | inj₂ rs = inj₂ (inj₂ (◃ᵛ-vals p u r) , rs)

-- a nonempty list justified against a value set makes it converge
◃*-conv : ∀ {A A′} (p : A ⊑ A′) U {D′}
  → U ≢ [] → ValSet D′ → p ⊢ U ◃* D′ → Conv D′
◃*-conv p [] U≢ vD′ rs = ⊥-elim (U≢ refl)
◃*-conv p (u ∷ U) U≢ vD′ (r , rs) = ◃ᵛ-conv p u (◃-val p u vD′ r)
