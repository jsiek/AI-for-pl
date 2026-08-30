module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  A telescope is
--     intrinsically indexed by its type-variable-to-anchor map σ.  `just α` marks the
--     unique live crossing of α; `nothing` marks a lexical type variable.  Begins may
--     insert only an absent anchor, while ends remove exactly the selected
--     type variable, so lying marker annotations are unrepresentable.
--   * Representation lookup is the total function `rep?`.  Its two transports
--     are deliberately different: lexical type variables travel by their accumulated
--     position route, while crossing type variables travel by anchor identity to the
--     query telescope's unique live alias.  A dead crossing recursively reads
--     its older anchor's representation.  Undefined routes refuse with
--     `nothing`; begin/end bracket choices are never consulted.
--   * Defines the λB-aligned value family.  Regions are transient rather
--     than results, and universal introduction has no dynamic body premise.
--   * `_≼[_,_]_` remains only a marker-balance certificate.  Its injection
--     index records lexical drift and delimiter positions for typing transport;
--     it is not representation lookup evidence.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (Maybe; just; nothing)
  renaming (map to mapMaybe)
open import Data.Nat using
  (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
import Data.Nat as Nat
open import Data.Nat.Properties using (m≤n⇒m≤1+n)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (¬_; yes; no)
open import Data.Vec.Base

open import Types
open import Primitives
open import Consistency
open import alt.ThetaTerms
open import alt.Conversion

private
  variable
    Θ Θ′ : AnchorCtx
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- TyVar maps
------------------------------------------------------------------------

-- Apply a function to every entry of a type-variable map.
mapᵛ : ∀ {n} {A B : Set} → (A → B) → Vec A n → Vec B n
mapᵛ f [] = []
mapᵛ f (x ∷ xs) = f x ∷ mapᵛ f xs

-- Insert a new entry at position i of a type-variable map, shifting later entries up.
insertᵛ : ∀ {n} {A : Set}
  → Fin (suc n) → A → Vec A n → Vec A (suc n)
insertᵛ zero x xs = x ∷ xs
insertᵛ (suc i) x (y ∷ ys) = y ∷ insertᵛ i x ys

-- Remove the entry at position i of a type-variable map, shifting later entries down.
removeᵛ : ∀ {n} {A : Set}
  → Fin (suc n) → Vec A (suc n) → Vec A n
removeᵛ zero (x ∷ xs) = xs
removeᵛ {n = suc n} (suc i) (x ∷ xs) =
  x ∷ removeᵛ i xs

infix 4 _∉ᵛ_

-- `α ∉ᵛ σ`: no type variable of σ currently aliases anchor α.
_∉ᵛ_ : ∀ {Θ Δ}
  → TyVar Θ → Vec (Maybe (TyVar Θ)) Δ → Set
α ∉ᵛ σ = ∀ Y → lookup σ Y ≢ just α

-- Find the type variable that currently aliases anchor α, if any (unique by the
-- begin constructor's freshness field).
liveTyVar? : ∀ {Θ Δ}
  → Vec (Maybe (TyVar Θ)) Δ → TyVar Θ
  → Maybe (TyVar Δ)
liveTyVar? [] α = nothing
liveTyVar? (nothing ∷ σ) α = mapMaybe suc (liveTyVar? σ α)
liveTyVar? (just β ∷ σ) α with α ≟ β
liveTyVar? (just β ∷ σ) .β | yes refl = just zero
liveTyVar? (just β ∷ σ) α | no α≢β =
  mapMaybe suc (liveTyVar? σ α)

-- Peel the `just` constructor off an equality.
just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- The live lookup is a function, so its selected alias is unique.  The
-- telescope's begin field is what makes that selected alias also the only
-- `just α` entry representable in σ.
liveTyVar?-unique : ∀ {Θ Δ} {σ : Vec (Maybe (TyVar Θ)) Δ}
    {α : TyVar Θ} {X Y : TyVar Δ}
  → liveTyVar? σ α ≡ just X
  → liveTyVar? σ α ≡ just Y
  → X ≡ Y
liveTyVar?-unique X-eq Y-eq =
  just-injective (trans (sym X-eq) Y-eq)

------------------------------------------------------------------------
-- Binder telescopes: type variables and anchors, no term variables
------------------------------------------------------------------------

infixl 5 _,begin[_≔_]⟨_⟩ _,typ _,end[_]
infixl 5 _,:=_

data TyEnv : (Θ : AnchorCtx) (Δ : TyCtx)
    → Vec (Maybe (TyVar Θ)) Δ → Set where
  ∅ : TyEnv zero zero []

  _,begin[_≔_]⟨_⟩ : ∀ {σ}
    → TyEnv Θ Δ σ
    → (Y : TyVar (suc Δ))
    → (α : TyVar Θ)
    → α ∉ᵛ σ
    → TyEnv Θ (suc Δ) (insertᵛ Y (just α) σ)

  _,typ : ∀ {σ}
    → TyEnv Θ Δ σ
    → TyEnv Θ (suc Δ) (insertᵛ zero nothing σ)

  _,:=_ : ∀ {σ}
    → TyEnv Θ Δ σ
    → Ty Δ
    → TyEnv (suc Θ) Δ (mapᵛ (mapMaybe suc) σ)

  _,end[_] : ∀ {σ}
    → TyEnv Θ (suc Δ) σ
    → (Y : TyVar (suc Δ))
    → TyEnv Θ Δ (removeᵛ Y σ)

------------------------------------------------------------------------
-- Telescope-aligned term contexts
------------------------------------------------------------------------

-- Insert one unused target position into an order-preserving injection.
-- The relation, rather than a function call in an index, keeps every route
-- constructor in constructor form.
data InsertTarget : ∀ {m n}
    → Fin (suc n) → m ↪ᵗ n → m ↪ᵗ suc n → Set where
  target-insert-empty : ∀ {n} (Y : Fin (suc n))
    → InsertTarget Y empty empty

  target-insert-zero : ∀ {m n} {ρ : m ↪ᵗ n}
    → InsertTarget zero ρ (skip ρ)

  target-insert-skip : ∀ {m n} {Y : Fin (suc n)} {ρ : m ↪ᵗ n}
      {ρ′ : m ↪ᵗ suc n}
    → InsertTarget Y ρ ρ′
    → InsertTarget (suc Y) (skip ρ) (skip ρ′)

  target-insert-keep : ∀ {m n} {Y : Fin (suc n)} {ρ : m ↪ᵗ n}
      {ρ′ : m ↪ᵗ suc n}
    → InsertTarget Y ρ ρ′
    → InsertTarget (suc Y) (keep ρ) (keep ρ′)

-- Delete a target position only when the injection skips it.  Consequently
-- a route can cross an end exactly when its binding predates the matching
-- begin; no type-occurrence test is involved.
data DeleteTarget : ∀ {m n}
    → Fin (suc n) → m ↪ᵗ suc n → m ↪ᵗ n → Set where
  target-delete-empty : ∀ {n} (Y : Fin (suc n))
    → DeleteTarget Y empty empty

  target-delete-zero : ∀ {m n} {ρ : m ↪ᵗ n}
    → DeleteTarget zero (skip ρ) ρ

  target-delete-skip : ∀ {m n} {Y : Fin (suc n)}
      {ρ : m ↪ᵗ suc n} {ρ′ : m ↪ᵗ n}
    → DeleteTarget Y ρ ρ′
    → DeleteTarget (suc Y) (skip ρ) (skip ρ′)

  target-delete-keep : ∀ {m n} {Y : Fin (suc n)}
      {ρ : m ↪ᵗ suc n} {ρ′ : m ↪ᵗ n}
    → DeleteTarget Y ρ ρ′
    → DeleteTarget (suc Y) (keep ρ) (keep ρ′)

------------------------------------------------------------------------
-- Lexical drift and balanced extension
------------------------------------------------------------------------

-- Widen an injection with one new type variable at position Y on both sides,
-- mapping the new type variable to the new type variable.
insert↪ᵗ : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′ → TyVar (suc Δ) → suc Δ ↪ᵗ suc Δ′
insert↪ᵗ ρ zero = keep ρ
insert↪ᵗ (keep ρ) (suc Y) = keep (insert↪ᵗ ρ Y)
insert↪ᵗ (skip ρ) (suc Y) = skip (insert↪ᵗ ρ (suc Y))

-- Narrow an injection by deleting source type variable Y together with its image.
delete↪ᵗ : ∀ {Δ Δ′}
  → suc Δ ↪ᵗ suc Δ′ → TyVar (suc Δ) → Δ ↪ᵗ Δ′
delete↪ᵗ (keep ρ) zero = ρ
delete↪ᵗ {Δ = suc Δ} {Δ′ = zero} (keep ()) (suc Y)
delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′} (keep ρ) (suc Y) =
  keep (delete↪ᵗ ρ Y)
delete↪ᵗ {Δ′ = zero} (skip ()) Y
delete↪ᵗ {Δ′ = suc Δ′} (skip ρ) Y = skip (delete↪ᵗ ρ Y)

infixl 7 _⨟↪ᵗ_

-- Compose two injections, diagrammatic order.
_⨟↪ᵗ_ : ∀ {Δ₁ Δ₂ Δ₃}
  → Δ₁ ↪ᵗ Δ₂ → Δ₂ ↪ᵗ Δ₃ → Δ₁ ↪ᵗ Δ₃
empty ⨟↪ᵗ empty = empty
ρ ⨟↪ᵗ skip η = skip (ρ ⨟↪ᵗ η)
empty ⨟↪ᵗ keep η = empty
keep ρ ⨟↪ᵗ keep η = keep (ρ ⨟↪ᵗ η)
skip ρ ⨟↪ᵗ keep η = skip (ρ ⨟↪ᵗ η)

injection-size : ∀ {Δ Δ′} → Δ ↪ᵗ Δ′ → Δ ≤ Δ′
injection-size empty = z≤n
injection-size (keep ρ) = s≤s (injection-size ρ)
injection-size (skip ρ) = m≤n⇒m≤1+n (injection-size ρ)

no-successor≤ : ∀ {Δ} → suc Δ ≤ Δ → ⊥
no-successor≤ {zero} ()
no-successor≤ {suc Δ} (s≤s sucΔ≤Δ) = no-successor≤ sucΔ≤Δ

no-injection-down : ∀ {Δ} → suc Δ ↪ᵗ Δ → ⊥
no-injection-down ρ = no-successor≤ (injection-size ρ)

same-injection-pointwise : ∀ {Δ} (ρ : Δ ↪ᵗ Δ) X
  → toRenameᵗ ρ X ≡ X
same-injection-pointwise {zero} empty ()
same-injection-pointwise {suc Δ} (keep ρ) zero = refl
same-injection-pointwise {suc Δ} (keep ρ) (suc X) =
  cong suc (same-injection-pointwise ρ X)
same-injection-pointwise {suc Δ} (skip ρ) X =
  ⊥-elim (no-injection-down ρ)

infix 4 _≼[_,_]_

-- `Shifted k α β`: anchor β is α's image after k newer anchors were born.
data Shifted : ∀ {Θ Θ′} → ℕ → TyVar Θ → TyVar Θ′ → Set where
  shifted-zero : ∀ {Θ} {α : TyVar Θ} → Shifted zero α α
  shifted-suc : ∀ {Θ Θ′ k} {α : TyVar Θ} {β : TyVar Θ′}
    → Shifted k α β → Shifted (suc k) α (suc β)

data _≼[_,_]_ : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    → TyEnv Θ Δ σ → ℕ → Δ ↪ᵗ Δ′ → TyEnv Θ′ Δ′ σ′ → Set where
  ≼-refl : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      ------------------------
    → Ψ ≼[ zero , id↪ᵗ ] Ψ

  ≼-ν : ∀ {Θ Θ′ Δ Δ′ k σ σ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ σ} {Ψ′ : TyEnv Θ′ Δ′ σ′} {B : Ty Δ′}
    → Ψ ≼[ k , ρ ] Ψ′
      --------------------------
    → Ψ ≼[ suc k , ρ ] (Ψ′ ,:= B)

  ≼-typ : ∀ {Θ Θ′ Δ Δ′ k σ σ′} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ σ} {Ψ′ : TyEnv Θ′ Δ′ σ′}
    → Ψ ≼[ k , ρ ] Ψ′
      ----------------------------
    → Ψ ≼[ k , skip ρ ] (Ψ′ ,typ)

  ≼-begin-end : ∀ {Θ Θ′ Θ″ Δ Δ′ Δ″ k k′ σ σ′ σ″}
      {ρ : Δ ↪ᵗ Δ′} {η : suc Δ′ ↪ᵗ suc Δ″}
      {Ψ : TyEnv Θ Δ σ} {Ψ′ : TyEnv Θ′ Δ′ σ′}
      {Ψ″ : TyEnv Θ″ (suc Δ″) σ″}
      {Z : TyVar (suc Δ′)} {β : TyVar Θ′} {fresh : β ∉ᵛ σ′}
    → Ψ ≼[ k , ρ ] Ψ′
    → (Ψ′ ,begin[ Z ≔ β ]⟨ fresh ⟩) ≼[ k′ , η ] Ψ″
      ------------------------------------------------------------
    → Ψ ≼[ k + k′ , ρ ⨟↪ᵗ delete↪ᵗ η Z ]
        (Ψ″ ,end[ toRenameᵗ η Z ])

  ≼-end-begin : ∀ {Θ Θ′ Θ″ Δ Δ′ Δ″ k k′ σ σ′ σ″}
      {ρ : suc Δ ↪ᵗ suc Δ′} {η : Δ′ ↪ᵗ Δ″}
      {Ψ : TyEnv Θ (suc Δ) σ} {Ψ′ : TyEnv Θ′ (suc Δ′) σ′}
      {Ψ″ : TyEnv Θ″ Δ″ σ″} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {β : TyVar Θ″} {fresh : β ∉ᵛ σ″}
    → lookup σ X ≡ just α
    → Ψ ≼[ k , ρ ] Ψ′
    → (Ψ′ ,end[ toRenameᵗ ρ X ]) ≼[ k′ , η ] Ψ″
    → Shifted (k + k′) α β
    → Ψ ≼[ k + k′ , insert↪ᵗ (delete↪ᵗ ρ X ⨟↪ᵗ η) X ]
        (Ψ″ ,begin[
          toRenameᵗ (insert↪ᵗ (delete↪ᵗ ρ X ⨟↪ᵗ η) X) X ≔ β
        ]⟨ fresh ⟩)

-- Read a balanced extension's anchor shift off its witness: where an anchor
-- of the small telescope sits in the large one.
shiftAlong : ∀ {Θ Θ′ Δ Δ′ k σ σ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Ψ′ : TyEnv Θ′ Δ′ σ′}
  → Ψ ≼[ k , ρ ] Ψ′ → TyVar Θ → TyVar Θ′
shiftAlong ≼-refl α = α
shiftAlong (≼-ν extension) α = suc (shiftAlong extension α)
shiftAlong (≼-typ extension) α = shiftAlong extension α
shiftAlong (≼-begin-end extension region) α =
  shiftAlong region (shiftAlong extension α)
shiftAlong (≼-end-begin tyVar-eq extension region shifted) α =
  shiftAlong region (shiftAlong extension α)

-- A typing target closes a balanced extension under telescope stages already
-- present on both sides.  It lives with the telescope geometry because term
-- bindings use it to transport their positional routes without inspecting
-- their birth types.
data TypingTarget : ∀ {Θ Θ′ Δ Δ′ σ σ′}
    (ρ : Δ ↪ᵗ Δ′) (φ : TyVar Θ → TyVar Θ′)
    → TyEnv Θ Δ σ → TyEnv Θ′ Δ′ σ′ → Set where
  balanced-target : ∀ {Θ Θ′ Δ Δ′ σ σ′ k} {ρ : Δ ↪ᵗ Δ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      (extension : Ψ ≼[ k , ρ ] Φ)
    → TypingTarget ρ (shiftAlong extension) Ψ Φ

  typing-target-begin : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
      {Y : TyVar (suc Δ)} {a : TyVar Θ}
      {fresh : a ∉ᵛ σ} {fresh′ : φ a ∉ᵛ σ′}
    → TypingTarget ρ φ Ψ Φ
    → TypingTarget (insert↪ᵗ ρ Y) φ
        (Ψ ,begin[ Y ≔ a ]⟨ fresh ⟩)
        (Φ ,begin[
          toRenameᵗ (insert↪ᵗ ρ Y) Y ≔ φ a
        ]⟨ fresh′ ⟩)

  typing-target-typ : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′}
    → TypingTarget ρ φ Ψ Φ
    → TypingTarget (keep ρ) φ (Ψ ,typ) (Φ ,typ)

  typing-target-ν : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : Δ ↪ᵗ Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ Δ σ} {Φ : TyEnv Θ′ Δ′ σ′} {A : Ty Δ}
    → TypingTarget ρ φ Ψ Φ
    → TypingTarget ρ (extᵗ φ) (Ψ ,:= A)
        (Φ ,:= renameᵗ (toRenameᵗ ρ) A)

  typing-target-end : ∀ {Θ Θ′ Δ Δ′ σ σ′}
      {ρ : suc Δ ↪ᵗ suc Δ′} {φ : TyVar Θ → TyVar Θ′}
      {Ψ : TyEnv Θ (suc Δ) σ} {Φ : TyEnv Θ′ (suc Δ′) σ′}
      {Y : TyVar (suc Δ)}
    → TypingTarget ρ φ Ψ Φ
    → TypingTarget (delete↪ᵗ ρ Y) φ (Ψ ,end[ Y ])
        (Φ ,end[ toRenameᵗ ρ Y ])

------------------------------------------------------------------------
-- Structural term-context paths
------------------------------------------------------------------------

-- A scope route names the exact telescope constructors between a binding's
-- birth telescope and its use telescope.  There is no numeric birth marker:
-- regular weakening is read directly from the route's injection index.
data ScopeRoute : ∀ {Θ₀ Θ Δ₀ Δ σ₀ σ}
    → TyEnv Θ₀ Δ₀ σ₀ → TyEnv Θ Δ σ → Δ₀ ↪ᵗ Δ → Set where
  scope-here : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    → ScopeRoute Ψ Ψ id↪ᵗ

  scope-ν : ∀ {Θ₀ Θ Δ₀ Δ σ₀ σ} {A : Ty Δ}
      {birth : TyEnv Θ₀ Δ₀ σ₀} {Ψ : TyEnv Θ Δ σ}
      {ρ : Δ₀ ↪ᵗ Δ}
    → ScopeRoute birth Ψ ρ
    → ScopeRoute birth (Ψ ,:= A) ρ

  scope-typ : ∀ {Θ₀ Θ Δ₀ Δ σ₀ σ}
      {birth : TyEnv Θ₀ Δ₀ σ₀} {Ψ : TyEnv Θ Δ σ}
      {ρ : Δ₀ ↪ᵗ Δ}
    → ScopeRoute birth Ψ ρ
    → ScopeRoute birth (Ψ ,typ) (skip ρ)

  scope-begin : ∀ {Θ₀ Θ Δ₀ Δ σ₀ σ}
      {birth : TyEnv Θ₀ Δ₀ σ₀} {Ψ : TyEnv Θ Δ σ}
      {ρ : Δ₀ ↪ᵗ Δ} {ρ′ : Δ₀ ↪ᵗ suc Δ}
      {Y : TyVar (suc Δ)} {α : TyVar Θ} {fresh : α ∉ᵛ σ}
    → ScopeRoute birth Ψ ρ
    → InsertTarget Y ρ ρ′
    → ScopeRoute birth (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) ρ′

  scope-end : ∀ {Θ₀ Θ Δ₀ Δ σ₀ σ}
      {birth : TyEnv Θ₀ Δ₀ σ₀} {Ψ : TyEnv Θ (suc Δ) σ}
      {ρ : Δ₀ ↪ᵗ suc Δ} {ρ′ : Δ₀ ↪ᵗ Δ}
      {Y : TyVar (suc Δ)}
    → ScopeRoute birth Ψ ρ
    → DeleteTarget Y ρ ρ′
    → ScopeRoute birth (Ψ ,end[ Y ]) ρ′

  scope-target : ∀ {Θ₀ Θ Θ′ Δ₀ Δ Δ′ σ₀ σ σ′}
      {birth : TyEnv Θ₀ Δ₀ σ₀} {Ψ : TyEnv Θ Δ σ}
      {Φ : TyEnv Θ′ Δ′ σ′} {η : Δ₀ ↪ᵗ Δ} {ρ : Δ ↪ᵗ Δ′}
      {φ : TyVar Θ → TyVar Θ′}
    → ScopeRoute birth Ψ η
    → TypingTarget ρ φ Ψ Φ
    → ScopeRoute birth Φ (η ⨟↪ᵗ ρ)

currentScope : ∀ {Θ Δ σ} (Ψ : TyEnv Θ Δ σ)
  → ScopeRoute Ψ Ψ id↪ᵗ
currentScope Ψ = scope-here

weakenAlong : ∀ {Θ₀ Θ Δ₀ Δ σ₀ σ}
    {birth : TyEnv Θ₀ Δ₀ σ₀} {Ψ : TyEnv Θ Δ σ}
    {ρ : Δ₀ ↪ᵗ Δ}
  → ScopeRoute birth Ψ ρ → Ty Δ₀ → Ty Δ
weakenAlong {ρ = ρ} ws A = renameᵗ (toRenameᵗ ρ) A

id↪-pointwise : ∀ {Δ} (X : TyVar Δ) → toRenameᵗ id↪ᵗ X ≡ X
id↪-pointwise zero = refl
id↪-pointwise (suc X) = cong suc (id↪-pointwise X)

data InsertView : ∀ {m n} → Fin (suc n) → m ↪ᵗ n → Set where
  insert-view : ∀ {m n} {Y : Fin (suc n)} {ρ : m ↪ᵗ n}
      {ρ′ : m ↪ᵗ suc n}
    → InsertTarget Y ρ ρ′
    → InsertView Y ρ

insertView : ∀ {m n} (Y : Fin (suc n)) (ρ : m ↪ᵗ n)
  → InsertView Y ρ
insertView Y empty = insert-view (target-insert-empty Y)
insertView zero (keep ρ) = insert-view target-insert-zero
insertView zero (skip ρ) = insert-view target-insert-zero
insertView (suc Y) (keep ρ) with insertView Y ρ
insertView (suc Y) (keep ρ) | insert-view insertion =
  insert-view (target-insert-keep insertion)
insertView (suc Y) (skip ρ) with insertView Y ρ
insertView (suc Y) (skip ρ) | insert-view insertion =
  insert-view (target-insert-skip insertion)

data DeleteView : ∀ {m n} → Fin (suc n) → m ↪ᵗ suc n → Set where
  delete-occupied : ∀ {m n} {Y : Fin (suc n)} {ρ : m ↪ᵗ suc n}
    → DeleteView Y ρ
  delete-open : ∀ {m n} {Y : Fin (suc n)} {ρ : m ↪ᵗ suc n}
      {ρ′ : m ↪ᵗ n}
    → DeleteTarget Y ρ ρ′
    → DeleteView Y ρ

deleteView : ∀ {m n} (Y : Fin (suc n)) (ρ : m ↪ᵗ suc n)
  → DeleteView Y ρ
deleteView Y empty = delete-open (target-delete-empty Y)
deleteView {n = zero} zero (keep ρ) = delete-occupied
deleteView {n = zero} zero (skip ρ) = delete-open target-delete-zero
deleteView {n = suc n} zero (keep ρ) = delete-occupied
deleteView {n = suc n} zero (skip ρ) = delete-open target-delete-zero
deleteView {n = suc n} (suc Y) (keep ρ) with deleteView Y ρ
deleteView {n = suc n} (suc Y) (keep ρ) | delete-occupied =
  delete-occupied
deleteView {n = suc n} (suc Y) (keep ρ) | delete-open deletion =
  delete-open (target-delete-keep deletion)
deleteView {n = suc n} (suc Y) (skip ρ) with deleteView Y ρ
deleteView {n = suc n} (suc Y) (skip ρ) | delete-occupied =
  delete-occupied
deleteView {n = suc n} (suc Y) (skip ρ) | delete-open deletion =
  delete-open (target-delete-skip deletion)

data Binding {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) : Set where
  _at_ : ∀ {Θ₀ Δ₀ σ₀} {birth : TyEnv Θ₀ Δ₀ σ₀}
      {ρ : Δ₀ ↪ᵗ Δ}
    → Ty Δ₀ → ScopeRoute birth Ψ ρ → Binding Ψ

data TermCtx {Θ Δ σ} (Ψ : TyEnv Θ Δ σ) : Set where
  [] : TermCtx Ψ
  _∷_ : Binding Ψ → TermCtx Ψ → TermCtx Ψ

beginBinding : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {Y : TyVar (suc Δ)} {α : TyVar Θ} {fresh : α ∉ᵛ σ}
  → Binding Ψ → Binding (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩)
beginBinding {Y = Y} (_at_ {ρ = ρ} A ws) with insertView Y ρ
beginBinding {Y = Y} (A at ws) | insert-view insertion =
  A at scope-begin ws insertion

beginCtx : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    {Y : TyVar (suc Δ)} {α : TyVar Θ} {fresh : α ∉ᵛ σ}
  → TermCtx Ψ → TermCtx (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩)
beginCtx [] = []
beginCtx (binding ∷ Γ) = beginBinding binding ∷ beginCtx Γ

typBinding : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
  → Binding Ψ → Binding (Ψ ,typ)
typBinding (A at ws) = A at scope-typ ws

typCtx : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
  → TermCtx Ψ → TermCtx (Ψ ,typ)
typCtx [] = []
typCtx (binding ∷ Γ) = typBinding binding ∷ typCtx Γ

νBinding : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ}
  → Binding Ψ → Binding (Ψ ,:= A)
νBinding (B at ws) = B at scope-ν ws

νCtx : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ}
  → TermCtx Ψ → TermCtx (Ψ ,:= A)
νCtx [] = []
νCtx (binding ∷ Γ) = νBinding binding ∷ νCtx Γ

endBinding? : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
    (Y : TyVar (suc Δ))
  → Binding Ψ → Maybe (Binding (Ψ ,end[ Y ]))
endBinding? Y (_at_ {ρ = ρ} A ws) with deleteView Y ρ
endBinding? Y (A at ws) | delete-occupied = nothing
endBinding? Y (A at ws) | delete-open deletion =
  just (A at scope-end ws deletion)

truncateForEnd : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
  → TermCtx Ψ → (Y : TyVar (suc Δ)) → TermCtx (Ψ ,end[ Y ])
truncateForEnd [] Y = []
truncateForEnd (binding ∷ Γ) Y with endBinding? Y binding
truncateForEnd (binding ∷ Γ) Y | nothing = truncateForEnd Γ Y
truncateForEnd (binding ∷ Γ) Y | just ended =
  ended ∷ truncateForEnd Γ Y

truncateForEnd-empty : ∀ {Θ Δ σ}
    {Ψ : TyEnv Θ (suc Δ) σ} (Y : TyVar (suc Δ))
  → truncateForEnd {Ψ = Ψ} [] Y ≡ []
truncateForEnd-empty Y = refl

infix 4 _∋_⦂[_]_

data _∋_⦂[_]_ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
    : (Γ : TermCtx Ψ) (x : ℕ) → ∀ {Θ₀ Δ₀ σ₀}
      {birth : TyEnv Θ₀ Δ₀ σ₀} {ρ : Δ₀ ↪ᵗ Δ}
    → ScopeRoute birth Ψ ρ → Ty Δ₀ → Set where
  Z : ∀ {Θ₀ Δ₀ σ₀} {birth : TyEnv Θ₀ Δ₀ σ₀}
      {ρ : Δ₀ ↪ᵗ Δ} {ws : ScopeRoute birth Ψ ρ}
      {A : Ty Δ₀} {Γ : TermCtx Ψ}
    → ((A at ws) ∷ Γ) ∋ zero ⦂[ ws ] A

  S : ∀ {Θ₀ Δ₀ σ₀ Θ₁ Δ₁ σ₁ x}
      {birth : TyEnv Θ₀ Δ₀ σ₀} {headBirth : TyEnv Θ₁ Δ₁ σ₁}
      {ρ : Δ₀ ↪ᵗ Δ} {η : Δ₁ ↪ᵗ Δ}
      {ws : ScopeRoute birth Ψ ρ} {head : ScopeRoute headBirth Ψ η}
      {A : Ty Δ₀} {B : Ty Δ₁} {Γ : TermCtx Ψ}
    → Γ ∋ x ⦂[ ws ] A
    → ((B at head) ∷ Γ) ∋ suc x ⦂[ ws ] A

------------------------------------------------------------------------
-- Anchor-directed executable representation lookup
------------------------------------------------------------------------

-- Adjust a type-variable route across an end marker: the ended type variable has no image,
-- every other type variable punches past it.
route-end : ∀ {Δ Δ′}
  → TyVar (suc Δ) → (TyVar Δ → Maybe (TyVar Δ′))
  → TyVar (suc Δ) → Maybe (TyVar Δ′)
route-end Y route X with Y ≟ X
route-end Y route .Y | yes refl = nothing
route-end Y route X | no Y≢X = route (punchOut Y X Y≢X)

-- Extend a type-variable route under one binder: the new type variable maps to the new type variable.
ext-route : ∀ {Δ Δ′}
  → (TyVar Δ → Maybe (TyVar Δ′))
  → TyVar (suc Δ) → Maybe (TyVar (suc Δ′))
ext-route route zero = just zero
ext-route route (suc X) = mapMaybe suc (route X)

-- The meaning of an anchor at the query: its live alias as a variable, or
-- its resolved representation if it is dead.
aliasResult? : ∀ {Θ Δ Δout}
  → (TyVar Θ → Maybe (Ty Δ))
  → Vec (Maybe (TyVar Θ)) Δ
  → (TyVar Δ → TyVar Δout)
  → TyVar Θ
  → Maybe (Ty Δout)
aliasResult? resolve target live-ren anchor
    with liveTyVar? target anchor
aliasResult? resolve target live-ren anchor | just Y =
  just (＇ live-ren Y)
aliasResult? resolve target live-ren anchor | nothing
    with resolve anchor
aliasResult? resolve target live-ren anchor | nothing | nothing = nothing
aliasResult? resolve target live-ren anchor | nothing | just A =
  just (renameᵗ live-ren A)

-- Transport a birth-scope type to the query scope: crossing type variables travel by
-- anchor (aliasResult?), lexical type variables by the positional route.
repoint? : ∀ {Θ₀ Θ Δ₀ Δ Δout}
  → (TyVar Θ → Maybe (Ty Δ))
  → Vec (Maybe (TyVar Θ)) Δ
  → Vec (Maybe (TyVar Θ₀)) Δ₀
  → (TyVar (suc Θ₀) → TyVar Θ)
  → (TyVar Δ₀ → Maybe (TyVar Δout))
  → (TyVar Δ → TyVar Δout)
  → Ty Δ₀
  → Maybe (Ty Δout)
repoint? resolve target σ₀ φ route live-ren (＇ X)
    with lookup σ₀ X
repoint? resolve target σ₀ φ route live-ren (＇ X) | nothing
    with route X
repoint? resolve target σ₀ φ route live-ren (＇ X)
    | nothing | nothing = nothing
repoint? resolve target σ₀ φ route live-ren (＇ X)
    | nothing | just Y = just (＇ Y)
repoint? resolve target σ₀ φ route live-ren (＇ X) | just β
  = aliasResult? resolve target live-ren (φ (suc β))
repoint? resolve target σ₀ φ route live-ren (‵ ι) = just (‵ ι)
repoint? resolve target σ₀ φ route live-ren ★ = just ★
repoint? resolve target σ₀ φ route live-ren (A ⇒ B)
    with repoint? resolve target σ₀ φ route live-ren A
repoint? resolve target σ₀ φ route live-ren (A ⇒ B) | nothing = nothing
repoint? resolve target σ₀ φ route live-ren (A ⇒ B) | just A′
    with repoint? resolve target σ₀ φ route live-ren B
repoint? resolve target σ₀ φ route live-ren (A ⇒ B)
    | just A′ | nothing = nothing
repoint? resolve target σ₀ φ route live-ren (A ⇒ B)
    | just A′ | just B′ = just (A′ ⇒ B′)
repoint? resolve target σ₀ φ route live-ren (`∀ A)
    with repoint? resolve target (nothing ∷ σ₀) φ
      (ext-route route) (λ X → suc (live-ren X)) A
repoint? resolve target σ₀ φ route live-ren (`∀ A) | nothing = nothing
repoint? resolve target σ₀ φ route live-ren (`∀ A) | just A′ =
  just (`∀ A′)

-- Instantiate repoint? at a ν entry: transport its representation from its
-- birth scope to the query scope.
repointAtν? : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
  → (TyVar Θ → Maybe (Ty Δ))
  → TyEnv Θ Δ σ
  → TyEnv Θ₀ Δ₀ σ₀
  → (TyVar (suc Θ₀) → TyVar Θ)
  → (TyVar Δ₀ → Maybe (TyVar Δ))
  → Ty Δ₀
  → Maybe (Ty Δ)
repointAtν? {σ = σ} {σ₀ = σ₀} resolve target prefix φ route A =
  repoint? resolve σ σ₀ φ route (λ X → X) A

-- Peel the telescope from the query down to the queried ν, accumulating the
-- anchor shift φ and the type-variable route, then repoint its representation.
scanRep? : ∀ {Θ Δ σ Θ₀ Δ₀ σ₀}
  → (TyVar Θ → Maybe (Ty Δ))
  → (target : TyEnv Θ Δ σ)
  → (current : TyEnv Θ₀ Δ₀ σ₀)
  → (TyVar Θ₀ → TyVar Θ)
  → (TyVar Δ₀ → Maybe (TyVar Δ))
  → TyVar Θ₀
  → Maybe (Ty Δ)
scanRep? resolve target ∅ φ route ()
scanRep? resolve target (Ψ ,begin[ Y ≔ β ]⟨ fresh ⟩)
    φ route α =
  scanRep? resolve target Ψ φ (λ X → route (punchIn Y X)) α
scanRep? resolve target (Ψ ,typ) φ route α =
  scanRep? resolve target Ψ φ (λ X → route (suc X)) α
scanRep? resolve target (Ψ ,:= A) φ route zero =
  repointAtν? resolve target Ψ φ route A
scanRep? resolve target (Ψ ,:= A) φ route (suc α) =
  scanRep? resolve target Ψ (λ β → φ (suc β)) route α
scanRep? resolve target (Ψ ,end[ Y ]) φ route α =
  scanRep? resolve target Ψ φ (route-end Y route) α

-- Fuel-indexed lookup body: resolving a dead crossing recurses on a strictly
-- older ν and consumes one unit of fuel.
repFuel? : ∀ (fuel : ℕ) {Θ Δ σ}
  → TyEnv Θ Δ σ → TyVar Θ → Maybe (Ty Δ)
repFuel? zero Ψ α = nothing
repFuel? (suc fuel) Ψ α =
  scanRep? (repFuel? fuel Ψ) Ψ Ψ (λ β → β) (λ X → just X) α

-- Look up the representation type of anchor α's ν binding, expressed in the
-- query scope.  Fuel is the queried ν's birth depth: `Θ ∸ toℕ α`.  Resolving a
-- dead crossing asks only for an older ν, and is the sole recursive call;
-- it therefore consumes one unit.  This tighter measure is invariant under
-- inserting a fresh newest ν (`suc Θ ∸ toℕ (suc α)` computes to the
-- same depth), which makes anchor transport expose the intended equation.
rep? : ∀ {Θ Δ σ} → TyEnv Θ Δ σ → TyVar Θ → Maybe (Ty Δ)
rep? {Θ = Θ} Ψ α = repFuel? (Θ ∸ toℕ α) Ψ α

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GenSafe : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  safe-⇒ : ∀ {Δ μ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
      ---------------------------------------------
    → GenSafe (c ↦ d)

  safe-∀ : ∀ {Δ μ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
      ----------------------
    → GenSafe (∀ᶜ c)

  safe-inst : ∀ {Δ μ} {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    → (B≢★ : B ≢ ★)
      ---------------------------
    → GenSafe ((inst c) B≢★)

  safe-gen : ∀ {Δ μ} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
      --------------------------
    → GenSafe ((gen c) A≢★)

data Inert : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  fun : ∀ {Δ} {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : flipᵐ μ ⊢ A′ ∼ A} {d : μ ⊢ B ∼ B′}
      ---------------------------------------------
    → Inert (c ↦ d)

  all : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
      ----------------------
    → Inert (∀ᶜ c)

  genᵥ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
      ------------------------
    → Inert ((gen c) A≢★)

-- Heads not covered by the ν-dissolution family.  Paired with `Value`, this
-- is the syntactic guard on a region adapter at a crossing.
data ImmobileHead : ∀ {Θ : AnchorCtx} {Δ : TyCtx}
    → Term Θ Δ → Set where
  seal-head : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → ImmobileHead (V ↓[ X ≔ α ] seal)

  reveal-fun-head : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c d}
    → ImmobileHead (V ↑[ X ≔ α ] (c ↦↑ d))

  conceal-fun-head : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c d}
    → ImmobileHead (V ↓[ X ≔ α ] (c ↦↓ d))

  adapter-head : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → ImmobileHead ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  adapter-region-head : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal}
    → ImmobileHead ((ν[ A ] M) ↑[ X ≔ α ] c)

NonLambda : ∀ {Θ Δ} → Term Θ Δ → Set
NonLambda V = ∀ {A N} → V ≢ (ƛ A ˙ N)

data Value : ∀ {Θ : AnchorCtx} {Δ : TyCtx} → Term Θ Δ → Set where
  ƛ_˙_ : ∀ {Θ Δ} (A : Ty Δ) (N : Term Θ Δ)
    → Value (ƛ A ˙ N)

  Λ_ : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
    → Value V
    → Value (Λ V)

  $ : ∀ {Θ Δ} (κ : Const)
    → Value {Θ = Θ} {Δ = Δ} ($ κ)

  inject : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ Gᵍ : Ground G ⦄ ⦃ G∼★ : μ ⊢ G ∼★ ⦄
      ⦃ Gns : NonStar G ⦄
    → Value V
    → Value (V ⟨ (idᵍ {μ = μ} Gᵍ) ! ⟩)

  _《_》 : ∀ {Θ Δ} {V : Term Θ Δ} {μ : Env∼ Δ} {A B : Ty Δ}
      {c : μ ⊢ A ∼ B}
    → Value V
    → Inert c
    → Value (V ⟨ c ⟩)

  seal-value : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ}
    → Value V
    → Value (V ↓[ X ≔ α ] seal)

  reveal-fun : ∀ {Θ Δ} {V : Term Θ (suc Δ)}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c d}
    → Value V
    → NonLambda V
    → Value (V ↑[ X ≔ α ] (c ↦↑ d))

  conceal-fun : ∀ {Θ Δ} {V : Term Θ Δ}
      {X : TyVar (suc Δ)} {α : TyVar Θ} {c d}
    → Value V
    → Value (V ↓[ X ≔ α ] (c ↦↓ d))

  adapter : ∀ {Θ Δ} {V : Term Θ Δ}
      {Y X : TyVar (suc Δ)} {β α : TyVar Θ}
    → Value V
    → ImmobileHead V
    → ¬ (X ≡ Y × α ≡ β)
    → Value ((V ↓[ Y ≔ β ] id↓) ↑[ X ≔ α ] id↑)

  adapter-region : ∀ {Θ Δ} {M : Term (suc Θ) (suc Δ)}
      {A : Ty (suc Δ)} {X : TyVar (suc Δ)} {α : TyVar Θ}
      {c : Reveal}
    → Value M
    → ImmobileHead M
    → X ∈ᵗ A
    → Value ((ν[ A ] M) ↑[ X ≔ α ] c)

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    σ : Vec (Maybe (TyVar Θ)) Δ
    Ψ Ψ′ : TyEnv Θ Δ σ
    Γ Γ′ : TermCtx Ψ
    A B C : Ty Δ
    F M N : Term Θ Δ
    x y z : Var

infix 4 _∣_⊢_⦂_

data _∣_⊢_⦂_ : ∀ {Θ Δ σ}
  → (Ψ : TyEnv Θ Δ σ) → TermCtx Ψ → Term Θ Δ → Ty Δ → Set where
  ⊢` : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ : TermCtx Ψ}
      {x : Var} {Θ₀ Δ₀ σ₀} {birth : TyEnv Θ₀ Δ₀ σ₀}
      {ρ : Δ₀ ↪ᵗ Δ} {ws : ScopeRoute birth Ψ ρ}
      {A₀ : Ty Δ₀}
    → Γ ∋ x ⦂[ ws ] A₀
      ---------------------------------------
    → Ψ ∣ Γ ⊢ (` x) ⦂ weakenAlong ws A₀

  ⊢ƛ :
      Ψ ∣ (A at currentScope Ψ) ∷ Γ ⊢ M ⦂ B
      ----------------------------------------------
    → Ψ ∣ Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· :
      Ψ ∣ Γ ⊢ F ⦂ (A ⇒ B)
    → Ψ ∣ Γ ⊢ M ⦂ A
      ---------------------
    → Ψ ∣ Γ ⊢ (F · M) ⦂ B

  ⊢Λ :
      Ψ ,typ ∣ typCtx Γ ⊢ M ⦂ A
      -------------------------
    → Ψ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢⦂∀ :
      Ψ ∣ Γ ⊢ F ⦂ `∀ C
      ----------------------------------
    → Ψ ∣ Γ ⊢ F ⦂∀ C [ A ] ⦂ C [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
      ---------------------------
    → Ψ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ :
      (op : Prim)
    → Ψ ∣ Γ ⊢ F ⦂ primArgTy op
    → Ψ ∣ Γ ⊢ M ⦂ primArgTy op
      -------------------------------------------
    → Ψ ∣ Γ ⊢ (F ⊕[ op ] M) ⦂ primResultTy op

  ⊢⟨⟩ : ∀ {μ}
    → Ψ ∣ Γ ⊢ M ⦂ A
    → (c : μ ⊢ A ∼ B)
      ---------------------
    → Ψ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢ν :
      Ψ ,:= A ∣ νCtx Γ ⊢ M ⦂ B
      ----------------------
    → Ψ ∣ Γ ⊢ ν[ A ] M ⦂ B

  ⊢reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ : TermCtx Ψ}
      {M : Term Θ (suc Δ)}
      {A : Ty (suc Δ)} {B C : Ty Δ} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal} {fresh : α ∉ᵛ σ}
    → rep? Ψ α ≡ just C
    → ⊢↑[ Y ⦂ wkᵗ Y C ] c ⦂ A ↝ wkᵗ Y B
    → Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩ ∣ beginCtx Γ ⊢ M ⦂ A
      --------------------------------
    → Ψ ∣ Γ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  ⊢conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {Γ : TermCtx Ψ} {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → lookup σ Y ≡ just α
    → rep? (Ψ ,end[ Y ]) α ≡ just C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ,end[ Y ] ∣ truncateForEnd Γ Y ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ∣ Γ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
