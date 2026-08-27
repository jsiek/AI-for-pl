module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  A telescope is
--     intrinsically indexed by its slot-to-anchor map σ.  `just α` marks the
--     unique live crossing of α; `nothing` marks a lexical slot.  Begins may
--     insert only an absent anchor, while ends remove exactly the selected
--     slot, so lying marker annotations are unrepresentable.
--   * Representation lookup is the total function `rep?`.  Its two transports
--     are deliberately different: lexical slots travel by their accumulated
--     position route, while crossing slots travel by anchor identity to the
--     query telescope's unique live alias.  A dead crossing recursively reads
--     its older anchor's representation.  Undefined routes refuse with
--     `nothing`; begin/end bracket choices are never consulted.
--   * `_≼[_,_]_` remains only a marker-balance certificate.  Its injection
--     index records lexical drift and delimiter positions for typing transport;
--     it is not representation lookup evidence.

open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
  renaming (map to mapMaybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)
open import Relation.Nullary using (yes; no)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Primitives
open import Consistency
open import alt.ThetaTerms
open import alt.Conversion

private
  variable
    Θ Θ′ : AnchorCtx
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Slot maps
------------------------------------------------------------------------

mapᵛ : ∀ {n} {A B : Set} → (A → B) → Vec.Vec A n → Vec.Vec B n
mapᵛ f Vec.[] = Vec.[]
mapᵛ f (x Vec.∷ xs) = f x Vec.∷ mapᵛ f xs

insertᵛ : ∀ {n} {A : Set}
  → Fin (suc n) → A → Vec.Vec A n → Vec.Vec A (suc n)
insertᵛ zero x xs = x Vec.∷ xs
insertᵛ (suc i) x (y Vec.∷ ys) = y Vec.∷ insertᵛ i x ys

removeᵛ : ∀ {n} {A : Set}
  → Fin (suc n) → Vec.Vec A (suc n) → Vec.Vec A n
removeᵛ zero (x Vec.∷ xs) = xs
removeᵛ {n = suc n} (suc i) (x Vec.∷ xs) =
  x Vec.∷ removeᵛ i xs

infix 4 _∉ᵛ_

_∉ᵛ_ : ∀ {Θ Δ}
  → TyVar Θ → Vec.Vec (Maybe (TyVar Θ)) Δ → Set
α ∉ᵛ σ = ∀ Y → Vec.lookup σ Y ≢ just α

liveSlot? : ∀ {Θ Δ}
  → Vec.Vec (Maybe (TyVar Θ)) Δ → TyVar Θ
  → Maybe (TyVar Δ)
liveSlot? Vec.[] α = nothing
liveSlot? (nothing Vec.∷ σ) α = mapMaybe suc (liveSlot? σ α)
liveSlot? (just β Vec.∷ σ) α with α ≟ β
liveSlot? (just β Vec.∷ σ) .β | yes refl = just zero
liveSlot? (just β Vec.∷ σ) α | no α≢β =
  mapMaybe suc (liveSlot? σ α)

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- The live lookup is a function, so its selected alias is unique.  The
-- telescope's begin field is what makes that selected alias also the only
-- `just α` entry representable in σ.
liveSlot?-unique : ∀ {Θ Δ} {σ : Vec.Vec (Maybe (TyVar Θ)) Δ}
    {α : TyVar Θ} {X Y : TyVar Δ}
  → liveSlot? σ α ≡ just X
  → liveSlot? σ α ≡ just Y
  → X ≡ Y
liveSlot?-unique X-eq Y-eq =
  just-injective (trans (sym X-eq) Y-eq)

------------------------------------------------------------------------
-- Binder telescopes: type variables and anchors, no term variables
------------------------------------------------------------------------

infixl 5 _,begin[_≔_]⟨_⟩ _,typ _,end[_]
infixl 5 _,:=_

data TyEnv : (Θ : AnchorCtx) (Δ : TyCtx)
    → Vec.Vec (Maybe (TyVar Θ)) Δ → Set where
  ∅ : TyEnv zero zero Vec.[]

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
-- Lexical drift and balanced extension
------------------------------------------------------------------------

insert↪ᵗ : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′ → TyVar (suc Δ) → suc Δ ↪ᵗ suc Δ′
insert↪ᵗ ρ zero = keep ρ
insert↪ᵗ (keep ρ) (suc Y) = keep (insert↪ᵗ ρ Y)
insert↪ᵗ (skip ρ) (suc Y) = skip (insert↪ᵗ ρ (suc Y))

delete↪ᵗ : ∀ {Δ Δ′}
  → suc Δ ↪ᵗ suc Δ′ → TyVar (suc Δ) → Δ ↪ᵗ Δ′
delete↪ᵗ (keep ρ) zero = ρ
delete↪ᵗ {Δ = suc Δ} {Δ′ = zero} (keep ()) (suc Y)
delete↪ᵗ {Δ = suc Δ} {Δ′ = suc Δ′} (keep ρ) (suc Y) =
  keep (delete↪ᵗ ρ Y)
delete↪ᵗ {Δ′ = zero} (skip ()) Y
delete↪ᵗ {Δ′ = suc Δ′} (skip ρ) Y = skip (delete↪ᵗ ρ Y)

infixl 7 _⨟↪ᵗ_

_⨟↪ᵗ_ : ∀ {Δ₁ Δ₂ Δ₃}
  → Δ₁ ↪ᵗ Δ₂ → Δ₂ ↪ᵗ Δ₃ → Δ₁ ↪ᵗ Δ₃
empty ⨟↪ᵗ empty = empty
ρ ⨟↪ᵗ skip η = skip (ρ ⨟↪ᵗ η)
empty ⨟↪ᵗ keep η = empty
keep ρ ⨟↪ᵗ keep η = keep (ρ ⨟↪ᵗ η)
skip ρ ⨟↪ᵗ keep η = skip (ρ ⨟↪ᵗ η)

infix 4 _≼[_,_]_

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
    → Vec.lookup σ X ≡ just α
    → Ψ ≼[ k , ρ ] Ψ′
    → (Ψ′ ,end[ toRenameᵗ ρ X ]) ≼[ k′ , η ] Ψ″
    → Shifted (k + k′) α β
    → Ψ ≼[ k + k′ , insert↪ᵗ (delete↪ᵗ ρ X ⨟↪ᵗ η) X ]
        (Ψ″ ,begin[
          toRenameᵗ (insert↪ᵗ (delete↪ᵗ ρ X ⨟↪ᵗ η) X) X ≔ β
        ]⟨ fresh ⟩)

shiftAlong : ∀ {Θ Θ′ Δ Δ′ k σ σ′} {ρ : Δ ↪ᵗ Δ′}
    {Ψ : TyEnv Θ Δ σ} {Ψ′ : TyEnv Θ′ Δ′ σ′}
  → Ψ ≼[ k , ρ ] Ψ′ → TyVar Θ → TyVar Θ′
shiftAlong ≼-refl α = α
shiftAlong (≼-ν extension) α = suc (shiftAlong extension α)
shiftAlong (≼-typ extension) α = shiftAlong extension α
shiftAlong (≼-begin-end extension region) α =
  shiftAlong region (shiftAlong extension α)
shiftAlong (≼-end-begin slot-eq extension region shifted) α =
  shiftAlong region (shiftAlong extension α)

------------------------------------------------------------------------
-- Anchor-directed executable representation lookup
------------------------------------------------------------------------

route-end : ∀ {Δ Δ′}
  → TyVar (suc Δ) → (TyVar Δ → Maybe (TyVar Δ′))
  → TyVar (suc Δ) → Maybe (TyVar Δ′)
route-end Y route X with Y ≟ X
route-end Y route .Y | yes refl = nothing
route-end Y route X | no Y≢X = route (punchOut Y X Y≢X)

ext-route : ∀ {Δ Δ′}
  → (TyVar Δ → Maybe (TyVar Δ′))
  → TyVar (suc Δ) → Maybe (TyVar (suc Δ′))
ext-route route zero = just zero
ext-route route (suc X) = mapMaybe suc (route X)

aliasResult? : ∀ {Θ Δ Δout}
  → (TyVar Θ → Maybe (Ty Δ))
  → Vec.Vec (Maybe (TyVar Θ)) Δ
  → (TyVar Δ → TyVar Δout)
  → TyVar Θ
  → Maybe (Ty Δout)
aliasResult? resolve target live-ren anchor
    with liveSlot? target anchor
aliasResult? resolve target live-ren anchor | just Y =
  just (＇ live-ren Y)
aliasResult? resolve target live-ren anchor | nothing
    with resolve anchor
aliasResult? resolve target live-ren anchor | nothing | nothing = nothing
aliasResult? resolve target live-ren anchor | nothing | just A =
  just (renameᵗ live-ren A)

repoint? : ∀ {Θ₀ Θ Δ₀ Δ Δout}
  → (TyVar Θ → Maybe (Ty Δ))
  → Vec.Vec (Maybe (TyVar Θ)) Δ
  → Vec.Vec (Maybe (TyVar Θ₀)) Δ₀
  → (TyVar (suc Θ₀) → TyVar Θ)
  → (TyVar Δ₀ → Maybe (TyVar Δout))
  → (TyVar Δ → TyVar Δout)
  → Ty Δ₀
  → Maybe (Ty Δout)
repoint? resolve target σ₀ φ route live-ren (＇ X)
    with Vec.lookup σ₀ X
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
    with repoint? resolve target (nothing Vec.∷ σ₀) φ
      (ext-route route) (λ X → suc (live-ren X)) A
repoint? resolve target σ₀ φ route live-ren (`∀ A) | nothing = nothing
repoint? resolve target σ₀ φ route live-ren (`∀ A) | just A′ =
  just (`∀ A′)

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

repFuel? : ∀ (fuel : ℕ) {Θ Δ σ}
  → TyEnv Θ Δ σ → TyVar Θ → Maybe (Ty Δ)
repFuel? zero Ψ α = nothing
repFuel? (suc fuel) Ψ α =
  scanRep? (repFuel? fuel Ψ) Ψ Ψ (λ β → β) (λ X → just X) α

-- Fuel is the queried ν's birth depth: `Θ ∸ toℕ α`.  Resolving a
-- dead crossing asks only for an older ν, and is the sole recursive call;
-- it therefore consumes one unit.  This tighter measure is invariant under
-- inserting a fresh newest ν (`suc Θ ∸ toℕ (suc α)` computes to the
-- same depth), which makes anchor transport expose the intended equation.
rep? : ∀ {Θ Δ σ} → TyEnv Θ Δ σ → TyVar Θ → Maybe (Ty Δ)
rep? {Θ = Θ} Ψ α = repFuel? (Θ ∸ toℕ α) Ψ α

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    σ : Vec.Vec (Maybe (TyVar Θ)) Δ
    Ψ Ψ′ : TyEnv Θ Δ σ
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    F M N : Term Θ Δ
    x y z : Var

infix 4 _∣_⊢_⦂_

data _∣_⊢_⦂_ : ∀ {Θ Δ σ}
  → TyEnv Θ Δ σ → TermCtx Δ → Term Θ Δ → Ty Δ → Set where
  ⊢` :
      Γ ∋ x ⦂ A
      -------------------
    → Ψ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ :
      Ψ ∣ A ∷ Γ ⊢ M ⦂ B
      -----------------------------
    → Ψ ∣ Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· :
      Ψ ∣ Γ ⊢ F ⦂ (A ⇒ B)
    → Ψ ∣ Γ ⊢ M ⦂ A
      ---------------------
    → Ψ ∣ Γ ⊢ (F · M) ⦂ B

  ⊢Λ :
      Ψ ,typ ∣ renameCtx suc Γ ⊢ M ⦂ A
      ----------------------------------
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
      Ψ ,:= A ∣ [] ⊢ M ⦂ B
      ----------------------
    → Ψ ∣ Γ ⊢ ν[ A ] M ⦂ B

  ⊢reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {Γ : TermCtx Δ}
      {M : Term Θ (suc Δ)}
      {A : Ty (suc Δ)} {B C : Ty Δ} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal} {fresh : α ∉ᵛ σ}
    → rep? Ψ α ≡ just C
    → ⊢↑[ Y ⦂ wkᵗ Y C ] c ⦂ A ↝ wkᵗ Y B
    → Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩ ∣ [] ⊢ M ⦂ A
      --------------------------------
    → Ψ ∣ Γ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  ⊢conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {Γ′ : TermCtx (suc Δ)} {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Vec.lookup σ Y ≡ just α
    → rep? (Ψ ,end[ Y ]) α ≡ just C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ,end[ Y ] ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
