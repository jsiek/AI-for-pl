module strong-rep-nu.Lookup where

-- File Charter:
--   * THE LOOKUP FUNCTIONS, each returning the ordinary derivation:
--     `lookupˡ?`, `find?`, `lookupʳ?`, `unread?`, and the lookup square
--     `∋:=?`.  They sit BELOW strong-rep-nu.Conversion, whose
--     composition `Δ ⊢ c₁ ⨟ c₂` reads a sealed name's representation
--     through `∋:=?`; strong-rep-nu.TypeCheck re-exports them.
--   * `respell η η′`, the renaming a crossing applies to a conversion:
--     each name of η to η′'s name for the same representation variable.
--     `lookupˡ?-complete` and `find?-complete` say the two searches it
--     runs miss nothing.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong-rep-nu.Ctx

lookupˡ? : ∀ {A : Set} (xs : List A) (i : ℕ) → Maybe (∃[ x ] xs ∋ˡ i := x)
lookupˡ? []       i       = nothing
lookupˡ? (x ∷ xs) zero    = just (x , here)
lookupˡ? (x ∷ xs) (suc i) with lookupˡ? xs i
lookupˡ? (x ∷ xs) (suc i) | just (y , d) = just (y , there d)
lookupˡ? (x ∷ xs) (suc i) | nothing      = nothing

-- Where a representation variable currently sits, if it is live at all.
-- This is what the re-bind clause of `_∣_⊢χᶜ_⇒_` needs.
find? : (Δ : TyCtx) (α : RVar) → Maybe (∃[ X ] Δ ∋ˡ X := α)
find? []      α = nothing
find? (β ∷ Δ) α with α ≟ β
find? (β ∷ Δ) α | yes refl = just (zero , here)
find? (β ∷ Δ) α | no  _    with find? Δ α
find? (β ∷ Δ) α | no  _    | just (X , d) = just (suc X , there d)
find? (β ∷ Δ) α | no  _    | nothing      = nothing

lookupʳ? : (Ξ : RepCtx) (α : RVar) → Maybe (∃[ b ] Ξ ∋ʳ α := b)
lookupʳ? []            α       = nothing
lookupʳ? (b ∷ Ξ)       zero    = just (renRepBinding suc b , r-here)
lookupʳ? (bindR R ∷ Ξ) (suc α) with lookupʳ? Ξ α
lookupʳ? (bindR R ∷ Ξ) (suc α) | just (b , d) =
  just (renRepBinding suc b , r-there d)
lookupʳ? (bindR R ∷ Ξ) (suc α) | nothing = nothing
lookupʳ? (abstR ∷ Ξ)   (suc α) with lookupʳ? Ξ α
lookupʳ? (abstR ∷ Ξ)   (suc α) | just (b , d) =
  just (renRepBinding suc b , r-there-abst d)
lookupʳ? (abstR ∷ Ξ)   (suc α) | nothing = nothing

-- Backward: the ordinary spelling a representation type has under a given
-- name map, if it has one.
unread? : (η : TyCtx) (R : Ty) → Maybe (∃[ A ] η ⊢ A ~ R)
unread? η (` α) with find? η α
unread? η (` α) | just (X , d) = just (` X , same-var d)
unread? η (` α) | nothing      = nothing
unread? η `ℕ = just (`ℕ , same-ℕ)
unread? η `𝔹 = just (`𝔹 , same-𝔹)
unread? η (R ⇒ S) with unread? η R
unread? η (R ⇒ S) | nothing = nothing
unread? η (R ⇒ S) | just (A , p) with unread? η S
unread? η (R ⇒ S) | just (A , p) | just (B , q) =
  just (A ⇒ B , same-⇒ p q)
unread? η (R ⇒ S) | just (A , p) | nothing = nothing
unread? η (`∀ R) with unread? (zero ∷ shiftReps η) R
unread? η (`∀ R) | just (A , p) = just (`∀ A , same-∀ p)
unread? η (`∀ R) | nothing      = nothing

∋:=? : (Γ : Ctxᵗ) (X : ℕ) → Maybe (∃[ A ] Γ ∋ X := A)
∋:=? Γ X with lookupˡ? (names Γ) X
∋:=? Γ X | nothing = nothing
∋:=? Γ X | just (α , nm) with lookupʳ? (reps Γ) α
∋:=? Γ X | just (α , nm) | nothing = nothing
∋:=? Γ X | just (α , nm) | just (abstR , rp) = nothing
∋:=? Γ X | just (α , nm) | just (bindR R , rp) with unread? (names Γ) R
∋:=? Γ X | just (α , nm) | just (bindR R , rp) | nothing = nothing
∋:=? Γ X | just (α , nm) | just (bindR R , rp) | just (A , sm) =
  just (A , α , R , nm , rp , sm)

------------------------------------------------------------------------
-- Respelling, and the completeness of the two searches it runs
------------------------------------------------------------------------

-- each name of η to η′'s name for the same representation variable; a
-- name η or η′ lacks is left alone (a typed conversion has none)
respell : TyCtx → TyCtx → ℕ → ℕ
respell η η′ X with lookupˡ? η X
respell η η′ X | just (α , _) with find? η′ α
respell η η′ X | just (α , _) | just (Y , _) = Y
respell η η′ X | just (α , _) | nothing      = X
respell η η′ X | nothing = X

lookupˡ?-complete : ∀ {A : Set} (xs : List A) (i : ℕ) {x}
  → xs ∋ˡ i := x → lookupˡ? xs i ≡ nothing → ⊥
lookupˡ?-complete (x ∷ xs) zero here ()
lookupˡ?-complete (y ∷ xs) (suc i) (there d) eq with lookupˡ? xs i in e
lookupˡ?-complete (y ∷ xs) (suc i) (there d) () | just _
lookupˡ?-complete (y ∷ xs) (suc i) (there d) eq | nothing =
  lookupˡ?-complete xs i d e

find?-complete : (η : TyCtx) (α : RVar) {Y : ℕ}
  → η ∋ˡ Y := α → find? η α ≡ nothing → ⊥
find?-complete (α ∷ η) α here eq with α ≟ α
find?-complete (α ∷ η) α here () | yes refl
find?-complete (α ∷ η) α here eq | no ne = ne refl
find?-complete (β ∷ η) α (there d) eq with α ≟ β
find?-complete (β ∷ η) α (there d) () | yes refl
find?-complete (β ∷ η) α (there d) eq | no ne with find? η α in e
find?-complete (β ∷ η) α (there d) () | no ne | just _
find?-complete (β ∷ η) α (there d) eq | no ne | nothing =
  find?-complete η α d e
