module Terms where

-- File Charter:
--   * Terms of PolyCν (thesis Fig. 10.7), ∀ν fragment.
--   * `Λν cs M` is the polymorphic function proxy Λν{X.([cs], M)}: the
--     casts in `cs` (outermost first) are run on the body when the proxy
--     is instantiated.  A source Λν X.M is `Λν [] M`.
--   * `inst M B ℓ N` is the instantiation form `let x = M {X ≅ B}; N`; in
--     N, type variable 0 is X and term variable 0 is x.  The label ℓ is a
--     precision derivation that does not affect evaluation; the
--     denotational proof of graduality uses it to give corresponding
--     instantiations of two related programs the same label
--     (PolyG/notes/denotational-graduality.md).  Elaboration uses the
--     reflexive derivation of B.
--   * `inj G V` is the thesis's injection ⟨tag_G(G)⟩↑ V.
--   * Term-level substitution of names for type variables, and
--     substitution of terms for term variables.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)

open import Types

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

data Dir : Set where
  up   : Dir
  down : Dir

flip : Dir → Dir
flip up = down
flip down = up

Stack : Set
Stack = List (Dir × Prec)

infixl 7 _·_
infix 9 `_

data Term : Set where
  `_     : ℕ → Term
  ℧      : Term
  true   : Term
  false  : Term
  if     : Term → Term → Term → Term
  ƛ      : Ty → Term → Term
  _·_    : Term → Term → Term
  letv   : Term → Term → Term
  seal   : Name → Term → Term
  unseal : Name → Term → Term
  is     : Ground → Term → Term
  inj    : Ground → Term → Term
  cast   : Dir → Prec → Term → Term
  Λν     : Stack → Term → Term
  inst   : Term → Ty → Prec → Term → Term

-- the term obtained by running a stack of casts on M
stack : Stack → Term → Term
stack [] M = M
stack ((d , p) ∷ cs) M = cast d p (stack cs M)

------------------------------------------------------------------------
-- Substituting names for type variables in terms
------------------------------------------------------------------------

substˢ : NSubst → Stack → Stack
substˢ σ [] = []
substˢ σ ((d , p) ∷ cs) = (d , substᵖ σ p) ∷ substˢ σ cs

substᵀ : NSubst → Term → Term
substᵀ σ (` x) = ` x
substᵀ σ ℧ = ℧
substᵀ σ true = true
substᵀ σ false = false
substᵀ σ (if L M N) = if (substᵀ σ L) (substᵀ σ M) (substᵀ σ N)
substᵀ σ (ƛ A M) = ƛ (substᵗ σ A) (substᵀ σ M)
substᵀ σ (L · M) = substᵀ σ L · substᵀ σ M
substᵀ σ (letv M N) = letv (substᵀ σ M) (substᵀ σ N)
substᵀ σ (seal α M) = seal (substₙ σ α) (substᵀ σ M)
substᵀ σ (unseal α M) = unseal (substₙ σ α) (substᵀ σ M)
substᵀ σ (is G M) = is (substG σ G) (substᵀ σ M)
substᵀ σ (inj G M) = inj (substG σ G) (substᵀ σ M)
substᵀ σ (cast d p M) = cast d (substᵖ σ p) (substᵀ σ M)
substᵀ σ (Λν cs M) = Λν (substˢ (extₙ σ) cs) (substᵀ (extₙ σ) M)
substᵀ σ (inst M B ℓ N) =
  inst (substᵀ σ M) (substᵗ σ B) (substᵖ σ ℓ) (substᵀ (extₙ σ) N)

⇑ᵀ : Term → Term
⇑ᵀ = substᵀ ↑ₙ

infix 8 _[_]ᵀ

_[_]ᵀ : Term → Name → Term
M [ α ]ᵀ = substᵀ (singleₙ α) M

------------------------------------------------------------------------
-- Renaming and substitution of term variables
------------------------------------------------------------------------

Rename : Set
Rename = ℕ → ℕ

Subst : Set
Subst = ℕ → Term

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term → Term
rename ρ (` x) = ` ρ x
rename ρ ℧ = ℧
rename ρ true = true
rename ρ false = false
rename ρ (if L M N) = if (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (ƛ A M) = ƛ A (rename (ext ρ) M)
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (letv M N) = letv (rename ρ M) (rename (ext ρ) N)
rename ρ (seal α M) = seal α (rename ρ M)
rename ρ (unseal α M) = unseal α (rename ρ M)
rename ρ (is G M) = is G (rename ρ M)
rename ρ (inj G M) = inj G (rename ρ M)
rename ρ (cast d p M) = cast d p (rename ρ M)
rename ρ (Λν cs M) = Λν cs (rename ρ M)
rename ρ (inst M B ℓ N) = inst (rename ρ M) B ℓ (rename (ext ρ) N)

exts : Subst → Subst
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

-- moving a substitution under a type binder
⇑ˢ : Subst → Subst
⇑ˢ σ x = ⇑ᵀ (σ x)

subst : Subst → Term → Term
subst σ (` x) = σ x
subst σ ℧ = ℧
subst σ true = true
subst σ false = false
subst σ (if L M N) = if (subst σ L) (subst σ M) (subst σ N)
subst σ (ƛ A M) = ƛ A (subst (exts σ) M)
subst σ (L · M) = subst σ L · subst σ M
subst σ (letv M N) = letv (subst σ M) (subst (exts σ) N)
subst σ (seal α M) = seal α (subst σ M)
subst σ (unseal α M) = unseal α (subst σ M)
subst σ (is G M) = is G (subst σ M)
subst σ (inj G M) = inj G (subst σ M)
subst σ (cast d p M) = cast d p (subst σ M)
subst σ (Λν cs M) = Λν cs (subst (⇑ˢ σ) M)
subst σ (inst M B ℓ N) = inst (subst σ M) B ℓ (subst (exts (⇑ˢ σ)) N)

single : Term → Subst
single V zero = V
single V (suc x) = ` x

infix 8 _[_]

_[_] : Term → Term → Term
N [ V ] = subst (single V) N
