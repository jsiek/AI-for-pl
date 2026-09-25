module strong-rep-nu.notes.SourceReduction where

-- File Charter:
--   * A SMALL-STEP CALL-BY-VALUE REDUCTION FOR THE SOURCE LANGUAGE
--     (strong-rep-nu.Source has none).  §1 type renaming and
--     substitution on `STerm`; §2 term renaming and substitution;
--     §3 the relation `_⟶ˢ_` (`β-ƛ`, `β-Λ`, `ξˢ-·₁`, `ξˢ-·₂`, `ξˢ-[]`)
--     and its closure `_⟶ˢ*_`; §4 a step function `stepˢ` that RETURNS
--     the derivation, so that `refl` checks in notes/ErasureProbe are
--     about the relation.
--   * PLAIN SYSTEM F, with the value restriction of `⊢ˢΛ`: a type
--     abstraction's body is a value, so there is no congruence under
--     `Λ`, and `β-Λ` asks for `SValue N`.  Substitution is the
--     standard one: under `ƛ` the image is shifted in the TERM
--     universe, under `Λ` in the TYPE universe.
--   * A NOTES MODULE: it edits nothing in Source.agda.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (∃-syntax; _,_; proj₁)

open import strong-rep-nu.Types
open import strong-rep-nu.Terms using (Var)
open import strong-rep-nu.Source

------------------------------------------------------------------------
-- 1. Types in terms
------------------------------------------------------------------------

renameˢᵗ : Renameᵗ → STerm → STerm
renameˢᵗ ρ (` x)     = ` x
renameˢᵗ ρ ($ k)     = $ k
renameˢᵗ ρ `true     = `true
renameˢᵗ ρ `false    = `false
renameˢᵗ ρ (ƛ A ∙ N) = ƛ renameᵗ ρ A ∙ renameˢᵗ ρ N
renameˢᵗ ρ (L · M)   = renameˢᵗ ρ L · renameˢᵗ ρ M
renameˢᵗ ρ (Λ N)     = Λ (renameˢᵗ (extᵗ ρ) N)
renameˢᵗ ρ (L [ A ]) = renameˢᵗ ρ L [ renameᵗ ρ A ]

substˢᵗ : Substᵗ → STerm → STerm
substˢᵗ σ (` x)     = ` x
substˢᵗ σ ($ k)     = $ k
substˢᵗ σ `true     = `true
substˢᵗ σ `false    = `false
substˢᵗ σ (ƛ A ∙ N) = ƛ substᵗ σ A ∙ substˢᵗ σ N
substˢᵗ σ (L · M)   = substˢᵗ σ L · substˢᵗ σ M
substˢᵗ σ (Λ N)     = Λ (substˢᵗ (extsᵗ σ) N)
substˢᵗ σ (L [ A ]) = substˢᵗ σ L [ substᵗ σ A ]

-- N [ A ]ᵀ : the type β-rule's substitution, type variable 0 := A
infix 8 _[_]ᵀ
_[_]ᵀ : STerm → Ty → STerm
N [ A ]ᵀ = substˢᵗ (singleTyEnv A) N

------------------------------------------------------------------------
-- 2. Terms in terms
------------------------------------------------------------------------

extˢ : (Var → Var) → Var → Var
extˢ ρ zero    = zero
extˢ ρ (suc x) = suc (ρ x)

renameˢ : (Var → Var) → STerm → STerm
renameˢ ρ (` x)     = ` (ρ x)
renameˢ ρ ($ k)     = $ k
renameˢ ρ `true     = `true
renameˢ ρ `false    = `false
renameˢ ρ (ƛ A ∙ N) = ƛ A ∙ renameˢ (extˢ ρ) N
renameˢ ρ (L · M)   = renameˢ ρ L · renameˢ ρ M
renameˢ ρ (Λ N)     = Λ (renameˢ ρ N)
renameˢ ρ (L [ A ]) = renameˢ ρ L [ A ]

extsˢ : (Var → STerm) → Var → STerm
extsˢ σ zero    = ` zero
extsˢ σ (suc x) = renameˢ suc (σ x)

-- under `Λ` the image crosses a type binder: shift its TYPES
substˢ : (Var → STerm) → STerm → STerm
substˢ σ (` x)     = σ x
substˢ σ ($ k)     = $ k
substˢ σ `true     = `true
substˢ σ `false    = `false
substˢ σ (ƛ A ∙ N) = ƛ A ∙ substˢ (extsˢ σ) N
substˢ σ (L · M)   = substˢ σ L · substˢ σ M
substˢ σ (Λ N)     = Λ (substˢ (λ x → renameˢᵗ suc (σ x)) N)
substˢ σ (L [ A ]) = substˢ σ L [ A ]

singleˢ : STerm → Var → STerm
singleˢ W zero    = W
singleˢ W (suc x) = ` x

-- N [ W ]ᵛ : the β-rule's substitution, term variable 0 := W
infix 8 _[_]ᵛ
_[_]ᵛ : STerm → STerm → STerm
N [ W ]ᵛ = substˢ (singleˢ W) N

------------------------------------------------------------------------
-- 3. Reduction
------------------------------------------------------------------------

infix 2 _⟶ˢ_
data _⟶ˢ_ : STerm → STerm → Set where

  β-ƛ : ∀ {A N W} → SValue W
      → (ƛ A ∙ N) · W ⟶ˢ N [ W ]ᵛ

  β-Λ : ∀ {N A} → SValue N
      → (Λ N) [ A ] ⟶ˢ N [ A ]ᵀ

  ξˢ-·₁ : ∀ {L L′ M} → L ⟶ˢ L′
        → L · M ⟶ˢ L′ · M

  ξˢ-·₂ : ∀ {V M M′} → SValue V → M ⟶ˢ M′
        → V · M ⟶ˢ V · M′

  ξˢ-[] : ∀ {L L′ A} → L ⟶ˢ L′
        → L [ A ] ⟶ˢ L′ [ A ]

infix 2 _⟶ˢ*_
data _⟶ˢ*_ : STerm → STerm → Set where
  doneˢ  : ∀ {M} → M ⟶ˢ* M
  _thenˢ_ : ∀ {L M N} → L ⟶ˢ M → M ⟶ˢ* N → L ⟶ˢ* N

infixr 2 _thenˢ_

------------------------------------------------------------------------
-- 4. The step function
------------------------------------------------------------------------

StepResultˢ : STerm → Set
StepResultˢ M = ∃[ N ] (M ⟶ˢ N)

private
  appRedexˢ : ∀ {L M} → SValue L → SValue M
    → Maybe (StepResultˢ (L · M))
  appRedexˢ SV-ƛ     vM = just (_ , β-ƛ vM)
  appRedexˢ SV-$     vM = nothing
  appRedexˢ SV-true  vM = nothing
  appRedexˢ SV-false vM = nothing
  appRedexˢ (SV-Λ v) vM = nothing

  tappRedexˢ : ∀ {L} (A : Ty) → SValue L
    → Maybe (StepResultˢ (L [ A ]))
  tappRedexˢ A (SV-Λ v) = just (_ , β-Λ v)
  tappRedexˢ A SV-ƛ     = nothing
  tappRedexˢ A SV-$     = nothing
  tappRedexˢ A SV-true  = nothing
  tappRedexˢ A SV-false = nothing

-- leftmost-outermost, call by value
stepˢ : (M : STerm) → Maybe (StepResultˢ M)
stepˢ (` x)     = nothing
stepˢ ($ k)     = nothing
stepˢ `true     = nothing
stepˢ `false    = nothing
stepˢ (ƛ A ∙ N) = nothing
stepˢ (Λ N)     = nothing
stepˢ (L · M) with stepˢ L
stepˢ (L · M) | just (L′ , s) = just (L′ · M , ξˢ-·₁ s)
stepˢ (L · M) | nothing with svalue? L
stepˢ (L · M) | nothing | nothing = nothing
stepˢ (L · M) | nothing | just vL with stepˢ M
stepˢ (L · M) | nothing | just vL | just (M′ , s) =
  just (L · M′ , ξˢ-·₂ vL s)
stepˢ (L · M) | nothing | just vL | nothing with svalue? M
stepˢ (L · M) | nothing | just vL | nothing | nothing = nothing
stepˢ (L · M) | nothing | just vL | nothing | just vM = appRedexˢ vL vM
stepˢ (L [ A ]) with stepˢ L
stepˢ (L [ A ]) | just (L′ , s) = just (L′ [ A ] , ξˢ-[] s)
stepˢ (L [ A ]) | nothing with svalue? L
stepˢ (L [ A ]) | nothing | nothing = nothing
stepˢ (L [ A ]) | nothing | just vL = tappRedexˢ A vL

stepToˢ : STerm → Maybe STerm
stepToˢ M = Maybe.map proj₁ (stepˢ M)

-- the states of a source run, the first one included
runˢ : ℕ → STerm → List STerm
runˢ zero    M = M ∷ []
runˢ (suc k) M with stepˢ M
runˢ (suc k) M | nothing       = M ∷ []
runˢ (suc k) M | just (M′ , s) = M ∷ runˢ k M′
