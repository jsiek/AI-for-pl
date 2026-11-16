module DenotInvariants where

-- File Charter:
--   * The syntactic invariant under which the denotation (Denotation.agda)
--     is adequate for reduction (DenotationMeta.agda).
--   * WfPrec n p: every name in the precision derivation p is well formed
--     with n type variables in scope; WfStack n cs for a stack of casts.
--   * Scoped n M: every type-level name in M is well formed with n type
--     variables in scope: the names of seal/unseal, the grounds of is/inj,
--     the precisions of casts and proxies, and the types of λ and
--     instantiation.  A Scoped 0 term is closed: every name substitution
--     fixes it (proof/ScopedProps.agda, closed-substᵀ).  Typing does not
--     imply this, since the typing rule for λ does not check its type.
--   * Proof scripts: proof/ScopedProps.agda.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)

open import Types
open import Terms

------------------------------------------------------------------------
-- Well-scoped precision derivations and stacks
------------------------------------------------------------------------

data WfPrec (n : ℕ) : Prec → Set where
  wfp★   : WfPrec n ★⊑
  wfptag : ∀ {G p} → WfGround n G → WfPrec n p → WfPrec n (tag G p)
  wfp‵   : ∀ {α} → WfName n α → WfPrec n (‵⊑ α)
  wfp𝔹   : WfPrec n 𝔹⊑
  wfp⇒   : ∀ {p q} → WfPrec n p → WfPrec n q → WfPrec n (p ⇒⊑ q)
  wfp∀   : ∀ {p} → WfPrec (suc n) p → WfPrec n (∀⊑ p)

data WfStack (n : ℕ) : Stack → Set where
  wfs[] : WfStack n []
  wfs∷  : ∀ {d p cs} → WfPrec n p → WfStack n cs → WfStack n ((d , p) ∷ cs)

------------------------------------------------------------------------
-- Well-scoped terms
------------------------------------------------------------------------

data Scoped (n : ℕ) : Term → Set where
  sc`      : ∀ {x} → Scoped n (` x)
  sc℧      : Scoped n ℧
  sctrue   : Scoped n true
  scfalse  : Scoped n false
  scif     : ∀ {L M N} →
    Scoped n L → Scoped n M → Scoped n N → Scoped n (if L M N)
  scƛ      : ∀ {A M} → WfTy n A → Scoped n M → Scoped n (ƛ A M)
  sc·      : ∀ {L M} → Scoped n L → Scoped n M → Scoped n (L · M)
  scletv   : ∀ {M N} → Scoped n M → Scoped n N → Scoped n (letv M N)
  scseal   : ∀ {α M} → WfName n α → Scoped n M → Scoped n (seal α M)
  scunseal : ∀ {α M} → WfName n α → Scoped n M → Scoped n (unseal α M)
  scis     : ∀ {G M} → WfGround n G → Scoped n M → Scoped n (is G M)
  scinj    : ∀ {G M} → WfGround n G → Scoped n M → Scoped n (inj G M)
  sccast   : ∀ {d p M} → WfPrec n p → Scoped n M → Scoped n (cast d p M)
  scΛν     : ∀ {cs M} →
    WfStack (suc n) cs → Scoped (suc n) M → Scoped n (Λν cs M)
  scinst   : ∀ {M B N} →
    Scoped n M → WfTy n B → Scoped (suc n) N → Scoped n (inst M B N)
