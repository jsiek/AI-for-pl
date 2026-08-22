module Pretty.Terms where

-- File Charter:
--   * Pretty prints all `NuTerms.Term` constructors with precedence-aware
--     parentheses and generated names for term, type, and seal binders.
--   * Renders `ν` in the compiled type-application notation used by the
--     Cambridge notes.

open import Agda.Builtin.String using (String; primShowNat)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)

open import NuTerms
open import Pretty.Coercions
open import Pretty.Names
open import Pretty.Strings
open import Pretty.Types
open import Primitives

record NameContext : Set where
  constructor names
  field
    typeNames : List TypeName
    termNames : List String
    nextSeal : ℕ

open NameContext

emptyNames : NameContext
emptyNames = names [] [] 0

underType : String → NameContext → NameContext
underType X χ =
  names (type-binder X ∷ typeNames χ)
    (termNames χ) (nextSeal χ)

underTerm : String → NameContext → NameContext
underTerm x χ =
  names (typeNames χ) (x ∷ termNames χ) (nextSeal χ)

reserveSeal : NameContext → NameContext
reserveSeal χ =
  names (typeNames χ) (termNames χ) (suc (nextSeal χ))

renderConst : Const → String
renderConst (κℕ n) = primShowNat n

renderPrim : Prim → String
renderPrim addℕ = "+"

mutual
  renderTermWith : NameContext → Term → String
  renderTermWith χ (` x) = lookupName "x" (termNames χ) x
  renderTermWith χ (ƛ M) =
    "λ" ++ˢ x ++ˢ ". " ++ˢ renderTermWith (underTerm x χ) M
    where
      x = freshTermName (termNames χ)
  renderTermWith χ (L · M) =
    renderApplicationHead χ L ++ˢ " " ++ˢ renderArgument χ M
  renderTermWith χ (Λ M) =
    "Λ" ++ˢ X ++ˢ ". " ++ˢ renderTermWith (underType X χ) M
    where
      X = freshTypeName (typeNames χ)
  renderTermWith χ (M •) = renderApplicationHead χ M ++ˢ " •"
  renderTermWith χ (ν A L c) =
    "ν " ++ˢ α ++ˢ " := " ++ˢ renderTypeWith (typeNames χ) A ++ˢ
    ". " ++ˢ renderApplicationHead (reserveSeal χ) L ++ˢ " @ " ++ˢ α ++ˢ
    " ⟨" ++ˢ
    renderCoercionWith (seal-binder α ∷ typeNames χ) c ++ˢ "⟩"
    where
      α = sealNameAt (nextSeal χ)
  renderTermWith χ ($ κ) = renderConst κ
  renderTermWith χ (L ⊕[ op ] M) =
    renderArgument χ L ++ˢ " " ++ˢ renderPrim op ++ˢ " " ++ˢ
    renderArgument χ M
  renderTermWith χ (M ⟨ c ⟩) =
    renderCastHead χ M ++ˢ " ⟨" ++ˢ
    renderCoercionWith (typeNames χ) c ++ˢ "⟩"
  renderTermWith χ blame = "blame"

  renderApplicationHead : NameContext → Term → String
  renderApplicationHead χ (` x) = renderTermWith χ (` x)
  renderApplicationHead χ (L · M) = renderTermWith χ (L · M)
  renderApplicationHead χ (M •) = renderTermWith χ (M •)
  renderApplicationHead χ ($ κ) = renderTermWith χ ($ κ)
  renderApplicationHead χ (M ⟨ c ⟩) = renderTermWith χ (M ⟨ c ⟩)
  renderApplicationHead χ blame = renderTermWith χ blame
  renderApplicationHead χ (ƛ M) = parenthesize (renderTermWith χ (ƛ M))
  renderApplicationHead χ (Λ M) = parenthesize (renderTermWith χ (Λ M))
  renderApplicationHead χ (ν A L c) =
    parenthesize (renderTermWith χ (ν A L c))
  renderApplicationHead χ (L ⊕[ op ] M) =
    parenthesize (renderTermWith χ (L ⊕[ op ] M))

  renderArgument : NameContext → Term → String
  renderArgument χ (` x) = renderTermWith χ (` x)
  renderArgument χ ($ κ) = renderTermWith χ ($ κ)
  renderArgument χ blame = renderTermWith χ blame
  renderArgument χ (ƛ M) = parenthesize (renderTermWith χ (ƛ M))
  renderArgument χ (L · M) = parenthesize (renderTermWith χ (L · M))
  renderArgument χ (Λ M) = parenthesize (renderTermWith χ (Λ M))
  renderArgument χ (M •) = parenthesize (renderTermWith χ (M •))
  renderArgument χ (ν A L c) = parenthesize (renderTermWith χ (ν A L c))
  renderArgument χ (L ⊕[ op ] M) =
    parenthesize (renderTermWith χ (L ⊕[ op ] M))
  renderArgument χ (M ⟨ c ⟩) =
    parenthesize (renderTermWith χ (M ⟨ c ⟩))

  renderCastHead : NameContext → Term → String
  renderCastHead χ (` x) = renderTermWith χ (` x)
  renderCastHead χ ($ κ) = renderTermWith χ ($ κ)
  renderCastHead χ (M ⟨ c ⟩) = renderTermWith χ (M ⟨ c ⟩)
  renderCastHead χ blame = renderTermWith χ blame
  renderCastHead χ (ƛ M) = parenthesize (renderTermWith χ (ƛ M))
  renderCastHead χ (L · M) = parenthesize (renderTermWith χ (L · M))
  renderCastHead χ (Λ M) = parenthesize (renderTermWith χ (Λ M))
  renderCastHead χ (M •) = parenthesize (renderTermWith χ (M •))
  renderCastHead χ (ν A L c) = parenthesize (renderTermWith χ (ν A L c))
  renderCastHead χ (L ⊕[ op ] M) =
    parenthesize (renderTermWith χ (L ⊕[ op ] M))

renderTerm : Term → String
renderTerm = renderTermWith emptyNames
