module Pretty.TypedTerms where

-- File Charter:
--   * Pretty prints terms from their checked typing derivations.
--   * Restores source-style type annotations on lambda binders, which the
--     extrinsic `NuTerms.Term` syntax itself does not retain.
--   * Reuses the precedence and naming policy of `Pretty.Terms`.

open import Agda.Builtin.String using (String)
open import Data.List using (_∷_)

open import NuTerms
open import Pretty.Coercions
open import Pretty.Names
open import Pretty.Strings
open import Pretty.Terms
open import Pretty.Types

open NameContext

mutual
  renderTypedTermWith : ∀ {Δ Σ Γ M A}
    → NameContext
    → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
    → String
  renderTypedTermWith χ (⊢` {x = x} x∈) =
    lookupName "x" (termNames χ) x
  renderTypedTermWith χ (⊢ƛ {A = A} A-wf body) =
    "λ" ++ˢ x ++ˢ " : " ++ˢ renderTypeWith (typeNames χ) A ++ˢ
    ". " ++ˢ renderTypedTermWith (underTerm x χ) body
    where
      x = freshTermName (termNames χ)
  renderTypedTermWith χ (⊢· function argument) =
    renderTypedApplicationHead χ function ++ˢ " " ++ˢ
    renderTypedArgument χ argument
  renderTypedTermWith χ (⊢Λ value body) =
    "Λ" ++ˢ X ++ˢ ". " ++ˢ renderTypedTermWith (underType X χ) body
    where
      X = freshTypeName (typeNames χ)
  renderTypedTermWith χ (⊢• {V = V} Δ-eq Σ-eq C-wf value no-• body) =
    renderApplicationHead χ (⇑ᵗᵐ V) ++ˢ " •"
  renderTypedTermWith χ (⊢ν {A = A} {c = c} A-wf function coercion) =
    "ν " ++ˢ α ++ˢ " := " ++ˢ renderTypeWith (typeNames χ) A ++ˢ
    ". " ++ˢ renderTypedApplicationHead (reserveSeal χ) function ++ˢ
    " @ " ++ˢ α ++ˢ " ⟨" ++ˢ
    renderCoercionWith (seal-binder α ∷ typeNames χ) c ++ˢ "⟩"
    where
      α = sealNameAt (nextSeal χ)
  renderTypedTermWith χ (⊢$ κ) = renderConst κ
  renderTypedTermWith χ (⊢⊕ left op right) =
    renderTypedArgument χ left ++ˢ " " ++ˢ renderPrim op ++ˢ " " ++ˢ
    renderTypedArgument χ right
  renderTypedTermWith χ (⊢⟨⟩ {c = c} coercion term) =
    renderTypedCastHead χ term ++ˢ " ⟨" ++ˢ
    renderCoercionWith (typeNames χ) c ++ˢ "⟩"
  renderTypedTermWith χ (⊢blame A-wf) = "blame"

  renderTypedApplicationHead : ∀ {Δ Σ Γ M A}
    → NameContext
    → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
    → String
  renderTypedApplicationHead χ proof@(⊢` x∈) =
    renderTypedTermWith χ proof
  renderTypedApplicationHead χ proof@(⊢· function argument) =
    renderTypedTermWith χ proof
  renderTypedApplicationHead χ
      proof@(⊢• Δ-eq Σ-eq C-wf value no-• body) =
    renderTypedTermWith χ proof
  renderTypedApplicationHead χ proof@(⊢$ κ) =
    renderTypedTermWith χ proof
  renderTypedApplicationHead χ proof@(⊢⟨⟩ coercion term) =
    renderTypedTermWith χ proof
  renderTypedApplicationHead χ proof@(⊢blame A-wf) =
    renderTypedTermWith χ proof
  renderTypedApplicationHead χ proof@(⊢ƛ A-wf body) =
    parenthesize (renderTypedTermWith χ proof)
  renderTypedApplicationHead χ proof@(⊢Λ value body) =
    parenthesize (renderTypedTermWith χ proof)
  renderTypedApplicationHead χ proof@(⊢ν A-wf function coercion) =
    parenthesize (renderTypedTermWith χ proof)
  renderTypedApplicationHead χ proof@(⊢⊕ left op right) =
    parenthesize (renderTypedTermWith χ proof)

  renderTypedArgument : ∀ {Δ Σ Γ M A}
    → NameContext
    → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
    → String
  renderTypedArgument χ proof@(⊢` x∈) = renderTypedTermWith χ proof
  renderTypedArgument χ proof@(⊢$ κ) = renderTypedTermWith χ proof
  renderTypedArgument χ proof@(⊢blame A-wf) = renderTypedTermWith χ proof
  renderTypedArgument χ proof = parenthesize (renderTypedTermWith χ proof)

  renderTypedCastHead : ∀ {Δ Σ Γ M A}
    → NameContext
    → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
    → String
  renderTypedCastHead χ proof@(⊢` x∈) = renderTypedTermWith χ proof
  renderTypedCastHead χ proof@(⊢$ κ) = renderTypedTermWith χ proof
  renderTypedCastHead χ proof@(⊢⟨⟩ coercion term) =
    renderTypedTermWith χ proof
  renderTypedCastHead χ proof@(⊢blame A-wf) = renderTypedTermWith χ proof
  renderTypedCastHead χ proof = parenthesize (renderTypedTermWith χ proof)

renderTypedTerm : ∀ {Δ Σ Γ M A}
  → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
  → String
renderTypedTerm = renderTypedTermWith emptyNames
