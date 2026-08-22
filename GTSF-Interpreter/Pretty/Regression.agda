module Pretty.Regression where

-- File Charter:
--   * Gives definitional regression checks for representative type,
--     coercion, term, and nested-allocation renderings.
--   * Ensures generated seal names remain distinct from de Bruijn lookup.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero)

open import Coercions
open import NuTerms
open import Pretty.Coercions
open import Pretty.Strings using (_++ˢ_)
open import Pretty.Terms
open import Pretty.Types
open import Types

private
  Nat : Ty
  Nat = ‵ `ℕ

  IdBody : Ty
  IdBody = X₀ ⇒ X₀

  polyId : Term
  polyId = Λ (ƛ (` zero))

  genId : Coercion
  genId = gen (★ ⇒ ★) ((X₀ !) ↦ (X₀ ？))

  instId : Coercion
  instId = inst (★ ⇒ ★) (seal ★ zero ↦ unseal zero ★)

  atNat : Term → Term
  atNat M = ν Nat M (reveal IdBody zero (⇑ᵗ Nat))

render-type-regression :
  renderType (`∀ IdBody) ≡ "∀X. X → X"
render-type-regression = refl

render-coercion-regression :
  renderCoercion genId ≡ "ν α := ★ . α! → α?"
render-coercion-regression = refl

render-inst-coercion-regression :
  renderCoercion instId ≡ "ν̅ α := ★ . α ♯ → α ♭"
render-inst-coercion-regression = refl

render-term-regression :
  renderTerm polyId ≡ "ΛX. λx. x"
render-term-regression = refl

render-nested-ν-regression :
  renderTerm (atNat (atNat polyId)) ≡
    "ν α := Nat. (ν β := Nat. (" ++ˢ
    "ΛX. λx. x) @ β ⟨β ♯ → β ♭⟩)" ++ˢ
    " @ α ⟨α ♯ → α ♭⟩"
render-nested-ν-regression = refl
