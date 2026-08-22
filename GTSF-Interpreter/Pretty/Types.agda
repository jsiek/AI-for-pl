module Pretty.Types where

-- File Charter:
--   * Pretty prints GTSF types with explicit de Bruijn-name environments.
--   * Preserves arrow associativity and introduces names at universal binders.

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)

open import Pretty.Names
open import Pretty.Strings
open import Types

renderBase : Base → String
renderBase `ℕ = "Nat"
renderBase `𝔹 = "Bool"

mutual
  renderTypeWith : List TypeName → Ty → String
  renderTypeWith names (＇ X) = lookupTypeName names X
  renderTypeWith names (‵ ι) = renderBase ι
  renderTypeWith names ★ = "★"
  renderTypeWith names (A ⇒ B) =
    renderTypeDomain names A ++ˢ " → " ++ˢ renderTypeWith names B
  renderTypeWith names (`∀ A) =
    "∀" ++ˢ X ++ˢ ". " ++ˢ
    renderTypeWith (type-binder X ∷ names) A
    where
      X = freshTypeName names

  renderTypeDomain : List TypeName → Ty → String
  renderTypeDomain names (＇ X) = renderTypeWith names (＇ X)
  renderTypeDomain names (‵ ι) = renderTypeWith names (‵ ι)
  renderTypeDomain names ★ = renderTypeWith names ★
  renderTypeDomain names (A ⇒ B) =
    parenthesize (renderTypeWith names (A ⇒ B))
  renderTypeDomain names (`∀ A) =
    parenthesize (renderTypeWith names (`∀ A))

renderType : Ty → String
renderType = renderTypeWith []
