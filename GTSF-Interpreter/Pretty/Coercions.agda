module Pretty.Coercions where

-- File Charter:
--   * Pretty prints every GTSF coercion constructor.
--   * Distinguishes whole-coercion endpoint metadata from the fresh seal's
--     `★` assignment in `gen` and `inst`.
--   * Elides the repeated underlying type from bound seal/unseal actions.

open import Agda.Builtin.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)

open import Coercions
open import Pretty.Names
open import Pretty.Strings
open import Pretty.Types

mutual
  renderCoercionWith : List TypeName → Coercion → String
  renderCoercionWith names (id A) =
    "id[" ++ˢ renderTypeWith names A ++ˢ "]"
  renderCoercionWith names (c ︔ d) =
    renderCoercionWith names c ++ˢ " ; " ++ˢ
    renderCoercionWith names d
  renderCoercionWith names (c ↦ d) =
    renderCoercionDomain names c ++ˢ " → " ++ˢ
    renderCoercionWith names d
  renderCoercionWith names (`∀ c) =
    "∀" ++ˢ X ++ˢ ". " ++ˢ
    renderCoercionWith (type-binder X ∷ names) c
    where
      X = freshTypeName names
  renderCoercionWith names (G !) =
    renderTypeDomain names G ++ˢ "!"
  renderCoercionWith names (G ？) =
    renderTypeDomain names G ++ˢ "?"
  renderCoercionWith names (seal A α) with lookupSealName names α
  renderCoercionWith names (seal A α) | just seal-name =
    seal-name ++ˢ " ♯"
  renderCoercionWith names (seal A α) | nothing =
    renderTypeDomain names A ++ˢ " ♯ " ++ˢ lookupTypeName names α
  renderCoercionWith names (unseal α A) with lookupSealName names α
  renderCoercionWith names (unseal α A) | just seal-name =
    seal-name ++ˢ " ♭"
  renderCoercionWith names (unseal α A) | nothing =
    lookupTypeName names α ++ˢ " ♭ " ++ˢ renderTypeDomain names A
  renderCoercionWith names (gen A c) =
    "ν " ++ˢ α ++ˢ " := ★ . " ++ˢ
    renderCoercionWith (seal-binder α ∷ names) c
    where
      α = freshSealName names
  renderCoercionWith names (inst B c) =
    "ν̅ " ++ˢ α ++ˢ " := ★ . " ++ˢ
    renderCoercionWith (seal-binder α ∷ names) c
    where
      α = freshSealName names

  renderCoercionDomain : List TypeName → Coercion → String
  renderCoercionDomain names (id A) = renderCoercionWith names (id A)
  renderCoercionDomain names (G !) = renderCoercionWith names (G !)
  renderCoercionDomain names (G ？) = renderCoercionWith names (G ？)
  renderCoercionDomain names (seal A α) =
    renderCoercionWith names (seal A α)
  renderCoercionDomain names (unseal α A) =
    renderCoercionWith names (unseal α A)
  renderCoercionDomain names (c ︔ d) =
    parenthesize (renderCoercionWith names (c ︔ d))
  renderCoercionDomain names (c ↦ d) =
    parenthesize (renderCoercionWith names (c ↦ d))
  renderCoercionDomain names (`∀ c) =
    parenthesize (renderCoercionWith names (`∀ c))
  renderCoercionDomain names (gen A c) =
    parenthesize (renderCoercionWith names (gen A c))
  renderCoercionDomain names (inst B c) =
    parenthesize (renderCoercionWith names (inst B c))

renderCoercion : Coercion → String
renderCoercion = renderCoercionWith []
