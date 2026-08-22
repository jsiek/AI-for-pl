module Pretty.Names where

-- File Charter:
--   * Separates printed universal-binder names from printed seal-binder names.
--   * Provides de Bruijn lookup through the combined type-variable namespace
--     while maintaining independent fresh-name counters.

open import Agda.Builtin.String using (String; primShowNat)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)

open import Pretty.Strings using (_++ˢ_; preferredNameAt)

data TypeName : Set where
  type-binder : String → TypeName
  seal-binder : String → TypeName

spelling : TypeName → String
spelling (type-binder X) = X
spelling (seal-binder α) = α

lookupTypeName : List TypeName → ℕ → String
lookupTypeName [] index = "T" ++ˢ primShowNat index
lookupTypeName (name ∷ names) zero = spelling name
lookupTypeName (name ∷ names) (suc index) = lookupTypeName names index

lookupSealName : List TypeName → ℕ → Maybe String
lookupSealName [] index = nothing
lookupSealName (type-binder X ∷ names) zero = nothing
lookupSealName (seal-binder α ∷ names) zero = just α
lookupSealName (name ∷ names) (suc index) = lookupSealName names index

typeBinderCount : List TypeName → ℕ
typeBinderCount [] = zero
typeBinderCount (type-binder X ∷ names) = suc (typeBinderCount names)
typeBinderCount (seal-binder α ∷ names) = typeBinderCount names

sealBinderCount : List TypeName → ℕ
sealBinderCount [] = zero
sealBinderCount (type-binder X ∷ names) = sealBinderCount names
sealBinderCount (seal-binder α ∷ names) = suc (sealBinderCount names)

freshTypeName : List TypeName → String
freshTypeName names =
  preferredNameAt "X" "Y" "Z" "X" (typeBinderCount names)

sealNameAt : ℕ → String
sealNameAt = preferredNameAt "α" "β" "γ" "α"

freshSealName : List TypeName → String
freshSealName names = sealNameAt (sealBinderCount names)
