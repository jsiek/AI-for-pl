module Runtime.InterpreterOperationalEnvironmentLookup where

-- File Charter:
--   * Looks up synchronized values in an exact operational environment.
--   * Preserves the static context entry and its interpreted endpoint types.
--   * Contains no interpreter call or reduction result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Interpreter
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterTermNarrowing
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
import NuTermImprecision as NTI
open import Types

operational-environment-lookup :
  ∀ {W W′ Φ Δᴸ Δᴿ θ θ′ γᵀ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : RelatedWorlds.WorldRelation W W′} →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  Σ[ V ∈ Value ]
  Σ[ V′ ∈ Value ]
    lookup γ x ≡ just V ×
    lookup γ′ x ≡ just V′ ×
    OperationalValueNarrowing
      ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
operational-environment-lookup
    (value ∷⊑∷ᵒ environment) Z =
  _ , _ , refl , refl , value
operational-environment-lookup
    (value ∷⊑∷ᵒ environment) (S x∈) =
  operational-environment-lookup environment x∈
