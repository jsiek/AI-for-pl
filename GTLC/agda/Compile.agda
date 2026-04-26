module Compile where

-- File Charter:
--   * Compilation function from GTLC typing derivations to cast-calculus terms.
--   * Preservation/precision proofs live in `proof/CompileMeta.agda`.

open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst)
open import Types
open import Contexts
open import Data.List using ([])
import GTLC as G
open import Coercions
open import CastCalculus

compile-∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ A
compile-∋ Z = Z
compile-∋ (S ∋x) = S (compile-∋ ∋x)

compile : ∀ {Γ M A} → Γ G.⊢ M ⦂ A → Termᶜ
compile (G.⊢` {x = x} _) = ` x
compile (G.⊢$ {n = n}) = $ n
compile (G.⊢ƛ {A = A} N⦂B) = ƛ A ⇒ compile N⦂B
compile (G.⊢· {ℓ = ℓ} L⦂A⇒B M⦂A′ A′~A) =
  compile L⦂A⇒B · cast compile M⦂A′ [ coerce ℓ A′~A ]
compile (G.⊢·★ {A = A} {ℓ = ℓ} L⦂★ M⦂A) =
  cast compile L⦂★ [ coerce ℓ (★~-ty (★ ⇒ ★)) ]
    · cast compile M⦂A [ coerce ℓ (~★-ty A) ]


--------------------------------------------------------------------------------
-- Private Metatheory
--------------------------------------------------------------------------------

-- Compilation preservation and precision proofs are implemented in
-- `proof/CompileMeta.agda`.
