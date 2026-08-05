module proof.InterpreterValueSubstitutionShapeProof where

-- File Charter:
--   * Proves outer-shape inversion for semantic name substitution.
--   * Covers all eight official semantic value forms exhaustively.
--   * Contains no interpreter execution or reduction argument.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Nullary using (no; yes)

open import Interpreter
open import Types

substitute-name-sealed-source :
  ∀ (X : Name) (α : SealName) (V : Value) {β U} →
  substituteName X α V ≡ sealed β U →
  Σ[ Q ∈ Value ] V ≡ sealed β Q
substitute-name-sealed-source X α (closure N γ θ) ()
substitute-name-sealed-source X α (constant κ) ()
substitute-name-sealed-source X α (tagged gG θ V) ()
substitute-name-sealed-source X α (sealed β V) refl =
  V , refl
substitute-name-sealed-source X α (function-proxy p q θ V) ()
substitute-name-sealed-source X α (type-abstraction Y V) eq
    with X ≟Name Y
substitute-name-sealed-source X α (type-abstraction .X V) ()
    | yes refl
substitute-name-sealed-source X α (type-abstraction Y V) ()
    | no X≢Y
substitute-name-sealed-source X α (forall-proxy c θ V) ()
substitute-name-sealed-source X α (generalized A c θ V) ()

substitute-name-constant-source :
  ∀ (X : Name) (α : SealName) (V : Value) {κ} →
  substituteName X α V ≡ constant κ →
  V ≡ constant κ
substitute-name-constant-source X α (closure N γ θ) ()
substitute-name-constant-source X α (constant κ) refl =
  refl
substitute-name-constant-source X α (tagged gG θ V) ()
substitute-name-constant-source X α (sealed β V) ()
substitute-name-constant-source X α (function-proxy p q θ V) ()
substitute-name-constant-source X α (type-abstraction Y V) eq
    with X ≟Name Y
substitute-name-constant-source X α (type-abstraction .X V) ()
    | yes refl
substitute-name-constant-source X α (type-abstraction Y V) ()
    | no X≢Y
substitute-name-constant-source X α (forall-proxy c θ V) ()
substitute-name-constant-source X α (generalized A c θ V) ()
