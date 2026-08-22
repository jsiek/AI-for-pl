module LR-narrow.Context.Constant where

-- File Charter:
--   * Proves the context lemma for the natural-constant term-imprecision
--     rule.
--   * Constructs the related immediate interpreter returns directly.
--   * Uses no provisional dynamic or universal LR clause.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (inj₁)

open import ImprecisionWf using (idι)
open import Interpreter using
  ( blamed
  ; constant
  ; interpret
  ; returned
  )
  renaming (World to RuntimeWorld)
open import LR-narrow.ClosedValues using (constant-closed)
open import LR-narrow.Context.KripkeRefl
open import LR-narrow.Context.TermRelation
open import LR-narrow.LogicalRelation
open import LR-narrow.World
open import NuTerms using ($)
open import Primitives using (κℕ)
open import Typing.InterpreterSemanticTypingCore using (constant-typed)
import Types

private
  constant-endpoints : ∀ {Φ Δᴸ Δᴿ w}
    → (I : Interpretation {Φ} {Δᴸ} {Δᴿ} w)
    → (n : ℕ)
    → TypedClosedEndpoints (idι {ι = Types.`ℕ}) I
        (constant (κℕ n)) (constant (κℕ n))
  constant-endpoints I n =
    typed-closed-endpoints constant-closed constant-closed
      constant-typed constant-typed

  constant-values-related : ∀ {Φ Δᴸ Δᴿ w}
    → (I : Interpretation {Φ} {Δᴸ} {Δᴿ} w)
    → (k n : ℕ)
    → ValueNarrowing (idι {ι = Types.`ℕ}) I k
        (constant (κℕ n)) (constant (κℕ n))
  constant-values-related I zero n = constant-endpoints I n
  constant-values-related I (suc k) n =
    constant-endpoints I n , same-natural n

  constant-forward : ∀ {Φ Δᴸ Δᴿ w γ γ′ k value n U V}
    → (I : Interpretation {Φ} {Δᴸ} {Δᴿ} w)
    → n ≤ k
    → interpret (left-world w) γ (left-types I) ($ (κℕ value)) n
        ≡ returned U V
    →
      (Σ[ m ∈ ℕ ]
       Σ[ U′ ∈ RuntimeWorld ]
       Σ[ V′ ∈ Interpreter.Value ]
       Σ[ future ∈ LR-narrow.World.World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ U) ×
         (right-world future ≡ U′) ×
         (interpret (right-world w) γ′ (right-types I)
           ($ (κℕ value)) m ≡ returned U′ V′) ×
         ValueNarrowing (idι {ι = Types.`ℕ}) futureᵢ
           (k ∸ n) V V′)
      Data.Sum.⊎
      (Σ[ m ∈ ℕ ]
       Σ[ U′ ∈ RuntimeWorld ]
       Σ[ future ∈ LR-narrow.World.World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ U) ×
         (right-world future ≡ U′) ×
         (interpret (right-world w) γ′ (right-types I)
           ($ (κℕ value)) m ≡ blamed U′))
  constant-forward {n = zero} I n≤k ()
  constant-forward {w = w} {k = k} {value = value} {n = suc n} I
      n≤k refl =
    inj₁
      (suc n , right-world w , constant (κℕ value) , w , I ,
       interpretation-⊒ⁱ-refl I , refl , refl , refl ,
       constant-values-related I (k ∸ suc n) value)

  constant-backward : ∀ {Φ Δᴸ Δᴿ w γ γ′ k value n U′ V′}
    → (I : Interpretation {Φ} {Δᴸ} {Δᴿ} w)
    → n ≤ k
    → interpret (right-world w) γ′ (right-types I) ($ (κℕ value)) n
        ≡ returned U′ V′
    → Σ[ m ∈ ℕ ]
      Σ[ U ∈ RuntimeWorld ]
      Σ[ V ∈ Interpreter.Value ]
      Σ[ future ∈ LR-narrow.World.World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ U) ×
        (right-world future ≡ U′) ×
        (interpret (left-world w) γ (left-types I)
          ($ (κℕ value)) m ≡ returned U V) ×
        ValueNarrowing (idι {ι = Types.`ℕ}) futureᵢ
          (k ∸ n) V V′
  constant-backward {n = zero} I n≤k ()
  constant-backward {w = w} {k = k} {value = value} {n = suc n} I
      n≤k refl =
    suc n , left-world w , constant (κℕ value) , w , I ,
    interpretation-⊒ⁱ-refl I , refl , refl , refl ,
    constant-values-related I (k ∸ suc n) value

  constant-forward-blame :
    ∀ {Φ Δᴸ Δᴿ w γ γ′ k value n U}
    → (I : Interpretation {Φ} {Δᴸ} {Δᴿ} w)
    → n ≤ k
    → interpret (left-world w) γ (left-types I) ($ (κℕ value)) n
        ≡ blamed U
    → Σ[ m ∈ ℕ ]
      Σ[ U′ ∈ RuntimeWorld ]
      Σ[ future ∈ LR-narrow.World.World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ U) ×
        (right-world future ≡ U′) ×
        (interpret (right-world w) γ′ (right-types I)
          ($ (κℕ value)) m ≡ blamed U′)
  constant-forward-blame {n = zero} I n≤k ()
  constant-forward-blame {n = suc n} I n≤k ()

constant-context : ∀ {Φ Δᴸ Δᴿ w γ γ′}
  → (I : Interpretation {Φ} {Δᴸ} {Δᴿ} w)
  → (k value : ℕ)
  → TermRelation (idι {ι = Types.`ℕ}) I k γ γ′
      ($ (κℕ value)) ($ (κℕ value))
constant-context I k value = record
  { forward-return = constant-forward I
  ; backward-return = constant-backward I
  ; forward-blame = constant-forward-blame I
  }
