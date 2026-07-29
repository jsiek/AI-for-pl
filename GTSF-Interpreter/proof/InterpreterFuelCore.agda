module proof.InterpreterFuelCore where

-- File Charter:
--   * Proves terminal-result stability for the four mutually recursive
--     direct-interpreter functions.
--   * Uses mutual induction on the original step index.
--   * Contains no reduction semantics or reduction-derived result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _+_)
open import Relation.Nullary using (yes; no)

open import Coercions
  using (Coercion)
  renaming
    ( id to idᶜ
    ; _︔_ to _︔ᶜ_
    ; _↦_ to _↦ᶜ_
    ; `∀ to ∀ᶜ
    ; _! to _!ᶜ
    ; _？ to _？ᶜ
    ; seal to sealᶜ
    ; unseal to unsealᶜ
    ; gen to genᶜ
    ; inst to instᶜ
    )
open import Interpreter
open import InterpreterOutcome
open import NuTerms
  using (Term)
  renaming
    ( `_ to `ᴵ_
    ; ƛ_ to ƛᴵ_
    ; _·_ to _·ᴵ_
    ; Λ_ to Λᴵ_
    ; _• to _•ᴵ
    ; ν to νᴵ
    ; $ to $ᴵ
    ; _⊕[_]_ to _⊕ᴵ[_]_
    ; _⟨_⟩ to _⟨ᴵ_⟩
    ; blame to blameᴵ
    )
open import Types using (★)

mutual

  interpret-terminal-stableᵖ :
    (n : StepIndex) →
    ∀ {W γ θ M o} →
    Terminal o →
    interpret W γ θ M n ≡ o →
    (k : StepIndex) →
    interpret W γ θ M (n + k) ≡ o

  interpret-terminal-stableᵖ zero terminal eq k =
    ⊥-elim (timed-terminal-absurd eq terminal)

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {`ᴵ x} terminal eq k
      with lookup γ x
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {`ᴵ x} terminal eq k
      | just V =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {`ᴵ x} terminal eq k
      | nothing =
    eq

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {ƛᴵ N} terminal eq k =
    eq

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      with interpret W γ θ L n in L-eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | timed W₁ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | blamed W₁
      rewrite interpret-terminal-stableᵖ n terminal-blame L-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | failed W₁ e
      rewrite interpret-terminal-stableᵖ n terminal-error L-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | returned W₁ V
      with interpret W₁ γ θ M n in M-eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | returned W₁ V | timed W₂ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | returned W₁ V | blamed W₂
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | interpret-terminal-stableᵖ n terminal-blame M-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | returned W₁ V | failed W₂ e
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | interpret-terminal-stableᵖ n terminal-error M-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ·ᴵ M} terminal eq k
      | returned W₁ V | returned W₂ U
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | interpret-terminal-stableᵖ n terminal-return M-eq k =
    applyValue-terminal-stableᵖ n terminal eq k

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {Λᴵ V} terminal eq k
      with syntacticValue? V
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {Λᴵ V} terminal eq k
      | no ¬vV =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {Λᴵ V} terminal eq k
      | yes vV
      with closeValue (Λᴵ vV) γ θ
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {Λᴵ V} terminal eq k
      | yes vV | just U =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {Λᴵ V} terminal eq k
      | yes vV | nothing =
    eq

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {M •ᴵ} terminal eq k =
    eq

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      with interpret W γ θ L n in L-eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | timed W₁ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | blamed W₁
      rewrite interpret-terminal-stableᵖ n terminal-blame L-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | failed W₁ e
      rewrite interpret-terminal-stableᵖ n terminal-error L-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | returned W₁ V
      with instantiateValue
        (allocate W₁ A θ) (freshSealName W₁) V n
        in inst-eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | returned W₁ V | timed W₃ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | returned W₁ V | blamed W₃
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | instantiateValue-terminal-stableᵖ
                n terminal-blame inst-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | returned W₁ V | failed W₃ e
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | instantiateValue-terminal-stableᵖ
                n terminal-error inst-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {νᴵ A L c} terminal eq k
      | returned W₁ V | returned W₃ U
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | instantiateValue-terminal-stableᵖ
                n terminal-return inst-eq k =
    coerceValue-terminal-stableᵖ n terminal eq k

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {$ᴵ κ} terminal eq k =
    eq

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      with interpret W γ θ L n in L-eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | timed W₁ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | blamed W₁
      rewrite interpret-terminal-stableᵖ n terminal-blame L-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | failed W₁ e
      rewrite interpret-terminal-stableᵖ n terminal-error L-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | returned W₁ V
      with interpret W₁ γ θ M n in M-eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | returned W₁ V | timed W₂ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | returned W₁ V | blamed W₂
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | interpret-terminal-stableᵖ n terminal-blame M-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | returned W₁ V | failed W₂ e
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | interpret-terminal-stableᵖ n terminal-error M-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {L ⊕ᴵ[ op ] M} terminal eq k
      | returned W₁ V | returned W₂ U
      rewrite interpret-terminal-stableᵖ n terminal-return L-eq k
            | interpret-terminal-stableᵖ n terminal-return M-eq k =
    eq

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {M ⟨ᴵ c ⟩} terminal eq k
      with interpret W γ θ M n in M-eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {M ⟨ᴵ c ⟩} terminal eq k
      | timed W₁ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {M ⟨ᴵ c ⟩} terminal eq k
      | blamed W₁
      rewrite interpret-terminal-stableᵖ n terminal-blame M-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {M ⟨ᴵ c ⟩} terminal eq k
      | failed W₁ e
      rewrite interpret-terminal-stableᵖ n terminal-error M-eq k =
    eq
  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {M ⟨ᴵ c ⟩} terminal eq k
      | returned W₁ V
      rewrite interpret-terminal-stableᵖ n terminal-return M-eq k =
    coerceValue-terminal-stableᵖ n terminal eq k

  interpret-terminal-stableᵖ (suc n)
      {W} {γ} {θ} {blameᴵ} terminal eq k =
    eq

  applyValue-terminal-stableᵖ :
    (n : StepIndex) →
    ∀ {W V U o} →
    Terminal o →
    applyValue W V U n ≡ o →
    (k : StepIndex) →
    applyValue W V U (n + k) ≡ o

  applyValue-terminal-stableᵖ zero terminal eq k =
    ⊥-elim (timed-terminal-absurd eq terminal)

  applyValue-terminal-stableᵖ (suc n)
      {W} {closure N γ θ} {U} terminal eq k =
    interpret-terminal-stableᵖ n terminal eq k

  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      with coerceValue W θ p U n in p-eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | timed W₁ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | blamed W₁
      rewrite coerceValue-terminal-stableᵖ
        n terminal-blame p-eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | failed W₁ e
      rewrite coerceValue-terminal-stableᵖ
        n terminal-error p-eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | returned W₁ U′
      with applyValue W₁ V U′ n in apply-eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | returned W₁ U′ | timed W₂ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | returned W₁ U′ | blamed W₂
      rewrite coerceValue-terminal-stableᵖ
                n terminal-return p-eq k
            | applyValue-terminal-stableᵖ
                n terminal-blame apply-eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | returned W₁ U′ | failed W₂ e
      rewrite coerceValue-terminal-stableᵖ
                n terminal-return p-eq k
            | applyValue-terminal-stableᵖ
                n terminal-error apply-eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {function-proxy p q θ V} {U} terminal eq k
      | returned W₁ U′ | returned W₂ V′
      rewrite coerceValue-terminal-stableᵖ
                n terminal-return p-eq k
            | applyValue-terminal-stableᵖ
                n terminal-return apply-eq k =
    coerceValue-terminal-stableᵖ n terminal eq k

  applyValue-terminal-stableᵖ (suc n)
      {W} {type-abstraction X V} {U} terminal eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {constant κ} {U} terminal eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {tagged gG θ V} {U} terminal eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {sealed α V} {U} terminal eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {forall-proxy c θ V} {U} terminal eq k =
    eq
  applyValue-terminal-stableᵖ (suc n)
      {W} {generalized A c θ V} {U} terminal eq k =
    eq

  instantiateValue-terminal-stableᵖ :
    (n : StepIndex) →
    ∀ {W α V o} →
    Terminal o →
    instantiateValue W α V n ≡ o →
    (k : StepIndex) →
    instantiateValue W α V (n + k) ≡ o

  instantiateValue-terminal-stableᵖ zero terminal eq k =
    ⊥-elim (timed-terminal-absurd eq terminal)

  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {type-abstraction X V} terminal eq k =
    eq

  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {forall-proxy c θ V} terminal eq k
      with instantiateValue W α V n in inst-eq
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {forall-proxy c θ V} terminal eq k
      | timed W₁ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {forall-proxy c θ V} terminal eq k
      | blamed W₁
      rewrite instantiateValue-terminal-stableᵖ
        n terminal-blame inst-eq k =
    eq
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {forall-proxy c θ V} terminal eq k
      | failed W₁ e
      rewrite instantiateValue-terminal-stableᵖ
        n terminal-error inst-eq k =
    eq
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {forall-proxy c θ V} terminal eq k
      | returned W₁ U
      rewrite instantiateValue-terminal-stableᵖ
        n terminal-return inst-eq k =
    coerceValue-terminal-stableᵖ n terminal eq k

  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {generalized A c θ V} terminal eq k =
    coerceValue-terminal-stableᵖ n terminal eq k

  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {closure N γ θ} terminal eq k =
    eq
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {constant κ} terminal eq k =
    eq
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {tagged gG θ V} terminal eq k =
    eq
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {sealed β V} terminal eq k =
    eq
  instantiateValue-terminal-stableᵖ (suc n)
      {W} {α} {function-proxy p q θ V} terminal eq k =
    eq

  coerceValue-terminal-stableᵖ :
    (n : StepIndex) →
    ∀ {W θ c V o} →
    Terminal o →
    coerceValue W θ c V n ≡ o →
    (k : StepIndex) →
    coerceValue W θ c V (n + k) ≡ o

  coerceValue-terminal-stableᵖ zero terminal eq k =
    ⊥-elim (timed-terminal-absurd eq terminal)

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {idᶜ A} {V} terminal eq k =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {c ︔ᶜ d} {V} terminal eq k
      with coerceValue W θ c V n in c-eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {c ︔ᶜ d} {V} terminal eq k
      | timed W₁ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {c ︔ᶜ d} {V} terminal eq k
      | blamed W₁
      rewrite coerceValue-terminal-stableᵖ
        n terminal-blame c-eq k =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {c ︔ᶜ d} {V} terminal eq k
      | failed W₁ e
      rewrite coerceValue-terminal-stableᵖ
        n terminal-error c-eq k =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {c ︔ᶜ d} {V} terminal eq k
      | returned W₁ U
      rewrite coerceValue-terminal-stableᵖ
        n terminal-return c-eq k =
    coerceValue-terminal-stableᵖ n terminal eq k

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {p ↦ᶜ q} {V} terminal eq k =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {∀ᶜ c} {V} terminal eq k =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G !ᶜ} {V} terminal eq k
      with ground? G
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G !ᶜ} {V} terminal eq k
      | no ¬gG =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G !ᶜ} {V} terminal eq k
      | yes gG
      with tagOf θ gG
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G !ᶜ} {V} terminal eq k
      | yes gG | just tag =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G !ᶜ} {V} terminal eq k
      | yes gG | nothing =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {V} terminal eq k
      with ground? G
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {V} terminal eq k
      | no ¬gG =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {V} terminal eq k
      | yes gG
      with tagOf θ gG
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {V} terminal eq k
      | yes gG | nothing =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {tagged {G = H} gH θ′ V} terminal eq k
      | yes gG | just expected
      with tagOf θ′ gH
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {tagged {G = H} gH θ′ V} terminal eq k
      | yes gG | just expected | nothing =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {tagged {G = H} gH θ′ V} terminal eq k
      | yes gG | just expected | just actual
      with expected ≟Tag actual
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {tagged {G = H} gH θ′ V} terminal eq k
      | yes gG | just expected | just actual | yes refl =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {tagged {G = H} gH θ′ V} terminal eq k
      | yes gG | just expected | just actual | no expected≢actual =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {closure N γ θ′} terminal eq k
      | yes gG | just expected =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {type-abstraction X V} terminal eq k
      | yes gG | just expected =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {constant κ} terminal eq k
      | yes gG | just expected =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {sealed α V} terminal eq k
      | yes gG | just expected =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {function-proxy p q θ′ V} terminal eq k
      | yes gG | just expected =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {forall-proxy c θ′ V} terminal eq k
      | yes gG | just expected =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {G ？ᶜ} {generalized A c θ′ V} terminal eq k
      | yes gG | just expected =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {sealᶜ A X} {V} terminal eq k
      with lookup θ X
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {sealᶜ A X} {V} terminal eq k
      | just (seal-name α) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {sealᶜ A X} {V} terminal eq k
      | just (abstract-name Y) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {sealᶜ A X} {V} terminal eq k
      | nothing =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {V} terminal eq k
      with lookup θ X
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {V} terminal eq k
      | nothing =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {V} terminal eq k
      | just (abstract-name Y) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {sealed β V} terminal eq k
      | just (seal-name α)
      with α ≟SealName β
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {sealed .α V} terminal eq k
      | just (seal-name α) | yes refl =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {sealed β V} terminal eq k
      | just (seal-name α) | no α≢β =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {closure N γ θ′} terminal eq k
      | just (seal-name α) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {type-abstraction Y V} terminal eq k
      | just (seal-name α) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {constant κ} terminal eq k
      | just (seal-name α) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {tagged gG θ′ V} terminal eq k
      | just (seal-name α) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A}
      {function-proxy p q θ′ V} terminal eq k
      | just (seal-name α) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {forall-proxy c θ′ V} terminal eq k
      | just (seal-name α) =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {unsealᶜ X A} {generalized B c θ′ V} terminal eq k
      | just (seal-name α) =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {genᶜ A c} {V} terminal eq k =
    eq

  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {instᶜ B c} {V} terminal eq k
      with instantiateValue
        (allocate W ★ θ) (freshSealName W) V n
        in inst-eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {instᶜ B c} {V} terminal eq k
      | timed W₃ =
    ⊥-elim (timed-terminal-absurd eq terminal)
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {instᶜ B c} {V} terminal eq k
      | blamed W₃
      rewrite instantiateValue-terminal-stableᵖ
        n terminal-blame inst-eq k =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {instᶜ B c} {V} terminal eq k
      | failed W₃ e
      rewrite instantiateValue-terminal-stableᵖ
        n terminal-error inst-eq k =
    eq
  coerceValue-terminal-stableᵖ (suc n)
      {W} {θ} {instᶜ B c} {V} terminal eq k
      | returned W₃ U
      rewrite instantiateValue-terminal-stableᵖ
        n terminal-return inst-eq k =
    coerceValue-terminal-stableᵖ n terminal eq k
