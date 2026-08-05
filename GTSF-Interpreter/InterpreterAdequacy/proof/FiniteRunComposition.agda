module InterpreterAdequacy.proof.FiniteRunComposition where

-- File Charter:
--   * Combines independently constructed finite interpreter returns or blame
--     outcomes at one common fuel index.
--   * Covers every sequencing shape used by term interpretation and the
--     three semantic-value entry points.
--   * Contains no typing, trace, reduction, or narrowing dependency.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (_+_; suc; zero)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import Coercions as C
open import Interpreter
open import Core.InterpreterFuel using
  ( applyValue-terminal-stable
  ; coerceValue-terminal-stable
  ; instantiateValue-terminal-stable
  ; interpret-terminal-stable
  )
open import Core.InterpreterOutcome using (terminal-blame; terminal-return)
import NuTerms as N
open import Primitives using (addℕ)
open import Types using (★)

private
  Computation : Set
  Computation = StepIndex → Outcome

  chain :
    Computation →
    (World → Value → Computation) →
    Computation
  chain head continuation n with head n
  chain head continuation n | timed W = timed W
  chain head continuation n | blamed W = blamed W
  chain head continuation n | failed W e = failed W e
  chain head continuation n | returned W V = continuation W V n

  sequence :
    World →
    Computation →
    (World → Value → Computation) →
    Computation
  sequence W head continuation zero = timed W
  sequence W head continuation (suc n) = chain head continuation n

  chain-after-return :
    (head : Computation) →
    (continuation : World → Value → Computation) →
    ∀ {n W V} →
    head n ≡ returned W V →
    chain head continuation n ≡ continuation W V n
  chain-after-return head continuation {n = n} head-eq
      with head n
  chain-after-return head continuation refl | returned W V = refl

  chain-after-blame :
    (head : Computation) →
    (continuation : World → Value → Computation) →
    ∀ {n W} →
    head n ≡ blamed W →
    chain head continuation n ≡ blamed W
  chain-after-blame head continuation {n = n} head-eq with head n
  chain-after-blame head continuation refl | blamed W = refl

  sequence-after-return :
    ∀ W₀ →
    (head : Computation) →
    (continuation : World → Value → Computation) →
    ∀ {n W V} →
    head n ≡ returned W V →
    sequence W₀ head continuation (suc n) ≡ continuation W V n
  sequence-after-return W₀ head continuation =
    chain-after-return head continuation

  sequence-after-blame :
    ∀ W₀ →
    (head : Computation) →
    (continuation : World → Value → Computation) →
    ∀ {n W} →
    head n ≡ blamed W →
    sequence W₀ head continuation (suc n) ≡ blamed W
  sequence-after-blame W₀ head continuation =
    chain-after-blame head continuation

  rotate-three : ∀ a b c → b + (a + c) ≡ a + (b + c)
  rotate-three a b c =
    trans (sym (+-assoc b a c))
      (trans (cong (_+ c) (+-comm b a)) (+-assoc a b c))

  move-third : ∀ a b c → c + (a + b) ≡ a + (b + c)
  move-third a b c =
    trans (sym (+-assoc c a b))
      (trans (cong (_+ b) (+-comm c a))
        (trans (+-assoc a c b)
          (cong (a +_) (+-comm c b))))

  applyValue-cont : Value → World → Value → Computation
  applyValue-cont V U Q = applyValue U V Q

  application-computation-eq :
    ∀ {W γ θ L M} n →
    interpret W γ θ (L N.· M) n ≡
    sequence W (interpret W γ θ L)
      (λ U V → chain (interpret U γ θ M) (applyValue-cont V)) n
  application-computation-eq zero = refl
  application-computation-eq {W} {γ} {θ} {L} {M} (suc n)
      with interpret W γ θ L n
  application-computation-eq (suc n) | timed U = refl
  application-computation-eq (suc n) | blamed U = refl
  application-computation-eq (suc n) | failed U e = refl
  application-computation-eq {W} {γ} {θ} {L} {M} (suc n)
      | returned U V
      with interpret U γ θ M n
  application-computation-eq (suc n) | returned U V | timed Z = refl
  application-computation-eq (suc n) | returned U V | blamed Z = refl
  application-computation-eq (suc n) | returned U V | failed Z e = refl
  application-computation-eq (suc n) | returned U V | returned Z Q = refl

  primitive-computation-eq :
    ∀ {W γ θ L M} n →
    interpret W γ θ (L N.⊕[ addℕ ] M) n ≡
    sequence W (interpret W γ θ L)
      (λ U V → chain (interpret U γ θ M)
        (λ Z Q k → applyPrimitive Z addℕ V Q)) n
  primitive-computation-eq zero = refl
  primitive-computation-eq {W} {γ} {θ} {L} {M} (suc n)
      with interpret W γ θ L n
  primitive-computation-eq (suc n) | timed U = refl
  primitive-computation-eq (suc n) | blamed U = refl
  primitive-computation-eq (suc n) | failed U e = refl
  primitive-computation-eq {W} {γ} {θ} {L} {M} (suc n)
      | returned U V
      with interpret U γ θ M n
  primitive-computation-eq (suc n) | returned U V | timed Z = refl
  primitive-computation-eq (suc n) | returned U V | blamed Z = refl
  primitive-computation-eq (suc n) | returned U V | failed Z e = refl
  primitive-computation-eq (suc n) | returned U V | returned Z Q = refl

  cast-computation-eq :
    ∀ {W γ θ M c} n →
    interpret W γ θ (M N.⟨ c ⟩) n ≡
    sequence W (interpret W γ θ M)
      (λ Z Q k → coerceValue Z θ c Q k) n
  cast-computation-eq zero = refl
  cast-computation-eq {W} {γ} {θ} {M} {c} (suc n)
      with interpret W γ θ M n
  cast-computation-eq (suc n) | timed Z = refl
  cast-computation-eq (suc n) | blamed Z = refl
  cast-computation-eq (suc n) | failed Z e = refl
  cast-computation-eq (suc n) | returned Z Q = refl

  proxy-computation-eq :
    ∀ {W p q θ V U} n →
    applyValue W (function-proxy p q θ V) U n ≡
    sequence W (coerceValue W θ p U)
      (λ Z Q → chain (applyValue Z V Q)
        (λ T P k → coerceValue T θ q P k)) n
  proxy-computation-eq zero = refl
  proxy-computation-eq {W} {p} {q} {θ} {V} {U} (suc n)
      with coerceValue W θ p U n
  proxy-computation-eq (suc n) | timed Z = refl
  proxy-computation-eq (suc n) | blamed Z = refl
  proxy-computation-eq (suc n) | failed Z e = refl
  proxy-computation-eq {W} {p} {q} {θ} {V} {U} (suc n)
      | returned Z Q
      with applyValue Z V Q n
  proxy-computation-eq (suc n) | returned Z Q | timed T = refl
  proxy-computation-eq (suc n) | returned Z Q | blamed T = refl
  proxy-computation-eq (suc n) | returned Z Q | failed T e = refl
  proxy-computation-eq (suc n) | returned Z Q | returned T P = refl

  nu-computation-eq :
    ∀ {W γ θ A L c} n →
    interpret W γ θ (N.ν A L c) n ≡
    sequence W (interpret W γ θ L)
      (λ U V →
        chain (instantiateValue
          (allocate U A θ) (freshSealName U) V)
          (λ Z Q k →
            coerceValue Z (seal-name (freshSealName U) ∷ θ) c Q k)) n
  nu-computation-eq zero = refl
  nu-computation-eq {W} {γ} {θ} {A} {L} {c} (suc n)
      with interpret W γ θ L n
  nu-computation-eq (suc n) | timed U = refl
  nu-computation-eq (suc n) | blamed U = refl
  nu-computation-eq (suc n) | failed U e = refl
  nu-computation-eq {W} {γ} {θ} {A} {L} {c} (suc n)
      | returned U V
      with instantiateValue (allocate U A θ) (freshSealName U) V n
  nu-computation-eq (suc n) | returned U V | timed Z = refl
  nu-computation-eq (suc n) | returned U V | blamed Z = refl
  nu-computation-eq (suc n) | returned U V | failed Z e = refl
  nu-computation-eq (suc n) | returned U V | returned Z Q = refl

  forall-computation-eq :
    ∀ {W α c θ V} n →
    instantiateValue W α (forall-proxy c θ V) n ≡
    sequence W (instantiateValue W α V)
      (λ Z U k → coerceValue Z (seal-name α ∷ θ) c U k) n
  forall-computation-eq zero = refl
  forall-computation-eq {W} {α} {c} {θ} {V} (suc n)
      with instantiateValue W α V n
  forall-computation-eq (suc n) | timed Z = refl
  forall-computation-eq (suc n) | blamed Z = refl
  forall-computation-eq (suc n) | failed Z e = refl
  forall-computation-eq (suc n) | returned Z U = refl

  sequence-coercion-eq :
    ∀ {W θ c d V} n →
    coerceValue W θ (c C.︔ d) V n ≡
    sequence W (coerceValue W θ c V)
      (λ Z U k → coerceValue Z θ d U k) n
  sequence-coercion-eq zero = refl
  sequence-coercion-eq {W} {θ} {c} {d} {V} (suc n)
      with coerceValue W θ c V n
  sequence-coercion-eq (suc n) | timed Z = refl
  sequence-coercion-eq (suc n) | blamed Z = refl
  sequence-coercion-eq (suc n) | failed Z e = refl
  sequence-coercion-eq (suc n) | returned Z U = refl

  inst-coercion-eq :
    ∀ {W θ B c V} n →
    coerceValue W θ (C.inst B c) V n ≡
    sequence W
      (instantiateValue (allocate W ★ θ) (freshSealName W) V)
      (λ Z U k →
        coerceValue Z (seal-name (freshSealName W) ∷ θ) c U k) n
  inst-coercion-eq zero = refl
  inst-coercion-eq {W} {θ} {B} {c} {V} (suc n)
      with instantiateValue (allocate W ★ θ) (freshSealName W) V n
  inst-coercion-eq (suc n) | timed Z = refl
  inst-coercion-eq (suc n) | blamed Z = refl
  inst-coercion-eq (suc n) | failed Z e = refl
  inst-coercion-eq (suc n) | returned Z U = refl

interpret-application-from-phases :
  ∀ {W γ θ L M nL W₁ F nM W₂ U nA W₃ R} →
  interpret W γ θ L nL ≡ returned W₁ F →
  interpret W₁ γ θ M nM ≡ returned W₂ U →
  applyValue W₂ F U nA ≡ returned W₃ R →
  interpret W γ θ (L N.· M) (suc (nL + (nM + nA))) ≡
    returned W₃ R
interpret-application-from-phases
    {W} {γ} {θ} {L} {M} {nL} {W₁} {F} {nM} {W₂} {U}
    {nA} {W₃} {R} L-eq M-eq A-eq =
  trans (application-computation-eq (suc total))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U V → chain (interpret U γ θ M) (applyValue-cont V))
        {n = total} L-total)
      (trans
        (chain-after-return (interpret W₁ γ θ M)
          (applyValue-cont F) {n = total} M-total)
        A-total))
  where
  total = nL + (nM + nA)
  L-total : interpret W γ θ L total ≡ returned W₁ F
  L-total = interpret-terminal-stable
    {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
    terminal-return L-eq (nM + nA)
  M-total : interpret W₁ γ θ M total ≡ returned W₂ U
  M-total = subst (λ n → interpret W₁ γ θ M n ≡ returned W₂ U)
    (rotate-three nL nM nA)
    (interpret-terminal-stable
      {W = W₁} {γ = γ} {θ = θ} {M = M} {n = nM}
      terminal-return M-eq (nL + nA))
  A-total : applyValue W₂ F U total ≡ returned W₃ R
  A-total = subst (λ n → applyValue W₂ F U n ≡ returned W₃ R)
    (move-third nL nM nA)
    (applyValue-terminal-stable
      {W = W₂} {V = F} {U = U} {n = nA}
      terminal-return A-eq (nL + nM))

interpret-primitive-from-phases :
  ∀ {W γ θ L M nL W₁ V nM W₂ U R} →
  interpret W γ θ L nL ≡ returned W₁ V →
  interpret W₁ γ θ M nM ≡ returned W₂ U →
  applyPrimitive W₂ addℕ V U ≡ returned W₂ R →
  interpret W γ θ (L N.⊕[ addℕ ] M) (suc (nL + nM)) ≡
    returned W₂ R
interpret-primitive-from-phases
    {W} {γ} {θ} {L} {M} {nL} {W₁} {V} {nM} {W₂} {U}
    {R} L-eq M-eq primitive-eq =
  trans (primitive-computation-eq (suc (nL + nM)))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U′ V′ → chain (interpret U′ γ θ M)
          (λ Z Q k → applyPrimitive Z addℕ V′ Q))
        {n = nL + nM}
        (interpret-terminal-stable
          {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
          terminal-return L-eq nM))
      (trans
        (chain-after-return (interpret W₁ γ θ M)
          (λ Z Q k → applyPrimitive Z addℕ V Q)
          {n = nL + nM} M-total)
        primitive-eq))
  where
  M-total : interpret W₁ γ θ M (nL + nM) ≡ returned W₂ U
  M-total = subst (λ n → interpret W₁ γ θ M n ≡ returned W₂ U)
    (+-comm nM nL)
    (interpret-terminal-stable
      {W = W₁} {γ = γ} {θ = θ} {M = M} {n = nM}
      terminal-return M-eq nL)

interpret-cast-from-phases :
  ∀ {W γ θ M c nM W₁ V nC W₂ R} →
  interpret W γ θ M nM ≡ returned W₁ V →
  coerceValue W₁ θ c V nC ≡ returned W₂ R →
  interpret W γ θ (M N.⟨ c ⟩) (suc (nM + nC)) ≡ returned W₂ R
interpret-cast-from-phases
    {W} {γ} {θ} {M} {c} {nM} {W₁} {V} {nC} {W₂} {R}
    M-eq C-eq =
  trans (cast-computation-eq (suc (nM + nC)))
    (trans
      (sequence-after-return W (interpret W γ θ M)
        (λ Z Q → coerceValue Z θ c Q) {n = nM + nC}
        (interpret-terminal-stable
          {W = W} {γ = γ} {θ = θ} {M = M} {n = nM}
          terminal-return M-eq nC))
      C-total)
  where
  C-total : coerceValue W₁ θ c V (nM + nC) ≡ returned W₂ R
  C-total = subst (λ n → coerceValue W₁ θ c V n ≡ returned W₂ R)
    (+-comm nC nM)
    (coerceValue-terminal-stable
      {W = W₁} {θ = θ} {c = c} {V = V} {n = nC}
      terminal-return C-eq nM)

apply-closure-from-body :
  ∀ {W N γ θ U n Z R} →
  interpret W (U ∷ γ) θ N n ≡ returned Z R →
  applyValue W (closure N γ θ) U (suc n) ≡ returned Z R
apply-closure-from-body body-eq = body-eq

apply-proxy-from-phases :
  ∀ {W p q θ V U nP W₁ U′ nA W₂ V′ nQ W₃ R} →
  coerceValue W θ p U nP ≡ returned W₁ U′ →
  applyValue W₁ V U′ nA ≡ returned W₂ V′ →
  coerceValue W₂ θ q V′ nQ ≡ returned W₃ R →
  applyValue W (function-proxy p q θ V) U
    (suc (nP + (nA + nQ))) ≡ returned W₃ R
apply-proxy-from-phases
    {W} {p} {q} {θ} {V} {U} {nP} {W₁} {U′} {nA} {W₂} {V′}
    {nQ} {W₃} {R} P-eq A-eq Q-eq =
  trans (proxy-computation-eq (suc total))
    (trans
      (sequence-after-return W (coerceValue W θ p U)
        (λ Z Q → chain (applyValue Z V Q)
          (λ T P k → coerceValue T θ q P k))
        {n = total} P-total)
      (trans
        (chain-after-return (applyValue W₁ V U′)
          (λ T P k → coerceValue T θ q P k)
          {n = total} A-total)
        Q-total))
  where
  total = nP + (nA + nQ)
  P-total : coerceValue W θ p U total ≡ returned W₁ U′
  P-total = coerceValue-terminal-stable
    {W = W} {θ = θ} {c = p} {V = U} {n = nP}
    terminal-return P-eq (nA + nQ)
  A-total : applyValue W₁ V U′ total ≡ returned W₂ V′
  A-total = subst (λ n → applyValue W₁ V U′ n ≡ returned W₂ V′)
    (rotate-three nP nA nQ)
    (applyValue-terminal-stable
      {W = W₁} {V = V} {U = U′} {n = nA}
      terminal-return A-eq (nP + nQ))
  Q-total : coerceValue W₂ θ q V′ total ≡ returned W₃ R
  Q-total = subst
    (λ n → coerceValue W₂ θ q V′ n ≡ returned W₃ R)
    (move-third nP nA nQ)
    (coerceValue-terminal-stable
      {W = W₂} {θ = θ} {c = q} {V = V′} {n = nQ}
      terminal-return Q-eq (nP + nA))

instantiate-forall-from-phases :
  ∀ {W α c θ V nI W₁ U nC W₂ R} →
  instantiateValue W α V nI ≡ returned W₁ U →
  coerceValue W₁ (seal-name α ∷ θ) c U nC ≡ returned W₂ R →
  instantiateValue W α (forall-proxy c θ V) (suc (nI + nC)) ≡
    returned W₂ R
instantiate-forall-from-phases
    {W} {α} {c} {θ} {V} {nI} {W₁} {U} {nC} {W₂} {R}
    I-eq C-eq =
  trans (forall-computation-eq (suc (nI + nC)))
    (trans
      (sequence-after-return W (instantiateValue W α V)
        (λ Z Q → coerceValue Z (seal-name α ∷ θ) c Q)
        {n = nI + nC}
        (instantiateValue-terminal-stable
          {W = W} {α = α} {V = V} {n = nI}
          terminal-return I-eq nC))
      C-total)
  where
  C-total :
    coerceValue W₁ (seal-name α ∷ θ) c U (nI + nC) ≡ returned W₂ R
  C-total = subst
    (λ n → coerceValue W₁ (seal-name α ∷ θ) c U n ≡ returned W₂ R)
    (+-comm nC nI)
    (coerceValue-terminal-stable
      {W = W₁} {θ = seal-name α ∷ θ} {c = c} {V = U}
      {n = nC} terminal-return C-eq nI)

coerce-sequence-from-phases :
  ∀ {W θ c d V nC W₁ U nD W₂ R} →
  coerceValue W θ c V nC ≡ returned W₁ U →
  coerceValue W₁ θ d U nD ≡ returned W₂ R →
  coerceValue W θ (c C.︔ d) V (suc (nC + nD)) ≡ returned W₂ R
coerce-sequence-from-phases
    {W} {θ} {c} {d} {V} {nC} {W₁} {U} {nD} {W₂} {R}
    C-eq D-eq =
  trans (sequence-coercion-eq (suc (nC + nD)))
    (trans
      (sequence-after-return W (coerceValue W θ c V)
        (λ Z Q → coerceValue Z θ d Q)
        {n = nC + nD}
        (coerceValue-terminal-stable
          {W = W} {θ = θ} {c = c} {V = V} {n = nC}
          terminal-return C-eq nD))
      D-total)
  where
  D-total : coerceValue W₁ θ d U (nC + nD) ≡ returned W₂ R
  D-total = subst (λ n → coerceValue W₁ θ d U n ≡ returned W₂ R)
    (+-comm nD nC)
    (coerceValue-terminal-stable
      {W = W₁} {θ = θ} {c = d} {V = U} {n = nD}
      terminal-return D-eq nC)

interpret-nu-from-phases :
  ∀ {W γ θ A L c nL W₁ V nI W₂ U nC W₃ R} →
  interpret W γ θ L nL ≡ returned W₁ V →
  instantiateValue (allocate W₁ A θ) (freshSealName W₁) V nI ≡
    returned W₂ U →
  coerceValue W₂ (seal-name (freshSealName W₁) ∷ θ) c U nC ≡
    returned W₃ R →
  interpret W γ θ (N.ν A L c) (suc (nL + (nI + nC))) ≡
    returned W₃ R
interpret-nu-from-phases
    {W} {γ} {θ} {A} {L} {c} {nL} {W₁} {V} {nI} {W₂} {U}
    {nC} {W₃} {R} L-eq I-eq C-eq =
  trans (nu-computation-eq (suc total))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U′ V′ →
          chain (instantiateValue
            (allocate U′ A θ) (freshSealName U′) V′)
            (λ Z Q k →
              coerceValue Z
                (seal-name (freshSealName U′) ∷ θ) c Q k))
        {n = total} L-total)
      (trans
        (chain-after-return
          (instantiateValue (allocate W₁ A θ) (freshSealName W₁) V)
          (λ Z Q k →
            coerceValue Z (seal-name (freshSealName W₁) ∷ θ) c Q k)
          {n = total} I-total)
        C-total))
  where
  total = nL + (nI + nC)
  L-total : interpret W γ θ L total ≡ returned W₁ V
  L-total = interpret-terminal-stable
    {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
    terminal-return L-eq (nI + nC)
  I-total :
    instantiateValue (allocate W₁ A θ) (freshSealName W₁) V total ≡
      returned W₂ U
  I-total = subst
    (λ n → instantiateValue (allocate W₁ A θ)
      (freshSealName W₁) V n ≡ returned W₂ U)
    (rotate-three nL nI nC)
    (instantiateValue-terminal-stable
      {W = allocate W₁ A θ} {α = freshSealName W₁} {V = V}
      {n = nI} terminal-return I-eq (nL + nC))
  C-total :
    coerceValue W₂ (seal-name (freshSealName W₁) ∷ θ) c U total ≡
      returned W₃ R
  C-total = subst
    (λ n → coerceValue W₂
      (seal-name (freshSealName W₁) ∷ θ) c U n ≡ returned W₃ R)
    (move-third nL nI nC)
    (coerceValue-terminal-stable
      {W = W₂} {θ = seal-name (freshSealName W₁) ∷ θ}
      {c = c} {V = U} {n = nC}
      terminal-return C-eq (nL + nI))

coerce-instantiation-from-phases :
  ∀ {W θ B c V nI W₁ U nC W₂ R} →
  instantiateValue (allocate W ★ θ) (freshSealName W) V nI ≡
    returned W₁ U →
  coerceValue W₁ (seal-name (freshSealName W) ∷ θ) c U nC ≡
    returned W₂ R →
  coerceValue W θ (C.inst B c) V (suc (nI + nC)) ≡ returned W₂ R
coerce-instantiation-from-phases
    {W} {θ} {B} {c} {V} {nI} {W₁} {U} {nC} {W₂} {R}
    I-eq C-eq =
  trans (inst-coercion-eq {W = W} {θ = θ} {B = B} {c = c} {V = V}
    (suc (nI + nC)))
    (trans
      (sequence-after-return W
        (instantiateValue (allocate W ★ θ) (freshSealName W) V)
        (λ Z Q →
          coerceValue Z (seal-name (freshSealName W) ∷ θ) c Q)
        {n = nI + nC}
        (instantiateValue-terminal-stable
          {W = allocate W ★ θ} {α = freshSealName W} {V = V}
          {n = nI} terminal-return I-eq nC))
      C-total)
  where
  C-total :
    coerceValue W₁ (seal-name (freshSealName W) ∷ θ) c U (nI + nC) ≡
      returned W₂ R
  C-total = subst
    (λ n → coerceValue W₁ (seal-name (freshSealName W) ∷ θ)
      c U n ≡ returned W₂ R)
    (+-comm nC nI)
    (coerceValue-terminal-stable
      {W = W₁} {θ = seal-name (freshSealName W) ∷ θ}
      {c = c} {V = U} {n = nC} terminal-return C-eq nI)

------------------------------------------------------------------------
-- Blame propagation through interpreter sequencing
------------------------------------------------------------------------

interpret-application-from-left-blame :
  ∀ {W γ θ L M n Z} →
  interpret W γ θ L n ≡ blamed Z →
  interpret W γ θ (L N.· M) (suc n) ≡ blamed Z
interpret-application-from-left-blame {W} {γ} {θ} {L} {M} {n} L-eq =
  trans (application-computation-eq (suc n))
    (sequence-after-blame W (interpret W γ θ L)
      (λ U V → chain (interpret U γ θ M) (applyValue-cont V))
      {n = n} L-eq)

interpret-application-from-right-blame :
  ∀ {W γ θ L M nL W₁ F nM Z} →
  interpret W γ θ L nL ≡ returned W₁ F →
  interpret W₁ γ θ M nM ≡ blamed Z →
  interpret W γ θ (L N.· M) (suc (nL + nM)) ≡ blamed Z
interpret-application-from-right-blame
    {W} {γ} {θ} {L} {M} {nL} {W₁} {F} {nM} {Z} L-eq M-eq =
  trans (application-computation-eq (suc total))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U V → chain (interpret U γ θ M) (applyValue-cont V))
        {n = total} L-total)
      (chain-after-blame (interpret W₁ γ θ M)
        (applyValue-cont F) {n = total} M-total))
  where
  total = nL + nM
  L-total = interpret-terminal-stable
    {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
    terminal-return L-eq nM
  M-total : interpret W₁ γ θ M total ≡ blamed Z
  M-total = subst (λ n → interpret W₁ γ θ M n ≡ blamed Z)
    (+-comm nM nL)
    (interpret-terminal-stable
      {W = W₁} {γ = γ} {θ = θ} {M = M} {n = nM}
      terminal-blame M-eq nL)

interpret-application-from-active-blame :
  ∀ {W γ θ L M nL W₁ F nM W₂ U nA Z} →
  interpret W γ θ L nL ≡ returned W₁ F →
  interpret W₁ γ θ M nM ≡ returned W₂ U →
  applyValue W₂ F U nA ≡ blamed Z →
  interpret W γ θ (L N.· M) (suc (nL + (nM + nA))) ≡ blamed Z
interpret-application-from-active-blame
    {W} {γ} {θ} {L} {M} {nL} {W₁} {F} {nM} {W₂} {U}
    {nA} {Z} L-eq M-eq A-eq =
  trans (application-computation-eq (suc total))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U′ V → chain (interpret U′ γ θ M) (applyValue-cont V))
        {n = total} L-total)
      (trans
        (chain-after-return (interpret W₁ γ θ M)
          (applyValue-cont F) {n = total} M-total)
        A-total))
  where
  total = nL + (nM + nA)
  L-total = interpret-terminal-stable
    {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
    terminal-return L-eq (nM + nA)
  M-total : interpret W₁ γ θ M total ≡ returned W₂ U
  M-total = subst (λ n → interpret W₁ γ θ M n ≡ returned W₂ U)
    (rotate-three nL nM nA)
    (interpret-terminal-stable
      {W = W₁} {γ = γ} {θ = θ} {M = M} {n = nM}
      terminal-return M-eq (nL + nA))
  A-total : applyValue W₂ F U total ≡ blamed Z
  A-total = subst (λ n → applyValue W₂ F U n ≡ blamed Z)
    (move-third nL nM nA)
    (applyValue-terminal-stable
      {W = W₂} {V = F} {U = U} {n = nA}
      terminal-blame A-eq (nL + nM))

interpret-primitive-from-left-blame :
  ∀ {W γ θ L M n Z} →
  interpret W γ θ L n ≡ blamed Z →
  interpret W γ θ (L N.⊕[ addℕ ] M) (suc n) ≡ blamed Z
interpret-primitive-from-left-blame {W} {γ} {θ} {L} {M} {n} L-eq =
  trans (primitive-computation-eq (suc n))
    (sequence-after-blame W (interpret W γ θ L)
      (λ U V → chain (interpret U γ θ M)
        (λ Z Q k → applyPrimitive Z addℕ V Q)) {n = n} L-eq)

interpret-primitive-from-right-blame :
  ∀ {W γ θ L M nL W₁ V nM Z} →
  interpret W γ θ L nL ≡ returned W₁ V →
  interpret W₁ γ θ M nM ≡ blamed Z →
  interpret W γ θ (L N.⊕[ addℕ ] M) (suc (nL + nM)) ≡ blamed Z
interpret-primitive-from-right-blame
    {W} {γ} {θ} {L} {M} {nL} {W₁} {V} {nM} {Z} L-eq M-eq =
  trans (primitive-computation-eq (suc total))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U V′ → chain (interpret U γ θ M)
          (λ Z′ Q k → applyPrimitive Z′ addℕ V′ Q))
        {n = total} L-total)
      (chain-after-blame (interpret W₁ γ θ M)
        (λ Z′ Q k → applyPrimitive Z′ addℕ V Q)
        {n = total} M-total))
  where
  total = nL + nM
  L-total = interpret-terminal-stable
    {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
    terminal-return L-eq nM
  M-total : interpret W₁ γ θ M total ≡ blamed Z
  M-total = subst (λ n → interpret W₁ γ θ M n ≡ blamed Z)
    (+-comm nM nL)
    (interpret-terminal-stable
      {W = W₁} {γ = γ} {θ = θ} {M = M} {n = nM}
      terminal-blame M-eq nL)

interpret-cast-from-operand-blame :
  ∀ {W γ θ M c n Z} →
  interpret W γ θ M n ≡ blamed Z →
  interpret W γ θ (M N.⟨ c ⟩) (suc n) ≡ blamed Z
interpret-cast-from-operand-blame {W} {γ} {θ} {M} {c} {n} M-eq =
  trans (cast-computation-eq (suc n))
    (sequence-after-blame W (interpret W γ θ M)
      (λ Z Q → coerceValue Z θ c Q) {n = n} M-eq)

interpret-cast-from-active-blame :
  ∀ {W γ θ M c nM W₁ V nC Z} →
  interpret W γ θ M nM ≡ returned W₁ V →
  coerceValue W₁ θ c V nC ≡ blamed Z →
  interpret W γ θ (M N.⟨ c ⟩) (suc (nM + nC)) ≡ blamed Z
interpret-cast-from-active-blame
    {W} {γ} {θ} {M} {c} {nM} {W₁} {V} {nC} {Z} M-eq C-eq =
  trans (cast-computation-eq (suc (nM + nC)))
    (trans
      (sequence-after-return W (interpret W γ θ M)
        (λ Z′ Q → coerceValue Z′ θ c Q) {n = nM + nC}
        (interpret-terminal-stable
          {W = W} {γ = γ} {θ = θ} {M = M} {n = nM}
          terminal-return M-eq nC))
      C-total)
  where
  C-total : coerceValue W₁ θ c V (nM + nC) ≡ blamed Z
  C-total = subst (λ n → coerceValue W₁ θ c V n ≡ blamed Z)
    (+-comm nC nM)
    (coerceValue-terminal-stable
      {W = W₁} {θ = θ} {c = c} {V = V} {n = nC}
      terminal-blame C-eq nM)

apply-closure-from-body-blame :
  ∀ {W N γ θ U n Z} →
  interpret W (U ∷ γ) θ N n ≡ blamed Z →
  applyValue W (closure N γ θ) U (suc n) ≡ blamed Z
apply-closure-from-body-blame body-eq = body-eq

apply-proxy-from-first-blame :
  ∀ {W p q θ V U n Z} →
  coerceValue W θ p U n ≡ blamed Z →
  applyValue W (function-proxy p q θ V) U (suc n) ≡ blamed Z
apply-proxy-from-first-blame {W} {p} {q} {θ} {V} {U} {n} P-eq =
  trans (proxy-computation-eq (suc n))
    (sequence-after-blame W (coerceValue W θ p U)
      (λ Z Q → chain (applyValue Z V Q)
        (λ T P k → coerceValue T θ q P k)) {n = n} P-eq)

apply-proxy-from-application-blame :
  ∀ {W p q θ V U nP W₁ U′ nA Z} →
  coerceValue W θ p U nP ≡ returned W₁ U′ →
  applyValue W₁ V U′ nA ≡ blamed Z →
  applyValue W (function-proxy p q θ V) U
    (suc (nP + nA)) ≡ blamed Z
apply-proxy-from-application-blame
    {W} {p} {q} {θ} {V} {U} {nP} {W₁} {U′} {nA} {Z}
    P-eq A-eq =
  trans (proxy-computation-eq (suc total))
    (trans
      (sequence-after-return W (coerceValue W θ p U)
        (λ Z′ Q → chain (applyValue Z′ V Q)
          (λ T P k → coerceValue T θ q P k))
        {n = total} P-total)
      (chain-after-blame (applyValue W₁ V U′)
        (λ T P k → coerceValue T θ q P k)
        {n = total} A-total))
  where
  total = nP + nA
  P-total = coerceValue-terminal-stable
    {W = W} {θ = θ} {c = p} {V = U} {n = nP}
    terminal-return P-eq nA
  A-total : applyValue W₁ V U′ total ≡ blamed Z
  A-total = subst (λ n → applyValue W₁ V U′ n ≡ blamed Z)
    (+-comm nA nP)
    (applyValue-terminal-stable
      {W = W₁} {V = V} {U = U′} {n = nA}
      terminal-blame A-eq nP)

apply-proxy-from-result-blame :
  ∀ {W p q θ V U nP W₁ U′ nA W₂ V′ nQ Z} →
  coerceValue W θ p U nP ≡ returned W₁ U′ →
  applyValue W₁ V U′ nA ≡ returned W₂ V′ →
  coerceValue W₂ θ q V′ nQ ≡ blamed Z →
  applyValue W (function-proxy p q θ V) U
    (suc (nP + (nA + nQ))) ≡ blamed Z
apply-proxy-from-result-blame
    {W} {p} {q} {θ} {V} {U} {nP} {W₁} {U′} {nA} {W₂} {V′}
    {nQ} {Z} P-eq A-eq Q-eq =
  trans (proxy-computation-eq (suc total))
    (trans
      (sequence-after-return W (coerceValue W θ p U)
        (λ Z′ Q → chain (applyValue Z′ V Q)
          (λ T P k → coerceValue T θ q P k))
        {n = total} P-total)
      (trans
        (chain-after-return (applyValue W₁ V U′)
          (λ T P k → coerceValue T θ q P k)
          {n = total} A-total)
        Q-total))
  where
  total = nP + (nA + nQ)
  P-total = coerceValue-terminal-stable
    {W = W} {θ = θ} {c = p} {V = U} {n = nP}
    terminal-return P-eq (nA + nQ)
  A-total : applyValue W₁ V U′ total ≡ returned W₂ V′
  A-total = subst (λ n → applyValue W₁ V U′ n ≡ returned W₂ V′)
    (rotate-three nP nA nQ)
    (applyValue-terminal-stable
      {W = W₁} {V = V} {U = U′} {n = nA}
      terminal-return A-eq (nP + nQ))
  Q-total : coerceValue W₂ θ q V′ total ≡ blamed Z
  Q-total = subst (λ n → coerceValue W₂ θ q V′ n ≡ blamed Z)
    (move-third nP nA nQ)
    (coerceValue-terminal-stable
      {W = W₂} {θ = θ} {c = q} {V = V′} {n = nQ}
      terminal-blame Q-eq (nP + nA))

instantiate-forall-from-inner-blame :
  ∀ {W α c θ V n Z} →
  instantiateValue W α V n ≡ blamed Z →
  instantiateValue W α (forall-proxy c θ V) (suc n) ≡ blamed Z
instantiate-forall-from-inner-blame {W} {α} {c} {θ} {V} {n} I-eq =
  trans (forall-computation-eq (suc n))
    (sequence-after-blame W (instantiateValue W α V)
      (λ Z U → coerceValue Z (seal-name α ∷ θ) c U)
      {n = n} I-eq)

instantiate-forall-from-coercion-blame :
  ∀ {W α c θ V nI W₁ U nC Z} →
  instantiateValue W α V nI ≡ returned W₁ U →
  coerceValue W₁ (seal-name α ∷ θ) c U nC ≡ blamed Z →
  instantiateValue W α (forall-proxy c θ V)
    (suc (nI + nC)) ≡ blamed Z
instantiate-forall-from-coercion-blame
    {W} {α} {c} {θ} {V} {nI} {W₁} {U} {nC} {Z} I-eq C-eq =
  trans (forall-computation-eq (suc (nI + nC)))
    (trans
      (sequence-after-return W (instantiateValue W α V)
        (λ Z′ U′ → coerceValue Z′ (seal-name α ∷ θ) c U′)
        {n = nI + nC}
        (instantiateValue-terminal-stable
          {W = W} {α = α} {V = V} {n = nI}
          terminal-return I-eq nC))
      C-total)
  where
  C-total :
    coerceValue W₁ (seal-name α ∷ θ) c U (nI + nC) ≡ blamed Z
  C-total = subst
    (λ n → coerceValue W₁ (seal-name α ∷ θ) c U n ≡ blamed Z)
    (+-comm nC nI)
    (coerceValue-terminal-stable
      {W = W₁} {θ = seal-name α ∷ θ} {c = c} {V = U} {n = nC}
      terminal-blame C-eq nI)

instantiate-generalized-from-coercion-blame :
  ∀ {W α A c θ V n Z} →
  coerceValue W (seal-name α ∷ θ) c V n ≡ blamed Z →
  instantiateValue W α (generalized A c θ V) (suc n) ≡ blamed Z
instantiate-generalized-from-coercion-blame C-eq = C-eq

coerce-sequence-from-first-blame :
  ∀ {W θ c d V n Z} →
  coerceValue W θ c V n ≡ blamed Z →
  coerceValue W θ (c C.︔ d) V (suc n) ≡ blamed Z
coerce-sequence-from-first-blame {W} {θ} {c} {d} {V} {n} C-eq =
  trans (sequence-coercion-eq (suc n))
    (sequence-after-blame W (coerceValue W θ c V)
      (λ Z U → coerceValue Z θ d U) {n = n} C-eq)

coerce-sequence-from-second-blame :
  ∀ {W θ c d V nC W₁ U nD Z} →
  coerceValue W θ c V nC ≡ returned W₁ U →
  coerceValue W₁ θ d U nD ≡ blamed Z →
  coerceValue W θ (c C.︔ d) V (suc (nC + nD)) ≡ blamed Z
coerce-sequence-from-second-blame
    {W} {θ} {c} {d} {V} {nC} {W₁} {U} {nD} {Z} C-eq D-eq =
  trans (sequence-coercion-eq (suc (nC + nD)))
    (trans
      (sequence-after-return W (coerceValue W θ c V)
        (λ Z′ U′ → coerceValue Z′ θ d U′) {n = nC + nD}
        (coerceValue-terminal-stable
          {W = W} {θ = θ} {c = c} {V = V} {n = nC}
          terminal-return C-eq nD))
      D-total)
  where
  D-total : coerceValue W₁ θ d U (nC + nD) ≡ blamed Z
  D-total = subst (λ n → coerceValue W₁ θ d U n ≡ blamed Z)
    (+-comm nD nC)
    (coerceValue-terminal-stable
      {W = W₁} {θ = θ} {c = d} {V = U} {n = nD}
      terminal-blame D-eq nC)

interpret-nu-from-operand-blame :
  ∀ {W γ θ A L c n Z} →
  interpret W γ θ L n ≡ blamed Z →
  interpret W γ θ (N.ν A L c) (suc n) ≡ blamed Z
interpret-nu-from-operand-blame {W} {γ} {θ} {A} {L} {c} {n} L-eq =
  trans (nu-computation-eq (suc n))
    (sequence-after-blame W (interpret W γ θ L)
      (λ U V → chain
        (instantiateValue (allocate U A θ) (freshSealName U) V)
        (λ Z Q k →
          coerceValue Z (seal-name (freshSealName U) ∷ θ) c Q k))
      {n = n} L-eq)

interpret-nu-from-instantiation-blame :
  ∀ {W γ θ A L c nL W₁ V nI Z} →
  interpret W γ θ L nL ≡ returned W₁ V →
  instantiateValue (allocate W₁ A θ) (freshSealName W₁) V nI ≡
    blamed Z →
  interpret W γ θ (N.ν A L c) (suc (nL + nI)) ≡ blamed Z
interpret-nu-from-instantiation-blame
    {W} {γ} {θ} {A} {L} {c} {nL} {W₁} {V} {nI} {Z}
    L-eq I-eq =
  trans (nu-computation-eq (suc total))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U V′ → chain
          (instantiateValue (allocate U A θ) (freshSealName U) V′)
          (λ Z′ Q k →
            coerceValue Z′ (seal-name (freshSealName U) ∷ θ) c Q k))
        {n = total} L-total)
      (chain-after-blame
        (instantiateValue (allocate W₁ A θ) (freshSealName W₁) V)
        (λ Z′ Q k →
          coerceValue Z′ (seal-name (freshSealName W₁) ∷ θ) c Q k)
        {n = total} I-total))
  where
  total = nL + nI
  L-total = interpret-terminal-stable
    {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
    terminal-return L-eq nI
  I-total :
    instantiateValue (allocate W₁ A θ) (freshSealName W₁) V total ≡
      blamed Z
  I-total = subst
    (λ n → instantiateValue (allocate W₁ A θ)
      (freshSealName W₁) V n ≡ blamed Z)
    (+-comm nI nL)
    (instantiateValue-terminal-stable
      {W = allocate W₁ A θ} {α = freshSealName W₁} {V = V}
      {n = nI} terminal-blame I-eq nL)

interpret-nu-from-coercion-blame :
  ∀ {W γ θ A L c nL W₁ V nI W₂ U nC Z} →
  interpret W γ θ L nL ≡ returned W₁ V →
  instantiateValue (allocate W₁ A θ) (freshSealName W₁) V nI ≡
    returned W₂ U →
  coerceValue W₂ (seal-name (freshSealName W₁) ∷ θ) c U nC ≡
    blamed Z →
  interpret W γ θ (N.ν A L c)
    (suc (nL + (nI + nC))) ≡ blamed Z
interpret-nu-from-coercion-blame
    {W} {γ} {θ} {A} {L} {c} {nL} {W₁} {V} {nI} {W₂} {U}
    {nC} {Z} L-eq I-eq C-eq =
  trans (nu-computation-eq (suc total))
    (trans
      (sequence-after-return W (interpret W γ θ L)
        (λ U′ V′ → chain
          (instantiateValue (allocate U′ A θ) (freshSealName U′) V′)
          (λ Z′ Q k →
            coerceValue Z′ (seal-name (freshSealName U′) ∷ θ) c Q k))
        {n = total} L-total)
      (trans
        (chain-after-return
          (instantiateValue (allocate W₁ A θ) (freshSealName W₁) V)
          (λ Z′ Q k →
            coerceValue Z′ (seal-name (freshSealName W₁) ∷ θ) c Q k)
          {n = total} I-total)
        C-total))
  where
  total = nL + (nI + nC)
  L-total = interpret-terminal-stable
    {W = W} {γ = γ} {θ = θ} {M = L} {n = nL}
    terminal-return L-eq (nI + nC)
  I-total :
    instantiateValue (allocate W₁ A θ) (freshSealName W₁) V total ≡
      returned W₂ U
  I-total = subst
    (λ n → instantiateValue (allocate W₁ A θ)
      (freshSealName W₁) V n ≡ returned W₂ U)
    (rotate-three nL nI nC)
    (instantiateValue-terminal-stable
      {W = allocate W₁ A θ} {α = freshSealName W₁} {V = V}
      {n = nI} terminal-return I-eq (nL + nC))
  C-total :
    coerceValue W₂ (seal-name (freshSealName W₁) ∷ θ) c U total ≡
      blamed Z
  C-total = subst
    (λ n → coerceValue W₂
      (seal-name (freshSealName W₁) ∷ θ) c U n ≡ blamed Z)
    (move-third nL nI nC)
    (coerceValue-terminal-stable
      {W = W₂} {θ = seal-name (freshSealName W₁) ∷ θ}
      {c = c} {V = U} {n = nC}
      terminal-blame C-eq (nL + nI))

coerce-instantiation-from-instantiation-blame :
  ∀ {W θ B c V nI Z} →
  instantiateValue (allocate W ★ θ) (freshSealName W) V nI ≡
    blamed Z →
  coerceValue W θ (C.inst B c) V (suc nI) ≡ blamed Z
coerce-instantiation-from-instantiation-blame
    {W} {θ} {B} {c} {V} {nI} I-eq =
  trans (inst-coercion-eq
    {W = W} {θ = θ} {B = B} {c = c} {V = V} (suc nI))
    (sequence-after-blame W
      (instantiateValue (allocate W ★ θ) (freshSealName W) V)
      (λ Z U →
        coerceValue Z (seal-name (freshSealName W) ∷ θ) c U)
      {n = nI} I-eq)

coerce-instantiation-from-coercion-blame :
  ∀ {W θ B c V nI W₁ U nC Z} →
  instantiateValue (allocate W ★ θ) (freshSealName W) V nI ≡
    returned W₁ U →
  coerceValue W₁ (seal-name (freshSealName W) ∷ θ) c U nC ≡
    blamed Z →
  coerceValue W θ (C.inst B c) V (suc (nI + nC)) ≡ blamed Z
coerce-instantiation-from-coercion-blame
    {W} {θ} {B} {c} {V} {nI} {W₁} {U} {nC} {Z} I-eq C-eq =
  trans (inst-coercion-eq
    {W = W} {θ = θ} {B = B} {c = c} {V = V}
    (suc (nI + nC)))
    (trans
      (sequence-after-return W
        (instantiateValue (allocate W ★ θ) (freshSealName W) V)
        (λ Z′ U′ →
          coerceValue Z′ (seal-name (freshSealName W) ∷ θ) c U′)
        {n = nI + nC}
        (instantiateValue-terminal-stable
          {W = allocate W ★ θ} {α = freshSealName W} {V = V}
          {n = nI} terminal-return I-eq nC))
      C-total)
  where
  C-total :
    coerceValue W₁ (seal-name (freshSealName W) ∷ θ) c U
      (nI + nC) ≡ blamed Z
  C-total = subst
    (λ n → coerceValue W₁ (seal-name (freshSealName W) ∷ θ)
      c U n ≡ blamed Z)
    (+-comm nC nI)
    (coerceValue-terminal-stable
      {W = W₁} {θ = seal-name (freshSealName W) ∷ θ}
      {c = c} {V = U} {n = nC} terminal-blame C-eq nI)
