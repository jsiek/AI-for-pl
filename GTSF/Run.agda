module Run where

-- File Charter:
--   * Connects source gradual type checking, compilation, and target
--     evaluation.
--   * Exports `run` for fuel-bounded execution of closed gradual programs and
--     `runTyped` for callers that already have source typing.
--   * Packages source typing, compiled target typing, the runtime invariant,
--     and the final value-or-blame `EvalOutcome` in one result record.

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)

open import Types
open import Ctx using (CtxWf; ctxWf-[]; ctxWf-∷)
open import Compile
  using
    ( compile
    ; compile-value
    ; consistency-cast-plan
    ; dynamic-application-function-consistent
    )
open import Eval using (EvalOutcome; eval)
open import GradualTypeCheck using (type-check)
open import proof.ImprecisionProperties using (~-sym)
open import proof.NuTermProperties using (CtxWf-⤊)

open import GradualTerms
  using (GTerm)
  renaming
    ( _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    ; ⊢⊕ to ⊢ᴳ⊕
    )
open import NuTerms
  using
    ( Term
    ; No•
    ; RuntimeOK
    ; no•-`
    ; no•-ƛ
    ; no•-·
    ; no•-Λ
    ; no•-ν
    ; no•-$
    ; no•-⊕
    ; no•-⟨⟩
    ; ok-no
    )
  renaming (_∣_∣_⊢_⦂_ to _∣_∣_⊢ᵀ_⦂_)

compile-no• :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  No• (proj₁ (compile hΓ M⊢))
compile-no• hΓ (⊢ᴳ` x∈) =
  no•-`
compile-no• hΓ (⊢ᴳƛ wfA M⊢)
    with compile (ctxWf-∷ wfA hΓ) M⊢
       | compile-no• (ctxWf-∷ wfA hΓ) M⊢
... | N , N⊢ | noN =
  no•-ƛ noN
compile-no• hΓ (⊢ᴳ· {ℓ = ℓ} L⊢ M⊢ A~A′)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan ℓ (~-sym A~A′)
       | compile-no• hΓ L⊢ | compile-no• hΓ M⊢
... | L′ , L′⊢ | M′ , M′⊢ | plan | noL | noM =
  no•-· noL (no•-⟨⟩ (no•-⟨⟩ noM))
compile-no• {Δ = Δ} hΓ (⊢ᴳ·★ {ℓ = ℓ} L⊢ M⊢ A′~★)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan {Δ = Δ} ℓ
           dynamic-application-function-consistent
       | consistency-cast-plan {Δ = Δ} ℓ A′~★
       | compile-no• hΓ L⊢ | compile-no• hΓ M⊢
... | L′ , L′⊢ | M′ , M′⊢ | fun-plan | arg-plan | noL | noM =
  no•-·
    (no•-⟨⟩ (no•-⟨⟩ noL))
    (no•-⟨⟩ (no•-⟨⟩ noM))
compile-no• hΓ (⊢ᴳΛ {occ = occ} vM M⊢)
    with compile (CtxWf-⤊ hΓ) M⊢
       | compile-value (CtxWf-⤊ hΓ) vM M⊢
       | compile-no• (CtxWf-⤊ hΓ) M⊢
... | N , N⊢ | vN | noN =
  no•-Λ noN
compile-no• hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA)
    with compile hΓ M⊢ | compile-no• hΓ M⊢
... | M′ , M′⊢ | noM =
  no•-ν noM
compile-no• hΓ (⊢ᴳ$ κ) =
  no•-$
compile-no• hΓ (⊢ᴳ⊕ {ℓ = ℓ} L⊢ A~ℕ op M⊢ B~ℕ)
    with compile hΓ L⊢ | compile hΓ M⊢
       | consistency-cast-plan ℓ A~ℕ | consistency-cast-plan ℓ B~ℕ
       | compile-no• hΓ L⊢ | compile-no• hΓ M⊢
... | L′ , L′⊢ | M′ , M′⊢ | planL | planM | noL | noM =
  no•-⊕ (no•-⟨⟩ (no•-⟨⟩ noL)) (no•-⟨⟩ (no•-⟨⟩ noM))

compile-runtime :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  RuntimeOK (proj₁ (compile hΓ M⊢))
compile-runtime hΓ M⊢ = ok-no (compile-no• hΓ M⊢)

compile-closed :
  ∀ {M A} →
  0 ∣ [] ⊢ᴳ M ⦂ A →
  Σ[ N ∈ Term ] RuntimeOK N × (0 ∣ [] ∣ [] ⊢ᵀ N ⦂ A)
compile-closed M⊢ with compile ctxWf-[] M⊢ | compile-runtime ctxWf-[] M⊢
... | N , N⊢ | okN = N , okN , N⊢

------------------------------------------------------------------------
-- Running closed gradual programs
------------------------------------------------------------------------

record RunResult (M : GTerm) : Set₁ where
  constructor ran
  field
    sourceType     : Ty
    sourceTyping   : 0 ∣ [] ⊢ᴳ M ⦂ sourceType
    target         : Term
    targetRuntime  : RuntimeOK target
    targetTyping   : 0 ∣ [] ∣ [] ⊢ᵀ target ⦂ sourceType
    evaluation     : EvalOutcome target

open RunResult public

runTyped :
  ∀ {M A} →
  (gas : ℕ) →
  0 ∣ [] ⊢ᴳ M ⦂ A →
  Maybe (RunResult M)
runTyped gas M⊢ with compile-closed M⊢
... | N , okN , N⊢ with eval gas N
...   | just evalResult = just (ran _ M⊢ N okN N⊢ evalResult)
...   | nothing = nothing

run :
  (gas : ℕ) →
  (M : GTerm) →
  Maybe (RunResult M)
run gas M with type-check 0 [] ctxWf-[] M
... | just (A , M⊢) = runTyped gas M⊢
... | nothing = nothing
