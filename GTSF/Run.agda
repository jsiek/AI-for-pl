module Run where

-- File Charter:
--   * Connects source gradual type checking, compilation, and target evaluation.
--   * Exports `runWithLabel`/`run` for fuel-bounded execution of closed gradual
--     programs and typed variants for callers that already have source typing.
--   * Packages source typing, compiled target typing, the runtime invariant,
--     and the final `EvalResult` in one result record.

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)

open import Types
open import Ctx using (CtxWf; ctxWf-[]; ctxWf-∷)
open import Coercions using (Label)
open import Compile
  using
    ( arrow★-consistent
    ; compile
    ; compile-value
    ; consistency-cast-plan
    )
open import Eval using (EvalResult; eval)
open import GradualTypeCheck using (type-check)
open import NuStore using (StoreWf)
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

------------------------------------------------------------------------
-- Empty runtime store
------------------------------------------------------------------------

empty-store-wf : ∀ {Δ} → StoreWf Δ []
empty-store-wf =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; unique = λ ()
    }

compile-no• :
  ∀ {Δ Γ M A} →
  (ℓ : Label) →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  No• (proj₁ (compile ℓ hΓ M⊢))
compile-no• ℓ hΓ (⊢ᴳ` x∈) =
  no•-`
compile-no• ℓ hΓ (⊢ᴳƛ wfA M⊢)
    with compile ℓ (ctxWf-∷ wfA hΓ) M⊢
       | compile-no• ℓ (ctxWf-∷ wfA hΓ) M⊢
... | N , N⊢ | noN =
  no•-ƛ noN
compile-no• ℓ hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    with compile ℓ hΓ L⊢ | compile ℓ hΓ M⊢
       | consistency-cast-plan ℓ (~-sym A~A′)
       | compile-no• ℓ hΓ L⊢ | compile-no• ℓ hΓ M⊢
... | L′ , L′⊢ | M′ , M′⊢ | plan | noL | noM =
  no•-· noL (no•-⟨⟩ (no•-⟨⟩ noM))
compile-no• ℓ hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    with compile ℓ hΓ L⊢ | compile ℓ hΓ M⊢
       | consistency-cast-plan ℓ (~-sym (arrow★-consistent A′~★))
       | compile-no• ℓ hΓ L⊢ | compile-no• ℓ hΓ M⊢
... | L′ , L′⊢ | M′ , M′⊢ | plan | noL | noM =
  no•-· (no•-⟨⟩ (no•-⟨⟩ noL)) noM
compile-no• ℓ hΓ (⊢ᴳΛ {occ = occ} vM M⊢)
    with compile ℓ (CtxWf-⤊ hΓ) M⊢
       | compile-value ℓ (CtxWf-⤊ hΓ) vM M⊢
       | compile-no• ℓ (CtxWf-⤊ hΓ) M⊢
... | N , N⊢ | vN | noN =
  no•-Λ noN
compile-no• ℓ hΓ (⊢ᴳ• {B = B} {A = A} M⊢ wfB wfA)
    with compile ℓ hΓ M⊢ | compile-no• ℓ hΓ M⊢
... | M′ , M′⊢ | noM =
  no•-ν noM
compile-no• ℓ hΓ (⊢ᴳ$ κ) =
  no•-$
compile-no• ℓ hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    with compile ℓ hΓ L⊢ | compile ℓ hΓ M⊢
       | consistency-cast-plan ℓ A~ℕ | consistency-cast-plan ℓ B~ℕ
       | compile-no• ℓ hΓ L⊢ | compile-no• ℓ hΓ M⊢
... | L′ , L′⊢ | M′ , M′⊢ | planL | planM | noL | noM =
  no•-⊕ (no•-⟨⟩ (no•-⟨⟩ noL)) (no•-⟨⟩ (no•-⟨⟩ noM))

compile-runtime :
  ∀ {Δ Γ M A} →
  (ℓ : Label) →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  RuntimeOK (proj₁ (compile ℓ hΓ M⊢))
compile-runtime ℓ hΓ M⊢ = ok-no (compile-no• ℓ hΓ M⊢)

compile-closed :
  ∀ {M A} →
  (ℓ : Label) →
  0 ∣ [] ⊢ᴳ M ⦂ A →
  Σ[ N ∈ Term ] RuntimeOK N × (0 ∣ [] ∣ [] ⊢ᵀ N ⦂ A)
compile-closed ℓ M⊢ with compile ℓ ctxWf-[] M⊢ | compile-runtime ℓ ctxWf-[] M⊢
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
    evaluation     : EvalResult 0 [] target sourceType

open RunResult public

runTypedWithLabel :
  ∀ {M A} →
  (ℓ : Label) →
  (gas : ℕ) →
  0 ∣ [] ⊢ᴳ M ⦂ A →
  Maybe (RunResult M)
runTypedWithLabel ℓ gas M⊢ with compile-closed ℓ M⊢
... | N , okN , N⊢ with eval gas empty-store-wf okN N⊢
...   | just result = just (ran _ M⊢ N okN N⊢ result)
...   | nothing = nothing

default-label : Label
default-label = zero

runTyped :
  ∀ {M A} →
  (gas : ℕ) →
  0 ∣ [] ⊢ᴳ M ⦂ A →
  Maybe (RunResult M)
runTyped gas M⊢ = runTypedWithLabel default-label gas M⊢

runWithLabel :
  (ℓ : Label) →
  (gas : ℕ) →
  (M : GTerm) →
  Maybe (RunResult M)
runWithLabel ℓ gas M with type-check 0 [] ctxWf-[] M
... | just (A , M⊢) = runTypedWithLabel ℓ gas M⊢
... | nothing = nothing

run :
  (gas : ℕ) →
  (M : GTerm) →
  Maybe (RunResult M)
run gas M = runWithLabel default-label gas M
