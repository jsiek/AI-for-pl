module proof.CompileInterpreterNarrowingProof where

-- File Charter:
--   * Proves that refined compilation produces only direct-interpreter source
--     terms.
--   * Combines endpoint image proofs with the reduction-free static compiler
--     monotonicity certificate.
--   * Performs structural recursion only on source typing.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import Compile using
  ( compileᵀ
  ; compileᵀ-value
  ; consistency-cast-plan
  ; dynamic-application-function-consistent
  )
open import CompileTermImprecision using
  (compile-preserves-term-imprecision; ctxImpToNu)
open import Ctx using (CtxWf; ctxWf-∷)
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import GradualTerms
  using ()
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
open import Imprecision using (_⊢_~_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import InterpreterCoercionNarrowing
open import InterpreterTermNarrowingCore
open import InterpreterWorldNarrowing
import NuTerms as N
open import Types
open import proof.CompileInterpreterNarrowingPolymorphism using
  ( compiled-instantiation-interpreter-term
  ; compiled-type-abstraction-interpreter-term
  )
open import proof.ImprecisionProperties using (~-sym)
open import proof.InterpreterTermNarrowingProof using
  ( interpreter-term-no-bullet
  ; interpreter-type-abstraction-value
  )
open import proof.NuTermProperties using (CtxWf-⤊)

compileᵀ-interpreter-term :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  InterpreterTerm (proj₁ (compileᵀ hΓ M⊢))
compileᵀ-interpreter-term hΓ (⊢ᴳ` x∈) =
  variable-term _
compileᵀ-interpreter-term hΓ (⊢ᴳƛ hA M⊢)
    with compileᵀ (ctxWf-∷ hA hΓ) M⊢
       | compileᵀ-interpreter-term (ctxWf-∷ hA hΓ) M⊢
compileᵀ-interpreter-term hΓ (⊢ᴳƛ hA M⊢)
    | N , N⊢ | N-ok =
  closure-term N-ok
compileᵀ-interpreter-term hΓ
    (⊢ᴳ· {ℓ = ℓ} L⊢ M⊢ A~C)
    with compileᵀ hΓ L⊢ | compileᵀ hΓ M⊢
       | consistency-cast-plan ℓ (~-sym A~C)
       | compileᵀ-interpreter-term hΓ L⊢
       | compileᵀ-interpreter-term hΓ M⊢
compileᵀ-interpreter-term hΓ (⊢ᴳ· L⊢ M⊢ A~C)
    | L , L⊢ᵀ | M , M⊢ᵀ | plan | L-ok | M-ok =
  application-term L-ok
    (coercion-application-term
      (coercion-application-term M-ok))
compileᵀ-interpreter-term {Δ = Δ} hΓ
    (⊢ᴳ·★ {ℓ = ℓ} L⊢ M⊢ C~★)
    with compileᵀ hΓ L⊢ | compileᵀ hΓ M⊢
       | consistency-cast-plan {Δ = Δ} ℓ
           dynamic-application-function-consistent
       | consistency-cast-plan {Δ = Δ} ℓ C~★
       | compileᵀ-interpreter-term hΓ L⊢
       | compileᵀ-interpreter-term hΓ M⊢
compileᵀ-interpreter-term {Δ = Δ} hΓ
    (⊢ᴳ·★ L⊢ M⊢ C~★)
    | L , L⊢ᵀ | M , M⊢ᵀ
    | function-plan | argument-plan | L-ok | M-ok =
  application-term
    (coercion-application-term
      (coercion-application-term L-ok))
    (coercion-application-term
      (coercion-application-term M-ok))
compileᵀ-interpreter-term hΓ (⊢ᴳΛ vV V⊢)
    with compileᵀ (CtxWf-⤊ hΓ) V⊢
       | compileᵀ-value (CtxWf-⤊ hΓ) vV V⊢
       | compileᵀ-interpreter-term (CtxWf-⤊ hΓ) V⊢
compileᵀ-interpreter-term hΓ (⊢ᴳΛ vV V⊢)
    | V , V⊢ᵀ | vVᵀ | V-ok =
  compiled-type-abstraction-interpreter-term vVᵀ V-ok
compileᵀ-interpreter-term hΓ (⊢ᴳ• M⊢ hB hA)
    with compileᵀ hΓ M⊢
       | compileᵀ-interpreter-term hΓ M⊢
compileᵀ-interpreter-term hΓ (⊢ᴳ• M⊢ hB hA)
    | M , M⊢ᵀ | M-ok =
  compiled-instantiation-interpreter-term M-ok
compileᵀ-interpreter-term hΓ (⊢ᴳ$ κ) =
  constant-term κ
compileᵀ-interpreter-term hΓ
    (⊢ᴳ⊕ {ℓ = ℓ} L⊢ A~ℕ op M⊢ B~ℕ)
    with compileᵀ hΓ L⊢ | compileᵀ hΓ M⊢
       | consistency-cast-plan ℓ A~ℕ
       | consistency-cast-plan ℓ B~ℕ
       | compileᵀ-interpreter-term hΓ L⊢
       | compileᵀ-interpreter-term hΓ M⊢
compileᵀ-interpreter-term hΓ
    (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L , L⊢ᵀ | M , M⊢ᵀ
    | left-plan | right-plan | L-ok | M-ok =
  primitive-term op
    (coercion-application-term
      (coercion-application-term L-ok))
    (coercion-application-term
      (coercion-application-term M-ok))

compileᵀ-no-runtime-bullet :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  N.No• (proj₁ (compileᵀ hΓ M⊢))
compileᵀ-no-runtime-bullet hΓ M⊢ =
  interpreter-term-no-bullet
    (compileᵀ-interpreter-term hΓ M⊢)

compileᵀ-raw-type-abstraction-value :
  ∀ {Δ Γ M A V} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  proj₁ (compileᵀ hΓ M⊢) ≡ N.Λ V →
  N.Value V
compileᵀ-raw-type-abstraction-value hΓ M⊢ compiled≡Λ =
  interpreter-type-abstraction-value
    (subst InterpreterTerm compiled≡Λ
      (compileᵀ-interpreter-term hΓ M⊢))

open RelatedWorlds

compile-preserves-interpreter-narrowing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {γ : GTI.CtxImp Φ Δᴸ Δᴿ}
    {M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  OpenInterpreterTermNarrowing
    empty-world⊑ Φ Δᴸ Δᴿ [] (ctxImpToNu γ)
    N N′ A B p
compile-preserves-interpreter-narrowing
    srcΓ-wf tgtΓ-wf M⊑M′ =
  open-interpreter-narrowing
    (compileᵀ-interpreter-term srcΓ-wf
      (GTI.gradual-term-imprecision-source-typing M⊑M′))
    (compileᵀ-interpreter-term tgtΓ-wf
      (GTI.gradual-term-imprecision-target-typing M⊑M′))
    (compile-preserves-term-imprecision
      srcΓ-wf tgtΓ-wf M⊑M′)
