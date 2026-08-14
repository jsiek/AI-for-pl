module proof.LR-narrow.Cast where

-- File Charter:
--   * Proves compatibility of the symmetric and one-sided CTI casts.
--   * Factors term evaluation from the shared related-value cast theorem.
--   * Keeps evaluator phase decomposition private.

open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (m∸n≤m)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
import Consistency as C
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (renameᵗ-injective; toRenameᵗ-injective)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitutionProperties using
  (value-imprecision-endpoints)
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return; value-question-complete)
open import proof.LR-narrow.BetaExpansion using (value-step-none)
open import proof.LR-narrow.Application using
  (prepend-result; prepend-return; value-return-exact; value-unique)
open import proof.LR-narrow.Closure using
  (value-imprecision-downward-to)

dynamic-atom-tag-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W (I.X⊑★ mode) Vᴵ Vᴾ
  → TypedEndpoints W I.★⊑★ Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-atom-tag-endpoints {W = W} {Z = Z} {mode = mode}
    {Gᴾ = Gᴾ} gᴾ ground-center Gᴾ∼★
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} endpoints =
  typed-endpoints ★ ★ refl refl
    (imprecise-value endpoints) precise-tag-value
    Vᴵ⊢★ precise-tag-typed
  where
  precise-type-eq : preciseType endpoints ≡ Gᴾ
  precise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (trans (preciseEmbedded endpoints) (sym ground-center))

  imprecise-type-eq : impreciseType endpoints ≡ ★
  imprecise-type-eq = renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (impreciseEmbedded endpoints)

  Vᴾ⊢Gᴾ = subst≡
    (λ A → ⟨ _ , preciseStore (core W) , [] ⟩ ⊢ Vᴾ ⦂ A)
    precise-type-eq (precise-typed endpoints)

  Vᴵ⊢★ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ Vᴵ ⦂ A)
    imprecise-type-eq (imprecise-typed endpoints)

  precise-tag-value = precise-value endpoints 《
    inj ⦃ Gᵍ = gᴾ ⦄ ⦃ G∼★ = Gᴾ∼★ ⦄
      ⦃ Gns = C.ground-nonstar gᴾ ⦄ 》

  precise-tag-typed = ⊢⟨⟩ Vᴾ⊢Gᴾ (groundInjection gᴾ Gᴾ∼★)


dynamic-atom-tag-value : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) (suc k) Vᴵ Vᴾ
  → ValueImprecision W I.★⊑★ (suc k) Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-atom-tag-value {W = W} {Z = Z} {mode = mode}
    gᴾ ground-center Gᴾ∼★ (endpoints , related) =
  dynamic-atom-tag-endpoints gᴾ ground-center Gᴾ∼★ endpoints ,
  inj₂ atom-tag
  where

  atom-tag = dynamic-atom-tag mode gᴾ ground-center Gᴾ∼★
    (dynamic-atom-downward (semanticEntry W Z) mode related)

dynamic-atom-tag-value-at : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (j : ℕ) {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) j Vᴵ Vᴾ
  → ValueImprecision W I.★⊑★ j Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
dynamic-atom-tag-value-at zero gᴾ ground-center Gᴾ∼★ endpoints =
  dynamic-atom-tag-endpoints gᴾ ground-center Gᴾ∼★ endpoints
dynamic-atom-tag-value-at (suc j) gᴾ ground-center Gᴾ∼★ related =
  dynamic-atom-tag-value gᴾ ground-center Gᴾ∼★ related

identity-cast-redex-question : ∀ {Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.cast-redex? V (C.id {μ = μ} a) ≡
        just (E.step-result keep V (pure-step (β-id vV′)))
identity-cast-redex-question (ƛ N) = (ƛ N) , refl
identity-cast-redex-question (Λ vV)
    with value-question-complete (Λ vV)
identity-cast-redex-question (Λ vV) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
identity-cast-redex-question ($ κ) = ($ κ) , refl
identity-cast-redex-question (vV 《 inert 》)
    with value-question-complete (vV 《 inert 》)
identity-cast-redex-question (vV 《 inert 》) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
identity-cast-redex-question (vV ↑ reveal)
    with value-question-complete (vV ↑ reveal)
identity-cast-redex-question (vV ↑ reveal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
identity-cast-redex-question (vV ↓ conceal)
    with value-question-complete (vV ↓ conceal)
identity-cast-redex-question (vV ↓ conceal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl

identity-cast-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ (V ⟨ C.id {μ = μ} a ⟩) ≡
        just (E.step-result keep V (pure-step (β-id vV′)))
identity-cast-step-question {Σ = Σ} {V = V} vV
    with E.step? Σ V | value-step-none {Σ = Σ} vV
       | identity-cast-redex-question vV
identity-cast-step-question vV
    | nothing | step-eq | vV′ , redex-eq = vV′ , redex-eq
identity-cast-step-question vV
    | just step | () | redex-complete

identity-cast-return-exact : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (gas : ℕ)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      interpretFrom Σ (suc gas) (V ⟨ C.id {μ = μ} a ⟩) ≡
        returned (E.result Δ (keep ∷ []) V
          (↠-step (pure-step (β-id vV′)) ↠-refl) vV′)
identity-cast-return-exact {Σ = Σ} gas vV
    with identity-cast-step-question {Σ = Σ} vV
identity-cast-return-exact {Σ = Σ} gas vV | vV′ , step-eq =
  vV′ , prepend-return {Σ = Σ} step-eq
    (value-return-exact {Σ = Σ} gas vV′)

identity-cast-zero-timed : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ} {μ : C.Env∼ Δ} {A : Ty Δ} {a : Atom A}
  → (vV : Value V)
  → interpretFrom Σ zero (V ⟨ C.id {μ = μ} a ⟩) ≡ timed
identity-cast-zero-timed vV with value-question-complete vV
identity-cast-zero-timed vV | vV′ , value-eq
    rewrite value-eq = refl

dynamic-atom-endpoints : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → TypedEndpoints W (I.X⊑★ mode) Vᴵ Vᴾ
dynamic-atom-endpoints {k = zero} endpoints = endpoints
dynamic-atom-endpoints {k = suc k} (endpoints , behavior) = endpoints

related-imprecise-identity : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴵ : C.Env∼ Δᴵ} {aᴵ : Atom Bᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) Vᴾ
related-imprecise-identity {W = W} {p = p} {k = k}
    {μᴵ = μᴵ} {aᴵ = aᴵ} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-impossible
  }
  where
  endpoints = value-imprecision-endpoints related
  vVᴵ = imprecise-value endpoints
  vVᴾ = precise-value endpoints

  relation-after : ∀ n → FutureValueRelation p W future-refl
      (k ∸ n) Vᴵ Vᴾ
  relation-after n =
    value-imprecision-downward-to (m∸n≤m k n) related

  forward : ∀ {n} {resultᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Vᴾ ]
          interpretFrom (preciseStore (core W)) m Vᴾ
            ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ)
  forward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  forward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  forward {n = zero} n≤k result-eq | zero-eq | ()
  forward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
       | value-return-exact {Σ = preciseStore (core W)} zero vVᴾ
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | precise-return
      with trans (sym imprecise-return) result-eq
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | precise-return | refl =
    inj₁ (zero , _ , precise-return ,
      paired-returns W future-refl refl refl
        (λ M → refl) (λ M → refl) (relation-after (suc n)))

  backward : ∀ {n} {resultᴾ}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n Vᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ]
        interpretFrom (impreciseStore (core W)) m
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = n} n≤k result-eq
      with value-return-exact {Σ = preciseStore (core W)} n vVᴾ
       | identity-cast-return-exact
          {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ}
          zero vVᴵ
  backward {n = n} n≤k result-eq
      | precise-return | vVᴵ′ , imprecise-return
      with trans (sym precise-return) result-eq
  backward {n = n} n≤k result-eq
      | precise-return | vVᴵ′ , imprecise-return | refl =
    suc zero , _ , imprecise-return ,
    paired-returns W future-refl refl refl
      (λ M → refl) (λ M → refl) (relation-after n)

  blame-impossible : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩)
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq
      with trans (sym zero-eq) blame-eq
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq | ()
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return
      with trans (sym imprecise-return) blame-eq
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return | ()

related-precise-identity : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴾ : C.Env∼ Δᴾ} {aᴾ : Atom Bᴾ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k Vᴵ
      (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
related-precise-identity {W = W} {p = p} {k = k}
    {μᴾ = μᴾ} {aᴾ = aᴾ} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-impossible
  }
  where
  endpoints = value-imprecision-endpoints related
  vVᴵ = imprecise-value endpoints
  vVᴾ = precise-value endpoints

  relation-after : ∀ n → FutureValueRelation p W future-refl
      (k ∸ n) Vᴵ Vᴾ
  relation-after n =
    value-imprecision-downward-to (m∸n≤m k n) related

  forward : ∀ {n} {resultᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n Vᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ]
          interpretFrom (preciseStore (core W)) m
            (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩))
  forward {n = n} n≤k result-eq
      with value-return-exact {Σ = impreciseStore (core W)} n vVᴵ
       | identity-cast-return-exact
          {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} zero vVᴾ
  forward {n = n} n≤k result-eq
      | imprecise-return | vVᴾ′ , precise-return
      with trans (sym imprecise-return) result-eq
  forward {n = n} n≤k result-eq
      | imprecise-return | vVᴾ′ , precise-return | refl =
    inj₁ (suc zero , _ , precise-return ,
      paired-returns W future-refl refl refl
        (λ M → refl) (λ M → refl) (relation-after n))

  backward : ∀ {n} {resultᴾ}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Vᴵ ]
        interpretFrom (impreciseStore (core W)) m Vᴵ
          ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} vVᴾ
  backward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  backward {n = zero} n≤k result-eq | zero-eq | ()
  backward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} n vVᴾ
       | value-return-exact {Σ = impreciseStore (core W)} zero vVᴵ
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | imprecise-return
      with trans (sym precise-return) result-eq
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | imprecise-return | refl =
    zero , _ , imprecise-return ,
    paired-returns W future-refl refl refl
      (λ M → refl) (λ M → refl) (relation-after (suc n))

  blame-impossible : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n Vᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , blame-eq)
      with value-return-exact {Σ = impreciseStore (core W)} n vVᴵ
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , blame-eq) | imprecise-return
      with trans (sym imprecise-return) blame-eq
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , blame-eq) | imprecise-return | ()

related-identities : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {μᴾ : C.Env∼ Δᴾ} {aᴾ : Atom Bᴾ}
    {μᴵ : C.Env∼ Δᴵ} {aᴵ : Atom Bᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩)
      (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
related-identities {W = W} {p = p} {k = k}
    {μᴾ = μᴾ} {aᴾ = aᴾ} {μᴵ = μᴵ} {aᴵ = aᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-impossible
  }
  where
  endpoints = value-imprecision-endpoints related
  vVᴵ = imprecise-value endpoints
  vVᴾ = precise-value endpoints

  relation-after : ∀ n → FutureValueRelation p W future-refl
      (k ∸ n) Vᴵ Vᴾ
  relation-after n =
    value-imprecision-downward-to (m∸n≤m k n) related

  forward : ∀ {n} {resultᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ]
          interpretFrom (preciseStore (core W)) m
            (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
          (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩))
  forward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  forward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  forward {n = zero} n≤k result-eq | zero-eq | ()
  forward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
       | identity-cast-return-exact
          {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} zero vVᴾ
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | vVᴾ′ , precise-return
      with trans (sym imprecise-return) result-eq
  forward {n = suc n} n≤k result-eq
      | vVᴵ′ , imprecise-return | vVᴾ′ , precise-return | refl =
    inj₁ (suc zero , _ , precise-return ,
      paired-returns W future-refl refl refl
        (λ M → refl) (λ M → refl) (relation-after (suc n)))

  backward : ∀ {n} {resultᴾ}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩) ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ]
        interpretFrom (impreciseStore (core W)) m
          (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩) ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = zero} n≤k result-eq
      with identity-cast-zero-timed
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} vVᴾ
  backward {n = zero} n≤k result-eq | zero-eq
      with trans (sym zero-eq) result-eq
  backward {n = zero} n≤k result-eq | zero-eq | ()
  backward {n = suc n} n≤k result-eq
      with identity-cast-return-exact
        {Σ = preciseStore (core W)} {μ = μᴾ} {a = aᴾ} n vVᴾ
       | identity-cast-return-exact
          {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} zero vVᴵ
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | vVᴵ′ , imprecise-return
      with trans (sym precise-return) result-eq
  backward {n = suc n} n≤k result-eq
      | vVᴾ′ , precise-return | vVᴵ′ , imprecise-return | refl =
    suc zero , _ , imprecise-return ,
    paired-returns W future-refl refl refl
      (λ M → refl) (λ M → refl) (relation-after (suc n))

  blame-impossible : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n
        (Vᴵ ⟨ C.id {μ = μᴵ} aᴵ ⟩)
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
        (Vᴾ ⟨ C.id {μ = μᴾ} aᴾ ⟩)
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-zero-timed
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} vVᴵ
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq
      with trans (sym zero-eq) blame-eq
  blame-impossible {n = zero} n≤k
      (Δ′ , changes , trace , blame-eq) | zero-eq | ()
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      with identity-cast-return-exact
        {Σ = impreciseStore (core W)} {μ = μᴵ} {a = aᴵ} n vVᴵ
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return
      with trans (sym imprecise-return) blame-eq
  blame-impossible {n = suc n} n≤k
      (Δ′ , changes , trace , blame-eq)
      | vVᴵ′ , imprecise-return | ()

related-dynamic-tag-left : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation I.★⊑★) k Vᴵ
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
related-dynamic-tag-left {W = W} {k = k}
    gᴾ ground-center Gᴾ∼★ related =
  related-values-return (imprecise-value endpoints)
    (precise-value output-endpoints) at-every-index
  where
  endpoints = dynamic-atom-endpoints related

  output-endpoints =
    dynamic-atom-tag-endpoints gᴾ ground-center Gᴾ∼★ endpoints

  at-every-index : ∀ j → j ≤ k
    → FutureValueRelation I.★⊑★ W future-refl j _ _
  at-every-index j j≤k = dynamic-atom-tag-value-at j gᴾ
    ground-center Gᴾ∼★ (value-imprecision-downward-to j≤k related)

related-dynamic-id★-tag : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ} {Z : TyVar Δᶜ}
    {mode : impEnv (core W) Z ≡ I.X⊑★}
    {Gᴾ : Ty Δᴾ} (gᴾ : Ground Gᴾ)
    (ground-center : embedPrecise (core W) Gᴾ ≡ ＇ Z)
    {μᴾ : C.Env∼ Δᴾ} (Gᴾ∼★ : μᴾ C.⊢ Gᴾ ∼★)
    {μᴵ : C.Env∼ Δᴵ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.X⊑★ mode) k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation I.★⊑★) k
      (Vᴵ ⟨ C.id {μ = μᴵ} ★ ⟩)
      (Vᴾ ⟨ groundInjection gᴾ Gᴾ∼★ ⟩)
related-dynamic-id★-tag {k = k} gᴾ ground-center Gᴾ∼★ related =
  related-imprecise-identity
    (dynamic-atom-tag-value-at k gᴾ ground-center Gᴾ∼★ related)
