module proof.LR-narrow.CastComposition where

-- File Charter:
--   * Composes an operand computation with related casts of returned values.
--   * Reassembles evaluator return and blame phases through cast frames.
--   * Is parameterized by the returned-value cast theorem to avoid cycles.

open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _≤?_; zero; suc; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
import Consistency as C
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.Application using
  (_++ˢ_; apply-stores-++; apply-terms-++; first-of-two≤;
   drop-left-≤; subtract-phases; return-store-reindex;
   blame-store-reindex; value-index-reindex; paired-returns-reindex;
   value-return-exact)
open import proof.LR-narrow.TypeApplication using
  (imprecise-phase-argument-eq; precise-phase-argument-eq;
   returned-injective)
open import proof.LR-narrow.CastPhases

sum-bound-from-split : ∀ {a b n k : ℕ}
  → a + b ≡ n
  → n ≤ k
  → a + b ≤ k
sum-bound-from-split refl n≤k = n≤k

map-paired-returns : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R S : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    {resultᴵ : E.EvalResult Mᴵ} {resultᴾ : E.EvalResult Mᴾ}
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) {j Vᴵ Vᴾ}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → S W′ W≼W′ j Vᴵ Vᴾ)
  → PairedReturns W R k resultᴵ resultᴾ
  → PairedReturns W S k resultᴵ resultᴾ
map-paired-returns map-related
    (paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ termsᴾ related) =
  paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ termsᴾ
    (map-related W′ W≼W′ related)

map-computations-related : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R S : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) {j Vᴵ Vᴾ}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → S W′ W≼W′ j Vᴵ Vᴾ)
  → ComputationsRelated W R k Mᴵ Mᴾ
  → ComputationsRelated W S k Mᴵ Mᴾ
map-computations-related {W = W} {S = S} {k = k}
    {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} map-related related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forward-blame related
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
          interpretFrom (preciseStore (core W)) m Mᴾ ≡ returned resultᴾ
          × PairedReturns W S (k ∸ n) resultᴵ resultᴾ)
      ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward n≤k result-eq with forward-return related n≤k result-eq
  forward n≤k result-eq | inj₁ (m , resultᴾ , return-eq , paired) =
    inj₁ (m , resultᴾ , return-eq ,
      map-paired-returns map-related paired)
  forward n≤k result-eq | inj₂ blaming = inj₂ blaming

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ ≡ returned resultᴵ
        × PairedReturns W S (k ∸ n) resultᴵ resultᴾ
  backward n≤k result-eq with backward-return related n≤k result-eq
  backward n≤k result-eq | m , resultᴵ , return-eq , paired =
    m , resultᴵ , return-eq , map-paired-returns map-related paired

computations-related-future-compose : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁ Aᴾ Aᴵ}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁)
    (q : impEnv (core W₀) I.⊢ Aᴾ ⊑ Aᴵ)
    {k : ℕ} {Mᴵ : Term Δᴵ₁} {Mᴾ : Term Δᴾ₁}
  → ComputationsRelated W₁
      (FutureValueRelation (liftCenterImprecision W₀≼W₁ q)) k Mᴵ Mᴾ
  → ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → FutureValueRelation q W₂
        (future-trans W₀≼W₁ W₁≼W₂)) k Mᴵ Mᴾ
computations-related-future-compose {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    W₀≼W₁ q =
  map-computations-related (λ W₂ W₁≼W₂ related →
    ClosureProof.value-imprecision-reindex
      (liftCenterImprecision (future-trans W₀≼W₁ W₁≼W₂) q)
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ q))
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴾ)
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴵ) related)

future-trans-assoc : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂ Δᴾ₃ Δᴵ₃ Δᶜ₃}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₃ : World Δᴾ₃ Δᴵ₃ Δᶜ₃}
    (W₀≼W₁ : Future W₀ W₁)
    (W₁≼W₂ : Future W₁ W₂)
    (W₂≼W₃ : Future W₂ W₃)
  → future-trans W₀≼W₁ (future-trans W₁≼W₂ W₂≼W₃) ≡
      future-trans (future-trans W₀≼W₁ W₁≼W₂) W₂≼W₃
future-trans-assoc W₀≼W₁ W₁≼W₂ future-refl = refl
future-trans-assoc W₀≼W₁ W₁≼W₂
    (future-paired W₂≼W₃ related fresh) =
  cong (λ W₀≼W₃ → future-paired W₀≼W₃ related fresh)
    (future-trans-assoc W₀≼W₁ W₁≼W₂ W₂≼W₃)
future-trans-assoc W₀≼W₁ W₁≼W₂
    (future-precise W₂≼W₃ fresh) =
  cong (λ W₀≼W₃ → future-precise W₀≼W₃ fresh)
    (future-trans-assoc W₀≼W₁ W₁≼W₂ W₂≼W₃)

computations-related-post-bind-compose : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾᵇ Δᴵᵇ Δᶜᵇ
     Δᴾ₁ Δᴵ₁ Δᶜ₁ Aᴾ Aᴵ}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {bound : World Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼B : Future W₀ bound)
    (W₀≼W₁ : Future W₀ W₁)
    (B≼W₁ : Future bound W₁)
  → future-trans W₀≼B B≼W₁ ≡ W₀≼W₁
  → (q : impEnv (core W₀) I.⊢ Aᴾ ⊑ Aᴵ)
  → {k : ℕ} {Mᴵ : Term Δᴵ₁} {Mᴾ : Term Δᴾ₁}
  → ComputationsRelated W₁
      (FutureValueRelation (liftCenterImprecision W₀≼W₁ q)) k Mᴵ Mᴾ
  → ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → PostBindValueRelation W₀≼B q W₂
        (future-trans W₀≼W₁ W₁≼W₂)) k Mᴵ Mᴾ
computations-related-post-bind-compose {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    W₀≼B W₀≼W₁ B≼W₁ factor q =
  map-computations-related (λ W₂ W₁≼W₂ related →
    future-trans B≼W₁ W₁≼W₂ ,
    trans (future-trans-assoc W₀≼B B≼W₁ W₁≼W₂)
      (cong (λ W₀≼W₁′ → future-trans W₀≼W₁′ W₁≼W₂) factor) ,
    ClosureProof.value-imprecision-reindex
      (liftCenterImprecision (future-trans W₀≼W₁ W₁≼W₂) q)
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ q))
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴾ)
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴵ) related)

assemble-cast-pair : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᶜ₁ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {S : IndexedValueRelation W₀}
    {Cᴾ Dᴾ : Ty Δᴾ₀} {Cᴵ Dᴵ : Ty Δᴵ₀}
    {μᴾ : C.Env∼ Δᴾ₀} {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ}
    {μᴵ : C.Env∼ Δᴵ₀} {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    {Mᴾ : Term Δᴾ₀} {Mᴵ : Term Δᴵ₀}
    {operandResultᴾ : E.EvalResult Mᴾ}
    {operandResultᴵ : E.EvalResult Mᴵ}
    {callResultᴾ : E.EvalResult
      (E.term operandResultᴾ
        ⟨ E.changes operandResultᴾ ▶ᶜ cᴾ ⟩)}
    {callResultᴵ : E.EvalResult
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)}
    {W₁ : World (E.Δ′ operandResultᴾ)
      (E.Δ′ operandResultᴵ) Δᶜ₁}
    {W₂ : World (E.Δ′ callResultᴾ) (E.Δ′ callResultᴵ) Δᶜ₂}
    {j k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → impreciseStore (core W₁) ≡
      E.changes operandResultᴵ ▶ˢ impreciseStore (core W₀)
  → preciseStore (core W₁) ≡
      E.changes operandResultᴾ ▶ˢ preciseStore (core W₀)
  → (∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₁ M)
  → (∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₁ M)
  → (W₁≼W₂ : Future W₁ W₂)
  → impreciseStore (core W₂) ≡
      E.changes callResultᴵ ▶ˢ impreciseStore (core W₁)
  → preciseStore (core W₂) ≡
      E.changes callResultᴾ ▶ˢ preciseStore (core W₁)
  → (∀ M → E.changes callResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₁≼W₂ M)
  → (∀ M → E.changes callResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₁≼W₂ M)
  → j ≡ k
  → S W₂ (future-trans W₀≼W₁ W₁≼W₂)
      j (E.term callResultᴵ) (E.term callResultᴾ)
  → PairedReturns W₀ S k
      (sequence-cast-result operandResultᴵ callResultᴵ)
      (sequence-cast-result operandResultᴾ callResultᴾ)
assemble-cast-pair {W₀ = W₀}
    {operandResultᴾ = operandResultᴾ}
    {operandResultᴵ = operandResultᴵ}
    {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
    {W₁ = W₁} {W₂ = W₂}
    W₀≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
    W₁≼W₂ callStoreᴵ callStoreᴾ callTermsᴵ callTermsᴾ refl
    call-related =
  paired-returns W₂ W₀≼W₂ imprecise-store-eq precise-store-eq
    imprecise-terms-eq precise-terms-eq call-related
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

  imprecise-store-eq = trans callStoreᴵ
    (trans (cong (λ Σ → E.changes callResultᴵ ▶ˢ Σ) operandStoreᴵ)
      (apply-stores-++ (E.changes operandResultᴵ)
        (E.changes callResultᴵ) (impreciseStore (core W₀))))

  precise-store-eq = trans callStoreᴾ
    (trans (cong (λ Σ → E.changes callResultᴾ ▶ˢ Σ) operandStoreᴾ)
      (apply-stores-++ (E.changes operandResultᴾ)
        (E.changes callResultᴾ) (preciseStore (core W₀))))

  imprecise-result = sequence-cast-result operandResultᴵ callResultᴵ
  precise-result = sequence-cast-result operandResultᴾ callResultᴾ

  imprecise-terms-eq : ∀ M → E.changes imprecise-result ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₂ M
  imprecise-terms-eq M = trans
    (sym (apply-terms-++ (E.changes operandResultᴵ)
      (E.changes callResultᴵ) M))
    (trans
      (cong (λ N → E.changes callResultᴵ ▶ᵀ N)
        (operandTermsᴵ M))
      (trans (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
        (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

  precise-terms-eq : ∀ M → E.changes precise-result ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₂ M
  precise-terms-eq M = trans
    (sym (apply-terms-++ (E.changes operandResultᴾ)
      (E.changes callResultᴾ) M))
    (trans
      (cong (λ N → E.changes callResultᴾ ▶ᵀ N)
        (operandTermsᴾ M))
      (trans (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
        (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

assemble-precise-cast-pair : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {S : IndexedValueRelation W₀}
    {Cᴾ Dᴾ : Ty Δᴾ₀} {μᴾ : C.Env∼ Δᴾ₀}
    {cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ}
    {Mᴾ : Term Δᴾ₀} {Mᴵ : Term Δᴵ₀}
    {operandResultᴾ : E.EvalResult Mᴾ}
    {operandResultᴵ : E.EvalResult Mᴵ}
    {callResultᴾ : E.EvalResult
      (E.term operandResultᴾ
        ⟨ E.changes operandResultᴾ ▶ᶜ cᴾ ⟩)}
    {W₁ : World (E.Δ′ operandResultᴾ)
      (E.Δ′ operandResultᴵ) Δᶜ₁}
    {j k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → impreciseStore (core W₁) ≡
      E.changes operandResultᴵ ▶ˢ impreciseStore (core W₀)
  → preciseStore (core W₁) ≡
      E.changes operandResultᴾ ▶ˢ preciseStore (core W₀)
  → (∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₁ M)
  → (∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₁ M)
  → PairedReturns W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W₀≼W₁ W₁≼W₂)) j
      (E.result _ [] (E.term operandResultᴵ) ↠-refl
        (E.value operandResultᴵ)) callResultᴾ
  → j ≡ k
  → PairedReturns W₀ S k operandResultᴵ
      (sequence-cast-result operandResultᴾ callResultᴾ)
assemble-precise-cast-pair {W₀ = W₀} {operandResultᴾ = operandResultᴾ}
    {operandResultᴵ = operandResultᴵ} {callResultᴾ = callResultᴾ}
    W₀≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
    (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
      callTermsᴵ callTermsᴾ callRelated) refl =
  paired-returns W₂ W₀≼W₂ imprecise-store-eq precise-store-eq
    imprecise-terms-eq precise-terms-eq callRelated
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

  imprecise-store-eq = trans callStoreᴵ operandStoreᴵ

  precise-store-eq = trans callStoreᴾ
    (trans
      (cong (λ Σ → E.changes callResultᴾ ▶ˢ Σ) operandStoreᴾ)
      (apply-stores-++ (E.changes operandResultᴾ)
        (E.changes callResultᴾ) (preciseStore (core W₀))))

  precise-result = sequence-cast-result operandResultᴾ callResultᴾ

  imprecise-terms-eq : ∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₂ M
  imprecise-terms-eq M = trans (operandTermsᴵ M)
    (trans
      (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
      (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))

  precise-terms-eq : ∀ M → E.changes precise-result ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₂ M
  precise-terms-eq M = trans
    (sym (apply-terms-++ (E.changes operandResultᴾ)
      (E.changes callResultᴾ) M))
    (trans
      (cong (λ N → E.changes callResultᴾ ▶ᵀ N) (operandTermsᴾ M))
      (trans
        (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
        (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

assemble-imprecise-cast-pair : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {S : IndexedValueRelation W₀}
    {Cᴵ Dᴵ : Ty Δᴵ₀} {μᴵ : C.Env∼ Δᴵ₀}
    {cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ}
    {Mᴾ : Term Δᴾ₀} {Mᴵ : Term Δᴵ₀}
    {operandResultᴾ : E.EvalResult Mᴾ}
    {operandResultᴵ : E.EvalResult Mᴵ}
    {callResultᴵ : E.EvalResult
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)}
    {W₁ : World (E.Δ′ operandResultᴾ)
      (E.Δ′ operandResultᴵ) Δᶜ₁}
    {j k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → impreciseStore (core W₁) ≡
      E.changes operandResultᴵ ▶ˢ impreciseStore (core W₀)
  → preciseStore (core W₁) ≡
      E.changes operandResultᴾ ▶ˢ preciseStore (core W₀)
  → (∀ M → E.changes operandResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₁ M)
  → (∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₁ M)
  → PairedReturns W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W₀≼W₁ W₁≼W₂)) j
      callResultᴵ
      (E.result _ [] (E.term operandResultᴾ) ↠-refl
        (E.value operandResultᴾ))
  → j ≡ k
  → PairedReturns W₀ S k
      (sequence-cast-result operandResultᴵ callResultᴵ)
      operandResultᴾ
assemble-imprecise-cast-pair {W₀ = W₀}
    {operandResultᴾ = operandResultᴾ}
    {operandResultᴵ = operandResultᴵ} {callResultᴵ = callResultᴵ}
    W₀≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
    (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
      callTermsᴵ callTermsᴾ callRelated) refl =
  paired-returns W₂ W₀≼W₂ imprecise-store-eq precise-store-eq
    imprecise-terms-eq precise-terms-eq callRelated
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

  imprecise-store-eq = trans callStoreᴵ
    (trans
      (cong (λ Σ → E.changes callResultᴵ ▶ˢ Σ) operandStoreᴵ)
      (apply-stores-++ (E.changes operandResultᴵ)
        (E.changes callResultᴵ) (impreciseStore (core W₀))))

  precise-store-eq = trans callStoreᴾ operandStoreᴾ

  imprecise-result = sequence-cast-result operandResultᴵ callResultᴵ

  imprecise-terms-eq : ∀ M → E.changes imprecise-result ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₂ M
  imprecise-terms-eq M = trans
    (sym (apply-terms-++ (E.changes operandResultᴵ)
      (E.changes callResultᴵ) M))
    (trans
      (cong (λ N → E.changes callResultᴵ ▶ᵀ N) (operandTermsᴵ M))
      (trans
        (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
        (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

  precise-terms-eq : ∀ M → E.changes operandResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₂ M
  precise-terms-eq M = trans (operandTermsᴾ M)
    (trans
      (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
      (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))

cast-computations-related : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {R S : IndexedValueRelation W}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
    (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
    (k : ℕ) (Mᴵ : Term Δᴵ) (Mᴾ : Term Δᴾ)
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Eᴾ Fᴾ : Ty Δᴾ′} {Eᴵ Fᴵ : Ty Δᴵ′}
      (W≼W′ : Future W W′)
      (r-sourceᴾ : embedPrecise (core W′) Eᴾ ≡
        liftCenterTy W≼W′ Aᴾ)
      (r-sourceᴵ : embedImprecise (core W′) Eᴵ ≡
        liftCenterTy W≼W′ Aᴵ)
      {νᴾ : C.Env∼ Δᴾ′} (dᴾ : νᴾ C.⊢ Eᴾ ∼ Fᴾ)
      {νᴵ : C.Env∼ Δᴵ′} (dᴵ : νᴵ C.⊢ Eᴵ ∼ Fᴵ)
      (s-targetᴾ : embedPrecise (core W′) Fᴾ ≡
        liftCenterTy W≼W′ Bᴾ)
      (s-targetᴵ : embedImprecise (core W′) Fᴵ ≡
        liftCenterTy W≼W′ Bᴵ)
      {j : ℕ} {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → ComputationsRelated W′
        (λ W″ W′≼W″ → S W″ (future-trans W≼W′ W′≼W″)) j
        (Vᴵ ⟨ dᴵ ⟩) (Vᴾ ⟨ dᴾ ⟩))
  → ComputationsRelated W R k Mᴵ Mᴾ
  → ComputationsRelated W S k
      (Mᴵ ⟨ cᴵ ⟩) (Mᴾ ⟨ cᴾ ⟩)
cast-computations-related {W = W} {S = S}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Cᴾ = Cᴾ} {Dᴾ = Dᴾ}
    {Cᴵ = Cᴵ} {Dᴵ = Dᴵ}
    p sourceᴾ sourceᴵ cᴾ cᴵ q targetᴾ targetᴵ
    k Mᴵ Mᴾ cast-values operand-related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forward-blame-cast
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult (Mᴵ ⟨ cᴵ ⟩)}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n (Mᴵ ⟨ cᴵ ⟩)
        ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult (Mᴾ ⟨ cᴾ ⟩) ]
          interpretFrom (preciseStore (core W)) m (Mᴾ ⟨ cᴾ ⟩)
            ≡ returned resultᴾ
          × PairedReturns W S
              (k ∸ n) resultᴵ resultᴾ)
       ⊎ (Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m (Mᴾ ⟨ cᴾ ⟩))
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      with cast-return-phases
        {Σ = impreciseStore (core W)} {gas = n}
        {M = Mᴵ} {c = cᴵ} {result = resultᴵ} result-eq
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResult operandReturn
          callGas callResult callReturn result-split gas-split
      with forward-return operand-related {n = operandGas}
        {resultᴵ = operandResult} operandGas≤ operandReturn
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k

    operandGas≤ = first-of-two≤
      {a = operandGas} {b = callGas} {k = k} phases≤
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResult operandReturn
          callGas callResult callReturn result-split gas-split
      | inj₂ (preciseOperandGas , preciseOperandBlame)
      with cast-operand-blame-expand
        {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
        {M = Mᴾ} {c = cᴾ} preciseOperandBlame
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResult operandReturn
          callGas callResult callReturn result-split gas-split
      | inj₂ (preciseOperandGas , preciseOperandBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      with forward-return call-related {n = callGas}
        {resultᴵ = callResultᴵ} callGas≤ callReturn-at-W₁
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k

    callGas≤ = drop-left-≤
      {a = operandGas} {b = callGas} {k = k} phases≤

    callReturn-at-W₁ = return-store-reindex
      {gas = callGas} {result = callResultᴵ}
      operandStoreᴵ callReturn

    precise-source-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    precise-target-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Dᴾ) Dᴾ
    imprecise-target-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Dᴵ) Dᴵ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-target-type) (trans (embedPrecise-lift W≼W₁ Dᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-target-type) (trans (embedImprecise-lift W≼W₁ Dᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ operandGas)
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)
      (E.term operandResultᴾ
        ⟨ E.changes operandResultᴾ ▶ᶜ cᴾ ⟩)
    call-related = cast-values
      {Eᴾ = E.changes operandResultᴾ ▶ᵗ Cᴾ}
      {Fᴾ = E.changes operandResultᴾ ▶ᵗ Dᴾ}
      {Eᴵ = E.changes operandResultᴵ ▶ᵗ Cᴵ}
      {Fᴵ = E.changes operandResultᴵ ▶ᵗ Dᴵ}
      W≼W₁
      sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴾ ▶ᶜ cᴾ)
      (E.changes operandResultᴵ ▶ᶜ cᴵ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ operandGas}
      {Vᴵ = E.term operandResultᴵ}
      {Vᴾ = E.term operandResultᴾ}
      operandValueRelated
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      with cast-call-blame-expand
        {Σ = preciseStore (core W)}
        {operandGas = preciseOperandGas} {callGas = preciseCallGas}
        {M = Mᴾ} {c = cᴾ} {operandResult = operandResultᴾ}
        preciseOperandReturn
        (blame-store-reindex {gas = preciseCallGas}
          (sym operandStoreᴾ) preciseCallBlame)
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated)
      with cast-return-expand {Σ = preciseStore (core W)}
        {operandGas = preciseOperandGas} {callGas = preciseCallGas}
        {M = Mᴾ} {c = cᴾ} {operandResult = operandResultᴾ}
        {callResult = callResultᴾ} preciseOperandReturn
        (return-store-reindex {gas = preciseCallGas}
          {result = callResultᴾ}
          (sym operandStoreᴾ) preciseCallReturn)
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated)
      | wholeGas , wholeReturn =
    inj₁ (wholeGas , sequence-cast-result operandResultᴾ callResultᴾ ,
      wholeReturn , paired-returns-reindex result-split refl assembled)
    where
    index-eq = trans (subtract-phases k operandGas callGas)
      (cong (k ∸_) gas-split)

    assembled = assemble-cast-pair
      {S = S} {cᴾ = cᴾ} {cᴵ = cᴵ}
      {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = operandResultᴵ}
      {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
      {j = k ∸ operandGas ∸ callGas} {k = k ∸ n}
      W≼W₁ operandStoreᴵ operandStoreᴾ
      operandTermsᴵ operandTermsᴾ W₁≼W₂ callStoreᴵ callStoreᴾ
      callTermsᴵ callTermsᴾ index-eq callValueRelated

  backward : ∀ {n} {resultᴾ : E.EvalResult (Mᴾ ⟨ cᴾ ⟩)}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n (Mᴾ ⟨ cᴾ ⟩)
        ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult (Mᴵ ⟨ cᴵ ⟩) ]
        interpretFrom (impreciseStore (core W)) m (Mᴵ ⟨ cᴵ ⟩)
          ≡ returned resultᴵ
        × PairedReturns W S
            (k ∸ n) resultᴵ resultᴾ
  backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
      with cast-return-phases {Σ = preciseStore (core W)} {gas = n}
        {M = Mᴾ} {c = cᴾ} {result = resultᴾ} result-eq
  backward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴾ operandReturn
          callGas callResultᴾ callReturn result-split gas-split
      with backward-return operand-related {n = operandGas}
        {resultᴾ = operandResultᴾ} operandGas≤ operandReturn
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k

    operandGas≤ = first-of-two≤
      {a = operandGas} {b = callGas} {k = k} phases≤
  backward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴾ operandReturn
          callGas callResultᴾ callReturn result-split gas-split
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      with backward-return call-related {n = callGas}
        {resultᴾ = callResultᴾ} callGas≤ callReturn-at-W₁
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k

    callGas≤ = drop-left-≤
      {a = operandGas} {b = callGas} {k = k} phases≤
    callReturn-at-W₁ = return-store-reindex
      {gas = callGas} {result = callResultᴾ}
      operandStoreᴾ callReturn

    precise-source-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    precise-target-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Dᴾ) Dᴾ
    imprecise-target-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Dᴵ) Dᴵ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-target-type) (trans (embedPrecise-lift W≼W₁ Dᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-target-type) (trans (embedImprecise-lift W≼W₁ Dᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ operandGas)
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)
      (E.term operandResultᴾ
        ⟨ E.changes operandResultᴾ ▶ᶜ cᴾ ⟩)
    call-related = cast-values
      {Eᴾ = E.changes operandResultᴾ ▶ᵗ Cᴾ}
      {Fᴾ = E.changes operandResultᴾ ▶ᵗ Dᴾ}
      {Eᴵ = E.changes operandResultᴵ ▶ᵗ Cᴵ}
      {Fᴵ = E.changes operandResultᴵ ▶ᵗ Dᴵ}
      W≼W₁
      sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴾ ▶ᶜ cᴾ)
      (E.changes operandResultᴵ ▶ᶜ cᴵ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ operandGas}
      {Vᴵ = E.term operandResultᴵ}
      {Vᴾ = E.term operandResultᴾ}
      operandValueRelated
  backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴾ operandReturn
          callGas callResultᴾ callReturn result-split gas-split
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      | impreciseCallGas , callResultᴵ , impreciseCallReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated
      with cast-return-expand {Σ = impreciseStore (core W)}
        {operandGas = impreciseOperandGas} {callGas = impreciseCallGas}
        {M = Mᴵ} {c = cᴵ} {operandResult = operandResultᴵ}
        {callResult = callResultᴵ} impreciseOperandReturn
        (return-store-reindex {gas = impreciseCallGas}
          {result = callResultᴵ}
          (sym operandStoreᴵ) impreciseCallReturn)
  backward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴾ operandReturn
          callGas callResultᴾ callReturn result-split gas-split
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      | impreciseCallGas , callResultᴵ , impreciseCallReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated
      | wholeGas , wholeReturn =
    wholeGas , sequence-cast-result operandResultᴵ callResultᴵ ,
    wholeReturn , paired-returns-reindex refl result-split assembled
    where
    index-eq = trans (subtract-phases k operandGas callGas)
      (cong (k ∸_) gas-split)

    assembled = assemble-cast-pair
      {S = S} {cᴾ = cᴾ} {cᴵ = cᴵ}
      {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = operandResultᴵ}
      {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
      {j = k ∸ operandGas ∸ callGas} {k = k ∸ n}
      W≼W₁ operandStoreᴵ operandStoreᴾ
      operandTermsᴵ operandTermsᴾ W₁≼W₂ callStoreᴵ callStoreᴾ
      callTermsᴵ callTermsᴾ index-eq callValueRelated

  forward-blame-cast : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n (Mᴵ ⟨ cᴵ ⟩)
    → Σ[ m ∈ ℕ ]
        BlamesFrom (preciseStore (core W)) m (Mᴾ ⟨ cᴾ ⟩)
  forward-blame-cast {n = n} n≤k blaming
      with cast-blame-phases {Σ = impreciseStore (core W)} {gas = n}
        {M = Mᴵ} {c = cᴵ} blaming
  forward-blame-cast {n = n} n≤k blaming
      | cast-operand-phase-blames operandGas operandBlame operandGas≤n
      with forward-blame operand-related {n = operandGas}
        (≤-trans operandGas≤n n≤k) operandBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-operand-phase-blames operandGas operandBlame operandGas≤n
      | preciseOperandGas , preciseOperandBlame
      with cast-operand-blame-expand
        {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
        {M = Mᴾ} {c = cᴾ} preciseOperandBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-operand-phase-blames operandGas operandBlame operandGas≤n
      | preciseOperandGas , preciseOperandBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      with forward-return operand-related {n = operandGas}
        {resultᴵ = operandResultᴵ} operandGas≤ operandReturn
    where
    operandGas≤ = first-of-two≤ (≤-trans phases≤n n≤k)
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₂ (preciseOperandGas , preciseOperandBlame)
      with cast-operand-blame-expand
        {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
        {M = Mᴾ} {c = cᴾ} preciseOperandBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₂ (preciseOperandGas , preciseOperandBlame)
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      with forward-blame call-related {n = callGas}
        callGas≤ callBlame-at-W₁
    where
    phases≤k = ≤-trans phases≤n n≤k
    callGas≤ = drop-left-≤ phases≤k
    callBlame-at-W₁ = blame-store-reindex {gas = callGas}
      operandStoreᴵ callBlame

    precise-source-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    precise-target-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Dᴾ) Dᴾ
    imprecise-target-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Dᴵ) Dᴵ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-target-type) (trans (embedPrecise-lift W≼W₁ Dᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-target-type) (trans (embedImprecise-lift W≼W₁ Dᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ operandGas)
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)
      (E.term operandResultᴾ
        ⟨ E.changes operandResultᴾ ▶ᶜ cᴾ ⟩)
    call-related = cast-values
      {Eᴾ = E.changes operandResultᴾ ▶ᵗ Cᴾ}
      {Fᴾ = E.changes operandResultᴾ ▶ᵗ Dᴾ}
      {Eᴵ = E.changes operandResultᴵ ▶ᵗ Cᴵ}
      {Fᴵ = E.changes operandResultᴵ ▶ᵗ Dᴵ}
      W≼W₁
      sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴾ ▶ᶜ cᴾ)
      (E.changes operandResultᴵ ▶ᶜ cᴵ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ operandGas}
      {Vᴵ = E.term operandResultᴵ}
      {Vᴾ = E.term operandResultᴾ}
      operandValueRelated
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | preciseCallGas , preciseCallBlame
      with cast-call-blame-expand
        {Σ = preciseStore (core W)}
        {operandGas = preciseOperandGas} {callGas = preciseCallGas}
        {M = Mᴾ} {c = cᴾ} {operandResult = operandResultᴾ}
        preciseOperandReturn
        (blame-store-reindex {gas = preciseCallGas}
          (sym operandStoreᴾ) preciseCallBlame)
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | preciseCallGas , preciseCallBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame

precise-cast-computations-related : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {R S : IndexedValueRelation W}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ Dᴾ : Ty Δᴾ} {Cᴵ : Ty Δᴵ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴾ : C.Env∼ Δᴾ} (cᴾ : μᴾ C.⊢ Cᴾ ∼ Dᴾ)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
    (targetᴾ : embedPrecise (core W) Dᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Cᴵ ≡ Bᴵ)
    (k : ℕ) (Mᴵ : Term Δᴵ) (Mᴾ : Term Δᴾ)
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Eᴾ Fᴾ : Ty Δᴾ′} {Eᴵ : Ty Δᴵ′}
      (W≼W′ : Future W W′)
      (r-sourceᴾ : embedPrecise (core W′) Eᴾ ≡
        liftCenterTy W≼W′ Aᴾ)
      (r-sourceᴵ : embedImprecise (core W′) Eᴵ ≡
        liftCenterTy W≼W′ Aᴵ)
      {νᴾ : C.Env∼ Δᴾ′} (dᴾ : νᴾ C.⊢ Eᴾ ∼ Fᴾ)
      (s-targetᴾ : embedPrecise (core W′) Fᴾ ≡
        liftCenterTy W≼W′ Bᴾ)
      (s-targetᴵ : embedImprecise (core W′) Eᴵ ≡
        liftCenterTy W≼W′ Bᴵ)
      {j : ℕ} {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → ComputationsRelated W′
        (λ W″ W′≼W″ → S W″ (future-trans W≼W′ W′≼W″)) j
        Vᴵ (Vᴾ ⟨ dᴾ ⟩))
  → ComputationsRelated W R k Mᴵ Mᴾ
  → ComputationsRelated W S k
      Mᴵ (Mᴾ ⟨ cᴾ ⟩)
precise-cast-computations-related {W = W} {S = S}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Cᴾ = Cᴾ} {Dᴾ = Dᴾ}
    {Cᴵ = Cᴵ} p sourceᴾ sourceᴵ cᴾ q targetᴾ targetᴵ
    k Mᴵ Mᴾ cast-values operand-related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forward-blame-cast
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n Mᴵ
        ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult (Mᴾ ⟨ cᴾ ⟩) ]
          interpretFrom (preciseStore (core W)) m (Mᴾ ⟨ cᴾ ⟩)
            ≡ returned resultᴾ
          × PairedReturns W S
              (k ∸ n) resultᴵ resultᴾ)
       ⊎ (Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m (Mᴾ ⟨ cᴾ ⟩))
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      with forward-return operand-related n≤k result-eq
  forward {n = n} n≤k result-eq
      | inj₂ (preciseOperandGas , preciseOperandBlame)
      with cast-operand-blame-expand
        {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
        {M = Mᴾ} {c = cᴾ} preciseOperandBlame
  forward {n = n} n≤k result-eq
      | inj₂ (preciseOperandGas , preciseOperandBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      | inj₁ (preciseOperandGas , operandResultᴾ ,
          preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      with forward-return call-related z≤n callReturnᴵ
    where
    precise-source-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes resultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    precise-target-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Dᴾ) Dᴾ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-target-type) (trans (embedPrecise-lift W≼W₁ Dᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ n) (E.term resultᴵ)
      (E.term operandResultᴾ
        ⟨ E.changes operandResultᴾ ▶ᶜ cᴾ ⟩)
    call-related = cast-values
      {Eᴾ = E.changes operandResultᴾ ▶ᵗ Cᴾ}
      {Fᴾ = E.changes operandResultᴾ ▶ᵗ Dᴾ}
      {Eᴵ = E.changes resultᴵ ▶ᵗ Cᴵ}
      W≼W₁
      sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴾ ▶ᶜ cᴾ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ n} {Vᴵ = E.term resultᴵ}
      {Vᴾ = E.term operandResultᴾ} operandValueRelated

    callReturnᴵ = value-return-exact
      {Σ = impreciseStore (core W₁)} zero (E.value resultᴵ)
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      | inj₁ (preciseOperandGas , operandResultᴾ ,
          preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      with cast-call-blame-expand
        {Σ = preciseStore (core W)}
        {operandGas = preciseOperandGas} {callGas = preciseCallGas}
        {M = Mᴾ} {c = cᴾ} {operandResult = operandResultᴾ}
        preciseOperandReturn
        (blame-store-reindex {gas = preciseCallGas}
          (sym operandStoreᴾ) preciseCallBlame)
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      | inj₁ (preciseOperandGas , operandResultᴾ ,
          preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      | inj₁ (preciseOperandGas , operandResultᴾ ,
          preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
          callPair)
      with cast-return-expand {Σ = preciseStore (core W)}
        {operandGas = preciseOperandGas} {callGas = preciseCallGas}
        {M = Mᴾ} {c = cᴾ} {operandResult = operandResultᴾ}
        {callResult = callResultᴾ} preciseOperandReturn
        (return-store-reindex {gas = preciseCallGas}
          {result = callResultᴾ}
          (sym operandStoreᴾ) preciseCallReturn)
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      | inj₁ (preciseOperandGas , operandResultᴾ ,
          preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn ,
          callPair)
      | wholeGas , wholeReturn =
    inj₁ (wholeGas , sequence-cast-result operandResultᴾ callResultᴾ ,
      wholeReturn , assembled)
    where
    assembled : PairedReturns W S (k ∸ n)
      resultᴵ (sequence-cast-result operandResultᴾ callResultᴾ)
    assembled = assemble-precise-cast-pair
      {S = S} {cᴾ = cᴾ}
      {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = resultᴵ} {callResultᴾ = callResultᴾ}
      W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
      callPair refl

  backward : ∀ {n} {resultᴾ : E.EvalResult (Mᴾ ⟨ cᴾ ⟩)}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n (Mᴾ ⟨ cᴾ ⟩)
        ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W S
            (k ∸ n) resultᴵ resultᴾ
  backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
      with cast-return-phases {Σ = preciseStore (core W)} {gas = n}
        {M = Mᴾ} {c = cᴾ} {result = resultᴾ} result-eq
  backward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴾ operandReturn
          callGas callResultᴾ callReturn result-split gas-split
      with backward-return operand-related {n = operandGas}
        {resultᴾ = operandResultᴾ} operandGas≤ operandReturn
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k

    operandGas≤ = first-of-two≤
      {a = operandGas} {b = callGas} {k = k} phases≤
  backward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴾ operandReturn
          callGas callResultᴾ callReturn result-split gas-split
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      with backward-return call-related {n = callGas}
        {resultᴾ = callResultᴾ} callGas≤ callReturn-at-W₁
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k

    callGas≤ = drop-left-≤
      {a = operandGas} {b = callGas} {k = k} phases≤
    callReturn-at-W₁ = return-store-reindex
      {gas = callGas} {result = callResultᴾ}
      operandStoreᴾ callReturn

    precise-source-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    precise-target-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Dᴾ) Dᴾ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-target-type) (trans (embedPrecise-lift W≼W₁ Dᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ operandGas) (E.term operandResultᴵ)
      (E.term operandResultᴾ
        ⟨ E.changes operandResultᴾ ▶ᶜ cᴾ ⟩)
    call-related = cast-values
      {Eᴾ = E.changes operandResultᴾ ▶ᵗ Cᴾ}
      {Fᴾ = E.changes operandResultᴾ ▶ᵗ Dᴾ}
      {Eᴵ = E.changes operandResultᴵ ▶ᵗ Cᴵ}
      W≼W₁
      sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴾ ▶ᶜ cᴾ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ operandGas} {Vᴵ = E.term operandResultᴵ}
      {Vᴾ = E.term operandResultᴾ} operandValueRelated
  backward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴾ operandReturn
          callGas callResultᴾ callReturn result-split gas-split
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      | impreciseCallGas , callResultᴵ , impreciseCallReturn , callPair =
    impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
      paired-returns-reindex refl result-split assembled
    where
    exactCallResult = E.result _ [] (E.term operandResultᴵ) ↠-refl
      (E.value operandResultᴵ)

    callResultEq : callResultᴵ ≡ exactCallResult
    callResultEq = returned-injective
      (trans (sym impreciseCallReturn)
        (value-return-exact {Σ = impreciseStore (core W₁)}
          impreciseCallGas (E.value operandResultᴵ)))

    exactCallPair = paired-returns-reindex
      (sym callResultEq) refl callPair

    indexEq = trans (subtract-phases k operandGas callGas)
      (cong (k ∸_) gas-split)

    assembled : PairedReturns W S (k ∸ n)
      operandResultᴵ (sequence-cast-result operandResultᴾ callResultᴾ)
    assembled = assemble-precise-cast-pair
      {S = S} {cᴾ = cᴾ}
      {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = operandResultᴵ} {callResultᴾ = callResultᴾ}
      W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
      exactCallPair indexEq

  forward-blame-cast : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ]
        BlamesFrom (preciseStore (core W)) m (Mᴾ ⟨ cᴾ ⟩)
  forward-blame-cast {n = n} n≤k blaming
      with forward-blame operand-related n≤k blaming
  forward-blame-cast {n = n} n≤k blaming
      | preciseOperandGas , preciseOperandBlame
      with cast-operand-blame-expand
        {Σ = preciseStore (core W)} {operandGas = preciseOperandGas}
        {M = Mᴾ} {c = cᴾ} preciseOperandBlame
  forward-blame-cast {n = n} n≤k blaming
      | preciseOperandGas , preciseOperandBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame

imprecise-cast-computations-related : ∀
    {Δᴾ Δᴵ Δᶜ : TyCtx} {W : World Δᴾ Δᴵ Δᶜ}
    {R S : IndexedValueRelation W}
    {Aᴾ Aᴵ Bᴾ Bᴵ : Ty Δᶜ}
    {Cᴾ : Ty Δᴾ} {Cᴵ Dᴵ : Ty Δᴵ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (sourceᴾ : embedPrecise (core W) Cᴾ ≡ Aᴾ)
    (sourceᴵ : embedImprecise (core W) Cᴵ ≡ Aᴵ)
    {μᴵ : C.Env∼ Δᴵ} (cᴵ : μᴵ C.⊢ Cᴵ ∼ Dᴵ)
    (q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ)
    (targetᴾ : embedPrecise (core W) Cᴾ ≡ Bᴾ)
    (targetᴵ : embedImprecise (core W) Dᴵ ≡ Bᴵ)
    (k : ℕ) (Mᴵ : Term Δᴵ) (Mᴾ : Term Δᴾ)
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′ : TyCtx}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {Eᴾ : Ty Δᴾ′} {Eᴵ Fᴵ : Ty Δᴵ′}
      (W≼W′ : Future W W′)
      (r-sourceᴾ : embedPrecise (core W′) Eᴾ ≡
        liftCenterTy W≼W′ Aᴾ)
      (r-sourceᴵ : embedImprecise (core W′) Eᴵ ≡
        liftCenterTy W≼W′ Aᴵ)
      {νᴵ : C.Env∼ Δᴵ′} (dᴵ : νᴵ C.⊢ Eᴵ ∼ Fᴵ)
      (s-targetᴾ : embedPrecise (core W′) Eᴾ ≡
        liftCenterTy W≼W′ Bᴾ)
      (s-targetᴵ : embedImprecise (core W′) Fᴵ ≡
        liftCenterTy W≼W′ Bᴵ)
      {j : ℕ} {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → R W′ W≼W′ j Vᴵ Vᴾ
    → ComputationsRelated W′
        (λ W″ W′≼W″ → S W″ (future-trans W≼W′ W′≼W″)) j
        (Vᴵ ⟨ dᴵ ⟩) Vᴾ)
  → ComputationsRelated W R k Mᴵ Mᴾ
  → ComputationsRelated W S k (Mᴵ ⟨ cᴵ ⟩) Mᴾ
imprecise-cast-computations-related {W = W} {S = S}
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Dᴵ = Dᴵ}
    p sourceᴾ sourceᴵ cᴵ q targetᴾ targetᴵ
    k Mᴵ Mᴾ cast-values operand-related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forward-blame-cast
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult (Mᴵ ⟨ cᴵ ⟩)}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n (Mᴵ ⟨ cᴵ ⟩)
        ≡ returned resultᴵ
    → ( Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
          interpretFrom (preciseStore (core W)) m Mᴾ
            ≡ returned resultᴾ
          × PairedReturns W S (k ∸ n) resultᴵ resultᴾ)
       ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward {n = n} {resultᴵ = resultᴵ} n≤k result-eq
      with cast-return-phases {Σ = impreciseStore (core W)} {gas = n}
        {M = Mᴵ} {c = cᴵ} {result = resultᴵ} result-eq
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      with forward-return operand-related {n = operandGas}
        {resultᴵ = operandResultᴵ} operandGas≤ operandReturn
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k
    operandGas≤ = first-of-two≤
      {a = operandGas} {b = callGas} {k = k} phases≤
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₂ (preciseOperandGas , preciseOperandBlame) =
    inj₂ (preciseOperandGas , preciseOperandBlame)
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      with forward-return call-related {n = callGas}
        {resultᴵ = callResultᴵ} callGas≤ callReturn-at-W₁
    where
    phases≤ : operandGas + callGas ≤ k
    phases≤ = sum-bound-from-split
      {a = operandGas} {b = callGas} {n = n} {k = k}
      gas-split n≤k
    callGas≤ = drop-left-≤
      {a = operandGas} {b = callGas} {k = k} phases≤

    callReturn-at-W₁ = return-store-reindex {gas = callGas}
      {result = callResultᴵ} operandStoreᴵ callReturn

    precise-source-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    imprecise-target-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Dᴵ) Dᴵ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-target-type) (trans (embedImprecise-lift W≼W₁ Dᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ operandGas)
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)
      (E.term operandResultᴾ)
    call-related = cast-values
      {Eᴾ = E.changes operandResultᴾ ▶ᵗ Cᴾ}
      {Eᴵ = E.changes operandResultᴵ ▶ᵗ Cᴵ}
      {Fᴵ = E.changes operandResultᴵ ▶ᵗ Dᴵ}
      W≼W₁ sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴵ ▶ᶜ cᴵ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ operandGas}
      {Vᴵ = E.term operandResultᴵ}
      {Vᴾ = E.term operandResultᴾ} operandValueRelated
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₂ (preciseCallGas , Δ′ , changes , trace , preciseCallBlame)
      with trans
        (sym (value-return-exact {Σ = preciseStore (core W₁)}
          preciseCallGas (E.value operandResultᴾ))) preciseCallBlame
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₂ (preciseCallGas , Δ′ , changes , trace , preciseCallBlame)
      | ()
  forward {n = n} n≤k result-eq
      | cast-return-phases-record operandGas operandResultᴵ operandReturn
          callGas callResultᴵ callReturn result-split gas-split
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | inj₁ (preciseCallGas , callResultᴾ , preciseCallReturn , callPair) =
    inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
      paired-returns-reindex result-split refl assembled)
    where
    exactCallResult = E.result _ [] (E.term operandResultᴾ) ↠-refl
      (E.value operandResultᴾ)

    callResultEq : callResultᴾ ≡ exactCallResult
    callResultEq = returned-injective
      (trans (sym preciseCallReturn)
        (value-return-exact {Σ = preciseStore (core W₁)}
          preciseCallGas (E.value operandResultᴾ)))

    exactCallPair = paired-returns-reindex refl (sym callResultEq) callPair
    indexEq = trans (subtract-phases k operandGas callGas)
      (cong (k ∸_) gas-split)

    assembled : PairedReturns W S (k ∸ n)
      (sequence-cast-result operandResultᴵ callResultᴵ) operandResultᴾ
    assembled = assemble-imprecise-cast-pair
      {S = S} {cᴵ = cᴵ} {operandResultᴾ = operandResultᴾ}
      {operandResultᴵ = operandResultᴵ} {callResultᴵ = callResultᴵ}
      W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
      exactCallPair indexEq

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n Mᴾ
        ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult (Mᴵ ⟨ cᴵ ⟩) ]
        interpretFrom (impreciseStore (core W)) m (Mᴵ ⟨ cᴵ ⟩)
          ≡ returned resultᴵ
        × PairedReturns W S (k ∸ n) resultᴵ resultᴾ
  backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
      with backward-return operand-related n≤k result-eq
  backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      with backward-return call-related {n = zero} z≤n callReturnᴾ
    where
    precise-source-type = precise-phase-argument-eq
      {χs = E.changes resultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    imprecise-target-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Dᴵ) Dᴵ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-target-type) (trans (embedImprecise-lift W≼W₁ Dᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ n)
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)
      (E.term resultᴾ)
    call-related = cast-values
      {Eᴾ = E.changes resultᴾ ▶ᵗ Cᴾ}
      {Eᴵ = E.changes operandResultᴵ ▶ᵗ Cᴵ}
      {Fᴵ = E.changes operandResultᴵ ▶ᵗ Dᴵ}
      W≼W₁ sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴵ ▶ᶜ cᴵ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ n} {Vᴵ = E.term operandResultᴵ}
      {Vᴾ = E.term resultᴾ} operandValueRelated

    callReturnᴾ = value-return-exact
      {Σ = preciseStore (core W₁)} zero (E.value resultᴾ)
  backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      | impreciseCallGas , callResultᴵ , impreciseCallReturn , callPair
      with cast-return-expand {Σ = impreciseStore (core W)}
        {operandGas = impreciseOperandGas} {callGas = impreciseCallGas}
        {M = Mᴵ} {c = cᴵ} {operandResult = operandResultᴵ}
        {callResult = callResultᴵ} impreciseOperandReturn
        (return-store-reindex {gas = impreciseCallGas}
          {result = callResultᴵ} (sym operandStoreᴵ) impreciseCallReturn)
  backward {n = n} {resultᴾ = resultᴾ} n≤k result-eq
      | impreciseOperandGas , operandResultᴵ , impreciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated
      | impreciseCallGas , callResultᴵ , impreciseCallReturn , callPair
      | wholeGas , wholeReturn =
    wholeGas , sequence-cast-result operandResultᴵ callResultᴵ ,
      wholeReturn , assembled
    where
    assembled : PairedReturns W S (k ∸ n)
      (sequence-cast-result operandResultᴵ callResultᴵ) resultᴾ
    assembled = assemble-imprecise-cast-pair
      {S = S} {cᴵ = cᴵ} {operandResultᴾ = resultᴾ}
      {operandResultᴵ = operandResultᴵ} {callResultᴵ = callResultᴵ}
      W≼W₁ operandStoreᴵ operandStoreᴾ operandTermsᴵ operandTermsᴾ
      callPair refl

  forward-blame-cast : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n (Mᴵ ⟨ cᴵ ⟩)
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
  forward-blame-cast {n = n} n≤k blaming
      with cast-blame-phases {Σ = impreciseStore (core W)} {gas = n}
        {M = Mᴵ} {c = cᴵ} blaming
  forward-blame-cast {n = n} n≤k blaming
      | cast-operand-phase-blames operandGas operandBlame operandGas≤n =
    forward-blame operand-related (≤-trans operandGas≤n n≤k) operandBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      with forward-return operand-related {n = operandGas}
        {resultᴵ = operandResultᴵ} operandGas≤ operandReturn
    where
    operandGas≤ = first-of-two≤
      {a = operandGas} {b = callGas} {k = k}
      (≤-trans phases≤n n≤k)
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₂ (preciseOperandGas , preciseOperandBlame) =
    preciseOperandGas , preciseOperandBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      with forward-blame call-related {n = callGas}
        callGas≤ callBlame-at-W₁
    where
    phases≤k = ≤-trans phases≤n n≤k
    callGas≤ = drop-left-≤
      {a = operandGas} {b = callGas} {k = k} phases≤k
    callBlame-at-W₁ = blame-store-reindex {gas = callGas}
      operandStoreᴵ callBlame

    precise-source-type = precise-phase-argument-eq
      {χs = E.changes operandResultᴾ} W≼W₁
      operandTermsᴾ (⇑ᵗ Cᴾ) Cᴾ
    imprecise-source-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Cᴵ) Cᴵ
    imprecise-target-type = imprecise-phase-argument-eq
      {χs = E.changes operandResultᴵ} W≼W₁
      operandTermsᴵ (⇑ᵗ Dᴵ) Dᴵ

    sourceᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) sourceᴾ))
    sourceᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-source-type) (trans (embedImprecise-lift W≼W₁ Cᴵ)
        (cong (liftCenterTy W≼W₁) sourceᴵ))
    targetᴾ-at-W₁ = trans (cong (embedPrecise (core W₁))
      precise-source-type) (trans (embedPrecise-lift W≼W₁ Cᴾ)
        (cong (liftCenterTy W≼W₁) targetᴾ))
    targetᴵ-at-W₁ = trans (cong (embedImprecise (core W₁))
      imprecise-target-type) (trans (embedImprecise-lift W≼W₁ Dᴵ)
        (cong (liftCenterTy W≼W₁) targetᴵ))

    call-related : ComputationsRelated W₁
      (λ W₂ W₁≼W₂ → S W₂ (future-trans W≼W₁ W₁≼W₂))
      (k ∸ operandGas)
      (E.term operandResultᴵ
        ⟨ E.changes operandResultᴵ ▶ᶜ cᴵ ⟩)
      (E.term operandResultᴾ)
    call-related = cast-values
      {Eᴾ = E.changes operandResultᴾ ▶ᵗ Cᴾ}
      {Eᴵ = E.changes operandResultᴵ ▶ᵗ Cᴵ}
      {Fᴵ = E.changes operandResultᴵ ▶ᵗ Dᴵ}
      W≼W₁ sourceᴾ-at-W₁ sourceᴵ-at-W₁
      (E.changes operandResultᴵ ▶ᶜ cᴵ)
      targetᴾ-at-W₁ targetᴵ-at-W₁
      {j = k ∸ operandGas}
      {Vᴵ = E.term operandResultᴵ}
      {Vᴾ = E.term operandResultᴾ} operandValueRelated
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | preciseCallGas , Δ′ , changes , trace , preciseCallBlame
      with trans
        (sym (value-return-exact {Σ = preciseStore (core W₁)}
          preciseCallGas (E.value operandResultᴾ))) preciseCallBlame
  forward-blame-cast {n = n} n≤k blaming
      | cast-call-phase-blames operandGas operandResultᴵ operandReturn
          callGas callBlame phases≤n
      | inj₁ (preciseOperandGas , operandResultᴾ , preciseOperandReturn ,
          paired-returns W₁ W≼W₁ operandStoreᴵ operandStoreᴾ
            operandTermsᴵ operandTermsᴾ operandValueRelated)
      | preciseCallGas , Δ′ , changes , trace , preciseCallBlame
      | ()
