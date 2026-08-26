module LR-narrow.Context.Variable where

-- File Charter:
--   * Proves the context lemma for the variable term-imprecision rule.
--   * Uses one related-environment lookup and immediate interpreter returns.
--   * Uses no provisional dynamic or universal LR clause.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (m∸n≤m)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using
  ( Environment
  ; Value
  ; blamed
  ; interpret
  ; lookup
  ; returned
  )
  renaming (World to RuntimeWorld)
open import LR-narrow.Context.KripkeRefl
open import LR-narrow.Context.RelatedEnvironmentLookup
open import LR-narrow.Context.RelatedEnvironments
open import LR-narrow.Context.TermRelation
open import LR-narrow.LogicalRelation
open import LR-narrow.World
open import NuTerms using (`_)
open import proof.NuCore.Relations.NuImprecisionTermContextDef
  using (CtxImp; ctx-imp)
open import Types using (TyCtx; _∋_⦂_)

private
  variable-return : ∀ {W γ θ x V n}
    → lookup γ x ≡ just V
    → interpret W γ θ (` x) (suc n) ≡ returned W V
  variable-return lookup-eq rewrite lookup-eq = refl

  variable-forward : ∀
      {Φ} {Δᴸ Δᴿ : TyCtx} {w : LR-narrow.World.World}
      {I : Interpretation {Φ} {Δᴸ} {Δᴿ} w} {k : ℕ}
      {γ γ′ : Environment} {x n U Q V V′ A A′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    → lookup γ x ≡ just V
    → lookup γ′ x ≡ just V′
    → (∀ j → j ≤ k → ValueNarrowing p I j V V′)
    → n ≤ k
    → interpret (left-world w) γ (left-types I) (` x) n
        ≡ returned U Q
    →
      (Σ[ m ∈ ℕ ]
       Σ[ U′ ∈ RuntimeWorld ]
       Σ[ Q′ ∈ Value ]
       Σ[ future ∈ LR-narrow.World.World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ U) ×
         (right-world future ≡ U′) ×
         (interpret (right-world w) γ′ (right-types I) (` x) m
           ≡ returned U′ Q′) ×
         ValueNarrowing p futureᵢ (k ∸ n) Q Q′)
      ⊎
      (Σ[ m ∈ ℕ ]
       Σ[ U′ ∈ RuntimeWorld ]
       Σ[ future ∈ LR-narrow.World.World ]
       Σ[ futureᵢ ∈ Interpretation future ]
         (futureᵢ ⊒ⁱ I) ×
         (left-world future ≡ U) ×
         (right-world future ≡ U′) ×
         (interpret (right-world w) γ′ (right-types I) (` x) m
           ≡ blamed U′))
  variable-forward {n = zero} left-eq right-eq related n≤k ()
  variable-forward {w = w} {I = I} {k = k} {γ = γ} {γ′ = γ′}
      {x = x} {n = suc n} {V = V} {V′ = V′}
      left-eq right-eq related n≤k result-eq
      with trans
        (sym (variable-return
          {W = left-world w} {γ = γ} {θ = left-types I}
          {x = x} {V = V} {n = n} left-eq))
        result-eq
  variable-forward {w = w} {I = I} {k = k} {γ = γ} {γ′ = γ′}
      {x = x} {n = suc n} {V = V} {V′ = V′}
      left-eq right-eq related n≤k result-eq
      | refl =
    inj₁
      (suc n , right-world w , _ , w , I ,
       interpretation-⊒ⁱ-refl I , refl , refl ,
       variable-return
         {W = right-world w} {γ = γ′} {θ = right-types I}
         {x = x} {V = V′} {n = n} right-eq ,
       related (k ∸ suc n) (m∸n≤m k (suc n)))

  variable-backward : ∀
      {Φ} {Δᴸ Δᴿ : TyCtx} {w : LR-narrow.World.World}
      {I : Interpretation {Φ} {Δᴸ} {Δᴿ} w} {k : ℕ}
      {γ γ′ : Environment} {x n U′ Q′ V V′ A A′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    → lookup γ x ≡ just V
    → lookup γ′ x ≡ just V′
    → (∀ j → j ≤ k → ValueNarrowing p I j V V′)
    → n ≤ k
    → interpret (right-world w) γ′ (right-types I) (` x) n
        ≡ returned U′ Q′
    → Σ[ m ∈ ℕ ]
      Σ[ U ∈ RuntimeWorld ]
      Σ[ Q ∈ Value ]
      Σ[ future ∈ LR-narrow.World.World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ U) ×
        (right-world future ≡ U′) ×
        (interpret (left-world w) γ (left-types I) (` x) m
          ≡ returned U Q) ×
        ValueNarrowing p futureᵢ (k ∸ n) Q Q′
  variable-backward {n = zero} left-eq right-eq related n≤k ()
  variable-backward {w = w} {I = I} {k = k} {γ = γ} {γ′ = γ′}
      {x = x} {n = suc n} {V = V} {V′ = V′}
      left-eq right-eq related n≤k result-eq
      with trans
        (sym (variable-return
          {W = right-world w} {γ = γ′} {θ = right-types I} {x = x}
          {V = V′} {n = n} right-eq))
        result-eq
  variable-backward {w = w} {I = I} {k = k} {γ = γ} {γ′ = γ′}
      {x = x} {n = suc n} {V = V} {V′ = V′}
      left-eq right-eq related n≤k result-eq
      | refl =
    suc n , left-world w , _ , w , I ,
    interpretation-⊒ⁱ-refl I , refl , refl ,
    variable-return
      {W = left-world w} {γ = γ} {θ = left-types I}
      {x = x} {V = V} {n = n} left-eq ,
    related (k ∸ suc n) (m∸n≤m k (suc n))

  variable-forward-blame : ∀
      {Φ} {Δᴸ Δᴿ : TyCtx} {w : LR-narrow.World.World}
      {I : Interpretation {Φ} {Δᴸ} {Δᴿ} w} {k : ℕ}
      {γ γ′ : Environment} {x n U V V′ A A′}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    → lookup γ x ≡ just V
    → lookup γ′ x ≡ just V′
    → (∀ j → j ≤ k → ValueNarrowing p I j V V′)
    → n ≤ k
    → interpret (left-world w) γ (left-types I) (` x) n
        ≡ blamed U
    → Σ[ m ∈ ℕ ]
      Σ[ U′ ∈ RuntimeWorld ]
      Σ[ future ∈ LR-narrow.World.World ]
      Σ[ futureᵢ ∈ Interpretation future ]
        (futureᵢ ⊒ⁱ I) ×
        (left-world future ≡ U) ×
        (right-world future ≡ U′) ×
        (interpret (right-world w) γ′ (right-types I) (` x) m
          ≡ blamed U′)
  variable-forward-blame {n = zero}
      left-eq right-eq related n≤k ()
  variable-forward-blame {w = w} {I = I} {γ = γ}
      {x = x} {n = suc n} {V = V}
      left-eq right-eq related n≤k result-eq
      with trans
        (sym (variable-return
          {W = left-world w} {γ = γ} {θ = left-types I} {x = x}
          {V = V} {n = n} left-eq))
        result-eq
  variable-forward-blame {w = w} {I = I} {γ = γ}
      {x = x} {n = suc n} {V = V}
      left-eq right-eq related n≤k result-eq | ()

variable-context : ∀
    {Φ} {Δᴸ Δᴿ : TyCtx} {w : LR-narrow.World.World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} w} {k : ℕ}
    {Γ : CtxImp Φ Δᴸ Δᴿ} {γ γ′ : Environment}
    {x A A′ p}
  → Γ ∋ x ⦂ ctx-imp A A′ p
  → RelatedEnvironments I k Γ γ γ′
  → TermRelation p I k γ γ′ (` x) (` x)
variable-context x∈ relatedγ
    with related-environment-lookup x∈ relatedγ
variable-context x∈ relatedγ
    | V , V′ , left-eq , right-eq , related = record
  { forward-return = variable-forward left-eq right-eq related
  ; backward-return = variable-backward left-eq right-eq related
  ; forward-blame = variable-forward-blame left-eq right-eq related
  }
