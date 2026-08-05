module Simulation.Coercion.InterpreterCoercionComponents where

-- File Charter:
--   * Exposes the executable domain and codomain plans retained by a
--     function-proxy coercion.
--   * Keeps paired narrowing and widening components distinct from ordinary
--     compiler casts.
--   * Delegates the static inversion to a reduction-free proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  (Coercion; ModeEnv; _↦_; _∣_∣_⊢_∶_=⇒_)
open import Data.Bool using (true)
open import Data.List using (_∷_)
import Data.Nat
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionWf using
  (ImpCtx; NonVar; _∣_⊢_⊑_⊣_; _↦_; ∀ⁱ_)
open import Interpreter using (TypeEnvironment)
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterSemanticTypingCore
import NuTermImprecision as NTI
open import proof.EndpointCanonicalMLBSimpleQuotient using
  (EndpointRepresentativeAlignment; endpoint-representatives-quotient)
open import proof.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import Types
import proof.InterpreterCoercionComponentsProof as Proof

component-left-applied-typing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c : Coercion} {right : CoercionAction}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) right p q →
  Σ[ μ ∈ ModeEnv ]
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ c ∶ A =⇒ B
component-left-applied-typing =
  Proof.component-left-applied-typing

component-right-applied-typing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {left : CoercionAction} {c′ : Coercion}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    left (apply-coercion c′) p q →
  Σ[ μ′ ∈ ModeEnv ]
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ c′ ∶ A′ =⇒ B′
component-right-applied-typing =
  Proof.component-right-applied-typing

quotient-down-left-typing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {d d′ C C′ D D′ X Y E}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′} →
  OperationalDownCoercionNarrowing
    Φ Δᴸ Δᴿ ρ d d′ pC
    (endpoint-representatives-quotient D⊑E alignment) →
  Σ[ μ ∈ ModeEnv ]
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ d ∶ C =⇒ D
quotient-down-left-typing =
  Proof.quotient-down-left-typing

quotient-down-right-typing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {d d′ C C′ D D′ X Y E}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′} →
  OperationalDownCoercionNarrowing
    Φ Δᴸ Δᴿ ρ d d′ pC
    (endpoint-representatives-quotient D⊑E alignment) →
  Σ[ μ′ ∈ ModeEnv ]
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ d′ ∶ C′ =⇒ D′
quotient-down-right-typing =
  Proof.quotient-down-right-typing

quotient-up-left-typing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {u u′ D D′ A A′ X Y E}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ u u′
    (endpoint-representatives-quotient D⊑E alignment) pA →
  Σ[ μ ∈ ModeEnv ]
    μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ ⊢ u ∶ D =⇒ A
quotient-up-left-typing =
  Proof.quotient-up-left-typing

quotient-up-right-typing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {u u′ D D′ A A′ X Y E}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ u u′
    (endpoint-representatives-quotient D⊑E alignment) pA →
  Σ[ μ′ ∈ ModeEnv ]
    μ′ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ ⊢ u′ ∶ D′ =⇒ A′
quotient-up-right-typing =
  Proof.quotient-up-right-typing

function-coercion-components :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c d c′ d′ : Coercion}
    {A A′ B B′ C C′ D D′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (c ↦ d)) (apply-coercion (c′ ↦ d′))
    (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) (apply-coercion c′) pC pA
  ×
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion d) (apply-coercion d′) pB pD
function-coercion-components =
  Proof.function-coercion-components

left-function-coercion-components :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c d : Coercion}
    {A B C D T₁ T₂ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ T₁ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ T₂ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ T₁ ⊣ Δᴿ}
    {pD : Φ ∣ Δᴸ ⊢ D ⊑ T₂ ⊣ Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (c ↦ d)) skip-coercion
    (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) skip-coercion pC pA
  ×
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion d) skip-coercion pB pD
left-function-coercion-components =
  Proof.left-function-coercion-components

right-function-coercion-components :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c′ d′ : Coercion}
    {S₁ S₂ A′ B′ C′ D′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ S₁ ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ S₂ ⊑ B′ ⊣ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ S₁ ⊑ C′ ⊣ Δᴿ}
    {pD : Φ ∣ Δᴸ ⊢ S₂ ⊑ D′ ⊣ Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion (c′ ↦ d′))
    (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion c′) pC pA
  ×
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion d′) pB pD
right-function-coercion-components =
  Proof.right-function-coercion-components

right-boundary-function-coercion-components :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ : TypeEnvironment}
    {c′ d′ : Coercion}
    {A A′ C′ D′ : Ty} {L₁ L₂ : SemanticType}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C′ ⇒ D′ ⊣ Δᴿ} →
  L₁ ⇒ᵛ L₂ ≡ ⟦ A ⟧[ θ ] →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion (c′ ↦ d′)) p q →
  Σ[ S₁ ∈ Ty ] Σ[ S₂ ∈ Ty ]
  Σ[ A₁′ ∈ Ty ] Σ[ B₁′ ∈ Ty ]
  Σ[ pA ∈ Φ ∣ Δᴸ ⊢ S₁ ⊑ A₁′ ⊣ Δᴿ ]
  Σ[ pB ∈ Φ ∣ Δᴸ ⊢ S₂ ⊑ B₁′ ⊣ Δᴿ ]
  Σ[ pC ∈ Φ ∣ Δᴸ ⊢ S₁ ⊑ C′ ⊣ Δᴿ ]
  Σ[ pD ∈ Φ ∣ Δᴸ ⊢ S₂ ⊑ D′ ⊣ Δᴿ ]
    (L₁ ≡ ⟦ S₁ ⟧[ θ ]) ×
    (L₂ ≡ ⟦ S₂ ⟧[ θ ]) ×
    (A′ ≡ A₁′ ⇒ B₁′) ×
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion c′) pC pA
    ×
    ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
      skip-coercion (apply-coercion d′) pB pD
right-boundary-function-coercion-components =
  Proof.right-boundary-function-coercion-components

paired-forall-coercion-component :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c c′ : Coercion}
    {A A′ B B′ : Ty}
    {p : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ A ⊑ A′ ⊣ Data.Nat.suc Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ B′ ⊣ Data.Nat.suc Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.`∀ c))
    (apply-coercion (Coercions.`∀ c′))
    (∀ⁱ p) (∀ⁱ q) →
  Σ[ ρ′ ∈ NTI.StoreImp
    (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ]
    NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ ×
    ComponentCoercionNarrowing
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ρ′
      (apply-coercion c) (apply-coercion c′) p q
paired-forall-coercion-component =
  Proof.paired-forall-coercion-component

left-forall-coercion-component :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c : Coercion} {A B T : Ty}
    {p : ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
          ImprecisionWf.⇑ᴸᵢ Φ) ∣ Data.Nat.suc Δᴸ
      ⊢ A ⊑ T ⊣ Δᴿ}
    {q : ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
          ImprecisionWf.⇑ᴸᵢ Φ) ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ T ⊣ Δᴿ}
    {nonvar : NonVar A} {occ : occurs Data.Nat.zero A ≡ true}
    {nonvar′ : NonVar B} {occ′ : occurs Data.Nat.zero B ≡ true} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.`∀ c)) skip-coercion
    (ImprecisionWf.ν nonvar occ p)
    (ImprecisionWf.ν nonvar′ occ′ q) →
  Σ[ ρ′ ∈ NTI.StoreImp
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ) (Data.Nat.suc Δᴸ) Δᴿ ]
    NTI.LiftLeftStoreⁱ
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ) ρ ρ′ ×
    ComponentCoercionNarrowing
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ)
      (Data.Nat.suc Δᴸ) Δᴿ ρ′
      (apply-coercion c) skip-coercion p q
left-forall-coercion-component =
  Proof.left-forall-coercion-component

right-forall-coercion-component :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c′ : Coercion}
    {A A′ B B′ : Ty}
    {p : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ A ⊑ A′ ⊣ Data.Nat.suc Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ B′ ⊣ Data.Nat.suc Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion (Coercions.`∀ c′))
    (∀ⁱ p) (∀ⁱ q) →
  Σ[ ρ′ ∈ NTI.StoreImp
    (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ]
    NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ ×
    ComponentCoercionNarrowing
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ρ′
      skip-coercion (apply-coercion c′) p q
right-forall-coercion-component =
  Proof.right-forall-coercion-component

paired-generalized-coercion-component :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c c′ : Coercion}
    {A A′ B B′ C C′ X X′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ B′ ⊣ Data.Nat.suc Δᴿ}
    {pX⇑ : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ ⇑ᵗ X ⊑ ⇑ᵗ X′ ⊣ Data.Nat.suc Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.gen C c))
    (apply-coercion (Coercions.gen C′ c′))
    p (∀ⁱ q) →
  Σ[ ρ′ ∈ NTI.StoreImp
    (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ]
    NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ ×
    ComponentCoercionNarrowing
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)
      (NTI.store-matched Data.Nat.zero (⇑ᵗ X)
        Data.Nat.zero (⇑ᵗ X′) pX⇑ ∷ ρ′)
      (apply-coercion c) (apply-coercion c′)
      (⊑-lift∀ᵢ p) q
paired-generalized-coercion-component =
  Proof.paired-generalized-coercion-component

paired-generalized-type-narrowing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c c′ : Coercion}
    {A A′ B B′ C C′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.gen C c))
    (apply-coercion (Coercions.gen C′ c′)) p q →
  InterpreterTypeNarrowing C C′
paired-generalized-type-narrowing =
  Proof.paired-generalized-type-narrowing

left-generalized-coercion-component :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c : Coercion}
    {A B C T X : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ T ⊣ Δᴿ}
    {q :
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ) ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ T ⊣ Δᴿ}
    {nonvar : NonVar B}
    {occ : occurs Data.Nat.zero B ≡ true}
    {hX : WfTy (Data.Nat.suc Δᴸ) (⇑ᵗ X)} →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.gen C c)) skip-coercion
    p (ImprecisionWf.ν nonvar occ q) →
  Σ[ ρ′ ∈ NTI.StoreImp
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ) (Data.Nat.suc Δᴸ) Δᴿ ]
    NTI.LiftLeftStoreⁱ
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ) ρ ρ′ ×
    ComponentCoercionNarrowing
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ)
      (Data.Nat.suc Δᴸ) Δᴿ
      (NTI.store-left Data.Nat.zero (⇑ᵗ X) hX ∷ ρ′)
      (apply-coercion c) skip-coercion
      (⊑-source-liftνᵢ p) q
left-generalized-coercion-component =
  Proof.left-generalized-coercion-component
