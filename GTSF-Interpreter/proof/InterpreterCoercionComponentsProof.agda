module proof.InterpreterCoercionComponentsProof where

-- File Charter:
--   * Inverts function-shaped operational and component coercion plans.
--   * Repackages contravariant domains and covariant codomains exactly once.
--   * Uses only coercion grammar, typing, and static narrowing evidence.

open import Coercions using
  ( Coercion
  ; ModeEnv
  ; cast-all
  ; cast-fun
  ; extᵈ
  ; genᵈ
  ; id-onlyᵈ
  ; _∣_∣_⊢_∶_=⇒_
  )
open import Conversion using
  ( conceal-fun
  ; conceal-all
  ; conceal-conversion-typing
  ; conversion↑⇒coercion
  ; conversion↓⇒coercion
  ; reveal-fun
  ; reveal-all
  ; reveal-conversion-typing
  ; ConcealConversion
  ; RevealConversion
  )
open import Data.Product using (_×_; _,_; proj₁; Σ-syntax)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (there)
import Data.Nat
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _∣_⊢_⊑_⊣_
  ; _↦_
  ; _ˣ⊑★
  ; ⇑ᴸᵢ
  ; ∀ⁱ_
  ; tag_⇛_
  )
open import Interpreter using (TypeEnvironment)
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterSemanticTypingCore
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
import NarrowWiden as NW
import NuTermImprecision as NTI
import QuotientedTermImprecision as QTI
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; refl; subst; sym)
open import TermTyping using
  (SealModeStore★; cast-ext)
open import proof.CastImprecision using
  (seal★-ext-shift; seal★-gen-shift)
open import proof.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import proof.EndpointCanonicalMLBSimpleQuotient using
  (EndpointRepresentativeAlignment; endpoint-representatives-quotient)
open import proof.NarrowWidenProperties using
  (allocate-gen-narrowing)
open import proof.NuImprecisionStoreCorrespondenceLift using
  (lift-store-corresponds)
open import proof.NuImprecisionStoreLift using
  (lift-left-store-result; lift-store-result)
open import Types

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
component-left-applied-typing
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-reveal correspondence source target)))) =
  _ , conversion↑⇒coercion (reveal-conversion-typing source)
component-left-applied-typing
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-conceal correspondence source target)))) =
  _ , conversion↓⇒coercion (conceal-conversion-typing source)
component-left-applied-typing
    (operational-component
      (paired-coercion-action
        (QTI.paired-widening
          mode seal source mode′ seal′ target compatible))) =
  _ , proj₁ source
component-left-applied-typing
    (operational-component
      (left-narrowing-action mode seal source)) =
  _ , proj₁ source
component-left-applied-typing
    (operational-component
      (left-widening-action mode seal source)) =
  _ , proj₁ source
component-left-applied-typing
    (operational-component
      (left-reveal-action source)) =
  _ , conversion↑⇒coercion (reveal-conversion-typing source)
component-left-applied-typing
    (operational-component
      (left-conceal-action source)) =
  _ , conversion↓⇒coercion (conceal-conversion-typing source)
component-left-applied-typing
    (paired-narrowing-component
      mode seal source mode′ seal′ target) =
  _ , proj₁ source
component-left-applied-typing
    (paired-widening-component
      mode seal source mode′ seal′ target) =
  _ , proj₁ source

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
component-right-applied-typing
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-reveal correspondence source target)))) =
  _ , conversion↑⇒coercion (reveal-conversion-typing target)
component-right-applied-typing
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-conceal correspondence source target)))) =
  _ , conversion↓⇒coercion (conceal-conversion-typing target)
component-right-applied-typing
    (operational-component
      (paired-coercion-action
        (QTI.paired-widening
          mode seal source mode′ seal′ target compatible))) =
  _ , proj₁ target
component-right-applied-typing
    (operational-component
      (right-narrowing-action mode seal target)) =
  _ , proj₁ target
component-right-applied-typing
    (operational-component
      (right-widening-action mode seal target)) =
  _ , proj₁ target
component-right-applied-typing
    (operational-component
      (right-static-widening-action seal target)) =
  _ , proj₁ target
component-right-applied-typing
    (operational-component
      (right-reveal-action target)) =
  _ , conversion↑⇒coercion (reveal-conversion-typing target)
component-right-applied-typing
    (operational-component
      (right-conceal-action target)) =
  _ , conversion↓⇒coercion (conceal-conversion-typing target)
component-right-applied-typing
    (paired-narrowing-component
      mode seal source mode′ seal′ target) =
  _ , proj₁ target
component-right-applied-typing
    (paired-widening-component
      mode seal source mode′ seal′ target) =
  _ , proj₁ target
component-right-applied-typing
    (right-static-narrowing-component seal target) =
  _ , proj₁ target

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
quotient-down-left-typing
    (paired-id-down-action source target) =
  _ , proj₁ source
quotient-down-left-typing
    (paired-generalized-down-action source target) =
  _ , proj₁ source

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
quotient-down-right-typing
    (paired-id-down-action source target) =
  _ , proj₁ target
quotient-down-right-typing
    (paired-generalized-down-action source target) =
  _ , proj₁ target

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
quotient-up-left-typing
    (paired-quotient-up-action
      (QTI.quotient-id-widening source target)) =
  _ , proj₁ source
quotient-up-left-typing
    (paired-quotient-up-action
      (QTI.quotient-cast-widening
        mode seal source mode′ seal′ target)) =
  _ , proj₁ source

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
quotient-up-right-typing
    (paired-quotient-up-action
      (QTI.quotient-id-widening source target)) =
  _ , proj₁ target
quotient-up-right-typing
    (paired-quotient-up-action
      (QTI.quotient-cast-widening
        mode seal source mode′ seal′ target)) =
  _ , proj₁ target

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
    (apply-coercion (Coercions._↦_ c d))
    (apply-coercion (Coercions._↦_ c′ d′))
    (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) (apply-coercion c′) pC pA
  ×
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion d) (apply-coercion d′) pB pD
function-coercion-components
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-reveal link
            (reveal-fun source-domain source-codomain)
            (reveal-fun target-domain target-codomain))))) =
  operational-component
    (paired-coercion-action
      (QTI.paired-conversion
        (QTI.paired-conceal link source-domain target-domain))) ,
  operational-component
    (paired-coercion-action
      (QTI.paired-conversion
        (QTI.paired-reveal link source-codomain target-codomain)))
function-coercion-components
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-conceal link
            (conceal-fun source-domain source-codomain)
            (conceal-fun target-domain target-codomain))))) =
  operational-component
    (paired-coercion-action
      (QTI.paired-conversion
        (QTI.paired-reveal link source-domain target-domain))) ,
  operational-component
    (paired-coercion-action
      (QTI.paired-conversion
        (QTI.paired-conceal link source-codomain target-codomain)))
function-coercion-components
    (operational-component
      (paired-coercion-action
        (QTI.paired-widening
          mode seal
          (cast-fun source-domain source-codomain ,
            NW.cross (source-domainⁿ NW.↦ source-codomainʷ))
          mode′ seal′
          (cast-fun target-domain target-codomain ,
            NW.cross (target-domainⁿ NW.↦ target-codomainʷ))
          compatible))) =
  paired-narrowing-component mode seal
    (source-domain , source-domainⁿ)
    mode′ seal′ (target-domain , target-domainⁿ) ,
  paired-widening-component mode seal
    (source-codomain , source-codomainʷ)
    mode′ seal′ (target-codomain , target-codomainʷ)
function-coercion-components
    (paired-narrowing-component mode seal
      (cast-fun source-domain source-codomain ,
        NW.cross (source-domainʷ NW.↦ source-codomainⁿ))
      mode′ seal′
      (cast-fun target-domain target-codomain ,
        NW.cross (target-domainʷ NW.↦ target-codomainⁿ))) =
  paired-widening-component mode seal
    (source-domain , source-domainʷ)
    mode′ seal′ (target-domain , target-domainʷ) ,
  paired-narrowing-component mode seal
    (source-codomain , source-codomainⁿ)
    mode′ seal′ (target-codomain , target-codomainⁿ)
function-coercion-components
    (paired-widening-component mode seal
      (cast-fun source-domain source-codomain ,
        NW.cross (source-domainⁿ NW.↦ source-codomainʷ))
      mode′ seal′
      (cast-fun target-domain target-codomain ,
        NW.cross (target-domainⁿ NW.↦ target-codomainʷ))) =
  paired-narrowing-component mode seal
    (source-domain , source-domainⁿ)
    mode′ seal′ (target-domain , target-domainⁿ) ,
  paired-widening-component mode seal
    (source-codomain , source-codomainʷ)
    mode′ seal′ (target-codomain , target-codomainʷ)

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
    (apply-coercion (Coercions._↦_ c d)) skip-coercion
    (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) skip-coercion pC pA
  ×
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion d) skip-coercion pB pD
left-function-coercion-components
    (operational-component
      (left-narrowing-action mode seal
        (cast-fun domain codomain ,
          NW.cross (domainʷ NW.↦ codomainⁿ)))) =
  operational-component
    (left-widening-action mode seal (domain , domainʷ)) ,
  operational-component
    (left-narrowing-action mode seal (codomain , codomainⁿ))
left-function-coercion-components
    (operational-component
      (left-widening-action mode seal
        (cast-fun domain codomain ,
          NW.cross (domainⁿ NW.↦ codomainʷ)))) =
  operational-component
    (left-narrowing-action mode seal (domain , domainⁿ)) ,
  operational-component
    (left-widening-action mode seal (codomain , codomainʷ))
left-function-coercion-components
    (operational-component
      (left-reveal-action
        (reveal-fun domain codomain))) =
  operational-component (left-conceal-action domain) ,
  operational-component (left-reveal-action codomain)
left-function-coercion-components
    (operational-component
      (left-conceal-action
        (conceal-fun domain codomain))) =
  operational-component (left-reveal-action domain) ,
  operational-component (left-conceal-action codomain)

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
    skip-coercion (apply-coercion (Coercions._↦_ c′ d′))
    (pA ImprecisionWf.↦ pB) (pC ImprecisionWf.↦ pD) →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion c′) pC pA
  ×
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion d′) pB pD
right-function-coercion-components
    (operational-component
      (right-narrowing-action mode seal
        (cast-fun domain codomain ,
          NW.cross (domainʷ NW.↦ codomainⁿ)))) =
  operational-component
    (right-widening-action mode seal (domain , domainʷ)) ,
  operational-component
    (right-narrowing-action mode seal (codomain , codomainⁿ))
right-function-coercion-components
    (operational-component
      (right-widening-action mode seal
        (cast-fun domain codomain ,
          NW.cross (domainⁿ NW.↦ codomainʷ)))) =
  operational-component
    (right-narrowing-action mode seal (domain , domainⁿ)) ,
  operational-component
    (right-widening-action mode seal (codomain , codomainʷ))
right-function-coercion-components
    (operational-component
      (right-static-widening-action seal
        (cast-fun domain codomain ,
          NW.cross (domainⁿ NW.↦ codomainʷ)))) =
  right-static-narrowing-component seal (domain , domainⁿ) ,
  operational-component
    (right-static-widening-action seal (codomain , codomainʷ))
right-function-coercion-components
    (operational-component
      (right-reveal-action
        (reveal-fun domain codomain))) =
  operational-component (right-conceal-action domain) ,
  operational-component (right-reveal-action codomain)
right-function-coercion-components
    (operational-component
      (right-conceal-action
        (conceal-fun domain codomain))) =
  operational-component (right-reveal-action domain) ,
  operational-component (right-conceal-action codomain)
right-function-coercion-components
    (right-static-narrowing-component seal
      (cast-fun domain codomain ,
        NW.cross (domainʷ NW.↦ codomainⁿ))) =
  operational-component
      (right-static-widening-action seal (domain , domainʷ)) ,
  right-static-narrowing-component seal (codomain , codomainⁿ)

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
    skip-coercion (apply-coercion (Coercions._↦_ c′ d′)) p q →
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
right-boundary-function-coercion-components
    {p = pA ImprecisionWf.↦ pB}
    {q = pC ImprecisionWf.↦ pD}
    refl
    (operational-component
      (right-narrowing-action mode seal
        (cast-fun domain codomain ,
          NW.cross (domainʷ NW.↦ codomainⁿ)))) =
  _ , _ , _ , _ , pA , pB , pC , pD ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  operational-component
    (right-widening-action mode seal (domain , domainʷ)) ,
  operational-component
    (right-narrowing-action mode seal (codomain , codomainⁿ))
right-boundary-function-coercion-components
    {p = pA ImprecisionWf.↦ pB}
    {q = pC ImprecisionWf.↦ pD}
    refl
    (operational-component
      (right-widening-action mode seal
        (cast-fun domain codomain ,
          NW.cross (domainⁿ NW.↦ codomainʷ)))) =
  _ , _ , _ , _ , pA , pB , pC , pD ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  operational-component
    (right-narrowing-action mode seal (domain , domainⁿ)) ,
  operational-component
    (right-widening-action mode seal (codomain , codomainʷ))
right-boundary-function-coercion-components
    {p = pA ImprecisionWf.↦ pB}
    {q = pC ImprecisionWf.↦ pD}
    refl
    (operational-component
      (right-static-widening-action seal
        (cast-fun domain codomain ,
          NW.cross (domainⁿ NW.↦ codomainʷ)))) =
  _ , _ , _ , _ , pA , pB , pC , pD ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  right-static-narrowing-component seal (domain , domainⁿ) ,
  operational-component
    (right-static-widening-action seal (codomain , codomainʷ))
right-boundary-function-coercion-components
    {p = pA ImprecisionWf.↦ pB}
    {q = pC ImprecisionWf.↦ pD}
    refl
    (operational-component
      (right-reveal-action
        (reveal-fun domain codomain))) =
  _ , _ , _ , _ , pA , pB , pC , pD ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  operational-component (right-conceal-action domain) ,
  operational-component (right-reveal-action codomain)
right-boundary-function-coercion-components
    {p = pA ImprecisionWf.↦ pB}
    {q = pC ImprecisionWf.↦ pD}
    refl
    (operational-component
      (right-conceal-action
        (conceal-fun domain codomain))) =
  _ , _ , _ , _ , pA , pB , pC , pD ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  operational-component (right-reveal-action domain) ,
  operational-component (right-conceal-action codomain)
right-boundary-function-coercion-components
    {p = pA ImprecisionWf.↦ pB}
    {q = pC ImprecisionWf.↦ pD}
    refl
    (right-static-narrowing-component seal
      (cast-fun domain codomain ,
        NW.cross (domainʷ NW.↦ codomainⁿ))) =
  _ , _ , _ , _ , pA , pB , pC , pD ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  Relation.Binary.PropositionalEquality.refl ,
  operational-component
    (right-static-widening-action seal (domain , domainʷ)) ,
  right-static-narrowing-component seal (codomain , codomainⁿ)
right-boundary-function-coercion-components
    {p = tag pA ⇛ pB}
    refl
    (operational-component
      (right-narrowing-action mode seal ()))
right-boundary-function-coercion-components
    {p = tag pA ⇛ pB}
    refl
    (operational-component
      (right-widening-action mode seal ()))
right-boundary-function-coercion-components
    {p = tag pA ⇛ pB}
    refl
    (operational-component
      (right-static-widening-action seal ()))
right-boundary-function-coercion-components
    {p = tag pA ⇛ pB}
    refl
    (operational-component
      (right-reveal-action ()))
right-boundary-function-coercion-components
    {p = tag pA ⇛ pB}
    refl
    (operational-component
      (right-conceal-action ()))
right-boundary-function-coercion-components
    {p = tag pA ⇛ pB}
    refl
    (right-static-narrowing-component seal ())
right-boundary-function-coercion-components {A = `∀ A} ()

paired-all-conversion-component :
  ∀ {Φ Δᴸ Δᴿ ρ ρ′ c c′ A A′ B B′ p q} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  QTI.PairedConversion Φ Δᴸ Δᴿ ρ
    (Coercions.`∀ c) (Coercions.`∀ c′)
    {`∀ A} {`∀ A′} {`∀ B} {`∀ B′}
    (∀ⁱ p) (∀ⁱ q) →
  QTI.PairedConversion
    (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ρ′
    c c′ {A} {A′} {B} {B′} p q
paired-all-conversion-component liftρ
    (QTI.paired-reveal correspondence
      (reveal-all source) (reveal-all target))
    with lift-store-corresponds liftρ correspondence
paired-all-conversion-component liftρ
    (QTI.paired-reveal correspondence
      (reveal-all source) (reveal-all target))
    | shifted-proof , shifted-correspondence =
  QTI.paired-reveal shifted-correspondence
    (subst
      (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
      (sym (NTI.leftStoreⁱ-lift liftρ)) source)
    (subst
      (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
      (sym (NTI.rightStoreⁱ-lift liftρ)) target)
paired-all-conversion-component liftρ
    (QTI.paired-conceal correspondence
      (conceal-all source) (conceal-all target))
    with lift-store-corresponds liftρ correspondence
paired-all-conversion-component liftρ
    (QTI.paired-conceal correspondence
      (conceal-all source) (conceal-all target))
    | shifted-proof , shifted-correspondence =
  QTI.paired-conceal shifted-correspondence
    (subst
      (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
      (sym (NTI.leftStoreⁱ-lift liftρ)) source)
    (subst
      (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
      (sym (NTI.rightStoreⁱ-lift liftρ)) target)

paired-forall-component-at :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)}
    {c c′ : Coercion} {A A′ B B′ : Ty}
    {p : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ A ⊑ A′ ⊣ Data.Nat.suc Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ B′ ⊣ Data.Nat.suc Δᴿ} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.`∀ c))
    (apply-coercion (Coercions.`∀ c′))
    (∀ⁱ p) (∀ⁱ q) →
  ComponentCoercionNarrowing
    (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ρ′
    (apply-coercion c) (apply-coercion c′) p q
paired-forall-component-at liftρ
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion conversion))) =
  operational-component
    (paired-coercion-action
      (QTI.paired-conversion
        (paired-all-conversion-component liftρ conversion)))
paired-forall-component-at liftρ
    (operational-component
      (paired-coercion-action
        (QTI.paired-widening
          mode seal
          (cast-all source , NW.cross (NW.`∀ sourceʷ))
          mode′ seal′
          (cast-all target , NW.cross (NW.`∀ targetʷ))
          compatible))) =
  paired-widening-component
    (cast-ext mode)
    (subst (SealModeStore★ (extᵈ _))
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (seal★-ext-shift seal))
    (subst
      (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (source , sourceʷ))
    (cast-ext mode′)
    (subst (SealModeStore★ (extᵈ _))
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (seal★-ext-shift seal′))
    (subst
      (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (target , targetʷ))
paired-forall-component-at liftρ
    (paired-narrowing-component
      mode seal (cast-all source , NW.cross (NW.`∀ sourceⁿ))
      mode′ seal′ (cast-all target , NW.cross (NW.`∀ targetⁿ))) =
  paired-narrowing-component
    (cast-ext mode)
    (subst (SealModeStore★ (extᵈ _))
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (seal★-ext-shift seal))
    (subst
      (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (source , sourceⁿ))
    (cast-ext mode′)
    (subst (SealModeStore★ (extᵈ _))
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (seal★-ext-shift seal′))
    (subst
      (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (target , targetⁿ))
paired-forall-component-at liftρ
    (paired-widening-component
      mode seal (cast-all source , NW.cross (NW.`∀ sourceʷ))
      mode′ seal′ (cast-all target , NW.cross (NW.`∀ targetʷ))) =
  paired-widening-component
    (cast-ext mode)
    (subst (SealModeStore★ (extᵈ _))
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (seal★-ext-shift seal))
    (subst
      (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (source , sourceʷ))
    (cast-ext mode′)
    (subst (SealModeStore★ (extᵈ _))
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (seal★-ext-shift seal′))
    (subst
      (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (target , targetʷ))

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
paired-forall-coercion-component {ρ = ρ} action
    with lift-store-result ρ
paired-forall-coercion-component action
    | ρ′ , liftρ =
  ρ′ , liftρ , paired-forall-component-at liftρ action

left-forall-component-at :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ)
      (Data.Nat.suc Δᴸ) Δᴿ}
    {c : Coercion} {A B T : Ty}
    {p : ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
          ImprecisionWf.⇑ᴸᵢ Φ) ∣ Data.Nat.suc Δᴸ
      ⊢ A ⊑ T ⊣ Δᴿ}
    {q : ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
          ImprecisionWf.⇑ᴸᵢ Φ) ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ T ⊣ Δᴿ}
    {nonvar : NonVar A}
    {occ : occurs Data.Nat.zero A ≡ true}
    {nonvar′ : NonVar B}
    {occ′ : occurs Data.Nat.zero B ≡ true} →
  NTI.LiftLeftStoreⁱ
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ) ρ ρ′ →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.`∀ c)) skip-coercion
    (ImprecisionWf.ν nonvar occ p)
    (ImprecisionWf.ν nonvar′ occ′ q) →
  ComponentCoercionNarrowing
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ)
    (Data.Nat.suc Δᴸ) Δᴿ ρ′
    (apply-coercion c) skip-coercion p q
left-forall-component-at liftρ
    (operational-component
      (left-narrowing-action
        mode seal (cast-all source , NW.cross (NW.`∀ sourceⁿ)))) =
  operational-component
    (left-narrowing-action
      (cast-ext mode)
      (subst (SealModeStore★ (extᵈ _))
        (sym (NTI.leftStoreⁱ-lift-left liftρ))
        (seal★-ext-shift seal))
      (subst
        (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
        (sym (NTI.leftStoreⁱ-lift-left liftρ))
        (source , sourceⁿ)))
left-forall-component-at liftρ
    (operational-component
      (left-widening-action
        mode seal (cast-all source , NW.cross (NW.`∀ sourceʷ)))) =
  operational-component
    (left-widening-action
      (cast-ext mode)
      (subst (SealModeStore★ (extᵈ _))
        (sym (NTI.leftStoreⁱ-lift-left liftρ))
        (seal★-ext-shift seal))
      (subst
        (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
        (sym (NTI.leftStoreⁱ-lift-left liftρ))
        (source , sourceʷ)))
left-forall-component-at liftρ
    (operational-component
      (left-reveal-action (reveal-all source))) =
  operational-component
    (left-reveal-action
      (subst
        (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
        (sym (NTI.leftStoreⁱ-lift-left liftρ))
        source))
left-forall-component-at liftρ
    (operational-component
      (left-conceal-action (conceal-all source))) =
  operational-component
    (left-conceal-action
      (subst
        (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
        (sym (NTI.leftStoreⁱ-lift-left liftρ))
        source))

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
    {nonvar : NonVar A}
    {occ : occurs Data.Nat.zero A ≡ true}
    {nonvar′ : NonVar B}
    {occ′ : occurs Data.Nat.zero B ≡ true} →
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
left-forall-coercion-component {ρ = ρ} action
    with lift-left-store-result ρ
left-forall-coercion-component action
    | ρ′ , liftρ =
  ρ′ , liftρ , left-forall-component-at liftρ action

right-forall-component-at :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)}
    {c′ : Coercion} {A A′ B B′ : Ty}
    {p : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ A ⊑ A′ ⊣ Data.Nat.suc Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ B′ ⊣ Data.Nat.suc Δᴿ} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    skip-coercion (apply-coercion (Coercions.`∀ c′))
    (∀ⁱ p) (∀ⁱ q) →
  ComponentCoercionNarrowing
    (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ) ρ′
    skip-coercion (apply-coercion c′) p q
right-forall-component-at liftρ
    (operational-component
      (right-narrowing-action
        mode seal (cast-all target , NW.cross (NW.`∀ targetⁿ)))) =
  operational-component
    (right-narrowing-action
      (cast-ext mode)
      (subst (SealModeStore★ (extᵈ _))
        (sym (NTI.rightStoreⁱ-lift liftρ))
        (seal★-ext-shift seal))
      (subst
        (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
        (sym (NTI.rightStoreⁱ-lift liftρ))
        (target , targetⁿ)))
right-forall-component-at liftρ
    (operational-component
      (right-widening-action
        mode seal (cast-all target , NW.cross (NW.`∀ targetʷ)))) =
  operational-component
    (right-widening-action
      (cast-ext mode)
      (subst (SealModeStore★ (extᵈ _))
        (sym (NTI.rightStoreⁱ-lift liftρ))
        (seal★-ext-shift seal))
      (subst
        (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
        (sym (NTI.rightStoreⁱ-lift liftρ))
        (target , targetʷ)))
right-forall-component-at liftρ
    (operational-component
      (right-static-widening-action
        seal (cast-all target , NW.cross (NW.`∀ targetʷ)))) =
  operational-component
    (right-static-widening-action
      (subst (SealModeStore★ (extᵈ _))
        (sym (NTI.rightStoreⁱ-lift liftρ))
        (seal★-ext-shift seal))
      (subst
        (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
        (sym (NTI.rightStoreⁱ-lift liftρ))
        (target , targetʷ)))
right-forall-component-at liftρ
    (operational-component
      (right-reveal-action (reveal-all target))) =
  operational-component
    (right-reveal-action
      (subst
        (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
        (sym (NTI.rightStoreⁱ-lift liftρ))
        target))
right-forall-component-at liftρ
    (operational-component
      (right-conceal-action (conceal-all target))) =
  operational-component
    (right-conceal-action
      (subst
        (λ Σ → ConcealConversion _ _ Σ _ _ _ _ _)
        (sym (NTI.rightStoreⁱ-lift liftρ))
        target))
right-forall-component-at liftρ
    (right-static-narrowing-component
      seal (cast-all target , NW.cross (NW.`∀ targetⁿ))) =
  right-static-narrowing-component
    (subst (SealModeStore★ (extᵈ _))
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (seal★-ext-shift seal))
    (subst
      (λ Σ → extᵈ _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊒ _)
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (target , targetⁿ))

right-forall-coercion-component :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {c′ : Coercion} {A A′ B B′ : Ty}
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
right-forall-coercion-component {ρ = ρ} action
    with lift-store-result ρ
right-forall-coercion-component action
    | ρ′ , liftρ =
  ρ′ , liftρ , right-forall-component-at liftρ action

paired-left-gen-seal :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {μ} {Aν : Ty}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  SealModeStore★ μ (NTI.leftStoreⁱ ρ) →
  SealModeStore★ (genᵈ μ)
    ((Data.Nat.zero , Aν) ∷ NTI.leftStoreⁱ ρ′)
paired-left-gen-seal liftρ seal Data.Nat.zero ()
paired-left-gen-seal {μ = μ} liftρ seal
    (Data.Nat.suc α) ok =
  there
    (subst (SealModeStore★ (genᵈ μ))
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (seal★-gen-shift seal)
      (Data.Nat.suc α) ok)

paired-right-gen-seal :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {μ} {Aν : Ty}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  SealModeStore★ μ (NTI.rightStoreⁱ ρ) →
  SealModeStore★ (genᵈ μ)
    ((Data.Nat.zero , Aν) ∷ NTI.rightStoreⁱ ρ′)
paired-right-gen-seal liftρ seal Data.Nat.zero ()
paired-right-gen-seal {μ = μ} liftρ seal
    (Data.Nat.suc α) ok =
  there
    (subst (SealModeStore★ (genᵈ μ))
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (seal★-gen-shift seal)
      (Data.Nat.suc α) ok)

left-gen-seal :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {μ} {Aν : Ty}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ)
      (Data.Nat.suc Δᴸ) Δᴿ} →
  NTI.LiftLeftStoreⁱ
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ) ρ ρ′ →
  SealModeStore★ μ (NTI.leftStoreⁱ ρ) →
  SealModeStore★ (genᵈ μ)
    ((Data.Nat.zero , Aν) ∷ NTI.leftStoreⁱ ρ′)
left-gen-seal liftρ seal Data.Nat.zero ()
left-gen-seal {μ = μ} liftρ seal
    (Data.Nat.suc α) ok =
  there
    (subst (SealModeStore★ (genᵈ μ))
      (sym (NTI.leftStoreⁱ-lift-left liftρ))
      (seal★-gen-shift seal)
      (Data.Nat.suc α) ok)

paired-left-generalized-body :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)}
    {μ} {A B X : Ty}
    {coercion : Coercion} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
    ⊢ Coercions.gen A coercion ∶ A ⊒ `∀ B →
  genᵈ μ ∣ Data.Nat.suc Δᴸ ∣
    ((Data.Nat.zero , ⇑ᵗ X) ∷ NTI.leftStoreⁱ ρ′)
    ⊢ coercion ∶ ⇑ᵗ A ⊒ B
paired-left-generalized-body
    {Δᴸ = Δᴸ} {μ = μ} {A = A} {B = B}
    {X = X} {coercion = coercion} liftρ cast =
  subst
    (λ Σ → genᵈ μ ∣ Data.Nat.suc Δᴸ ∣ Σ
      ⊢ coercion ∶ ⇑ᵗ A ⊒ B)
    (sym (cong
      ((Data.Nat.zero , ⇑ᵗ X) ∷_)
      (NTI.leftStoreⁱ-lift liftρ)))
    (allocate-gen-narrowing {Aν = ⇑ᵗ X} cast)

paired-right-generalized-body :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)}
    {μ} {A B X : Ty}
    {coercion : Coercion} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  μ ∣ Δᴿ ∣ NTI.rightStoreⁱ ρ
    ⊢ Coercions.gen A coercion ∶ A ⊒ `∀ B →
  genᵈ μ ∣ Data.Nat.suc Δᴿ ∣
    ((Data.Nat.zero , ⇑ᵗ X) ∷ NTI.rightStoreⁱ ρ′)
    ⊢ coercion ∶ ⇑ᵗ A ⊒ B
paired-right-generalized-body
    {Δᴿ = Δᴿ} {μ = μ} {A = A} {B = B}
    {X = X} {coercion = coercion} liftρ cast =
  subst
    (λ Σ → genᵈ μ ∣ Data.Nat.suc Δᴿ ∣ Σ
      ⊢ coercion ∶ ⇑ᵗ A ⊒ B)
    (sym (cong
      ((Data.Nat.zero , ⇑ᵗ X) ∷_)
      (NTI.rightStoreⁱ-lift liftρ)))
    (allocate-gen-narrowing {Aν = ⇑ᵗ X} cast)

paired-generalized-component-at :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)}
    {c c′ : Coercion}
    {A A′ B B′ C C′ X X′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ B ⊑ B′ ⊣ Data.Nat.suc Δᴿ}
    {pX⇑ : ∀ᵢᶜ Φ ∣ Data.Nat.suc Δᴸ
      ⊢ ⇑ᵗ X ⊑ ⇑ᵗ X′ ⊣ Data.Nat.suc Δᴿ} →
  NTI.LiftStoreⁱ (∀ᵢᶜ Φ) ρ ρ′ →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.gen C c))
    (apply-coercion (Coercions.gen C′ c′))
    p (∀ⁱ q) →
  ComponentCoercionNarrowing
    (∀ᵢᶜ Φ) (Data.Nat.suc Δᴸ) (Data.Nat.suc Δᴿ)
    (NTI.store-matched Data.Nat.zero (⇑ᵗ X)
      Data.Nat.zero (⇑ᵗ X′) pX⇑ ∷ ρ′)
    (apply-coercion c) (apply-coercion c′)
    (⊑-lift∀ᵢ p) q
paired-generalized-component-at liftρ
    (paired-narrowing-component
      mode seal
      (Coercions.cast-gen hC occ source ,
        NW.gen sourceⁿ)
      mode′ seal′
      (Coercions.cast-gen hC′ occ′ target ,
        NW.gen targetⁿ)) =
  paired-narrowing-component
    (TermTyping.cast-gen mode)
    (paired-left-gen-seal liftρ seal)
    (paired-left-generalized-body liftρ
      (Coercions.cast-gen hC occ source , NW.gen sourceⁿ))
    (TermTyping.cast-gen mode′)
    (paired-right-gen-seal liftρ seal′)
    (paired-right-generalized-body liftρ
      (Coercions.cast-gen hC′ occ′ target , NW.gen targetⁿ))
paired-generalized-component-at liftρ
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-reveal correspondence () target))))
paired-generalized-component-at liftρ
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-conceal correspondence () target))))
paired-generalized-component-at liftρ
    (operational-component
      (paired-coercion-action
        (QTI.paired-widening
          mode seal
          (Coercions.cast-gen hC occ source , NW.cross ())
          mode′ seal′ target compatible)))
paired-generalized-component-at liftρ
    (paired-widening-component
      mode seal
      (Coercions.cast-gen hC occ source , NW.cross ())
      mode′ seal′ target)

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
paired-generalized-coercion-component {ρ = ρ} action
    with lift-store-result ρ
paired-generalized-coercion-component action
    | ρ′ , liftρ =
  ρ′ , liftρ , paired-generalized-component-at liftρ action

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
paired-generalized-type-narrowing
    {p = p}
    (paired-narrowing-component
      mode seal
      (Coercions.cast-gen hC occ source , NW.gen sourceⁿ)
      mode′ seal′
      (Coercions.cast-gen hC′ occ′ target , NW.gen targetⁿ)) =
  type-narrowing p
paired-generalized-type-narrowing
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-reveal correspondence () target))))
paired-generalized-type-narrowing
    (operational-component
      (paired-coercion-action
        (QTI.paired-conversion
          (QTI.paired-conceal correspondence () target))))
paired-generalized-type-narrowing
    (operational-component
      (paired-coercion-action
        (QTI.paired-widening
          mode seal
          (Coercions.cast-gen hC occ source , NW.cross ())
          mode′ seal′ target compatible)))
paired-generalized-type-narrowing
    (paired-widening-component
      mode seal
      (Coercions.cast-gen hC occ source , NW.cross ())
      mode′ seal′ target)

left-generalized-body :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ)
      (Data.Nat.suc Δᴸ) Δᴿ}
    {μ} {A B X : Ty}
    {coercion : Coercion} →
  NTI.LiftLeftStoreⁱ
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ) ρ ρ′ →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
    ⊢ Coercions.gen A coercion ∶ A ⊒ `∀ B →
  genᵈ μ ∣ Data.Nat.suc Δᴸ ∣
    ((Data.Nat.zero , ⇑ᵗ X) ∷ NTI.leftStoreⁱ ρ′)
    ⊢ coercion ∶ ⇑ᵗ A ⊒ B
left-generalized-body
    {Δᴸ = Δᴸ} {μ = μ} {A = A} {B = B}
    {X = X} {coercion = coercion} liftρ cast =
  subst
    (λ Σ → genᵈ μ ∣ Data.Nat.suc Δᴸ ∣ Σ
      ⊢ coercion ∶ ⇑ᵗ A ⊒ B)
    (sym (cong
      ((Data.Nat.zero , ⇑ᵗ X) ∷_)
      (NTI.leftStoreⁱ-lift-left liftρ)))
    (allocate-gen-narrowing {Aν = ⇑ᵗ X} cast)

left-generalized-component-at :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : NTI.StoreImp
      ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
        ImprecisionWf.⇑ᴸᵢ Φ)
      (Data.Nat.suc Δᴸ) Δᴿ}
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
  NTI.LiftLeftStoreⁱ
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ) ρ ρ′ →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion (Coercions.gen C c)) skip-coercion
    p (ImprecisionWf.ν nonvar occ q) →
  ComponentCoercionNarrowing
    ((Data.Nat.zero ImprecisionWf.ˣ⊑★) ∷
      ImprecisionWf.⇑ᴸᵢ Φ)
    (Data.Nat.suc Δᴸ) Δᴿ
    (NTI.store-left Data.Nat.zero (⇑ᵗ X) hX ∷ ρ′)
    (apply-coercion c) skip-coercion
    (⊑-source-liftνᵢ p) q
left-generalized-component-at liftρ
    (operational-component
      (left-narrowing-action mode seal
        (Coercions.cast-gen hC occurrence source ,
          NW.gen sourceⁿ))) =
  operational-component
    (left-narrowing-action
      (TermTyping.cast-gen mode)
      (left-gen-seal liftρ seal)
      (left-generalized-body liftρ
        (Coercions.cast-gen hC occurrence source ,
          NW.gen sourceⁿ)))
left-generalized-component-at liftρ
    (operational-component
      (left-widening-action mode seal
        (Coercions.cast-gen hC occurrence source ,
          NW.cross ())))
left-generalized-component-at liftρ
    (operational-component
      (left-reveal-action ()))
left-generalized-component-at liftρ
    (operational-component
      (left-conceal-action ()))

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
left-generalized-coercion-component {ρ = ρ} action
    with lift-left-store-result ρ
left-generalized-coercion-component action
    | ρ′ , liftρ =
  ρ′ , liftρ , left-generalized-component-at liftρ action
