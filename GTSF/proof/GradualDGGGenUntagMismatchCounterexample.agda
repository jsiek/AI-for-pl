module proof.GradualDGGGenUntagMismatchCounterexample where

-- File Charter:
--   * Refutes the public `GradualDGG` theorem with a closed gradual-term
--     imprecision derivation.
--   * Connects compilation to whole source-value and target-blame traces.
--   * Introduces no result carrier, view, outcome, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; z<s)
open import Data.Product using (_,_)

import Coercions as C
open import Compile using
  ( CastPlan
  ; cast
  ; consistency-cast-plan
  )
open import DynamicGradualGuarantee using
  ( GradualDGG
  ; compiled-left
  ; compiled-right
  )
import Imprecision as Imp
open import ImprecisionWf using
  ( id★
  ; tag_⇛_
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import GradualTermImprecision using
  ( _∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_
  ; x⊑xᴳ
  ; ƛ⊑ƛᴳ
  ; ·⊑·ᴳ
  ; κ⊑κᴳ
  )
open import GradualTerms using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·[_]_ to _·ᴳ[_]_
    ; $ to $ᴳ
    )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; blame
  ; no•-`
  ; no•-ƛ
  ; no•-⟨⟩
  ; _⟨_⟩
  )
  renaming
    ( `_ to `ᵀ_
    ; ƛ_ to ƛᵀ_
    ; _·_ to _·ᵀ_
    ; $ to $ᵀ
    )
open import NuReduction using
  ( keep
  ; pure-step
  ; shift-keep
  ; β
  ; β-id
  ; blame-·₂
  ; blame-⟨⟩
  ; ξ-·₂
  ; ξ-⟨⟩
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import Primitives using (κℕ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Types as T
open import Types using
  ( Ty
  ; ★
  ; wf★
  ; wfVar
  ; wf⇒
  ; wf∀
  ; ＇_
  ; _⇒_
  ; `∀
  ; Z
  )
open import proof.ImprecisionProperties using (⊑-refl-idᵢ; ~-sym)
open import proof.MaximalLowerBoundsWf using (⊑-forgetᵢ)
open import proof.NuImprecisionGenUntagCounterexampleCore using
  ( A
  ; G
  ; X
  ; p
  ; q
  ; source-gen
  )
open import
  proof.NuImprecisionGenUntagMismatchCounterexampleCore using
  ( HNat
  ; WNat
  ; noSourceValue
  ; sourceValue
  ; taggedNat
  ; target-blame-trace
  ; targetRedex
  ; vSourceValue
  ; vTaggedNat
  ; vWNat
  )
open import proof.NuReductionDeterminism using
  (source-blame-excludes-value)
open import proof.ReductionProperties using
  ( cast-↠
  ; ·₂-↠
  ; ↠-trans
  )


label : T.Label
label = zero

idᴳ : Ty → GTerm
idᴳ B = ƛᴳ B ⇒ `ᴳ zero

nat-producerᴳ : GTerm
nat-producerᴳ = idᴳ ★ ·ᴳ[ label ] $ᴳ (κℕ zero)

source-programᴳ : GTerm
source-programᴳ = idᴳ A ·ᴳ[ label ] nat-producerᴳ

target-programᴳ : GTerm
target-programᴳ = idᴳ G ·ᴳ[ label ] nat-producerᴳ

wfA : T.WfTy zero A
wfA = wf∀ (wf⇒ (wfVar z<s) (wfVar z<s))

wfG : T.WfTy zero G
wfG = wf⇒ wf★ wf★

G⊑★ : [] ∣ zero ⊢ G ⊑ ★ ⊣ zero
G⊑★ = tag id★ ⇛ id★

star~nat : zero Imp.⊢ ★ ~ HNat
star~nat = HNat , Imp.tag T.`ℕ , Imp.idι

A~star : zero Imp.⊢ A ~ ★
A~star =
  A , ⊑-refl-idᵢ wfA , ⊑-forgetᵢ p

G~star : zero Imp.⊢ G ~ ★
G~star =
  G , ⊑-refl-idᵢ wfG , ⊑-forgetᵢ G⊑★

id-star-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ idᴳ ★ ⊑ idᴳ ★ ⦂ G ⊑ G ∶ id★ ↦ id★
id-star-relation =
  ƛ⊑ƛᴳ wf★ wf★ (x⊑xᴳ Z)

nat-producer-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ nat-producerᴳ ⊑ nat-producerᴳ ⦂ ★ ⊑ ★ ∶ id★
nat-producer-relation =
  ·⊑·ᴳ id-star-relation κ⊑κᴳ star~nat star~nat

outer-function-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ idᴳ A ⊑ idᴳ G ⦂ A ⇒ A ⊑ G ⇒ G ∶ q ↦ q
outer-function-relation =
  ƛ⊑ƛᴳ wfA wfG (x⊑xᴳ Z)

public-mismatch-relation :
  [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ source-programᴳ ⊑ target-programᴳ ⦂ A ⊑ G ∶ q
public-mismatch-relation =
  ·⊑·ᴳ outer-function-relation nat-producer-relation A~star G~star

nat-plan : CastPlan zero [] HNat ★
nat-plan = consistency-cast-plan label (~-sym star~nat)

source-plan : CastPlan zero [] ★ A
source-plan = consistency-cast-plan label (~-sym A~star)

target-plan : CastPlan zero [] ★ G
target-plan = consistency-cast-plan label (~-sym G~star)

idᵀ : Term
idᵀ = ƛᵀ (`ᵀ zero)

compiled-nat-producer : Term
compiled-nat-producer = idᵀ ·ᵀ cast nat-plan WNat

compiled-source : Term
compiled-source = idᵀ ·ᵀ cast source-plan compiled-nat-producer

compiled-target : Term
compiled-target = idᵀ ·ᵀ cast target-plan compiled-nat-producer

compiled-left-shape :
  compiled-left public-mismatch-relation ≡ compiled-source
compiled-left-shape = refl

compiled-right-shape :
  compiled-right public-mismatch-relation ≡ compiled-target
compiled-right-shape = refl

nat-down-shape : Compile.down nat-plan ≡ C.id HNat
nat-down-shape = refl

nat-up-shape : Compile.up nat-plan ≡ HNat C.!
nat-up-shape = refl

source-down-shape : Compile.down source-plan ≡ source-gen
source-down-shape = refl

target-down-shape : Compile.down target-plan ≡ G C.？
target-down-shape = refl

source-up : C.Coercion
source-up = C.`∀ ((C.id X) C.↦ (C.id X))

target-up : C.Coercion
target-up = (C.id ★) C.↦ (C.id ★)

source-up-shape : Compile.up source-plan ≡ source-up
source-up-shape = refl

target-up-shape : Compile.up target-plan ≡ target-up
target-up-shape = refl

v-idᵀ : Value idᵀ
v-idᵀ = ƛᵀ (`ᵀ zero)

no-idᵀ : No• idᵀ
no-idᵀ = no•-ƛ no•-`

source-final : Term
source-final = sourceValue ⟨ source-up ⟩

v-source-final : Value source-final
v-source-final = vSourceValue ⟨ C.`∀ ((C.id X) C.↦ (C.id X)) ⟩

no-source-final : No• source-final
no-source-final = no•-⟨⟩ noSourceValue

nat-producer-trace :
  compiled-nat-producer —↠[ keep ∷ keep ∷ [] ] taggedNat
nat-producer-trace
    rewrite nat-down-shape | nat-up-shape =
  ↠-step
    (ξ-·₂ v-idᵀ shift-keep
      (ξ-⟨⟩ (pure-step (β-id vWNat))))
    (↠-step (pure-step (β vTaggedNat)) ↠-refl)

source-argument-trace :
  cast source-plan compiled-nat-producer
    —↠[ keep ∷ keep ∷ [] ] source-final
source-argument-trace
    rewrite source-down-shape | source-up-shape =
  cast-↠ (cast-↠ nat-producer-trace)

compiled-source-trace :
  compiled-source —↠[ keep ∷ keep ∷ keep ∷ [] ] source-final
compiled-source-trace =
  ↠-trans
    (·₂-↠ v-idᵀ no-idᵀ source-argument-trace)
    (↠-step (pure-step (β v-source-final)) ↠-refl)

public-source-trace :
  compiled-left public-mismatch-relation
    —↠[ keep ∷ keep ∷ keep ∷ [] ] source-final
public-source-trace =
  subst
    (λ M → M —↠[ keep ∷ keep ∷ keep ∷ [] ] source-final)
    (sym compiled-left-shape)
    compiled-source-trace

target-down-final : Term
target-down-final = targetRedex ⟨ target-up ⟩

target-argument-prefix :
  cast target-plan compiled-nat-producer
    —↠[ keep ∷ keep ∷ [] ] target-down-final
target-argument-prefix
    rewrite target-down-shape | target-up-shape =
  cast-↠ (cast-↠ nat-producer-trace)

target-argument-tail :
  target-down-final —↠[ keep ∷ keep ∷ [] ] blame
target-argument-tail =
  ↠-trans
    (cast-↠ target-blame-trace)
    (↠-step (pure-step blame-⟨⟩) ↠-refl)

target-argument-trace :
  cast target-plan compiled-nat-producer
    —↠[ keep ∷ keep ∷ keep ∷ keep ∷ [] ] blame
target-argument-trace =
  ↠-trans target-argument-prefix target-argument-tail

compiled-target-blame :
  compiled-target
    —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ] blame
compiled-target-blame =
  ↠-trans
    (·₂-↠ v-idᵀ no-idᵀ target-argument-trace)
    (↠-step (pure-step (blame-·₂ v-idᵀ)) ↠-refl)

public-target-blame :
  compiled-right public-mismatch-relation
    —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ] blame
public-target-blame =
  subst
    (λ M →
      M —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ] blame)
    (sym compiled-right-shape)
    compiled-target-blame

gradual-dgg-gen-untag-mismatch-counterexample : GradualDGG → ⊥
gradual-dgg-gen-untag-mismatch-counterexample dgg
    with dgg public-mismatch-relation
gradual-dgg-gen-untag-mismatch-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    with forward source-final (keep ∷ keep ∷ keep ∷ [])
      public-source-trace v-source-final
gradual-dgg-gen-untag-mismatch-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    | V′ , χs′ , Φ , ρ , r , target-trace , vV′ ,
      left-eq , right-eq , final-relation =
  source-blame-excludes-value public-target-blame target-trace vV′
