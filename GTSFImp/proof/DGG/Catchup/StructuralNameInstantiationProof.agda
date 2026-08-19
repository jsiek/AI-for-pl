module proof.DGG.Catchup.StructuralNameInstantiationProof where

-- File Charter:
--   * Implements the structural worker for named target instantiation.
--   * Uses cast mass as the primary accessibility measure.
--   * Replays source wrappers only after target normalization is known.

import Data.Fin as Fin
import Data.List as List
import Data.Nat.Induction as NatInduction
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _+_; s≤s)
open import Data.Nat.Properties using (+-assoc; n<1+n; ≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
import Data.Product.Relation.Binary.Lex.Strict as ProductLex
open import Data.Sum.Base using (inj₁; inj₂)
import Induction.WellFounded as WF
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyVar; NonVar; _∈ᵗ_; ★; ＇_; `∀; ⇑ᵗ; _[_]ᵗ;
   renameᵗ)
open import Imprecision using (X⊑★)
open import Consistency using
  (Env∼; _↪ᵗ_; wk↪ᵗ; keep; toRenameᵗ; extᵐ; instᵐ; genᵐ;
   _⊢_∼_; inst_; ↑ᶜ_; close-instᶜ; _↦_; ∀ᶜ_; gen_; _[_]ᶜ)
import Conversion as Conv
open import Conversion using (Conv↑; Conv↓; replaceTy; 〖_,_↑_〗)
import CastTerms as CT
open import CastTerms using
  (Term; Value; Inert; GenSafe; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _⟨_⟩;
   _↑_; _↓_; _⦂∀_[_]; renameᵗᵐ; ⇑ᵗᵐ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTy;
   applyBody; _—→[_]_; _—↠[_]_; ↠-refl; ↠-step; pure-step;
   β-Λ; β-∀; β-gen; β-inst; β-reveal-∀; β-conceal-∀;
   id-reveal; id-conceal; conceal-reveal; ξ-reveal; ξ-conceal)
open import proof.TypeInTermSubst using
  (renameᵗ-wk-eq; renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.TypeSafety.Progress as Prog
import proof.Imprecision as PI
import proof.Consistency as PC
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
import proof.DGG.Inversion.SpineValueProof as SpineValueProof
open import proof.DGG.Catchup.InstInversionDef using
  (StructuralValueInstantiationᵀ)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (FuelStepSurface; ResidualCastBuilderᵀ; inst-alloc-decreaseᵀ; castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankProof
  using
    (_<ʳ_; rank-name<; rank-exp<; rank-length<;
     lambda-rank-decreases; reveal-rank-decreases;
     conceal-rank-decreases; cast-frame-rank-decreases;
     reveal-frame-value-rank-decreases;
     reveal-frame-value-rank-decreases-any;
     conceal-frame-value-rank-decreases;
     conceal-frame-value-rank-decreases-any;
     reveal-frame-id-rank-decreases;
     reveal-frame-conceal-rank-decreases;
     conceal-frame-id-rank-decreases)
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassProof
  using (all-cast-mass-decreases)
open import proof.DGG.Catchup.StructuralValueInstantiationCastProof
open import proof.DGG.Catchup.StructuralValueInstantiationAllCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationGenCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationInstCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationPendingCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationValueCastMassProof
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldEvidenceProof
open import proof.DGG.Catchup.StructuralWorldSmartLiftProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof
open import proof.DGG.Catchup.StructuralFrameOutcomeDef
open import proof.DGG.Catchup.StructuralFrameOutcomeProof
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralTargetSourceTransportProof
open import proof.DGG.Catchup.StructuralTargetFrameDecompositionProof
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (value-no-step)
open import proof.DGG.Catchup.StructuralTargetInstPeelProof
open import proof.DGG.Catchup.StructuralTargetLambdaPeelProof
open import proof.DGG.Catchup.StructuralTargetAllPeelProof
open import proof.DGG.Catchup.StructuralTargetGenPeelProof
open import proof.DGG.Catchup.StructuralTargetRevealPeelProof
open import proof.DGG.Catchup.StructuralTargetConcealPeelProof
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralInstantiationDescentProof
open import proof.DGG.Catchup.StructuralSourceLambdaReplayProof
open import proof.DGG.Catchup.StructuralSourceRebaseReplayProof
open import proof.DGG.Catchup.StructuralAllDescentProof
open import proof.DGG.Catchup.StructuralGenDescentProof
open import proof.DGG.Catchup.StructuralInstDescentProof
open import proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralStrictViewSurfaceDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Inversion.SpineValueDef using
  (AllValueView; allv-Λ; allv-∀; allv-gen; allv-reveal;
   allv-conceal)


RankTuple : Set
RankTuple = ℕ × (ℕ × ℕ)


rank-tuple : InstantiationRank → RankTuple
rank-tuple (inst-rank names exp length) = names , (exp , length)


_<ʳlex_ : RankTuple → RankTuple → Set
_<ʳlex_ =
  ProductLex.×-Lex _≡_ _<_
    (ProductLex.×-Lex _≡_ _<_ _<_)


rank<→lex : ∀ {r r′}
  → r <ʳ r′
  → rank-tuple r <ʳlex rank-tuple r′
rank<→lex (rank-name< names<) = inj₁ names<
rank<→lex (rank-exp< names≡ exp<) =
  inj₂ (names≡ , inj₁ exp<)
rank<→lex (rank-length< names≡ exp≡ length<) =
  inj₂ (names≡ , inj₂ (exp≡ , length<))


rank-lex-wf : WF.WellFounded _<ʳlex_
rank-lex-wf =
  ProductLex.×-wellFounded NatInduction.<-wellFounded
    (ProductLex.×-wellFounded NatInduction.<-wellFounded
      NatInduction.<-wellFounded)


derivSize : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ p
  → ℕ
derivSize (CTI2.x⊑x² x) = zero
derivSize (CTI2.ƛ⊑ƛ² rel) = suc (suc (derivSize rel))
derivSize (CTI2.·⊑·² rel₁ rel₂) =
  suc (suc (derivSize rel₁ + derivSize rel₂))
derivSize (CTI2.Λ⊑Λ² liftγ vV vV′ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV target⊢ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.•⊑•² p∀ rel q r) =
  suc (suc (derivSize rel))
derivSize (CTI2.•⊑² p∀ rel q r) =
  suc (suc (derivSize rel))
derivSize (CTI2.κ⊑κ² κ p) = zero
derivSize (CTI2.cast⊑cast² c c′ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.⊑cast² c′ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.⊑reveal² mono rb sc c⊢ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.⊑conceal² mono rb sc c⊢ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.cast⊑² c rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.reveal⊑² mono rb sc c⊢ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.conceal⊑²-seal-star-open no-target mono rb sc c⊢ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.conceal⊑²-source-ok ok mono rb sc c⊢ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.reveal⊑reveal² mono rb sc c⊢ c⊢′ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.conceal⊑conceal² ok mono rb sc c⊢ c⊢′ rel q) =
  suc (suc (derivSize rel))
derivSize (CTI2.packaged-seal-star² ok mono rb sc c⊢ c⊢′ rel★ rel q) =
  suc (suc (derivSize rel★ + derivSize rel))
derivSize (CTI2.blame⊑² target⊢ p) = zero
derivSize (CTI2.⊕⊑⊕² op rel₁ rel₂ r) =
  suc (suc (derivSize rel₁ + derivSize rel₂))


data WorkerPhase : Set where
  spine-phase name-phase : WorkerPhase


phaseDerivSize : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → WorkerPhase
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ p
  → ℕ
phaseDerivSize spine-phase rel = suc (derivSize rel)
phaseDerivSize name-phase rel = derivSize rel


TerminationMeasure : Set
TerminationMeasure = ℕ × (RankTuple × ℕ)


_<ᵐ_ : TerminationMeasure → TerminationMeasure → Set
_<ᵐ_ =
  ProductLex.×-Lex _≡_ _<_
    (ProductLex.×-Lex _≡_ _<ʳlex_ _<_)


terminationMeasure : ∀ {phase Δ}
    {V : Term Δ} {A B : Ty Δ}
    {Δᴸ Δᵂ} {W : CTX.World Δᴸ Δ Δᵂ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ}
    {Aᴸ : Ty Δᴸ} {p : Aᴸ CTX.⊑ᵂ⟨ W ⟩ A}
  → (vV : Value V)
  → (spine : InstantiationSpine A B)
  → (rel : W CTI2.∣ γ ⊢² M ⊑ V ∶ p)
  → TerminationMeasure
terminationMeasure {phase = phase} vV spine rel =
  pendingCastMass vV spine ,
  (rank-tuple (pendingRank vV spine) , phaseDerivSize phase rel)


termination-measure-wf : WF.WellFounded _<ᵐ_
termination-measure-wf =
  ProductLex.×-wellFounded NatInduction.<-wellFounded
    (ProductLex.×-wellFounded rank-lex-wf
      NatInduction.<-wellFounded)


termination-measure-access : ∀ m → Acc _<ᵐ_ m
termination-measure-access = termination-measure-wf


measure-mass< : ∀ {m m′ r r′ s s′}
  → m < m′
  → (m , (r , s)) <ᵐ (m′ , (r′ , s′))
measure-mass< mass< = inj₁ mass<


measure-rank< : ∀ {m m′ r r′ s s′}
  → m ≡ m′
  → r <ʳlex r′
  → (m , (r , s)) <ᵐ (m′ , (r′ , s′))
measure-rank< mass≡ rank< =
  inj₂ (mass≡ , inj₁ rank<)


measure-source< : ∀ {m r s s′}
  → s < s′
  → (m , (r , s)) <ᵐ (m , (r , s′))
measure-source< size< = inj₂ (refl , inj₂ (refl , size<))


StructuralValueSpineInstantiationAccᵀ : Set₁
StructuralValueSpineInstantiationAccᵀ =
  StructuralStrictViewSurfaces
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {C₀ E : Ty Δᴿ}
    {p : A CTX.⊑ᵂ⟨ W ⟩ C₀}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → FuelStepSurface fuel
  → ResidualCastBuilderᵀ
  → inst-alloc-decreaseᵀ
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → (rel : W CTI2.∣ γ ⊢² M ⊑ V ∶ p)
  → Value M
  → (vV : Value V)
  → (spine : InstantiationSpine C₀ E)
  → TargetFrameAbsorptionChain W γ A spine q
  → SpineTypedʷ {fuel = fuel} W spine
  → Acc _<ᵐ_ (terminationMeasure {phase = spine-phase} vV spine rel)
  → (target : StructuralTargetInstantiationPackage W V spine)
  → StructuralTargetInstantiationPackage.W′ target CTI2.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q


StructuralNameInstantiationAccᵀ : Set₁
StructuralNameInstantiationAccᵀ =
  StructuralStrictViewSurfaces
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTX.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → FuelStepSurface fuel
  → ResidualCastBuilderᵀ
  → inst-alloc-decreaseᵀ
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → (rel : W CTI2.∣ γ ⊢² M ⊑ V ∶ p)
  → Value M
  → (vV : Value V)
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → Acc _<ᵐ_ (terminationMeasure {phase = name-phase} vV
      (name-type-app-frame B X refl refl ▻ⁱ spine) rel)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → StructuralTargetInstantiationPackage.W′ target CTI2.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q


StructuralNameInstantiationEqualᵀ : Set₁
StructuralNameInstantiationEqualᵀ =
  StructuralValueSpineInstantiationAccᵀ


StructuralNameInstantiationStrictᵀ : Set₁
StructuralNameInstantiationStrictᵀ =
  StructuralValueSpineInstantiationAccᵀ


rel-⊑-unique : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A CTX.⊑ᵂ⟨ W ⟩ B}
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ p
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ q
rel-⊑-unique {W = W} {γ = γ} {p = p} {q = q} rel =
  subst≡ (λ r → W CTI2.∣ γ ⊢² _ ⊑ _ ∶ r)
    (PI.⊑-unique p q) rel


rel-target-transportᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ p
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ subst≡ (A CTX.⊑ᵂ⟨ W ⟩_) eq p
rel-target-transportᴿ refl rel = rel


type-frame-rank-decreases : ∀ {Δ A B E V}
    {eq : A ≡ B}
    (vV : Value {Δ = Δ} V)
    (spine : InstantiationSpine B E)
  → pendingRank vV spine <ʳ
      pendingRank vV (type-transport-frame eq ▻ⁱ spine)
type-frame-rank-decreases vV spine =
  rank-length< refl refl (n<1+n (spineLength spine))


all-primary-decreases-at : ∀ {Δ} {μ : Env∼ Δ}
    {A B : Ty (suc Δ)} {E : Ty Δ} {V}
    (vV : CT.Value {Δ = Δ} V)
    (d : extᵐ μ ⊢ A ∼ B)
    (X : TyVar Δ)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingCastMass vV
      (name-type-app-frame A X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine) <
      pendingCastMass (vV CT.《 CT.all {c = d} 》)
        (name-type-app-frame B X refl refl ▻ⁱ spine)
all-primary-decreases-at vV d X spine
    rewrite spine-cast-mass-map keep spine =
  all-cast-mass-decreases vV spine (PC.castSize-open-var-≤ d X)


value-cast-mass-irrel : ∀ {Δ} {V : Term Δ}
  → (vV vV′ : Value V)
  → valueCastMass vV ≡ valueCastMass vV′
value-cast-mass-irrel (CT.ƛ N) (CT.ƛ N′) = refl
value-cast-mass-irrel (CT.Λ vV) (CT.Λ vV′) =
  value-cast-mass-irrel vV vV′
value-cast-mass-irrel (CT.$ k) (CT.$ k′) = refl
value-cast-mass-irrel (vV CT.《 inert 》) (vV′ CT.《 inert′ 》) =
  cong₂ _+_ (value-cast-mass-irrel vV vV′) refl
value-cast-mass-irrel (vV CT.↑ rv) (vV′ CT.↑ rv′) =
  value-cast-mass-irrel vV vV′
value-cast-mass-irrel (vV CT.↓ cv) (vV′ CT.↓ cv′) =
  value-cast-mass-irrel vV vV′


cast-frame-mass-equal : ∀ {Δ A B E V μ}
    {c : μ ⊢ A ∼ B}
    (vV : Value {Δ = Δ} V)
    (inert : Inert c)
    (spine : InstantiationSpine B E)
  → pendingCastMass (vV CT.《 inert 》) spine ≡
      pendingCastMass vV (cast-frame c ▻ⁱ spine)
cast-frame-mass-equal {c = c} vV inert spine =
  +-assoc (valueCastMass vV) (castSize c) (spineCastMass spine)


pending-cast-mass-map-keep : ∀ {Δ A B V}
    (vV : Value {Δ = Δ} V)
    (spine : InstantiationSpine A B)
  → pendingCastMass vV (mapInstantiationSpine keep spine) ≡
      pendingCastMass vV spine
pending-cast-mass-map-keep vV spine =
  cong₂ _+_ refl (spine-cast-mass-map keep spine)


reveal-frame-value-mass-equal-any : ∀ {Δ A B E V}
    {c : Conv↑ Δ A B}
    (vV : Value V)
    (child : Value (V CT.↑ c))
    (spine : InstantiationSpine B E)
  → pendingCastMass child spine ≡
      pendingCastMass vV (reveal-frame c ▻ⁱ spine)
reveal-frame-value-mass-equal-any vV (vW CT.↑ rv) spine
    rewrite value-cast-mass-irrel vW vV =
  refl


conceal-frame-value-mass-equal-any : ∀ {Δ A B E V}
    {c : Conv↓ Δ A B}
    (vV : Value V)
    (child : Value (V CT.↓ c))
    (spine : InstantiationSpine B E)
  → pendingCastMass child spine ≡
      pendingCastMass vV (conceal-frame c ▻ⁱ spine)
conceal-frame-value-mass-equal-any vV (vW CT.↓ cv) spine
    rewrite value-cast-mass-irrel vW vV =
  refl


safe-inst-child-spine : ∀ {Δ} {μ : Env∼ Δ}
    {A : Ty (suc Δ)} {B E : Ty Δ}
    {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
  → InstantiationSpine B E
  → InstantiationSpine (applyTy (bind ★) (`∀ A)) (applyTy (bind ★) E)
safe-inst-child-spine {A = A} {B = B} {c = c} spine =
  name-type-app-frame (applyBody (bind ★) A) Fin.zero refl refl ▻ⁱ
  type-transport-frame (applyBody-open-zero A) ▻ⁱ
  reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
  type-transport-frame
    (trans (replace-zero-open A ★)
      (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
  cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
  type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
  mapInstantiationSpine (bind ★) spine


lambda-child-spine : ∀ {Δ} {B : Ty (suc Δ)} {E : Ty Δ}
    {X : TyVar Δ}
  → InstantiationSpine (B [ ＇ X ]ᵗ) E
  → InstantiationSpine
      (replaceTy Fin.zero (⇑ᵗ (＇ X)) B)
      (applyTy (bind (＇ X)) E)
lambda-child-spine {B = B} {X = X} spine =
  type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
  mapInstantiationSpine (bind (＇ X)) spine


all-cast-child-spine : ∀ {Δ} {μ : Env∼ Δ}
    {B C : Ty (suc Δ)} {E : Ty Δ} {X : TyVar Δ}
    {d : extᵐ μ ⊢ B ∼ C}
  → InstantiationSpine (C [ ＇ X ]ᵗ) E
  → InstantiationSpine (`∀ B) E
all-cast-child-spine {B = B} {X = X} {d = d} spine =
  name-type-app-frame B X refl refl ▻ⁱ
  cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
  mapInstantiationSpine keep spine


gen-child-spine : ∀ {Δ} {μ : Env∼ Δ}
    {A E : Ty Δ} {B : Ty (suc Δ)} {X : TyVar Δ}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
  → InstantiationSpine (B [ ＇ X ]ᵗ) E
  → InstantiationSpine (⇑ᵗ A) (applyTy (bind (＇ X)) E)
gen-child-spine {B = B} {X = X} {c = c} spine =
  cast-frame c ▻ⁱ
  reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
  type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
  mapInstantiationSpine (bind (＇ X)) spine


reveal-child-spine : ∀ {Δ} {B C : Ty (suc Δ)} {E : Ty Δ}
    {X : TyVar Δ} {c : Conv↑ (suc Δ) C B}
  → InstantiationSpine (B [ ＇ X ]ᵗ) E
  → InstantiationSpine (applyTy (bind (＇ X)) (`∀ C))
      (applyTy (bind (＇ X)) E)
reveal-child-spine {B = B} {C = C} {X = X} {c = c} spine =
  name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
    refl refl ▻ⁱ
  type-transport-frame (applyBody-open-zero C) ▻ⁱ
  reveal-frame c ▻ⁱ
  reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
  type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
  mapInstantiationSpine (bind (＇ X)) spine


conceal-child-spine : ∀ {Δ} {B C : Ty (suc Δ)} {E : Ty Δ}
    {X : TyVar Δ} {c : Conv↓ (suc Δ) C B}
  → InstantiationSpine (B [ ＇ X ]ᵗ) E
  → InstantiationSpine (applyTy (bind (＇ X)) (`∀ C))
      (applyTy (bind (＇ X)) E)
conceal-child-spine {B = B} {C = C} {X = X} {c = c} spine =
  name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
    refl refl ▻ⁱ
  type-transport-frame (applyBody-open-zero C) ▻ⁱ
  conceal-frame c ▻ⁱ
  reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
  type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
  mapInstantiationSpine (bind (＇ X)) spine


lambda-child-mass-equal : ∀ {Δ} {B : Ty (suc Δ)}
    {E : Ty Δ} {V : Term (suc Δ)} {X : TyVar Δ}
    (vV : Value V)
    (vChild : Value (V CT.↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗))
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingCastMass vChild (lambda-child-spine {B = B} {X = X} spine) ≡
      pendingCastMass (CT.Λ vV)
        (name-type-app-frame B X refl refl ▻ⁱ spine)
lambda-child-mass-equal {X = X} vV (vW CT.↑ rv) spine
    rewrite value-cast-mass-irrel vW vV
          | spine-cast-mass-map (bind (＇ X)) spine =
  refl


reveal-strict-child-mass-equal : ∀ {Δ} {B C : Ty (suc Δ)}
    {E : Ty Δ} {V : Term Δ} {X : TyVar Δ}
    {c : Conv↑ (suc Δ) C B}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingCastMass (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
      (reveal-child-spine {X = X} {c = c} spine) ≡
      pendingCastMass (vV CT.↑ CT.all {c = c})
        (name-type-app-frame B X refl refl ▻ⁱ spine)
reveal-strict-child-mass-equal {X = X} vV spine
    rewrite value-cast-mass-rename wk↪ᵗ vV
          | spine-cast-mass-map (bind (＇ X)) spine =
  refl


conceal-strict-child-mass-equal : ∀ {Δ} {B C : Ty (suc Δ)}
    {E : Ty Δ} {V : Term Δ} {X : TyVar Δ}
    {c : Conv↓ (suc Δ) C B}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingCastMass (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
      (conceal-child-spine {X = X} {c = c} spine) ≡
      pendingCastMass (vV CT.↓ CT.all {c = c})
        (name-type-app-frame B X refl refl ▻ⁱ spine)
conceal-strict-child-mass-equal {X = X} vV spine
    rewrite value-cast-mass-rename wk↪ᵗ vV
          | spine-cast-mass-map (bind (＇ X)) spine =
  refl


all-view→all-value-view : ∀ {Δ} {B : Ty (suc Δ)} {V : Term Δ}
  → Prog.AllView B V
  → AllValueView V
all-view→all-value-view (Prog.av-Λ vV refl) =
  allv-Λ vV refl
all-view→all-value-view (Prog.av-∀ vV refl) =
  allv-∀ vV refl
all-view→all-value-view (Prog.av-gen vV A≢★ safe refl) =
  allv-gen vV A≢★ safe refl
all-view→all-value-view (Prog.av-reveal vV refl) =
  allv-reveal vV refl
all-view→all-value-view (Prog.av-conceal vV refl) =
  allv-conceal vV refl


relation-all-value-view : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {p : A CTX.⊑ᵂ⟨ W ⟩ `∀ B}
  → Value V
  → (rel : W CTI2.∣ γ ⊢² M ⊑ V ∶ p)
  → AllValueView V
relation-all-value-view vV rel =
  all-view→all-value-view
    (Prog.canonical-∀ vV (CTI2T.target-typing² rel))


target-empty-final-relation : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A CTX.⊑ᵂ⟨ W ⟩ B}
  → Value V
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → (target : StructuralTargetInstantiationPackage W V ([]ⁱ {A = B}))
  → StructuralTargetInstantiationPackage.W′ target CTI2.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q
target-empty-final-relation {W = W} {γ = γ} vV rel target
    with StructuralTargetInstantiationPackage.post-reduction target
target-empty-final-relation {W = W} {γ = γ} vV rel target
    | ↠-refl
    with StructuralTargetInstantiationPackage.structural-ext target
target-empty-final-relation {W = W} {γ = γ} vV rel target
    | ↠-refl | structural-[] =
  subst≡
    (λ γ′ → W CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
    (sym (ECR.mapCtxᴿ-same γ))
    (rel-⊑-unique rel)
target-empty-final-relation vV rel target | ↠-step step rest =
  ⊥-elim (value-no-step vV step)


mapCtx-target-insert-bind : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ (suc Δᴿ) Δ′}
    {π : Δ ↪ᵗ Δ′} {R : Ty Δᴿ}
  → (ins : TE.TargetInsert wk↪ᵗ π W W′)
  → (follows : CTX.targetStoreʷ W′ ≡
      applyStores (bind R ∷ []) (CTX.targetStoreʷ W))
  → (γ : CTX.CtxImp W)
  → ECR.mapCtxᴿ (target-insert-bind-world-extendᴿ ins follows) γ ≡
      TE.mapCtxᵀ ins γ
mapCtx-target-insert-bind ins follows List.[] = refl
mapCtx-target-insert-bind {W′ = W′} {R = R} ins follows
    (CTX.ctx-imp A B p List.∷ γ) =
  cong₂ List._∷_ entry-eq (mapCtx-target-insert-bind ins follows γ)
  where
  ext = target-insert-bind-world-extendᴿ ins follows

  entry-eq :
      CTX.ctx-imp A (⇑ᵗ B) (ECR.transport⊑ᵂ ext p) ≡
      CTX.ctx-imp A (renameᵗ (toRenameᵗ wk↪ᵗ) B)
        (TE.transport⊑ᵂ ins p)
  entry-eq =
    TE.ctx-imp-target-eq {W = W′}
      {A = A} {B = ⇑ᵗ B}
      {B′ = renameᵗ (toRenameᵗ wk↪ᵗ) B}
      {p = ECR.transport⊑ᵂ ext p}
      {q = TE.transport⊑ᵂ ins p}
      (sym (renameᵗ-wk-eq B))


target-insert-bind-relation : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ (suc Δᴿ) Δ′}
    {π : Δ ↪ᵗ Δ′} {R : Ty Δᴿ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (ins : TE.TargetInsert wk↪ᵗ π W W′)
  → (follows : CTX.targetStoreʷ W′ ≡
      applyStores (bind R ∷ []) (CTX.targetStoreʷ W))
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → W′ CTI2.∣
      ECR.mapCtxᴿ (target-insert-bind-world-extendᴿ ins follows) γ
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ V ∶
        ECR.transport⊑ᵂ (target-insert-bind-world-extendᴿ ins follows) p
target-insert-bind-relation {γ = γ} {B = B} {p = p}
    ins follows rel =
  subst≡
    (λ γ′ → _ CTI2.∣ γ′ ⊢² _ ⊑ _ ∶
      ECR.transport⊑ᵂ ext p)
    (sym (mapCtx-target-insert-bind ins follows γ))
    (TE.⊢²-retargetᴿ {q = ECR.transport⊑ᵂ ext p}
      (renameᵗ-wk-eq B) (TE.⊢²-target-insert ins rel))
  where
  ext = target-insert-bind-world-extendᴿ ins follows


structural-name-cast-equal :
  StructuralStrictViewSurfaces
  → StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
      {γ : CTX.CtxImp W}
      {U V : Term Δᴸ} {N : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ} {ν : Env∼ Δᴸ}
      {p : A CTX.⊑ᵂ⟨ W ⟩ `∀ B}
      {q : A′ CTX.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → ResidualCastBuilderᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W A′ E q)
    → StructuralNameChainPlan {fuel = fuel} W γ A′ E q plan
    → (c : ν ⊢ A ∼ A′)
    → Inert c
    → (prem : W CTI2.∣ γ ⊢² U ⊑ N ∶ p)
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ A′
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ᵐ_ (terminationMeasure {phase = spine-phase} vN
        (name-type-app-frame B X refl refl ▻ⁱ spine) prem)
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² U ⟨ c ⟩ ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-cast-equal surfaces worker {B = B} {X = X}
    fuel-step residual-cast-builder inst-decrease plan chain-plan c inert
    prem vU vN view spine chain typed access target
    with StructuralNamePostPlan.cast-child plan c
       | StructuralNameChainPlan.cast-child chain-plan c chain typed
structural-name-cast-equal surfaces worker {B = B} {X = X}
    fuel-step residual-cast-builder inst-decrease plan chain-plan c inert
    prem vU vN view spine chain typed access target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan) =
  structural-inert-cast-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    c inert
    (worker surfaces fuel-step residual-cast-builder inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed access target)


structural-name-plain-Λ-equal :
  StructuralStrictViewSurfaces
  → StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
      {γ : CTX.CtxImp W}
      {γᴸ : CTX.CtxImp (CTX.liftWorldLeft X⊑★ W)}
      {U : Term (suc Δᴸ)} {N : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ}
      {p : A CTX.⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ W ⟩ `∀ B}
      {q : `∀ A CTX.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → ResidualCastBuilderᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W (`∀ A) E q)
    → StructuralNameChainPlan {fuel = fuel} W γ (`∀ A) E q plan
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTX.LiftCtxᴸ X⊑★ γ γᴸ
    → (prem : CTX.liftWorldLeft X⊑★ W CTI2.∣ γᴸ
        ⊢² U ⊑ N ∶ p)
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ (`∀ A)
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ᵐ_ (terminationMeasure {phase = spine-phase} vN
        (name-type-app-frame B X refl refl ▻ⁱ spine) prem)
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² Λ U ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-plain-Λ-equal surfaces worker {γ = γ} {γᴸ = γᴸ}
    {B = B} {X = X}
    fuel-step residual-cast-builder inst-decrease plan chain-plan Anv z∈A
    liftγ prem vU vN view spine chain typed access target
    with StructuralNamePostPlan.plain-Λ-child plan refl
       | StructuralNameChainPlan.plain-Λ-child chain-plan refl liftγ
           chain typed
structural-name-plain-Λ-equal surfaces worker {γ = γ} {γᴸ = γᴸ}
    {B = B} {X = X}
    fuel-step residual-cast-builder inst-decrease plan chain-plan Anv z∈A
    liftγ prem vU vN view spine chain typed access target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan) =
  structural-Λ-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    Anv z∈A liftγ vU target⊢ child-rel
  where
  targetᴸ = structural-target-lift-left X⊑★ target

  child-rel =
    worker surfaces fuel-step residual-cast-builder inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed access targetᴸ

  liftγ′ =
    mapCtxᴿ-liftCtxᴸ
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext target))
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext targetᴸ))
      liftγ

  target⊢ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (liftCtxᴸ-target-ctx liftγ′)
      (CTI2T.target-typing² child-rel)


structural-name-smart-Λ-equal :
  StructuralStrictViewSurfaces
  → StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ Δᵐ}
      {W : CTX.World Δᴸ Δᴿ Δ}
      {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
      {γ : CTX.CtxImp W} {γᵐ : CTX.CtxImp Wᵐ}
      {U : Term (suc Δᴸ)} {N : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ}
      {p : A CTX.⊑ᵂ⟨ Wᵐ ⟩ `∀ B}
      {q : `∀ A CTX.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → ResidualCastBuilderᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W (`∀ A) E q)
    → StructuralNameChainPlan {fuel = fuel} W γ (`∀ A) E q plan
    → NonVar A
    → Fin.zero ∈ᵗ A
    → (liftW : CTX.SmartCommaLiftᴸ W Wᵐ)
    → CTX.SmartLiftCtxᴸ γ γᵐ
    → (prem : Wᵐ CTI2.∣ γᵐ ⊢² U ⊑ N ∶ p)
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ (`∀ A)
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ᵐ_ (terminationMeasure {phase = spine-phase} vN
        (name-type-app-frame B X refl refl ▻ⁱ spine) prem)
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² Λ U ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-smart-Λ-equal surfaces worker {γ = γ} {γᵐ = γᵐ}
    {B = B} {X = X}
    fuel-step residual-cast-builder inst-decrease plan chain-plan Anv z∈A
    liftW liftγ prem vU vN view spine chain typed access target
    with StructuralNamePostPlan.smart-Λ-child plan refl liftW
       | StructuralNameChainPlan.smart-Λ-child chain-plan refl liftW
           liftγ chain typed
structural-name-smart-Λ-equal surfaces worker {γ = γ} {γᵐ = γᵐ}
    {B = B} {X = X}
    fuel-step residual-cast-builder inst-decrease plan chain-plan Anv z∈A
    liftW liftγ prem vU vN view spine chain typed access target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan)
    with structural-smart-liftᴸ
      (StructuralTargetInstantiationPackage.structural-ext target)
      liftW
structural-name-smart-Λ-equal surfaces worker {γ = γ} {γᵐ = γᵐ}
    {B = B} {X = X}
    fuel-step residual-cast-builder inst-decrease plan chain-plan Anv z∈A
    liftW liftγ prem vU vN view spine chain typed access target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan)
    | record { premise-plan = planᵐ ; post-lift = liftW′ } =
  CTI2.Λ⊑²-smart-comma Anv z∈A liftW′ liftγ′ vU target⊢
    child-rel
    (ECR.transport⊑ᵂ
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext target))
      _)
  where
  targetᵐ = record
    { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ target
    ; χs = StructuralTargetInstantiationPackage.χs target
    ; Δ′ = _
    ; W′ = _
    ; structural-ext = planᵐ
    ; final = StructuralTargetInstantiationPackage.final target
    ; final-value =
        StructuralTargetInstantiationPackage.final-value target
    ; post-reduction =
        StructuralTargetInstantiationPackage.post-reduction target
    }

  child-rel =
    worker surfaces fuel-step residual-cast-builder inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed access targetᵐ

  liftγ′ =
    mapCtxᴿ-smartLiftCtxᴸ
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext target))
      (structural-world-extendᴿ planᵐ)
      liftγ

  postTarget⊢ =
    CTI2T.target-typing² child-rel

  target⊢ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (smartLiftCtxᴸ-target-ctx liftγ′)
      (subst≡ (λ Σ → ⟨ _ , Σ , _ ⟩ ⊢ _ ⦂ _)
        (smartCommaLift-target-store liftW′)
        postTarget⊢)


structural-name-reveal-equal :
  StructuralStrictViewSurfaces
  → StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ}
      {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
      {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
      {U : Term Δᴸ} {N : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ?}
      {c : Conv↑ Δᴸ A A′}
      {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
      {q : A′ CTX.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → ResidualCastBuilderᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W A′ E q)
    → StructuralNameChainPlan {fuel = fuel} W γ A′ E q plan
    → CTX.ImpEnvMono W Wᵖ
    → (rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?)
    → CTX.SameCtx γ γᵖ
    → CTX.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c
    → (prem : Wᵖ CTI2.∣ γᵖ ⊢² U ⊑ N ∶ p)
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ A′
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ᵐ_ (terminationMeasure {phase = spine-phase} vN
        (name-type-app-frame B X refl refl ▻ⁱ spine) prem)
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² U ↑ c ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-reveal-equal surfaces worker {B = B} {X = X} {c = c}
    fuel-step residual-cast-builder inst-decrease plan chain-plan mono rb sc
    c⊢ prem vU vN view spine chain typed access target
    with StructuralNamePostPlan.reveal-child plan {c = c} rb
       | StructuralNameChainPlan.reveal-child chain-plan {c = c} rb sc
           chain typed
structural-name-reveal-equal surfaces worker {B = B} {X = X} {c = c}
    fuel-step residual-cast-builder inst-decrease plan chain-plan mono rb sc
    c⊢ prem vU vN view spine chain typed access target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan) =
  structural-reveal-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    mono rb sc c⊢
    (worker surfaces fuel-step residual-cast-builder inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed access
      (structural-target-rebase-left rb target))


mutual

  structural-value-spine-instantiation-acc :
    StructuralValueSpineInstantiationAccᵀ
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      []ⁱ tfa-[] st-[] (WF.acc smaller) target =
    target-empty-final-relation vV rel target
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (type-transport-frame eq ▻ⁱ spine) (tfa-type chain)
      (st-type typed) (WF.acc smaller) target =
    child-rel
    where
    child-target = structural-target-frame-value-peel vV target

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan
        (rel-target-transportᴿ eq rel) vM vV spine chain typed
        (smaller
          (measure-rank< refl
            (rank<→lex
              (type-frame-rank-decreases {eq = eq} vV spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      (tfa-name chain) (st-name typed) (WF.acc smaller) target =
    structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM vV
      (relation-all-value-view vV rel) spine (tfa-name chain)
      (st-name typed)
      (smaller (measure-source< (n<1+n (derivSize rel))))
      target
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame {A = B₀} {B = C} c ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast (cast-inert inert) typed-tail) (WF.acc smaller) target
      with target-frame-cast-absorption chain rel
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame {A = B₀} {B = C} c ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast (cast-inert inert) typed-tail) (WF.acc smaller) target
      | qC′ , rel-cast =
    child-rel
    where
    child-value = vV CT.《 inert 》
    child-target = structural-target-frame-value-peel child-value target

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan rel-cast vM
        child-value spine tail typed-tail
        (smaller
          (measure-rank< (cast-frame-mass-equal vV inert spine)
            (rank<→lex (cast-frame-rank-decreases vV inert spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame (c ↦ d) ▻ⁱ spine) chain@(tfa-cast qC tail)
      typed@(st-cast (cast-safe CT.safe-⇒ parent< parent-prov) typed-tail)
      (WF.acc smaller) target
      with target-frame-cast-absorption chain rel
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame (c ↦ d) ▻ⁱ spine) chain@(tfa-cast qC tail)
      typed@(st-cast (cast-safe CT.safe-⇒ parent< parent-prov) typed-tail)
      (WF.acc smaller) target
      | qC′ , rel-cast =
    child-rel
    where
    child-value = vV CT.《 CT.fun 》
    child-target = structural-target-frame-value-peel child-value target

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan rel-cast vM
        child-value spine tail typed-tail
        (smaller
          (measure-rank< (cast-frame-mass-equal {c = c ↦ d} vV CT.fun spine)
            (rank<→lex
              (cast-frame-rank-decreases {c = c ↦ d} vV CT.fun spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame (∀ᶜ c) ▻ⁱ spine) chain@(tfa-cast qC tail)
      typed@(st-cast (cast-safe CT.safe-∀ parent< parent-prov) typed-tail)
      (WF.acc smaller) target
      with target-frame-cast-absorption chain rel
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame (∀ᶜ c) ▻ⁱ spine) chain@(tfa-cast qC tail)
      typed@(st-cast (cast-safe CT.safe-∀ parent< parent-prov) typed-tail)
      (WF.acc smaller) target
      | qC′ , rel-cast =
    child-rel
    where
    child-value = vV CT.《 CT.all 》
    child-target = structural-target-frame-value-peel child-value target

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan rel-cast vM
        child-value spine tail typed-tail
        (smaller
          (measure-rank< (cast-frame-mass-equal vV CT.all spine)
            (rank<→lex
              (cast-frame-rank-decreases {c = ∀ᶜ c} vV CT.all spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame ((gen c) A≢★) ▻ⁱ spine) chain@(tfa-cast qC tail)
      typed@(st-cast (cast-safe (CT.safe-gen A≢★′ safe)
        parent< parent-prov) typed-tail)
      (WF.acc smaller) target
      with target-frame-cast-absorption chain rel
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame ((gen c) A≢★) ▻ⁱ spine) chain@(tfa-cast qC tail)
      typed@(st-cast (cast-safe (CT.safe-gen A≢★′ safe)
        parent< parent-prov) typed-tail)
      (WF.acc smaller) target
      | qC′ , rel-cast =
    child-rel
    where
    child-inert = CT.genᵥ A≢★ safe
    child-value = vV CT.《 child-inert 》
    child-target = structural-target-frame-value-peel child-value target

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan rel-cast vM
        child-value spine tail typed-tail
        (smaller
          (measure-rank< (cast-frame-mass-equal vV child-inert spine)
            (rank<→lex
              (cast-frame-rank-decreases {c = (gen c) A≢★} vV
                child-inert spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame {A = B₀} {B = C} c ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast {c = .c}
        (cast-residual residual<fuel residual-prov)
        typed-tail)
      (WF.acc smaller) target
      with target-frame-cast-absorption chain rel
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame {A = B₀} {B = C} c ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast {c = .c}
        (cast-residual residual<fuel residual-prov)
        typed-tail)
      (WF.acc smaller) target
      | qC′ , rel-cast
        with residual-cast-stop-package {B = B₀} {C = C}
          {q = qC′} {c = c}
          fuel-step residual-cast-builder
          rel vM vV residual<fuel
          (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
             {W = W′} {Aₛ = Aₛ} {p = p} {q = q} →
             residual-prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
               {χs = χs} {W = W′} {Aₛ = Aₛ}
               {p = p} {q = q})
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame {A = B₀} {B = C} c ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast {c = .c}
        (cast-residual residual<fuel residual-prov)
        typed-tail)
      (WF.acc smaller) target
      | qC′ , rel-cast
      | record { Δᴿ′ = Δᴿ′ ; χs = χs ; Δ′ = Δ′ ; W′ = W′
          ; ext = ext ; final = N ; final-value = vN
          ; post-reduction = post↠ ; final-relation = stop-rel }
        with StructuralNameChainPlan.residual-tail-child chain-plan
          {B = B₀} {C = C} {c = c} {qC = qC′}
          vV residual<fuel
          (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
             {W = W′} {Aₛ = Aₛ} {p = p} {q = q} →
             residual-prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
               {χs = χs} {W = W′} {Aₛ = Aₛ}
               {p = p} {q = q})
          chain typed
        χs W′ ext N vN post↠ stop-rel target
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame {A = B₀} {B = C} c ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast (cast-residual residual<fuel residual-prov) typed-tail)
      (WF.acc smaller) target
      | qC′ , rel-cast
      | record { Δᴿ′ = Δᴿ′ ; χs = χs ; Δ′ = Δ′ ; W′ = W′
          ; ext = ext ; final = N ; final-value = vN
          ; post-reduction = post↠ ; final-relation = stop-rel }
      | child-spine , child-plan , child-chain-plan , child-chain ,
        child-typed , child-target , mass< , finish =
      finish
        (structural-value-spine-instantiation-acc surfaces fuel-step
          residual-cast-builder inst-decrease child-plan child-chain-plan
          stop-rel vM vN child-spine child-chain child-typed
          (smaller (measure-mass< mass<))
          child-target)
  structural-value-spine-instantiation-acc surfaces {W = W} fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame (inst_ {A = A} {B = B} c B≢★) ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast {c = .((inst c) B≢★)}
        (cast-safe (CT.safe-inst B≢★′)
        parent< parent-prov) typed-tail) (WF.acc smaller) target
      with structural-target-inst-peel vV B≢★ spine target
  structural-value-spine-instantiation-acc surfaces {W = W} fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame (inst_ {A = A} {B = B} c B≢★) ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast {c = .((inst c) B≢★)}
        (cast-safe (CT.safe-inst B≢★′)
        parent< parent-prov) typed-tail) (WF.acc smaller) target
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      with StructuralNamePostPlan.target-bind-child plan ins follows
         | StructuralNameChainPlan.target-bind-child chain-plan ins follows
             (safe-inst-child-spine {A = A} {B = B} {c = c} spine)
  structural-value-spine-instantiation-acc surfaces {W = W} fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (cast-frame (inst_ {A = A} {B = B} c B≢★) ▻ⁱ spine)
      chain@(tfa-cast qC tail)
      typed@(st-cast {c = .((inst c) B≢★)}
        (cast-safe (CT.safe-inst B≢★′)
        parent< parent-prov) typed-tail) (WF.acc smaller) target
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      | child-plan | child-chain , (child-typed′ , child-chain-plan) =
    finish-target child-final
    where
    child-value = renameᵗᵐ-preserves-Value wk↪ᵗ vV

    residual<fuel =
      ≤-trans (s≤s (inst-decrease {c = c} B≢★)) parent<

    residual-prov =
      inst-residual-frame-provenance {A = A} {B = B} {c = c} B≢★

    child-typed =
      spine-typed-store-eq follows
        (spine-typed-inst-child {W = W} {A = A} {B = B} {c = c}
          {spine = spine}
          residual<fuel
          (λ {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ} {χs = χs}
             {W = W′} {Aₛ = Aₛ} {p = p} {q = q} →
             residual-prov {Δᴸ = Δᴸ} {Δ′ = Δ′} {Δᵂ = Δᵂ}
               {χs = χs} {W = W′} {Aₛ = Aₛ}
               {p = p} {q = q})
          typed-tail)

    child-rel =
      target-insert-bind-relation ins follows rel

    child-final =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease child-plan child-chain-plan
        child-rel vM child-value
        (safe-inst-child-spine {A = A} {B = B} {c = c} spine)
        child-chain child-typed
        (smaller
          (measure-mass< (inst-primary-decreases vV B≢★ spine)))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (reveal-frame c ▻ⁱ spine)
      chain@(tfa-reveal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-reveal c⊢′ typed-tail) (WF.acc smaller) target
      with transport rel
         | structural-reveal-frame-outcome c⊢′ (CTI2T.target-typing² rel) vV
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (reveal-frame c ▻ⁱ spine)
      chain@(tfa-reveal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-reveal c⊢′ typed-tail) (WF.acc smaller) target
      | pᵖ , relᵖ | structural-frame-value child-value =
    child-rel
    where
    child-target = structural-target-frame-value-peel child-value target

    rel-reveal = CTI2.⊑reveal² mono rb sc c⊢ relᵖ qC

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan rel-reveal vM
        child-value spine tail typed-tail
        (smaller
          (measure-rank<
            (reveal-frame-value-mass-equal-any vV child-value spine)
            (rank<→lex
              (reveal-frame-value-rank-decreases-any vV child-value spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (reveal-frame c ▻ⁱ spine)
      chain@(tfa-reveal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-reveal c⊢′ typed-tail) (WF.acc smaller) target
      | pᵖ , relᵖ
      | structural-frame-keep step@(pure-step (id-reveal vStep)) vN =
    finish-target child-rel
    where
    child-peel =
      structural-target-reveal-frame-keep-peel vV spine step vV target

    child-target = proj₁ child-peel

    finish-target = proj₂ child-peel

    rel-reveal = CTI2.⊑reveal² mono rb sc c⊢ relᵖ qC

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan
        (keep-rel rel-reveal step vV) vM vV
        (mapInstantiationSpine keep spine) keep-chain
        (spine-typed-map-keep typed-tail)
        (smaller
          (measure-rank< (pending-cast-mass-map-keep vV spine)
            (rank<→lex
              (reveal-frame-id-rank-decreases {c = c} vV spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM
      (vInner CT.↓ CT.seal {X = Xₛ} {R = Rₛ})
      (reveal-frame c ▻ⁱ spine)
      chain@(tfa-reveal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-reveal c⊢′ typed-tail) (WF.acc smaller) target
      | pᵖ , relᵖ
      | structural-frame-keep step@(pure-step (conceal-reveal vStep)) vN =
    finish-target child-rel
    where
    child-peel =
      structural-target-reveal-frame-keep-peel
        (vInner CT.↓ CT.seal) spine step vInner target

    child-target = proj₁ child-peel

    finish-target = proj₂ child-peel

    rel-reveal = CTI2.⊑reveal² mono rb sc c⊢ relᵖ qC

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan
        (keep-rel rel-reveal step vInner) vM vInner
        (mapInstantiationSpine keep spine) keep-chain
        (spine-typed-map-keep typed-tail)
        (smaller
          (measure-rank< (pending-cast-mass-map-keep vInner spine)
            (rank<→lex
              (reveal-frame-conceal-rank-decreases {c = c}
                {d = Conv.seal Xₛ Rₛ} vInner
                (CT.seal {X = Xₛ} {R = Rₛ}) spine))))
        child-target
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (reveal-frame c ▻ⁱ spine)
      chain@(tfa-reveal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-reveal c⊢′ typed-tail) (WF.acc smaller) target
      | pᵖ , relᵖ
      | structural-frame-keep (ξ-reveal step eq) vN =
    ⊥-elim (value-no-step vV step)

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (conceal-frame c ▻ⁱ spine)
      chain@(tfa-conceal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-conceal c⊢′ typed-tail) (WF.acc smaller) target
      with transport rel
         | structural-conceal-frame-outcome c⊢′ vV
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (conceal-frame c ▻ⁱ spine)
      chain@(tfa-conceal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-conceal c⊢′ typed-tail) (WF.acc smaller) target
      | pᵖ , relᵖ | structural-frame-value child-value =
    child-rel
    where
    child-target = structural-target-frame-value-peel child-value target

    rel-conceal = CTI2.⊑conceal² mono rb sc c⊢ relᵖ qC

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan rel-conceal vM
        child-value spine tail typed-tail
        (smaller
          (measure-rank<
            (conceal-frame-value-mass-equal-any vV child-value spine)
            (rank<→lex
              (conceal-frame-value-rank-decreases-any vV child-value spine))))
        child-target

  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (conceal-frame c ▻ⁱ spine)
      chain@(tfa-conceal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-conceal c⊢′ typed-tail) (WF.acc smaller) target
      | pᵖ , relᵖ
      | structural-frame-keep step@(pure-step (id-conceal vStep)) vN =
    finish-target child-rel
    where
    child-peel =
      structural-target-conceal-frame-keep-peel vV spine step vV target

    child-target = proj₁ child-peel

    finish-target = proj₂ child-peel

    rel-conceal = CTI2.⊑conceal² mono rb sc c⊢ relᵖ qC

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease plan chain-plan
        (keep-rel rel-conceal step vV) vM vV
        (mapInstantiationSpine keep spine) keep-chain
        (spine-typed-map-keep typed-tail)
        (smaller
          (measure-rank< (pending-cast-mass-map-keep vV spine)
            (rank<→lex
              (conceal-frame-id-rank-decreases {c = c} vV spine))))
        child-target
  structural-value-spine-instantiation-acc surfaces fuel-step
      residual-cast-builder inst-decrease plan chain-plan rel vM vV
      (conceal-frame c ▻ⁱ spine)
      chain@(tfa-conceal mono rb sc c⊢ transport qC keep-rel keep-chain tail)
      typed@(st-conceal c⊢′ typed-tail) (WF.acc smaller) target
      | pᵖ , relᵖ
      | structural-frame-keep (ξ-conceal step eq) vN =
    ⊥-elim (value-no-step vV step)



  structural-name-instantiation-acc : StructuralNameInstantiationAccᵀ
  structural-name-instantiation-acc surfaces {W = W} {γ = γ}
      {A = A′} {B = B} {E = E} {X = X} {q = qE}
      fuel-step residual-cast-builder
      inst-decrease plan chain-plan
      (CTI2.cast⊑² {A = A₀} {A′ = .A′} {B = .(`∀ B)}
        {p = p₀} c prem q)
      (vU CT.《 inert 》) vN view spine chain typed (WF.acc smaller) target
      with StructuralNamePostPlan.cast-child plan c
         | StructuralNameChainPlan.cast-child chain-plan c chain typed
  structural-name-instantiation-acc surfaces {W = W} {γ = γ}
      {A = A′} {B = B} {E = E} {X = X} {q = qE}
      fuel-step residual-cast-builder
      inst-decrease plan chain-plan
      (CTI2.cast⊑² {A = A₀} {A′ = .A′} {B = .(`∀ B)}
        {p = p₀} c prem q)
      (vU CT.《 inert 》) vN view spine chain typed (WF.acc smaller) target
      | q₀ , child-plan
      | child-chain , (child-typed , child-chain-plan) =
    structural-inert-cast-replay
      (StructuralTargetInstantiationPackage.structural-ext target)
      c inert
      (structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease child-plan child-chain-plan prem vU vN
        (name-type-app-frame B X refl refl ▻ⁱ spine)
        child-chain child-typed
        (smaller
          (measure-source< (n<1+n (suc (derivSize prem)))))
        target)
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan
      (CTI2.Λ⊑² Anv z∈A liftγ vU target⊢ prem q)
      (CT.Λ vU′) vN view spine chain typed (WF.acc smaller) target
      with StructuralNamePostPlan.plain-Λ-child plan refl
         | StructuralNameChainPlan.plain-Λ-child chain-plan refl liftγ
             chain typed
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder inst-decrease plan chain-plan
      (CTI2.Λ⊑² Anv z∈A liftγ vU target⊢ prem q)
      (CT.Λ vU′) vN view spine chain typed (WF.acc smaller) target
      | q₀ , child-plan
      | child-chain , (child-typed , child-chain-plan) =
    structural-Λ-replay
      (StructuralTargetInstantiationPackage.structural-ext target)
      Anv z∈A liftγ vU target⊢′ child-rel
    where
    targetᴸ = structural-target-lift-left X⊑★ target

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease child-plan child-chain-plan
        prem vU vN (name-type-app-frame B X refl refl ▻ⁱ spine)
        child-chain child-typed
        (smaller
          (measure-source< (n<1+n (suc (derivSize prem)))))
        targetᴸ

    liftγ′ =
      mapCtxᴿ-liftCtxᴸ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext targetᴸ))
        liftγ

    target⊢′ =
      subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (liftCtxᴸ-target-ctx liftγ′)
        (CTI2T.target-typing² child-rel)
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan
      (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vU target⊢ prem q)
      (CT.Λ vU′) vN view spine chain typed (WF.acc smaller) target
      with StructuralNamePostPlan.smart-Λ-child plan refl liftW
         | StructuralNameChainPlan.smart-Λ-child chain-plan refl liftW
             liftγ chain typed
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder inst-decrease plan chain-plan
      (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vU target⊢ prem q)
      (CT.Λ vU′) vN view spine chain typed (WF.acc smaller) target
      | q₀ , child-plan
      | child-chain , (child-typed , child-chain-plan)
      with structural-smart-liftᴸ
        (StructuralTargetInstantiationPackage.structural-ext target)
        liftW
  structural-name-instantiation-acc surfaces {γ = γ} {B = B} {X = X}
      fuel-step residual-cast-builder inst-decrease plan chain-plan
      (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vU target⊢ prem q)
      (CT.Λ vU′) vN view spine chain typed (WF.acc smaller) target
      | q₀ , child-plan
      | child-chain , (child-typed , child-chain-plan)
      | record { premise-plan = planᵐ ; post-lift = liftW′ } =
    CTI2.Λ⊑²-smart-comma Anv z∈A liftW′ liftγ′ vU target⊢′
      child-rel
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        _)
    where
    targetᵐ = record
      { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ target
      ; χs = StructuralTargetInstantiationPackage.χs target
      ; Δ′ = _
      ; W′ = _
      ; structural-ext = planᵐ
      ; final = StructuralTargetInstantiationPackage.final target
      ; final-value =
          StructuralTargetInstantiationPackage.final-value target
      ; post-reduction =
          StructuralTargetInstantiationPackage.post-reduction target
      }

    child-rel =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease child-plan child-chain-plan
        prem vU vN (name-type-app-frame B X refl refl ▻ⁱ spine)
        child-chain child-typed
        (smaller
          (measure-source< (n<1+n (suc (derivSize prem)))))
        targetᵐ

    liftγ′ =
      mapCtxᴿ-smartLiftCtxᴸ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        (structural-world-extendᴿ planᵐ)
        liftγ

    postTarget⊢ =
      CTI2T.target-typing² child-rel

    target⊢′ =
      subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (smartLiftCtxᴸ-target-ctx liftγ′)
        (subst≡ (λ Σ → ⟨ _ , Σ , _ ⟩ ⊢ _ ⦂ _)
          (smartCommaLift-target-store liftW′)
          postTarget⊢)
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan
      (CTI2.reveal⊑² {c = c} mono rb sc c⊢ prem q)
      (vU CT.↑ rv) vN view spine chain typed (WF.acc smaller) target
      with StructuralNamePostPlan.reveal-child plan {c = c} rb
         | StructuralNameChainPlan.reveal-child chain-plan {c = c} rb sc
             chain typed
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder inst-decrease plan chain-plan
      (CTI2.reveal⊑² {c = c} mono rb sc c⊢ prem q)
      (vU CT.↑ rv) vN view spine chain typed (WF.acc smaller) target
      | q₀ , child-plan
      | child-chain , (child-typed , child-chain-plan) =
    structural-reveal-replay
      (StructuralTargetInstantiationPackage.structural-ext target)
      mono rb sc c⊢
      (structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease child-plan child-chain-plan
        prem vU vN (name-type-app-frame B X refl refl ▻ⁱ spine)
        child-chain child-typed
        (smaller
          (measure-source< (n<1+n (suc (derivSize prem)))))
        (structural-target-rebase-left rb target))
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan
      (CTI2.conceal⊑²-seal-star-open {X = Xᴸ} no-target mono rb sc
        c⊢ prem q)
      (vU CT.↓ cv) vN view spine chain typed (WF.acc smaller) target
      with StructuralNamePostPlan.conceal-child plan
             {c = Conv.seal Xᴸ ★} rb
         | StructuralNameChainPlan.conceal-child chain-plan
             {c = Conv.seal Xᴸ ★} rb sc chain typed
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder inst-decrease plan chain-plan
      (CTI2.conceal⊑²-seal-star-open {X = Xᴸ} no-target mono rb sc
        c⊢ prem q)
      (vU CT.↓ cv) vN view spine chain typed (WF.acc smaller) target
      | q₀ , child-plan
      | child-chain , (child-typed , child-chain-plan) =
    structural-conceal-seal-star-open-replay
      (StructuralTargetInstantiationPackage.structural-ext target)
      mono rb sc c⊢
      (StructuralStrictViewSurfaces.conceal-equal-no-target surfaces
        rb no-target spine target)
      (structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease child-plan child-chain-plan
        prem vU vN (name-type-app-frame B X refl refl ▻ⁱ spine)
        child-chain child-typed
        (smaller
          (measure-source< (n<1+n (suc (derivSize prem)))))
        (structural-target-tag-rebase-left rb target))
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan
      (CTI2.conceal⊑²-source-ok {c = c} ok mono rb sc c⊢ prem q)
      (vU CT.↓ cv) vN view spine chain typed (WF.acc smaller) target
      with StructuralNamePostPlan.conceal-child plan {c = c} rb
         | StructuralNameChainPlan.conceal-child chain-plan {c = c} rb sc
             chain typed
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder inst-decrease plan chain-plan
      (CTI2.conceal⊑²-source-ok {c = c} ok mono rb sc c⊢ prem q)
      (vU CT.↓ cv) vN view spine chain typed (WF.acc smaller) target
      | q₀ , child-plan
      | child-chain , (child-typed , child-chain-plan) =
    structural-conceal-source-ok-replay
      (StructuralTargetInstantiationPackage.structural-ext target)
      mono rb sc c⊢
      (StructuralStrictViewSurfaces.conceal-equal-source-ok surfaces rb ok
        spine target)
      (structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease child-plan child-chain-plan
        prem vU vN (name-type-app-frame B X refl refl ▻ⁱ spine)
        child-chain child-typed
        (smaller
          (measure-source< (n<1+n (suc (derivSize prem)))))
        (structural-target-tag-rebase-left rb target))
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM (CT.Λ vV)
      (allv-Λ vV′ refl) spine chain typed (WF.acc smaller) target
      with structural-target-Λ-peel vV spine target
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM (CT.Λ vV)
      (allv-Λ vV′ refl) spine chain typed (WF.acc smaller) target
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      with StructuralStrictViewSurfaces.Λ-cell surfaces plan chain-plan
        rel vM vV spine chain typed ins follows child-target
  structural-name-instantiation-acc surfaces {B = B} {X = X} fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM (CT.Λ vV)
      (allv-Λ vV′ refl) spine chain typed (WF.acc smaller) target
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      | child =
    finish-target child-final
    where
    child-value = StructuralStrictChild.child-value child

    child-final =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease
        (StructuralStrictChild.child-plan child)
        (StructuralStrictChild.child-chain-plan child)
        (StructuralStrictChild.child-relation child) vM child-value
        (lambda-child-spine {B = B} {X = X} spine)
        (StructuralStrictChild.child-chain child)
        (StructuralStrictChild.child-typed child)
        (smaller
          (measure-rank< (lambda-child-mass-equal vV child-value spine)
            (rank<→lex
              (lambda-rank-decreases {X = X} vV child-value spine))))
        child-target

  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM (vV CT.《 CT.all {c = d} 》)
      (allv-∀ vV′ refl) spine chain typed (WF.acc smaller) target
      with Prog.canonical-∀ (vV CT.《 CT.all {c = d} 》)
        (CTI2T.target-typing² rel)
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM (vV CT.《 CT.all {c = d} 》)
      (allv-∀ vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-∀ vVᵗ refl
      with structural-target-all-peel vV spine target
  structural-name-instantiation-acc surfaces {X = X} fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM (vV CT.《 CT.all {c = d} 》)
      (allv-∀ vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-∀ vVᵗ refl
      | child-target , finish-target
      with StructuralStrictViewSurfaces.∀-cast-cell surfaces plan
        chain-plan rel vM vV spine chain typed child-target
  structural-name-instantiation-acc surfaces {X = X} fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM (vV CT.《 CT.all {c = d} 》)
      (allv-∀ vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-∀ vVᵗ refl
      | child-target , finish-target
      | child =
    finish-target child-final
    where
    child-final =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease
        (StructuralStrictChild.child-plan child)
        (StructuralStrictChild.child-chain-plan child)
        (StructuralStrictChild.child-relation child) vM vV
        (all-cast-child-spine {X = X} {d = d} spine)
        (StructuralStrictChild.child-chain child)
        (StructuralStrictChild.child-typed child)
        (smaller
          (measure-mass< (all-primary-decreases-at vV d X spine)))
        child-target
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder inst-decrease plan chain-plan rel vM
      (vV CT.《 CT.genᵥ {c = c} A≢★ safe 》)
      (allv-gen vV′ A≢★′ safe′ refl) spine chain typed (WF.acc smaller) target
      with Prog.canonical-∀ (vV CT.《 CT.genᵥ A≢★ safe 》)
        (CTI2T.target-typing² rel)
  structural-name-instantiation-acc surfaces {X = X} fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.《 CT.genᵥ A≢★ safe 》)
      (allv-gen vV′ A≢★′ safe′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-gen vVᵗ A≢★ᵗ safeᵗ refl
      with structural-target-gen-peel vV A≢★ safe spine target
  structural-name-instantiation-acc surfaces {X = X} fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.《 CT.genᵥ {c = c} A≢★ safe 》)
      (allv-gen vV′ A≢★′ safe′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-gen vVᵗ A≢★ᵗ safeᵗ refl
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      with StructuralStrictViewSurfaces.gen-cell surfaces plan chain-plan
        A≢★ rel vM vV safe spine chain typed ins follows child-target
  structural-name-instantiation-acc surfaces {X = X} fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.《 CT.genᵥ {c = c} A≢★ safe 》)
      (allv-gen vV′ A≢★′ safe′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-gen vVᵗ A≢★ᵗ safeᵗ refl
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      | child =
    finish-target child-final
    where
    child-value = renameᵗᵐ-preserves-Value wk↪ᵗ vV

    child-final =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease
        (StructuralStrictChild.child-plan child)
        (StructuralStrictChild.child-chain-plan child)
        (StructuralStrictChild.child-relation child) vM child-value
        (gen-child-spine {X = X} {c = c} spine)
        (StructuralStrictChild.child-chain child)
        (StructuralStrictChild.child-typed child)
        (smaller
          (measure-mass<
            (gen-primary-decreases {X = X} {c = c} {A≠★ = A≢★}
              vV safe spine)))
        child-target
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↑ CT.all {c = c})
      (allv-reveal vV′ refl) spine chain typed (WF.acc smaller) target
      with Prog.canonical-∀ (vV CT.↑ CT.all {c = c})
        (CTI2T.target-typing² rel)
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↑ CT.all {c = c})
      (allv-reveal vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-reveal vVᵗ refl
      with structural-target-reveal-peel vV spine target
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↑ CT.all {c = c})
      (allv-reveal vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-reveal vVᵗ refl
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      with StructuralStrictViewSurfaces.reveal-cell surfaces plan
        chain-plan rel vM vV spine chain typed ins follows child-target
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↑ CT.all {c = c})
      (allv-reveal vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-reveal vVᵗ refl
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      | child =
    finish-target child-final
    where
    child-value = renameᵗᵐ-preserves-Value wk↪ᵗ vV

    child-final =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease
        (StructuralStrictChild.child-plan child)
        (StructuralStrictChild.child-chain-plan child)
        (StructuralStrictChild.child-relation child) vM child-value
        (reveal-child-spine {X = X} {c = c} spine)
        (StructuralStrictChild.child-chain child)
        (StructuralStrictChild.child-typed child)
        (smaller
          (measure-rank<
            (reveal-strict-child-mass-equal {B = B} {X = X} {c = c}
              vV spine)
            (rank<→lex
              (reveal-rank-decreases {B = B} {X = X} {c = c}
                vV spine))))
        child-target
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↓ CT.all {c = c})
      (allv-conceal vV′ refl) spine chain typed (WF.acc smaller) target
      with Prog.canonical-∀ (vV CT.↓ CT.all {c = c})
        (CTI2T.target-typing² rel)
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↓ CT.all {c = c})
      (allv-conceal vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-conceal vVᵗ refl
      with structural-target-conceal-peel vV spine target
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↓ CT.all {c = c})
      (allv-conceal vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-conceal vVᵗ refl
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      with StructuralStrictViewSurfaces.conceal-cell surfaces plan
        chain-plan rel vM vV spine chain typed ins follows child-target
  structural-name-instantiation-acc surfaces {B = B} {X = X}
      fuel-step residual-cast-builder
      inst-decrease plan chain-plan rel vM
      (vV CT.↓ CT.all {c = c})
      (allv-conceal vV′ refl) spine chain typed (WF.acc smaller) target
      | Prog.av-conceal vVᵗ refl
      | Δ₁ , π , W₁ , ins , follows , child-target , finish-target
      | child =
    finish-target child-final
    where
    child-value = renameᵗᵐ-preserves-Value wk↪ᵗ vV

    child-final =
      structural-value-spine-instantiation-acc surfaces fuel-step
        residual-cast-builder inst-decrease
        (StructuralStrictChild.child-plan child)
        (StructuralStrictChild.child-chain-plan child)
        (StructuralStrictChild.child-relation child) vM child-value
        (conceal-child-spine {X = X} {c = c} spine)
        (StructuralStrictChild.child-chain child)
        (StructuralStrictChild.child-typed child)
        (smaller
          (measure-rank<
            (conceal-strict-child-mass-equal {B = B} {X = X} {c = c}
              vV spine)
            (rank<→lex
              (conceal-rank-decreases {B = B} {X = X} {c = c}
                vV spine))))
        child-target


structural-name-instantiation : StructuralNameInstantiationᵀ
structural-name-instantiation surfaces {B = B} {X = X}
    fuel-step residual-cast-builder
    inst-decrease plan chain-plan rel vM vV view spine chain typed target =
  structural-name-instantiation-acc surfaces fuel-step residual-cast-builder
    inst-decrease plan chain-plan rel vM vV view spine chain typed
    (termination-measure-access
      (terminationMeasure {phase = name-phase} vV
        (name-type-app-frame B X refl refl ▻ⁱ spine) rel))
    target


structural-value-instantiation : StructuralValueInstantiationᵀ
structural-value-instantiation {fuel = fuel} {W = W} {γ = γ}
    {A = A} {B = B} {R = R} {q = q}
    surfaces name-worker fuel-step residual-cast-builder inst-decrease plan
    chain-plan rel vM vV view target =
  erase-structural-name-root surfaces name-worker fuel-step residual-cast-builder
    inst-decrease plan chain-plan rel vM
    (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
    (SpineValueProof.rename-all-value-view wk↪ᵗ view)
    []ⁱ
    (root-value-instantiation-frame-chain
      {W = W} {γ = γ} {A = A} {B = B} {R = R} {q = q})
    (root-value-instantiation-spine-typed
      {fuel = fuel} {W = W} {A = A} {B = B} {R = R})
    target
