module proof.LR-narrow.FundamentalAssembly where

-- File Charter:
--   * Assembles the fundamental property by exhaustive recursion on the
--     compiled term-imprecision derivation.
--   * Closes every constructor that already has a checked compatibility
--     lemma, and isolates each remaining obligation as an explicit field of
--     `RemainingObligations`.
--   * Each obligation receives the structural induction hypothesis that the
--     recursion can supply, stated for every semantic world realizing the
--     premise's syntactic world.
--   * Contains no postulate, hole, or catch-all case.  The parameters of
--     `Assembly` are the exact proof debt of the total theorem.

open import Data.Nat using (suc)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import Types
open import CastTerms
open import Conversion using (Conv↑; Conv↓; _⊢↑[_]_; _⊢↓[_]_; seal)
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.TermRelation
open import LR-narrow.Variable using (variable-compatible)
open import LR-narrow.Constant using (constant-compatible)
open import LR-narrow.Blame using (blame-compatible)
open import LR-narrow.Primitive using (primitive-compatible)
open import LR-narrow.Lambda using (lambda-compatible-from-body)
open import LR-narrow.Application using (application-compatible)
open import LR-narrow.TypeApplication using
  (type-application-compatible; right-type-application-compatible)
open import LR-narrow.Cast using
  (cast-cast-compatible; right-cast-compatible; left-cast-compatible)
open import LR-narrow.Universal using (universal-body-imprecision)
open import LR-narrow.Fundamental using
  (universal-fundamental; right-universal-fundamental;
   right-universal-smart-fundamental)

------------------------------------------------------------------------
-- Fundamental property at a semantic realization of a syntactic world
------------------------------------------------------------------------

-- The recursion runs over derivations at an arbitrary syntactic world
-- `Wᶜ`.  A semantic world `W` realizes it when `forgetWorld W ≡ Wᶜ`; the
-- motive is then the ordinary fundamental property.

FundamentalAt : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ)
  → forgetWorld W ≡ Wᶜ
  → {Γ : CTI.CtxImp Wᶜ}
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ}
  → Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p
  → Set₁
FundamentalAt W refl d = FundamentalProperty {W = W} d

-- The induction hypothesis the structural recursion supplies for a
-- premise: the fundamental property at every semantic realization of
-- the premise's syntactic world.

Hypothesis : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ}
  → Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p
  → Set₁
Hypothesis {Δᴾ} {Δᴵ} {Δᶜ} d =
  ∀ (W : World Δᴾ Δᴵ Δᶜ) (eq : forgetWorld W ≡ _)
  → FundamentalAt W eq d

------------------------------------------------------------------------
-- Views on the operator imprecision of a type application
------------------------------------------------------------------------

-- The structural cases are exactly those consumed by the checked type
-- application lemmas; every other constructor is residual Milestone 3
-- work.  Both views are total by explicit enumeration.

NotPairedStructural : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → μ I.⊢ A ⊑ B → Set
NotPairedStructural (I.∀⊑∀ _) = ⊥
NotPairedStructural I.★⊑★ = ⊤
NotPairedStructural I.ι⊑ι = ⊤
NotPairedStructural I.X⊑X = ⊤
NotPairedStructural (I.⇒⊑⇒ _ _) = ⊤
NotPairedStructural (I.⇒⊑★ _ _) = ⊤
NotPairedStructural I.ι⊑★ = ⊤
NotPairedStructural (I.X⊑★ _) = ⊤
NotPairedStructural (I.∀⊑ _ _ _) = ⊤
NotPairedStructural I.∀★⊑★ = ⊤
NotPairedStructural (I.∀⊑★ _ _) = ⊤
NotPairedStructural I.bot-elim = ⊤
NotPairedStructural I.bot⊑★ = ⊤

NotRightStructural : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → μ I.⊢ A ⊑ B → Set
NotRightStructural (I.∀⊑ _ _ _) = ⊥
NotRightStructural I.★⊑★ = ⊤
NotRightStructural I.ι⊑ι = ⊤
NotRightStructural I.X⊑X = ⊤
NotRightStructural (I.⇒⊑⇒ _ _) = ⊤
NotRightStructural (I.∀⊑∀ _) = ⊤
NotRightStructural (I.⇒⊑★ _ _) = ⊤
NotRightStructural I.ι⊑★ = ⊤
NotRightStructural (I.X⊑★ _) = ⊤
NotRightStructural I.∀★⊑★ = ⊤
NotRightStructural (I.∀⊑★ _ _) = ⊤
NotRightStructural I.bot-elim = ⊤
NotRightStructural I.bot⊑★ = ⊤

-- The views are computed at variable indices, so the recursion can
-- dispatch on them even though the embedded operator types are stuck
-- renamings.

data PairedView {Δ} {μ : I.ImpEnv Δ} {C C′ : Ty (suc Δ)} :
    μ I.⊢ `∀ C ⊑ `∀ C′ → Set where
  paired-structural : (p : I.extᵐ μ I.⊢ C ⊑ C′)
    → PairedView (I.∀⊑∀ p)
  paired-nonstructural : (p∀ : μ I.⊢ `∀ C ⊑ `∀ C′)
    → NotPairedStructural p∀
    → PairedView p∀

pairedView : ∀ {Δ} {μ : I.ImpEnv Δ} {C C′ : Ty (suc Δ)}
  → (p∀ : μ I.⊢ `∀ C ⊑ `∀ C′) → PairedView p∀
pairedView (I.∀⊑∀ p) = paired-structural p
pairedView (I.∀⊑ nonvar occurs p) =
  paired-nonstructural (I.∀⊑ nonvar occurs p) tt
pairedView I.bot-elim = paired-nonstructural I.bot-elim tt

data RightView {Δ} {μ : I.ImpEnv Δ} {C : Ty (suc Δ)} {B : Ty Δ} :
    μ I.⊢ `∀ C ⊑ B → Set where
  right-structural : (nonvar : NonVar C) (occurs : Fin.zero ∈ᵗ C)
      (p : I.instᵐ μ I.⊢ C ⊑ ⇑ᵗ B)
    → RightView (I.∀⊑ nonvar occurs p)
  right-nonstructural : (p∀ : μ I.⊢ `∀ C ⊑ B)
    → NotRightStructural p∀
    → RightView p∀

rightView : ∀ {Δ} {μ : I.ImpEnv Δ} {C : Ty (suc Δ)} {B : Ty Δ}
  → (p∀ : μ I.⊢ `∀ C ⊑ B) → RightView p∀
rightView (I.∀⊑ nonvar occurs p) = right-structural nonvar occurs p
rightView (I.∀⊑∀ p) = right-nonstructural (I.∀⊑∀ p) tt
rightView I.∀★⊑★ = right-nonstructural I.∀★⊑★ tt
rightView (I.∀⊑★ ns p) = right-nonstructural (I.∀⊑★ ns p) tt
rightView I.bot-elim = right-nonstructural I.bot-elim tt
rightView I.bot⊑★ = right-nonstructural I.bot⊑★ tt

------------------------------------------------------------------------
-- Remaining obligations
------------------------------------------------------------------------

record RemainingObligations : Set₂ where
  field

    -- Milestone 1.4: symmetric universal body motive.
    universal-body : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
        {W : World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)}
        {Γᵇ : CTI.CtxImp
          (CTI.liftWorldBoth I.X⊑X (forgetWorld W))}
        {p : Aᴾ CTI.⊑ᵂ⟨
          CTI.liftWorldBoth I.X⊑X (forgetWorld W) ⟩ Aᴵ}
        {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
        (liftΓ : CTI.LiftCtx I.X⊑X Γ Γᵇ)
        (vVᴾ : Value Vᴾ)
        (vVᴵ : Value Vᴵ)
        (body : CTI.liftWorldBoth I.X⊑X (forgetWorld W) ∣ Γᵇ
          ⊢² Vᴾ ⊑ Vᴵ ∶ p)
        (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ `∀ Aᴵ)
      → Hypothesis body
      → UniversalBodyFundamentalProperty {W = W} {Γ = Γ} {Γᵇ = Γᵇ}
          {p = p} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
          (universal-body-imprecision {W = W} p)
          body

    -- Milestone 1.5: one-sided universal body motive.
    right-universal-body : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)}
        {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨
          CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
        {Γ′ : CTI.CtxImp
          (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
        {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
        (nonvar : NonVar Aᴾ)
        (occurs : Fin.zero ∈ᵗ Aᴾ)
        (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
        (vVᴾ : Value Vᴾ)
        (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
          CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ)
        (body : CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ∣ Γ′
          ⊢² Vᴾ ⊑ Mᴵ ∶ p)
        (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → Hypothesis body
      → RightUniversalBodyFundamentalProperty
          {W = W} {Γ = Γ}
          {Wᵇ = CTI.liftWorldLeft I.X⊑★ (forgetWorld W)} {Γᵇ = Γ′}
          {p = p} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ} q body

    -- Milestone 1.5: smart-comma one-sided universal body motive.
    right-universal-smart-body : ∀ {Δᴾ Δᴵ Δᶜ Δᵐ}
        {W : World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)}
        {Wᵐ : CTI.World (suc Δᴾ) Δᴵ Δᵐ}
        {Γᵐ : CTI.CtxImp Wᵐ}
        {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨ Wᵐ ⟩ Bᴵ}
        {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
        (nonvar : NonVar Aᴾ)
        (occurs : Fin.zero ∈ᵗ Aᴾ)
        (smart : CTI.SmartCommaLiftᴸ (forgetWorld W) Wᵐ)
        (liftΓ : CTI.SmartLiftCtxᴸ Γ Γᵐ)
        (vVᴾ : Value Vᴾ)
        (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ (forgetWorld W) ,
          CTI.tgtCtxʷ Γ ⟩ ⊢ Mᴵ ⦂ Bᴵ)
        (body : Wᵐ ∣ Γᵐ ⊢² Vᴾ ⊑ Mᴵ ∶ p)
        (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → Hypothesis body
      → RightUniversalBodyFundamentalProperty
          {W = W} {Γ = Γ} {Wᵇ = Wᵐ} {Γᵇ = Γᵐ}
          {p = p} {Vᴾ = Vᴾ} {Mᴵ = Mᴵ} q body

    -- Milestone 2: rebase-sensitive cast forms.  Each receives the
    -- hypothesis for its premise at every semantic realization of the
    -- rebased world `W′`.
    target-reveal : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ : Ty Δᴾ} {Bᴵ Bᴵ′ : Ty Δᴵ} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c′ : Conv↑ Δᴵ Bᴵ Bᴵ′}
        (mono : CTI.ImpEnvMono (forgetWorld W) W′)
        (rebase : CTI.RebaseAtᴿ (forgetWorld W) W′ Xᴵ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.targetStoreʷ (forgetWorld W) ⊢↑[ Xᴵ? ] c′)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ′)
      → Hypothesis prem
      → FundamentalProperty {W = W}
          (CTIR.⊑reveal² mono rebase same ok prem q)

    target-conceal : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ : Ty Δᴾ} {Bᴵ Bᴵ′ : Ty Δᴵ} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c′ : Conv↓ Δᴵ Bᴵ Bᴵ′}
        (mono : CTI.ImpEnvMono (forgetWorld W) W′)
        (rebase : CTI.RebaseAtᴿ W′ (forgetWorld W) Xᴵ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.targetStoreʷ (forgetWorld W) ⊢↓[ Xᴵ? ] c′)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ′)
      → Hypothesis prem
      → FundamentalProperty {W = W}
          (CTIR.⊑conceal² mono rebase same ok prem q)

    source-reveal : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Aᴾ′ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Xᴾ? : Maybe (TyVar Δᴾ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c : Conv↑ Δᴾ Aᴾ Aᴾ′}
        (mono : CTI.ImpEnvMono (forgetWorld W) W′)
        (rebase : CTI.RebaseAtᴸ (forgetWorld W) W′ Xᴾ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.sourceStoreʷ (forgetWorld W) ⊢↑[ Xᴾ? ] c)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ′ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → Hypothesis prem
      → FundamentalProperty {W = W}
          (CTIR.reveal⊑² mono rebase same ok prem q)

    source-conceal-seal-star : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Bᴵ : Ty Δᴵ} {X : TyVar Δᴾ}
        {p : ★ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ}
        (open-target : CTI.NoTargetOccupantAtSource W′ X)
        (mono : CTI.ImpEnvMono (forgetWorld W) W′)
        (rebase : CTI.TagRebaseAtᴸ W′ (forgetWorld W) (just X) nothing)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.sourceStoreʷ (forgetWorld W) ⊢↓[ just X ] seal X ★)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : (＇ X) ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → Hypothesis prem
      → FundamentalProperty {W = W}
          (CTIR.conceal⊑²-seal-star-open
            open-target mono rebase same ok prem q)

    source-conceal : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Aᴾ′ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
        {Xᴾ? : Maybe (TyVar Δᴾ)} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c : Conv↓ Δᴾ Aᴾ Aᴾ′}
        (ok-source : CTI.SourceConcealOK W′ Mᴾ c Xᴵ? Mᴵ)
        (mono : CTI.ImpEnvMono (forgetWorld W) W′)
        (rebase : CTI.TagRebaseAtᴸ W′ (forgetWorld W) Xᴾ? Xᴵ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.sourceStoreʷ (forgetWorld W) ⊢↓[ Xᴾ? ] c)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ′ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → Hypothesis prem
      → FundamentalProperty {W = W}
          (CTIR.conceal⊑²-source-ok ok-source mono rebase same ok prem q)

    reveal-reveal : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {Wᵖ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γᵖ : CTI.CtxImp Wᵖ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Bᴾ : Ty Δᴾ} {Aᴵ Bᴵ : Ty Δᴵ}
        {Xᴾ : TyVar Δᴾ} {Xᴵ : TyVar Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨ Wᵖ ⟩ Aᴵ}
        {c : Conv↑ Δᴾ Aᴾ Bᴾ} {c′ : Conv↑ Δᴵ Aᴵ Bᴵ}
        (mono : CTI.ImpEnvMono (forgetWorld W) Wᵖ)
        (rebase : CTI.RebaseAt (forgetWorld W) Wᵖ Xᴾ Xᴵ)
        (same : CTI.SameCtx Γ Γᵖ)
        (okᴾ : CTI.sourceStoreʷ (forgetWorld W) ⊢↑[ just Xᴾ ] c)
        (okᴵ : CTI.targetStoreʷ (forgetWorld W) ⊢↑[ just Xᴵ ] c′)
        (prem : Wᵖ ∣ Γᵖ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → Hypothesis prem
      → FundamentalProperty {W = W}
          (CTIR.reveal⊑reveal² mono rebase same okᴾ okᴵ prem q)

    conceal-conceal : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {Wᵖ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γᵖ : CTI.CtxImp Wᵖ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Bᴾ : Ty Δᴾ} {Aᴵ Bᴵ : Ty Δᴵ}
        {Xᴾ : TyVar Δᴾ} {Xᴵ : TyVar Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨ Wᵖ ⟩ Aᴵ}
        {c : Conv↓ Δᴾ Aᴾ Bᴾ} {c′ : Conv↓ Δᴵ Aᴵ Bᴵ}
        (partner : CTI.MatchedConcealPartnerOK Wᵖ Mᴾ c (just Xᴵ) Mᴵ)
        (mono : CTI.ImpEnvMono (forgetWorld W) Wᵖ)
        (rebase : CTI.RebaseAt Wᵖ (forgetWorld W) Xᴾ Xᴵ)
        (same : CTI.SameCtx Γ Γᵖ)
        (okᴾ : CTI.sourceStoreʷ (forgetWorld W) ⊢↓[ just Xᴾ ] c)
        (okᴵ : CTI.targetStoreʷ (forgetWorld W) ⊢↓[ just Xᴵ ] c′)
        (prem : Wᵖ ∣ Γᵖ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → Hypothesis prem
      → FundamentalProperty {W = W}
          (CTIR.conceal⊑conceal² partner mono rebase same okᴾ okᴵ prem q)

    packaged-seal-star : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ} {Wᵖ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)} {Γᵖ : CTI.CtxImp Wᵖ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Xᴾ : TyVar Δᴾ} {Xᴵ : TyVar Δᴵ} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p★ : ★ CTI.⊑ᵂ⟨ Wᵖ ⟩ ★}
        {qᵖ : (＇ Xᴾ) CTI.⊑ᵂ⟨ Wᵖ ⟩ ★}
        (partner : CTI.MatchedConcealPartnerOK Wᵖ Mᴾ (seal Xᴾ ★) Xᴵ? Mᴵ)
        (mono : CTI.ImpEnvMono (forgetWorld W) Wᵖ)
        (rebase : CTI.RebaseAt Wᵖ (forgetWorld W) Xᴾ Xᴵ)
        (same : CTI.SameCtx Γ Γᵖ)
        (okᴾ : CTI.sourceStoreʷ (forgetWorld W) ⊢↓[ just Xᴾ ] seal Xᴾ ★)
        (okᴵ : CTI.targetStoreʷ (forgetWorld W) ⊢↓[ just Xᴵ ] seal Xᴵ ★)
        (prem : Wᵖ ∣ Γᵖ ⊢² Mᴾ ⊑ Mᴵ ∶ p★)
        (sealed : Wᵖ ∣ Γᵖ ⊢² Mᴾ ↓ seal Xᴾ ★ ⊑ Mᴵ ∶ qᵖ)
        (q : (＇ Xᴾ) ⊑ᵂ⟨ core W ⟩ (＇ Xᴵ))
      → Hypothesis prem
      → Hypothesis sealed
      → FundamentalProperty {W = W}
          (CTIR.packaged-seal-star²
            partner mono rebase same okᴾ okᴵ prem sealed q)

    -- Milestone 3: universal elimination whose operator imprecision is
    -- not the structural `∀⊑∀` (paired) or `∀⊑` (one-sided) view.
    type-application-nonstructural : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)}
        {Cᴾ : Ty (suc Δᴾ)} {Cᴵ : Ty (suc Δᴵ)}
        {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        (p∀ : `∀ Cᴾ ⊑ᵂ⟨ core W ⟩ `∀ Cᴵ)
        (M⊑ : forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
        (q : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
        (r : Cᴾ [ Aᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Cᴵ [ Aᴵ ]ᵗ)
      → NotPairedStructural p∀
      → FundamentalProperty {W = W} M⊑
      → FundamentalProperty {W = W} (CTIR.•⊑•² p∀ M⊑ q r)

    right-type-application-nonstructural : ∀ {Δᴾ Δᴵ Δᶜ}
        {W : World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp (forgetWorld W)}
        {Cᴾ : Ty (suc Δᴾ)} {Aᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        (p∀ : `∀ Cᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
        (M⊑ : forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
        (q : Aᴾ ⊑ᵂ⟨ core W ⟩ ★)
        (r : Cᴾ [ Aᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      → NotRightStructural p∀
      → FundamentalProperty {W = W} M⊑
      → FundamentalProperty {W = W} (CTIR.•⊑² p∀ M⊑ q r)


------------------------------------------------------------------------
-- The assembled theorem
------------------------------------------------------------------------

module Assembly (obligations : RemainingObligations) where
  open RemainingObligations obligations

  -- Paired type application, dispatched on the operator imprecision.
  type-application-case : ∀ {Δᴾ Δᴵ Δᶜ}
      {W : World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp (forgetWorld W)}
      {Cᴾ : Ty (suc Δᴾ)} {Cᴵ : Ty (suc Δᴵ)}
      {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      (p∀ : `∀ Cᴾ ⊑ᵂ⟨ core W ⟩ `∀ Cᴵ)
      (M⊑ : forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
      (q : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
      (r : Cᴾ [ Aᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Cᴵ [ Aᴵ ]ᵗ)
    → FundamentalProperty {W = W} M⊑
    → FundamentalProperty {W = W} (CTIR.•⊑•² p∀ M⊑ q r)
  type-application-case p∀ M⊑ q r ih with pairedView p∀
  type-application-case p∀ M⊑ q r ih | paired-structural p =
    fundamental-proof
      (type-application-compatible {q = q} M⊑
        (fundamental-relation ih))
  type-application-case p∀ M⊑ q r ih
      | paired-nonstructural _ residual =
    type-application-nonstructural p∀ M⊑ q r residual ih

  -- One-sided type application, dispatched on the operator imprecision.
  right-type-application-case : ∀ {Δᴾ Δᴵ Δᶜ}
      {W : World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp (forgetWorld W)}
      {Cᴾ : Ty (suc Δᴾ)} {Aᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      (p∀ : `∀ Cᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
      (M⊑ : forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
      (q : Aᴾ ⊑ᵂ⟨ core W ⟩ ★)
      (r : Cᴾ [ Aᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Bᴵ)
    → FundamentalProperty {W = W} M⊑
    → FundamentalProperty {W = W} (CTIR.•⊑² p∀ M⊑ q r)
  right-type-application-case p∀ M⊑ q r ih with rightView p∀
  right-type-application-case p∀ M⊑ q r ih
      | right-structural nonvar occurs p =
    fundamental-proof
      (right-type-application-compatible {q = q} M⊑
        (fundamental-relation ih))
  right-type-application-case p∀ M⊑ q r ih
      | right-nonstructural _ residual =
    right-type-application-nonstructural p∀ M⊑ q r residual ih

  fundamental : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
      {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp Wᶜ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      {p : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ}
      (d : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
    → Hypothesis d
  fundamental (CTIR.x⊑x² x∈) W refl =
    fundamental-proof (λ k → variable-compatible x∈)
  fundamental (CTIR.κ⊑κ² κ p) W refl =
    fundamental-proof (λ k → constant-compatible κ)
  fundamental (CTIR.blame⊑² target⊢ p) W refl =
    fundamental-proof (λ k → blame-compatible target⊢ p)
  fundamental (CTIR.ƛ⊑ƛ² body) W refl =
    fundamental-proof (λ k →
      lambda-compatible-from-body body
        (λ i i≤k → fundamental-relation (fundamental body W refl) i))
  fundamental (CTIR.·⊑·² L⊑ M⊑) W refl =
    fundamental-proof
      (application-compatible L⊑ M⊑
        (fundamental-relation (fundamental L⊑ W refl))
        (fundamental-relation (fundamental M⊑ W refl)))
  fundamental (CTIR.⊕⊑⊕² op L⊑ M⊑ r) W refl =
    fundamental-proof
      (primitive-compatible op L⊑ M⊑
        (fundamental-relation (fundamental L⊑ W refl))
        (fundamental-relation (fundamental M⊑ W refl)))
  fundamental (CTIR.cast⊑cast² c c′ M⊑ q) W refl =
    fundamental-proof
      (cast-cast-compatible c c′ M⊑ q
        (fundamental-relation (fundamental M⊑ W refl)))
  fundamental (CTIR.⊑cast² c′ M⊑ q) W refl =
    fundamental-proof
      (right-cast-compatible c′ M⊑ q
        (fundamental-relation (fundamental M⊑ W refl)))
  fundamental (CTIR.cast⊑² c M⊑ q) W refl =
    fundamental-proof
      (left-cast-compatible c M⊑ q
        (fundamental-relation (fundamental M⊑ W refl)))
  fundamental (CTIR.•⊑•² p∀ M⊑ q r) W refl =
    type-application-case p∀ M⊑ q r (fundamental M⊑ W refl)
  fundamental (CTIR.•⊑² p∀ M⊑ q r) W refl =
    right-type-application-case p∀ M⊑ q r (fundamental M⊑ W refl)
  fundamental (CTIR.Λ⊑Λ² liftΓ vVᴾ vVᴵ body q) W refl =
    universal-fundamental liftΓ vVᴾ vVᴵ body q
      (universal-body liftΓ vVᴾ vVᴵ body q (fundamental body))
  fundamental
      (CTIR.Λ⊑² nonvar occurs liftΓ vVᴾ target⊢ body q) W refl =
    right-universal-fundamental nonvar occurs liftΓ vVᴾ target⊢ body q
      (right-universal-body nonvar occurs liftΓ vVᴾ target⊢ body q
        (fundamental body))
  fundamental
      (CTIR.Λ⊑²-smart-comma nonvar occurs smart liftΓ vVᴾ target⊢
        body q) W refl =
    right-universal-smart-fundamental
      nonvar occurs smart liftΓ vVᴾ target⊢ body q
      (right-universal-smart-body
        nonvar occurs smart liftΓ vVᴾ target⊢ body q
        (fundamental body))
  fundamental (CTIR.⊑reveal² mono rebase same ok prem q) W refl =
    target-reveal mono rebase same ok prem q (fundamental prem)
  fundamental (CTIR.⊑conceal² mono rebase same ok prem q) W refl =
    target-conceal mono rebase same ok prem q (fundamental prem)
  fundamental (CTIR.reveal⊑² mono rebase same ok prem q) W refl =
    source-reveal mono rebase same ok prem q (fundamental prem)
  fundamental
      (CTIR.conceal⊑²-seal-star-open
        open-target mono rebase same ok prem q) W refl =
    source-conceal-seal-star open-target mono rebase same ok prem q
      (fundamental prem)
  fundamental
      (CTIR.conceal⊑²-source-ok
        ok-source mono rebase same ok prem q) W refl =
    source-conceal ok-source mono rebase same ok prem q
      (fundamental prem)
  fundamental
      (CTIR.reveal⊑reveal² mono rebase same okᴾ okᴵ prem q) W refl =
    reveal-reveal mono rebase same okᴾ okᴵ prem q (fundamental prem)
  fundamental
      (CTIR.conceal⊑conceal²
        partner mono rebase same okᴾ okᴵ prem q) W refl =
    conceal-conceal partner mono rebase same okᴾ okᴵ prem q
      (fundamental prem)
  fundamental
      (CTIR.packaged-seal-star²
        partner mono rebase same okᴾ okᴵ prem sealed q) W refl =
    packaged-seal-star partner mono rebase same okᴾ okᴵ prem sealed q
      (fundamental prem) (fundamental sealed)
