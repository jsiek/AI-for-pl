module proof.LR-narrow.FundamentalAssembly where

-- File Charter:
--   * Assembles the insertion-generalized fundamental property by exhaustive
--     recursion on the compiled term-imprecision derivation.
--   * Closes every constructor that has a checked compatibility lemma on the
--     renamed endpoint terms, and isolates each remaining obligation as an
--     explicit field of `RemainingObligations`.
--   * Each obligation receives the insertion-generalized induction hypothesis
--     for its premises.
--   * Contains no postulate, hole, or catch-all case.  The parameters of
--     `Assembly` are the exact proof debt of the total theorem.

open import Data.Nat using (ℕ; suc)
open import Data.List using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)
  renaming (subst to subst≡)

open import Types
open import CastTerms
open import Conversion using (Conv↑; Conv↓; _⊢↑[_]_; _⊢↓[_]_; seal)
open import Consistency using (_↪ᵗ_; toRenameᵗ; renameᵐᶜ)
import Imprecision as I
open import Primitives using (Const; Prim; addℕ; and𝔹; constTy;
  primArgTy; primResultTy; constTy-renameᵗ)
open import proof.TypeInTermSubst using
  (typing-renameᵗ; toRename-keep-eq; rename-openᵗ)
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.CastTermImprecision2Typing as CTIT
open CTIR using (_∣_⊢²_⊑_∶_)
open import proof.DGG.WorldInsert
open import LR-narrow.World
open import LR-narrow.TermRelation
open import LR-narrow.Insertion
open import LR-narrow.Variable using (variable-compatible)
open import LR-narrow.Constant using (constant-compatible)
open import LR-narrow.Blame using (blame-compatible)
open import LR-narrow.Primitive using (primitive-compatible)
open import LR-narrow.Lambda using (lambda-compatible-from-body)
open import LR-narrow.Application using (application-compatible)
open import LR-narrow.TypeApplication using
  (type-application-compatible; right-type-application-compatible)
open import LR-narrow.CastObligations using (CastValueObligations)
import LR-narrow.Cast as Cast

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

-- Every obligation is stated below an arbitrary insertion of the
-- derivation's syntactic world into a semantic world and must produce the
-- open relation for the renamed conclusion terms.

record RemainingObligations : Set₂ where
  field

    -- Value-level cast compatibilities reopened after the circular
    -- proofs were removed; see LR-narrow.CastObligations.
    cast-values : CastValueObligations

    -- Milestone 1.7: symmetric universal introduction.
    universal-intro : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
        {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ}
        {Γᵇ : CTI.CtxImp (CTI.liftWorldBoth I.X⊑X Wᶜ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X Wᶜ ⟩ Aᴵ}
        {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
        (liftΓ : CTI.LiftCtx I.X⊑X Γ Γᵇ)
        (vVᴾ : Value Vᴾ)
        (vVᴵ : Value Vᴵ)
        (body : CTI.liftWorldBoth I.X⊑X Wᶜ ∣ Γᵇ ⊢² Vᴾ ⊑ Vᴵ ∶ p)
        (q : `∀ Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ `∀ Aᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty body
      → ∀ k → InsertedTermRelation W ins q k Γ (Λ Vᴾ) (Λ Vᴵ)

    -- Milestone 1.8: one-sided universal introduction.
    right-universal-intro : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ}
        {Γ′ : CTI.CtxImp (CTI.liftWorldLeft I.X⊑★ Wᶜ)}
        {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldLeft I.X⊑★ Wᶜ ⟩ Bᴵ}
        {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
        (nonvar : NonVar Aᴾ)
        (occurs : Fin.zero ∈ᵗ Aᴾ)
        (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
        (vVᴾ : Value Vᴾ)
        (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ Wᶜ , CTI.tgtCtxʷ Γ ⟩
          ⊢ Mᴵ ⦂ Bᴵ)
        (body : CTI.liftWorldLeft I.X⊑★ Wᶜ ∣ Γ′ ⊢² Vᴾ ⊑ Mᴵ ∶ p)
        (q : `∀ Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty body
      → ∀ k → InsertedTermRelation W ins q k Γ (Λ Vᴾ) Mᴵ

    -- Milestone 1.8: smart-comma one-sided universal introduction.
    right-universal-smart-intro : ∀ {Δᴾ Δᴵ Δᶜ Δᵐ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ}
        {Wᵐ : CTI.World (suc Δᴾ) Δᴵ Δᵐ}
        {Γᵐ : CTI.CtxImp Wᵐ}
        {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨ Wᵐ ⟩ Bᴵ}
        {Vᴾ : Term (suc Δᴾ)} {Mᴵ : Term Δᴵ}
        (nonvar : NonVar Aᴾ)
        (occurs : Fin.zero ∈ᵗ Aᴾ)
        (smart : CTI.SmartCommaLiftᴸ Wᶜ Wᵐ)
        (liftΓ : CTI.SmartLiftCtxᴸ Γ Γᵐ)
        (vVᴾ : Value Vᴾ)
        (target⊢ : ⟨ Δᴵ , CTI.targetStoreʷ Wᶜ , CTI.tgtCtxʷ Γ ⟩
          ⊢ Mᴵ ⦂ Bᴵ)
        (body : Wᵐ ∣ Γᵐ ⊢² Vᴾ ⊑ Mᴵ ∶ p)
        (q : `∀ Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty body
      → ∀ k → InsertedTermRelation W ins q k Γ (Λ Vᴾ) Mᴵ

    -- Milestone 2: rebase-sensitive cast forms.
    target-reveal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ : Ty Δᴾ} {Bᴵ Bᴵ′ : Ty Δᴵ} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c′ : Conv↑ Δᴵ Bᴵ Bᴵ′}
        (mono : CTI.ImpEnvMono Wᶜ W′)
        (rebase : CTI.RebaseAtᴿ Wᶜ W′ Xᴵ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.targetStoreʷ Wᶜ ⊢↑[ Xᴵ? ] c′)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ′)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → ∀ k → InsertedTermRelation W ins q k Γ Mᴾ (Mᴵ ↑ c′)

    target-conceal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ : Ty Δᴾ} {Bᴵ Bᴵ′ : Ty Δᴵ} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c′ : Conv↓ Δᴵ Bᴵ Bᴵ′}
        (mono : CTI.ImpEnvMono Wᶜ W′)
        (rebase : CTI.RebaseAtᴿ W′ Wᶜ Xᴵ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.targetStoreʷ Wᶜ ⊢↓[ Xᴵ? ] c′)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ′)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → ∀ k → InsertedTermRelation W ins q k Γ Mᴾ (Mᴵ ↓ c′)

    source-reveal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Aᴾ′ : Ty Δᴾ} {Bᴵ : Ty Δᴵ} {Xᴾ? : Maybe (TyVar Δᴾ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c : Conv↑ Δᴾ Aᴾ Aᴾ′}
        (mono : CTI.ImpEnvMono Wᶜ W′)
        (rebase : CTI.RebaseAtᴸ Wᶜ W′ Xᴾ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.sourceStoreʷ Wᶜ ⊢↑[ Xᴾ? ] c)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ′ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → ∀ k → InsertedTermRelation W ins q k Γ (Mᴾ ↑ c) Mᴵ

    source-conceal-seal-star : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Bᴵ : Ty Δᴵ} {X : TyVar Δᴾ}
        {p : ★ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ}
        (open-target : CTI.NoTargetOccupantAtSource W′ X)
        (mono : CTI.ImpEnvMono Wᶜ W′)
        (rebase : CTI.TagRebaseAtᴸ W′ Wᶜ (just X) nothing)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.sourceStoreʷ Wᶜ ⊢↓[ just X ] seal X ★)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : (＇ X) CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → ∀ k → InsertedTermRelation W ins q k Γ
          (Mᴾ ↓ seal X ★) Mᴵ

    source-conceal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ W′ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γ′ : CTI.CtxImp W′}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Aᴾ′ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
        {Xᴾ? : Maybe (TyVar Δᴾ)} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p : Aᴾ CTI.⊑ᵂ⟨ W′ ⟩ Bᴵ} {c : Conv↓ Δᴾ Aᴾ Aᴾ′}
        (ok-source : CTI.SourceConcealOK W′ Mᴾ c Xᴵ? Mᴵ)
        (mono : CTI.ImpEnvMono Wᶜ W′)
        (rebase : CTI.TagRebaseAtᴸ W′ Wᶜ Xᴾ? Xᴵ?)
        (same : CTI.SameCtx Γ Γ′)
        (ok : CTI.sourceStoreʷ Wᶜ ⊢↓[ Xᴾ? ] c)
        (prem : W′ ∣ Γ′ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Aᴾ′ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → ∀ k → InsertedTermRelation W ins q k Γ (Mᴾ ↓ c) Mᴵ

    reveal-reveal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ Wᵖ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γᵖ : CTI.CtxImp Wᵖ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Bᴾ : Ty Δᴾ} {Aᴵ Bᴵ : Ty Δᴵ}
        {Xᴾ : TyVar Δᴾ} {Xᴵ : TyVar Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨ Wᵖ ⟩ Aᴵ}
        {c : Conv↑ Δᴾ Aᴾ Bᴾ} {c′ : Conv↑ Δᴵ Aᴵ Bᴵ}
        (mono : CTI.ImpEnvMono Wᶜ Wᵖ)
        (rebase : CTI.RebaseAt Wᶜ Wᵖ Xᴾ Xᴵ)
        (same : CTI.SameCtx Γ Γᵖ)
        (okᴾ : CTI.sourceStoreʷ Wᶜ ⊢↑[ just Xᴾ ] c)
        (okᴵ : CTI.targetStoreʷ Wᶜ ⊢↑[ just Xᴵ ] c′)
        (prem : Wᵖ ∣ Γᵖ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Bᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → ∀ k → InsertedTermRelation W ins q k Γ (Mᴾ ↑ c) (Mᴵ ↑ c′)

    conceal-conceal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ Wᵖ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γᵖ : CTI.CtxImp Wᵖ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Aᴾ Bᴾ : Ty Δᴾ} {Aᴵ Bᴵ : Ty Δᴵ}
        {Xᴾ : TyVar Δᴾ} {Xᴵ : TyVar Δᴵ}
        {p : Aᴾ CTI.⊑ᵂ⟨ Wᵖ ⟩ Aᴵ}
        {c : Conv↓ Δᴾ Aᴾ Bᴾ} {c′ : Conv↓ Δᴵ Aᴵ Bᴵ}
        (partner : CTI.MatchedConcealPartnerOK Wᵖ Mᴾ c (just Xᴵ) Mᴵ)
        (mono : CTI.ImpEnvMono Wᶜ Wᵖ)
        (rebase : CTI.RebaseAt Wᵖ Wᶜ Xᴾ Xᴵ)
        (same : CTI.SameCtx Γ Γᵖ)
        (okᴾ : CTI.sourceStoreʷ Wᶜ ⊢↓[ just Xᴾ ] c)
        (okᴵ : CTI.targetStoreʷ Wᶜ ⊢↓[ just Xᴵ ] c′)
        (prem : Wᵖ ∣ Γᵖ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
        (q : Bᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → ∀ k → InsertedTermRelation W ins q k Γ (Mᴾ ↓ c) (Mᴵ ↓ c′)

    packaged-seal-star : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ Wᵖ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ} {Γᵖ : CTI.CtxImp Wᵖ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        {Xᴾ : TyVar Δᴾ} {Xᴵ : TyVar Δᴵ} {Xᴵ? : Maybe (TyVar Δᴵ)}
        {p★ : ★ CTI.⊑ᵂ⟨ Wᵖ ⟩ ★}
        {qᵖ : (＇ Xᴾ) CTI.⊑ᵂ⟨ Wᵖ ⟩ ★}
        (partner : CTI.MatchedConcealPartnerOK Wᵖ Mᴾ (seal Xᴾ ★) Xᴵ? Mᴵ)
        (mono : CTI.ImpEnvMono Wᶜ Wᵖ)
        (rebase : CTI.RebaseAt Wᵖ Wᶜ Xᴾ Xᴵ)
        (same : CTI.SameCtx Γ Γᵖ)
        (okᴾ : CTI.sourceStoreʷ Wᶜ ⊢↓[ just Xᴾ ] seal Xᴾ ★)
        (okᴵ : CTI.targetStoreʷ Wᶜ ⊢↓[ just Xᴵ ] seal Xᴵ ★)
        (prem : Wᵖ ∣ Γᵖ ⊢² Mᴾ ⊑ Mᴵ ∶ p★)
        (sealed : Wᵖ ∣ Γᵖ ⊢² Mᴾ ↓ seal Xᴾ ★ ⊑ Mᴵ ∶ qᵖ)
        (q : (＇ Xᴾ) CTI.⊑ᵂ⟨ Wᶜ ⟩ (＇ Xᴵ))
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → InsertedFundamentalProperty prem
      → InsertedFundamentalProperty sealed
      → ∀ k → InsertedTermRelation W ins q k Γ
          (Mᴾ ↓ seal Xᴾ ★) (Mᴵ ↓ seal Xᴵ ★)

    -- Milestone 3: universal elimination whose inserted operator
    -- imprecision is not the structural `∀⊑∀` (paired) or `∀⊑`
    -- (one-sided) view.
    type-application-nonstructural : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ}
        {Cᴾ : Ty (suc Δᴾ)} {Cᴵ : Ty (suc Δᴵ)}
        {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        (p∀ : `∀ Cᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ `∀ Cᴵ)
        (M⊑ : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
        (q : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ)
        (r : Cᴾ [ Aᴾ ]ᵗ CTI.⊑ᵂ⟨ Wᶜ ⟩ Cᴵ [ Aᴵ ]ᵗ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → NotPairedStructural (insert⊑ ins p∀)
      → InsertedFundamentalProperty M⊑
      → ∀ k → InsertedTermRelation W ins r k Γ
          (Mᴾ ⦂∀ Cᴾ [ Aᴾ ]) (Mᴵ ⦂∀ Cᴵ [ Aᴵ ])

    right-type-application-nonstructural : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
        {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
        {Γ : CTI.CtxImp Wᶜ}
        {Cᴾ : Ty (suc Δᴾ)} {Aᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
        {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
        (p∀ : `∀ Cᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        (M⊑ : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
        (q : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ ★)
        (r : Cᴾ [ Aᴾ ]ᵗ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → NotRightStructural (insert⊑ ins p∀)
      → InsertedFundamentalProperty M⊑
      → ∀ k → InsertedTermRelation W ins r k Γ
          (Mᴾ ⦂∀ Cᴾ [ Aᴾ ]) Mᴵ

------------------------------------------------------------------------
-- Closed-type helpers
------------------------------------------------------------------------

primArgTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (op : Prim)
  → renameᵗ ρ (primArgTy {Δ} op) ≡ primArgTy {Δ′} op
primArgTy-renameᵗ ρ addℕ = refl
primArgTy-renameᵗ ρ and𝔹 = refl

primResultTy-renameᵗ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (op : Prim)
  → renameᵗ ρ (primResultTy {Δ} op) ≡ primResultTy {Δ′} op
primResultTy-renameᵗ ρ addℕ = refl
primResultTy-renameᵗ ρ and𝔹 = refl

-- Relations at a closed type are stated at the canonical spelling of that
-- type; these helpers accept any spelling equal to it.

constant-case : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)} (κ : Const)
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
  → Rᴾ ≡ constTy κ
  → Rᴵ ≡ constTy κ
  → (q : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → CompiledTermRelation {W = W} q k Γ ($ κ) ($ κ)
constant-case κ refl refl q = constant-compatible κ {p = q}

primitive-case : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)} (op : Prim)
    {Pᴾ Qᴾ Rᴾ : Ty Δᴾ} {Pᴵ Qᴵ Rᴵ : Ty Δᴵ}
    {Lᴾ Mᴾ : Term Δᴾ} {Lᴵ Mᴵ : Term Δᴵ}
  → Pᴾ ≡ primArgTy op → Pᴵ ≡ primArgTy op
  → Qᴾ ≡ primArgTy op → Qᴵ ≡ primArgTy op
  → Rᴾ ≡ primResultTy op → Rᴵ ≡ primResultTy op
  → (p : Pᴾ ⊑ᵂ⟨ core W ⟩ Pᴵ)
  → (q : Qᴾ ⊑ᵂ⟨ core W ⟩ Qᴵ)
  → (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Lᴾ Lᴵ)
  → (∀ k → CompiledTermRelation {W = W} q k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} r k Γ
      (Lᴾ ⊕[ op ] Mᴾ) (Lᴵ ⊕[ op ] Mᴵ)
primitive-case op refl refl refl refl refl refl p q r =
  primitive-compatible op {p = p} {q = q} {r = r}

------------------------------------------------------------------------
-- The assembled theorem
------------------------------------------------------------------------

module Assembly (obligations : RemainingObligations) where
  open RemainingObligations obligations
  open Cast cast-values using
    (cast-cast-compatible; right-cast-compatible; left-cast-compatible)

  fundamental : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
      {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp Wᶜ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      {p : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ}
      (d : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
    → InsertedFundamentalProperty d

  -- Paired type application, dispatched on the inserted operator
  -- imprecision.  The structural lemma is instantiated at the syntactic
  -- spelling of the renamed body type and the result is reindexed to
  -- the term renaming's spelling.
  type-application-case : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
      {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp Wᶜ}
      {Cᴾ : Ty (suc Δᴾ)} {Cᴵ : Ty (suc Δᴵ)}
      {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      (p∀ : `∀ Cᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ `∀ Cᴵ)
      (M⊑ : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
      (q : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ)
      (r : Cᴾ [ Aᴾ ]ᵗ CTI.⊑ᵂ⟨ Wᶜ ⟩ Cᴵ [ Aᴵ ]ᵗ)
      {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
      (W : World Δᴾ′ Δᴵ′ Δᶜ′)
      (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
    → InsertedFundamentalProperty M⊑
    → ∀ k → InsertedTermRelation W ins r k Γ
        (Mᴾ ⦂∀ Cᴾ [ Aᴾ ]) (Mᴵ ⦂∀ Cᴵ [ Aᴵ ])
  type-application-case p∀ M⊑ q r W ins ih k
      with insert⊑ ins p∀ in inserted-eq | pairedView (insert⊑ ins p∀)
  type-application-case {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
      {Mᴾ = Mᴾ} {Mᴵ = Mᴵ} p∀ M⊑ q r {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} W ins ih k
      | _ | paired-structural p =
    compiled-term-relation-reindex r′ (insert⊑ ins r)
      (sym (rename-openᵗ (toRenameᵗ ρᴾ) Cᴾ Aᴾ))
      (sym (rename-openᵗ (toRenameᵗ ρᴵ) Cᴵ Aᴵ))
      refl
      (cong (λ T → renameᵗᵐ ρᴾ Mᴾ ⦂∀ T [ renameᵗ (toRenameᵗ ρᴾ) Aᴾ ])
        (sym (renameᵗ-cong Cᴾ (toRename-keep-eq ρᴾ))))
      (cong (λ T → renameᵗᵐ ρᴵ Mᴵ ⦂∀ T [ renameᵗ (toRenameᵗ ρᴵ) Aᴵ ])
        (sym (renameᵗ-cong Cᴵ (toRename-keep-eq ρᴵ))))
      (type-application-compatible {W = W}
        {Cᴾ = renameᵗ (extᵗ (toRenameᵗ ρᴾ)) Cᴾ}
        {Cᴵ = renameᵗ (extᵗ (toRenameᵗ ρᴵ)) Cᴵ}
        {p = p} {q = insert⊑ ins q} {r = r′}
        (λ j → compiled-term-relation-reindex
          (insert⊑ ins p∀) (I.∀⊑∀ p) refl refl refl refl refl
          (inserted-relation ih W ins j))
        k)
    where
    r′ : renameᵗ (extᵗ (toRenameᵗ ρᴾ)) Cᴾ [ renameᵗ (toRenameᵗ ρᴾ) Aᴾ ]ᵗ
        ⊑ᵂ⟨ core W ⟩
        renameᵗ (extᵗ (toRenameᵗ ρᴵ)) Cᴵ [ renameᵗ (toRenameᵗ ρᴵ) Aᴵ ]ᵗ
    r′ = subst≡ (λ T → T ⊑ᵂ⟨ core W ⟩ _)
      (rename-openᵗ (toRenameᵗ ρᴾ) Cᴾ Aᴾ)
      (subst≡ (λ T → _ ⊑ᵂ⟨ core W ⟩ T)
        (rename-openᵗ (toRenameᵗ ρᴵ) Cᴵ Aᴵ)
        (insert⊑ ins r))
  type-application-case p∀ M⊑ q r W ins ih k
      | _ | paired-nonstructural _ residual =
    type-application-nonstructural p∀ M⊑ q r W ins
      (subst≡ NotPairedStructural (sym inserted-eq) residual) ih k

  -- One-sided type application, dispatched on the inserted operator
  -- imprecision.
  right-type-application-case : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
      {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp Wᶜ}
      {Cᴾ : Ty (suc Δᴾ)} {Aᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      (p∀ : `∀ Cᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
      (M⊑ : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p∀)
      (q : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ ★)
      (r : Cᴾ [ Aᴾ ]ᵗ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ)
      {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
      (W : World Δᴾ′ Δᴵ′ Δᶜ′)
      (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
    → InsertedFundamentalProperty M⊑
    → ∀ k → InsertedTermRelation W ins r k Γ
        (Mᴾ ⦂∀ Cᴾ [ Aᴾ ]) Mᴵ
  right-type-application-case p∀ M⊑ q r W ins ih k
      with insert⊑ ins p∀ in inserted-eq | rightView (insert⊑ ins p∀)
  right-type-application-case {Cᴾ = Cᴾ} {Aᴾ = Aᴾ} {Bᴵ = Bᴵ}
      {Mᴾ = Mᴾ} {Mᴵ = Mᴵ} p∀ M⊑ q r {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} W ins ih k
      | _ | right-structural nonvar occurs p =
    compiled-term-relation-reindex r′ (insert⊑ ins r)
      (sym (rename-openᵗ (toRenameᵗ ρᴾ) Cᴾ Aᴾ))
      refl
      refl
      (cong (λ T → renameᵗᵐ ρᴾ Mᴾ ⦂∀ T [ renameᵗ (toRenameᵗ ρᴾ) Aᴾ ])
        (sym (renameᵗ-cong Cᴾ (toRename-keep-eq ρᴾ))))
      refl
      (right-type-application-compatible {W = W}
        {Cᴾ = renameᵗ (extᵗ (toRenameᵗ ρᴾ)) Cᴾ}
        {p = p} {nonvar = nonvar} {occurs = occurs}
        {q = insert⊑ ins q} {r = r′}
        (λ j → compiled-term-relation-reindex
          (insert⊑ ins p∀) (I.∀⊑ nonvar occurs p) refl refl refl refl refl
          (inserted-relation ih W ins j))
        k)
    where
    r′ : renameᵗ (extᵗ (toRenameᵗ ρᴾ)) Cᴾ [ renameᵗ (toRenameᵗ ρᴾ) Aᴾ ]ᵗ
        ⊑ᵂ⟨ core W ⟩ renameᵗ (toRenameᵗ ρᴵ) Bᴵ
    r′ = subst≡ (λ T → T ⊑ᵂ⟨ core W ⟩ _)
      (rename-openᵗ (toRenameᵗ ρᴾ) Cᴾ Aᴾ)
      (insert⊑ ins r)
  right-type-application-case p∀ M⊑ q r W ins ih k
      | _ | right-nonstructural _ residual =
    right-type-application-nonstructural p∀ M⊑ q r W ins
      (subst≡ NotRightStructural (sym inserted-eq) residual) ih k

  -- Lambda introduction: the endpoint typings of the lambda are obtained
  -- from the derivation and renamed along the insertion.
  lambda-case : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
      {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp Wᶜ}
      {Aᴾ Bᴾ : Ty Δᴾ} {Aᴵ Bᴵ : Ty Δᴵ}
      {pA : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ} {pB : Bᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Bᴵ}
      {Nᴾ : Term Δᴾ} {Nᴵ : Term Δᴵ}
      (body : Wᶜ ∣ CTI.ctx-imp Aᴾ Aᴵ pA ∷ Γ ⊢² Nᴾ ⊑ Nᴵ ∶ pB)
      {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
      (W : World Δᴾ′ Δᴵ′ Δᶜ′)
      (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
    → InsertedFundamentalProperty body
    → ∀ k → InsertedTermRelation W ins (I.⇒⊑⇒ pA pB) k Γ
        (ƛ Nᴾ) (ƛ Nᴵ)
  lambda-case {Γ = Γ} {pA = pA} {pB = pB}
      body {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} W ins ih k =
    compiled-term-relation-reindex
      (I.⇒⊑⇒ (insert⊑ ins pA) (insert⊑ ins pB))
      (insert⊑ ins (I.⇒⊑⇒ pA pB)) refl refl refl refl refl
      (lambda-compatible-from-body {W = W}
        {p = insert⊑ ins pA} {q = insert⊑ ins pB}
        precise-typing imprecise-typing
        (λ i i≤k → inserted-relation ih W ins i))
    where
    lambda-derivation = CTIR.ƛ⊑ƛ² body

    precise-typing =
      subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
        (sym (insertCtx-src ins Γ))
        (typing-renameᵗ (sourceStore-rename ins)
          (CTIT.source-typing² lambda-derivation))

    imprecise-typing =
      subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
        (sym (insertCtx-tgt ins Γ))
        (typing-renameᵗ (targetStore-rename ins)
          (CTIT.target-typing² lambda-derivation))

  -- The recursion.
  fundamental-relation′ : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
      {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
      {Γ : CTI.CtxImp Wᶜ}
      {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
      {p : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ}
      (d : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p)
      {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
      (W : World Δᴾ′ Δᴵ′ Δᶜ′)
      (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
    → ∀ k → InsertedTermRelation W ins p k Γ Mᴾ Mᴵ
  fundamental-relation′ (CTIR.x⊑x² x∈) W ins k =
    variable-compatible (insertCtx-∋ ins x∈)
  fundamental-relation′ (CTIR.κ⊑κ² κ p) {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} W ins k =
    constant-case κ
      (sym (constTy-renameᵗ (toRenameᵗ ρᴾ) κ))
      (sym (constTy-renameᵗ (toRenameᵗ ρᴵ) κ))
      (insert⊑ ins p)
  fundamental-relation′ {Γ = Γ} (CTIR.blame⊑² target⊢ p) W ins k =
    blame-compatible
      (subst≡ (λ Γ′ → ⟨ _ , _ , Γ′ ⟩ ⊢ _ ⦂ _)
        (sym (insertCtx-tgt ins Γ))
        (typing-renameᵗ (targetStore-rename ins) target⊢))
      (insert⊑ ins p)
  fundamental-relation′ (CTIR.ƛ⊑ƛ² body) W ins k =
    lambda-case body W ins (fundamental body) k
  fundamental-relation′ (CTIR.·⊑·² {pA = pA} {pB = pB} L⊑ M⊑) W ins k =
    application-compatible {W = W}
      {p = insert⊑ ins pA} {q = insert⊑ ins pB}
      (λ j → compiled-term-relation-reindex
        (insert⊑ ins (I.⇒⊑⇒ pA pB))
        (I.⇒⊑⇒ (insert⊑ ins pA) (insert⊑ ins pB))
        refl refl refl refl refl
        (fundamental-relation′ L⊑ W ins j))
      (fundamental-relation′ M⊑ W ins) k
  fundamental-relation′ (CTIR.⊕⊑⊕² op {p = p} {q = q} L⊑ M⊑ r)
      {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} W ins k =
    primitive-case op
      (primArgTy-renameᵗ (toRenameᵗ ρᴾ) op)
      (primArgTy-renameᵗ (toRenameᵗ ρᴵ) op)
      (primArgTy-renameᵗ (toRenameᵗ ρᴾ) op)
      (primArgTy-renameᵗ (toRenameᵗ ρᴵ) op)
      (primResultTy-renameᵗ (toRenameᵗ ρᴾ) op)
      (primResultTy-renameᵗ (toRenameᵗ ρᴵ) op)
      (insert⊑ ins p) (insert⊑ ins q) (insert⊑ ins r)
      (fundamental-relation′ L⊑ W ins)
      (fundamental-relation′ M⊑ W ins) k
  fundamental-relation′ (CTIR.cast⊑cast² c c′ M⊑ q)
      {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} W ins k =
    cast-cast-compatible {W = W} (renameᵐᶜ ρᴾ c) (renameᵐᶜ ρᴵ c′)
      (insert⊑ ins q) (fundamental-relation′ M⊑ W ins) k
  fundamental-relation′ (CTIR.⊑cast² c′ M⊑ q) {ρᴵ = ρᴵ} W ins k =
    right-cast-compatible {W = W} (renameᵐᶜ ρᴵ c′)
      (insert⊑ ins q) (fundamental-relation′ M⊑ W ins) k
  fundamental-relation′ (CTIR.cast⊑² c M⊑ q) {ρᴾ = ρᴾ} W ins k =
    left-cast-compatible {W = W} (renameᵐᶜ ρᴾ c)
      (insert⊑ ins q) (fundamental-relation′ M⊑ W ins) k
  fundamental-relation′ (CTIR.•⊑•² p∀ M⊑ q r) W ins k =
    type-application-case p∀ M⊑ q r W ins (fundamental M⊑) k
  fundamental-relation′ (CTIR.•⊑² p∀ M⊑ q r) W ins k =
    right-type-application-case p∀ M⊑ q r W ins (fundamental M⊑) k
  fundamental-relation′ (CTIR.Λ⊑Λ² liftΓ vVᴾ vVᴵ body q) W ins k =
    universal-intro liftΓ vVᴾ vVᴵ body q W ins (fundamental body) k
  fundamental-relation′
      (CTIR.Λ⊑² nonvar occurs liftΓ vVᴾ target⊢ body q) W ins k =
    right-universal-intro nonvar occurs liftΓ vVᴾ target⊢ body q W ins
      (fundamental body) k
  fundamental-relation′
      (CTIR.Λ⊑²-smart-comma nonvar occurs smart liftΓ vVᴾ target⊢
        body q) W ins k =
    right-universal-smart-intro nonvar occurs smart liftΓ vVᴾ target⊢
      body q W ins (fundamental body) k
  fundamental-relation′ (CTIR.⊑reveal² mono rebase same ok prem q)
      W ins k =
    target-reveal mono rebase same ok prem q W ins (fundamental prem) k
  fundamental-relation′ (CTIR.⊑conceal² mono rebase same ok prem q)
      W ins k =
    target-conceal mono rebase same ok prem q W ins (fundamental prem) k
  fundamental-relation′ (CTIR.reveal⊑² mono rebase same ok prem q)
      W ins k =
    source-reveal mono rebase same ok prem q W ins (fundamental prem) k
  fundamental-relation′
      (CTIR.conceal⊑²-seal-star-open
        open-target mono rebase same ok prem q) W ins k =
    source-conceal-seal-star open-target mono rebase same ok prem q
      W ins (fundamental prem) k
  fundamental-relation′
      (CTIR.conceal⊑²-source-ok
        ok-source mono rebase same ok prem q) W ins k =
    source-conceal ok-source mono rebase same ok prem q
      W ins (fundamental prem) k
  fundamental-relation′
      (CTIR.reveal⊑reveal² mono rebase same okᴾ okᴵ prem q) W ins k =
    reveal-reveal mono rebase same okᴾ okᴵ prem q W ins
      (fundamental prem) k
  fundamental-relation′
      (CTIR.conceal⊑conceal²
        partner mono rebase same okᴾ okᴵ prem q) W ins k =
    conceal-conceal partner mono rebase same okᴾ okᴵ prem q W ins
      (fundamental prem) k
  fundamental-relation′
      (CTIR.packaged-seal-star²
        partner mono rebase same okᴾ okᴵ prem sealed q) W ins k =
    packaged-seal-star partner mono rebase same okᴾ okᴵ prem sealed q
      W ins (fundamental prem) (fundamental sealed) k

  fundamental d = inserted-proof (fundamental-relation′ d)
