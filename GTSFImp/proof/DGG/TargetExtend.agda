module proof.DGG.TargetExtend where

-- File Charter:
--   * Transports version-2 cast-term-imprecision derivations across
--     right-only target store extension.
--   * Provides the target-side weakening helpers for indexed conversions,
--     partner predicates, and derivation-level target extension.
--   * The public theorem specializes to the parked single right bind used by
--     the DGG instantiation cases; internal helpers keep target weakening
--     separate from source-side structure.

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-lift)
open import Consistency using (_↪ᵗ_; keep; toRenameᵗ; wk↪ᵗ)
import Conversion
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import CastTerms using (Term; Value; renameᵗᵐ)
import Reduction
open import Reduction using (bind; _∷_; [])
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-ext; StoreRename-keep; StoreRename-wk-bind;
   renameᵗᵐ-preserves-Value; toRename-wk-eq; typing-renameᵗ)
open import proof.ImprecisionConsistency using (fin-suc-injective)
open import proof.DGG.Parked.ParkedWorldProof using (right-bind-⊑ᵂ)
import proof.Imprecision as PI

open CTI2 using
  ( World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_
  ; PivotJoin; _⊢↑[_]_; _⊢↓[_]_
  )

------------------------------------------------------------------------
-- Optional target pivots and indexed conversion typing
------------------------------------------------------------------------

mapPivot : ∀ {Δ Δ′}
  → (TyVar Δ → TyVar Δ′)
  → Maybe (TyVar Δ)
  → Maybe (TyVar Δ′)
mapPivot ρ (just X) = just (ρ X)
mapPivot ρ nothing = nothing

renamePivotJoin : ∀ {Δ Δ′} {p q r : Maybe (TyVar Δ)}
  → (ρ : TyVar Δ → TyVar Δ′)
  → PivotJoin p q r
  → PivotJoin (mapPivot ρ p) (mapPivot ρ q) (mapPivot ρ r)
renamePivotJoin ρ CTI2.join-none = CTI2.join-none
renamePivotJoin ρ CTI2.join-left = CTI2.join-left
renamePivotJoin ρ CTI2.join-right = CTI2.join-right
renamePivotJoin ρ CTI2.join-both = CTI2.join-both

mutual
  reveal-renameˣ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X? A B}
      {c : Conversion.Conv↑ Δ A B}
    → StoreRename ρ Σ Σ′
    → Σ ⊢↑[ X? ] c
    → Σ′ ⊢↑[ mapPivot ρ X? ] rename↑ ρ c
  reveal-renameˣ hΣ (CTI2.⊢↑-unsealˣ X∈) =
    CTI2.⊢↑-unsealˣ (hΣ X∈)
  reveal-renameˣ hΣ (CTI2.⊢↑-⇒ˣ join c⊢ d⊢) =
    CTI2.⊢↑-⇒ˣ (renamePivotJoin _ join)
      (conceal-renameˣ hΣ c⊢) (reveal-renameˣ hΣ d⊢)
  reveal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↑-∀ˣ c⊢) =
    CTI2.⊢↑-∀ˣ (reveal-renameˣ (StoreRename-ext hΣ) c⊢)
  reveal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↑-∀-idˣ c⊢) =
    CTI2.⊢↑-∀-idˣ (reveal-renameˣ (StoreRename-ext hΣ) c⊢)
  reveal-renameˣ hΣ CTI2.⊢↑-idˣ = CTI2.⊢↑-idˣ

  conceal-renameˣ : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′}
      {Σ : TyStore Δ} {Σ′ : TyStore Δ′} {X? A B}
      {c : Conversion.Conv↓ Δ A B}
    → StoreRename ρ Σ Σ′
    → Σ ⊢↓[ X? ] c
    → Σ′ ⊢↓[ mapPivot ρ X? ] rename↓ ρ c
  conceal-renameˣ hΣ (CTI2.⊢↓-sealˣ X∈) =
    CTI2.⊢↓-sealˣ (hΣ X∈)
  conceal-renameˣ hΣ (CTI2.⊢↓-⇒ˣ join c⊢ d⊢) =
    CTI2.⊢↓-⇒ˣ (renamePivotJoin _ join)
      (reveal-renameˣ hΣ c⊢) (conceal-renameˣ hΣ d⊢)
  conceal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↓-∀ˣ c⊢) =
    CTI2.⊢↓-∀ˣ (conceal-renameˣ (StoreRename-ext hΣ) c⊢)
  conceal-renameˣ {ρ = ρ} hΣ (CTI2.⊢↓-∀-idˣ c⊢) =
    CTI2.⊢↓-∀-idˣ (conceal-renameˣ (StoreRename-ext hΣ) c⊢)
  conceal-renameˣ hΣ CTI2.⊢↓-idˣ = CTI2.⊢↓-idˣ

------------------------------------------------------------------------
-- Target-term syntactic side conditions
------------------------------------------------------------------------

notTopTag-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) {M : Term Δ}
  → CTI2.NotTopTag M
  → CTI2.NotTopTag (renameᵗᵐ ρ M)
notTopTag-rename ρ (CTI2.not-` x) = CTI2.not-` x
notTopTag-rename ρ CTI2.not-ƛ = CTI2.not-ƛ
notTopTag-rename ρ CTI2.not-· = CTI2.not-·
notTopTag-rename ρ CTI2.not-Λ = CTI2.not-Λ
notTopTag-rename ρ CTI2.not-⦂∀ = CTI2.not-⦂∀
notTopTag-rename ρ (CTI2.not-$ κ) = CTI2.not-$ κ
notTopTag-rename ρ (CTI2.not-⊕ op) = CTI2.not-⊕ op
notTopTag-rename ρ CTI2.not-↑ = CTI2.not-↑
notTopTag-rename ρ CTI2.not-↓ = CTI2.not-↓
notTopTag-rename ρ CTI2.not-blame = CTI2.not-blame

renameRep★PartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {X : TyVar Δᴸ} {P Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.Rep★PartnerOK W X P Xᴿ? M′
  → CTI2.Rep★PartnerOK W′ X P
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameRep★PartnerOK align (CTI2.rep★-untagged nt) =
  CTI2.rep★-untagged (notTopTag-rename _ nt)
renameRep★PartnerOK align (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag (renameNonVar _ Gnv)
renameRep★PartnerOK align (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag (align aligned)
renameRep★PartnerOK align
    (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X (align aligned)
renameRep★PartnerOK align (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (renameRep★PartnerOK align ok)

renameSealPartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {X : TyVar Δᴸ} {P R Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.SealPartnerOK W X P R Xᴿ? M′
  → CTI2.SealPartnerOK W′ X P R
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameSealPartnerOK align (CTI2.star-rep-target ok) =
  CTI2.star-rep-target (renameRep★PartnerOK align ok)
renameSealPartnerOK align (CTI2.plain-target nt) =
  CTI2.plain-target (notTopTag-rename _ nt)
renameSealPartnerOK align CTI2.name-protected-target =
  CTI2.name-protected-target

renameSourceConcealPartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.SourceConcealPartnerOK W M c Xᴿ? M′
  → CTI2.SourceConcealPartnerOK W′ M c
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameSourceConcealPartnerOK align (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok (renameSealPartnerOK align ok)
renameSourceConcealPartnerOK align CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
renameSourceConcealPartnerOK align CTI2.all-conceal-target =
  CTI2.all-conceal-target
renameSourceConcealPartnerOK align CTI2.id-conceal-target =
  CTI2.id-conceal-target

renameMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {ρ : Δᴿ ↪ᵗ Δᴿ′}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → (∀ {X₀ Y₀}
      → CTI2.CenterAligned W X₀ Y₀
      → CTI2.CenterAligned W′ X₀ (toRenameᵗ ρ Y₀))
  → CTI2.MatchedConcealPartnerOK W M c Xᴿ? M′
  → CTI2.MatchedConcealPartnerOK W′ M c
      (mapPivot (toRenameᵗ ρ) Xᴿ?) (renameᵗᵐ ρ M′)
renameMatchedConcealPartnerOK align
    (CTI2.matched-seal-star-partner ok) =
  CTI2.matched-seal-star-partner (renameRep★PartnerOK align ok)
renameMatchedConcealPartnerOK align
    (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
renameMatchedConcealPartnerOK align CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
renameMatchedConcealPartnerOK align CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
renameMatchedConcealPartnerOK align CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target

------------------------------------------------------------------------
-- Rebasing evidence across one root right bind
------------------------------------------------------------------------

right-target-map : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ)
  → ∀ Y
  → toRenameᵗ (keep η) (toRenameᵗ wk↪ᵗ Y)
      ≡ Fin.suc (toRenameᵗ η Y)
right-target-map η Y =
  cong (toRenameᵗ (keep η)) (toRename-wk-eq Y)

right-resolveVar-map : ∀ {Δ} (Σ : TyStore Δ) (B : Ty Δ)
  → ∀ Y
  → CTI2.resolveVar (TyStore.store-bind Σ B) (toRenameᵗ wk↪ᵗ Y)
      ≡ ⇑ᵗ (CTI2.resolveVar Σ Y)
right-resolveVar-map Σ B Y =
  cong (CTI2.resolveVar (TyStore.store-bind Σ B)) (toRename-wk-eq Y)

right-storeRep : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTI2.StoreRepImp W Xᴸ Xᴿ
  → CTI2.StoreRepImp (CTI2.rightOnlyWorld W B)
      Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
right-storeRep {W = W} {B = B} {Xᴿ = Xᴿ}
    (CTI2.store-rep-imp represented) =
  CTI2.store-rep-imp
    (subst≡
      (λ R → CTI2.resolveVar (CTI2.sourceStoreʷ W) _
        ⊑ᵂ⟨ CTI2.rightOnlyWorld W B ⟩ R)
      (sym (right-resolveVar-map (CTI2.targetStoreʷ W) B Xᴿ))
      (right-bind-⊑ᵂ {W = W} {B′ = B} represented))

rightRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ Xᴿ}
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.RebaseAt (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B) Xᴸ (toRenameᵗ wk↪ᵗ Xᴿ)
rightRebaseAt {W = W} {W′ = W′} {B = B} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    (CTI2.rebase-at
      (CTI2.same-runtime source-eq target-eq)
      offL frozenR aligned reps) =
  CTI2.rebase-at
    (CTI2.same-runtime source-eq
      (cong (λ Σ → TyStore.store-bind Σ B) target-eq))
    (λ Y≢ → cong Fin.suc (offL Y≢))
    frozenR′
    (trans (cong Fin.suc aligned)
      (sym (right-target-map (CTI2.ηᴿʷ W′) Xᴿ)))
    (right-storeRep reps)
  where
  frozenR′ : ∀ Y
    → toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W′ B)) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Y
  frozenR′ Fin.zero = refl
  frozenR′ (Fin.suc Y) = cong Fin.suc (frozenR Y)

right-disaligned : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) {B : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
  → (∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ
      (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Xᴿ
        ≢ toRenameᵗ
          (CTI2.ηᴸʷ (CTI2.rightOnlyWorld W B)) Xᴸ
right-disaligned W disaligned Fin.zero ()
right-disaligned W disaligned (Fin.suc Xᴿ) eq =
  disaligned Xᴿ (fin-suc-injective eq)

rightRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ?}
  → CTI2.RebaseAtᴸ W W′ Xᴸ?
  → CTI2.RebaseAtᴸ (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B) Xᴸ?
rightRebaseAtᴸ CTI2.rebase-idᴸ = CTI2.rebase-idᴸ
rightRebaseAtᴸ (CTI2.rebase-varᴸ rb) =
  CTI2.rebase-varᴸ (rightRebaseAt rb)
rightRebaseAtᴸ {W = W} {B = B}
    (CTI2.rebase-onlyᴸ to-star disaligned represented) =
  CTI2.rebase-onlyᴸ to-star (right-disaligned W {B = B} disaligned)
    (right-bind-⊑ᵂ {W = W} {B′ = B} represented)

rightTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
  → CTI2.TagRebaseAtᴸ W W′ Xᴸ? Xᴿ?
  → CTI2.TagRebaseAtᴸ (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B) Xᴸ?
      (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightTagRebaseAtᴸ CTI2.tag-rebase-idᴸ = CTI2.tag-rebase-idᴸ
rightTagRebaseAtᴸ (CTI2.tag-rebase-varᴸ rb) =
  CTI2.tag-rebase-varᴸ (rightRebaseAt rb)
rightTagRebaseAtᴸ {W = W} {B = B}
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented) =
  CTI2.tag-rebase-onlyᴸ to-star
    (right-disaligned W {B = B} disaligned)
    (right-bind-⊑ᵂ {W = W} {B′ = B} represented)

rightRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ} {Xᴿ?}
  → CTI2.RebaseAtᴿ W W′ Xᴿ?
  → CTI2.RebaseAtᴿ (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld W′ B)
      (mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
rightRebaseAtᴿ CTI2.rebase-idᴿ = CTI2.rebase-idᴿ
rightRebaseAtᴿ (CTI2.rebase-varᴿ rb) =
  CTI2.rebase-varᴿ (rightRebaseAt rb)

------------------------------------------------------------------------
-- Retargeting derivations
------------------------------------------------------------------------

mapCtxᴿ-∋ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    {γ : CtxImp W} {x A B}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → γ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B p
  → ECR.mapCtxᴿ ext γ CTI2.∋ʷ x ⦂
      CTI2.ctx-imp A (χs Reduction.▶ᵗ B) (ECR.transport⊑ᵂ ext p)
mapCtxᴿ-∋ ext CTI2.Zʷ = CTI2.Zʷ
mapCtxᴿ-∋ ext (CTI2.Sʷ x∈) = CTI2.Sʷ (mapCtxᴿ-∋ ext x∈)

⊢²-retarget : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p q : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶ q
⊢²-retarget {W = W} {γ = γ} {M = M} {N = N} {p = p} {q = q} d =
  subst≡ (λ r → W ∣ γ ⊢² M ⊑ N ∶ r) (PI.⊑-unique p q) d

------------------------------------------------------------------------
-- Public single-bind surface
------------------------------------------------------------------------

TargetExtendBindᵀ : Set
TargetExtendBindᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → (ext : ECR.WorldExtendᴿ (bind B′ ∷ []) W
      (CTI2.rightOnlyWorld W B′))
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → CTI2.rightOnlyWorld W B′
      ∣ ECR.mapCtxᴿ ext γ
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ M′ ∶ ECR.transport⊑ᵂ ext p
