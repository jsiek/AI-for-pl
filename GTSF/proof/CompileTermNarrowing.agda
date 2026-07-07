module proof.CompileTermNarrowing where

-- File Charter:
--   * Compile monotonicity for source-level gradual term narrowing.
--   * States that compiling two source terms related by
--     `GradualTermNarrowing` yields target terms related by
--     `MediatedNarrowing`.
--   * Structural and cast-plan cases are proved directly; the remaining
--     right-only polymorphic and ν bridges are explicit fields of the
--     specialized `CompileIndexMediation` plan.

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (zero; suc; z<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; inspect; subst; sym; trans; [_])

open import Types
open import Ctx using (CtxWf; ctxWf-∷; ⤊ᵗ)
open import Compile
  using
    ( CastPlan
    ; arrow★-consistent
    ; cast
    ; compile
    ; compile-value
    ; consistency-cast-plan
    ; down⊒
    ; empty-store-wf-at
    ; lower
    ; upDual⊒
    )
open import NuTerms
  renaming
    ( _∣_∣_⊢_⦂_ to _∣_∣_⊢ᵀ_⦂_
    ; ⊢` to ⊢ᵀ`
    ; ⊢ƛ to ⊢ᵀƛ
    ; ⊢Λ to ⊢ᵀΛ
    ; ⊢$ to ⊢ᵀ$
    )
open import GradualTerms
  using (GTerm; _·[_]_; Λ_; _`[_]; _⊕[_at_]_)
  renaming
    ( _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    ; ⊢⊕ to ⊢ᴳ⊕
    )
open import NarrowWiden using
  ( CtxNrw
  ; CtxNrwEntry
  ; ctx-nrw
  ; cross
  ; id-＇
  ; id-‵
  ; _∣_∣_⊢_∶_⊒_
  ; _∣_⊢_∶ᶜ_⊒_
  ; fun-narrow-domain-dualᶜ
  ; narrow-mode-relax
  ; narrow-weaken
  )
  renaming (gen to genⁿ)
open import Coercions using
  ( Coercion
  ; ModeIncl
  ; cast-gen
  ; gen
  ; genᵈ
  ; id
  ; tag-or-idᵈ
  ; _↦_
  ; cast-id
  )
  renaming (`∀ to `∀ᶜ)
open import Primitives using (addℕ; κℕ; constTy)
open import proof.NuTermProperties using (CtxWf-⤊; term-weaken)
open import proof.CoercionProperties using (coercion-wfᵐ)
open import Store using (StoreIncl)
open import StoreCorrespondence using
  ( SealCorr
  ; ⇑ᶜorr
  ; ⇑ʳᶜorr
  ; corr-⇑ʳᶜorr
  ; leftStore
  ; rightStore-⇑ʳᶜorr
  )
open import Mediation using
  ( MedTy
  ; MatchedVar
  ; med-var
  ; med-⇒
  ; medTy-mapʳ
  ; mv-shiftʳ
  )
open import proof.ImprecisionProperties using (~-refl; ~-sym)
open import TermNarrowingSeparated using
  ( CtxCorr
  ; CtxCorrEntry
  ; ctx-entry
  ; leftCtx
  ; ⇑ᵍᶜ
  )

open import GradualTermNarrowing
  using
    ( _∣_∣_⊢ᴳ_⊒_∶_⦂_⊒_
    ; gradual-term-typing-endpoints
    ; x⊒xᴳ
    ; ƛ⊒ƛᴳ
    ; ·⊒·ᴳ
    ; Λ⊒Λᴳ
    ; ⊒Λᴳ
    ; []⊒[]ᴳ
    ; ⊒[]ᴳ
    ; κ⊒κᴳ
    ; ⊕⊒⊕ᴳ
    ; gradual-term-narrowing-source-typing
    ; gradual-term-narrowing-target-typing
    ; gradual-term-narrowing-index-typing
    ; srcCtxⁿ
    ; tgtCtxⁿ
    ; srcCtxⁿ-⇑ᵍ
    ; tgtCtxⁿ-⇑ᵍ
    )
open import MediatedNarrowing
  using
    ( _∣_∣_∣_⊢_⊒_∶_⦂_⊒ᵐ_
    ; _∣_∣_∣_⊢_∶_⊒ᵐ_
    ; _∣_∣_⊢_∶ᶜ_⊒ᵐ_
    ; fun-narrow-domain-dualᵐᶜ
    ; fun-narrow-domain-dual-typingᵐᶜ
    ; ⇑ʳᵍᶜ
    ; x⊒xᵗ
    ; ƛ⊒ƛᵗ
    ; ·⊒·ᵗ
    ; Λ⊒Λᵗ
    ; ⊒Λᵗ
    ; κ⊒κᵗ
    ; ⊕⊒⊕ᵗ
    ; cast+⊒ᵗ
    ; cast-⊒ᵗ
    ; ⊒cast+ᵗ
    ; ⊒cast-ᵗ
    )

ctxNrwToCorrEntry : CtxNrwEntry → CtxCorrEntry
ctxNrwToCorrEntry (ctx-nrw A B p) = ctx-entry A B p

ctxNrwToCorr : CtxNrw → CtxCorr
ctxNrwToCorr = map ctxNrwToCorrEntry

ctxNrwToCorr-⇑ :
  ∀ γ →
  ctxNrwToCorr (GradualTermNarrowing.⇑ᵍ γ) ≡ ⇑ᵍᶜ (ctxNrwToCorr γ)
ctxNrwToCorr-⇑ [] = refl
ctxNrwToCorr-⇑ (ctx-nrw A B p ∷ γ) =
  cong₂ _∷_ refl (ctxNrwToCorr-⇑ γ)

ctxNrwToCorr-∋ :
  ∀ {γ x A B p} →
  γ ∋ x ⦂ ctx-nrw A B p →
  ctxNrwToCorr γ ∋ x ⦂ ctx-entry A B p
ctxNrwToCorr-∋ Z = Z
ctxNrwToCorr-∋ (S x∋p) = S (ctxNrwToCorr-∋ x∋p)

srcCtxⁿ-∋ :
  ∀ {γ x A B p} →
  γ ∋ x ⦂ ctx-nrw A B p →
  srcCtxⁿ γ ∋ x ⦂ A
srcCtxⁿ-∋ Z = Z
srcCtxⁿ-∋ (S x∋p) = S (srcCtxⁿ-∋ x∋p)

tgtCtxⁿ-∋ :
  ∀ {γ x A B p} →
  γ ∋ x ⦂ ctx-nrw A B p →
  tgtCtxⁿ γ ∋ x ⦂ B
tgtCtxⁿ-∋ Z = Z
tgtCtxⁿ-∋ (S x∋p) = S (tgtCtxⁿ-∋ x∋p)

leftCtx-ctxNrwToCorr :
  ∀ γ →
  leftCtx (ctxNrwToCorr γ) ≡ srcCtxⁿ γ
leftCtx-ctxNrwToCorr [] = refl
leftCtx-ctxNrwToCorr (ctx-nrw A B p ∷ γ) =
  cong (A ∷_) (leftCtx-ctxNrwToCorr γ)

record CompileIndexMediation (Δ : TyCtx) (ρ : SealCorr) : Set₁ where
  inductive
  field
    indexᵐᶜ :
      ∀ {p A B} →
      Δ ∣ [] ⊢ p ∶ᶜ A ⊒ B →
      Δ ∣ Δ ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ B

    fun-domain-dualᵐᶜ :
      ∀ {p q A A′ B B′} →
      (p↦qᶜ : Δ ∣ [] ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
      fun-narrow-domain-dualᵐᶜ (indexᵐᶜ p↦qᶜ) ≡
        fun-narrow-domain-dualᶜ p↦qᶜ

    right-only-forall-bodyᵐ :
      ∀ {γ N V′ p A Aʳ B} →
      (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
      (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
      (N⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ N ⦂ A) →
      (V′⊢ : suc Δ ∣ ⤊ᵗ (tgtCtxⁿ γ) ⊢ᴳ V′ ⦂ B) →
      Δ ∣ Δ ∣ ρ ⊢ gen Aʳ p ∶ᶜ A ⊒ᵐ `∀ B →
      suc Δ ∣ [] ∣ GradualTermNarrowing.⇑ᵍ γ
        ⊢ᴳ GradualTermNarrowing.⇑ᵗᴳ N ⊒ V′ ∶ p ⦂ ⇑ᵗ A ⊒ B →
      Δ ∣ suc Δ ∣ ⇑ʳᶜorr ρ ∣ ⇑ʳᵍᶜ (ctxNrwToCorr γ) ⊢
        proj₁ (compile srcΓ-wf N⊢) ⊒
        proj₁ (compile (CtxWf-⤊ tgtΓ-wf) V′⊢)
          ∶ p ⦂ A ⊒ᵐ B

    type-applicationνᵐ :
      ∀ {γ M M′ T T′ A B p q r} →
      (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
      (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
      (MT⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ M `[ T ] ⦂ A [ T ]ᵗ) →
      (M′T′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ M′ `[ T′ ] ⦂ B [ T′ ]ᵗ) →
      Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ `∀ᶜ p ⦂ `∀ A ⊒ `∀ B →
      Δ ∣ Δ ∣ ρ ⊢ q ∶ᶜ T ⊒ᵐ T′ →
      Δ ∣ Δ ∣ ρ ⊢ r ∶ᶜ A [ T ]ᵗ ⊒ᵐ B [ T′ ]ᵗ →
      Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢
        proj₁ (compile srcΓ-wf MT⊢) ⊒
        proj₁ (compile tgtΓ-wf M′T′⊢)
          ∶ r ⦂ A [ T ]ᵗ ⊒ᵐ B [ T′ ]ᵗ

    target-type-applicationνᵐ :
      ∀ {γ M M′ T′ A B p q r} →
      (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
      (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
      (M⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ M ⦂ A) →
      (M′T′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ M′ `[ T′ ] ⦂ B [ T′ ]ᵗ) →
      Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ gen A p ⦂ A ⊒ `∀ B →
      Δ ∣ Δ ∣ ρ ⊢ q ∶ᶜ ★ ⊒ᵐ T′ →
      Δ ∣ Δ ∣ ρ ⊢ r ∶ᶜ A ⊒ᵐ B [ T′ ]ᵗ →
      Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢
        proj₁ (compile srcΓ-wf M⊢) ⊒
        proj₁ (compile tgtΓ-wf M′T′⊢)
          ∶ r ⦂ A ⊒ᵐ B [ T′ ]ᵗ

    shiftᵐ :
      CompileIndexMediation (suc Δ) (⇑ᶜorr ρ)

open CompileIndexMediation

no-empty-var-med :
  ∀ {Aʳ} →
  MedTy (MatchedVar []) (＇ zero) Aʳ →
  ⊥
no-empty-var-med (med-var ())

empty-var-indexᵐ-impossible :
  suc zero ∣ suc zero ∣ [] ⊢ id (＇ zero) ∶ᶜ ＇ zero ⊒ᵐ ＇ zero →
  ⊥
empty-var-indexᵐ-impossible (stores , hA , hB , Aʳ , medA , home) =
  no-empty-var-med medA

empty-var-lambdaᵐ-impossible :
  suc zero ∣ suc zero ∣ [] ∣ [] ⊢
    ƛ (` zero) ⊒ ƛ (` zero)
      ∶ id (＇ zero) ↦ id (＇ zero)
      ⦂ (＇ zero ⇒ ＇ zero) ⊒ᵐ (＇ zero ⇒ ＇ zero) →
  ⊥
empty-var-lambdaᵐ-impossible
    (ƛ⊒ƛᵗ (stores , hA , hB , Aʳ , med-⇒ medA medB , home) body) =
  no-empty-var-med medA

-- Consequently the current mediated relation cannot express the
-- shared-store polymorphic identity example at the empty correspondence.
empty-poly-idᵐ-impossible :
  zero ∣ zero ∣ [] ∣ [] ⊢
    Λ (ƛ (` zero)) ⊒ Λ (ƛ (` zero))
      ∶ `∀ᶜ (id (＇ zero) ↦ id (＇ zero))
      ⦂ `∀ (＇ zero ⇒ ＇ zero) ⊒ᵐ `∀ (＇ zero ⇒ ＇ zero) →
  ⊥
empty-poly-idᵐ-impossible (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′) =
  empty-var-lambdaᵐ-impossible V⊒V′

-- The plan cannot be instantiated by the bare empty correspondence:
-- after shifting under a type binder, the source index `id (＇ zero)`
-- needs a matched variable witness, but `MatchedVar []` has none.
empty-shift-index-plan-impossible :
  CompileIndexMediation (suc zero) [] →
  ⊥
empty-shift-index-plan-impossible med
    with indexᵐᶜ med (cast-id (wfVar z<s) refl , cross (id-＇ zero))
empty-shift-index-plan-impossible med | varᶜ =
  empty-var-indexᵐ-impossible varᶜ

empty-compile-index-plan-impossible :
  CompileIndexMediation zero [] →
  ⊥
empty-compile-index-plan-impossible med =
  empty-shift-index-plan-impossible (shiftᵐ med)

compile-context-subst-term :
  ∀ {Δ Γ Γ′ M A}
  → (Γ≡Γ′ : Γ ≡ Γ′)
  → (Γ-wf : CtxWf Δ Γ)
  → (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A)
  → proj₁
      (compile
        (subst (CtxWf Δ) Γ≡Γ′ Γ-wf)
        (subst (λ Γ₀ → Δ ∣ Γ₀ ⊢ᴳ M ⦂ A) Γ≡Γ′ M⊢))
      ≡ proj₁ (compile Γ-wf M⊢)
compile-context-subst-term refl Γ-wf M⊢ = refl

gradual-typing-subst-sym-subst :
  ∀ {Δ Γ Γ′ M A} →
  (Γ≡Γ′ : Γ ≡ Γ′) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  subst (λ Γ₀ → Δ ∣ Γ₀ ⊢ᴳ M ⦂ A) (sym Γ≡Γ′)
    (subst (λ Γ₀ → Δ ∣ Γ₀ ⊢ᴳ M ⦂ A) Γ≡Γ′ M⊢) ≡ M⊢
gradual-typing-subst-sym-subst refl M⊢ = refl

mediated-narrowing-cong-terms :
  ∀ {ΔL ΔR ρ γ L L′ R R′ p A B}
  → L ≡ L′
  → R ≡ R′
  → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ R ∶ p ⦂ A ⊒ᵐ B
  → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L′ ⊒ R′ ∶ p ⦂ A ⊒ᵐ B
mediated-narrowing-cong-terms refl refl L⊒R = L⊒R

mediated-narrowing-context-cong :
  ∀ {ΔL ΔR ρ γ γ′ L R p A B}
  → γ ≡ γ′
  → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ R ∶ p ⦂ A ⊒ᵐ B
  → ΔL ∣ ΔR ∣ ρ ∣ γ′ ⊢ L ⊒ R ∶ p ⦂ A ⊒ᵐ B
mediated-narrowing-context-cong refl L⊒R = L⊒R

mediated-narrowing-index-cong :
  ∀ {ΔL ΔR ρ γ L R p p′ A B}
  → p ≡ p′
  → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ R ∶ p ⦂ A ⊒ᵐ B
  → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ R ∶ p′ ⦂ A ⊒ᵐ B
mediated-narrowing-index-cong refl L⊒R = L⊒R

const-indexᶜ :
  ∀ {Δ} κ →
  Δ ∣ [] ⊢ id (constTy κ) ∶ᶜ constTy κ ⊒ constTy κ
const-indexᶜ (κℕ n) = cast-id wfBase refl , cross (id-‵ `ℕ)

fun-source-domain-wf :
  ∀ {Δ p q A A′ B B′} →
  Δ ∣ [] ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  WfTy Δ A
fun-source-domain-wf p↦qᶜ
    with coercion-wfᵐ empty-store-wf-at (proj₁ p↦qᶜ)
fun-source-domain-wf p↦qᶜ | wf⇒ hA hB , wf⇒ hA′ hB′ = hA

fun-target-domain-wf :
  ∀ {Δ p q A A′ B B′} →
  Δ ∣ [] ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  WfTy Δ A′
fun-target-domain-wf p↦qᶜ
    with coercion-wfᵐ empty-store-wf-at (proj₁ p↦qᶜ)
fun-target-domain-wf p↦qᶜ | wf⇒ hA hB , wf⇒ hA′ hB′ = hA′

gradual-term-narrowing-canonical-source-typing :
  ∀ {Δ γ M M′ p A B} →
  Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ srcCtxⁿ γ ⊢ᴳ M ⦂ A
gradual-term-narrowing-canonical-source-typing (x⊒xᴳ pᶜ x∋p) =
  ⊢ᴳ` (srcCtxⁿ-∋ x∋p)
gradual-term-narrowing-canonical-source-typing
    (ƛ⊒ƛᴳ p↦qᶜ N⊒N′) =
  ⊢ᴳƛ
    (fun-source-domain-wf p↦qᶜ)
    (gradual-term-narrowing-canonical-source-typing N⊒N′)
gradual-term-narrowing-canonical-source-typing
    (·⊒·ᴳ p↦qᶜ L⊒L′ M⊒M′) =
  ⊢ᴳ·
    (gradual-term-narrowing-canonical-source-typing L⊒L′)
    (gradual-term-narrowing-canonical-source-typing M⊒M′)
    (~-refl (fun-source-domain-wf p↦qᶜ))
gradual-term-narrowing-canonical-source-typing
    (Λ⊒Λᴳ {typing = gradual-term-typing-endpoints
      (⊢ᴳΛ {occ = occ} vV V⊢) V′⊢}
      allᶜ vVₙ vV′ₙ V⊒V′) =
  ⊢ᴳΛ {occ = occ} vVₙ
    (subst
      (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
      (srcCtxⁿ-⇑ᵍ _)
      (gradual-term-narrowing-canonical-source-typing V⊒V′))
gradual-term-narrowing-canonical-source-typing
    rel@(⊒Λᴳ pᶜ vV′ N⊒V′) =
  gradual-term-narrowing-source-typing rel
gradual-term-narrowing-canonical-source-typing
    rel@([]⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  gradual-term-narrowing-source-typing rel
gradual-term-narrowing-canonical-source-typing
    rel@(⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  gradual-term-narrowing-source-typing rel
gradual-term-narrowing-canonical-source-typing (κ⊒κᴳ κ) =
  ⊢ᴳ$ κ
gradual-term-narrowing-canonical-source-typing
    (⊕⊒⊕ᴳ {op = op} M⊒M′ N⊒N′) =
  ⊢ᴳ⊕
    (gradual-term-narrowing-canonical-source-typing M⊒M′)
    (~-refl wfBase)
    op
    (gradual-term-narrowing-canonical-source-typing N⊒N′)
    (~-refl wfBase)

gradual-term-narrowing-canonical-target-typing :
  ∀ {Δ γ M M′ p A B} →
  Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  Δ ∣ tgtCtxⁿ γ ⊢ᴳ M′ ⦂ B
gradual-term-narrowing-canonical-target-typing (x⊒xᴳ pᶜ x∋p) =
  ⊢ᴳ` (tgtCtxⁿ-∋ x∋p)
gradual-term-narrowing-canonical-target-typing
    (ƛ⊒ƛᴳ p↦qᶜ N⊒N′) =
  ⊢ᴳƛ
    (fun-target-domain-wf p↦qᶜ)
    (gradual-term-narrowing-canonical-target-typing N⊒N′)
gradual-term-narrowing-canonical-target-typing
    (·⊒·ᴳ p↦qᶜ L⊒L′ M⊒M′) =
  ⊢ᴳ·
    (gradual-term-narrowing-canonical-target-typing L⊒L′)
    (gradual-term-narrowing-canonical-target-typing M⊒M′)
    (~-refl (fun-target-domain-wf p↦qᶜ))
gradual-term-narrowing-canonical-target-typing
    (Λ⊒Λᴳ {typing = gradual-term-typing-endpoints
      V⊢ (⊢ᴳΛ {occ = occ} vV′ V′⊢)}
      allᶜ vVₙ vV′ₙ V⊒V′) =
  ⊢ᴳΛ {occ = occ} vV′ₙ
    (subst
      (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
      (tgtCtxⁿ-⇑ᵍ _)
      (gradual-term-narrowing-canonical-target-typing V⊒V′))
gradual-term-narrowing-canonical-target-typing
    rel@(⊒Λᴳ pᶜ vV′ N⊒V′) =
  gradual-term-narrowing-target-typing rel
gradual-term-narrowing-canonical-target-typing
    rel@([]⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  gradual-term-narrowing-target-typing rel
gradual-term-narrowing-canonical-target-typing
    rel@(⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  gradual-term-narrowing-target-typing rel
gradual-term-narrowing-canonical-target-typing (κ⊒κᴳ κ) =
  ⊢ᴳ$ κ
gradual-term-narrowing-canonical-target-typing
    (⊕⊒⊕ᴳ {op = op} M⊒M′ N⊒N′) =
  ⊢ᴳ⊕
    (gradual-term-narrowing-canonical-target-typing M⊒M′)
    (~-refl wfBase)
    op
    (gradual-term-narrowing-canonical-target-typing N⊒N′)
    (~-refl wfBase)

empty-store-incl :
  ∀ {Σ} →
  StoreIncl [] Σ
empty-store-incl ()

narrow-empty-weaken :
  ∀ {μ Δ Σ c A B} →
  μ ∣ Δ ∣ [] ⊢ c ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B
narrow-empty-weaken = narrow-weaken ≤-refl empty-store-incl

narrow-store-cong :
  ∀ {μ Δ Σ Σ′ c A B} →
  Σ ≡ Σ′ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ′ ⊢ c ∶ A ⊒ B
narrow-store-cong refl c⊒ = c⊒

gen-tag-or-id-incl :
  ModeIncl (genᵈ tag-or-idᵈ) tag-or-idᵈ
gen-tag-or-id-incl zero = refl
gen-tag-or-id-incl (suc X) = refl

gen-body-indexᵐᶜ :
  ∀ {Δ ρ p A Aʳ B} →
  Δ ∣ Δ ∣ ρ ⊢ gen Aʳ p ∶ᶜ A ⊒ᵐ `∀ B →
  Δ ∣ suc Δ ∣ ⇑ʳᶜorr ρ ⊢ p ∶ᶜ A ⊒ᵐ B
gen-body-indexᵐᶜ {ρ = ρ}
    (stores , hA , wf∀ hB , Aʳ ,
      med , (cast-gen hAʳ occ p⊢ , genⁿ pⁿ)) =
  corr-⇑ʳᶜorr stores ,
  hA ,
  hB ,
  ⇑ᵗ Aʳ ,
  medTy-mapʳ suc mv-shiftʳ med ,
  narrow-store-cong
    (sym (rightStore-⇑ʳᶜorr ρ))
    (narrow-mode-relax gen-tag-or-id-incl (p⊢ , pⁿ))

compile-no• :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ᴳ M ⦂ A) →
  No• (proj₁ (compile hΓ M⊢))
compile-no• hΓ (⊢ᴳ` x∈) = no•-`
compile-no• hΓ (⊢ᴳƛ wfA M⊢)
    with compile (ctxWf-∷ wfA hΓ) M⊢
       | compile-no• (ctxWf-∷ wfA hΓ) M⊢
compile-no• hΓ (⊢ᴳƛ wfA M⊢) | N , N⊢ | noN =
  no•-ƛ noN
compile-no• hΓ (⊢ᴳ· {ℓ = ℓ} L⊢ M⊢ A~A′)
    with compile hΓ L⊢
       | compile-no• hΓ L⊢
       | compile hΓ M⊢
       | compile-no• hΓ M⊢
       | consistency-cast-plan ℓ (~-sym A~A′)
compile-no• hΓ (⊢ᴳ· L⊢ M⊢ A~A′)
    | L′ , L′⊢ | noL′ | M′ , M′⊢ | noM′ | plan =
  no•-· noL′ (no•-⟨⟩ (no•-⟨⟩ noM′))
compile-no• hΓ (⊢ᴳ·★ {ℓ = ℓ} L⊢ M⊢ A′~★)
    with compile hΓ L⊢
       | compile-no• hΓ L⊢
       | compile hΓ M⊢
       | compile-no• hΓ M⊢
       | consistency-cast-plan ℓ (~-sym (arrow★-consistent A′~★))
compile-no• hΓ (⊢ᴳ·★ L⊢ M⊢ A′~★)
    | L′ , L′⊢ | noL′ | M′ , M′⊢ | noM′ | plan =
  no•-· (no•-⟨⟩ (no•-⟨⟩ noL′)) noM′
compile-no• hΓ (⊢ᴳΛ vM M⊢)
    with compile (CtxWf-⤊ hΓ) M⊢
       | compile-no• (CtxWf-⤊ hΓ) M⊢
compile-no• hΓ (⊢ᴳΛ vM M⊢) | N , N⊢ | noN =
  no•-Λ noN
compile-no• hΓ (⊢ᴳ• M⊢ wfB wfA)
    with compile hΓ M⊢
       | compile-no• hΓ M⊢
compile-no• hΓ (⊢ᴳ• M⊢ wfB wfA) | M′ , M′⊢ | noM′ =
  no•-ν noM′
compile-no• hΓ (⊢ᴳ$ κ) = no•-$
compile-no• hΓ (⊢ᴳ⊕ {ℓ = ℓ} L⊢ A~ℕ op M⊢ B~ℕ)
    with compile hΓ L⊢
       | compile-no• hΓ L⊢
       | compile hΓ M⊢
       | compile-no• hΓ M⊢
       | consistency-cast-plan ℓ A~ℕ
       | consistency-cast-plan ℓ B~ℕ
compile-no• hΓ (⊢ᴳ⊕ L⊢ A~ℕ op M⊢ B~ℕ)
    | L′ , L′⊢ | noL′ | M′ , M′⊢ | noM′ | planL | planM =
  no•-⊕
    (no•-⟨⟩ (no•-⟨⟩ noL′))
    (no•-⟨⟩ (no•-⟨⟩ noM′))

compile-source-left-typing :
  ∀ {Δ ρ γ N A} →
  (N⊢ : Δ ∣ [] ∣ srcCtxⁿ γ ⊢ᵀ N ⦂ A) →
  No• N →
  Δ ∣ leftStore ρ ∣ leftCtx (ctxNrwToCorr γ) ⊢ᵀ N ⦂ A
compile-source-left-typing {ρ = ρ} {γ = γ} N⊢ noN =
  subst
    (λ Γ → _ ∣ leftStore ρ ∣ Γ ⊢ᵀ _ ⦂ _)
    (sym (leftCtx-ctxNrwToCorr γ))
    (term-weaken ≤-refl empty-store-incl noN N⊢)

cast-plan-left-narrowing :
  ∀ {Δ ρ γ M M′ A B C q r s μ ν} →
  (plan : CastPlan Δ [] A B) →
  Δ ∣ Δ ∣ ρ ⊢ q ∶ᶜ lower plan ⊒ᵐ C →
  μ ∣ Δ ∣ Δ ∣ ρ ⊢ r ∶ A ⊒ᵐ C →
  ν ∣ Δ ∣ Δ ∣ ρ ⊢ s ∶ B ⊒ᵐ C →
  Δ ∣ Δ ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ᵐ C →
  Δ ∣ Δ ∣ ρ ∣ γ ⊢ cast plan M ⊒ M′ ∶ s ⦂ B ⊒ᵐ C
cast-plan-left-narrowing plan qᶜ r⊒ s⊒ M⊒M′ =
  cast+⊒ᵗ
    qᶜ
    s⊒
    (narrow-empty-weaken (proj₂ (proj₂ (upDual⊒ plan))))
    (cast-⊒ᵗ
      qᶜ
      r⊒
      (narrow-empty-weaken (proj₂ (down⊒ plan)))
      M⊒M′)

cast-plan-right-narrowing :
  ∀ {Δ ρ γ M M′ A B C p q r μ} →
  (plan : CastPlan Δ [] A B) →
  Δ ∣ Δ ∣ ρ ⊢ p ∶ᶜ C ⊒ᵐ A →
  μ ∣ Δ ∣ Δ ∣ ρ ⊢ q ∶ C ⊒ᵐ lower plan →
  Δ ∣ Δ ∣ ρ ⊢ r ∶ᶜ C ⊒ᵐ B →
  Δ ∣ Δ ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ C ⊒ᵐ A →
  Δ ∣ Δ ∣ ρ ∣ γ ⊢ M ⊒ cast plan M′ ∶ r ⦂ C ⊒ᵐ B
cast-plan-right-narrowing plan pᶜ q⊒ rᶜ M⊒M′ =
  ⊒cast+ᵗ
    rᶜ
    q⊒
    (narrow-empty-weaken (proj₂ (proj₂ (upDual⊒ plan))))
    (⊒cast-ᵗ
      pᶜ
      q⊒
      (narrow-empty-weaken (proj₂ (down⊒ plan)))
      M⊒M′)

variable
  Δ : TyCtx
  ρ : SealCorr
  γ : CtxNrw
  A B : Ty
  p : Coercion
  M M′ : GTerm

compile-preserves-target-forall-narrowing-canonical :
  ∀ {Δ ρ γ N V′ p A B} →
  (med : CompileIndexMediation Δ ρ) →
  (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
  (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
  (N⊒ΛV′ : Δ ∣ [] ∣ γ ⊢ᴳ N ⊒ Λ V′ ∶ gen A p ⦂ A ⊒ `∀ B) →
  let
    N⊢ = gradual-term-narrowing-canonical-source-typing N⊒ΛV′
    ΛV′⊢ = gradual-term-narrowing-canonical-target-typing N⊒ΛV′
    L = proj₁ (compile srcΓ-wf N⊢)
    L′ = proj₁ (compile tgtΓ-wf ΛV′⊢)
  in
  Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ L ⊒ L′ ∶ gen A p ⦂ A ⊒ᵐ `∀ B
compile-preserves-target-forall-narrowing-canonical {ρ = ρ}
    med srcΓ-wf tgtΓ-wf
    (⊒Λᴳ {typing = gradual-term-typing-endpoints N⊢ (⊢ᴳΛ vV′ V′⊢)}
      pᶜ vV′ₙ N⊒V′) =
  ⊒Λᵗ
    (compile-source-left-typing {ρ = ρ}
      (proj₂ (compile srcΓ-wf N⊢))
      (compile-no• srcΓ-wf N⊢))
    genᶜ
    (compile-value (CtxWf-⤊ tgtΓ-wf) vV′ₙ V′⊢)
    (right-only-forall-bodyᵐ med
      srcΓ-wf
      tgtΓ-wf
      N⊢
      V′⊢
      genᶜ
      N⊒V′)
  where
    genᶜ = indexᵐᶜ med pᶜ

compile-preserves-term-narrowing-canonical :
  (med : CompileIndexMediation Δ ρ) →
  (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
  (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
  (M⊒M′ : Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B) →
  let
    M⊢ = gradual-term-narrowing-canonical-source-typing M⊒M′
    M′⊢ = gradual-term-narrowing-canonical-target-typing M⊒M′
    N = proj₁ (compile srcΓ-wf M⊢)
    N′ = proj₁ (compile tgtΓ-wf M′⊢)
  in
  Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    (x⊒xᴳ pᶜ x∋p) =
  x⊒xᵗ (indexᵐᶜ med pᶜ) (ctxNrwToCorr-∋ x∋p)
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    (κ⊒κᴳ κ) =
  κ⊒κᵗ κ (indexᵐᶜ med (const-indexᶜ κ))
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    (ƛ⊒ƛᴳ {p = p} {q = q} {A = A} {A′ = A′}
      {B = B} {B′ = B′} p↦qᶜ N⊒N′) =
  ƛ⊒ƛᵗ {p = p} {q = q}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    (indexᵐᶜ med p↦qᶜ)
    (mediated-narrowing-context-cong
      (cong (λ c → ctx-entry A A′ c ∷ ctxNrwToCorr _)
        (sym (fun-domain-dualᵐᶜ med p↦qᶜ)))
      (compile-preserves-term-narrowing-canonical med
        (ctxWf-∷ (fun-source-domain-wf p↦qᶜ) srcΓ-wf)
        (ctxWf-∷ (fun-target-domain-wf p↦qᶜ) tgtΓ-wf)
        N⊒N′))
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    (Λ⊒Λᴳ {typing = gradual-term-typing-endpoints
      (⊢ᴳΛ vV V₀⊢) (⊢ᴳΛ vV′ V′₀⊢)}
      allᶜ vVₙ vV′ₙ V⊒V′) =
  Λ⊒Λᵗ
    (indexᵐᶜ med allᶜ)
    (compile-value (CtxWf-⤊ srcΓ-wf) vVₙ V⊢)
    (compile-value (CtxWf-⤊ tgtΓ-wf) vV′ₙ V′⊢)
    (mediated-narrowing-cong-terms
      src-body-eq
      tgt-body-eq
      (mediated-narrowing-context-cong
        (ctxNrwToCorr-⇑ _)
        (compile-preserves-term-narrowing-canonical (shiftᵐ med)
          srcΓ⇑-wf
          tgtΓ⇑-wf
          V⊒V′)))
  where
    V⊢ =
      subst
        (λ Γ₀ → _ ∣ Γ₀ ⊢ᴳ _ ⦂ _)
        (srcCtxⁿ-⇑ᵍ _)
        (gradual-term-narrowing-canonical-source-typing V⊒V′)
    V′⊢ =
      subst
        (λ Γ₀ → _ ∣ Γ₀ ⊢ᴳ _ ⦂ _)
        (tgtCtxⁿ-⇑ᵍ _)
        (gradual-term-narrowing-canonical-target-typing V⊒V′)
    srcΓ⇑-wf =
      subst (CtxWf _) (sym (srcCtxⁿ-⇑ᵍ _)) (CtxWf-⤊ srcΓ-wf)
    tgtΓ⇑-wf =
      subst (CtxWf _) (sym (tgtCtxⁿ-⇑ᵍ _)) (CtxWf-⤊ tgtΓ-wf)
    src-body-eq =
      trans
        (cong
          (λ V⊢₀ → proj₁ (compile srcΓ⇑-wf V⊢₀))
          (sym
            (gradual-typing-subst-sym-subst
              (srcCtxⁿ-⇑ᵍ _)
              (gradual-term-narrowing-canonical-source-typing V⊒V′))))
        (compile-context-subst-term
          (sym (srcCtxⁿ-⇑ᵍ _))
          (CtxWf-⤊ srcΓ-wf)
          V⊢)
    tgt-body-eq =
      trans
        (cong
          (λ V′⊢₀ → proj₁ (compile tgtΓ⇑-wf V′⊢₀))
          (sym
            (gradual-typing-subst-sym-subst
              (tgtCtxⁿ-⇑ᵍ _)
              (gradual-term-narrowing-canonical-target-typing V⊒V′))))
        (compile-context-subst-term
          (sym (tgtCtxⁿ-⇑ᵍ _))
          (CtxWf-⤊ tgtΓ-wf)
          V′⊢)
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    (·⊒·ᴳ {p = p} {q = q} {A = A} {A′ = A′} {ℓ = ℓ}
      p↦qᶜ L⊒L′ R⊒R′)
    with compile srcΓ-wf
           (gradual-term-narrowing-canonical-source-typing L⊒L′)
       | inspect
           (compile srcΓ-wf)
           (gradual-term-narrowing-canonical-source-typing L⊒L′)
       | compile tgtΓ-wf
           (gradual-term-narrowing-canonical-target-typing L⊒L′)
       | inspect
           (compile tgtΓ-wf)
           (gradual-term-narrowing-canonical-target-typing L⊒L′)
       | compile srcΓ-wf
           (gradual-term-narrowing-canonical-source-typing R⊒R′)
       | inspect
           (compile srcΓ-wf)
           (gradual-term-narrowing-canonical-source-typing R⊒R′)
       | compile tgtΓ-wf
           (gradual-term-narrowing-canonical-target-typing R⊒R′)
       | inspect
           (compile tgtΓ-wf)
           (gradual-term-narrowing-canonical-target-typing R⊒R′)
       | consistency-cast-plan ℓ
           (~-sym (~-refl (fun-source-domain-wf p↦qᶜ)))
       | inspect
           (consistency-cast-plan ℓ)
           (~-sym (~-refl (fun-source-domain-wf p↦qᶜ)))
       | consistency-cast-plan ℓ
           (~-sym (~-refl (fun-target-domain-wf p↦qᶜ)))
       | inspect
           (consistency-cast-plan ℓ)
           (~-sym (~-refl (fun-target-domain-wf p↦qᶜ)))
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    (·⊒·ᴳ {p = p} {q = q} {A = A} {A′ = A′} {ℓ = ℓ}
      p↦qᶜ L⊒L′ R⊒R′)
    | Lᵀ , L⊢ | [ eqL ]
    | L′ᵀ , L′⊢ | [ eqL′ ]
    | Rᵀ , R⊢ | [ eqR ]
    | R′ᵀ , R′⊢ | [ eqR′ ]
    | plan | [ eqPlan ]
    | plan′ | [ eqPlan′ ] =
  ·⊒·ᵗ
    (indexᵐᶜ med p↦qᶜ)
    (mediated-narrowing-cong-terms
      {L = proj₁ (compile srcΓ-wf
        (gradual-term-narrowing-canonical-source-typing L⊒L′))}
      {R = proj₁ (compile tgtΓ-wf
        (gradual-term-narrowing-canonical-target-typing L⊒L′))}
      {R′ = L′ᵀ}
      (cong proj₁ eqL)
      (cong proj₁ eqL′)
      (compile-preserves-term-narrowing-canonical med
        srcΓ-wf tgtΓ-wf L⊒L′))
    (cast-plan-right-narrowing
      tgtPlan
      domainᶜ
      domainᶜ
      domainᶜ
      (cast-plan-left-narrowing
        srcPlan
        domainᶜ
        domainᶜ
        domainᶜ
        (mediated-narrowing-index-cong
          (sym (fun-domain-dualᵐᶜ med p↦qᶜ))
          (mediated-narrowing-cong-terms
            {L = proj₁ (compile srcΓ-wf
              (gradual-term-narrowing-canonical-source-typing R⊒R′))}
            {R = proj₁ (compile tgtΓ-wf
              (gradual-term-narrowing-canonical-target-typing R⊒R′))}
            {R′ = R′ᵀ}
            (cong proj₁ eqR)
            (cong proj₁ eqR′)
            (compile-preserves-term-narrowing-canonical med
              srcΓ-wf tgtΓ-wf R⊒R′)))))
  where
    domainᶜ =
      fun-narrow-domain-dual-typingᵐᶜ (indexᵐᶜ med p↦qᶜ)
    srcPlan =
      consistency-cast-plan ℓ (~-sym (~-refl (fun-source-domain-wf p↦qᶜ)))
    tgtPlan =
      consistency-cast-plan ℓ (~-sym (~-refl (fun-target-domain-wf p↦qᶜ)))
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    rel@(⊒Λᴳ pᶜ vV′ N⊒V′) =
  compile-preserves-target-forall-narrowing-canonical
    med srcΓ-wf tgtΓ-wf rel
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    ([]⊒[]ᴳ {typing = gradual-term-typing-endpoints MT⊢ M′T′⊢}
      M⊒M′ qᶜ rᶜ) =
  type-applicationνᵐ med
    srcΓ-wf
    tgtΓ-wf
    MT⊢
    M′T′⊢
    M⊒M′
    (indexᵐᶜ med qᶜ)
    (indexᵐᶜ med rᶜ)
compile-preserves-term-narrowing-canonical med srcΓ-wf tgtΓ-wf
    (⊒[]ᴳ {typing = gradual-term-typing-endpoints M⊢ M′T′⊢}
      M⊒M′ qᶜ rᶜ) =
  target-type-applicationνᵐ med
    srcΓ-wf
    tgtΓ-wf
    M⊢
    M′T′⊢
    M⊒M′
    (indexᵐᶜ med qᶜ)
    (indexᵐᶜ med rᶜ)
compile-preserves-term-narrowing-canonical {Δ = Δ} med srcΓ-wf tgtΓ-wf
    (⊕⊒⊕ᴳ {op = addℕ} {ℓ = ℓ} M⊒M′ N⊒N′)
    with compile srcΓ-wf
           (gradual-term-narrowing-canonical-source-typing M⊒M′)
       | inspect
           (compile srcΓ-wf)
           (gradual-term-narrowing-canonical-source-typing M⊒M′)
       | compile tgtΓ-wf
           (gradual-term-narrowing-canonical-target-typing M⊒M′)
       | inspect
           (compile tgtΓ-wf)
           (gradual-term-narrowing-canonical-target-typing M⊒M′)
       | compile srcΓ-wf
           (gradual-term-narrowing-canonical-source-typing N⊒N′)
       | inspect
           (compile srcΓ-wf)
           (gradual-term-narrowing-canonical-source-typing N⊒N′)
       | compile tgtΓ-wf
           (gradual-term-narrowing-canonical-target-typing N⊒N′)
       | inspect
           (compile tgtΓ-wf)
           (gradual-term-narrowing-canonical-target-typing N⊒N′)
       | consistency-cast-plan ℓ (~-refl {Δ = Δ} {A = ‵ `ℕ} wfBase)
compile-preserves-term-narrowing-canonical {Δ = Δ} med srcΓ-wf tgtΓ-wf
    (⊕⊒⊕ᴳ {op = addℕ} {ℓ = ℓ} M⊒M′ N⊒N′)
    | Mᵀ , M⊢ | [ eqM ]
    | M′ᵀ , M′⊢ | [ eqM′ ]
    | Nᵀ , N⊢ | [ eqN ]
    | N′ᵀ , N′⊢ | [ eqN′ ]
    | plan =
  ⊕⊒⊕ᵗ
    ℕᶜ
    (cast-plan-right-narrowing natPlan ℕᶜ ℕᶜ ℕᶜ
      (cast-plan-left-narrowing natPlan ℕᶜ ℕᶜ ℕᶜ
        (mediated-narrowing-cong-terms
          {L = proj₁ (compile srcΓ-wf
            (gradual-term-narrowing-canonical-source-typing M⊒M′))}
          {R = proj₁ (compile tgtΓ-wf
            (gradual-term-narrowing-canonical-target-typing M⊒M′))}
          {R′ = M′ᵀ}
          (cong proj₁ eqM)
          (cong proj₁ eqM′)
          (compile-preserves-term-narrowing-canonical med
            srcΓ-wf tgtΓ-wf M⊒M′))))
    (cast-plan-right-narrowing natPlan ℕᶜ ℕᶜ ℕᶜ
      (cast-plan-left-narrowing natPlan ℕᶜ ℕᶜ ℕᶜ
        (mediated-narrowing-cong-terms
          {L = proj₁ (compile srcΓ-wf
            (gradual-term-narrowing-canonical-source-typing N⊒N′))}
          {R = proj₁ (compile tgtΓ-wf
            (gradual-term-narrowing-canonical-target-typing N⊒N′))}
          {R′ = N′ᵀ}
          (cong proj₁ eqN)
          (cong proj₁ eqN′)
          (compile-preserves-term-narrowing-canonical med
            srcΓ-wf tgtΓ-wf N⊒N′))))
  where
    ℕᶜ = indexᵐᶜ med (cast-id wfBase refl , cross (id-‵ `ℕ))
    natPlan = consistency-cast-plan ℓ (~-refl {Δ = Δ} {A = ‵ `ℕ} wfBase)

compile-preserves-term-narrowing :
  (med : CompileIndexMediation Δ ρ) →
  (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
  (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
  (M⊒M′ : Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B) →
  let
    M⊢ = gradual-term-narrowing-canonical-source-typing M⊒M′
    M′⊢ = gradual-term-narrowing-canonical-target-typing M⊒M′
    N = proj₁ (compile srcΓ-wf M⊢)
    N′ = proj₁ (compile tgtΓ-wf M′⊢)
  in
  Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B
compile-preserves-term-narrowing med srcΓ-wf tgtΓ-wf M⊒M′ =
  compile-preserves-term-narrowing-canonical
    med
    srcΓ-wf
    tgtΓ-wf
    M⊒M′
