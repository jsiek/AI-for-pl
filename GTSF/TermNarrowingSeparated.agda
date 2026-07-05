module TermNarrowingSeparated where

-- File Charter:
--   * First separated-store term-narrowing surface for GTSF.
--   * Uses independent left/right type contexts and stores, connected by the
--     explicit `SealCorr` relation from `StoreCorrespondence`.
--   * Covers the value, lambda, application, and primitive forms needed to start
--     migrating the DGG beta proof away from shared-store target shifting.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import Types
open import Ctx using (⤊ᵗ)
open import Coercions
open import NarrowWiden using (cross; dualⁿ; dualʷ; _∣_∣_⊢_∶_⊒_)
  renaming (_↦_ to _↦ⁿʷ_)
open import Primitives
open import NuTerms
open import StoreCorrespondence
open import proof.CoercionProperties using
  ( coercion-src-tgtᵐ
  ; dualActionOk-normal
  ; dualStoreAt-normal
  )
open import proof.NarrowWidenProperties using
  ( dualⁿ-flips-typingᵐ
  ; dualʷ-flips-typingᵐ
  )

------------------------------------------------------------------------
-- Separate term-context correspondence
------------------------------------------------------------------------

data CtxCorrEntry : Set where
  ctx-entry : Ty → Ty → Coercion → CtxCorrEntry

CtxCorr : Set
CtxCorr = List CtxCorrEntry

leftCtxEntry : CtxCorrEntry → Ty
leftCtxEntry (ctx-entry A B p) = A

rightCtxEntry : CtxCorrEntry → Ty
rightCtxEntry (ctx-entry A B p) = B

corrCtxEntry : CtxCorrEntry → Coercion
corrCtxEntry (ctx-entry A B p) = p

leftCtx : CtxCorr → Ctx
leftCtx = map leftCtxEntry

rightCtx : CtxCorr → Ctx
rightCtx = map rightCtxEntry

shiftCtxCorrEntry : CtxCorrEntry → CtxCorrEntry
shiftCtxCorrEntry (ctx-entry A B p) =
  ctx-entry (⇑ᵗ A) (⇑ᵗ B) (⇑ᶜ p)

⇑ᵍᶜ : CtxCorr → CtxCorr
⇑ᵍᶜ = map shiftCtxCorrEntry

leftCtx-∋ :
  ∀ {γ x A B p} →
  γ ∋ x ⦂ ctx-entry A B p →
  leftCtx γ ∋ x ⦂ A
leftCtx-∋ Z = Z
leftCtx-∋ (S x∋p) = S (leftCtx-∋ x∋p)

rightCtx-∋ :
  ∀ {γ x A B p} →
  γ ∋ x ⦂ ctx-entry A B p →
  rightCtx γ ∋ x ⦂ B
rightCtx-∋ Z = Z
rightCtx-∋ (S x∋p) = S (rightCtx-∋ x∋p)

leftCtx-⇑ᵍᶜ :
  ∀ γ →
  leftCtx (⇑ᵍᶜ γ) ≡ ⤊ᵗ (leftCtx γ)
leftCtx-⇑ᵍᶜ [] = refl
leftCtx-⇑ᵍᶜ (ctx-entry A B p ∷ γ) =
  cong (⇑ᵗ A ∷_) (leftCtx-⇑ᵍᶜ γ)

rightCtx-⇑ᵍᶜ :
  ∀ γ →
  rightCtx (⇑ᵍᶜ γ) ≡ ⤊ᵗ (rightCtx γ)
rightCtx-⇑ᵍᶜ [] = refl
rightCtx-⇑ᵍᶜ (ctx-entry A B p ∷ γ) =
  cong (⇑ᵗ B ∷_) (rightCtx-⇑ᵍᶜ γ)

shift-left-term-typing :
  ∀ {Δ ρ γ M A} →
  suc Δ ∣ leftStore (⇑ᶜorr ρ) ∣ leftCtx (⇑ᵍᶜ γ) ⊢ M ⦂ A →
  suc Δ ∣ ⟰ᵗ (leftStore ρ) ∣ ⤊ᵗ (leftCtx γ) ⊢ M ⦂ A
shift-left-term-typing {ρ = ρ} {γ = γ} M⊢ =
  subst (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
    (leftCtx-⇑ᵍᶜ γ)
    (subst (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
      (leftStore-⇑ᶜorr ρ)
      M⊢)

shift-right-term-typing :
  ∀ {Δ ρ γ M A} →
  suc Δ ∣ rightStore (⇑ᶜorr ρ) ∣ rightCtx (⇑ᵍᶜ γ) ⊢ M ⦂ A →
  suc Δ ∣ ⟰ᵗ (rightStore ρ) ∣ ⤊ᵗ (rightCtx γ) ⊢ M ⦂ A
shift-right-term-typing {ρ = ρ} {γ = γ} M⊢ =
  subst (λ Γ → _ ∣ _ ∣ Γ ⊢ _ ⦂ _)
    (rightCtx-⇑ᵍᶜ γ)
    (subst (λ Σ → _ ∣ Σ ∣ _ ⊢ _ ⦂ _)
      (rightStore-⇑ᶜorr ρ)
      M⊢)

------------------------------------------------------------------------
-- Cross-store coercion evidence
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶ᶜ_⊒_
infix 4 _∣_∣_∣_⊢_∶_⊒_

_∣_∣_∣_⊢_∶_⊒_ :
  ModeEnv → TyCtx → TyCtx → SealCorr → Coercion → Ty → Ty → Set₁
μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ B =
  StoreCorr ΔL ΔR ρ ×
  src r ≡ A ×
  tgt r ≡ B ×
  WfTy ΔL A ×
  WfTy ΔR B ×
  (μ ∣ ΔL ∣ leftStore ρ ⊢ r ∶ A ⊒ B) ×
  (μ ∣ ΔR ∣ rightStore ρ ⊢ r ∶ A ⊒ B)

_∣_∣_⊢_∶ᶜ_⊒_ :
  TyCtx → TyCtx → SealCorr → Coercion → Ty → Ty → Set₁
ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ B =
  tag-or-idᵈ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ B

fun-narrow-domain-dual :
  ∀ {μ ΔL ΔR ρ p q A A′ B B′} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  Coercion
fun-narrow-domain-dual
    (_ , _ , _ , _ , _ ,
      (_ , cross (pʷ ↦ⁿʷ _)) ,
      _) =
  proj₁ (dualʷ normalᵃ pʷ)

fun-narrow-domain-dualᶜ :
  ∀ {ΔL ΔR ρ p q A A′ B B′} →
  ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  Coercion
fun-narrow-domain-dualᶜ = fun-narrow-domain-dual

fun-narrow-domain-dual-typingᶜ :
  ∀ {ΔL ΔR ρ p q A A′ B B′} →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
             ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᶜ p↦qᶜ ∶ᶜ A ⊒ A′
fun-narrow-domain-dual-typingᶜ
    (stores , _ , _ , wf⇒ hA hB , wf⇒ hA′ hB′ ,
      (cast-fun p⊢L _ , cross (pʷL ↦ⁿʷ _)) ,
      (cast-fun p⊢R _ , cross (_ ↦ⁿʷ _))) =
  let
    pᵈ⊒L =
      dualʷ-flips-typingᵐ
        {μ = tag-or-idᵈ}
        {η = normalᵃ}
        {ν = tag-or-idᵈ}
        dualActionOk-normal
        dualStoreAt-normal
        (leftStore-wf stores)
        (p⊢L , pʷL)

    pᵈ⊒R =
      dualʷ-flips-typingᵐ
        {μ = tag-or-idᵈ}
        {η = normalᵃ}
        {ν = tag-or-idᵈ}
        dualActionOk-normal
        dualStoreAt-normal
        (rightStore-wf stores)
        (p⊢R , pʷL)
  in
  stores ,
  proj₁ (coercion-src-tgtᵐ (proj₁ pᵈ⊒L)) ,
  proj₂ (coercion-src-tgtᵐ (proj₁ pᵈ⊒L)) ,
  hA ,
  hA′ ,
  pᵈ⊒L ,
  pᵈ⊒R

fun-narrow-codomainᶜ :
  ∀ {ΔL ΔR ρ p q A A′ B B′} →
  ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ B ⊒ B′
fun-narrow-codomainᶜ
    (stores , _ , _ , wf⇒ hA hB , wf⇒ hA′ hB′ ,
      (cast-fun _ q⊢L , cross (_ ↦ⁿʷ qⁿL)) ,
      (cast-fun _ q⊢R , cross (_ ↦ⁿʷ qⁿR))) =
  stores ,
  proj₁ (coercion-src-tgtᵐ q⊢L) ,
  proj₂ (coercion-src-tgtᵐ q⊢L) ,
  hB ,
  hB′ ,
  (q⊢L , qⁿL) ,
  (q⊢R , qⁿR)

narrowing-store-corrᶜ :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
  StoreCorr ΔL ΔR ρ
narrowing-store-corrᶜ (stores , _ , _ , _ , _ , _ , _) = stores

narrowing-dual :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
  Coercion
narrowing-dual (_ , _ , _ , _ , _ , (_ , cⁿ) , _) =
  proj₁ (dualⁿ normalᵃ cⁿ)

narrowing-left-coercion-typingᶜ :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
  ∃[ μ′ ] μ′ ∣ ΔL ∣ leftStore ρ ⊢ c ∶ A =⇒ B
narrowing-left-coercion-typingᶜ {μ = μ} (_ , _ , _ , _ , _ , c⊒L , _) =
  μ , proj₁ c⊒L

narrowing-right-coercion-typingᶜ :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B →
  ∃[ μ′ ] μ′ ∣ ΔR ∣ rightStore ρ ⊢ c ∶ A =⇒ B
narrowing-right-coercion-typingᶜ {μ = μ} (_ , _ , _ , _ , _ , _ , c⊒R) =
  μ , proj₁ c⊒R

narrowing-left-dual-coercion-typingᶜ :
  ∀ {μ ΔL ΔR ρ c A B} →
  (c⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B) →
  ∃[ μ′ ] μ′ ∣ ΔL ∣ leftStore ρ ⊢ narrowing-dual c⊒ ∶ B =⇒ A
narrowing-left-dual-coercion-typingᶜ {μ = μ}
    (stores , _ , _ , _ , _ , (c⊢L , cⁿL) , _) =
  μ ,
  proj₁
    (dualⁿ-flips-typingᵐ
      {μ = μ}
      {η = normalᵃ}
      {ν = μ}
      dualActionOk-normal
      dualStoreAt-normal
      (leftStore-wf stores)
      (c⊢L , cⁿL))

narrowing-right-dual-coercion-typingᶜ :
  ∀ {μ ΔL ΔR ρ c A B} →
  (c⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ B) →
  ∃[ μ′ ] μ′ ∣ ΔR ∣ rightStore ρ ⊢ narrowing-dual c⊒ ∶ B =⇒ A
narrowing-right-dual-coercion-typingᶜ {μ = μ}
    (stores , _ , _ , _ , _ , (_ , cⁿL) , (c⊢R , _)) =
  μ ,
  proj₁
    (dualⁿ-flips-typingᵐ
      {μ = μ}
      {η = normalᵃ}
      {ν = μ}
      dualActionOk-normal
      dualStoreAt-normal
      (rightStore-wf stores)
      (c⊢R , cⁿL))

------------------------------------------------------------------------
-- Typed/well-indexed separated term narrowing
------------------------------------------------------------------------

TermTypingEndpointsᶜ :
  (ΔL ΔR : TyCtx) (ρ : SealCorr) (γ : CtxCorr) →
  (M M′ : Term) (A B : Ty) → Set₁
TermTypingEndpointsᶜ ΔL ΔR ρ γ M M′ A B =
  (ΔL ∣ leftStore ρ ∣ leftCtx γ ⊢ M ⦂ A) ×
  (ΔR ∣ rightStore ρ ∣ rightCtx γ ⊢ M′ ⦂ B)

infix 4 _∣_∣_∣_⊢_⊒_∶_⦂_⊒_

data _∣_∣_∣_⊢_⊒_∶_⦂_⊒_
    : TyCtx → TyCtx → SealCorr → CtxCorr →
      Term → Term → Coercion → Ty → Ty → Set₁ where

  -- The Cambridge25 notation uses p and q for coercions whose evidence is
  -- restricted to `∶ᶜ` (the tag-or-id mode).  It uses r for cast-composed
  -- result coercions, whose evidence is the general μ-indexed narrowing
  -- typing.  The separated rules below keep that naming convention visible:
  -- p/q premises use `_⊢_∶ᶜ_⊒_`, while r premises use `_∣_∣_∣_⊢_∶_⊒_`.

  -- The coercion evidence is deliberately general-mode: blame sits on the
  -- target side of any well-typed narrowing index, not only tag-or-id
  -- ones.  (The `∶ᶜ` restriction here previously forced the separated DGG
  -- theorem to demand `∶ᶜ` evidence for the relation index, which the
  -- `⊒cast+ᵗ` inner relations cannot supply.)
  ⊒blameᵗ : ∀ {ΔL ΔR ρ γ M p A B μ}
    → ΔL ∣ leftStore ρ ∣ leftCtx γ ⊢ M ⦂ A
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ B
      ------------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ blame ∶ p ⦂ A ⊒ B

  x⊒xᵗ : ∀ {ΔL ΔR ρ γ x p A B}
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ B
    → γ ∋ x ⦂ ctx-entry A B p
      ---------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ ` x ⊒ ` x ∶ p ⦂ A ⊒ B

  ƛ⊒ƛᵗ : ∀ {ΔL ΔR ρ γ N N′ p q A A′ B B′}
    → (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                   ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → ΔL ∣ ΔR ∣ ρ ∣
        ctx-entry A A′ (fun-narrow-domain-dualᶜ p↦qᶜ) ∷ γ
        ⊢ N ⊒ N′ ∶ q ⦂ B ⊒ B′
      -------------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ ƛ N ⊒ ƛ N′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ A′ ⇒ B′

  ·⊒·ᵗ : ∀ {ΔL ΔR ρ γ L L′ M M′ p q A A′ B B′}
    → (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                   ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′))
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ L′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ A′ ⇒ B′
    → ΔL ∣ ΔR ∣ ρ ∣ γ
        ⊢ M ⊒ M′ ∶ fun-narrow-domain-dualᶜ p↦qᶜ ⦂ A ⊒ A′
      -----------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L · M ⊒ L′ · M′ ∶ q ⦂ B ⊒ B′

  Λ⊒Λᵗ : ∀ {ΔL ΔR ρ γ V V′ p A B}
    → ΔL ∣ ΔR ∣ ρ ⊢ `∀ p ∶ᶜ `∀ A ⊒ `∀ B
    → Value V
    → Value V′
    → suc ΔL ∣ suc ΔR ∣ ⇑ᶜorr ρ ∣ ⇑ᵍᶜ γ
        ⊢ V ⊒ V′ ∶ p ⦂ A ⊒ B
      -----------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ Λ V ⊒ Λ V′ ∶ `∀ p
        ⦂ `∀ A ⊒ `∀ B

  κ⊒κᵗ : ∀ {ΔL ΔR ρ γ} κ
    → ΔL ∣ ΔR ∣ ρ ⊢ id (constTy κ) ∶ᶜ constTy κ ⊒ constTy κ
      -----------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ $ κ ⊒ $ κ ∶ id (constTy κ)
        ⦂ constTy κ ⊒ constTy κ

  ⊕⊒⊕ᵗ : ∀ {ΔL ΔR ρ γ M M′ N N′}
    → ΔL ∣ ΔR ∣ ρ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ ‵ `ℕ
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ N ⊒ N′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ ‵ `ℕ
      ------------------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊕[ addℕ ] N ⊒ M′ ⊕[ addℕ ] N′
        ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ ‵ `ℕ

  ⊒cast+ᵗ : ∀ {ΔL ΔR ρ γ M M′ p r t A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ C
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ B
    → (t⊒ : η ∣ ΔL ∣ ΔR ∣ ρ ⊢ t ∶ C ⊒ B)
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ B
      -------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ
        ⊢ M ⊒ M′ ⟨ narrowing-dual t⊒ ⟩ ∶ p ⦂ A ⊒ C

  ⊒cast-ᵗ : ∀ {ΔL ΔR ρ γ M M′ p r t A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ C
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ B
    → η ∣ ΔL ∣ ΔR ∣ ρ ⊢ t ∶ C ⊒ B
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ C
      ---------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ⟨ t ⟩ ∶ r ⦂ A ⊒ B

  cast+⊒ᵗ : ∀ {ΔL ΔR ρ γ M M′ q r s A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ C ⊒ B
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ B
    → (s⊒ : η ∣ ΔL ∣ ΔR ∣ ρ ⊢ s ∶ A ⊒ C)
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ q ⦂ C ⊒ B
      -------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ
        ⊢ M ⟨ narrowing-dual s⊒ ⟩ ⊒ M′ ∶ r ⦂ A ⊒ B

  cast-⊒ᵗ : ∀ {ΔL ΔR ρ γ M M′ q r s A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ C ⊒ B
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ B
    → η ∣ ΔL ∣ ΔR ∣ ρ ⊢ s ∶ A ⊒ C
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ B
      ---------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⟨ s ⟩ ⊒ M′ ∶ q ⦂ C ⊒ B

typed-term-narrowing-term-typingᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  TermTypingEndpointsᶜ ΔL ΔR ρ γ M M′ A B
typed-term-narrowing-term-typingᶜ
    (⊒blameᵗ M⊢ (_ , _ , _ , _ , hB , _ , _)) =
  M⊢ , ⊢blame hB
typed-term-narrowing-term-typingᶜ
    (x⊒xᵗ pᶜ x∋p) =
  ⊢` (leftCtx-∋ x∋p) , ⊢` (rightCtx-∋ x∋p)
typed-term-narrowing-term-typingᶜ
    (ƛ⊒ƛᵗ (_ , _ , _ , wf⇒ hA hB , wf⇒ hA′ hB′ , _ , _)
      N⊒N′) =
  let
    N⊢ , N′⊢ = typed-term-narrowing-term-typingᶜ N⊒N′
  in
  ⊢ƛ hA N⊢ , ⊢ƛ hA′ N′⊢
typed-term-narrowing-term-typingᶜ
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  let
    L⊢ , L′⊢ = typed-term-narrowing-term-typingᶜ L⊒L′
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᶜ M⊒M′
  in
  ⊢· L⊢ M⊢ , ⊢· L′⊢ M′⊢
typed-term-narrowing-term-typingᶜ {ρ = ρ} {γ = γ}
    (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′) =
  let
    V⊢ , V′⊢ = typed-term-narrowing-term-typingᶜ V⊒V′
  in
  ⊢Λ vV (shift-left-term-typing {ρ = ρ} {γ = γ} V⊢) ,
  ⊢Λ vV′ (shift-right-term-typing {ρ = ρ} {γ = γ} V′⊢)
typed-term-narrowing-term-typingᶜ
    (κ⊒κᵗ κ pᶜ) =
  ⊢$ κ , ⊢$ κ
typed-term-narrowing-term-typingᶜ
    (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′) =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᶜ M⊒M′
    N⊢ , N′⊢ = typed-term-narrowing-term-typingᶜ N⊒N′
  in
  ⊢⊕ M⊢ addℕ N⊢ , ⊢⊕ M′⊢ addℕ N′⊢
typed-term-narrowing-term-typingᶜ
    (⊒cast+ᵗ {η = η} pᶜ rᶜ t⊒ M⊒M′)
    with narrowing-right-dual-coercion-typingᶜ {μ = η} t⊒
typed-term-narrowing-term-typingᶜ
    (⊒cast+ᵗ {η = η} pᶜ rᶜ t⊒ M⊒M′) | μ′ , t⊢ =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᶜ M⊒M′
  in
  M⊢ , ⊢⟨⟩ t⊢ M′⊢
typed-term-narrowing-term-typingᶜ
    (⊒cast-ᵗ {η = η} pᶜ rᶜ t⊒ M⊒M′)
    with narrowing-right-coercion-typingᶜ {μ = η} t⊒
typed-term-narrowing-term-typingᶜ
    (⊒cast-ᵗ {η = η} pᶜ rᶜ t⊒ M⊒M′) | μ′ , t⊢ =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᶜ M⊒M′
  in
  M⊢ , ⊢⟨⟩ t⊢ M′⊢
typed-term-narrowing-term-typingᶜ
    (cast+⊒ᵗ {η = η} qᶜ rᶜ s⊒ M⊒M′)
    with narrowing-left-dual-coercion-typingᶜ {μ = η} s⊒
typed-term-narrowing-term-typingᶜ
    (cast+⊒ᵗ {η = η} qᶜ rᶜ s⊒ M⊒M′) | μ′ , s⊢ =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᶜ M⊒M′
  in
  ⊢⟨⟩ s⊢ M⊢ , M′⊢
typed-term-narrowing-term-typingᶜ
    (cast-⊒ᵗ {η = η} qᶜ rᶜ s⊒ M⊒M′)
    with narrowing-left-coercion-typingᶜ {μ = η} s⊒
typed-term-narrowing-term-typingᶜ
    (cast-⊒ᵗ {η = η} qᶜ rᶜ s⊒ M⊒M′) | μ′ , s⊢ =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᶜ M⊒M′
  in
  ⊢⟨⟩ s⊢ M⊢ , M′⊢

typed-term-narrowing-coercion :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  ∃[ μ ] μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ B
typed-term-narrowing-coercion (⊒blameᵗ {μ = μ} M⊢ p⊒) =
  μ , p⊒
typed-term-narrowing-coercion (x⊒xᵗ pᶜ x∋p) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercion (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) =
  tag-or-idᵈ , p↦qᶜ
typed-term-narrowing-coercion (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  tag-or-idᵈ , fun-narrow-codomainᶜ p↦qᶜ
typed-term-narrowing-coercion (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′) =
  tag-or-idᵈ , allᶜ
typed-term-narrowing-coercion (κ⊒κᵗ κ pᶜ) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercion (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercion (⊒cast+ᵗ pᶜ r⊒ t⊒ M⊒M′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercion (⊒cast-ᵗ {μ = μ} pᶜ r⊒ t⊒ M⊒M′) =
  μ , r⊒
typed-term-narrowing-coercion (cast+⊒ᵗ {μ = μ} qᶜ r⊒ s⊒ M⊒M′) =
  μ , r⊒
typed-term-narrowing-coercion (cast-⊒ᵗ qᶜ r⊒ s⊒ M⊒M′) =
  tag-or-idᵈ , qᶜ

typed-term-narrowing-source-typingᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  ΔL ∣ leftStore ρ ∣ leftCtx γ ⊢ M ⦂ A
typed-term-narrowing-source-typingᶜ M⊒M′
    with typed-term-narrowing-term-typingᶜ M⊒M′
typed-term-narrowing-source-typingᶜ M⊒M′ | M⊢ , M′⊢ = M⊢

typed-term-narrowing-target-typingᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  ΔR ∣ rightStore ρ ∣ rightCtx γ ⊢ M′ ⦂ B
typed-term-narrowing-target-typingᶜ M⊒M′
    with typed-term-narrowing-term-typingᶜ M⊒M′
typed-term-narrowing-target-typingᶜ M⊒M′ | M⊢ , M′⊢ = M′⊢
