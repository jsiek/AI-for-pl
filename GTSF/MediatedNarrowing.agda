module MediatedNarrowing where

-- File Charter:
--   * The mediated separated-store term-narrowing relation: the
--     successor of `TermNarrowingSeparated` per the 2026-07-06 design
--     decision (checklist: "Right store changes and shared coercion
--     raws").
--   * The relation's coercion index is typed against ONE home store
--     (right/target); the seal correspondence mediates the source-side
--     endpoint (`Mediation.MedTy`).  Cast evidence is homed on its own
--     cast's side as a plain one-store judgment, so store changes only
--     ever rewrite raws together with the store they are typed
--     against.
--   * The proofs migrate here from the `TermNarrowingSeparated`
--     surface; once they have, the old relation is deleted.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import Types
open import Ctx using (⤊ᵗ)
open import Coercions
open import NarrowWiden using (cross; dualⁿ; dualʷ; _∣_∣_⊢_∶_⊒_)
  renaming (_↦_ to _↦ⁿʷ_)
open import Primitives
open import NuTerms
open import StoreCorrespondence
open import Mediation
open import TermNarrowingSeparated using
  ( CtxCorrEntry
  ; ctx-entry
  ; CtxCorr
  ; leftCtx
  ; rightCtx
  ; ⇑ᵍᶜ
  ; leftCtx-∋
  ; rightCtx-∋
  ; shift-left-term-typing
  ; shift-right-term-typing
  ; TermTypingEndpointsᶜ
  )
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
-- Mediated cross-store coercion evidence (home = right)
------------------------------------------------------------------------

infix 4 _∣_∣_∣_⊢_∶_⊒ᵐ_
infix 4 _∣_∣_⊢_∶ᶜ_⊒ᵐ_

_∣_∣_∣_⊢_∶_⊒ᵐ_ :
  ModeEnv → TyCtx → TyCtx → SealCorr → Coercion → Ty → Ty → Set₁
μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B =
  StoreCorr ΔL ΔR ρ ×
  WfTy ΔL A ×
  WfTy ΔR B ×
  Σ[ Aʳ ∈ Ty ]
    MedTy (MatchedVar ρ) A Aʳ ×
    (μ ∣ ΔR ∣ rightStore ρ ⊢ r ∶ Aʳ ⊒ B)

_∣_∣_⊢_∶ᶜ_⊒ᵐ_ :
  TyCtx → TyCtx → SealCorr → Coercion → Ty → Ty → Set₁
ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ B =
  tag-or-idᵈ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ᵐ B

-- Dual of one-store evidence (used for the raws the cast rules embed
-- in their own side's term).
narrowing-dual¹ :
  ∀ {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Coercion
narrowing-dual¹ (_ , cⁿ) = proj₁ (dualⁿ normalᵃ cⁿ)

narrowing-store-corrᵐᶜ :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ᵐ B →
  StoreCorr ΔL ΔR ρ
narrowing-store-corrᵐᶜ (stores , _) = stores

-- Dual of the home evidence of a mediated index.
narrowing-dualᵐ :
  ∀ {μ ΔL ΔR ρ c A B} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ c ∶ A ⊒ᵐ B →
  Coercion
narrowing-dualᵐ (_ , _ , _ , _ , _ , (_ , cⁿ)) =
  proj₁ (dualⁿ normalᵃ cⁿ)

------------------------------------------------------------------------
-- Function-coercion projections
------------------------------------------------------------------------

fun-narrow-domain-dualᵐ :
  ∀ {μ ΔL ΔR ρ p q A A′ B B′} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′) →
  Coercion
fun-narrow-domain-dualᵐ
    (_ , _ , _ , _ , _ , (_ , cross (pʷ ↦ⁿʷ _))) =
  proj₁ (dualʷ normalᵃ pʷ)

fun-narrow-domain-dualᵐᶜ :
  ∀ {ΔL ΔR ρ p q A A′ B B′} →
  ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′) →
  Coercion
fun-narrow-domain-dualᵐᶜ = fun-narrow-domain-dualᵐ

-- The mediated package for the domain dual.  Note it needs a single
-- `dualʷ-flips-typingᵐ` in the home store; the old two-store version
-- needed one per store.
fun-narrow-domain-dual-typingᵐᶜ :
  ∀ {ΔL ΔR ρ p q A A′ B B′} →
  (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
             ∶ᶜ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′)) →
  ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᵐᶜ p↦qᶜ ∶ᶜ A ⊒ᵐ A′
fun-narrow-domain-dual-typingᵐᶜ
    (stores , wf⇒ hA hB , wf⇒ hA′ hB′ , _ ,
      med-⇒ medA medB ,
      (cast-fun p⊢ q⊢ , cross (pʷ ↦ⁿʷ qⁿ))) =
  stores ,
  hA ,
  hA′ ,
  _ ,
  medA ,
  dualʷ-flips-typingᵐ
    {μ = tag-or-idᵈ}
    {η = normalᵃ}
    {ν = tag-or-idᵈ}
    dualActionOk-normal
    dualStoreAt-normal
    (rightStore-wf stores)
    (p⊢ , pʷ)

fun-narrow-codomainᵐᶜ :
  ∀ {ΔL ΔR ρ p q A A′ B B′} →
  ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′) →
  ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ B ⊒ᵐ B′
fun-narrow-codomainᵐᶜ
    (stores , wf⇒ hA hB , wf⇒ hA′ hB′ , _ ,
      med-⇒ medA medB ,
      (cast-fun p⊢ q⊢ , cross (pʷ ↦ⁿʷ qⁿ))) =
  stores , hB , hB′ , _ , medB , (q⊢ , qⁿ)

-- Mode-generic variants of the two projections above, for the cast
-- evidences the sim-beta cast branches project (their mode is the
-- cast rule's implicit, not tag-or-idᵈ).
fun-narrow-domain-dual-typingᵐ :
  ∀ {μ ΔL ΔR ρ p q A A′ B B′} →
  (p↦q⊒ : μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
             ∶ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′)) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ fun-narrow-domain-dualᵐ p↦q⊒ ∶ A ⊒ᵐ A′
fun-narrow-domain-dual-typingᵐ {μ = μ}
    (stores , wf⇒ hA hB , wf⇒ hA′ hB′ , _ ,
      med-⇒ medA medB ,
      (cast-fun p⊢ q⊢ , cross (pʷ ↦ⁿʷ qⁿ))) =
  stores ,
  hA ,
  hA′ ,
  _ ,
  medA ,
  dualʷ-flips-typingᵐ
    {μ = μ}
    {η = normalᵃ}
    {ν = μ}
    dualActionOk-normal
    dualStoreAt-normal
    (rightStore-wf stores)
    (p⊢ , pʷ)

fun-narrow-codomainᵐ :
  ∀ {μ ΔL ΔR ρ p q A A′ B B′} →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q ∶ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′) →
  μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ q ∶ B ⊒ᵐ B′
fun-narrow-codomainᵐ
    (stores , wf⇒ hA hB , wf⇒ hA′ hB′ , _ ,
      med-⇒ medA medB ,
      (cast-fun p⊢ q⊢ , cross (pʷ ↦ⁿʷ qⁿ))) =
  stores , hB , hB′ , _ , medB , (q⊢ , qⁿ)

------------------------------------------------------------------------
-- Composition side conditions
------------------------------------------------------------------------

-- Target-cast rules (⊒cast±ᵗ): both factors and the composite live in
-- the home store, because a mediated index's home typing already ends
-- at right-side types.
infix 4 _∣_∣_⊢_⨟ʳ_≈_∶_⊒ᵐ_

record _∣_∣_⊢_⨟ʳ_≈_∶_⊒ᵐ_
    (ΔL ΔR : TyCtx) (ρ : SealCorr)
    (p t r : Coercion) (A B : Ty) : Set₁ where
  constructor composed-index-tgt
  field
    {midTy} : Ty
    {νᶜᵒᵐᵖ} : ModeEnv
    p⊒ : νᶜᵒᵐᵖ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ᵐ midTy
    t⊒ʳ : νᶜᵒᵐᵖ ∣ ΔR ∣ rightStore ρ ⊢ t ∶ midTy ⊒ B
    r⊒ : νᶜᵒᵐᵖ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B

-- Source-cast rules (cast±⊒ᵗ): the cast factor lives in the left
-- store and is glued to the composition on the nose — the mediated
-- judgment's source endpoint is itself a left-side type, so the
-- middle type needs no left image and no coercion mediation (`MedCo`)
-- at all; the `MedTy` inside the mediated factors carries the only
-- mediation.  The left factor keeps its own mode environment: under
-- a left store change it shifts with the left store, while the
-- mediated factors' home typings (right store, untouched) keep
-- theirs.
infix 4 _∣_∣_⊢_⨟ˡ_≈_∶_⊒ᵐ_

record _∣_∣_⊢_⨟ˡ_≈_∶_⊒ᵐ_
    (ΔL ΔR : TyCtx) (ρ : SealCorr)
    (s q r : Coercion) (A B : Ty) : Set₁ where
  constructor composed-index-src
  field
    {midTy} : Ty          -- the inner source type; a left-side type
    {ηˢ} : ModeEnv
    {νᶜᵒᵐᵖ} : ModeEnv
    s⊒ˡ : ηˢ ∣ ΔL ∣ leftStore ρ ⊢ s ∶ A ⊒ midTy
    q⊒ : νᶜᵒᵐᵖ ∣ ΔL ∣ ΔR ∣ ρ ⊢ q ∶ midTy ⊒ᵐ B
    r⊒ : νᶜᵒᵐᵖ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B

------------------------------------------------------------------------
-- The mediated term-narrowing relation
------------------------------------------------------------------------

infix 4 _∣_∣_∣_⊢_⊒_∶_⦂_⊒ᵐ_

data _∣_∣_∣_⊢_⊒_∶_⦂_⊒ᵐ_
    : TyCtx → TyCtx → SealCorr → CtxCorr →
      Term → Term → Coercion → Ty → Ty → Set₁ where

  ⊒blameᵗ : ∀ {ΔL ΔR ρ γ M p A B μ}
    → ΔL ∣ leftStore ρ ∣ leftCtx γ ⊢ M ⦂ A
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ᵐ B
      ------------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ blame ∶ p ⦂ A ⊒ᵐ B

  x⊒xᵗ : ∀ {ΔL ΔR ρ γ x p A B}
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ B
    → γ ∋ x ⦂ ctx-entry A B p
      ---------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ ` x ⊒ ` x ∶ p ⦂ A ⊒ᵐ B

  ƛ⊒ƛᵗ : ∀ {ΔL ΔR ρ γ N N′ p q A A′ B B′}
    → (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                   ∶ᶜ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′))
    → ΔL ∣ ΔR ∣ ρ ∣
        ctx-entry A A′ (fun-narrow-domain-dualᵐᶜ p↦qᶜ) ∷ γ
        ⊢ N ⊒ N′ ∶ q ⦂ B ⊒ᵐ B′
      -------------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ ƛ N ⊒ ƛ N′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′

  ·⊒·ᵗ : ∀ {ΔL ΔR ρ γ L L′ M M′ p q A A′ B B′}
    → (p↦qᶜ : ΔL ∣ ΔR ∣ ρ ⊢ p ↦ q
                   ∶ᶜ (A ⇒ B) ⊒ᵐ (A′ ⇒ B′))
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ L′ ∶ p ↦ q
        ⦂ A ⇒ B ⊒ᵐ A′ ⇒ B′
    → ΔL ∣ ΔR ∣ ρ ∣ γ
        ⊢ M ⊒ M′ ∶ fun-narrow-domain-dualᵐᶜ p↦qᶜ ⦂ A ⊒ᵐ A′
      -----------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L · M ⊒ L′ · M′ ∶ q ⦂ B ⊒ᵐ B′

  Λ⊒Λᵗ : ∀ {ΔL ΔR ρ γ V V′ p A B}
    → ΔL ∣ ΔR ∣ ρ ⊢ `∀ p ∶ᶜ `∀ A ⊒ᵐ `∀ B
    → Value V
    → Value V′
    → suc ΔL ∣ suc ΔR ∣ ⇑ᶜorr ρ ∣ ⇑ᵍᶜ γ
        ⊢ V ⊒ V′ ∶ p ⦂ A ⊒ᵐ B
      -----------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ Λ V ⊒ Λ V′ ∶ `∀ p
        ⦂ `∀ A ⊒ᵐ `∀ B

  ⊒Λᵗ : ∀ {ΔL ΔR ρ γ N V′ p A B}
    → TermTypingEndpointsᶜ ΔL ΔR ρ γ N (Λ V′) A (`∀ B)
    → ΔL ∣ ΔR ∣ ρ ⊢ gen A p ∶ᶜ A ⊒ᵐ `∀ B
    → suc ΔL ∣ suc ΔR ∣ right-only zero ★ ∷ ⇑ᶜorr ρ ∣ ⇑ᵍᶜ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ∶ p ⦂ ⇑ᵗ A ⊒ᵐ B
      --------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ N ⊒ Λ V′ ∶ gen A p ⦂ A ⊒ᵐ `∀ B

  ⊒⟨ν⟩ᵗ : ∀ {ΔL ΔR ρ γ N V′ p s A B}
    → TermTypingEndpointsᶜ ΔL ΔR ρ γ N (V′ ⟨ gen A s ⟩) A (`∀ B)
    → ΔL ∣ ΔR ∣ ρ ⊢ gen A p ∶ᶜ A ⊒ᵐ `∀ B
    → Inert s
    → suc ΔL ∣ suc ΔR ∣ right-only zero ★ ∷ ⇑ᶜorr ρ ∣ ⇑ᵍᶜ γ
        ⊢ ⇑ᵗᵐ N ⊒ V′ ⟨ s ⟩ ∶ p ⦂ ⇑ᵗ A ⊒ᵐ B
      -----------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ N ⊒ V′ ⟨ gen A s ⟩ ∶ gen A p
        ⦂ A ⊒ᵐ `∀ B

  α⊒αᵗ : ∀ {ΔL ΔR ρ γ γ′ L L′ p q A B C D E F}
    → γ′ ≡ ⇑ᵍᶜ γ
    → TermTypingEndpointsᶜ (suc ΔL) (suc ΔR)
        (matched zero (⇑ᵗ A) zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ) γ′
        ((⇑ᵗᵐ L) •) ((⇑ᵗᵐ L′) •) C D
    → ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ A ⊒ᵐ B
    → suc ΔL ∣ suc ΔR ∣ matched zero (⇑ᵗ A) zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ
        ⊢ p ∶ᶜ C ⊒ᵐ D
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ L′ ∶ `∀ p ⦂ E ⊒ᵐ F
      ------------------------------------------------
    → suc ΔL ∣ suc ΔR ∣ matched zero (⇑ᵗ A) zero (⇑ᵗ B) ∷ ⇑ᶜorr ρ ∣ γ′
        ⊢ (⇑ᵗᵐ L) • ⊒ (⇑ᵗᵐ L′) • ∶ p ⦂ C ⊒ᵐ D

  ⊒αᵗ : ∀ {ΔL ΔR ρ γ γ′ L L′ p A B C D E F}
    → γ′ ≡ ⇑ᵍᶜ γ
    → TermTypingEndpointsᶜ (suc ΔL) (suc ΔR)
        (right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ) γ′
        (⇑ᵗᵐ L) ((⇑ᵗᵐ L′) •) C D
    → suc ΔL ∣ suc ΔR ∣ right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ
        ⊢ p ∶ᶜ C ⊒ᵐ D
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ L ⊒ L′ ∶ gen B p ⦂ E ⊒ᵐ F
      -----------------------------------------------
    → suc ΔL ∣ suc ΔR ∣ right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ ∣ γ′
        ⊢ ⇑ᵗᵐ L ⊒ (⇑ᵗᵐ L′) • ∶ p ⦂ C ⊒ᵐ D

  ν⊒νᵗ : ∀ {ΔL ΔR ρ γ A A′ B B′ N N′ p q}
    → TermTypingEndpointsᶜ ΔL ΔR ρ γ
        (ν A N (⇑ᶜ p)) (ν A′ N′ (⇑ᶜ p)) B B′
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ B ⊒ᵐ B′
    → ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ A ⊒ᵐ A′
    → suc ΔL ∣ suc ΔR ∣ matched zero (⇑ᵗ A) zero (⇑ᵗ A′) ∷ ⇑ᶜorr ρ
        ∣ ⇑ᵍᶜ γ
        ⊢ N ⊒ N′ ∶ ⇑ᶜ p ⦂ ⇑ᵗ B ⊒ᵐ ⇑ᵗ B′
      ------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ ν A N (⇑ᶜ p) ⊒ ν A′ N′ (⇑ᶜ p) ∶ p
        ⦂ B ⊒ᵐ B′

  ⊒νᵗ : ∀ {ΔL ΔR ρ γ A B B′ N N′ p}
    → TermTypingEndpointsᶜ ΔL ΔR ρ γ N (ν A N′ (⇑ᶜ p)) B B′
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ B ⊒ᵐ B′
    → suc ΔL ∣ suc ΔR ∣ right-only zero (⇑ᵗ A) ∷ ⇑ᶜorr ρ ∣ ⇑ᵍᶜ γ
        ⊢ ⇑ᵗᵐ N ⊒ N′ ∶ ⇑ᶜ p ⦂ ⇑ᵗ B ⊒ᵐ ⇑ᵗ B′
      ---------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ N ⊒ ν A N′ (⇑ᶜ p) ∶ p ⦂ B ⊒ᵐ B′

  κ⊒κᵗ : ∀ {ΔL ΔR ρ γ} κ
    → ΔL ∣ ΔR ∣ ρ ⊢ id (constTy κ) ∶ᶜ constTy κ ⊒ᵐ constTy κ
      -----------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ $ κ ⊒ $ κ ∶ id (constTy κ)
        ⦂ constTy κ ⊒ᵐ constTy κ

  ⊕⊒⊕ᵗ : ∀ {ΔL ΔR ρ γ M M′ N N′}
    → ΔL ∣ ΔR ∣ ρ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ N ⊒ N′ ∶ id (‵ `ℕ)
        ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ
      ------------------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊕[ addℕ ] N ⊒ M′ ⊕[ addℕ ] N′
        ∶ id (‵ `ℕ) ⦂ ‵ `ℕ ⊒ᵐ ‵ `ℕ

  -- The cast rules: the cast coercion's evidence lives in the store
  -- of the side that carries the cast, and the composition side
  -- condition glues that one-store factor to mediated evidence for
  -- the other two indices (`⨟ʳ` for target casts, `⨟ˡ` for source
  -- casts).

  ⊒cast+ᵗ : ∀ {ΔL ΔR ρ γ M M′ p r t A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ C
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B
    → (t⊒ʳ : η ∣ ΔR ∣ rightStore ρ ⊢ t ∶ C ⊒ B)
    → ΔL ∣ ΔR ∣ ρ ⊢ p ⨟ʳ t ≈ r ∶ A ⊒ᵐ B
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ᵐ B
      -------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ
        ⊢ M ⊒ M′ ⟨ narrowing-dual¹ t⊒ʳ ⟩ ∶ p ⦂ A ⊒ᵐ C

  ⊒cast-ᵗ : ∀ {ΔL ΔR ρ γ M M′ p r t A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ C
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B
    → η ∣ ΔR ∣ rightStore ρ ⊢ t ∶ C ⊒ B
    → ΔL ∣ ΔR ∣ ρ ⊢ p ⨟ʳ t ≈ r ∶ A ⊒ᵐ B
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ C
      ---------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ⟨ t ⟩ ∶ r ⦂ A ⊒ᵐ B

  cast+⊒ᵗ : ∀ {ΔL ΔR ρ γ M M′ q r s A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ C ⊒ᵐ B
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B
    → (s⊒ˡ : η ∣ ΔL ∣ leftStore ρ ⊢ s ∶ A ⊒ C)
    → ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ˡ q ≈ r ∶ A ⊒ᵐ B
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ q ⦂ C ⊒ᵐ B
      -------------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ
        ⊢ M ⟨ narrowing-dual¹ s⊒ˡ ⟩ ⊒ M′ ∶ r ⦂ A ⊒ᵐ B

  cast-⊒ᵗ : ∀ {ΔL ΔR ρ γ M M′ q r s A B C μ η}
    → ΔL ∣ ΔR ∣ ρ ⊢ q ∶ᶜ C ⊒ᵐ B
    → μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ r ∶ A ⊒ᵐ B
    → η ∣ ΔL ∣ leftStore ρ ⊢ s ∶ A ⊒ C
    → ΔL ∣ ΔR ∣ ρ ⊢ s ⨟ˡ q ≈ r ∶ A ⊒ᵐ B
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ᵐ B
      ---------------------------------------------------
    → ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⟨ s ⟩ ⊒ M′ ∶ q ⦂ C ⊒ᵐ B

------------------------------------------------------------------------
-- Extractors
------------------------------------------------------------------------

typed-term-narrowing-term-typingᵐᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  TermTypingEndpointsᶜ ΔL ΔR ρ γ M M′ A B
typed-term-narrowing-term-typingᵐᶜ
    (⊒blameᵗ M⊢ (_ , _ , hB , _)) =
  M⊢ , ⊢blame hB
typed-term-narrowing-term-typingᵐᶜ (x⊒xᵗ pᶜ x∋p) =
  ⊢` (leftCtx-∋ x∋p) , ⊢` (rightCtx-∋ x∋p)
typed-term-narrowing-term-typingᵐᶜ
    (ƛ⊒ƛᵗ (_ , wf⇒ hA hB , wf⇒ hA′ hB′ , _) N⊒N′) =
  let
    N⊢ , N′⊢ = typed-term-narrowing-term-typingᵐᶜ N⊒N′
  in
  ⊢ƛ hA N⊢ , ⊢ƛ hA′ N′⊢
typed-term-narrowing-term-typingᵐᶜ (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  let
    L⊢ , L′⊢ = typed-term-narrowing-term-typingᵐᶜ L⊒L′
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᵐᶜ M⊒M′
  in
  ⊢· L⊢ M⊢ , ⊢· L′⊢ M′⊢
typed-term-narrowing-term-typingᵐᶜ {ρ = ρ} {γ = γ}
    (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′) =
  let
    V⊢ , V′⊢ = typed-term-narrowing-term-typingᵐᶜ V⊒V′
  in
  ⊢Λ vV (shift-left-term-typing {ρ = ρ} {γ = γ} V⊢) ,
  ⊢Λ vV′ (shift-right-term-typing {ρ = ρ} {γ = γ} V′⊢)
typed-term-narrowing-term-typingᵐᶜ (⊒Λᵗ typing genᶜ N⊒V′) = typing
typed-term-narrowing-term-typingᵐᶜ (⊒⟨ν⟩ᵗ typing genᶜ i N⊒V′s) =
  typing
typed-term-narrowing-term-typingᵐᶜ (α⊒αᵗ γ′≡ typing qᶜ pᶜ L⊒L′) =
  typing
typed-term-narrowing-term-typingᵐᶜ (⊒αᵗ γ′≡ typing pᶜ L⊒L′) = typing
typed-term-narrowing-term-typingᵐᶜ (ν⊒νᵗ typing pᶜ qᶜ N⊒N′) = typing
typed-term-narrowing-term-typingᵐᶜ (⊒νᵗ typing pᶜ N⊒N′) = typing
typed-term-narrowing-term-typingᵐᶜ (κ⊒κᵗ κ pᶜ) =
  ⊢$ κ , ⊢$ κ
typed-term-narrowing-term-typingᵐᶜ (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′) =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᵐᶜ M⊒M′
    N⊢ , N′⊢ = typed-term-narrowing-term-typingᵐᶜ N⊒N′
  in
  ⊢⊕ M⊢ addℕ N⊢ , ⊢⊕ M′⊢ addℕ N′⊢
typed-term-narrowing-term-typingᵐᶜ
    (⊒cast+ᵗ {η = η} pᶜ r⊒ t⊒ʳ _ M⊒M′) =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᵐᶜ M⊒M′
    tᵈ⊢ =
      dualⁿ-flips-typingᵐ
        {μ = η} {η = normalᵃ} {ν = η}
        dualActionOk-normal
        dualStoreAt-normal
        (rightStore-wf (narrowing-store-corrᵐᶜ pᶜ))
        t⊒ʳ
  in
  M⊢ , ⊢⟨⟩ (proj₁ tᵈ⊢) M′⊢
typed-term-narrowing-term-typingᵐᶜ
    (⊒cast-ᵗ pᶜ r⊒ t⊒ʳ _ M⊒M′) =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᵐᶜ M⊒M′
  in
  M⊢ , ⊢⟨⟩ (proj₁ t⊒ʳ) M′⊢
typed-term-narrowing-term-typingᵐᶜ
    (cast+⊒ᵗ {η = η} qᶜ r⊒ s⊒ˡ _ M⊒M′) =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᵐᶜ M⊒M′
    sᵈ⊢ =
      dualⁿ-flips-typingᵐ
        {μ = η} {η = normalᵃ} {ν = η}
        dualActionOk-normal
        dualStoreAt-normal
        (leftStore-wf (narrowing-store-corrᵐᶜ qᶜ))
        s⊒ˡ
  in
  ⊢⟨⟩ (proj₁ sᵈ⊢) M⊢ , M′⊢
typed-term-narrowing-term-typingᵐᶜ
    (cast-⊒ᵗ qᶜ r⊒ s⊒ˡ _ M⊒M′) =
  let
    M⊢ , M′⊢ = typed-term-narrowing-term-typingᵐᶜ M⊒M′
  in
  ⊢⟨⟩ (proj₁ s⊒ˡ) M⊢ , M′⊢

typed-term-narrowing-coercionᵐ :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  ∃[ μ ] μ ∣ ΔL ∣ ΔR ∣ ρ ⊢ p ∶ A ⊒ᵐ B
typed-term-narrowing-coercionᵐ (⊒blameᵗ {μ = μ} M⊢ p⊒) = μ , p⊒
typed-term-narrowing-coercionᵐ (x⊒xᵗ pᶜ x∋p) = tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) = tag-or-idᵈ , p↦qᶜ
typed-term-narrowing-coercionᵐ (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  tag-or-idᵈ , fun-narrow-codomainᵐᶜ p↦qᶜ
typed-term-narrowing-coercionᵐ (Λ⊒Λᵗ allᶜ vV vV′ V⊒V′) =
  tag-or-idᵈ , allᶜ
typed-term-narrowing-coercionᵐ (⊒Λᵗ typing genᶜ N⊒V′) =
  tag-or-idᵈ , genᶜ
typed-term-narrowing-coercionᵐ (⊒⟨ν⟩ᵗ typing genᶜ i N⊒V′s) =
  tag-or-idᵈ , genᶜ
typed-term-narrowing-coercionᵐ (α⊒αᵗ γ′≡ typing qᶜ pᶜ L⊒L′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (⊒αᵗ γ′≡ typing pᶜ L⊒L′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (ν⊒νᵗ typing pᶜ qᶜ N⊒N′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (⊒νᵗ typing pᶜ N⊒N′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (κ⊒κᵗ κ pᶜ) = tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (⊒cast+ᵗ pᶜ r⊒ t⊒ʳ _ M⊒M′) =
  tag-or-idᵈ , pᶜ
typed-term-narrowing-coercionᵐ (⊒cast-ᵗ {μ = μ} pᶜ r⊒ t⊒ʳ _ M⊒M′) =
  μ , r⊒
typed-term-narrowing-coercionᵐ (cast+⊒ᵗ {μ = μ} qᶜ r⊒ s⊒ˡ _ M⊒M′) =
  μ , r⊒
typed-term-narrowing-coercionᵐ (cast-⊒ᵗ qᶜ r⊒ s⊒ˡ _ M⊒M′) =
  tag-or-idᵈ , qᶜ

typed-term-narrowing-source-typingᵐᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  ΔL ∣ leftStore ρ ∣ leftCtx γ ⊢ M ⦂ A
typed-term-narrowing-source-typingᵐᶜ M⊒M′ =
  proj₁ (typed-term-narrowing-term-typingᵐᶜ M⊒M′)

typed-term-narrowing-target-typingᵐᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B} →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  ΔR ∣ rightStore ρ ∣ rightCtx γ ⊢ M′ ⦂ B
typed-term-narrowing-target-typingᵐᶜ M⊒M′ =
  proj₂ (typed-term-narrowing-term-typingᵐᶜ M⊒M′)
