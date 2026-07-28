module proof.Compilation.CompileTermImprecision where

-- File Charter:
--   * Proves compilation monotone from gradual-term imprecision to the new
--     mutually recursive ordinary/quotiented Nu-term imprecision judgments.
--   * Uses quotiented type imprecision only between the hidden lower types of
--     compiled narrowing/widening pairs.
--   * Keeps application and cast reasoning orthogonal.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst; sym; trans)

open import Types
open import Ctx using (CtxWf; ctxWf-∷)
open import Coercions using (id-only≤tag-or-idᵈ)
open import CastImprecisionShape using
  ( narrowing
  ; widening
  ; shape-id-star
  ; shape-fun
  ; shape-untag-fun
  ; _⊢ᶜ_⦂_
  )
open import Conversion using (reveal↑)
open import Compile using
  ( CastPlan
  ; cast
  ; compileᵀ
  ; compileᵀ-value
  ; consistency-cast-plan
  ; dynamic-application-function-consistent
  ; down
  ; down⊒
  ; down-shape
  ; lower
  ; lower-selected
  ; lower⊑source
  ; lower⊑target
  ; up
  ; up⊑
  ; up-shape
  ; ν-reveal-conversion
  )
open import GradualTerms
  using (GTerm)
  renaming
    ( `_ to `ᴳ_
    ; ƛ_⇒_ to ƛᴳ_⇒_
    ; _·[_]_ to _·ᴳ[_]_
    ; Λ_ to Λᴳ_
    ; _`[_] to _`ᴳ[_]
    ; $ to $ᴳ
    ; _⊕[_at_]_ to _⊕ᴳ[_at_]_
    ; _∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_
    ; ⊢` to ⊢ᴳ`
    ; ⊢ƛ to ⊢ᴳƛ
    ; ⊢· to ⊢ᴳ·
    ; ⊢·★ to ⊢ᴳ·★
    ; ⊢Λ to ⊢ᴳΛ
    ; ⊢• to ⊢ᴳ•
    ; ⊢$ to ⊢ᴳ$
    ; ⊢⊕ to ⊢ᴳ⊕
    )
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
import ImprecisionWf as IWF
import Imprecision as Imp
open import Imprecision using () renaming (idι to idιᴵ; ν to νᴵ)
open import ImprecisionWf
  using
    ( ImpCtx
    ; _ˣ⊑★
    ; _ˣ⊑ˣ_
    ; ⇑ᵢ
    ; ⇑ᴸᵢ
    ; _∣_⊢_⊑_⊣_
    )
open import ImprecisionComposition using
  ( ⌊_⌋
  ; id★ˢ
  ; _↦ˢ_
  ; tag_⇛ˢ_
  ; comp-↦-↦
  ; comp-↦-tag
  ; _；⌊_⌋≋ᵖ_；_
  )
open import NuTerms using (Term)
open import NarrowWiden using (narrow-mode-relax; widen-mode-relax)
open import Primitives using (Prim; addℕ; κℕ)
open import proof.Core.Properties.NuTermProperties using (CtxWf-⤊)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( shape-lift∀ᵢ
  ; shape-source-liftνᵢ
  )
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-target-star-right-id★)
open import proof.Core.Properties.CastImprecision using (seal★-tag-or-id)
open import proof.Core.Properties.NarrowWidenProperties using (StoreDetWf)
open import proof.Core.Properties.ImprecisionProperties using
  ( ~-sym
  ; ⊑-base-inv-idᵢ
  ; ⊑-forall-base-⊥
  ; ⊑-refl-idᵢ
  )
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimpleQuotient using
  (MLB-monotoneᵖ)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ⊑-forgetᵢ
  ; ⊑-lift∀ᵢ
  ; ⊑-source-liftνᵢ
  )
open import proof.Core.Properties.TypeProperties using
  ( TyRenameWf-suc
  ; renameᵗ-preserves-WfTy
  )
open import TermTyping using (cast-tag-or-id)

import GradualTermImprecision as GTI
open import GradualTermImprecision using (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
import proof.NuCore.Relations.NuImprecisionTermContextDef as NTI
import proof.Store.Core.NuImprecisionRelationalStoreDef as NTS
import QuotientedTermImprecision as QTI
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)

variable
  Φ Ψ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  γ γ′ : GTI.CtxImp Φ Δᴸ Δᴿ
  A A′ B B′ C C′ : Ty
  p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
  M M′ N N′ L L′ V V′ : GTerm
  x : Var
  ℓ : Label
  op : Prim

storeDetWf-[] :
  ∀ {Δ} →
  StoreDetWf Δ []
storeDetWf-[] =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; wfOlder = λ ()
    ; unique = λ ()
    }

------------------------------------------------------------------------
-- Context conversion
------------------------------------------------------------------------

ctxImpToNuEntry :
  GTI.CtxImpEntry Φ Δᴸ Δᴿ →
  NTI.CtxImpEntry Φ Δᴸ Δᴿ
ctxImpToNuEntry (GTI.ctx-imp A B p) =
  NTI.ctx-imp A B p

ctxImpToNu :
  GTI.CtxImp Φ Δᴸ Δᴿ →
  NTI.CtxImp Φ Δᴸ Δᴿ
ctxImpToNu [] = []
ctxImpToNu (entry ∷ γ) = ctxImpToNuEntry entry ∷ ctxImpToNu γ

leftCtx-ctxImpToNu :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : GTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.leftCtxⁱ (ctxImpToNu γ) ≡ GTI.srcCtxⁱ γ
leftCtx-ctxImpToNu [] = refl
leftCtx-ctxImpToNu (GTI.ctx-imp A B p ∷ γ) =
  cong₂ _∷_ refl (leftCtx-ctxImpToNu γ)

rightCtx-ctxImpToNu :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : GTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.rightCtxⁱ (ctxImpToNu γ) ≡ GTI.tgtCtxⁱ γ
rightCtx-ctxImpToNu [] = refl
rightCtx-ctxImpToNu (GTI.ctx-imp A B p ∷ γ) =
  cong₂ _∷_ refl (rightCtx-ctxImpToNu γ)

ctxImpToNu-∋ :
  ∀ {Φ Δᴸ Δᴿ γ x A B p} →
  γ ∋ x ⦂ GTI.ctx-imp A B p →
  ctxImpToNu {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} γ
    ∋ x ⦂ NTI.ctx-imp A B p
ctxImpToNu-∋ Z = Z
ctxImpToNu-∋ (S x∈) = S (ctxImpToNu-∋ x∈)

ctxImpToNu-lift :
  ∀ {Φ Δᴸ Δᴿ Ψ}
    {γ : GTI.CtxImp Φ Δᴸ Δᴿ}
    {γ′ : GTI.CtxImp Ψ (suc Δᴸ) (suc Δᴿ)} →
  GTI.LiftCtxⁱ Ψ γ γ′ →
  NTI.LiftCtxⁱ Ψ (ctxImpToNu γ) (ctxImpToNu γ′)
ctxImpToNu-lift GTI.lift-[] = NTI.lift-ctx-[]
ctxImpToNu-lift (GTI.lift-∷ shape liftγ) =
  NTI.lift-ctx-∷ shape (ctxImpToNu-lift liftγ)

ctxImpToNu-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ}
    {γ : GTI.CtxImp Φ Δᴸ Δᴿ}
    {γ′ : GTI.CtxImp Ψ (suc Δᴸ) Δᴿ} →
  GTI.LiftLeftCtxⁱ Ψ γ γ′ →
  NTI.LiftLeftCtxⁱ Ψ (ctxImpToNu γ) (ctxImpToNu γ′)
ctxImpToNu-lift-left GTI.lift-left-[] = NTI.lift-left-ctx-[]
ctxImpToNu-lift-left (GTI.lift-left-∷ shape liftγ) =
  NTI.lift-left-ctx-∷ shape (ctxImpToNu-lift-left liftγ)

------------------------------------------------------------------------
-- Type-imprecision lifting for ν compilation
------------------------------------------------------------------------

nuCtx⇑ :
  ∀ {Φ Δᴸ Δᴿ} →
  NTI.CtxImp Φ Δᴸ Δᴿ →
  NTI.CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) (suc Δᴸ) (suc Δᴿ)
nuCtx⇑ [] = []
nuCtx⇑ (NTI.ctx-imp A B p ∷ γ) =
  NTI.ctx-imp (⇑ᵗ A) (⇑ᵗ B) (⊑-lift∀ᵢ p) ∷ nuCtx⇑ γ

nuCtx⇑-lift :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ (nuCtx⇑ γ)
nuCtx⇑-lift [] = NTI.lift-ctx-[]
nuCtx⇑-lift (NTI.ctx-imp A B p ∷ γ) =
  NTI.lift-ctx-∷ (shape-lift∀ᵢ p) (nuCtx⇑-lift γ)

nuCtx⇑ᴸ :
  ∀ {Φ Δᴸ Δᴿ} →
  NTI.CtxImp Φ Δᴸ Δᴿ →
  NTI.CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ
nuCtx⇑ᴸ [] = []
nuCtx⇑ᴸ (NTI.ctx-imp A B p ∷ γ) =
  NTI.ctx-imp (⇑ᵗ A) B (⊑-source-liftνᵢ p) ∷ nuCtx⇑ᴸ γ

nuCtx⇑ᴸ-lift :
  ∀ {Φ Δᴸ Δᴿ} →
  (γ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  NTI.LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ (nuCtx⇑ᴸ γ)
nuCtx⇑ᴸ-lift [] = NTI.lift-left-ctx-[]
nuCtx⇑ᴸ-lift (NTI.ctx-imp A B p ∷ γ) =
  NTI.lift-left-ctx-∷ (shape-source-liftνᵢ p) (nuCtx⇑ᴸ-lift γ)

------------------------------------------------------------------------
-- Congruence helpers for compiler proof plumbing
------------------------------------------------------------------------

compile-context-subst-term-sym :
  ∀ {Δ Γ Γ′ M A}
  → (Γ′≡Γ : Γ′ ≡ Γ)
  → (Γ-wf : CtxWf Δ Γ)
  → (M⊢ : Δ ∣ Γ′ ⊢ᴳ M ⦂ A)
  → proj₁
      (compileᵀ
        (subst (CtxWf Δ) (sym Γ′≡Γ) Γ-wf)
        M⊢)
      ≡ proj₁
        (compileᵀ
          Γ-wf
          (subst (λ Γ₀ → Δ ∣ Γ₀ ⊢ᴳ M ⦂ A) Γ′≡Γ M⊢))
compile-context-subst-term-sym refl Γ-wf M⊢ = refl

nu-term-imprecision-cong-terms :
  ∀ {Φ Δᴸ Δᴿ ρ γ L L′ R R′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  L ≡ L′ →
  R ≡ R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ L ⊑ R ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ ⊢ᴺ L′ ⊑ R′ ⦂ A ⊑ B ∶ p
nu-term-imprecision-cong-terms refl refl L⊑R = L⊑R

imprecision-target-subst :
  ∀ {Φ Δᴸ Δᴿ A B B′} →
  B ≡ B′ →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ
imprecision-target-subst refl A⊑B = A⊑B

compiled-argument-cast-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ M M′ A A′ C C′ pA pC} →
  (plan : CastPlan Δᴸ [] C A) →
  (plan′ : CastPlan Δᴿ [] C′ A′) →
  (q : Φ ∣ Δᴸ ⊢ lower plan ⊑ᵖ lower plan′ ⊣ Δᴿ) →
  ⌊ lower⊑source plan ⌋ ；⌊ pC ⌋≋ᵖ q ；
    ⌊ lower⊑source plan′ ⌋ →
  ⌊ lower⊑target plan ⌋ ；⌊ pA ⌋≋ᵖ q ；
    ⌊ lower⊑target plan′ ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ cast plan M ⊑ cast plan′ M′ ⦂ A ⊑ A′ ∶ pA
compiled-argument-cast-imprecision {pA = pA}
    plan plan′ lower⊑lower′ down-square up-square M⊑M′ =
  QTI.up⊑upᵀ
    (QTI.down⊑downᵀ
      (down⊒ plan) (down-shape plan)
      (down⊒ plan′) (down-shape plan′)
      M⊑M′ lower⊑lower′ down-square)
    (QTI.quotient-id-widening (up⊑ plan) (up⊑ plan′))
    pA (up-shape plan) (up-shape plan′) up-square

compiled-cast-nat-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ M M′ A A′ p ℓ} →
  (A~ℕ : Imp._⊢_~_ Δᴸ A (‵ `ℕ)) →
  (A′~ℕ : Imp._⊢_~_ Δᴿ A′ (‵ `ℕ)) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ cast (consistency-cast-plan ℓ A~ℕ) M
      ⊑ cast (consistency-cast-plan ℓ A′~ℕ) M′
    ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ IWF.idι
compiled-cast-nat-imprecision
    {p = p} {ℓ = ℓ} A~ℕ A′~ℕ M⊑M′ =
  let
    plan = consistency-cast-plan ℓ A~ℕ
    plan′ = consistency-cast-plan ℓ A′~ℕ
    lower-monotonicity =
      MLB-monotoneᵖ p IWF.idι
        (lower-selected plan) (lower-selected plan′)
  in
  compiled-argument-cast-imprecision plan plan′
    (proj₁ lower-monotonicity)
    (proj₁ (proj₂ lower-monotonicity))
    (proj₂ (proj₂ lower-monotonicity))
    M⊑M′

dynamic-application-plan-lower :
  ∀ (Δ : TyCtx) (ℓ : Label) →
  lower
    (consistency-cast-plan {Δ = Δ} ℓ
      dynamic-application-function-consistent)
    ≡ ★ ⇒ ★
dynamic-application-plan-lower Δ ℓ = refl

dynamic-application-plan-down-shape :
  ∀ (Δ : TyCtx) (ℓ : Label) →
  narrowing
    ⊢ᶜ down
      (consistency-cast-plan {Δ = Δ} ℓ
        dynamic-application-function-consistent)
    ⦂ tag id★ˢ ⇛ˢ id★ˢ
dynamic-application-plan-down-shape Δ ℓ =
  shape-untag-fun

dynamic-application-plan-up-shape :
  ∀ (Δ : TyCtx) (ℓ : Label) →
  widening
    ⊢ᶜ up
      (consistency-cast-plan {Δ = Δ} ℓ
        dynamic-application-function-consistent)
    ⦂ id★ˢ ↦ˢ id★ˢ
dynamic-application-plan-up-shape Δ ℓ =
  shape-fun shape-id-star shape-id-star

compiled-right-dynamic-function-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ L L′ A B pA pB ℓ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ L ⊑ L′ ⦂ A ⇒ B ⊑ ★ ∶ IWF.tag pA ⇛ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ L ⊑ cast
      (consistency-cast-plan {Δ = Δᴿ} ℓ
        dynamic-application-function-consistent) L′
    ⦂ A ⇒ B ⊑ ★ ⇒ ★ ∶ pA IWF.↦ pB
compiled-right-dynamic-function-imprecision
    {Δᴿ = Δᴿ} {pA = pA} {pB = pB} {ℓ = ℓ} L⊑L′ =
  let
    plan = consistency-cast-plan {Δ = Δᴿ} ℓ
      dynamic-application-function-consistent
    arrow⊑lower =
      imprecision-target-subst
        (sym (dynamic-application-plan-lower Δᴿ ℓ))
        (pA IWF.↦ pB)
    L⊑L′↓ =
      QTI.⊑cast⊒ᵀ cast-tag-or-id seal★-tag-or-id
        (narrow-mode-relax id-only≤tag-or-idᵈ (down⊒ plan))
        L⊑L′ arrow⊑lower
        (dynamic-application-plan-down-shape Δᴿ ℓ)
        (comp-↦-tag
          (compose-target-star-right-id★ pA)
          (compose-target-star-right-id★ pB))
  in
  QTI.⊑cast⊑ᵀ cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ (up⊑ plan))
    L⊑L′↓ (pA IWF.↦ pB)
    (dynamic-application-plan-up-shape Δᴿ ℓ)
    (comp-↦-↦
      (compose-target-star-right-id★ pA)
      (compose-target-star-right-id★ pB))

compiled-dynamic-function-imprecision :
  ∀ {Φ Δᴸ Δᴿ δ L L′ ℓ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ L ⊑ L′ ⦂ ★ ⊑ ★ ∶ IWF.id★ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ δ
    ⊢ᴺ cast
      (consistency-cast-plan {Δ = Δᴸ} ℓ
        dynamic-application-function-consistent) L
      ⊑ cast
        (consistency-cast-plan {Δ = Δᴿ} ℓ
          dynamic-application-function-consistent) L′
    ⦂ ★ ⇒ ★ ⊑ ★ ⇒ ★ ∶ IWF.id★ IWF.↦ IWF.id★
compiled-dynamic-function-imprecision
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ℓ = ℓ} L⊑L′ =
  let
    plan = consistency-cast-plan {Δ = Δᴸ} ℓ
      dynamic-application-function-consistent
    plan′ = consistency-cast-plan {Δ = Δᴿ} ℓ
      dynamic-application-function-consistent
    lower-monotonicity =
      MLB-monotoneᵖ IWF.id★
        (IWF.id★ IWF.↦ IWF.id★)
        (lower-selected plan) (lower-selected plan′)
  in
  compiled-argument-cast-imprecision plan plan′
    (proj₁ lower-monotonicity)
    (proj₁ (proj₂ lower-monotonicity))
    (proj₂ (proj₂ lower-monotonicity))
    L⊑L′

------------------------------------------------------------------------
-- Compile monotonicity
------------------------------------------------------------------------

compile-preserves-term-imprecision-typed :
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ ctxImpToNu γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
compile-preserves-term-imprecision-typed
    srcΓ-wf tgtΓ-wf (GTI.x⊑xᴳ x∈) =
  QTI.x⊑xᵀ (ctxImpToNu-∋ x∈)
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.ƛ⊑ƛᴳ hA hA′ N⊑N′) =
  QTI.ƛ⊑ƛᵀ hA hA′
    (compile-preserves-term-imprecision-typed
      (ctxWf-∷ hA srcΓ-wf)
      (ctxWf-∷ hA′ tgtΓ-wf)
      N⊑N′)
-- application, function endpoints on both sides
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.·⊑·ᴳ {ℓ = ℓ} {pA = pA} {pC = pC}
      L⊑L′ N⊑N′ A~C A′~C′) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
    plan = consistency-cast-plan ℓ (~-sym A~C)
    plan′ = consistency-cast-plan ℓ (~-sym A′~C′)
    lower-monotonicity =
      MLB-monotoneᵖ pC pA
        (lower-selected plan) (lower-selected plan′)
  in
  QTI.·⊑·ᵀ
    L⊑L′ᵀ
    (compiled-argument-cast-imprecision plan plan′
      (proj₁ lower-monotonicity)
      (proj₁ (proj₂ lower-monotonicity))
      (proj₂ (proj₂ lower-monotonicity))
      N⊑N′ᵀ)
-- application, right function type is ★
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.·⊑·★ᴳ {ℓ = ℓ} {pA = pA} {pB = pB} {pC = pC}
      L⊑L′ N⊑N′ A~C C′~★) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
    argument-plan = consistency-cast-plan ℓ (~-sym A~C)
    argument-plan′ = consistency-cast-plan ℓ C′~★
    argument-lower-monotonicity =
      MLB-monotoneᵖ pC pA
        (lower-selected argument-plan) (lower-selected argument-plan′)
  in
  QTI.·⊑·ᵀ
    (compiled-right-dynamic-function-imprecision {ℓ = ℓ} L⊑L′ᵀ)
    (compiled-argument-cast-imprecision argument-plan argument-plan′
      (proj₁ argument-lower-monotonicity)
      (proj₁ (proj₂ argument-lower-monotonicity))
      (proj₂ (proj₂ argument-lower-monotonicity))
      N⊑N′ᵀ)
-- application, both function types are ★
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.·★⊑·★ᴳ {ℓ = ℓ} {pC = pC}
      L⊑L′ N⊑N′ C~★ C′~★) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
    argument-plan = consistency-cast-plan ℓ C~★
    argument-plan′ = consistency-cast-plan ℓ C′~★
    argument-lower-monotonicity =
      MLB-monotoneᵖ pC IWF.id★
        (lower-selected argument-plan) (lower-selected argument-plan′)
  in
  QTI.·⊑·ᵀ
    (compiled-dynamic-function-imprecision {ℓ = ℓ} L⊑L′ᵀ)
    (compiled-argument-cast-imprecision argument-plan argument-plan′
      (proj₁ argument-lower-monotonicity)
      (proj₁ (proj₂ argument-lower-monotonicity))
      (proj₂ (proj₂ argument-lower-monotonicity))
      N⊑N′ᵀ)
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.Λ⊑Λᴳ liftγ vV vV′ occA occB V⊑V′) =
  QTI.Λ⊑Λᵀ
    NTS.lift-store-[]
    (ctxImpToNu-lift liftγ)
    (compileᵀ-value (CtxWf-⤊ srcΓ-wf) vV
      (subst
        (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
        (GTI.srcCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑V′)))
    (compileᵀ-value (CtxWf-⤊ tgtΓ-wf) vV′
      (subst
        (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
        (GTI.tgtCtxⁱ-lift liftγ)
        (GTI.gradual-term-imprecision-target-typing V⊑V′)))
    (nu-term-imprecision-cong-terms
      (compile-context-subst-term-sym
        (GTI.srcCtxⁱ-lift liftγ)
        (CtxWf-⤊ srcΓ-wf)
        (GTI.gradual-term-imprecision-source-typing V⊑V′))
      (compile-context-subst-term-sym
        (GTI.tgtCtxⁱ-lift liftγ)
        (CtxWf-⤊ tgtΓ-wf)
        (GTI.gradual-term-imprecision-target-typing V⊑V′))
      (compile-preserves-term-imprecision-typed
        (subst (CtxWf _) (sym (GTI.srcCtxⁱ-lift liftγ))
          (CtxWf-⤊ srcΓ-wf))
        (subst (CtxWf _) (sym (GTI.tgtCtxⁱ-lift liftγ))
          (CtxWf-⤊ tgtΓ-wf))
        V⊑V′))
-- left-only Λ imprecision
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    rel@(GTI.Λ⊑ᴳ occ liftγ vV V⊑N′) =
  let
    V⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        (subst (CtxWf _) (sym (GTI.srcCtxⁱ-lift-left liftγ))
          (CtxWf-⤊ srcΓ-wf))
        (subst (CtxWf _) (sym (GTI.tgtCtxⁱ-lift-left liftγ))
          tgtΓ-wf)
        V⊑N′
  in
  QTI.Λ⊑ᵀ occ
    NTS.lift-left-store-[]
    (ctxImpToNu-lift-left liftγ)
    (compileᵀ-value (CtxWf-⤊ srcΓ-wf) vV
      (subst
        (λ Γ → _ ∣ Γ ⊢ᴳ _ ⦂ _)
        (GTI.srcCtxⁱ-lift-left liftγ)
        (GTI.gradual-term-imprecision-source-typing V⊑N′)))
    (nu-term-imprecision-cong-terms
      (compile-context-subst-term-sym
        (GTI.srcCtxⁱ-lift-left liftγ)
        (CtxWf-⤊ srcΓ-wf)
        (GTI.gradual-term-imprecision-source-typing V⊑N′))
      (compile-context-subst-term-sym
        (GTI.tgtCtxⁱ-lift-left liftγ)
        tgtΓ-wf
        (GTI.gradual-term-imprecision-target-typing V⊑N′))
      V⊑N′ᵀ)
-- synchronized type application
compile-preserves-term-imprecision-typed
    {γ = γ} srcΓ-wf tgtΓ-wf
    rel@(GTI.[]⊑[]ᴳ hA hT hB hT′ M⊑M′ q r replacement) =
  let
    M⊑M′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        M⊑M′
  in
  QTI.ν⊑νᵀ hT hT′
    (reveal↑ (ν-reveal-conversion hT hA))
    (reveal↑ (ν-reveal-conversion hT′ hB))
    q
    (⊑-lift∀ᵢ q)
    NTS.lift-store-[]
    (nuCtx⇑-lift (ctxImpToNu γ))
    M⊑M′ᵀ
    replacement
-- left-only type application
compile-preserves-term-imprecision-typed
    {γ = γ} srcΓ-wf tgtΓ-wf
    rel@(GTI.[]⊑ᴳ hA hT M⊑M′ q r replacement) =
  let
    M⊑M′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        M⊑M′
  in
  QTI.ν⊑ᵀ hT
    (renameᵗ-preserves-WfTy hT TyRenameWf-suc)
    (reveal↑ (ν-reveal-conversion hT hA))
    NTS.lift-left-store-[]
    (nuCtx⇑ᴸ-lift (ctxImpToNu γ))
    M⊑M′ᵀ
    replacement
compile-preserves-term-imprecision-typed
    srcΓ-wf tgtΓ-wf GTI.κ⊑κᴳ =
  QTI.κ⊑κᵀ
-- primitive addition
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    prim@(GTI.⊕⊑⊕ᴳ {op = addℕ} {ℓ = ℓ} L⊑L′ A~ℕ A′~ℕ
      N⊑N′ B~ℕ B′~ℕ) =
  let
    L⊑L′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        L⊑L′
    N⊑N′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        N⊑N′
  in
  QTI.⊕⊑⊕ᵀ
    (compiled-cast-nat-imprecision {ℓ = ℓ} A~ℕ A′~ℕ L⊑L′ᵀ)
    (compiled-cast-nat-imprecision {ℓ = ℓ} B~ℕ B′~ℕ N⊑N′ᵀ)

compile-preserves-term-imprecision :
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ ctxImpToNu γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
compile-preserves-term-imprecision
    srcΓ-wf tgtΓ-wf M⊑M′ =
  compile-preserves-term-imprecision-typed
    srcΓ-wf
    tgtΓ-wf
    M⊑M′
