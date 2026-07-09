module proof.CompileTermImprecision where

-- File Charter:
--   * Compile monotonicity scaffold for source gradual-term imprecision.
--   * Converts `GradualTermImprecision` contexts to `NuTermImprecision`
--     contexts and proves the structural compiler cases.
--   * Leaves the cast/ν-heavy compiler cases as Agda interaction holes, so
--     the remaining proof obligations are reported directly by Agda.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst; sym)

open import Types
open import Ctx using (CtxWf; ctxWf-∷)
open import Compile using (compileᵀ; compileᵀ-value)
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
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTerms using (Term)
open import Primitives using (Prim; addℕ; κℕ)
open import proof.NuTermProperties using (CtxWf-⤊)

import GradualTermImprecision as GTI
open import GradualTermImprecision using (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
import NuTermImprecision as NTI
open import NuTermImprecision using (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)

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
ctxImpToNu-lift (GTI.lift-∷ liftγ) =
  NTI.lift-ctx-∷ (ctxImpToNu-lift liftγ)

ctxImpToNu-lift-left :
  ∀ {Φ Δᴸ Δᴿ Ψ}
    {γ : GTI.CtxImp Φ Δᴸ Δᴿ}
    {γ′ : GTI.CtxImp Ψ (suc Δᴸ) Δᴿ} →
  GTI.LiftLeftCtxⁱ Ψ γ γ′ →
  NTI.LiftLeftCtxⁱ Ψ (ctxImpToNu γ) (ctxImpToNu γ′)
ctxImpToNu-lift-left GTI.lift-left-[] = NTI.lift-left-ctx-[]
ctxImpToNu-lift-left (GTI.lift-left-∷ liftγ) =
  NTI.lift-left-ctx-∷ (ctxImpToNu-lift-left liftγ)

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

------------------------------------------------------------------------
-- Compile monotonicity, with holes for the remaining hard cases
------------------------------------------------------------------------

compile-preserves-term-imprecision-typed :
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ ctxImpToNu γ ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf (GTI.x⊑xᴳ x∈) =
  NTI.x⊑xᵀ (ctxImpToNu-∋ x∈)
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.ƛ⊑ƛᴳ hA hA′ N⊑N′) =
  NTI.ƛ⊑ƛᵀ hA hA′
    (compile-preserves-term-imprecision-typed
      (ctxWf-∷ hA srcΓ-wf)
      (ctxWf-∷ hA′ tgtΓ-wf)
      N⊑N′)
-- application, function endpoints on both sides
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    app@(GTI.·⊑·ᴳ L⊑L′ N⊑N′ A~C A′~C′) =
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
  {!!}
-- application, right function type is ★
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    app@(GTI.·⊑·★ᴳ L⊑L′ N⊑N′ A~C C′~★) =
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
  {!!}
-- application, both function types are ★
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    app@(GTI.·★⊑·★ᴳ L⊑L′ N⊑N′ C~★ C′~★) =
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
  {!!}
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    (GTI.Λ⊑Λᴳ liftγ vV vV′ occA occB V⊑V′) =
  NTI.Λ⊑Λᵀ
    NTI.lift-store-[]
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
  {!!}
-- synchronized type application
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    rel@(GTI.[]⊑[]ᴳ hA hT hB hT′ M⊑M′ q r) =
  let
    M⊑M′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        M⊑M′
  in
  {!!}
-- left-only type application
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    rel@(GTI.[]⊑ᴳ hA hT M⊑M′ q r) =
  let
    M⊑M′ᵀ =
      compile-preserves-term-imprecision-typed
        srcΓ-wf
        tgtΓ-wf
        M⊑M′
  in
  {!!}
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf GTI.κ⊑κᴳ =
  NTI.κ⊑κᵀ
-- primitive addition
compile-preserves-term-imprecision-typed srcΓ-wf tgtΓ-wf
    prim@(GTI.⊕⊑⊕ᴳ {op = addℕ} L⊑L′ A~ℕ A′~ℕ
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
  {!!}

compile-preserves-term-imprecision :
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ ctxImpToNu γ ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
compile-preserves-term-imprecision srcΓ-wf tgtΓ-wf M⊑M′ =
  compile-preserves-term-imprecision-typed
    srcΓ-wf
    tgtΓ-wf
    M⊑M′
