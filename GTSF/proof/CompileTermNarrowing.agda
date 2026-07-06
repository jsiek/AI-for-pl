module proof.CompileTermNarrowing where

-- File Charter:
--   * Compile monotonicity for source-level gradual term narrowing.
--   * States that compiling two source terms related by
--     `GradualTermNarrowing` yields target terms related by
--     `MediatedNarrowing`.
--   * The easy structural cases are proved directly.  The remaining
--     compiler-specific cases are named postulate boundaries isolating the
--     needed cast-plan composition and type-application/ν algebra.

open import Data.List using ([]; _∷_; map)
open import Data.Nat using (suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; subst; sym)

open import Types
open import Ctx using (CtxWf; ctxWf-∷)
open import Compile using (compile; compile-value)
open import NuTerms
  using (Term)
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
  ; id-‵
  ; _∣_⊢_∶ᶜ_⊒_
  ; fun-narrow-domain-dualᶜ
  )
open import Coercions using (Coercion; id; _↦_; cast-id)
open import Primitives using (Const; Prim; κℕ; constTy)
open import proof.NuTermProperties using (CtxWf-⤊)
open import StoreCorrespondence using (SealCorr; ⇑ᶜorr)
open import TermNarrowingSeparated using
  ( CtxCorr
  ; CtxCorrEntry
  ; ctx-entry
  ; leftCtx
  ; rightCtx
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
    ; _∣_∣_⊢_∶ᶜ_⊒ᵐ_
    ; fun-narrow-domain-dualᵐᶜ
    ; x⊒xᵗ
    ; ƛ⊒ƛᵗ
    ; Λ⊒Λᵗ
    ; κ⊒κᵗ
    )

ctxNrwToCorrEntry : CtxNrwEntry → CtxCorrEntry
ctxNrwToCorrEntry (ctx-nrw A B p) = ctx-entry A B p

ctxNrwToCorr : CtxNrw → CtxCorr
ctxNrwToCorr = map ctxNrwToCorrEntry

leftCtx-ctxNrwToCorr : ∀ γ → leftCtx (ctxNrwToCorr γ) ≡ srcCtxⁿ γ
leftCtx-ctxNrwToCorr [] = refl
leftCtx-ctxNrwToCorr (ctx-nrw A B p ∷ γ) =
  cong₂ _∷_ refl (leftCtx-ctxNrwToCorr γ)

rightCtx-ctxNrwToCorr : ∀ γ → rightCtx (ctxNrwToCorr γ) ≡ tgtCtxⁿ γ
rightCtx-ctxNrwToCorr [] = refl
rightCtx-ctxNrwToCorr (ctx-nrw A B p ∷ γ) =
  cong₂ _∷_ refl (rightCtx-ctxNrwToCorr γ)

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

    shiftᵐ :
      CompileIndexMediation (suc Δ) (⇑ᶜorr ρ)

open CompileIndexMediation

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

const-indexᶜ :
  ∀ {Δ} κ →
  Δ ∣ [] ⊢ id (constTy κ) ∶ᶜ constTy κ ⊒ constTy κ
const-indexᶜ (κℕ n) = cast-id wfBase refl , cross (id-‵ `ℕ)

-- These are the remaining compiler-specific proof obligations from issue #58.
-- They are stated over `MediatedNarrowing`, not the obsolete shared-store
-- `TermNarrowing` relation.
postulate
  compile-preserves-application-narrowing :
    ∀ {Δ ρ γ L L′ R R′ p A B ℓ} →
    (med : CompileIndexMediation Δ ρ) →
    (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
    (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
    (LR⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ L ·[ ℓ ] R ⦂ A) →
    (L′R′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ L′ ·[ ℓ ] R′ ⦂ B) →
    (LR⊒L′R′ : Δ ∣ [] ∣ γ ⊢ᴳ L ·[ ℓ ] R ⊒ L′ ·[ ℓ ] R′
                  ∶ p ⦂ A ⊒ B) →
    let
      N = proj₁ (compile srcΓ-wf LR⊢)
      N′ = proj₁ (compile tgtΓ-wf L′R′⊢)
    in
    Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B

  compile-preserves-target-forall-narrowing :
    ∀ {Δ ρ γ N V′ p A B} →
    (med : CompileIndexMediation Δ ρ) →
    (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
    (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
    (N⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ N ⦂ A) →
    (ΛV′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ Λ V′ ⦂ B) →
    (N⊒ΛV′ : Δ ∣ [] ∣ γ ⊢ᴳ N ⊒ Λ V′ ∶ p ⦂ A ⊒ B) →
    let
      L = proj₁ (compile srcΓ-wf N⊢)
      L′ = proj₁ (compile tgtΓ-wf ΛV′⊢)
    in
    Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ L ⊒ L′ ∶ p ⦂ A ⊒ᵐ B

  compile-preserves-type-application-narrowing :
    ∀ {Δ ρ γ M M′ T T′ p A B} →
    (med : CompileIndexMediation Δ ρ) →
    (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
    (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
    (MT⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ M `[ T ] ⦂ A) →
    (M′T′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ M′ `[ T′ ] ⦂ B) →
    (MT⊒M′T′ : Δ ∣ [] ∣ γ ⊢ᴳ M `[ T ] ⊒ M′ `[ T′ ]
                  ∶ p ⦂ A ⊒ B) →
    let
      N = proj₁ (compile srcΓ-wf MT⊢)
      N′ = proj₁ (compile tgtΓ-wf M′T′⊢)
    in
    Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B

  compile-preserves-target-type-application-narrowing :
    ∀ {Δ ρ γ M M′ T′ p A B} →
    (med : CompileIndexMediation Δ ρ) →
    (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
    (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
    (M⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ M ⦂ A) →
    (M′T′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ M′ `[ T′ ] ⦂ B) →
    (M⊒M′T′ : Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ `[ T′ ] ∶ p ⦂ A ⊒ B) →
    let
      N = proj₁ (compile srcΓ-wf M⊢)
      N′ = proj₁ (compile tgtΓ-wf M′T′⊢)
    in
    Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B

  compile-preserves-primitive-narrowing :
    ∀ {Δ ρ γ L L′ R R′ p A B op ℓ} →
    (med : CompileIndexMediation Δ ρ) →
    (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
    (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
    (LR⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ L ⊕[ op at ℓ ] R ⦂ A) →
    (L′R′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ L′ ⊕[ op at ℓ ] R′ ⦂ B) →
    (LR⊒L′R′ : Δ ∣ [] ∣ γ ⊢ᴳ L ⊕[ op at ℓ ] R ⊒
                  L′ ⊕[ op at ℓ ] R′ ∶ p ⦂ A ⊒ B) →
    let
      N = proj₁ (compile srcΓ-wf LR⊢)
      N′ = proj₁ (compile tgtΓ-wf L′R′⊢)
    in
    Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B

variable
  Δ : TyCtx
  ρ : SealCorr
  γ : CtxNrw
  A B : Ty
  p : Coercion
  M M′ : GTerm

compile-preserves-term-narrowing-typed :
  (med : CompileIndexMediation Δ ρ) →
  (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
  (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
  (M⊢ : Δ ∣ srcCtxⁿ γ ⊢ᴳ M ⦂ A) →
  (M′⊢ : Δ ∣ tgtCtxⁿ γ ⊢ᴳ M′ ⦂ B) →
  (M⊒M′ : Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B) →
  let
    N = proj₁ (compile srcΓ-wf M⊢)
    N′ = proj₁ (compile tgtΓ-wf M′⊢)
  in
  Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ (x⊒xᴳ pᶜ x∋p)
    with M⊢ | M′⊢
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    _ _ (x⊒xᴳ pᶜ x∋p) | ⊢ᴳ` x∈ˢ | ⊢ᴳ` x∈ᵗ =
  x⊒xᵗ (indexᵐᶜ med pᶜ) (ctxNrwToCorr-∋ x∋p)
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ (κ⊒κᴳ κ)
    with M⊢ | M′⊢
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    _ _ (κ⊒κᴳ κ) | ⊢ᴳ$ .κ | ⊢ᴳ$ .κ =
  κ⊒κᵗ κ (indexᵐᶜ med (const-indexᶜ κ))
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ (ƛ⊒ƛᴳ {p = p} {q = q} {A = A} {A′ = A′}
      {B = B} {B′ = B′} p↦qᶜ N⊒N′)
    with M⊢ | M′⊢
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    _ _
    (ƛ⊒ƛᴳ {p = p} {q = q} {A = A} {A′ = A′} {B = B} {B′ = B′}
      p↦qᶜ N⊒N′)
    | ⊢ᴳƛ wfA N⊢ | ⊢ᴳƛ wfA′ N′⊢ =
  ƛ⊒ƛᵗ {p = p} {q = q}
    {A = A} {A′ = A′} {B = B} {B′ = B′}
    (indexᵐᶜ med p↦qᶜ)
    (mediated-narrowing-context-cong
      (cong (λ c → ctx-entry A A′ c ∷ ctxNrwToCorr _)
        (sym (fun-domain-dualᵐᶜ med p↦qᶜ)))
      (compile-preserves-term-narrowing-typed med
        (ctxWf-∷ wfA srcΓ-wf)
        (ctxWf-∷ wfA′ tgtΓ-wf)
        N⊢
        N′⊢
        N⊒N′))
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ (Λ⊒Λᴳ allᶜ vVₙ vV′ₙ V⊒V′)
    with M⊢ | M′⊢
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    _ _ (Λ⊒Λᴳ allᶜ vVₙ vV′ₙ V⊒V′)
    | ⊢ᴳΛ vV V⊢ | ⊢ᴳΛ vV′ V′⊢ =
  Λ⊒Λᵗ
    (indexᵐᶜ med allᶜ)
    (compile-value (CtxWf-⤊ srcΓ-wf) vV V⊢)
    (compile-value (CtxWf-⤊ tgtΓ-wf) vV′ V′⊢)
    (mediated-narrowing-cong-terms
      (compile-context-subst-term
        (sym (srcCtxⁿ-⇑ᵍ _)) (CtxWf-⤊ srcΓ-wf) V⊢)
      (compile-context-subst-term
        (sym (tgtCtxⁿ-⇑ᵍ _)) (CtxWf-⤊ tgtΓ-wf) V′⊢)
      (mediated-narrowing-context-cong
        (ctxNrwToCorr-⇑ _)
        (compile-preserves-term-narrowing-typed (shiftᵐ med)
          (subst (CtxWf _) (sym (srcCtxⁿ-⇑ᵍ _)) (CtxWf-⤊ srcΓ-wf))
          (subst (CtxWf _) (sym (tgtCtxⁿ-⇑ᵍ _)) (CtxWf-⤊ tgtΓ-wf))
          (subst (λ Γ₀ → _ ∣ Γ₀ ⊢ᴳ _ ⦂ _) (sym (srcCtxⁿ-⇑ᵍ _)) V⊢)
          (subst (λ Γ₀ → _ ∣ Γ₀ ⊢ᴳ _ ⦂ _) (sym (tgtCtxⁿ-⇑ᵍ _)) V′⊢)
          V⊒V′)))
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ app@(·⊒·ᴳ p↦qᶜ L⊒L′ N⊒N′) =
  compile-preserves-application-narrowing med srcΓ-wf tgtΓ-wf M⊢ M′⊢ app
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ rel@(⊒Λᴳ pᶜ vV′ N⊒V′) =
  compile-preserves-target-forall-narrowing med srcΓ-wf tgtΓ-wf M⊢ M′⊢ rel
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ rel@([]⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  compile-preserves-type-application-narrowing med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ rel
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ rel@(⊒[]ᴳ M⊒M′ qᶜ rᶜ) =
  compile-preserves-target-type-application-narrowing med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ rel
compile-preserves-term-narrowing-typed med srcΓ-wf tgtΓ-wf
    M⊢ M′⊢ prim@(⊕⊒⊕ᴳ M⊒M′ N⊒N′) =
  compile-preserves-primitive-narrowing med srcΓ-wf tgtΓ-wf M⊢ M′⊢ prim

compile-preserves-term-narrowing :
  (med : CompileIndexMediation Δ ρ) →
  (srcΓ-wf : CtxWf Δ (srcCtxⁿ γ)) →
  (tgtΓ-wf : CtxWf Δ (tgtCtxⁿ γ)) →
  (M⊒M′ : Δ ∣ [] ∣ γ ⊢ᴳ M ⊒ M′ ∶ p ⦂ A ⊒ B) →
  let
    M⊢ = gradual-term-narrowing-source-typing M⊒M′
    M′⊢ = gradual-term-narrowing-target-typing M⊒M′
    N = proj₁ (compile srcΓ-wf M⊢)
    N′ = proj₁ (compile tgtΓ-wf M′⊢)
  in
  Δ ∣ Δ ∣ ρ ∣ ctxNrwToCorr γ ⊢ N ⊒ N′ ∶ p ⦂ A ⊒ᵐ B
compile-preserves-term-narrowing med srcΓ-wf tgtΓ-wf M⊒M′ =
  compile-preserves-term-narrowing-typed
    med
    srcΓ-wf
    tgtΓ-wf
    (gradual-term-narrowing-source-typing M⊒M′)
    (gradual-term-narrowing-target-typing M⊒M′)
    M⊒M′
