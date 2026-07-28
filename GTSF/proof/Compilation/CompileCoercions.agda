module proof.Compilation.CompileCoercions where

-- File Charter:
--   * Coercion synthesis for the GTSF compiler.
--   * Defines realization of imprecision-assumption contexts by target-store
--     coercions, plus `coerce-up` and `coerce-down` for type-imprecision
--     proofs.
--   * Specialized indexed synthesis retains the hereditary cast shape needed
--     to connect compiled casts to quotient term imprecision.
--   * This file deliberately does not choose maximal lower bounds; it only
--     turns a chosen imprecision witness into typed target coercions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import Types
open import Store using (StoreIncl; StoreIncl-drop)
open import Coercions
  using
    ( Coercion
    ; ModeEnv
    ; id-only
    ; tag-or-id
    ; seal-or-id
    ; id-onlyᵈ
    ; tag-or-idᵈ
    ; extᵈ
    ; genᵈ
    ; instᵈ
    ; _∣_∣_⊢_∶_=⇒_
    ; _∣_⊢_∶_=⇒_
    ; idTyAllowed
    ; cast-id
    ; cast-seq
    ; cast-tag
    ; cast-untag
    ; cast-fun
    ; cast-all
    ; cast-seal
    ; cast-unseal
    ; cast-inst
    ; cast-gen
    )
  renaming
    ( id to idᶜ
    ; _︔_ to _︔ᶜ_
    ; _↦_ to _↦ᶜ_
    ; `∀ to `∀ᶜ
    ; _! to _!ᶜ
    ; _？ to _？ᶜ
    ; seal to sealᶜ
    ; unseal to unsealᶜ
    ; inst to instᶜ
    ; gen to genᶜ
    )
open import Imprecision
open import ImprecisionWf
  using (_∣_⊢_⊑_⊣_)
  renaming
    ( id★ to id★ᵢ
    ; idˣ to idˣᵢ
    ; idι to idιᵢ
    ; _↦_ to _↦ᵢ_
    ; ∀ⁱ_ to ∀ⁱᵢ_
    ; tag_ to tagᵢ_
    ; tag_⇛_ to tagᵢ_⇛_
    ; tagˣ to tagˣᵢ
    ; ν to νᵢ
    ; ⊑-src-wf to ⊑-src-wfᵢ
    ; ⊑-tgt-wf to ⊑-tgt-wfᵢ
    )
import NarrowWiden as NW
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NarrowWidenComposition using
  (widening-at-instSafe-target)
open import CastImprecisionShape using
  ( _⊢ᶜ_⦂_
  ; narrowing
  ; widening
  ; shape-id-var
  ; shape-id-base
  ; shape-id-star
  ; shape-fun
  ; shape-all
  ; shape-tag-var
  ; shape-tag-base
  ; shape-tag-fun
  ; shape-untag-var
  ; shape-untag-base
  ; shape-untag-fun
  ; shape-seal
  ; shape-unseal
  ; shape-gen
  ; shape-inst
  ; shape-sequence-widening
  ; shape-sequence-narrowing
  )
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; id★ˢ
  ; idˣˢ
  ; tagˣˢ
  ; _↦ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  ; comp-↦-tag
  ; comp-ν
  ; _；_≋_
  )
open import proof.Compilation.GenSafeProperties using
  ( GenSafeShape
  ; shape-fun
  ; shape-all
  ; raise-genSafeShape
  ; narrowing-at-genSafe-source
  )
open import proof.Core.Properties.CoercionProperties
  using
    ( ModeRename
    ; coercion-renameᵗᵐ
    ; coercion-weakenᵐ
    ; modeRename-idTyAllowed
    )
open import proof.Core.Properties.TypeProperties
  using (TyRenameWf-suc; renameᵗ-id; renameᵗ-preserves-WfTy)
open import proof.Core.Properties.ImprecisionCompositionProperties using
  (compose-target-star-right-id★)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-rename; shape-rename; shape-subst-source)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  ( ⊑-forgetᵢ
  ; ⊑-target-liftνᵢ
  ; rename-assm²-⇑ᴸ-to-⇑ᵢ
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (⊑-renameᵗ²ᵢ)

------------------------------------------------------------------------
-- Realizing imprecision assumptions as target coercions
------------------------------------------------------------------------

ModeRename-suc-ext :
  ∀ {μ} →
  ModeRename suc μ (extᵈ μ)
ModeRename-suc-ext {μ} X with μ X
ModeRename-suc-ext X | id-only = refl
ModeRename-suc-ext X | tag-or-id = refl
ModeRename-suc-ext X | seal-or-id = refl

ModeRename-suc-gen :
  ∀ {μ} →
  ModeRename suc μ (genᵈ μ)
ModeRename-suc-gen {μ} X with μ X
ModeRename-suc-gen X | id-only = refl
ModeRename-suc-gen X | tag-or-id = refl
ModeRename-suc-gen X | seal-or-id = refl

ModeRename-suc-inst :
  ∀ {μ} →
  ModeRename suc μ (instᵈ μ)
ModeRename-suc-inst {μ} X with μ X
ModeRename-suc-inst X | id-only = refl
ModeRename-suc-inst X | tag-or-id = refl
ModeRename-suc-inst X | seal-or-id = refl

ModeRename-suc-id-only :
  ModeRename suc id-onlyᵈ id-onlyᵈ
ModeRename-suc-id-only X = refl

ModeRename-suc-tag-or-id :
  ModeRename suc tag-or-idᵈ tag-or-idᵈ
ModeRename-suc-tag-or-id X = refl

AllIdMode : ModeEnv → Set
AllIdMode μ = ∀ X → μ X ≡ id-only

AllIdMode-ext :
  ∀ {μ} →
  AllIdMode μ →
  AllIdMode (extᵈ μ)
AllIdMode-ext all-id zero = refl
AllIdMode-ext all-id (suc X) = all-id X

idTyAllowed-all-id :
  ∀ {μ A} →
  AllIdMode μ →
  idTyAllowed μ A ≡ true
idTyAllowed-all-id {A = ＇ α} all-id rewrite all-id α = refl
idTyAllowed-all-id {A = ‵ ι} all-id = refl
idTyAllowed-all-id {A = ★} all-id = refl
idTyAllowed-all-id {A = A ⇒ B} all-id
    rewrite idTyAllowed-all-id {A = A} all-id
          | idTyAllowed-all-id {A = B} all-id =
  refl
idTyAllowed-all-id {A = `∀ A} all-id =
  idTyAllowed-all-id {A = A} (AllIdMode-ext all-id)

idTyAllowed-id-only :
  ∀ A →
  idTyAllowed id-onlyᵈ A ≡ true
idTyAllowed-id-only A = idTyAllowed-all-id {A = A} (λ X → refl)

idTyAllowed-shift-gen :
  ∀ {μ B} →
  idTyAllowed μ B ≡ true →
  idTyAllowed (genᵈ μ) (⇑ᵗ B) ≡ true
idTyAllowed-shift-gen {μ = μ} {B = B} ok =
  modeRename-idTyAllowed {ρ = suc} {μ = μ} {ν = genᵈ μ} {A = B}
    ModeRename-suc-gen ok

idTyAllowed-shift-inst :
  ∀ {μ B} →
  idTyAllowed μ B ≡ true →
  idTyAllowed (instᵈ μ) (⇑ᵗ B) ≡ true
idTyAllowed-shift-inst {μ = μ} {B = B} ok =
  modeRename-idTyAllowed {ρ = suc} {μ = μ} {ν = instᵈ μ} {A = B}
    ModeRename-suc-inst ok

data Realizesᵐ (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) : ImpCtx → Set₁ where
  real-[] :
    Realizesᵐ μ Δ Σ []

  real-xx : ∀ {Φ X Y c d} →
    WfTy Δ (＇ X) →
    WfTy Δ (＇ Y) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ＇ Y →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ＇ Y =⇒ ＇ X →
    Realizesᵐ μ Δ Σ Φ →
    Realizesᵐ μ Δ Σ ((X ˣ⊑ˣ Y) ∷ Φ)

  real-star : ∀ {Φ X c d} →
    WfTy Δ (＇ X) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ★ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ★ =⇒ ＇ X →
    Realizesᵐ μ Δ Σ Φ →
    Realizesᵐ μ Δ Σ ((X ˣ⊑★) ∷ Φ)

Realizes : TyCtx → Store → ImpCtx → Set₁
Realizes Δ Σ Φ = Realizesᵐ id-onlyᵈ Δ Σ Φ

realizes-xx-up :
  ∀ {μ Δ Σ Φ X Y} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ＇ Y
realizes-xx-up (real-xx hX hY c⊢ d⊢ r) (here refl) = _ , c⊢
realizes-xx-up (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-xx-up r x∈
realizes-xx-up (real-star hX c⊢ d⊢ r) (here ())
realizes-xx-up (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-xx-up r x∈

realizes-xx-down :
  ∀ {μ Δ Σ Φ X Y} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ Y =⇒ ＇ X
realizes-xx-down (real-xx hX hY c⊢ d⊢ r) (here refl) = _ , d⊢
realizes-xx-down (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-xx-down r x∈
realizes-xx-down (real-star hX c⊢ d⊢ r) (here ())
realizes-xx-down (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-xx-down r x∈

realizes-star-up :
  ∀ {μ Δ Σ Φ X} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ★
realizes-star-up (real-xx hX hY c⊢ d⊢ r) (here ())
realizes-star-up (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-star-up r x∈
realizes-star-up (real-star hX c⊢ d⊢ r) (here refl) = _ , c⊢
realizes-star-up (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-star-up r x∈

realizes-star-down :
  ∀ {μ Δ Σ Φ X} →
  Realizesᵐ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ★ =⇒ ＇ X
realizes-star-down (real-xx hX hY c⊢ d⊢ r) (here ())
realizes-star-down (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-star-down r x∈
realizes-star-down (real-star hX c⊢ d⊢ r) (here refl) = _ , d⊢
realizes-star-down (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-star-down r x∈

Realizes-store-weaken :
  ∀ {μ Δ Σ Σ′ Φ} →
  StoreIncl Σ Σ′ →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ μ Δ Σ′ Φ
Realizes-store-weaken incl real-[] = real-[]
Realizes-store-weaken incl (real-xx hX hY c⊢ d⊢ r) =
  real-xx
    hX
    hY
    (coercion-weakenᵐ ≤-refl incl c⊢)
    (coercion-weakenᵐ ≤-refl incl d⊢)
    (Realizes-store-weaken incl r)
Realizes-store-weaken incl (real-star hX c⊢ d⊢ r) =
  real-star
    hX
    (coercion-weakenᵐ ≤-refl incl c⊢)
    (coercion-weakenᵐ ≤-refl incl d⊢)
    (Realizes-store-weaken incl r)

Realizes-rename-suc :
  ∀ {μ ν Δ Σ Φ} →
  ModeRename suc μ ν →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ ν (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
Realizes-rename-suc rel real-[] = real-[]
Realizes-rename-suc rel (real-xx hX hY c⊢ d⊢ r) =
  real-xx
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hY TyRenameWf-suc)
    (coercion-renameᵗᵐ TyRenameWf-suc rel c⊢)
    (coercion-renameᵗᵐ TyRenameWf-suc rel d⊢)
    (Realizes-rename-suc rel r)
Realizes-rename-suc rel (real-star hX c⊢ d⊢ r) =
  real-star
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (coercion-renameᵗᵐ TyRenameWf-suc rel c⊢)
    (coercion-renameᵗᵐ TyRenameWf-suc rel d⊢)
    (Realizes-rename-suc rel r)

Realizes-⇑ᵢ :
  ∀ {μ Δ Σ Φ} →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (extᵈ μ) (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
Realizes-⇑ᵢ = Realizes-rename-suc ModeRename-suc-ext

Realizes-∀ⁱ :
  ∀ {μ Δ Σ Φ} →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
Realizes-∀ⁱ r =
  real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl)
    (cast-id (wfVar z<s) refl)
    (Realizes-⇑ᵢ r)

Realizes-ν-inst :
  ∀ {μ Δ Σ Φ} →
  (ℓ : Label) →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (instᵈ μ) (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ)
    ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
Realizes-ν-inst ℓ r =
  real-star
    (wfVar z<s)
    (cast-unseal wf★ (here refl) refl)
    (cast-seal wf★ (here refl) refl)
    (Realizes-store-weaken StoreIncl-drop
      (Realizes-rename-suc ModeRename-suc-inst r))

Realizes-ν-gen :
  ∀ {μ Δ Σ Φ} →
  (ℓ : Label) →
  Realizesᵐ μ Δ Σ Φ →
  Realizesᵐ (genᵈ μ) (suc Δ) (⟰ᵗ Σ) ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
Realizes-ν-gen ℓ r =
  real-star
    (wfVar z<s)
    (cast-tag (wfVar z<s) (＇ zero) refl)
    (cast-untag (wfVar z<s) (＇ zero) refl)
    (Realizes-rename-suc ModeRename-suc-gen r)

realizes-idᵢ :
  ∀ Δ →
  Realizes Δ [] (idᵢ Δ)
realizes-idᵢ zero = real-[]
realizes-idᵢ (suc Δ) =
  real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) (idTyAllowed-id-only (＇ zero)))
    (cast-id (wfVar z<s) (idTyAllowed-id-only (＇ zero)))
    (Realizes-rename-suc ModeRename-suc-id-only (realizes-idᵢ Δ))

------------------------------------------------------------------------
-- Realizing imprecision assumptions as canonical narrowing/widening casts
------------------------------------------------------------------------

idTyAllowed-true : (μ : ModeEnv) → (A : Ty) → idTyAllowed μ A ≡ true
idTyAllowed-true μ (＇ α) with μ α
idTyAllowed-true μ (＇ α) | id-only = refl
idTyAllowed-true μ (＇ α) | tag-or-id = refl
idTyAllowed-true μ (＇ α) | seal-or-id = refl
idTyAllowed-true μ (‵ ι) = refl
idTyAllowed-true μ ★ = refl
idTyAllowed-true μ (A ⇒ B)
    rewrite idTyAllowed-true μ A | idTyAllowed-true μ B =
  refl
idTyAllowed-true μ (`∀ A) = idTyAllowed-true (extᵈ μ) A

data Realizesᴺᵂ (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) :
    ImpCtx → Set₁ where
  realᵂⁿ-[] :
    Realizesᴺᵂ μ Δ Σ []

  realᵂⁿ-xx : ∀ {Φ X Y c d} →
    WfTy Δ (＇ X) →
    WfTy Δ (＇ Y) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ＇ Y →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ＇ Y ⊒ ＇ X →
    Realizesᴺᵂ μ Δ Σ Φ →
    Realizesᴺᵂ μ Δ Σ ((X ˣ⊑ˣ Y) ∷ Φ)

  realᵂⁿ-star : ∀ {Φ X c d} →
    WfTy Δ (＇ X) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ★ →
    NW.StrictWidening c →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ★ ⊒ ＇ X →
    NW.StrictNarrowing d →
    Realizesᴺᵂ μ Δ Σ Φ →
    Realizesᴺᵂ μ Δ Σ ((X ˣ⊑★) ∷ Φ)

realizes-xx-upʷ :
  ∀ {μ Δ Σ Φ X Y} →
  Realizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ＇ Y
realizes-xx-upʷ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (here refl) = _ , c⊑
realizes-xx-upʷ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-xx-upʷ r x∈
realizes-xx-upʷ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (here ())
realizes-xx-upʷ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (there x∈) =
  realizes-xx-upʷ r x∈

realizes-xx-downⁿ :
  ∀ {μ Δ Σ Φ X Y} →
  Realizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ Y ⊒ ＇ X
realizes-xx-downⁿ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (here refl) = _ , d⊒
realizes-xx-downⁿ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-xx-downⁿ r x∈
realizes-xx-downⁿ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (here ())
realizes-xx-downⁿ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (there x∈) =
  realizes-xx-downⁿ r x∈

realizes-star-upʷ :
  ∀ {μ Δ Σ Φ X} →
  Realizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ]
    (μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ★) × NW.StrictWidening c
realizes-star-upʷ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (here ())
realizes-star-upʷ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-star-upʷ r x∈
realizes-star-upʷ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (here refl) =
  _ , c⊑ , cˢ
realizes-star-upʷ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (there x∈) =
  realizes-star-upʷ r x∈

realizes-star-downⁿ :
  ∀ {μ Δ Σ Φ X} →
  Realizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ]
    (μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ ＇ X) × NW.StrictNarrowing c
realizes-star-downⁿ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (here ())
realizes-star-downⁿ (realᵂⁿ-xx hX hY c⊑ d⊒ r) (there x∈) =
  realizes-star-downⁿ r x∈
realizes-star-downⁿ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (here refl) =
  _ , d⊒ , dˢ
realizes-star-downⁿ (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) (there x∈) =
  realizes-star-downⁿ r x∈

Realizesᴺᵂ-store-weaken :
  ∀ {μ Δ Σ Σ′ Φ} →
  StoreIncl Σ Σ′ →
  Realizesᴺᵂ μ Δ Σ Φ →
  Realizesᴺᵂ μ Δ Σ′ Φ
Realizesᴺᵂ-store-weaken incl realᵂⁿ-[] = realᵂⁿ-[]
Realizesᴺᵂ-store-weaken incl (realᵂⁿ-xx hX hY c⊑ d⊒ r) =
  realᵂⁿ-xx hX hY
    (NW.widen-weaken ≤-refl incl c⊑)
    (NW.narrow-weaken ≤-refl incl d⊒)
    (Realizesᴺᵂ-store-weaken incl r)
Realizesᴺᵂ-store-weaken incl
    (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) =
  realᵂⁿ-star hX
    (NW.widen-weaken ≤-refl incl c⊑)
    cˢ
    (NW.narrow-weaken ≤-refl incl d⊒)
    dˢ
    (Realizesᴺᵂ-store-weaken incl r)

Realizesᴺᵂ-rename-suc :
  ∀ {μ ν Δ Σ Φ} →
  ModeRename suc μ ν →
  Realizesᴺᵂ μ Δ Σ Φ →
  Realizesᴺᵂ ν (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
Realizesᴺᵂ-rename-suc rel realᵂⁿ-[] = realᵂⁿ-[]
Realizesᴺᵂ-rename-suc rel (realᵂⁿ-xx hX hY c⊑ d⊒ r) =
  realᵂⁿ-xx
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hY TyRenameWf-suc)
    (NW.widen-renameᵗ TyRenameWf-suc rel c⊑)
    (NW.narrow-renameᵗ TyRenameWf-suc rel d⊒)
    (Realizesᴺᵂ-rename-suc rel r)
Realizesᴺᵂ-rename-suc rel (realᵂⁿ-star hX c⊑ cˢ d⊒ dˢ r) =
  realᵂⁿ-star
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (NW.widen-renameᵗ TyRenameWf-suc rel c⊑)
    (NW.renameStrictʷ suc cˢ)
    (NW.narrow-renameᵗ TyRenameWf-suc rel d⊒)
    (NW.renameStrictⁿ suc dˢ)
    (Realizesᴺᵂ-rename-suc rel r)

Realizesᴺᵂ-⇑ᵢ :
  ∀ {μ Δ Σ Φ} →
  Realizesᴺᵂ μ Δ Σ Φ →
  Realizesᴺᵂ (extᵈ μ) (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
Realizesᴺᵂ-⇑ᵢ = Realizesᴺᵂ-rename-suc ModeRename-suc-ext

Realizesᴺᵂ-∀ⁱ :
  ∀ {μ Δ Σ Φ} →
  Realizesᴺᵂ μ Δ Σ Φ →
  Realizesᴺᵂ (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
Realizesᴺᵂ-∀ⁱ r =
  realᵂⁿ-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    (Realizesᴺᵂ-⇑ᵢ r)

Realizesᴺᵂ-ν-inst :
  ∀ {μ Δ Σ Φ} →
  Realizesᴺᵂ μ Δ Σ Φ →
  Realizesᴺᵂ (instᵈ μ) (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ)
    ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
Realizesᴺᵂ-ν-inst r =
  realᵂⁿ-star
    (wfVar z<s)
    (cast-unseal wf★ (here refl) refl , NW.unsealʷ zero ★)
    (NW.strict-unseal zero ★)
    (cast-seal wf★ (here refl) refl , NW.sealⁿ ★ zero)
    (NW.strict-seal ★ zero)
    (Realizesᴺᵂ-store-weaken StoreIncl-drop
      (Realizesᴺᵂ-rename-suc ModeRename-suc-inst r))

Realizesᴺᵂ-ν-gen :
  ∀ {μ Δ Σ Φ} →
  Realizesᴺᵂ μ Δ Σ Φ →
  Realizesᴺᵂ (genᵈ μ) (suc Δ) (⟰ᵗ Σ) ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
Realizesᴺᵂ-ν-gen r =
  realᵂⁿ-star
    (wfVar z<s)
    (cast-tag (wfVar z<s) (＇ zero) refl , NW.tag (＇ zero))
    (NW.strict-tag (＇ zero))
    (cast-untag (wfVar z<s) (＇ zero) refl , NW.untag (＇ zero))
    (NW.strict-untag (＇ zero))
    (Realizesᴺᵂ-rename-suc ModeRename-suc-gen r)

realizes-idᵢᴺᵂ :
  ∀ Δ →
  Realizesᴺᵂ tag-or-idᵈ Δ [] (idᵢ Δ)
realizes-idᵢᴺᵂ zero = realᵂⁿ-[]
realizes-idᵢᴺᵂ (suc Δ) =
  realᵂⁿ-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    (Realizesᴺᵂ-rename-suc ModeRename-suc-tag-or-id
      (realizes-idᵢᴺᵂ Δ))

realizes-idᵢᴺᵂ-id-only :
  ∀ Δ →
  Realizesᴺᵂ id-onlyᵈ Δ [] (idᵢ Δ)
realizes-idᵢᴺᵂ-id-only zero = realᵂⁿ-[]
realizes-idᵢᴺᵂ-id-only (suc Δ) =
  realᵂⁿ-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    (Realizesᴺᵂ-rename-suc ModeRename-suc-id-only
      (realizes-idᵢᴺᵂ-id-only Δ))

------------------------------------------------------------------------
-- Hereditary shapes for realized imprecision assumptions
------------------------------------------------------------------------

data ShapeRealizesᴺᵂ (μ : ModeEnv) (Δ : TyCtx) (Σ : Store) :
    ImpCtx → Set₁ where
  shape-real-[] :
    ShapeRealizesᴺᵂ μ Δ Σ []

  shape-real-xx : ∀ {Φ X Y c d} →
    WfTy Δ (＇ X) →
    WfTy Δ (＇ Y) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ＇ Y →
    widening ⊢ᶜ c ⦂ idˣˢ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ＇ Y ⊒ ＇ X →
    narrowing ⊢ᶜ d ⦂ idˣˢ →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    ShapeRealizesᴺᵂ μ Δ Σ ((X ˣ⊑ˣ Y) ∷ Φ)

  shape-real-star : ∀ {Φ X c d} →
    WfTy Δ (＇ X) →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ★ →
    NW.StrictWidening c →
    widening ⊢ᶜ c ⦂ tagˣˢ →
    μ ∣ Δ ∣ Σ ⊢ d ∶ ★ ⊒ ＇ X →
    NW.StrictNarrowing d →
    narrowing ⊢ᶜ d ⦂ tagˣˢ →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    ShapeRealizesᴺᵂ μ Δ Σ ((X ˣ⊑★) ∷ Φ)

realizes-shape-xx-up :
  ∀ {μ Δ Σ Φ X Y} →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ]
    (μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ＇ Y) ×
    (widening ⊢ᶜ c ⦂ idˣˢ)
realizes-shape-xx-up
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (here refl) =
  _ , c⊑ , c-shape
realizes-shape-xx-up
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (there x∈) =
  realizes-shape-xx-up shapes x∈
realizes-shape-xx-up
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (here ())
realizes-shape-xx-up
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (there x∈) =
  realizes-shape-xx-up shapes x∈

realizes-shape-xx-down :
  ∀ {μ Δ Σ Φ X Y} →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ]
    (μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ Y ⊒ ＇ X) ×
    (narrowing ⊢ᶜ c ⦂ idˣˢ)
realizes-shape-xx-down
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (here refl) =
  _ , d⊒ , d-shape
realizes-shape-xx-down
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (there x∈) =
  realizes-shape-xx-down shapes x∈
realizes-shape-xx-down
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (here ())
realizes-shape-xx-down
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (there x∈) =
  realizes-shape-xx-down shapes x∈

realizes-shape-star-up :
  ∀ {μ Δ Σ Φ X} →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ]
    (μ ∣ Δ ∣ Σ ⊢ c ∶ ＇ X ⊑ ★) ×
    NW.StrictWidening c ×
    (widening ⊢ᶜ c ⦂ tagˣˢ)
realizes-shape-star-up
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (here ())
realizes-shape-star-up
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (there x∈) =
  realizes-shape-star-up shapes x∈
realizes-shape-star-up
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (here refl) =
  _ , c⊑ , cˢ , c-shape
realizes-shape-star-up
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (there x∈) =
  realizes-shape-star-up shapes x∈

realizes-shape-star-down :
  ∀ {μ Δ Σ Φ X} →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ]
    (μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ ＇ X) ×
    NW.StrictNarrowing c ×
    (narrowing ⊢ᶜ c ⦂ tagˣˢ)
realizes-shape-star-down
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (here ())
realizes-shape-star-down
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes)
    (there x∈) =
  realizes-shape-star-down shapes x∈
realizes-shape-star-down
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (here refl) =
  _ , d⊒ , dˢ , d-shape
realizes-shape-star-down
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes)
    (there x∈) =
  realizes-shape-star-down shapes x∈

ShapeRealizesᴺᵂ-store-weaken :
  ∀ {μ Δ Σ Σ′ Φ} →
  StoreIncl Σ Σ′ →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  ShapeRealizesᴺᵂ μ Δ Σ′ Φ
ShapeRealizesᴺᵂ-store-weaken incl shape-real-[] =
  shape-real-[]
ShapeRealizesᴺᵂ-store-weaken incl
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes) =
  shape-real-xx hX hY
    (NW.widen-weaken ≤-refl incl c⊑) c-shape
    (NW.narrow-weaken ≤-refl incl d⊒) d-shape
    (ShapeRealizesᴺᵂ-store-weaken incl shapes)
ShapeRealizesᴺᵂ-store-weaken incl
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes) =
  shape-real-star hX
    (NW.widen-weaken ≤-refl incl c⊑) cˢ c-shape
    (NW.narrow-weaken ≤-refl incl d⊒) dˢ d-shape
    (ShapeRealizesᴺᵂ-store-weaken incl shapes)

ShapeRealizesᴺᵂ-rename-suc :
  ∀ {μ ν Δ Σ Φ} →
  ModeRename suc μ ν →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  ShapeRealizesᴺᵂ ν (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
ShapeRealizesᴺᵂ-rename-suc rel shape-real-[] =
  shape-real-[]
ShapeRealizesᴺᵂ-rename-suc rel
    (shape-real-xx hX hY c⊑ c-shape d⊒ d-shape shapes) =
  shape-real-xx
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hY TyRenameWf-suc)
    (NW.widen-renameᵗ TyRenameWf-suc rel c⊑)
    (cast-shape-rename suc c-shape)
    (NW.narrow-renameᵗ TyRenameWf-suc rel d⊒)
    (cast-shape-rename suc d-shape)
    (ShapeRealizesᴺᵂ-rename-suc rel shapes)
ShapeRealizesᴺᵂ-rename-suc rel
    (shape-real-star hX c⊑ cˢ c-shape d⊒ dˢ d-shape shapes) =
  shape-real-star
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (NW.widen-renameᵗ TyRenameWf-suc rel c⊑)
    (NW.renameStrictʷ suc cˢ)
    (cast-shape-rename suc c-shape)
    (NW.narrow-renameᵗ TyRenameWf-suc rel d⊒)
    (NW.renameStrictⁿ suc dˢ)
    (cast-shape-rename suc d-shape)
    (ShapeRealizesᴺᵂ-rename-suc rel shapes)

ShapeRealizesᴺᵂ-∀ⁱ :
  ∀ {μ Δ Σ Φ} →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  ShapeRealizesᴺᵂ (extᵈ μ) (suc Δ) (⟰ᵗ Σ)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
ShapeRealizesᴺᵂ-∀ⁱ shapes =
  shape-real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    shape-id-var
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    shape-id-var
    (ShapeRealizesᴺᵂ-rename-suc ModeRename-suc-ext shapes)

ShapeRealizesᴺᵂ-ν-inst :
  ∀ {μ Δ Σ Φ} →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  ShapeRealizesᴺᵂ (instᵈ μ) (suc Δ)
    ((zero , ★) ∷ ⟰ᵗ Σ) ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
ShapeRealizesᴺᵂ-ν-inst shapes =
  shape-real-star
    (wfVar z<s)
    (cast-unseal wf★ (here refl) refl , NW.unsealʷ zero ★)
    (NW.strict-unseal zero ★)
    shape-unseal
    (cast-seal wf★ (here refl) refl , NW.sealⁿ ★ zero)
    (NW.strict-seal ★ zero)
    shape-seal
    (ShapeRealizesᴺᵂ-store-weaken StoreIncl-drop
      (ShapeRealizesᴺᵂ-rename-suc ModeRename-suc-inst shapes))

ShapeRealizesᴺᵂ-ν-gen :
  ∀ {μ Δ Σ Φ} →
  ShapeRealizesᴺᵂ μ Δ Σ Φ →
  ShapeRealizesᴺᵂ (genᵈ μ) (suc Δ) (⟰ᵗ Σ)
    ((zero ˣ⊑★) ∷ ⇑ᵢ Φ)
ShapeRealizesᴺᵂ-ν-gen shapes =
  shape-real-star
    (wfVar z<s)
    (cast-tag (wfVar z<s) (＇ zero) refl , NW.tag (＇ zero))
    (NW.strict-tag (＇ zero))
    shape-tag-var
    (cast-untag (wfVar z<s) (＇ zero) refl , NW.untag (＇ zero))
    (NW.strict-untag (＇ zero))
    shape-untag-var
    (ShapeRealizesᴺᵂ-rename-suc ModeRename-suc-gen shapes)

realizes-idᵢᴺᵂ-id-only-shapes :
  ∀ Δ →
  ShapeRealizesᴺᵂ id-onlyᵈ Δ [] (idᵢ Δ)
realizes-idᵢᴺᵂ-id-only-shapes zero =
  shape-real-[]
realizes-idᵢᴺᵂ-id-only-shapes (suc Δ) =
  shape-real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    shape-id-var
    (cast-id (wfVar z<s) refl , NW.cross (NW.id-＇ zero))
    shape-id-var
    (ShapeRealizesᴺᵂ-rename-suc ModeRename-suc-id-only
      (realizes-idᵢᴺᵂ-id-only-shapes Δ))

------------------------------------------------------------------------
-- Canonical narrowing/widening synthesis from imprecision
------------------------------------------------------------------------

data UpStarView {μ Δ Σ Φ} :
    Realizesᴺᵂ μ Δ Σ Φ →
    ∀ {A} → Φ ⊢ A ⊑ ★ → Set₁ where
  up★-id : ∀ {r} →
    UpStarView r id★

  up★-strict : ∀ {r A p c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ ★ →
    NW.StrictWidening c →
    UpStarView r {A = A} p

data DownStarView {μ Δ Σ Φ} :
    Realizesᴺᵂ μ Δ Σ Φ →
    ∀ {A} → Φ ⊢ A ⊑ ★ → Set₁ where
  down★-id : ∀ {r} →
    DownStarView r id★

  down★-strict : ∀ {r A p c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ A →
    NW.StrictNarrowing c →
    DownStarView r {A = A} p

data UpNuStarCore {μ Δ Σ Φ} :
    Realizesᴺᵂ μ Δ Σ Φ →
    ∀ {A} → Φ ⊢ A ⊑ ★ → Set₁ where
  upν★-core : ∀ {r A p c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ (★ ⇒ ★) →
    NW.InstSafe c →
    UpNuStarCore r {A = A} p

data DownNuStarCore {μ Δ Σ Φ} :
    Realizesᴺᵂ μ Δ Σ Φ →
    ∀ {A} → Φ ⊢ A ⊑ ★ → Set₁ where
  downν★-core : ∀ {r A p c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ (★ ⇒ ★) ⊒ A →
    NW.GenSafe c →
    DownNuStarCore r {A = A} p

nonVar-occurs-to-var⊥ :
  ∀ {Φ A X} →
  NonVar A →
  occurs zero A ≡ true →
  Φ ⊢ A ⊑ ＇ X →
  ⊥
nonVar-occurs-to-var⊥ nonvar-base () p
nonVar-occurs-to-var⊥ nonvar-star () p
nonVar-occurs-to-var⊥ nonvar-fun occ ()
nonVar-occurs-to-var⊥ nonvar-all occ (ν nonvar occ′ p) =
  nonVar-occurs-to-var⊥ nonvar occ′ p

nonVar-occurs-to-base⊥ :
  ∀ {Φ A ι} →
  NonVar A →
  occurs zero A ≡ true →
  Φ ⊢ A ⊑ ‵ ι →
  ⊥
nonVar-occurs-to-base⊥ nonvar-base () p
nonVar-occurs-to-base⊥ nonvar-star () p
nonVar-occurs-to-base⊥ nonvar-fun occ ()
nonVar-occurs-to-base⊥ nonvar-all occ (ν nonvar occ′ p) =
  nonVar-occurs-to-base⊥ nonvar occ′ p

nonVar-occurs→genSafeShape :
  ∀ {A} →
  NonVar A →
  occurs zero A ≡ true →
  GenSafeShape A
nonVar-occurs→genSafeShape nonvar-base ()
nonVar-occurs→genSafeShape nonvar-star ()
nonVar-occurs→genSafeShape nonvar-fun occ = shape-fun
nonVar-occurs→genSafeShape nonvar-all occ = shape-all

mutual
  coerce-upʷᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    Realizesᴺᵂ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊑ A
  coerce-upʷᵐ ℓ wf★ wf★ r id★ =
    idᶜ ★ , cast-id wf★ refl , NW.id★
  coerce-upʷᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY r (idˣ X⊑Y) =
    realizes-xx-upʷ r X⊑Y
  coerce-upʷᵐ {C = ‵ ι} ℓ wfBase wfBase r idι =
    idᶜ (‵ ι) , cast-id wfBase refl , NW.cross (NW.id-‵ ι)
  coerce-upʷᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      with coerce-downⁿᵐ ℓ hA hA′ r p
         | coerce-upʷᵐ ℓ hB hB′ r q
  coerce-upʷᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      | s , s⊒ | t , t⊑ =
    (s ↦ᶜ t) , cast-fun (proj₁ s⊒) (proj₁ t⊑) ,
    NW.cross (proj₂ s⊒ NW.↦ proj₂ t⊑)
  coerce-upʷᵐ ℓ (wf∀ hA) (wf∀ hB) r (∀ⁱ p)
      with coerce-upʷᵐ ℓ hA hB (Realizesᴺᵂ-∀ⁱ r) p
  coerce-upʷᵐ ℓ (wf∀ hA) (wf∀ hB) r (∀ⁱ p)
      | c , c⊑ =
    `∀ᶜ c , cast-all (proj₁ c⊑) , NW.cross (NW.`∀ (proj₂ c⊑))
  coerce-upʷᵐ {C = ‵ ι} ℓ wfBase wf★ r (tag ι) =
    (‵ ι) !ᶜ , cast-tag wfBase (‵ ι) refl , NW.tag (‵ ι)
  coerce-upʷᵐ ℓ (wf⇒ hA hB) wf★ r (tag_⇛_ p q)
      with coerce-up-fun-starˢʷ ℓ hA hB r p q
  coerce-upʷᵐ ℓ (wf⇒ hA hB) wf★ r (tag_⇛_ p q)
      | c , c⊑ , cˢ =
    c , c⊑
  coerce-upʷᵐ {C = ＇ X} ℓ hX wf★ r (tagˣ X⊑★)
      with realizes-star-upʷ r X⊑★
  coerce-upʷᵐ {C = ＇ X} ℓ hX wf★ r (tagˣ X⊑★)
      | c , c⊑ , cˢ =
    c , c⊑
  coerce-upʷᵐ {A = B₁ ⇒ B₂} ℓ (wf∀ hA) (wf⇒ hB₁ hB₂)
      r (ν safe occ p)
      with coerce-upʷᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy (wf⇒ hB₁ hB₂) TyRenameWf-suc)
             (Realizesᴺᵂ-ν-inst r)
             p
  coerce-upʷᵐ {A = B₁ ⇒ B₂} ℓ (wf∀ hA) (wf⇒ hB₁ hB₂)
      r (ν safe occ p)
      | c , c⊑ =
    instᶜ (B₁ ⇒ B₂) c ,
    cast-inst (wf⇒ hB₁ hB₂) occ (proj₁ c⊑) ,
    NW.inst
      (widening-at-instSafe-target
        (raise-genSafeShape shape-fun)
        (proj₁ c⊑) occ (proj₂ c⊑))
  coerce-upʷᵐ {A = `∀ B} ℓ (wf∀ hA) (wf∀ hB) r (ν safe occ p)
      with coerce-upʷᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy (wf∀ hB) TyRenameWf-suc)
             (Realizesᴺᵂ-ν-inst r)
             p
  coerce-upʷᵐ {A = `∀ B} ℓ (wf∀ hA) (wf∀ hB) r (ν safe occ p)
      | c , c⊑ =
    instᶜ (`∀ B) c , cast-inst (wf∀ hB) occ (proj₁ c⊑) ,
    NW.inst
      (widening-at-instSafe-target
        (raise-genSafeShape shape-all)
        (proj₁ c⊑) occ (proj₂ c⊑))
  coerce-upʷᵐ ℓ (wf∀ hA) (wfVar Y<Δ) r
      (ν nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-var⊥ nonvar occ p)
  coerce-upʷᵐ ℓ (wf∀ hA) wfBase r (ν nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-base⊥ nonvar occ p)
  coerce-upʷᵐ ℓ (wf∀ hA) wf★ r (ν nonvar occ p)
      with coerce-up-nu-star-core ℓ hA (Realizesᴺᵂ-ν-inst r)
             (nonVar-occurs→genSafeShape nonvar occ) p
  coerce-upʷᵐ ℓ (wf∀ hA) wf★ r (ν nonvar occ p)
      | upν★-core {c = c} c⊑ cᵍ =
    (instᶜ (★ ⇒ ★) c ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    cast-seq
      (cast-inst (wf⇒ wf★ wf★) occ (proj₁ c⊑))
      (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
    NW.inst-fun-tag cᵍ

  coerce-downⁿᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    Realizesᴺᵂ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ C
  coerce-downⁿᵐ ℓ wf★ wf★ r id★ =
    idᶜ ★ , cast-id wf★ refl , NW.id★
  coerce-downⁿᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY r (idˣ X⊑Y) =
    realizes-xx-downⁿ r X⊑Y
  coerce-downⁿᵐ {C = ‵ ι} ℓ wfBase wfBase r idι =
    idᶜ (‵ ι) , cast-id wfBase refl , NW.cross (NW.id-‵ ι)
  coerce-downⁿᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      with coerce-upʷᵐ ℓ hA hA′ r p
         | coerce-downⁿᵐ ℓ hB hB′ r q
  coerce-downⁿᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      | s , s⊑ | t , t⊒ =
    (s ↦ᶜ t) , cast-fun (proj₁ s⊑) (proj₁ t⊒) ,
    NW.cross (proj₂ s⊑ NW.↦ proj₂ t⊒)
  coerce-downⁿᵐ ℓ (wf∀ hA) (wf∀ hB) r (∀ⁱ p)
      with coerce-downⁿᵐ ℓ hA hB (Realizesᴺᵂ-∀ⁱ r) p
  coerce-downⁿᵐ ℓ (wf∀ hA) (wf∀ hB) r (∀ⁱ p)
      | c , c⊒ =
    `∀ᶜ c , cast-all (proj₁ c⊒) , NW.cross (NW.`∀ (proj₂ c⊒))
  coerce-downⁿᵐ {C = ‵ ι} ℓ wfBase wf★ r (tag ι) =
    (‵ ι) ？ᶜ , cast-untag wfBase (‵ ι) refl , NW.untag (‵ ι)
  coerce-downⁿᵐ ℓ (wf⇒ hA hB) wf★ r (tag_⇛_ p q)
      with coerce-down-fun-starˢⁿ ℓ hA hB r p q
  coerce-downⁿᵐ ℓ (wf⇒ hA hB) wf★ r (tag_⇛_ p q)
      | c , c⊒ , cˢ =
    c , c⊒
  coerce-downⁿᵐ {C = ＇ X} ℓ hX wf★ r (tagˣ X⊑★)
      with realizes-star-downⁿ r X⊑★
  coerce-downⁿᵐ {C = ＇ X} ℓ hX wf★ r (tagˣ X⊑★)
      | c , c⊒ , cˢ =
    c , c⊒
  coerce-downⁿᵐ {A = B₁ ⇒ B₂} ℓ (wf∀ hA) (wf⇒ hB₁ hB₂)
      r (ν safe occ p)
      with coerce-downⁿᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy (wf⇒ hB₁ hB₂) TyRenameWf-suc)
             (Realizesᴺᵂ-ν-gen r)
             p
  coerce-downⁿᵐ {A = B₁ ⇒ B₂} ℓ (wf∀ hA) (wf⇒ hB₁ hB₂)
      r (ν safe occ p)
      | c , c⊒ =
    genᶜ (B₁ ⇒ B₂) c ,
    cast-gen (wf⇒ hB₁ hB₂) occ (proj₁ c⊒) ,
    NW.gen
      (narrowing-at-genSafe-source
        (raise-genSafeShape shape-fun)
        (proj₁ c⊒) occ (proj₂ c⊒))
  coerce-downⁿᵐ {A = `∀ B} ℓ (wf∀ hA) (wf∀ hB) r (ν safe occ p)
      with coerce-downⁿᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy (wf∀ hB) TyRenameWf-suc)
             (Realizesᴺᵂ-ν-gen r)
             p
  coerce-downⁿᵐ {A = `∀ B} ℓ (wf∀ hA) (wf∀ hB) r (ν safe occ p)
      | c , c⊒ =
    genᶜ (`∀ B) c , cast-gen (wf∀ hB) occ (proj₁ c⊒) ,
    NW.gen
      (narrowing-at-genSafe-source
        (raise-genSafeShape shape-all)
        (proj₁ c⊒) occ (proj₂ c⊒))
  coerce-downⁿᵐ ℓ (wf∀ hA) (wfVar Y<Δ) r
      (ν nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-var⊥ nonvar occ p)
  coerce-downⁿᵐ ℓ (wf∀ hA) wfBase r (ν nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-base⊥ nonvar occ p)
  coerce-downⁿᵐ ℓ (wf∀ hA) wf★ r (ν nonvar occ p)
      with coerce-down-nu-star-core ℓ hA (Realizesᴺᵂ-ν-gen r)
             (nonVar-occurs→genSafeShape nonvar occ) p
  coerce-downⁿᵐ ℓ (wf∀ hA) wf★ r (ν nonvar occ p)
      | downν★-core {c = c} c⊒ cᵍ =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ genᶜ (★ ⇒ ★) c) ,
    cast-seq
      (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
      (cast-gen (wf⇒ wf★ wf★) occ (proj₁ c⊒)) ,
    NW.fun-untag-gen cᵍ

  coerce-up-nu-star-core :
    ∀ {μ Δ Σ Φ A} →
    (ℓ : Label) →
    WfTy Δ A →
    (r : Realizesᴺᵂ μ Δ Σ Φ) →
    GenSafeShape A →
    (p : Φ ⊢ A ⊑ ★) →
    UpNuStarCore r p
  coerce-up-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      with down-star-view ℓ hA r p | up-star-view ℓ hB r q
  coerce-up-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q) | down★-id | up★-id =
    upν★-core
      (cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
       NW.cross (NW.id★ NW.↦ NW.id★))
      (NW.safe-fun NW.id★ NW.id★)
  coerce-up-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      | down★-id | up★-strict {c = t} t⊑ tˢ =
    upν★-core
      (cast-fun (cast-id wf★ refl) (proj₁ t⊑) ,
       NW.cross (NW.id★ NW.↦ proj₂ t⊑))
      (NW.safe-fun NW.id★ (proj₂ t⊑))
  coerce-up-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      | down★-strict {c = s} s⊒ sˢ | up★-id =
    upν★-core
      (cast-fun (proj₁ s⊒) (cast-id wf★ refl) ,
       NW.cross (proj₂ s⊒ NW.↦ NW.id★))
      (NW.safe-fun (proj₂ s⊒) NW.id★)
  coerce-up-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      | down★-strict {c = s} s⊒ sˢ
      | up★-strict {c = t} t⊑ tˢ =
    upν★-core
      (cast-fun (proj₁ s⊒) (proj₁ t⊑) ,
       NW.cross (proj₂ s⊒ NW.↦ proj₂ t⊑))
      (NW.safe-fun (proj₂ s⊒) (proj₂ t⊑))
  coerce-up-nu-star-core ℓ (wf∀ hA) r shape-all
      (ν nonvar occ p)
      with coerce-up-nu-star-core ℓ hA
             (Realizesᴺᵂ-ν-inst r)
             (nonVar-occurs→genSafeShape nonvar occ) p
  coerce-up-nu-star-core ℓ (wf∀ hA) r shape-all
      (ν nonvar occ p) | upν★-core {c = c} c⊑ cᵍ =
    upν★-core
      (cast-inst (wf⇒ wf★ wf★) occ (proj₁ c⊑) , NW.inst cᵍ)
      (NW.safe-inst cᵍ)

  coerce-down-nu-star-core :
    ∀ {μ Δ Σ Φ A} →
    (ℓ : Label) →
    WfTy Δ A →
    (r : Realizesᴺᵂ μ Δ Σ Φ) →
    GenSafeShape A →
    (p : Φ ⊢ A ⊑ ★) →
    DownNuStarCore r p
  coerce-down-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      with up-star-view ℓ hA r p | down-star-view ℓ hB r q
  coerce-down-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q) | up★-id | down★-id =
    downν★-core
      (cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
       NW.cross (NW.id★ NW.↦ NW.id★))
      (NW.safe-fun NW.id★ NW.id★)
  coerce-down-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      | up★-id | down★-strict {c = t} t⊒ tˢ =
    downν★-core
      (cast-fun (cast-id wf★ refl) (proj₁ t⊒) ,
       NW.cross (NW.id★ NW.↦ proj₂ t⊒))
      (NW.safe-fun NW.id★ (proj₂ t⊒))
  coerce-down-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      | up★-strict {c = s} s⊑ sˢ | down★-id =
    downν★-core
      (cast-fun (proj₁ s⊑) (cast-id wf★ refl) ,
       NW.cross (proj₂ s⊑ NW.↦ NW.id★))
      (NW.safe-fun (proj₂ s⊑) NW.id★)
  coerce-down-nu-star-core ℓ (wf⇒ hA hB) r shape-fun
      (tag_⇛_ p q)
      | up★-strict {c = s} s⊑ sˢ
      | down★-strict {c = t} t⊒ tˢ =
    downν★-core
      (cast-fun (proj₁ s⊑) (proj₁ t⊒) ,
       NW.cross (proj₂ s⊑ NW.↦ proj₂ t⊒))
      (NW.safe-fun (proj₂ s⊑) (proj₂ t⊒))
  coerce-down-nu-star-core ℓ (wf∀ hA) r shape-all
      (ν nonvar occ p)
      with coerce-down-nu-star-core ℓ hA
             (Realizesᴺᵂ-ν-gen r)
             (nonVar-occurs→genSafeShape nonvar occ) p
  coerce-down-nu-star-core ℓ (wf∀ hA) r shape-all
      (ν nonvar occ p) | downν★-core {c = c} c⊒ cᵍ =
    downν★-core
      (cast-gen (wf⇒ wf★ wf★) occ (proj₁ c⊒) , NW.gen cᵍ)
      (NW.safe-gen cᵍ)

  up-star-view :
    ∀ {μ Δ Σ Φ A} →
    (ℓ : Label) →
    WfTy Δ A →
    (r : Realizesᴺᵂ μ Δ Σ Φ) →
    (p : Φ ⊢ A ⊑ ★) →
    UpStarView r p
  up-star-view ℓ wf★ r id★ =
    up★-id
  up-star-view {A = ‵ ι} ℓ wfBase r (tag ι) =
    up★-strict
      (cast-tag wfBase (‵ ι) refl , NW.tag (‵ ι))
      (NW.strict-tag (‵ ι))
  up-star-view ℓ (wf⇒ hA hB) r (tag_⇛_ p q)
      with coerce-up-fun-starˢʷ ℓ hA hB r p q
  up-star-view ℓ (wf⇒ hA hB) r (tag_⇛_ p q)
      | c , c⊑ , cˢ =
    up★-strict c⊑ cˢ
  up-star-view {A = ＇ X} ℓ hX r (tagˣ X⊑★)
      with realizes-star-upʷ r X⊑★
  up-star-view {A = ＇ X} ℓ hX r (tagˣ X⊑★)
      | c , c⊑ , cˢ =
    up★-strict c⊑ cˢ
  up-star-view {A = `∀ A} ℓ (wf∀ hA) r (ν safe occ p)
      with coerce-up-nu-star-core ℓ hA (Realizesᴺᵂ-ν-inst r)
             (nonVar-occurs→genSafeShape safe occ) p
  up-star-view {A = `∀ A} ℓ (wf∀ hA) r (ν safe occ p)
      | upν★-core {c = c} c⊑ cᵍ =
    up★-strict
      (cast-seq
        (cast-inst (wf⇒ wf★ wf★) occ (proj₁ c⊑))
        (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
       NW.inst-fun-tag cᵍ)
      (NW.strict-inst-fun-tag cᵍ)

  down-star-view :
    ∀ {μ Δ Σ Φ A} →
    (ℓ : Label) →
    WfTy Δ A →
    (r : Realizesᴺᵂ μ Δ Σ Φ) →
    (p : Φ ⊢ A ⊑ ★) →
    DownStarView r p
  down-star-view ℓ wf★ r id★ =
    down★-id
  down-star-view {A = ‵ ι} ℓ wfBase r (tag ι) =
    down★-strict
      (cast-untag wfBase (‵ ι) refl , NW.untag (‵ ι))
      (NW.strict-untag (‵ ι))
  down-star-view ℓ (wf⇒ hA hB) r (tag_⇛_ p q)
      with coerce-down-fun-starˢⁿ ℓ hA hB r p q
  down-star-view ℓ (wf⇒ hA hB) r (tag_⇛_ p q)
      | c , c⊒ , cˢ =
    down★-strict c⊒ cˢ
  down-star-view {A = ＇ X} ℓ hX r (tagˣ X⊑★)
      with realizes-star-downⁿ r X⊑★
  down-star-view {A = ＇ X} ℓ hX r (tagˣ X⊑★)
      | c , c⊒ , cˢ =
    down★-strict c⊒ cˢ
  down-star-view {A = `∀ A} ℓ (wf∀ hA) r (ν safe occ p)
      with coerce-down-nu-star-core ℓ hA (Realizesᴺᵂ-ν-gen r)
             (nonVar-occurs→genSafeShape safe occ) p
  down-star-view {A = `∀ A} ℓ (wf∀ hA) r (ν safe occ p)
      | downν★-core {c = c} c⊒ cᵍ =
    down★-strict
      (cast-seq
        (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
        (cast-gen (wf⇒ wf★ wf★) occ (proj₁ c⊒)) ,
       NW.fun-untag-gen cᵍ)
      (NW.strict-fun-untag-gen cᵍ)

  coerce-up-fun-starˢʷ :
    ∀ {μ Δ Σ Φ A B} →
    (ℓ : Label) →
    WfTy Δ A →
    WfTy Δ B →
    (r : Realizesᴺᵂ μ Δ Σ Φ) →
    Φ ⊢ A ⊑ ★ →
    Φ ⊢ B ⊑ ★ →
    Σ[ c ∈ Coercion ]
      (μ ∣ Δ ∣ Σ ⊢ c ∶ A ⇒ B ⊑ ★) × NW.StrictWidening c
  coerce-up-fun-starˢʷ ℓ hA hB r p q
      with down-star-view ℓ hA r p | up-star-view ℓ hB r q
  coerce-up-fun-starˢʷ ℓ hA hB r p q
      | down★-id | up★-id =
    ((★ ⇒ ★) !ᶜ) ,
    (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl , NW.tag ★⇒★) ,
    NW.strict-tag ★⇒★
  coerce-up-fun-starˢʷ ℓ hA hB r p q
      | down★-id | up★-strict {c = t} t⊑ tˢ =
    ((idᶜ ★ ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    (cast-seq
      (cast-fun (cast-id wf★ refl) (proj₁ t⊑))
      (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
     NW.strictʷ→widen (NW.strict-tag-seq (NW.cw-funʳ NW.id★ tˢ) ★⇒★)) ,
    NW.strict-tag-seq (NW.cw-funʳ NW.id★ tˢ) ★⇒★
  coerce-up-fun-starˢʷ ℓ hA hB r p q
      | down★-strict {c = s} s⊒ sˢ | up★-id =
    ((s ↦ᶜ idᶜ ★) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    (cast-seq
      (cast-fun (proj₁ s⊒) (cast-id wf★ refl))
      (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
     NW.strictʷ→widen (NW.strict-tag-seq (NW.cw-funˡ sˢ NW.id★) ★⇒★)) ,
    NW.strict-tag-seq (NW.cw-funˡ sˢ NW.id★) ★⇒★
  coerce-up-fun-starˢʷ ℓ hA hB r p q
      | down★-strict {c = s} s⊒ sˢ
      | up★-strict {c = t} t⊑ tˢ =
    ((s ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    (cast-seq
      (cast-fun (proj₁ s⊒) (proj₁ t⊑))
      (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
     NW.strictʷ→widen
       (NW.strict-tag-seq (NW.cw-funˡ sˢ (proj₂ t⊑)) ★⇒★)) ,
    NW.strict-tag-seq (NW.cw-funˡ sˢ (proj₂ t⊑)) ★⇒★

  coerce-down-fun-starˢⁿ :
    ∀ {μ Δ Σ Φ A B} →
    (ℓ : Label) →
    WfTy Δ A →
    WfTy Δ B →
    (r : Realizesᴺᵂ μ Δ Σ Φ) →
    Φ ⊢ A ⊑ ★ →
    Φ ⊢ B ⊑ ★ →
    Σ[ c ∈ Coercion ]
      (μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ A ⇒ B) × NW.StrictNarrowing c
  coerce-down-fun-starˢⁿ ℓ hA hB r p q
      with up-star-view ℓ hA r p | down-star-view ℓ hB r q
  coerce-down-fun-starˢⁿ ℓ hA hB r p q
      | up★-id | down★-id =
    ((★ ⇒ ★) ？ᶜ) ,
    (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl , NW.untag ★⇒★) ,
    NW.strict-untag ★⇒★
  coerce-down-fun-starˢⁿ ℓ hA hB r p q
      | up★-id | down★-strict {c = t} t⊒ tˢ =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (idᶜ ★ ↦ᶜ t)) ,
    (cast-seq
      (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
      (cast-fun (cast-id wf★ refl) (proj₁ t⊒)) ,
     NW.strictⁿ→narrow (NW.strict-untag-seq ★⇒★
       (NW.cn-funʳ NW.id★ tˢ))) ,
    NW.strict-untag-seq ★⇒★ (NW.cn-funʳ NW.id★ tˢ)
  coerce-down-fun-starˢⁿ ℓ hA hB r p q
      | up★-strict {c = s} s⊑ sˢ | down★-id =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (s ↦ᶜ idᶜ ★)) ,
    (cast-seq
      (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
      (cast-fun (proj₁ s⊑) (cast-id wf★ refl)) ,
     NW.strictⁿ→narrow (NW.strict-untag-seq ★⇒★
       (NW.cn-funˡ sˢ NW.id★))) ,
    NW.strict-untag-seq ★⇒★ (NW.cn-funˡ sˢ NW.id★)
  coerce-down-fun-starˢⁿ ℓ hA hB r p q
      | up★-strict {c = s} s⊑ sˢ
      | down★-strict {c = t} t⊒ tˢ =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (s ↦ᶜ t)) ,
    (cast-seq
      (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
      (cast-fun (proj₁ s⊑) (proj₁ t⊒)) ,
     NW.strictⁿ→narrow
       (NW.strict-untag-seq ★⇒★ (NW.cn-funˡ sˢ (proj₂ t⊒)))) ,
    NW.strict-untag-seq ★⇒★ (NW.cn-funˡ sˢ (proj₂ t⊒))

coerce-upʷ :
  ∀ {μ Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  Realizesᴺᵂ μ Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊑ A
coerce-upʷ = coerce-upʷᵐ

coerce-downⁿ :
  ∀ {μ Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  Realizesᴺᵂ μ Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ C
coerce-downⁿ = coerce-downⁿᵐ

------------------------------------------------------------------------
-- Indexed synthesis retaining hereditary cast shape
------------------------------------------------------------------------

shape-target-liftνᵢ :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  ⌊ ⊑-target-liftνᵢ p ⌋ ≡ ⌊ p ⌋
shape-target-liftνᵢ {A = A} p =
  trans
    (shape-subst-source (renameᵗ-id A) renamed)
    (shape-rename
      rename-assm²-⇑ᴸ-to-⇑ᵢ
      (λ X<Δ → X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p)
  where
  renamed =
    ⊑-renameᵗ²ᵢ
      rename-assm²-⇑ᴸ-to-⇑ᵢ
      (λ X<Δ → X<Δ)
      (λ Y<Δ → s<s Y<Δ)
      p

data UpStarShapeView {μ Δ Σ Φ A}
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) : Set₁ where
  up★-shape-id :
    (eqA : A ≡ ★) →
    subst (λ T → Φ ∣ Δ ⊢ T ⊑ ★ ⊣ Δ) eqA p ≡ id★ᵢ →
    UpStarShapeView p

  up★-shape-strict : ∀ {c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ ★ →
    NW.StrictWidening c →
    widening ⊢ᶜ c ⦂ ⌊ p ⌋ →
    UpStarShapeView p

data DownStarShapeView {μ Δ Σ Φ A}
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) : Set₁ where
  down★-shape-id :
    (eqA : A ≡ ★) →
    subst (λ T → Φ ∣ Δ ⊢ T ⊑ ★ ⊣ Δ) eqA p ≡ id★ᵢ →
    DownStarShapeView p

  down★-shape-strict : ∀ {c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ A →
    NW.StrictNarrowing c →
    narrowing ⊢ᶜ c ⦂ ⌊ p ⌋ →
    DownStarShapeView p

data UpNuStarShapeCore {μ Δ Σ Φ A}
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) : Set₁ where
  upν★-shape-core : ∀ {c s} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ (★ ⇒ ★) →
    NW.InstSafe c →
    widening ⊢ᶜ c ⦂ s →
    s ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ ⌊ p ⌋ →
    UpNuStarShapeCore p

data DownNuStarShapeCore {μ Δ Σ Φ A}
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) : Set₁ where
  downν★-shape-core : ∀ {c s} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ (★ ⇒ ★) ⊒ A →
    NW.GenSafe c →
    narrowing ⊢ᶜ c ⦂ s →
    s ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ ⌊ p ⌋ →
    DownNuStarShapeCore p

mutual
  coerce-upʷ-shapeᵐ :
    ∀ {μ Δ Σ Φ C A} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    (p : Φ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
    Σ[ c ∈ Coercion ]
      (μ ∣ Δ ∣ Σ ⊢ c ∶ C ⊑ A) ×
      (widening ⊢ᶜ c ⦂ ⌊ p ⌋)
  coerce-upʷ-shapeᵐ ℓ shapes id★ᵢ =
    idᶜ ★ , (cast-id wf★ refl , NW.id★) , shape-id-star
  coerce-upʷ-shapeᵐ ℓ shapes (idˣᵢ x∈ X<Δ Y<Δ) =
    realizes-shape-xx-up shapes x∈
  coerce-upʷ-shapeᵐ {C = ‵ ι} ℓ shapes idιᵢ =
    idᶜ (‵ ι) ,
    (cast-id wfBase refl , NW.cross (NW.id-‵ ι)) ,
    shape-id-base
  coerce-upʷ-shapeᵐ ℓ shapes (p ↦ᵢ q)
      with coerce-downⁿ-shapeᵐ ℓ shapes p
         | coerce-upʷ-shapeᵐ ℓ shapes q
  coerce-upʷ-shapeᵐ ℓ shapes (p ↦ᵢ q)
      | s , s⊒ , s-shape | t , t⊑ , t-shape =
    (s ↦ᶜ t) ,
    (cast-fun (proj₁ s⊒) (proj₁ t⊑) ,
     NW.cross (proj₂ s⊒ NW.↦ proj₂ t⊑)) ,
    shape-fun s-shape t-shape
  coerce-upʷ-shapeᵐ ℓ shapes (∀ⁱᵢ p)
      with coerce-upʷ-shapeᵐ ℓ (ShapeRealizesᴺᵂ-∀ⁱ shapes) p
  coerce-upʷ-shapeᵐ ℓ shapes (∀ⁱᵢ p)
      | c , c⊑ , c-shape =
    `∀ᶜ c ,
    (cast-all (proj₁ c⊑) , NW.cross (NW.`∀ (proj₂ c⊑))) ,
    shape-all c-shape
  coerce-upʷ-shapeᵐ {C = ‵ ι} ℓ shapes (tagᵢ ι) =
    (‵ ι) !ᶜ ,
    (cast-tag wfBase (‵ ι) refl , NW.tag (‵ ι)) ,
    shape-tag-base
  coerce-upʷ-shapeᵐ ℓ shapes (tagᵢ p ⇛ q)
      with coerce-up-fun-star-shape ℓ shapes p q
  coerce-upʷ-shapeᵐ ℓ shapes (tagᵢ p ⇛ q)
      | c , c⊑ , cˢ , c-shape =
    c , c⊑ , c-shape
  coerce-upʷ-shapeᵐ {C = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      with realizes-shape-star-up shapes x★∈
  coerce-upʷ-shapeᵐ {C = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      | c , c⊑ , cˢ , c-shape =
    c , c⊑ , c-shape
  coerce-upʷ-shapeᵐ {A = B₁ ⇒ B₂} ℓ shapes
      (νᵢ safe occ p)
      with ⊑-tgt-wfᵢ p
         | coerce-upʷ-shapeᵐ ℓ
             (ShapeRealizesᴺᵂ-ν-inst shapes)
             (⊑-target-liftνᵢ p)
  coerce-upʷ-shapeᵐ {A = B₁ ⇒ B₂} ℓ shapes
      (νᵢ safe occ p)
      | wf⇒ hB₁ hB₂ | c , c⊑ , c-shape =
    instᶜ (B₁ ⇒ B₂) c ,
    (cast-inst (wf⇒ hB₁ hB₂) occ (proj₁ c⊑) ,
     NW.inst
       (widening-at-instSafe-target
         (raise-genSafeShape shape-fun)
         (proj₁ c⊑) occ (proj₂ c⊑))) ,
    subst
      (λ s → widening ⊢ᶜ instᶜ (B₁ ⇒ B₂) c ⦂ s)
      (cong νˢ_ (shape-target-liftνᵢ p))
      (shape-inst c-shape)
  coerce-upʷ-shapeᵐ {A = `∀ B} ℓ shapes
      (νᵢ safe occ p)
      with ⊑-tgt-wfᵢ p
         | coerce-upʷ-shapeᵐ ℓ
             (ShapeRealizesᴺᵂ-ν-inst shapes)
             (⊑-target-liftνᵢ p)
  coerce-upʷ-shapeᵐ {A = `∀ B} ℓ shapes
      (νᵢ safe occ p)
      | wf∀ hB | c , c⊑ , c-shape =
    instᶜ (`∀ B) c ,
    (cast-inst (wf∀ hB) occ (proj₁ c⊑) ,
     NW.inst
       (widening-at-instSafe-target
         (raise-genSafeShape shape-all)
         (proj₁ c⊑) occ (proj₂ c⊑))) ,
    subst
      (λ s → widening ⊢ᶜ instᶜ (`∀ B) c ⦂ s)
      (cong νˢ_ (shape-target-liftνᵢ p))
      (shape-inst c-shape)
  coerce-upʷ-shapeᵐ {A = ＇ Y} ℓ shapes
      (νᵢ nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-var⊥ nonvar occ (⊑-forgetᵢ p))
  coerce-upʷ-shapeᵐ {A = ‵ ι} ℓ shapes
      (νᵢ nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-base⊥ nonvar occ (⊑-forgetᵢ p))
  coerce-upʷ-shapeᵐ {A = ★} ℓ shapes (νᵢ nonvar occ p)
      with coerce-up-nu-star-shape-core ℓ
             (ShapeRealizesᴺᵂ-ν-inst shapes)
             (nonVar-occurs→genSafeShape nonvar occ)
             (⊑-target-liftνᵢ p)
  coerce-upʷ-shapeᵐ {A = ★} ℓ shapes (νᵢ nonvar occ p)
      | upν★-shape-core {c = c}
          c⊑ cᵍ c-shape comp =
    (instᶜ (★ ⇒ ★) c ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    (cast-seq
       (cast-inst (wf⇒ wf★ wf★) occ (proj₁ c⊑))
       (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
     NW.inst-fun-tag cᵍ) ,
    subst
      (λ s →
        widening ⊢ᶜ
          (instᶜ (★ ⇒ ★) c ︔ᶜ ((★ ⇒ ★) !ᶜ)) ⦂ s)
      (cong νˢ_ (shape-target-liftνᵢ p))
      (shape-sequence-widening
        (shape-inst c-shape)
        shape-tag-fun
        (comp-ν comp))

  coerce-downⁿ-shapeᵐ :
    ∀ {μ Δ Σ Φ C A} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    (p : Φ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
    Σ[ c ∈ Coercion ]
      (μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ C) ×
      (narrowing ⊢ᶜ c ⦂ ⌊ p ⌋)
  coerce-downⁿ-shapeᵐ ℓ shapes id★ᵢ =
    idᶜ ★ , (cast-id wf★ refl , NW.id★) , shape-id-star
  coerce-downⁿ-shapeᵐ ℓ shapes (idˣᵢ x∈ X<Δ Y<Δ) =
    realizes-shape-xx-down shapes x∈
  coerce-downⁿ-shapeᵐ {C = ‵ ι} ℓ shapes idιᵢ =
    idᶜ (‵ ι) ,
    (cast-id wfBase refl , NW.cross (NW.id-‵ ι)) ,
    shape-id-base
  coerce-downⁿ-shapeᵐ ℓ shapes (p ↦ᵢ q)
      with coerce-upʷ-shapeᵐ ℓ shapes p
         | coerce-downⁿ-shapeᵐ ℓ shapes q
  coerce-downⁿ-shapeᵐ ℓ shapes (p ↦ᵢ q)
      | s , s⊑ , s-shape | t , t⊒ , t-shape =
    (s ↦ᶜ t) ,
    (cast-fun (proj₁ s⊑) (proj₁ t⊒) ,
     NW.cross (proj₂ s⊑ NW.↦ proj₂ t⊒)) ,
    shape-fun s-shape t-shape
  coerce-downⁿ-shapeᵐ ℓ shapes (∀ⁱᵢ p)
      with coerce-downⁿ-shapeᵐ ℓ
             (ShapeRealizesᴺᵂ-∀ⁱ shapes) p
  coerce-downⁿ-shapeᵐ ℓ shapes (∀ⁱᵢ p)
      | c , c⊒ , c-shape =
    `∀ᶜ c ,
    (cast-all (proj₁ c⊒) , NW.cross (NW.`∀ (proj₂ c⊒))) ,
    shape-all c-shape
  coerce-downⁿ-shapeᵐ {C = ‵ ι} ℓ shapes (tagᵢ ι) =
    (‵ ι) ？ᶜ ,
    (cast-untag wfBase (‵ ι) refl , NW.untag (‵ ι)) ,
    shape-untag-base
  coerce-downⁿ-shapeᵐ ℓ shapes (tagᵢ p ⇛ q)
      with coerce-down-fun-star-shape ℓ shapes p q
  coerce-downⁿ-shapeᵐ ℓ shapes (tagᵢ p ⇛ q)
      | c , c⊒ , cˢ , c-shape =
    c , c⊒ , c-shape
  coerce-downⁿ-shapeᵐ {C = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      with realizes-shape-star-down shapes x★∈
  coerce-downⁿ-shapeᵐ {C = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      | c , c⊒ , cˢ , c-shape =
    c , c⊒ , c-shape
  coerce-downⁿ-shapeᵐ {A = B₁ ⇒ B₂} ℓ shapes
      (νᵢ safe occ p)
      with ⊑-tgt-wfᵢ p
         | coerce-downⁿ-shapeᵐ ℓ
             (ShapeRealizesᴺᵂ-ν-gen shapes)
             (⊑-target-liftνᵢ p)
  coerce-downⁿ-shapeᵐ {A = B₁ ⇒ B₂} ℓ shapes
      (νᵢ safe occ p)
      | wf⇒ hB₁ hB₂ | c , c⊒ , c-shape =
    genᶜ (B₁ ⇒ B₂) c ,
    (cast-gen (wf⇒ hB₁ hB₂) occ (proj₁ c⊒) ,
     NW.gen
       (narrowing-at-genSafe-source
         (raise-genSafeShape shape-fun)
         (proj₁ c⊒) occ (proj₂ c⊒))) ,
    subst
      (λ s → narrowing ⊢ᶜ genᶜ (B₁ ⇒ B₂) c ⦂ s)
      (cong νˢ_ (shape-target-liftνᵢ p))
      (shape-gen c-shape)
  coerce-downⁿ-shapeᵐ {A = `∀ B} ℓ shapes
      (νᵢ safe occ p)
      with ⊑-tgt-wfᵢ p
         | coerce-downⁿ-shapeᵐ ℓ
             (ShapeRealizesᴺᵂ-ν-gen shapes)
             (⊑-target-liftνᵢ p)
  coerce-downⁿ-shapeᵐ {A = `∀ B} ℓ shapes
      (νᵢ safe occ p)
      | wf∀ hB | c , c⊒ , c-shape =
    genᶜ (`∀ B) c ,
    (cast-gen (wf∀ hB) occ (proj₁ c⊒) ,
     NW.gen
       (narrowing-at-genSafe-source
         (raise-genSafeShape shape-all)
         (proj₁ c⊒) occ (proj₂ c⊒))) ,
    subst
      (λ s → narrowing ⊢ᶜ genᶜ (`∀ B) c ⦂ s)
      (cong νˢ_ (shape-target-liftνᵢ p))
      (shape-gen c-shape)
  coerce-downⁿ-shapeᵐ {A = ＇ Y} ℓ shapes
      (νᵢ nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-var⊥ nonvar occ (⊑-forgetᵢ p))
  coerce-downⁿ-shapeᵐ {A = ‵ ι} ℓ shapes
      (νᵢ nonvar occ p) =
    ⊥-elim (nonVar-occurs-to-base⊥ nonvar occ (⊑-forgetᵢ p))
  coerce-downⁿ-shapeᵐ {A = ★} ℓ shapes (νᵢ nonvar occ p)
      with coerce-down-nu-star-shape-core ℓ
             (ShapeRealizesᴺᵂ-ν-gen shapes)
             (nonVar-occurs→genSafeShape nonvar occ)
             (⊑-target-liftνᵢ p)
  coerce-downⁿ-shapeᵐ {A = ★} ℓ shapes (νᵢ nonvar occ p)
      | downν★-shape-core {c = c}
          c⊒ cᵍ c-shape comp =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ genᶜ (★ ⇒ ★) c) ,
    (cast-seq
       (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
       (cast-gen (wf⇒ wf★ wf★) occ (proj₁ c⊒)) ,
     NW.fun-untag-gen cᵍ) ,
    subst
      (λ s →
        narrowing ⊢ᶜ
          (((★ ⇒ ★) ？ᶜ) ︔ᶜ genᶜ (★ ⇒ ★) c) ⦂ s)
      (cong νˢ_ (shape-target-liftνᵢ p))
      (shape-sequence-narrowing
        shape-untag-fun
        (shape-gen c-shape)
        (comp-ν comp))

  up-star-shape-view :
    ∀ {μ Δ Σ Φ A} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) →
    UpStarShapeView {μ = μ} {Σ = Σ} p
  up-star-shape-view ℓ shapes id★ᵢ =
    up★-shape-id refl refl
  up-star-shape-view {A = ‵ ι} ℓ shapes (tagᵢ ι) =
    up★-shape-strict
      (cast-tag wfBase (‵ ι) refl , NW.tag (‵ ι))
      (NW.strict-tag (‵ ι))
      shape-tag-base
  up-star-shape-view ℓ shapes (tagᵢ p ⇛ q)
      with coerce-up-fun-star-shape ℓ shapes p q
  up-star-shape-view ℓ shapes (tagᵢ p ⇛ q)
      | c , c⊑ , cˢ , c-shape =
    up★-shape-strict c⊑ cˢ c-shape
  up-star-shape-view {A = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      with realizes-shape-star-up shapes x★∈
  up-star-shape-view {A = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      | c , c⊑ , cˢ , c-shape =
    up★-shape-strict c⊑ cˢ c-shape
  up-star-shape-view ℓ shapes (νᵢ safe occ p)
      with coerce-up-nu-star-shape-core ℓ
             (ShapeRealizesᴺᵂ-ν-inst shapes)
             (nonVar-occurs→genSafeShape safe occ)
             (⊑-target-liftνᵢ p)
  up-star-shape-view ℓ shapes (νᵢ safe occ p)
      | upν★-shape-core {c = c}
          c⊑ cᵍ c-shape comp =
    up★-shape-strict
      (cast-seq
        (cast-inst (wf⇒ wf★ wf★) occ (proj₁ c⊑))
        (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
       NW.inst-fun-tag cᵍ)
      (NW.strict-inst-fun-tag cᵍ)
      (subst
        (λ s →
          widening ⊢ᶜ
            (instᶜ (★ ⇒ ★) c ︔ᶜ ((★ ⇒ ★) !ᶜ)) ⦂ s)
        (cong νˢ_ (shape-target-liftνᵢ p))
        (shape-sequence-widening
          (shape-inst c-shape)
          shape-tag-fun
          (comp-ν comp)))

  down-star-shape-view :
    ∀ {μ Δ Σ Φ A} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) →
    DownStarShapeView {μ = μ} {Σ = Σ} p
  down-star-shape-view ℓ shapes id★ᵢ =
    down★-shape-id refl refl
  down-star-shape-view {A = ‵ ι} ℓ shapes (tagᵢ ι) =
    down★-shape-strict
      (cast-untag wfBase (‵ ι) refl , NW.untag (‵ ι))
      (NW.strict-untag (‵ ι))
      shape-untag-base
  down-star-shape-view ℓ shapes (tagᵢ p ⇛ q)
      with coerce-down-fun-star-shape ℓ shapes p q
  down-star-shape-view ℓ shapes (tagᵢ p ⇛ q)
      | c , c⊒ , cˢ , c-shape =
    down★-shape-strict c⊒ cˢ c-shape
  down-star-shape-view {A = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      with realizes-shape-star-down shapes x★∈
  down-star-shape-view {A = ＇ X} ℓ shapes
      (tagˣᵢ x★∈ X<Δ)
      | c , c⊒ , cˢ , c-shape =
    down★-shape-strict c⊒ cˢ c-shape
  down-star-shape-view ℓ shapes (νᵢ safe occ p)
      with coerce-down-nu-star-shape-core ℓ
             (ShapeRealizesᴺᵂ-ν-gen shapes)
             (nonVar-occurs→genSafeShape safe occ)
             (⊑-target-liftνᵢ p)
  down-star-shape-view ℓ shapes (νᵢ safe occ p)
      | downν★-shape-core {c = c}
          c⊒ cᵍ c-shape comp =
    down★-shape-strict
      (cast-seq
        (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
        (cast-gen (wf⇒ wf★ wf★) occ (proj₁ c⊒)) ,
       NW.fun-untag-gen cᵍ)
      (NW.strict-fun-untag-gen cᵍ)
      (subst
        (λ s →
          narrowing ⊢ᶜ
            (((★ ⇒ ★) ？ᶜ) ︔ᶜ genᶜ (★ ⇒ ★) c) ⦂ s)
        (cong νˢ_ (shape-target-liftνᵢ p))
        (shape-sequence-narrowing
          shape-untag-fun
          (shape-gen c-shape)
          (comp-ν comp)))

  coerce-up-fun-star-shape :
    ∀ {μ Δ Σ Φ A B} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) →
    (q : Φ ∣ Δ ⊢ B ⊑ ★ ⊣ Δ) →
    Σ[ c ∈ Coercion ]
      (μ ∣ Δ ∣ Σ ⊢ c ∶ A ⇒ B ⊑ ★) ×
      NW.StrictWidening c ×
      (widening ⊢ᶜ c ⦂ ⌊ tagᵢ p ⇛ q ⌋)
  coerce-up-fun-star-shape ℓ shapes p q
      with down-star-shape-view ℓ shapes p
         | up-star-shape-view ℓ shapes q
  coerce-up-fun-star-shape ℓ shapes p q
      | down★-shape-id refl refl | up★-shape-id refl refl =
    ((★ ⇒ ★) !ᶜ) ,
    (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl , NW.tag ★⇒★) ,
    NW.strict-tag ★⇒★ ,
    shape-tag-fun
  coerce-up-fun-star-shape ℓ shapes p q
      | down★-shape-id refl refl
      | up★-shape-strict {c = t}
          t⊑ tˢ t-shape =
    ((idᶜ ★ ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    (cast-seq
      (cast-fun (cast-id wf★ refl) (proj₁ t⊑))
      (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
     NW.strictʷ→widen
       (NW.strict-tag-seq (NW.cw-funʳ NW.id★ tˢ) ★⇒★)) ,
    NW.strict-tag-seq (NW.cw-funʳ NW.id★ tˢ) ★⇒★ ,
    shape-sequence-widening
      (shape-fun shape-id-star t-shape)
      shape-tag-fun
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-up-fun-star-shape ℓ shapes p q
      | down★-shape-strict {c = s}
          s⊒ sˢ s-shape
      | up★-shape-id refl refl =
    ((s ↦ᶜ idᶜ ★) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    (cast-seq
      (cast-fun (proj₁ s⊒) (cast-id wf★ refl))
      (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
     NW.strictʷ→widen
       (NW.strict-tag-seq (NW.cw-funˡ sˢ NW.id★) ★⇒★)) ,
    NW.strict-tag-seq (NW.cw-funˡ sˢ NW.id★) ★⇒★ ,
    shape-sequence-widening
      (shape-fun s-shape shape-id-star)
      shape-tag-fun
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-up-fun-star-shape ℓ shapes p q
      | down★-shape-strict {c = s}
          s⊒ sˢ s-shape
      | up★-shape-strict {c = t}
          t⊑ tˢ t-shape =
    ((s ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    (cast-seq
      (cast-fun (proj₁ s⊒) (proj₁ t⊑))
      (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl) ,
     NW.strictʷ→widen
       (NW.strict-tag-seq (NW.cw-funˡ sˢ (proj₂ t⊑)) ★⇒★)) ,
    NW.strict-tag-seq (NW.cw-funˡ sˢ (proj₂ t⊑)) ★⇒★ ,
    shape-sequence-widening
      (shape-fun s-shape t-shape)
      shape-tag-fun
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))

  coerce-down-fun-star-shape :
    ∀ {μ Δ Σ Φ A B} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) →
    (q : Φ ∣ Δ ⊢ B ⊑ ★ ⊣ Δ) →
    Σ[ c ∈ Coercion ]
      (μ ∣ Δ ∣ Σ ⊢ c ∶ ★ ⊒ A ⇒ B) ×
      NW.StrictNarrowing c ×
      (narrowing ⊢ᶜ c ⦂ ⌊ tagᵢ p ⇛ q ⌋)
  coerce-down-fun-star-shape ℓ shapes p q
      with up-star-shape-view ℓ shapes p
         | down-star-shape-view ℓ shapes q
  coerce-down-fun-star-shape ℓ shapes p q
      | up★-shape-id refl refl | down★-shape-id refl refl =
    ((★ ⇒ ★) ？ᶜ) ,
    (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl , NW.untag ★⇒★) ,
    NW.strict-untag ★⇒★ ,
    shape-untag-fun
  coerce-down-fun-star-shape ℓ shapes p q
      | up★-shape-id refl refl
      | down★-shape-strict {c = t}
          t⊒ tˢ t-shape =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (idᶜ ★ ↦ᶜ t)) ,
    (cast-seq
      (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
      (cast-fun (cast-id wf★ refl) (proj₁ t⊒)) ,
     NW.strictⁿ→narrow
       (NW.strict-untag-seq ★⇒★ (NW.cn-funʳ NW.id★ tˢ))) ,
    NW.strict-untag-seq ★⇒★ (NW.cn-funʳ NW.id★ tˢ) ,
    shape-sequence-narrowing
      shape-untag-fun
      (shape-fun shape-id-star t-shape)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-down-fun-star-shape ℓ shapes p q
      | up★-shape-strict {c = s}
          s⊑ sˢ s-shape
      | down★-shape-id refl refl =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (s ↦ᶜ idᶜ ★)) ,
    (cast-seq
      (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
      (cast-fun (proj₁ s⊑) (cast-id wf★ refl)) ,
     NW.strictⁿ→narrow
       (NW.strict-untag-seq ★⇒★ (NW.cn-funˡ sˢ NW.id★))) ,
    NW.strict-untag-seq ★⇒★ (NW.cn-funˡ sˢ NW.id★) ,
    shape-sequence-narrowing
      shape-untag-fun
      (shape-fun s-shape shape-id-star)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-down-fun-star-shape ℓ shapes p q
      | up★-shape-strict {c = s}
          s⊑ sˢ s-shape
      | down★-shape-strict {c = t}
          t⊒ tˢ t-shape =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (s ↦ᶜ t)) ,
    (cast-seq
      (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl)
      (cast-fun (proj₁ s⊑) (proj₁ t⊒)) ,
     NW.strictⁿ→narrow
       (NW.strict-untag-seq ★⇒★
         (NW.cn-funˡ sˢ (proj₂ t⊒)))) ,
    NW.strict-untag-seq ★⇒★
      (NW.cn-funˡ sˢ (proj₂ t⊒)) ,
    shape-sequence-narrowing
      shape-untag-fun
      (shape-fun s-shape t-shape)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))

  coerce-up-nu-star-shape-core :
    ∀ {μ Δ Σ Φ A} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    GenSafeShape A →
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) →
    UpNuStarShapeCore {μ = μ} {Σ = Σ} p
  coerce-up-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      with down-star-shape-view ℓ shapes p
         | up-star-shape-view ℓ shapes q
  coerce-up-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | down★-shape-id refl refl | up★-shape-id refl refl =
    upν★-shape-core
      (cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
       NW.cross (NW.id★ NW.↦ NW.id★))
      (NW.safe-fun NW.id★ NW.id★)
      (shape-fun shape-id-star shape-id-star)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-up-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | down★-shape-id refl refl
      | up★-shape-strict {c = t}
          t⊑ tˢ t-shape =
    upν★-shape-core
      (cast-fun (cast-id wf★ refl) (proj₁ t⊑) ,
       NW.cross (NW.id★ NW.↦ proj₂ t⊑))
      (NW.safe-fun NW.id★ (proj₂ t⊑))
      (shape-fun shape-id-star t-shape)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-up-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | down★-shape-strict {c = s}
          s⊒ sˢ s-shape
      | up★-shape-id refl refl =
    upν★-shape-core
      (cast-fun (proj₁ s⊒) (cast-id wf★ refl) ,
       NW.cross (proj₂ s⊒ NW.↦ NW.id★))
      (NW.safe-fun (proj₂ s⊒) NW.id★)
      (shape-fun s-shape shape-id-star)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-up-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | down★-shape-strict {c = s}
          s⊒ sˢ s-shape
      | up★-shape-strict {c = t}
          t⊑ tˢ t-shape =
    upν★-shape-core
      (cast-fun (proj₁ s⊒) (proj₁ t⊑) ,
       NW.cross (proj₂ s⊒ NW.↦ proj₂ t⊑))
      (NW.safe-fun (proj₂ s⊒) (proj₂ t⊑))
      (shape-fun s-shape t-shape)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-up-nu-star-shape-core ℓ shapes shape-all
      (νᵢ safe occ p)
      with coerce-up-nu-star-shape-core ℓ
             (ShapeRealizesᴺᵂ-ν-inst shapes)
             (nonVar-occurs→genSafeShape safe occ)
             (⊑-target-liftνᵢ p)
  coerce-up-nu-star-shape-core ℓ shapes shape-all
      (νᵢ safe occ p)
      | upν★-shape-core {c = c} {s = s}
          c⊑ cᵍ c-shape comp =
    upν★-shape-core
      (cast-inst (wf⇒ wf★ wf★) occ (proj₁ c⊑) , NW.inst cᵍ)
      (NW.safe-inst cᵍ)
      (shape-inst c-shape)
      (subst
        (λ r →
          (νˢ s) ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ r)
        (cong νˢ_ (shape-target-liftνᵢ p))
        (comp-ν comp))

  coerce-down-nu-star-shape-core :
    ∀ {μ Δ Σ Φ A} →
    Label →
    ShapeRealizesᴺᵂ μ Δ Σ Φ →
    GenSafeShape A →
    (p : Φ ∣ Δ ⊢ A ⊑ ★ ⊣ Δ) →
    DownNuStarShapeCore {μ = μ} {Σ = Σ} p
  coerce-down-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      with up-star-shape-view ℓ shapes p
         | down-star-shape-view ℓ shapes q
  coerce-down-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | up★-shape-id refl refl | down★-shape-id refl refl =
    downν★-shape-core
      (cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
       NW.cross (NW.id★ NW.↦ NW.id★))
      (NW.safe-fun NW.id★ NW.id★)
      (shape-fun shape-id-star shape-id-star)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-down-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | up★-shape-id refl refl
      | down★-shape-strict {c = t}
          t⊒ tˢ t-shape =
    downν★-shape-core
      (cast-fun (cast-id wf★ refl) (proj₁ t⊒) ,
       NW.cross (NW.id★ NW.↦ proj₂ t⊒))
      (NW.safe-fun NW.id★ (proj₂ t⊒))
      (shape-fun shape-id-star t-shape)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-down-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | up★-shape-strict {c = s}
          s⊑ sˢ s-shape
      | down★-shape-id refl refl =
    downν★-shape-core
      (cast-fun (proj₁ s⊑) (cast-id wf★ refl) ,
       NW.cross (proj₂ s⊑ NW.↦ NW.id★))
      (NW.safe-fun (proj₂ s⊑) NW.id★)
      (shape-fun s-shape shape-id-star)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-down-nu-star-shape-core ℓ shapes shape-fun
      (tagᵢ p ⇛ q)
      | up★-shape-strict {c = s}
          s⊑ sˢ s-shape
      | down★-shape-strict {c = t}
          t⊒ tˢ t-shape =
    downν★-shape-core
      (cast-fun (proj₁ s⊑) (proj₁ t⊒) ,
       NW.cross (proj₂ s⊑ NW.↦ proj₂ t⊒))
      (NW.safe-fun (proj₂ s⊑) (proj₂ t⊒))
      (shape-fun s-shape t-shape)
      (comp-↦-tag
        (compose-target-star-right-id★ p)
        (compose-target-star-right-id★ q))
  coerce-down-nu-star-shape-core ℓ shapes shape-all
      (νᵢ safe occ p)
      with coerce-down-nu-star-shape-core ℓ
             (ShapeRealizesᴺᵂ-ν-gen shapes)
             (nonVar-occurs→genSafeShape safe occ)
             (⊑-target-liftνᵢ p)
  coerce-down-nu-star-shape-core ℓ shapes shape-all
      (νᵢ safe occ p)
      | downν★-shape-core {c = c} {s = s}
          c⊒ cᵍ c-shape comp =
    downν★-shape-core
      (cast-gen (wf⇒ wf★ wf★) occ (proj₁ c⊒) , NW.gen cᵍ)
      (NW.safe-gen cᵍ)
      (shape-gen c-shape)
      (subst
        (λ r →
          (νˢ s) ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ r)
        (cong νˢ_ (shape-target-liftνᵢ p))
        (comp-ν comp))

coerce-upʷ-shape-idᵢ :
  ∀ {Δ C A} →
  Label →
  (p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
  Σ[ c ∈ Coercion ]
    (id-onlyᵈ ∣ Δ ∣ [] ⊢ c ∶ C ⊑ A) ×
    (widening ⊢ᶜ c ⦂ ⌊ p ⌋)
coerce-upʷ-shape-idᵢ {Δ = Δ} ℓ p =
  coerce-upʷ-shapeᵐ ℓ
    (realizes-idᵢᴺᵂ-id-only-shapes Δ) p

coerce-downⁿ-shape-idᵢ :
  ∀ {Δ C A} →
  Label →
  (p : idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ) →
  Σ[ c ∈ Coercion ]
    (id-onlyᵈ ∣ Δ ∣ [] ⊢ c ∶ A ⊒ C) ×
    (narrowing ⊢ᶜ c ⦂ ⌊ p ⌋)
coerce-downⁿ-shape-idᵢ {Δ = Δ} ℓ p =
  coerce-downⁿ-shapeᵐ ℓ
    (realizes-idᵢᴺᵂ-id-only-shapes Δ) p

------------------------------------------------------------------------
-- Coercion synthesis from imprecision
------------------------------------------------------------------------

mutual
  coerce-upᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    idTyAllowed μ A ≡ true →
    Realizesᵐ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ C =⇒ A
  coerce-upᵐ ℓ wf★ wf★ ok r id★ =
    idᶜ ★ , cast-id wf★ refl
  coerce-upᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY ok r (idˣ X⊑Y) =
    realizes-xx-up r X⊑Y
  coerce-upᵐ {C = ‵ ι} ℓ wfBase wfBase ok r idι =
    idᶜ (‵ ι) , cast-id wfBase refl
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      with idTyAllowed μ A′ in okA′ | idTyAllowed μ B′ in okB′
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true
      with coerce-downᵐ ℓ hA hA′ okA′ r p
         | coerce-upᵐ ℓ hB hB′ okB′ r q
  coerce-upᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true | s , s⊢ | t , t⊢ =
    (s ↦ᶜ t) , cast-fun s⊢ t⊢
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | false | b
  coerce-upᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | true | false
  coerce-upᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      with coerce-upᵐ ℓ hA hB ok (Realizes-∀ⁱ r) p
  coerce-upᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      | c , c⊢ =
    `∀ᶜ c , cast-all c⊢
  coerce-upᵐ {C = ‵ ι} ℓ wfBase wf★ ok r (tag ι) =
    ((‵ ι) !ᶜ) , cast-tag wfBase (‵ ι) refl
  coerce-upᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇛_ p q)
      with coerce-downᵐ ℓ hA wf★ refl r p
         | coerce-upᵐ ℓ hB wf★ refl r q
  coerce-upᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇛_ p q)
      | s , s⊢ | t , t⊢ =
    ((s ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    cast-seq (cast-fun s⊢ t⊢) (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl)
  coerce-upᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-star-up r X⊑★
  coerce-upᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν safe occ p)
      with coerce-upᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-inst {μ = μ} {B = B} ok)
             (Realizes-ν-inst ℓ r)
             p
  coerce-upᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν safe occ p)
      | c , c⊢ =
    instᶜ B c , cast-inst hB occ c⊢

  coerce-downᵐ :
    ∀ {μ Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    idTyAllowed μ A ≡ true →
    Realizesᵐ μ Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ C
  coerce-downᵐ ℓ wf★ wf★ ok r id★ =
    idᶜ ★ , cast-id wf★ refl
  coerce-downᵐ {C = ＇ X} {A = ＇ Y} ℓ hX hY ok r (idˣ X⊑Y) =
    realizes-xx-down r X⊑Y
  coerce-downᵐ {C = ‵ ι} ℓ wfBase wfBase ok r idι =
    idᶜ (‵ ι) , cast-id wfBase refl
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      with idTyAllowed μ A′ in okA′ | idTyAllowed μ B′ in okB′
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true
      with coerce-upᵐ ℓ hA hA′ okA′ r p
         | coerce-downᵐ ℓ hB hB′ okB′ r q
  coerce-downᵐ ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) ok r (p ↦ q)
      | true | true | s , s⊢ | t , t⊢ =
    (s ↦ᶜ t) , cast-fun s⊢ t⊢
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | false | b
  coerce-downᵐ {μ = μ} {A = A′ ⇒ B′} ℓ
      (wf⇒ hA hB) (wf⇒ hA′ hB′) () r (p ↦ q)
      | true | false
  coerce-downᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      with coerce-downᵐ ℓ hA hB ok (Realizes-∀ⁱ r) p
  coerce-downᵐ ℓ (wf∀ hA) (wf∀ hB) ok r (∀ⁱ p)
      | c , c⊢ =
    `∀ᶜ c , cast-all c⊢
  coerce-downᵐ {C = ‵ ι} ℓ wfBase wf★ ok r (tag ι) =
    ((‵ ι) ？ᶜ) , cast-untag wfBase (‵ ι) refl
  coerce-downᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇛_ p q)
      with coerce-upᵐ ℓ hA wf★ refl r p
         | coerce-downᵐ ℓ hB wf★ refl r q
  coerce-downᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇛_ p q)
      | s , s⊢ | t , t⊢ =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (s ↦ᶜ t)) ,
    cast-seq (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl) (cast-fun s⊢ t⊢)
  coerce-downᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-star-down r X⊑★
  coerce-downᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν safe occ p)
      with coerce-downᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-gen {μ = μ} {B = B} ok)
             (Realizes-ν-gen ℓ r)
             p
  coerce-downᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν safe occ p)
      | c , c⊢ =
    genᶜ B c , cast-gen hB occ c⊢

coerce-up :
  ∀ {Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  Realizes Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ C =⇒ A
coerce-up {A = A} ℓ hC hA r p =
  result
  where
    result : Σ[ c ∈ Coercion ] _ ∣ _ ⊢ c ∶ _ =⇒ A
    result with coerce-upᵐ ℓ hC hA (idTyAllowed-id-only A) r p
    result | c , c⊢ = c , id-onlyᵈ , c⊢

coerce-down :
  ∀ {Δ Σ Φ C A} →
  (ℓ : Label) →
  WfTy Δ C →
  WfTy Δ A →
  Realizes Δ Σ Φ →
  Φ ⊢ C ⊑ A →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ A =⇒ C
coerce-down {A = A} ℓ hC hA r p =
  result
  where
    result : Σ[ c ∈ Coercion ] _ ∣ _ ⊢ c ∶ A =⇒ _
    result with coerce-downᵐ ℓ hC hA (idTyAllowed-id-only A) r p
    result | c , c⊢ = c , id-onlyᵈ , c⊢
