module proof.CompileCoercions where

-- File Charter:
--   * Coercion synthesis for the GTSF compiler.
--   * Defines realization of imprecision-assumption contexts by target-store
--     coercions, plus `coerce-up` and `coerce-down` for type-imprecision proofs.
--   * This file deliberately does not choose maximal lower bounds; it only
--     turns a chosen imprecision witness into typed target coercions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; _,_)

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
    ; extᵈ
    ; genᵈ
    ; instᵈ
    ; Label
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
open import proof.CoercionProperties
  using
    ( ModeRename
    ; coercion-renameᵗᵐ
    ; coercion-weakenᵐ
    ; modeRename-idTyAllowed
    )
open import proof.TypeProperties
  using (TyRenameWf-suc; renameᵗ-preserves-WfTy)

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
  coerce-upᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      with coerce-downᵐ ℓ hA wf★ refl r p
         | coerce-upᵐ ℓ hB wf★ refl r q
  coerce-upᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      | s , s⊢ | t , t⊢ =
    ((s ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    cast-seq (cast-fun s⊢ t⊢) (cast-tag (wf⇒ wf★ wf★) ★⇒★ refl)
  coerce-upᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-star-up r X⊑★
  coerce-upᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      with coerce-upᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-inst {μ = μ} {B = B} ok)
             (Realizes-ν-inst ℓ r)
             p
  coerce-upᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
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
  coerce-downᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      with coerce-upᵐ ℓ hA wf★ refl r p
         | coerce-downᵐ ℓ hB wf★ refl r q
  coerce-downᵐ ℓ (wf⇒ hA hB) wf★ ok r (tag_⇒_ p q)
      | s , s⊢ | t , t⊢ =
    (((★ ⇒ ★) ？ᶜ) ︔ᶜ (s ↦ᶜ t)) ,
    cast-seq (cast-untag (wf⇒ wf★ wf★) ★⇒★ refl) (cast-fun s⊢ t⊢)
  coerce-downᵐ {C = ＇ X} ℓ hX wf★ ok r (tagˣ X⊑★) =
    realizes-star-down r X⊑★
  coerce-downᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
      with coerce-downᵐ ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (idTyAllowed-shift-gen {μ = μ} {B = B} ok)
             (Realizes-ν-gen ℓ r)
             p
  coerce-downᵐ {μ = μ} {A = B} ℓ (wf∀ hA) hB ok r (ν occ p)
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
