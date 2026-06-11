module proof.CompileCoercions where

-- File Charter:
--   * Coercion synthesis for the GTSF compiler.
--   * Defines realization of imprecision-assumption contexts by target-store
--     coercions, plus `coerce-up` and `coerce-down` for type-imprecision proofs.
--   * This file deliberately does not choose maximal lower bounds; it only
--     turns a chosen imprecision witness into typed target coercions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s)
open import Data.Nat.Properties using (n≤1+n; ≤-refl)
open import Data.Product using (Σ-syntax; _,_)

open import Types
open import Store using (StoreIncl; StoreIncl-drop)
open import Coercions
  using
    ( Coercion
    ; Label
    ; _∣_⊢_∶_=⇒_
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
    ; _？_ to _？ᶜ_
    ; seal to sealᶜ
    ; unseal to unsealᶜ
    ; inst to instᶜ
    ; gen to genᶜ
    )
open import Imprecision
open import proof.CoercionProperties using (coercion-renameᵗ; coercion-weaken)
open import proof.TypeProperties
  using (TyRenameWf-suc; WfTy-weakenᵗ; renameᵗ-preserves-WfTy)

------------------------------------------------------------------------
-- Realizing imprecision assumptions as target coercions
------------------------------------------------------------------------

data Realizes (Δ : TyCtx) (Σ : Store) : ImpCtx → Set₁ where
  real-[] :
    Realizes Δ Σ []

  real-xx : ∀ {Φ X Y c d} →
    WfTy Δ (＇ X) →
    WfTy Δ (＇ Y) →
    Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ＇ Y →
    Δ ∣ Σ ⊢ d ∶ ＇ Y =⇒ ＇ X →
    Realizes Δ Σ Φ →
    Realizes Δ Σ ((X ˣ⊑ˣ Y) ∷ Φ)

  real-star : ∀ {Φ X c d} →
    WfTy Δ (＇ X) →
    Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ★ →
    Δ ∣ Σ ⊢ d ∶ ★ =⇒ ＇ X →
    Realizes Δ Σ Φ →
    Realizes Δ Σ ((X ˣ⊑★) ∷ Φ)

realizes-xx-up :
  ∀ {Δ Σ Φ X Y} →
  Realizes Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ＇ Y
realizes-xx-up (real-xx hX hY c⊢ d⊢ r) (here refl) = _ , c⊢
realizes-xx-up (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-xx-up r x∈
realizes-xx-up (real-star hX c⊢ d⊢ r) (here ())
realizes-xx-up (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-xx-up r x∈

realizes-xx-down :
  ∀ {Δ Σ Φ X Y} →
  Realizes Δ Σ Φ →
  (X ˣ⊑ˣ Y) ∈ Φ →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ ＇ Y =⇒ ＇ X
realizes-xx-down (real-xx hX hY c⊢ d⊢ r) (here refl) = _ , d⊢
realizes-xx-down (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-xx-down r x∈
realizes-xx-down (real-star hX c⊢ d⊢ r) (here ())
realizes-xx-down (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-xx-down r x∈

realizes-star-up :
  ∀ {Δ Σ Φ X} →
  Realizes Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ★
realizes-star-up (real-xx hX hY c⊢ d⊢ r) (here ())
realizes-star-up (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-star-up r x∈
realizes-star-up (real-star hX c⊢ d⊢ r) (here refl) = _ , c⊢
realizes-star-up (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-star-up r x∈

realizes-star-down :
  ∀ {Δ Σ Φ X} →
  Realizes Δ Σ Φ →
  (X ˣ⊑★) ∈ Φ →
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ ★ =⇒ ＇ X
realizes-star-down (real-xx hX hY c⊢ d⊢ r) (here ())
realizes-star-down (real-xx hX hY c⊢ d⊢ r) (there x∈) =
  realizes-star-down r x∈
realizes-star-down (real-star hX c⊢ d⊢ r) (here refl) = _ , d⊢
realizes-star-down (real-star hX c⊢ d⊢ r) (there x∈) =
  realizes-star-down r x∈

Realizes-store-weaken :
  ∀ {Δ Σ Σ′ Φ} →
  StoreIncl Σ Σ′ →
  Realizes Δ Σ Φ →
  Realizes Δ Σ′ Φ
Realizes-store-weaken incl real-[] = real-[]
Realizes-store-weaken incl (real-xx hX hY c⊢ d⊢ r) =
  real-xx
    hX
    hY
    (coercion-weaken ≤-refl incl c⊢)
    (coercion-weaken ≤-refl incl d⊢)
    (Realizes-store-weaken incl r)
Realizes-store-weaken incl (real-star hX c⊢ d⊢ r) =
  real-star
    hX
    (coercion-weaken ≤-refl incl c⊢)
    (coercion-weaken ≤-refl incl d⊢)
    (Realizes-store-weaken incl r)

Realizes-⇑ᵢ :
  ∀ {Δ Σ Φ} →
  Realizes Δ Σ Φ →
  Realizes (suc Δ) (⟰ᵗ Σ) (⇑ᵢ Φ)
Realizes-⇑ᵢ real-[] = real-[]
Realizes-⇑ᵢ (real-xx hX hY c⊢ d⊢ r) =
  real-xx
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (renameᵗ-preserves-WfTy hY TyRenameWf-suc)
    (coercion-renameᵗ TyRenameWf-suc c⊢)
    (coercion-renameᵗ TyRenameWf-suc d⊢)
    (Realizes-⇑ᵢ r)
Realizes-⇑ᵢ (real-star hX c⊢ d⊢ r) =
  real-star
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (coercion-renameᵗ TyRenameWf-suc c⊢)
    (coercion-renameᵗ TyRenameWf-suc d⊢)
    (Realizes-⇑ᵢ r)

var-to-shift :
  ∀ {Δ Σ X} →
  (ℓ : Label) →
  WfTy Δ (＇ X) →
  Σ[ c ∈ Coercion ] suc Δ ∣ Σ ⊢ c ∶ ＇ X =⇒ ＇ suc X
var-to-shift {Δ = Δ} {X = X} ℓ hX =
  (((＇ X) !ᶜ) ︔ᶜ ((＇ (suc X)) ？ᶜ ℓ)) ,
  cast-seq
    (cast-tag (WfTy-weakenᵗ hX (n≤1+n Δ)) (＇ X))
    (cast-untag (renameᵗ-preserves-WfTy hX TyRenameWf-suc) (＇ (suc X)))

var-from-shift :
  ∀ {Δ Σ X} →
  (ℓ : Label) →
  WfTy Δ (＇ X) →
  Σ[ c ∈ Coercion ] suc Δ ∣ Σ ⊢ c ∶ ＇ suc X =⇒ ＇ X
var-from-shift {Δ = Δ} {X = X} ℓ hX =
  (((＇ (suc X)) !ᶜ) ︔ᶜ ((＇ X) ？ᶜ ℓ)) ,
  cast-seq
    (cast-tag (renameᵗ-preserves-WfTy hX TyRenameWf-suc) (＇ (suc X)))
    (cast-untag (WfTy-weakenᵗ hX (n≤1+n Δ)) (＇ X))

Realizes-⇑ᴸᵢ :
  ∀ {Δ Σ Φ} →
  (ℓ : Label) →
  Realizes Δ Σ Φ →
  Realizes (suc Δ) (⟰ᵗ Σ) (⇑ᴸᵢ Φ)
Realizes-⇑ᴸᵢ ℓ real-[] = real-[]
Realizes-⇑ᴸᵢ {Δ = Δ} ℓ (real-xx hX hY c⊢ d⊢ r)
    with var-from-shift ℓ hY | var-to-shift ℓ hY
Realizes-⇑ᴸᵢ {Δ = Δ} ℓ (real-xx hX hY c⊢ d⊢ r)
    | y↓ , y↓⊢ | y↑ , y↑⊢ =
  real-xx
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (WfTy-weakenᵗ hY (n≤1+n Δ))
    (cast-seq (coercion-renameᵗ TyRenameWf-suc c⊢) y↓⊢)
    (cast-seq y↑⊢ (coercion-renameᵗ TyRenameWf-suc d⊢))
    (Realizes-⇑ᴸᵢ ℓ r)
Realizes-⇑ᴸᵢ ℓ (real-star hX c⊢ d⊢ r) =
  real-star
    (renameᵗ-preserves-WfTy hX TyRenameWf-suc)
    (coercion-renameᵗ TyRenameWf-suc c⊢)
    (coercion-renameᵗ TyRenameWf-suc d⊢)
    (Realizes-⇑ᴸᵢ ℓ r)

Realizes-∀ⁱ :
  ∀ {Δ Σ Φ} →
  Realizes Δ Σ Φ →
  Realizes (suc Δ) (⟰ᵗ Σ) ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
Realizes-∀ⁱ r =
  real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s))
    (cast-id (wfVar z<s))
    (Realizes-⇑ᵢ r)

Realizes-ν-inst :
  ∀ {Δ Σ Φ} →
  (ℓ : Label) →
  Realizes Δ Σ Φ →
  Realizes (suc Δ) ((zero , ★) ∷ ⟰ᵗ Σ) ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
Realizes-ν-inst ℓ r =
  real-star
    (wfVar z<s)
    (cast-unseal wf★ (here refl))
    (cast-seal wf★ (here refl))
    (Realizes-store-weaken StoreIncl-drop (Realizes-⇑ᴸᵢ ℓ r))

Realizes-ν-gen :
  ∀ {Δ Σ Φ} →
  (ℓ : Label) →
  Realizes Δ Σ Φ →
  Realizes (suc Δ) (⟰ᵗ Σ) ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
Realizes-ν-gen ℓ r =
  real-star
    (wfVar z<s)
    (cast-tag (wfVar z<s) (＇ zero))
    (cast-untag {ℓ = ℓ} (wfVar z<s) (＇ zero))
    (Realizes-⇑ᴸᵢ ℓ r)

realizes-idᵢ :
  ∀ Δ →
  Realizes Δ [] (idᵢ Δ)
realizes-idᵢ zero = real-[]
realizes-idᵢ (suc Δ) =
  real-xx
    (wfVar z<s)
    (wfVar z<s)
    (cast-id (wfVar z<s))
    (cast-id (wfVar z<s))
    (Realizes-⇑ᵢ (realizes-idᵢ Δ))

------------------------------------------------------------------------
-- Coercion synthesis from imprecision
------------------------------------------------------------------------

mutual
  coerce-up :
    ∀ {Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    Realizes Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ C =⇒ A
  coerce-up ℓ wf★ wf★ r id★ =
    idᶜ ★ , cast-id wf★
  coerce-up {C = ＇ X} {A = ＇ Y} ℓ hX hY r (idˣ X⊑Y) =
    realizes-xx-up r X⊑Y
  coerce-up {C = ‵ ι} ℓ wfBase wfBase r idι =
    idᶜ (‵ ι) , cast-id wfBase
  coerce-up ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      with coerce-down ℓ hA hA′ r p | coerce-up ℓ hB hB′ r q
  coerce-up ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      | s , s⊢ | t , t⊢ =
    (s ↦ᶜ t) , cast-fun s⊢ t⊢
  coerce-up ℓ (wf∀ {occ = occA} hA) (wf∀ {occ = occB} hB) r (∀ⁱ p)
      with coerce-up ℓ hA hB (Realizes-∀ⁱ r) p
  coerce-up ℓ (wf∀ {occ = occA} hA) (wf∀ {occ = occB} hB) r (∀ⁱ p)
      | c , c⊢ =
    `∀ᶜ c , cast-all {occA = occA} {occB = occB} c⊢
  coerce-up {C = ‵ ι} ℓ wfBase wf★ r (tag ι) =
    ((‵ ι) !ᶜ) , cast-tag wfBase (‵ ι)
  coerce-up ℓ (wf⇒ hA hB) wf★ r (tag_⇒_ p q)
      with coerce-down ℓ hA wf★ r p | coerce-up ℓ hB wf★ r q
  coerce-up ℓ (wf⇒ hA hB) wf★ r (tag_⇒_ p q)
      | s , s⊢ | t , t⊢ =
    ((s ↦ᶜ t) ︔ᶜ ((★ ⇒ ★) !ᶜ)) ,
    cast-seq (cast-fun s⊢ t⊢) (cast-tag (wf⇒ wf★ wf★) ★⇒★)
  coerce-up {C = ＇ X} ℓ hX wf★ r (tagˣ X⊑★) =
    realizes-star-up r X⊑★
  coerce-up {A = B} ℓ (wf∀ {occ = occA} hA) hB r (ν occ p)
      with coerce-up ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (Realizes-ν-inst ℓ r)
             p
  coerce-up {A = B} ℓ (wf∀ {occ = occA} hA) hB r (ν occ p)
      | c , c⊢ =
    instᶜ B c , cast-inst {occA = occ} hB c⊢

  coerce-down :
    ∀ {Δ Σ Φ C A} →
    (ℓ : Label) →
    WfTy Δ C →
    WfTy Δ A →
    Realizes Δ Σ Φ →
    Φ ⊢ C ⊑ A →
    Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ∶ A =⇒ C
  coerce-down ℓ wf★ wf★ r id★ =
    idᶜ ★ , cast-id wf★
  coerce-down {C = ＇ X} {A = ＇ Y} ℓ hX hY r (idˣ X⊑Y) =
    realizes-xx-down r X⊑Y
  coerce-down {C = ‵ ι} ℓ wfBase wfBase r idι =
    idᶜ (‵ ι) , cast-id wfBase
  coerce-down ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      with coerce-up ℓ hA hA′ r p | coerce-down ℓ hB hB′ r q
  coerce-down ℓ (wf⇒ hA hB) (wf⇒ hA′ hB′) r (p ↦ q)
      | s , s⊢ | t , t⊢ =
    (s ↦ᶜ t) , cast-fun s⊢ t⊢
  coerce-down ℓ (wf∀ {occ = occA} hA) (wf∀ {occ = occB} hB) r (∀ⁱ p)
      with coerce-down ℓ hA hB (Realizes-∀ⁱ r) p
  coerce-down ℓ (wf∀ {occ = occA} hA) (wf∀ {occ = occB} hB) r (∀ⁱ p)
      | c , c⊢ =
    `∀ᶜ c , cast-all {occA = occB} {occB = occA} c⊢
  coerce-down {C = ‵ ι} ℓ wfBase wf★ r (tag ι) =
    ((‵ ι) ？ᶜ ℓ) , cast-untag wfBase (‵ ι)
  coerce-down ℓ (wf⇒ hA hB) wf★ r (tag_⇒_ p q)
      with coerce-up ℓ hA wf★ r p | coerce-down ℓ hB wf★ r q
  coerce-down ℓ (wf⇒ hA hB) wf★ r (tag_⇒_ p q)
      | s , s⊢ | t , t⊢ =
    (((★ ⇒ ★) ？ᶜ ℓ) ︔ᶜ (s ↦ᶜ t)) ,
    cast-seq (cast-untag (wf⇒ wf★ wf★) ★⇒★) (cast-fun s⊢ t⊢)
  coerce-down {C = ＇ X} ℓ hX wf★ r (tagˣ X⊑★) =
    realizes-star-down r X⊑★
  coerce-down {A = B} ℓ (wf∀ {occ = occA} hA) hB r (ν occ p)
      with coerce-down ℓ
             hA
             (renameᵗ-preserves-WfTy hB TyRenameWf-suc)
             (Realizes-ν-gen ℓ r)
             p
  coerce-down {A = B} ℓ (wf∀ {occ = occA} hA) hB r (ν occ p)
      | c , c⊢ =
    genᶜ B c , cast-gen {occB = occ} hB c⊢
