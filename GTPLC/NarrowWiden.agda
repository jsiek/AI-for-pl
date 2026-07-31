module NarrowWiden where

-- File Charter:
--   * Defines one-context narrowing and widening for GTPLC coercions.
--   * Characterizes a kind of normal form for coercions.
--   * Indexes both relations by a coercion, type context, type store,
--     and mode environment.
--   * Equates bundled narrowings by their coercion components.
--   * Includes store-indexed seal and unseal rules.
--   * Provides bundled notation and proofs of ordinary coercion typing.

open import Data.Bool using (true)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import Coercions

------------------------------------------------------------------------
-- One-context coercion-indexed narrowing and widening
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⦂_⊑_
infix 4 _∣_∣_⊢_⦂_⊒_

mutual

  ----------------------------------------------------------------------
  -- Widening
  ----------------------------------------------------------------------

  data _∣_∣_⊢_⦂_⊑_ (μ : ModeEnv) (Δ : TyCtx) (Σ : TyStore) :
      Coercion → Ty → Ty → Set where

    idᵃ : ∀ {A} (a : Atom A)
      → WfTy Δ A
        --------------------------
      → μ ∣ Δ ∣ Σ ⊢ id ⦂ A ⊑ A

    _↦_ : ∀ {c d A A′ B B′}
      → μ ∣ Δ ∣ Σ ⊢ c ⦂ A′ ⊒ A
      → μ ∣ Δ ∣ Σ ⊢ d ⦂ B ⊑ B′
        -------------------------------------------
      → μ ∣ Δ ∣ Σ ⊢ c ↦ d ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

    ∀ʷ_ : ∀ {c A B}
      → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ⊑ B
        --------------------------------------
      → μ ∣ Δ ∣ Σ ⊢ `∀ c ⦂ (`∀ A) ⊑ (`∀ B)

    tag : ∀ {A} (G : Tag)
      → WfTag Δ G
      → tagAllowed μ G ≡ true
      → G ꞉ A
        ----------------------------
      → μ ∣ Δ ∣ Σ ⊢ G ! ⦂ A ⊑ ★

    -- See [rationale](Rationale.md#canonical-sequence-association).
    tag-seq : ∀ {c A B} (G : Tag)
      → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
      → WfTag Δ G
      → tagAllowed μ G ≡ true
      → G ꞉ B
      → NonVar A
      → A ≢ B
        ----------------------------------
      → μ ∣ Δ ∣ Σ ⊢ (c ︔ (G !)) ⦂ A ⊑ ★

    unseal : ∀ {X A}
      → X < Δ
      → WfTy Δ A
      → (X , A) ∈ Σ
      → sealModeAllowed (μ X) ≡ true
        ----------------------------------
      → μ ∣ Δ ∣ Σ ⊢ unseal X ⦂ ＇ X ⊑ A

    unseal-seq : ∀ {X c A B}
      → X < Δ
      → (X , A) ∈ Σ
      → sealModeAllowed (μ X) ≡ true
      → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
      → A ≢ B
        ----------------------------------------
      → μ ∣ Δ ∣ Σ ⊢ (unseal X ︔ c) ⦂ ＇ X ⊑ B

    -- See [rationale](Rationale.md#gen-inst-side-conditions).
    inst : ∀ {c A B}
      → NonVar A
      → zero ∈ᵗ A
      → WfTy Δ B
      → instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
          ⊢ c ⦂ A ⊑ ⇑ᵗ B
      → B ≢ ★
        -----------------------------------
      → μ ∣ Δ ∣ Σ ⊢ inst c ⦂ (`∀ A) ⊑ B

  ----------------------------------------------------------------------
  -- Narrowing
  ----------------------------------------------------------------------

  data _∣_∣_⊢_⦂_⊒_ (μ : ModeEnv) (Δ : TyCtx) (Σ : TyStore) :
      Coercion → Ty → Ty → Set where

    idᵃ : ∀ {A} (a : Atom A)
      → WfTy Δ A
        --------------------------
      → μ ∣ Δ ∣ Σ ⊢ id ⦂ A ⊒ A

    _↦_ : ∀ {c d A A′ B B′}
      → μ ∣ Δ ∣ Σ ⊢ c ⦂ A′ ⊑ A
      → μ ∣ Δ ∣ Σ ⊢ d ⦂ B ⊒ B′
        -------------------------------------------
      → μ ∣ Δ ∣ Σ ⊢ c ↦ d ⦂ (A ⇒ B) ⊒ (A′ ⇒ B′)

    ∀ⁿ_ : ∀ {c A B}
      → extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ⊒ B
        --------------------------------------
      → μ ∣ Δ ∣ Σ ⊢ `∀ c ⦂ (`∀ A) ⊒ (`∀ B)

    untag : ∀ {B} (G : Tag)
      → WfTag Δ G
      → tagAllowed μ G ≡ true
      → G ꞉ B
        ----------------------------
      → μ ∣ Δ ∣ Σ ⊢ G ？ ⦂ ★ ⊒ B

    -- See [rationale](Rationale.md#canonical-sequence-association).
    untag-seq : ∀ {c A B} (G : Tag)
      → WfTag Δ G
      → tagAllowed μ G ≡ true
      → G ꞉ A
      → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
      → NonVar B
      → A ≢ B
        ----------------------------------
      → μ ∣ Δ ∣ Σ ⊢ ((G ？) ︔ c) ⦂ ★ ⊒ B

    seal : ∀ {X A}
      → X < Δ
      → WfTy Δ A
      → (X , A) ∈ Σ
      → sealModeAllowed (μ X) ≡ true
        --------------------------------
      → μ ∣ Δ ∣ Σ ⊢ seal X ⦂ A ⊒ ＇ X

    seal-seq : ∀ {X c A B}
      → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
      → X < Δ
      → (X , B) ∈ Σ
      → sealModeAllowed (μ X) ≡ true
      → A ≢ B
        --------------------------------------
      → μ ∣ Δ ∣ Σ ⊢ (c ︔ seal X) ⦂ A ⊒ ＇ X

    -- See [rationale](Rationale.md#gen-inst-side-conditions).
    gen : ∀ {c A B}
      → NonVar A
      → zero ∈ᵗ A
      → WfTy Δ B
      → genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ⦂ ⇑ᵗ B ⊒ A
      → B ≢ ★
        ---------------------------------
      → μ ∣ Δ ∣ Σ ⊢ gen c ⦂ B ⊒ (`∀ A)

------------------------------------------------------------------------
-- Bundled notation
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⊑_
infix 4 _∣_∣_⊢_⊒_
infix 4 _∣_⊢_⦂_⊑_
infix 4 _∣_⊢_⦂_⊒_
infix 4 _∣_⊢_⊑_
infix 4 _∣_⊢_⊒_

_∣_∣_⊢_⊑_ : ModeEnv → TyCtx → TyStore → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ A ⊑ B =
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B

_∣_∣_⊢_⊒_ : ModeEnv → TyCtx → TyStore → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ A ⊒ B =
  Σ[ c ∈ Coercion ] μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B

_∣_⊢_⦂_⊑_ : TyCtx → TyStore → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ⦂ A ⊑ B =
  Σ[ μ ∈ ModeEnv ] μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B

_∣_⊢_⦂_⊒_ : TyCtx → TyStore → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ⦂ A ⊒ B =
  Σ[ μ ∈ ModeEnv ] μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B

_∣_⊢_⊑_ : TyCtx → TyStore → Ty → Ty → Set
Δ ∣ Σ ⊢ A ⊑ B =
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ⦂ A ⊑ B

_∣_⊢_⊒_ : TyCtx → TyStore → Ty → Ty → Set
Δ ∣ Σ ⊢ A ⊒ B =
  Σ[ c ∈ Coercion ] Δ ∣ Σ ⊢ c ⦂ A ⊒ B

------------------------------------------------------------------------
-- Narrowing equivalence
------------------------------------------------------------------------

infix 4 _≐ⁿ_

_≐ⁿ_ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → Set
p ≐ⁿ q = proj₁ p ≡ proj₁ q

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

tag-type-wf : ∀ {Δ G A}
  → WfTag Δ G
  → G ꞉ A
  → WfTy Δ A
tag-type-wf (wfTagVar X<Δ) (tag-var X) = wfVar X<Δ
tag-type-wf wfTagBase (tag-base ι) = wfBase
tag-type-wf wf★⇒★ tag-fun = wf⇒ wf★ wf★

mutual

  ⊑-src-wf : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → WfTy Δ A
  ⊑-src-wf (idᵃ _ hA) = hA
  ⊑-src-wf (p ↦ q) = wf⇒ (⊒-tgt-wf p) (⊑-src-wf q)
  ⊑-src-wf (∀ʷ p) = wf∀ (⊑-src-wf p)
  ⊑-src-wf (tag G hG _ G꞉A) = tag-type-wf hG G꞉A
  ⊑-src-wf (tag-seq G p _ _ _ _ _) = ⊑-src-wf p
  ⊑-src-wf (unseal X<Δ _ _ _) = wfVar X<Δ
  ⊑-src-wf (unseal-seq X<Δ _ _ _ _) = wfVar X<Δ
  ⊑-src-wf (inst _ _ _ p _) = wf∀ (⊑-src-wf p)

  ⊑-tgt-wf : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → WfTy Δ B
  ⊑-tgt-wf (idᵃ _ hA) = hA
  ⊑-tgt-wf (p ↦ q) = wf⇒ (⊒-src-wf p) (⊑-tgt-wf q)
  ⊑-tgt-wf (∀ʷ p) = wf∀ (⊑-tgt-wf p)
  ⊑-tgt-wf (tag _ _ _ _) = wf★
  ⊑-tgt-wf (tag-seq _ _ _ _ _ _ _) = wf★
  ⊑-tgt-wf (unseal _ hA _ _) = hA
  ⊑-tgt-wf (unseal-seq _ _ _ p _) = ⊑-tgt-wf p
  ⊑-tgt-wf (inst _ _ hB _ _) = hB

  ⊒-src-wf : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → WfTy Δ A
  ⊒-src-wf (idᵃ _ hA) = hA
  ⊒-src-wf (p ↦ q) = wf⇒ (⊑-tgt-wf p) (⊒-src-wf q)
  ⊒-src-wf (∀ⁿ p) = wf∀ (⊒-src-wf p)
  ⊒-src-wf (untag _ _ _ _) = wf★
  ⊒-src-wf (untag-seq _ _ _ _ _ _ _) = wf★
  ⊒-src-wf (seal _ hA _ _) = hA
  ⊒-src-wf (seal-seq p _ _ _ _) = ⊒-src-wf p
  ⊒-src-wf (gen _ _ hB _ _) = hB

  ⊒-tgt-wf : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → WfTy Δ B
  ⊒-tgt-wf (idᵃ _ hA) = hA
  ⊒-tgt-wf (p ↦ q) = wf⇒ (⊑-src-wf p) (⊒-tgt-wf q)
  ⊒-tgt-wf (∀ⁿ p) = wf∀ (⊒-tgt-wf p)
  ⊒-tgt-wf (untag G hG _ G꞉B) = tag-type-wf hG G꞉B
  ⊒-tgt-wf (untag-seq _ _ _ _ p _ _) = ⊒-tgt-wf p
  ⊒-tgt-wf (seal X<Δ _ _ _) = wfVar X<Δ
  ⊒-tgt-wf (seal-seq _ X<Δ _ _ _) = wfVar X<Δ
  ⊒-tgt-wf (gen _ _ _ p _) = wf∀ (⊒-tgt-wf p)

⊑-wf : ∀ {μ Δ Σ c A B}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → WfTy Δ A × WfTy Δ B
⊑-wf p = ⊑-src-wf p , ⊑-tgt-wf p

⊒-wf : ∀ {μ Δ Σ c A B}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
  → WfTy Δ A × WfTy Δ B
⊒-wf p = ⊒-src-wf p , ⊒-tgt-wf p

------------------------------------------------------------------------
-- Narrowing and widening imply ordinary coercion typing
------------------------------------------------------------------------

mutual

  widening-typing : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
    → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  widening-typing (idᵃ _ hA) = cast-id hA
  widening-typing (p ↦ q) =
    cast-fun (narrowing-typing p) (widening-typing q)
  widening-typing (∀ʷ p) = cast-all (widening-typing p)
  widening-typing (tag G hG allowed G꞉A) =
    cast-tag hG allowed G꞉A
  widening-typing (tag-seq G p hG allowed G꞉B _ _) =
    cast-seq (widening-typing p) (cast-tag hG allowed G꞉B)
  widening-typing (unseal _ hA X,A∈Σ allowed) =
    cast-unseal hA X,A∈Σ allowed
  widening-typing (unseal-seq _ X,A∈Σ allowed p _) =
    cast-seq
      (cast-unseal (⊑-src-wf p) X,A∈Σ allowed)
      (widening-typing p)
  widening-typing (inst _ zero∈A hB p _) =
    cast-inst hB zero∈A (widening-typing p)

  narrowing-typing : ∀ {μ Δ Σ c A B}
    → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
    → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
  narrowing-typing (idᵃ _ hA) = cast-id hA
  narrowing-typing (p ↦ q) =
    cast-fun (widening-typing p) (narrowing-typing q)
  narrowing-typing (∀ⁿ p) = cast-all (narrowing-typing p)
  narrowing-typing (untag G hG allowed G꞉B) =
    cast-untag hG allowed G꞉B
  narrowing-typing (untag-seq G hG allowed G꞉A p _ _) =
    cast-seq
      (cast-untag hG allowed G꞉A)
      (narrowing-typing p)
  narrowing-typing (seal _ hA X,A∈Σ allowed) =
    cast-seal hA X,A∈Σ allowed
  narrowing-typing (seal-seq p _ X,B∈Σ allowed _) =
    cast-seq
      (narrowing-typing p)
      (cast-seal (⊒-tgt-wf p) X,B∈Σ allowed)
  narrowing-typing (gen _ zero∈A hB p _) =
    cast-gen hB zero∈A (narrowing-typing p)

------------------------------------------------------------------------
-- Smart sequence wrappers
------------------------------------------------------------------------

wrap-unseal : ∀ {μ Δ Σ X c A B}
  → X < Δ
  → (X , A) ∈ Σ
  → sealModeAllowed (μ X) ≡ true
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → ∃[ d ] μ ∣ Δ ∣ Σ ⊢ d ⦂ ＇ X ⊑ B
wrap-unseal {X = X} {A = A} {B = B}
    X<Δ X,A∈Σ allowed p with A ≟Ty B
wrap-unseal {X = X} {A = A}
    X<Δ X,A∈Σ allowed p | yes refl =
  unseal X , unseal X<Δ (⊑-tgt-wf p) X,A∈Σ allowed
wrap-unseal {X = X} {c = c}
    X<Δ X,A∈Σ allowed p | no A≢B =
  (unseal X ︔ c) , unseal-seq X<Δ X,A∈Σ allowed p A≢B

wrap-seal : ∀ {μ Δ Σ X c A B}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
  → X < Δ
  → (X , B) ∈ Σ
  → sealModeAllowed (μ X) ≡ true
  → ∃[ d ] μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊒ ＇ X
wrap-seal {X = X} {A = A} {B = B}
    p X<Δ X,B∈Σ allowed with A ≟Ty B
wrap-seal {X = X} {A = A}
    p X<Δ X,A∈Σ allowed | yes refl =
  seal X , seal X<Δ (⊒-src-wf p) X,A∈Σ allowed
wrap-seal {X = X} {c = c}
    p X<Δ X,B∈Σ allowed | no A≢B =
  (c ︔ seal X) , seal-seq p X<Δ X,B∈Σ allowed A≢B

wrap-tag-nonvar : ∀ {μ Δ Σ c A B G}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → WfTag Δ G
  → tagAllowed μ G ≡ true
  → G ꞉ B
  → NonVar A
  → ∃[ d ] μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊑ ★
wrap-tag-nonvar {A = A} {B = B} p hG allowed G꞉B nonvarA
    with A ≟Ty B
wrap-tag-nonvar {G = G} p hG allowed G꞉B nonvarA | yes refl =
  G ! , tag G hG allowed G꞉B
wrap-tag-nonvar {c = c} {G = G} p hG allowed G꞉B nonvarA
    | no A≢B =
  (c ︔ (G !)) , tag-seq G p hG allowed G꞉B nonvarA A≢B

wrap-tag : ∀ {μ Δ Σ c A B G}
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊑ B
  → WfTag Δ G
  → tagAllowed μ G ≡ true
  → G ꞉ B
  → ∃[ d ] μ ∣ Δ ∣ Σ ⊢ d ⦂ A ⊑ ★
wrap-tag {A = ＇ X} {G = G} (idᵃ (＇ .X) hA) hG allowed G꞉A =
  G ! , tag G hG allowed G꞉A
wrap-tag {A = ＇ X} (tag H hH H-ok H꞉A) hG allowed ()
wrap-tag {A = ＇ X} {G = G} (unseal X<Δ hB X,B∈Σ seal-ok)
    hG tag-ok G꞉B =
  wrap-unseal X<Δ X,B∈Σ seal-ok (tag G hG tag-ok G꞉B)
wrap-tag {A = ＇ X} (unseal-seq X<Δ X,A∈Σ seal-ok p A≢B)
    hG tag-ok G꞉B with wrap-tag p hG tag-ok G꞉B
wrap-tag {A = ＇ X} (unseal-seq X<Δ X,A∈Σ seal-ok p A≢B)
    hG tag-ok G꞉B | d , p′ =
  wrap-unseal X<Δ X,A∈Σ seal-ok p′
wrap-tag {A = ‵ ι} p hG allowed G꞉B =
  wrap-tag-nonvar p hG allowed G꞉B nonvar-base
wrap-tag {A = ★} p hG allowed G꞉B =
  wrap-tag-nonvar p hG allowed G꞉B nonvar-star
wrap-tag {A = A ⇒ B} p hG allowed G꞉C =
  wrap-tag-nonvar p hG allowed G꞉C nonvar-fun
wrap-tag {A = `∀ A} p hG allowed G꞉B =
  wrap-tag-nonvar p hG allowed G꞉B nonvar-all

wrap-untag-nonvar : ∀ {μ Δ Σ c A B G}
  → WfTag Δ G
  → tagAllowed μ G ≡ true
  → G ꞉ A
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
  → NonVar B
  → ∃[ d ] μ ∣ Δ ∣ Σ ⊢ d ⦂ ★ ⊒ B
wrap-untag-nonvar {A = A} {B = B} hG allowed G꞉A p nonvarB
    with A ≟Ty B
wrap-untag-nonvar {G = G} hG allowed G꞉A p nonvarB | yes refl =
  G ？ , untag G hG allowed G꞉A
wrap-untag-nonvar {c = c} {G = G} hG allowed G꞉A p nonvarB
    | no A≢B =
  (G ？) ︔ c , untag-seq G hG allowed G꞉A p nonvarB A≢B

wrap-untag : ∀ {μ Δ Σ c A B G}
  → WfTag Δ G
  → tagAllowed μ G ≡ true
  → G ꞉ A
  → μ ∣ Δ ∣ Σ ⊢ c ⦂ A ⊒ B
  → ∃[ d ] μ ∣ Δ ∣ Σ ⊢ d ⦂ ★ ⊒ B
wrap-untag {B = ＇ X} {G = G} hG allowed G꞉A
    (idᵃ (＇ .X) hA) =
  G ？ , untag G hG allowed G꞉A
wrap-untag {B = ＇ X} hG allowed () (untag H hH H-ok H꞉B)
wrap-untag {B = ＇ X} {G = G} hG tag-ok G꞉A
    (seal X<Δ hA X,A∈Σ seal-ok) =
  wrap-seal (untag G hG tag-ok G꞉A) X<Δ X,A∈Σ seal-ok
wrap-untag {B = ＇ X} hG tag-ok G꞉A
    (seal-seq p X<Δ X,B∈Σ seal-ok A≢B)
    with wrap-untag hG tag-ok G꞉A p
wrap-untag {B = ＇ X} hG tag-ok G꞉A
    (seal-seq p X<Δ X,B∈Σ seal-ok A≢B) | d , p′ =
  wrap-seal p′ X<Δ X,B∈Σ seal-ok
wrap-untag {B = ‵ ι} hG allowed G꞉A p =
  wrap-untag-nonvar hG allowed G꞉A p nonvar-base
wrap-untag {B = ★} hG allowed G꞉A p =
  wrap-untag-nonvar hG allowed G꞉A p nonvar-star
wrap-untag {B = A ⇒ B} hG allowed G꞉C p =
  wrap-untag-nonvar hG allowed G꞉C p nonvar-fun
wrap-untag {B = `∀ A} hG allowed G꞉B p =
  wrap-untag-nonvar hG allowed G꞉B p nonvar-all
