{-# OPTIONS --allow-unsolved-metas #-}

{-
  Term-narrowing examples for the Nu syntax.

  This file mechanizes the `⊒` examples from cambridge23.lagda.md that are
  expressible with the current TermNarrowing rules.  The examples focus on
  the K/id-style polymorphic narrowing derivations around `⊒Λ`; casted
  continuations are added as the coercion-equivalence side conditions mature.
  The narrowing derivations use the typed relation; endpoint typing witnesses
  are left implicit here so the examples remain focused on narrowing shape.
-}

module NarrowingExamples where

open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong; cong₂)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc; z<s)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.Core.Properties.NarrowWidenProperties using (StoreDetWf)
open import proof.Core.Properties.TermNarrowingProperties using (cast+⊒cast+-derivedᵗ)

------------------------------------------------------------------------
-- Shared syntax from cambridge23 Examples 1 and 6
------------------------------------------------------------------------

c★ : Term
c★ = $ (κℕ 0) ⟨ (‵ `ℕ) ! ⟩

var0-fun : Coercion
var0-fun =
  ((＇ 0) !) ↦ ((＇ 0) ？)

base-fun : Base → Coercion
base-fun ι =
  ((‵ ι) !) ↦ ((‵ ι) ？)

star-seal-fun : Coercion
star-seal-fun =
  (unseal 0 ★) ↦ (seal ★ 0)

base-seal-fun : Base → Coercion
base-seal-fun ι =
  (unseal 0 (‵ ι) ︔ ((‵ ι) !))
    ↦ (((‵ ι) ？) ︔ seal (‵ ι) 0)

base-seal-step-fun : Base → Coercion
base-seal-step-fun ι =
  (unseal 0 (‵ ι)) ↦ (seal (‵ ι) 0)

base-untag : Base → Coercion
base-untag ι = (‵ ι) ？

base-store-det : ∀ {Δ ι} →
  StoreDetWf (suc Δ) ((0 , ‵ ι) ∷ [])
base-store-det =
  record
    { at = record
        { bound = λ { (here refl) → z<s }
        ; wfTy = λ { (here refl) → wfBase }
        }
    ; wfOlder = λ { (here refl) → wfBase }
    ; unique = λ { (here refl) (here refl) → refl }
    }

empty-store-narrowing : ∀ {Δ} →
  Δ ⊢ [] ꞉ [] ⊒ˢ []
empty-store-narrowing = ⊒ˢ-nil

empty-store-det : ∀ {Δ} →
  StoreDetWf Δ []
empty-store-det =
  record
    { at = record
        { bound = λ ()
        ; wfTy = λ ()
        }
    ; wfOlder = λ ()
    ; unique = λ ()
    }

id★-store-narrowing : ∀ {Δ} →
  Δ ⊢ (0 ꞉ id ★) ∷ [] ꞉ ((0 , ★) ∷ []) ⊒ˢ ((0 , ★) ∷ [])
id★-store-narrowing =
  ⊒ˢ-both wf★ wf★ (id-onlyᵈ , (cast-id wf★ refl , id★)) ⊒ˢ-nil

star-store-det : StoreDetWf 1 ((0 , ★) ∷ [])
star-store-det =
  record
    { at = record
        { bound = λ { (here refl) → z<s }
        ; wfTy = λ { (here refl) → wf★ }
        }
    ; wfOlder = λ { (here refl) → wf★ }
    ; unique = λ { (here refl) (here refl) → refl }
    }

idBase-store-narrowing : ∀ {Δ ι} →
  Δ ⊢ (0 ꞉ id (‵ ι)) ∷ [] ꞉
      ((0 , ‵ ι) ∷ []) ⊒ˢ ((0 , ‵ ι) ∷ [])
idBase-store-narrowing {ι = ι} =
  ⊒ˢ-both wfBase wfBase
    (id-onlyᵈ , (cast-id wfBase refl , cross (id-‵ ι)))
    ⊒ˢ-nil

base-untag-store-narrowing : ∀ {Δ ι} →
  Δ ⊢ (0 ꞉ base-untag ι) ∷ [] ꞉
      ((0 , ★) ∷ []) ⊒ˢ ((0 , ‵ ι) ∷ [])
base-untag-store-narrowing {ι = ι} =
  ⊒ˢ-both wf★ wfBase
    (tag-or-idᵈ ,
      (cast-untag wfBase (‵ ι) refl , untag (‵ ι)))
    ⊒ˢ-nil

base-right-store-narrowing : ∀ {Δ ι} →
  Δ ⊢ (0 ꞉= ‵ ι ⊒) ∷ [] ꞉ [] ⊒ˢ ((0 , ‵ ι) ∷ [])
base-right-store-narrowing =
  ⊒ˢ-right wfBase ⊒ˢ-nil

wf★⇒★ˢ : ∀ {Δ Σ} →
  WfTyˢ Δ Σ (★ ⇒ ★)
wf★⇒★ˢ = wf⇒ˢ wf★ˢ wf★ˢ

wf∀id0ˢ : ∀ {Δ Σ} →
  WfTyˢ Δ Σ (`∀ (＇ 0 ⇒ ＇ 0))
wf∀id0ˢ =
  wf∀ˢ (wf⇒ˢ (wfVarᵗ z<s) (wfVarᵗ z<s))

wf-poly-fun-endpoints : ∀ {Δ Σ} →
  EndpointWf Δ Σ (★ ⇒ ★) (`∀ (＇ 0 ⇒ ＇ 0))
wf-poly-fun-endpoints = wf★⇒★ˢ , wf∀id0ˢ

wf-var-fun-endpoints : ∀ {Δ Σ} →
  EndpointWf (suc Δ) Σ (★ ⇒ ★) (＇ 0 ⇒ ＇ 0)
wf-var-fun-endpoints =
  wf★⇒★ˢ , wf⇒ˢ (wfVarᵗ z<s) (wfVarᵗ z<s)

wf-store-var-fun-endpoints : ∀ {Δ Σ A} →
  EndpointWf Δ ((0 , A) ∷ Σ) (★ ⇒ ★) (＇ 0 ⇒ ＇ 0)
wf-store-var-fun-endpoints =
  wf★⇒★ˢ , wf⇒ˢ (wfVarˢ (here refl)) (wfVarˢ (here refl))

wf-base-store-var-fun-endpoints : ∀ {Δ Σ ι} →
  EndpointWf Δ ((0 , ‵ ι) ∷ Σ) (‵ ι ⇒ ‵ ι) (＇ 0 ⇒ ＇ 0)
wf-base-store-var-fun-endpoints =
  wf⇒ˢ wfBaseˢ wfBaseˢ ,
  wf⇒ˢ (wfVarˢ (here refl)) (wfVarˢ (here refl))

wf-base-fun-endpoints : ∀ {Δ Σ ι} →
  EndpointWf Δ Σ (★ ⇒ ★) (‵ ι ⇒ ‵ ι)
wf-base-fun-endpoints =
  wf★⇒★ˢ , wf⇒ˢ wfBaseˢ wfBaseˢ

wf★-base-endpoints : ∀ {Δ Σ ι} →
  EndpointWf Δ Σ ★ (‵ ι)
wf★-base-endpoints = wf★ˢ , wfBaseˢ

var0-fun-grammar : Narrowing var0-fun
var0-fun-grammar =
  cross (tag (＇ 0) ↦ untag (＇ 0))

var0-fun-safe : GenSafe var0-fun
var0-fun-safe =
  safe-fun (tag (＇ 0)) (untag (＇ 0))

var0-fun-typing :
  ∀ {μ Δ Σ} →
  WfTy Δ (＇ 0) →
  idTyAllowed μ (＇ 0) ≡ true →
  tagTyAllowed μ (＇ 0) ≡ true →
  μ ∣ Δ ∣ Σ ⊢ var0-fun ∶ (★ ⇒ ★) =⇒ (＇ 0 ⇒ ＇ 0)
var0-fun-typing hX id-ok tag-ok =
  cast-fun
    (cast-tag hX (＇ 0) tag-ok)
    (cast-untag hX (＇ 0) tag-ok)

var0-fun-narrowingᵐ :
  ∀ {Δ Σ} →
  tag-or-idᵈ ∣ suc Δ ∣ Σ
    ⊢ var0-fun ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
var0-fun-narrowingᵐ =
  var0-fun-typing {μ = tag-or-idᵈ} (wfVar z<s) refl refl ,
  var0-fun-grammar

var0-fun-narrowing :
  ∀ {Δ Σ} →
  suc Δ ∣ Σ ⊢ var0-fun ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
var0-fun-narrowing = tag-or-idᵈ , var0-fun-narrowingᵐ

id★-fun-narrowingᵐ : ∀ {μ Δ Σ} →
  μ ∣ Δ ∣ Σ ⊢ id ★ ↦ id ★ ∶ (★ ⇒ ★) ⊒ (★ ⇒ ★)
id★-fun-narrowingᵐ =
  cast-fun (cast-id wf★ refl) (cast-id wf★ refl) ,
  cross (id★ ↦ id★)

id-base-fun-narrowingᵐ : ∀ {μ Δ Σ ι} →
  μ ∣ Δ ∣ Σ ⊢ id (‵ ι) ↦ id (‵ ι) ∶
    (‵ ι ⇒ ‵ ι) ⊒ (‵ ι ⇒ ‵ ι)
id-base-fun-narrowingᵐ {ι = ι} =
  cast-fun (cast-id wfBase refl) (cast-id wfBase refl) ,
  cross (cross (id-‵ ι) ↦ cross (id-‵ ι))

id★-narrowingᵐ : ∀ {μ Δ Σ} →
  μ ∣ Δ ∣ Σ ⊢ id ★ ∶ ★ ⊒ ★
id★-narrowingᵐ =
  cast-id wf★ refl , id★

id-base-narrowingᵐ : ∀ {μ Δ Σ ι} →
  μ ∣ Δ ∣ Σ ⊢ id (‵ ι) ∶ ‵ ι ⊒ ‵ ι
id-base-narrowingᵐ {ι = ι} =
  cast-id wfBase refl , cross (id-‵ ι)

id-var0-fun-narrowingᵐ : ∀ {μ Δ Σ} →
  idTyAllowed μ (＇ 0) ≡ true →
  μ ∣ suc Δ ∣ Σ
    ⊢ id (＇ 0) ↦ id (＇ 0) ∶ (＇ 0 ⇒ ＇ 0) ⊒ (＇ 0 ⇒ ＇ 0)
id-var0-fun-narrowingᵐ id-ok =
  cast-fun (cast-id (wfVar z<s) id-ok) (cast-id (wfVar z<s) id-ok) ,
  cross (cross (id-＇ 0) ↦ cross (id-＇ 0))

forall-id-var0-fun-narrowingᵐ : ∀ {μ Δ Σ} →
  μ ∣ Δ ∣ Σ
    ⊢ `∀ (id (＇ 0) ↦ id (＇ 0)) ∶
      `∀ (＇ 0 ⇒ ＇ 0) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
forall-id-var0-fun-narrowingᵐ {μ = μ} {Δ = Δ} {Σ = Σ} =
  cast-all
    (proj₁
      (id-var0-fun-narrowingᵐ {μ = extᵈ μ} {Δ = Δ} {Σ = ⟰ᵗ Σ}
        refl)) ,
  cross
    (`∀
      (proj₂
        (id-var0-fun-narrowingᵐ {μ = extᵈ μ} {Δ = Δ} {Σ = ⟰ᵗ Σ}
          refl)))

poly-fun-narrowingᵐ : ∀ {Δ Σ} →
  id-onlyᵈ ∣ Δ ∣ Σ ⊢ gen (★ ⇒ ★) var0-fun ∶
    (★ ⇒ ★) ⊒ (`∀ (＇ 0 ⇒ ＇ 0))
poly-fun-narrowingᵐ =
  cast-gen (wf⇒ wf★ wf★) refl
    (var0-fun-typing {μ = genᵈ id-onlyᵈ} (wfVar z<s) refl refl) ,
  gen var0-fun-safe

poly-fun-narrowing : ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ gen (★ ⇒ ★) var0-fun ∶
    (★ ⇒ ★) ⊒ (`∀ (＇ 0 ⇒ ＇ 0))
poly-fun-narrowing = id-onlyᵈ , poly-fun-narrowingᵐ

base-fun-grammar : ∀ {ι} →
  Narrowing (base-fun ι)
base-fun-grammar {ι = ι} =
  cross (tag (‵ ι) ↦ untag (‵ ι))

base-fun-narrowingᵐ : ∀ {μ Δ Σ ι} →
  μ ∣ Δ ∣ Σ ⊢ base-fun ι ∶ (★ ⇒ ★) ⊒ (‵ ι ⇒ ‵ ι)
base-fun-narrowingᵐ {ι = ι} =
    (cast-fun
      (cast-tag wfBase (‵ ι) refl)
      (cast-untag wfBase (‵ ι) refl) ,
     base-fun-grammar)

base-fun-narrowing : ∀ {Δ Σ ι} →
  Δ ∣ Σ ⊢ base-fun ι ∶ (★ ⇒ ★) ⊒ (‵ ι ⇒ ‵ ι)
base-fun-narrowing =
  tag-or-idᵈ , base-fun-narrowingᵐ

base-seal-step-fun-grammar : ∀ {ι} →
  Narrowing (base-seal-step-fun ι)
base-seal-step-fun-grammar {ι = ι} =
  cross (unsealʷ 0 (‵ ι) ↦ sealⁿ (‵ ι) 0)

base-seal-step-fun-narrowingᵐ : ∀ {Δ Σ ι} →
  seal-or-idᵈ ∣ Δ ∣ ((0 , ‵ ι) ∷ Σ)
    ⊢ base-seal-step-fun ι ∶ (‵ ι ⇒ ‵ ι) ⊒ (＇ 0 ⇒ ＇ 0)
base-seal-step-fun-narrowingᵐ {ι = ι} =
  cast-fun
    (cast-unseal wfBase (here refl) refl)
    (cast-seal wfBase (here refl) refl) ,
  base-seal-step-fun-grammar

star-seal-fun-narrowingᵐ : ∀ {Δ Σ} →
  seal-or-idᵈ ∣ Δ ∣ ((0 , ★) ∷ Σ) ⊢ star-seal-fun ∶
    (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
star-seal-fun-narrowingᵐ =
  cast-fun
    (cast-unseal wf★ (here refl) refl)
    (cast-seal wf★ (here refl) refl) ,
  cross (unsealʷ 0 ★ ↦ sealⁿ ★ 0)

star-seal-fun-narrowing : ∀ {Δ Σ} →
  Δ ∣ ((0 , ★) ∷ Σ) ⊢ star-seal-fun ∶
    (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
star-seal-fun-narrowing = seal-or-idᵈ , star-seal-fun-narrowingᵐ

base-untag-grammar : ∀ {ι} →
  Narrowing (base-untag ι)
base-untag-grammar {ι = ι} = untag (‵ ι)

base-untag-narrowingᵐ : ∀ {μ Δ Σ ι} →
  μ ∣ Δ ∣ Σ ⊢ base-untag ι ∶ ★ ⊒ (‵ ι)
base-untag-narrowingᵐ {ι = ι} =
  cast-untag wfBase (‵ ι) refl ,
  base-untag-grammar

base-untag-narrowing : ∀ {Δ Σ ι} →
  Δ ∣ Σ ⊢ base-untag ι ∶ ★ ⊒ (‵ ι)
base-untag-narrowing = tag-or-idᵈ , base-untag-narrowingᵐ

id★-cast : ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id ★ ∶ᶜ ★ ⊒ ★
id★-cast =
  id★-narrowingᵐ {μ = tag-or-idᵈ}

id-base-cast : ∀ {Δ Σ ι} →
  Δ ∣ Σ ⊢ id (‵ ι) ∶ᶜ ‵ ι ⊒ ‵ ι
id-base-cast =
  id-base-narrowingᵐ {μ = tag-or-idᵈ}

id-var0-cast : ∀ {Δ Σ} →
  suc Δ ∣ Σ ⊢ id (＇ 0) ∶ᶜ ＇ 0 ⊒ ＇ 0
id-var0-cast =
  cast-id (wfVar z<s) refl , cross (id-＇ 0)

var0-untag-cast : ∀ {Δ Σ} →
  suc Δ ∣ Σ ⊢ (＇ 0) ？ ∶ᶜ ★ ⊒ ＇ 0
var0-untag-cast =
  cast-untag (wfVar z<s) (＇ 0) refl ,
  untag (＇ 0)

id★-fun-cast : ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id ★ ↦ id ★ ∶ᶜ (★ ⇒ ★) ⊒ (★ ⇒ ★)
id★-fun-cast =
  id★-fun-narrowingᵐ {μ = tag-or-idᵈ}

id-base-fun-cast : ∀ {Δ Σ ι} →
  Δ ∣ Σ ⊢ id (‵ ι) ↦ id (‵ ι) ∶ᶜ
    (‵ ι ⇒ ‵ ι) ⊒ (‵ ι ⇒ ‵ ι)
id-base-fun-cast =
  id-base-fun-narrowingᵐ {μ = tag-or-idᵈ}

id-var0-fun-cast : ∀ {Δ Σ} →
  suc Δ ∣ Σ ⊢ id (＇ 0) ↦ id (＇ 0) ∶ᶜ
    (＇ 0 ⇒ ＇ 0) ⊒ (＇ 0 ⇒ ＇ 0)
id-var0-fun-cast =
  id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl

var0-fun-cast : ∀ {Δ Σ} →
  suc Δ ∣ Σ ⊢ var0-fun ∶ᶜ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
var0-fun-cast =
  var0-fun-narrowingᵐ

forall-id-var0-fun-cast : ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ `∀ (id (＇ 0) ↦ id (＇ 0)) ∶ᶜ
    `∀ (＇ 0 ⇒ ＇ 0) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
forall-id-var0-fun-cast =
  forall-id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ}

poly-fun-cast : ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ gen (★ ⇒ ★) var0-fun ∶ᶜ
    (★ ⇒ ★) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
poly-fun-cast =
  cast-gen (wf⇒ wf★ wf★) refl
    (var0-fun-typing {μ = genᵈ tag-or-idᵈ} (wfVar z<s) refl refl) ,
  gen var0-fun-safe

base-fun-cast : ∀ {Δ Σ ι} →
  Δ ∣ Σ ⊢ base-fun ι ∶ᶜ (★ ⇒ ★) ⊒ (‵ ι ⇒ ‵ ι)
base-fun-cast =
  base-fun-narrowingᵐ {μ = tag-or-idᵈ}

base-untag-cast : ∀ {Δ Σ ι} →
  Δ ∣ Σ ⊢ base-untag ι ∶ᶜ ★ ⊒ ‵ ι
base-untag-cast =
  base-untag-narrowingᵐ {μ = tag-or-idᵈ}

------------------------------------------------------------------------
-- Example 1
------------------------------------------------------------------------

-- cambridge23 line 266 / line 406.
ex1-⊒Λ :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0) ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★) var0-fun ⦂ _ ⊒ _
ex1-⊒Λ =
  ⊒Λᵗ poly-fun-cast
    (ƛ⊒ƛᵗ var0-fun-cast (x⊒xᵗ var0-untag-cast Z))

-- cambridge23 line 272 side condition (i), at the raw-composition level.
ex1-line272-⨟ :
  gen (★ ⇒ ★) var0-fun
    ⨟ `∀ (id (＇ 0) ↦ id (＇ 0))
    ≡ gen (★ ⇒ ★) var0-fun
ex1-line272-⨟ =
  trans
    (⨟-gen-∀ (★ ⇒ ★) var0-fun (id (＇ 0) ↦ id (＇ 0)))
    (cong (gen (★ ⇒ ★))
      (trans
        (⨟-↦ ((＇ 0) !) ((＇ 0) ？) (id (＇ 0)) (id (＇ 0)))
        refl))

ex1-line272-≈ : ∀ {Δ} →
  Δ ∣ [] ⊢
    gen (★ ⇒ ★) var0-fun
      ≈ proj₁ (_⨟ⁿ_ {wfΣ = empty-store-det}
          poly-fun-narrowingᵐ
          (forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ}))
      ∶ (★ ⇒ ★) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
ex1-line272-≈ =
  endpointsⁿ refl refl refl refl
    empty-store-narrowing
    wf-poly-fun-endpoints
    wf-poly-fun-endpoints
    poly-fun-narrowing
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = empty-store-det}
      poly-fun⊒ forall-id-var0-fun⊒))
  where
    poly-fun⊒ = poly-fun-narrowingᵐ

    forall-id-var0-fun⊒ =
      forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ}

ex1-cast- :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★) var0-fun ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0)) ⦂ _ ⊒ _
ex1-cast- =
  cast-⊒ᵗ forall-id-var0-fun-cast empty-store-det
    poly-fun-narrowingᵐ
    (forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ})
    ex1-line272-≈ ex1-⊒Λ

ex1-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★) var0-fun ⟩
        ⟨ inst (★ ⇒ ★)
          ((seal ★ 0) ↦ (unseal 0 ★)) ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★) var0-fun ⦂ _ ⊒ _
ex1-initial =
  cast+⊒ᵗ
    {p = `∀ (id (＇ 0) ↦ id (＇ 0))}
    {r = gen (★ ⇒ ★) var0-fun}
    {t = gen (★ ⇒ ★) var0-fun}
    forall-id-var0-fun-cast poly-fun-cast empty-store-det
    poly-fun-narrowingᵐ
    (forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ})
    ex1-line272-≈ ex1-cast-

-- cambridge23 line 293 side condition (iii), at the raw-composition level.
ex1-line293-⨟ :
  var0-fun ⨟ (id (＇ 0) ↦ id (＇ 0)) ≡ var0-fun
ex1-line293-⨟ =
  trans
    (⨟-↦ ((＇ 0) !) ((＇ 0) ？) (id (＇ 0)) (id (＇ 0)))
    refl

ex1-line293-≈ :
  1 ∣ (0 ꞉ id ★) ∷ [] ⊢
    var0-fun
      ≈ proj₁ (_⨟ⁿ_ {wfΣ = star-store-det}
          var0-fun-narrowingᵐ
          (id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex1-line293-≈ =
  endpointsⁿ refl refl refl refl
    id★-store-narrowing
    wf-var-fun-endpoints
    wf-var-fun-endpoints
    var0-fun-narrowing
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = star-store-det}
      var0-fun⊒ id-var0-fun⊒))
  where
    var0-fun⊒ = var0-fun-narrowingᵐ

    id-var0-fun⊒ =
      id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl

ex1-line294-⨟ :
  star-seal-fun ⨟ (id (＇ 0) ↦ id (＇ 0)) ≡ star-seal-fun
ex1-line294-⨟ =
  trans
    (⨟-↦ (unseal 0 ★) (seal ★ 0) (id (＇ 0)) (id (＇ 0)))
    refl

ex1-line294-≈ :
  1 ∣ (0 ꞉ id ★) ∷ [] ⊢
    var0-fun
      ≈ proj₁ (_⨟ⁿ_ {wfΣ = star-store-det}
          star-seal-fun-narrowingᵐ
          (id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex1-line294-≈ =
  endpointsⁿ refl refl refl refl
    id★-store-narrowing
    wf-var-fun-endpoints
    wf-var-fun-endpoints
    var0-fun-narrowing
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = star-store-det}
      star-seal-fun⊒ id-var0-fun⊒))
  where
    star-seal-fun⊒ = star-seal-fun-narrowingᵐ

    id-var0-fun⊒ =
      id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl

ex1-inner-⊒Λ-premise :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ var0-fun ⦂ _ ⊒ _
ex1-inner-⊒Λ-premise =
  ƛ⊒ƛᵗ var0-fun-cast (x⊒xᵗ var0-untag-cast Z)

ex1-inner-cast- :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩
      ⊒ ƛ (` 0)
    ∶ id (＇ 0) ↦ id (＇ 0) ⦂ _ ⊒ _
ex1-inner-cast- =
  cast-⊒ᵗ id-var0-fun-cast star-store-det
    var0-fun-narrowingᵐ
    (id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl)
    ex1-line293-≈ ex1-inner-⊒Λ-premise

ex1-inner-cast+ :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩ ⟨ - star-seal-fun ⟩
      ⊒ ƛ (` 0)
    ∶ var0-fun ⦂ _ ⊒ _
ex1-inner-cast+ =
  cast+⊒ᵗ
    {p = id (＇ 0) ↦ id (＇ 0)}
    {r = var0-fun}
    {t = star-seal-fun}
    id-var0-fun-cast var0-fun-cast star-store-det
    star-seal-fun-narrowingᵐ
    (id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl)
    ex1-line294-≈ ex1-inner-cast-

ex1-split :
  1 ∣ (0 ꞉= ★ ⊒) ∷ (⊒ 1 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ ((＇ 1) !) ↦ ((＇ 1) ？) ⟩
        ⟨ - ((unseal 1 ★) ↦ (seal ★ 1)) ⟩
      ⊒ ƛ (` 0)
    ∶ var0-fun ⦂ _ ⊒ _
ex1-split =
  splitᵗ
    {N =
      (ƛ (` 0)) ⟨ var0-fun ⟩ ⟨ - star-seal-fun ⟩}
    {N′ = ƛ (` 0)}
    {p = var0-fun}
    {q = id ★}
    {A = ★}
    {α = 0}
    {αᵢ = 1}
    id★-cast
    var0-fun-cast
    ex1-inner-cast+

-- cambridge23 line 291: this is after three reduction steps from
-- `ex1-initial`, not after the first reduction step.
ex1-after-reduction :
  0 ∣ (⊒ 0 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ var0-fun ⟩
        ⟨ - star-seal-fun ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★) var0-fun ⦂ _ ⊒ _
ex1-after-reduction =
  ⊒Λᵗ poly-fun-cast ex1-split

------------------------------------------------------------------------
-- Example 2
------------------------------------------------------------------------

ex2-id :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id ★ ↦ id ★ ⦂ _ ⊒ _
ex2-id =
  ƛ⊒ƛᵗ id★-fun-cast (x⊒xᵗ id★-cast Z)

-- cambridge23 line 307, left-hand raw composition.
ex2-line307-left-⨟ :
  (id ★ ↦ id ★)
    ⨟ gen (★ ⇒ ★)
        var0-fun
    ≡ gen (★ ⇒ ★)
        var0-fun
ex2-line307-left-⨟ =
  trans
    (⨟-genʳ (id ★ ↦ id ★) (★ ⇒ ★)
      var0-fun)
    (cong (gen (★ ⇒ ★))
      (trans
        (⨟-↦ (id ★) (id ★) ((＇ 0) !) ((＇ 0) ？))
        refl))

ex2-line307-≈ :
  0 ∣ [] ⊢
    (id ★ ↦ id ★)
      ⨟ gen (★ ⇒ ★)
          var0-fun
      ≈ gen (★ ⇒ ★)
          var0-fun
          ⨟ `∀ (id (＇ 0) ↦ id (＇ 0))
      ∶ (★ ⇒ ★) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
ex2-line307-≈ rewrite ex2-line307-left-⨟ | ex1-line272-⨟ =
  endpointsⁿ refl refl refl refl
    empty-store-narrowing
    wf-poly-fun-endpoints
    wf-poly-fun-endpoints
    poly-fun-narrowing
    poly-fun-narrowing

ex2-line303-right-≈ :
  0 ∣ [] ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = empty-store-det}
      (id★-fun-narrowingᵐ {μ = id-onlyᵈ})
      poly-fun-narrowingᵐ)
      ≈ gen (★ ⇒ ★)
          var0-fun
      ∶ (★ ⇒ ★) ⊒ `∀ (＇ 0 ⇒ ＇ 0)
ex2-line303-right-≈ =
  endpointsⁿ refl refl refl refl
    empty-store-narrowing
    wf-poly-fun-endpoints
    wf-poly-fun-endpoints
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = empty-store-det}
      id★-fun⊒ poly-fun⊒))
    poly-fun-narrowing
  where
    id★-fun⊒ = id★-fun-narrowingᵐ {μ = id-onlyᵈ}

    poly-fun⊒ = poly-fun-narrowingᵐ

ex2-right-cast :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ƛ (` 0))
          ⟨ gen (★ ⇒ ★)
            var0-fun ⟩
    ∶ gen (★ ⇒ ★)
        var0-fun ⦂ _ ⊒ _
ex2-right-cast =
  ⊒cast-ᵗ id★-fun-cast poly-fun-cast empty-store-det
    (id★-fun-narrowingᵐ {μ = id-onlyᵈ})
    poly-fun-narrowingᵐ
    ex2-line303-right-≈ ex2-id

ex2-line303 :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          var0-fun ⟩
      ⊒ (ƛ (` 0))
          ⟨ gen (★ ⇒ ★)
            var0-fun ⟩
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0)) ⦂ _ ⊒ _
ex2-line303 =
  cast-⊒ᵗ forall-id-var0-fun-cast empty-store-det
    poly-fun-narrowingᵐ
    (forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ})
    ex1-line272-≈ ex2-right-cast

ex2-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          var0-fun ⟩
        ⟨ inst (★ ⇒ ★)
          ((seal ★ 0) ↦ (unseal 0 ★)) ⟩
      ⊒ (ƛ (` 0))
          ⟨ gen (★ ⇒ ★)
            var0-fun ⟩
    ∶ gen (★ ⇒ ★)
        var0-fun ⦂ _ ⊒ _
ex2-initial =
  cast+⊒ᵗ
    {p = `∀ (id (＇ 0) ↦ id (＇ 0))}
    {r = gen (★ ⇒ ★)
      var0-fun}
    {t = gen (★ ⇒ ★)
      var0-fun}
    forall-id-var0-fun-cast poly-fun-cast empty-store-det
    poly-fun-narrowingᵐ
    (forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ})
    ex1-line272-≈ ex2-line303

ex2-inner-id :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id ★ ↦ id ★ ⦂ _ ⊒ _
ex2-inner-id =
  ƛ⊒ƛᵗ id★-fun-cast (x⊒xᵗ id★-cast Z)

ex2-line316-left-⨟ :
  (id ★ ↦ id ★)
    ⨟ var0-fun
    ≡ var0-fun
ex2-line316-left-⨟ =
  trans
    (⨟-↦ (id ★) (id ★) ((＇ 0) !) ((＇ 0) ？))
    refl

ex2-line316-right-≈ :
  1 ∣ (0 ꞉ id ★) ∷ [] ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = star-store-det}
      (id★-fun-narrowingᵐ {μ = tag-or-idᵈ})
      var0-fun-narrowingᵐ)
      ≈ var0-fun
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex2-line316-right-≈ =
  endpointsⁿ refl refl refl refl
    id★-store-narrowing
    wf-var-fun-endpoints
    wf-var-fun-endpoints
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = star-store-det}
      id★-fun⊒ var0-fun⊒))
    var0-fun-narrowing
  where
    id★-fun⊒ = id★-fun-narrowingᵐ {μ = tag-or-idᵈ}

    var0-fun⊒ = var0-fun-narrowingᵐ

ex2-inner-right-cast :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ƛ (` 0)) ⟨ var0-fun ⟩
    ∶ var0-fun ⦂ _ ⊒ _
ex2-inner-right-cast =
  ⊒cast-ᵗ id★-fun-cast var0-fun-cast star-store-det
    (id★-fun-narrowingᵐ {μ = tag-or-idᵈ})
    var0-fun-narrowingᵐ
    ex2-line316-right-≈ ex2-inner-id

ex2-line316 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩
      ⊒ (ƛ (` 0)) ⟨ var0-fun ⟩
    ∶ id (＇ 0) ↦ id (＇ 0) ⦂ _ ⊒ _
ex2-line316 =
  cast-⊒ᵗ id-var0-fun-cast star-store-det
    var0-fun-narrowingᵐ
    (id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl)
    ex1-line293-≈ ex2-inner-right-cast

ex2-line318 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩ ⟨ - star-seal-fun ⟩
      ⊒ (ƛ (` 0)) ⟨ var0-fun ⟩
    ∶ var0-fun ⦂ _ ⊒ _
ex2-line318 =
  cast+⊒ᵗ
    {p = id (＇ 0) ↦ id (＇ 0)}
    {r = var0-fun}
    {t = star-seal-fun}
    id-var0-fun-cast var0-fun-cast star-store-det
    star-seal-fun-narrowingᵐ
    (id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl)
    ex1-line294-≈ ex2-line316

ex2-split :
  1 ∣ (0 ꞉= ★ ⊒) ∷ (⊒ 1 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ ((＇ 1) !) ↦ ((＇ 1) ？) ⟩
        ⟨ - ((unseal 1 ★) ↦ (seal ★ 1)) ⟩
      ⊒ (ƛ (` 0)) ⟨ var0-fun ⟩
    ∶ var0-fun ⦂ _ ⊒ _
ex2-split =
  splitᵗ
    {N =
      (ƛ (` 0)) ⟨ var0-fun ⟩ ⟨ - star-seal-fun ⟩}
    {N′ = (ƛ (` 0)) ⟨ var0-fun ⟩}
    {p = var0-fun}
    {q = id ★}
    {A = ★}
    {α = 0}
    {αᵢ = 1}
    id★-cast
    var0-fun-cast
    ex2-line318

-- cambridge23 line 320: as with Example 1, this is after the catch-up
-- reductions, not after the first reduction step.
ex2-after-reduction :
  0 ∣ (⊒ 0 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩ ⟨ - star-seal-fun ⟩
      ⊒ (ƛ (` 0)) ⟨ gen (★ ⇒ ★) var0-fun ⟩
    ∶ gen (★ ⇒ ★) var0-fun ⦂ _ ⊒ _
ex2-after-reduction =
  ⊒⟨ν⟩ᵗ poly-fun-cast (_ ↦ _) ex2-split

------------------------------------------------------------------------
-- Example 3
------------------------------------------------------------------------

ex3-line329 :
  1 ∣ (0 ꞉= ‵ `ℕ ⊒) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ (Λ (ƛ (` 0))) •
    ∶ var0-fun ⦂ _ ⊒ _
ex3-line329 =
  ⊒αᵗ {p = var0-fun} {A = ‵ `ℕ} refl var0-fun-cast
    (⊒Λᵗ
      {A = ★ ⇒ ★}
      {N = ƛ (` 0)}
      {V′ = ƛ (` 0)}
      {p = var0-fun}
      poly-fun-cast
      (ƛ⊒ƛᵗ var0-fun-cast (x⊒xᵗ var0-untag-cast Z)))

ex3-line329-extend :
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ (Λ (ƛ (` 0))) •
    ∶ var0-fun ⦂ _ ⊒ _
ex3-line329-extend =
  extendᵗ
    {M = ƛ (` 0)}
    {N′ = (Λ (ƛ (` 0))) •}
    {p = var0-fun}
    {q = id (‵ `ℕ)}
    {A = ‵ `ℕ}
    {B = ‵ `ℕ}
    {α = 0}
    id-base-cast
    var0-fun-cast
    ex3-line329

ex3-line331-⨟ :
  base-fun `ℕ
    ⨟ base-seal-step-fun `ℕ
    ≡ base-seal-fun `ℕ
ex3-line331-⨟ =
  trans
    (⨟-↦ ((‵ `ℕ) !) ((‵ `ℕ) ？)
      (unseal 0 (‵ `ℕ)) (seal (‵ `ℕ) 0))
    refl

ex3-line331-≈ :
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = base-store-det}
      (base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `ℕ})
      (base-seal-step-fun-narrowingᵐ {ι = `ℕ}))
      ≈ var0-fun
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex3-line331-≈ =
  endpointsⁿ refl refl refl refl
    idBase-store-narrowing
    wf-store-var-fun-endpoints
    wf-store-var-fun-endpoints
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = base-store-det}
      base-fun⊒ base-seal-step-fun⊒))
    var0-fun-narrowing
  where
    base-fun⊒ =
      base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `ℕ}

    base-seal-step-fun⊒ =
      base-seal-step-fun-narrowingᵐ {ι = `ℕ}

ex3-line331 :
  1 ∣ (0 ꞉ id (‵ `ℕ)) ∷ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ ((Λ (ƛ (` 0))) •)
          ⟨ - base-seal-step-fun `ℕ ⟩
    ∶ base-fun `ℕ ⦂ _ ⊒ _
ex3-line331 =
  ⊒cast+ᵗ
    {q = base-fun `ℕ}
    {r = var0-fun}
    {s = base-seal-step-fun `ℕ}
    base-fun-cast
    base-store-det
    (base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `ℕ})
    (base-seal-step-fun-narrowingᵐ {ι = `ℕ})
    ex3-line331-≈
    ex3-line329-extend

------------------------------------------------------------------------
-- Example 4
------------------------------------------------------------------------

ex4-poly-id :
  0 ∣ [] ∣ []
    ⊢ Λ (ƛ (` 0)) ⊒ Λ (ƛ (` 0))
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0)) ⦂ _ ⊒ _
ex4-poly-id =
  Λ⊒Λᵗ forall-id-var0-fun-cast (ƛ (` 0))
    (ƛ⊒ƛᵗ id-var0-fun-cast (x⊒xᵗ id-var0-cast Z))

ex4-initial :
  0 ∣ [] ∣ []
    ⊢ (Λ (ƛ (` 0)))
        ⟨ inst (★ ⇒ ★)
          ((seal ★ 0) ↦ (unseal 0 ★)) ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        var0-fun ⦂ _ ⊒ _
ex4-initial =
  cast+⊒ᵗ
    {p = `∀ (id (＇ 0) ↦ id (＇ 0))}
    {r = gen (★ ⇒ ★)
      var0-fun}
    {t = gen (★ ⇒ ★)
      var0-fun}
    forall-id-var0-fun-cast poly-fun-cast empty-store-det
    poly-fun-narrowingᵐ
    (forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ})
    ex1-line272-≈ ex4-poly-id

ex4-line352 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id (＇ 0) ↦ id (＇ 0) ⦂ _ ⊒ _
ex4-line352 =
  ƛ⊒ƛᵗ id-var0-fun-cast (x⊒xᵗ id-var0-cast Z)

ex4-line353 :
  1 ∣ (0 ꞉ id ★) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - star-seal-fun ⟩
      ⊒ ƛ (` 0)
    ∶ var0-fun ⦂ _ ⊒ _
ex4-line353 =
  cast+⊒ᵗ
    {p = id (＇ 0) ↦ id (＇ 0)}
    {r = var0-fun}
    {t = star-seal-fun}
    id-var0-fun-cast var0-fun-cast star-store-det
    star-seal-fun-narrowingᵐ
    (id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl)
    ex1-line294-≈ ex4-line352

ex4-split :
  1 ∣ (0 ꞉= ★ ⊒) ∷ (⊒ 1 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - ((unseal 1 ★) ↦ (seal ★ 1)) ⟩
      ⊒ ƛ (` 0)
    ∶ var0-fun ⦂ _ ⊒ _
ex4-split =
  splitᵗ
    {N =
      (ƛ (` 0))
        ⟨ - star-seal-fun ⟩}
    {N′ = ƛ (` 0)}
    {p = var0-fun}
    {q = id ★}
    {A = ★}
    {α = 0}
    {αᵢ = 1}
    id★-cast
    var0-fun-cast
    ex4-line353

-- cambridge23 Example 4, final displayed derivation after the ν̅ reduction
-- exposes the fresh seal variable.
ex4-after-reduction :
  0 ∣ (⊒ 0 ꞉=☆) ∷ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ - star-seal-fun ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        var0-fun ⦂ _ ⊒ _
ex4-after-reduction =
  ⊒Λᵗ poly-fun-cast ex4-split

------------------------------------------------------------------------
-- Example 5
------------------------------------------------------------------------

-- cambridge23 Example 5 uses a tagged value at one ground type as the
-- argument to a function expecting another ground type.  Here `c★` is tagged
-- at ℕ, so the function side below uses 𝔹 for the mismatching ground type.
ex5-line380-⨟ :
  (id ★ ↦ id ★)
    ⨟ base-fun `𝔹
    ≡ base-fun `𝔹
ex5-line380-⨟ =
  trans
    (⨟-↦ (id ★) (id ★) ((‵ `𝔹) !) ((‵ `𝔹) ？))
    refl

ex5-line380-≈ :
  0 ∣ [] ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = empty-store-det}
      (id★-fun-narrowingᵐ {μ = tag-or-idᵈ})
      (base-fun-narrowingᵐ {μ = tag-or-idᵈ} {ι = `𝔹}))
      ≈ base-fun `𝔹
      ∶ (★ ⇒ ★) ⊒ (‵ `𝔹 ⇒ ‵ `𝔹)
ex5-line380-≈ =
  endpointsⁿ refl refl refl refl
    empty-store-narrowing
    wf-base-fun-endpoints
    wf-base-fun-endpoints
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = empty-store-det}
      id★-fun⊒ base-fun⊒))
    base-fun-narrowing
  where
    id★-fun⊒ = id★-fun-narrowingᵐ {μ = tag-or-idᵈ}

    base-fun⊒ = base-fun-narrowingᵐ {μ = tag-or-idᵈ} {ι = `𝔹}

ex5-function-base :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ base-fun `𝔹 ⦂ _ ⊒ _
ex5-function-base =
  ƛ⊒ƛᵗ (base-fun-cast {ι = `𝔹})
    (x⊒xᵗ (base-untag-cast {ι = `𝔹}) Z)

-- cambridge23 Example 5, line 379, function-side premise.
ex5-function-cast :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ƛ (` 0))
          ⟨ - base-fun `𝔹 ⟩
    ∶ id ★ ↦ id ★ ⦂ _ ⊒ _
ex5-function-cast =
  ⊒cast+ᵗ
    {q = id ★ ↦ id ★}
    {r = base-fun `𝔹}
    {s = base-fun `𝔹}
    {A = ★ ⇒ ★}
    {B = ‵ `𝔹 ⇒ ‵ `𝔹}
    id★-fun-cast
    empty-store-det
    (id★-fun-narrowingᵐ {μ = tag-or-idᵈ})
    (base-fun-narrowingᵐ {μ = tag-or-idᵈ} {ι = `𝔹})
    ex5-line380-≈ ex5-function-base

-- cambridge23 Example 5, argument-side premise, using the barred two-sided
-- cast rule with `ℕ!` as the dual of `ℕ?;idℕ`.
ex5-c★ :
  0 ∣ [] ∣ []
    ⊢ c★ ⊒ c★ ∶ id ★ ⦂ _ ⊒ _
ex5-c★ =
  ⊒cast+ᵗ
    {q = id ★}
    {r = base-untag `ℕ}
    {s = base-untag `ℕ}
    id★-cast
    empty-store-det
    id★⊒
    base-untag⊒
    (endpointsⁿ refl refl refl refl
      empty-store-narrowing
      wf★-base-endpoints
      wf★-base-endpoints
      (_ , proj₂ (_⨟ⁿ_ {wfΣ = empty-store-det} id★⊒ base-untag⊒))
      base-untag-narrowing)
    (cast+⊒ᵗ
      {p = id (‵ `ℕ)}
      {r = base-untag `ℕ}
      {t = base-untag `ℕ}
      id-base-cast
      base-untag-cast
      empty-store-det
      base-untag⊒
      id-base⊒
      (endpointsⁿ refl refl refl refl
        empty-store-narrowing
        wf★-base-endpoints
        wf★-base-endpoints
        base-untag-narrowing
        (_ , proj₂ (_⨟ⁿ_ {wfΣ = empty-store-det}
          base-untag⊒ id-base⊒)))
      (κ⊒κᵗ (κℕ 0)))
  where
    id★⊒ = id★-narrowingᵐ {μ = tag-or-idᵈ}

    base-untag⊒ = base-untag-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ}

    id-base⊒ = id-base-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ}

-- cambridge23 Example 5, initial displayed derivation.
ex5-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0)) · c★
      ⊒ ((ƛ (` 0)) ⟨ - base-fun `𝔹 ⟩)
        · c★
    ∶ id ★ ⦂ _ ⊒ _
ex5-initial =
  ·⊒·ᵗ id★-fun-cast ex5-function-cast ex5-c★

-- cambridge23 Example 5, after the reductions to blame.
ex5-after-reduction :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0)) · c★ ⊒ blame ∶ id ★ ⦂ _ ⊒ _
ex5-after-reduction =
  ⊒blameᵗ id★-cast

------------------------------------------------------------------------
-- Example 6
------------------------------------------------------------------------

-- cambridge23 Example 6, line 403.
ex6-open-ν𝔹 :
  1 ∣ (0 ꞉= ‵ `𝔹 ⊒) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ (Λ (ƛ (` 0))) •
    ∶ var0-fun ⦂ _ ⊒ _
ex6-open-ν𝔹 =
  ⊒αᵗ {p = var0-fun} {A = ‵ `𝔹} refl var0-fun-cast
    (⊒Λᵗ
      {A = ★ ⇒ ★}
      {N = ƛ (` 0)}
      {V′ = ƛ (` 0)}
      {p = var0-fun}
      poly-fun-cast
      (ƛ⊒ƛᵗ var0-fun-cast (x⊒xᵗ var0-untag-cast Z)))

ex6-line405-⨟ :
  base-fun `𝔹
    ⨟ base-seal-step-fun `𝔹
    ≡ base-seal-fun `𝔹
ex6-line405-⨟ =
  trans
    (⨟-↦ ((‵ `𝔹) !) ((‵ `𝔹) ？)
      (unseal 0 (‵ `𝔹)) (seal (‵ `𝔹) 0))
    refl

-- cambridge23 Example 6, line 405 side condition (i), with the corrected
-- result `ι!→ι?`.  The seal/tag bridge reads identity-like evidence from the
-- exact `α:=ι` assumption.
ex6-line405-≈ :
  1 ∣ (0 ꞉= ‵ `𝔹 ⊒) ∷ [] ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = base-store-det}
      (base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `𝔹})
      (base-seal-step-fun-narrowingᵐ {ι = `𝔹}))
      ≈ var0-fun
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex6-line405-≈ =
  endpointsⁿ refl refl refl refl
    base-right-store-narrowing
    wf-var-fun-endpoints
    wf-var-fun-endpoints
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = base-store-det}
      base-fun⊒ base-seal-step-fun⊒))
    var0-fun-narrowing
  where
    base-fun⊒ =
      base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `𝔹}

    base-seal-step-fun⊒ =
      base-seal-step-fun-narrowingᵐ {ι = `𝔹}

-- cambridge23 Example 6, line 405.
ex6-line405 :
  1 ∣ (0 ꞉= ‵ `𝔹 ⊒) ∷ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ ((Λ (ƛ (` 0))) •)
          ⟨ - base-seal-step-fun `𝔹 ⟩
    ∶ base-fun `𝔹 ⦂ _ ⊒ _
ex6-line405 =
  ⊒cast+ᵗ
    {q = base-fun `𝔹}
    {r = var0-fun}
    {s = base-seal-step-fun `𝔹}
    (base-fun-cast {ι = `𝔹})
    base-store-det
    (base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `𝔹})
    (base-seal-step-fun-narrowingᵐ {ι = `𝔹})
    ex6-line405-≈
    ex6-open-ν𝔹

ex6-line407-ν :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ ν (‵ `𝔹)
          (((Λ (ƛ (` 0))) •)
            ⟨ - base-seal-step-fun `𝔹 ⟩)
          (⇑ᶜ (base-fun `𝔹))
    ∶ base-fun `𝔹 ⦂ _ ⊒ _
ex6-line407-ν =
  ⊒νᵗ (base-fun-cast {ι = `𝔹}) ex6-line405

-- cambridge23 Example 6, line 407 side condition (ii).
ex6-line407 :
  0 ∣ [] ∣ []
    ⊢ ƛ (` 0)
      ⊒ (ν (‵ `𝔹)
          (((Λ (ƛ (` 0))) •)
            ⟨ - base-seal-step-fun `𝔹 ⟩)
          (⇑ᶜ (base-fun `𝔹)))
          ⟨ - base-fun `𝔹 ⟩
    ∶ id ★ ↦ id ★ ⦂ _ ⊒ _
ex6-line407 =
  ⊒cast+ᵗ
    {q = id ★ ↦ id ★}
    {r = base-fun `𝔹}
    {s = base-fun `𝔹}
    {A = ★ ⇒ ★}
    {B = ‵ `𝔹 ⇒ ‵ `𝔹}
    id★-fun-cast
    empty-store-det
    (id★-fun-narrowingᵐ {μ = tag-or-idᵈ})
    (base-fun-narrowingᵐ {μ = tag-or-idᵈ} {ι = `𝔹})
    ex5-line380-≈
    ex6-line407-ν

ex6-initial :
  0 ∣ [] ∣ []
    ⊢ (ƛ (` 0)) · c★
      ⊒ ((ν (‵ `𝔹)
          (((Λ (ƛ (` 0))) •)
            ⟨ - base-seal-step-fun `𝔹 ⟩)
          (⇑ᶜ (base-fun `𝔹))
            ⟨ - base-fun `𝔹 ⟩)
        · c★)
    ∶ id ★ ⦂ _ ⊒ _
ex6-initial =
  ·⊒·ᵗ id★-fun-cast ex6-line407 ex5-c★

-- cambridge23 line 473.  This endpoint is independent of the casted
-- derivation above it because `⊒blame` relates any left term to blame.
ex6-blame :
  0 ∣ (0 ꞉= ‵ `ℕ ⊒) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) · c★ ⊒ blame ∶ id ★ ⦂ _ ⊒ _
ex6-blame =
  ⊒blameᵗ id★-cast

------------------------------------------------------------------------
-- Example 7
------------------------------------------------------------------------

-- cambridge25 Example 7, line 708 in the one-variable de Bruijn context
-- used by the following α-application.
ex7-line708 :
  1 ∣ [] ∣ []
    ⊢ ƛ (` 0) ⊒ Λ (ƛ (` 0))
    ∶ gen (★ ⇒ ★)
        var0-fun ⦂ _ ⊒ _
ex7-line708 =
  ⊒Λᵗ
    {A = ★ ⇒ ★}
    {N = ƛ (` 0)}
    {V′ = ƛ (` 0)}
    {p = var0-fun}
    poly-fun-cast
    (ƛ⊒ƛᵗ var0-fun-cast (x⊒xᵗ var0-untag-cast Z))

-- cambridge25 Example 7, line 710.
ex7-line710 :
  1 ∣ [] ∣ []
    ⊢ (ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          var0-fun ⟩
      ⊒ Λ (ƛ (` 0))
    ∶ `∀ (id (＇ 0) ↦ id (＇ 0)) ⦂ _ ⊒ _
ex7-line710 =
  cast-⊒ᵗ forall-id-var0-fun-cast empty-store-det
    poly-fun-narrowingᵐ
    (forall-id-var0-fun-narrowingᵐ {μ = id-onlyᵈ})
    ex1-line272-≈ ex7-line708

-- cambridge25 Example 7, line 712.
ex7-line712 : ∀ {ι} →
  2 ∣ (0 ꞉ id (‵ ι)) ∷ [] ∣ []
    ⊢ (⇑ᵗᵐ ((ƛ (` 0))
        ⟨ gen (★ ⇒ ★)
          var0-fun ⟩)) •
      ⊒ (⇑ᵗᵐ (Λ (ƛ (` 0)))) •
    ∶ id (＇ 0) ↦ id (＇ 0) ⦂ _ ⊒ _
ex7-line712 {ι = ι} =
  α⊒αᵗ {q = id (‵ ι)} refl
    id-base-cast id-var0-fun-cast ex7-line710

ex7-downcast-left-≈ : ∀ {Δ ι} →
  suc Δ ∣ (0 ꞉ id (‵ ι)) ∷ [] ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = base-store-det}
      (id-base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = ι})
      (base-seal-step-fun-narrowingᵐ {ι = ι}))
      ≈ base-seal-step-fun ι
      ∶ (‵ ι ⇒ ‵ ι) ⊒ (＇ 0 ⇒ ＇ 0)
ex7-downcast-left-≈ {ι = ι} =
  endpointsⁿ refl refl refl refl
    idBase-store-narrowing
    wf-base-store-var-fun-endpoints
    wf-base-store-var-fun-endpoints
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = base-store-det}
      id-base-fun⊒ base-seal-step-fun⊒))
    (seal-or-idᵈ , base-seal-step-fun⊒)
  where
    id-base-fun⊒ = id-base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = ι}

    base-seal-step-fun⊒ =
      base-seal-step-fun-narrowingᵐ {ι = ι}

ex7-downcast-right-≈ : ∀ {Δ ι} →
  suc Δ ∣ (0 ꞉ id (‵ ι)) ∷ [] ⊢
    base-seal-step-fun ι
      ≈ proj₁ (_⨟ⁿ_ {wfΣ = base-store-det}
          (base-seal-step-fun-narrowingᵐ {ι = ι})
          (id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl))
      ∶ (‵ ι ⇒ ‵ ι) ⊒ (＇ 0 ⇒ ＇ 0)
ex7-downcast-right-≈ {ι = ι} =
  endpointsⁿ refl refl refl refl
    idBase-store-narrowing
    wf-base-store-var-fun-endpoints
    wf-base-store-var-fun-endpoints
    (seal-or-idᵈ , base-seal-step-fun⊒)
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = base-store-det}
      base-seal-step-fun⊒ id-var0-fun⊒))
  where
    base-seal-step-fun⊒ =
      base-seal-step-fun-narrowingᵐ {ι = ι}

    id-var0-fun⊒ =
      id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl

-- cambridge25 Example 7, line 714.
ex7-line714 : ∀ {ι} →
  2 ∣ (0 ꞉ id (‵ ι)) ∷ [] ∣ []
    ⊢ ((⇑ᵗᵐ ((ƛ (` 0))
          ⟨ gen (★ ⇒ ★) var0-fun ⟩)) •)
        ⟨ - base-seal-step-fun ι ⟩
      ⊒ ((⇑ᵗᵐ (Λ (ƛ (` 0)))) •) ⟨ - base-seal-step-fun ι ⟩
    ∶ id (‵ ι) ↦ id (‵ ι) ⦂ _ ⊒ _
ex7-line714 {ι = ι} =
  cast+⊒cast+-derivedᵗ
    {p = id (＇ 0) ↦ id (＇ 0)}
    {q = id (‵ ι) ↦ id (‵ ι)}
    {r = base-seal-step-fun ι}
    {s = base-seal-step-fun ι}
    {t = base-seal-step-fun ι}
    id-var0-fun-cast
    id-base-fun-cast
    base-store-det
    (id-base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = ι})
    (base-seal-step-fun-narrowingᵐ {ι = ι})
    ex7-downcast-left-≈
    base-store-det
    (base-seal-step-fun-narrowingᵐ {ι = ι})
    (id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl)
    ex7-downcast-right-≈
    ex7-line712

-- cambridge25 Example 7, line 716.
ex7-line716 : ∀ {ι} →
  1 ∣ [] ∣ []
    ⊢ ν (‵ ι)
        (((⇑ᵗᵐ ((ƛ (` 0))
            ⟨ gen (★ ⇒ ★) var0-fun ⟩)) •)
          ⟨ - base-seal-step-fun ι ⟩)
        (⇑ᶜ (id (‵ ι) ↦ id (‵ ι)))
      ⊒ ν (‵ ι)
          (((⇑ᵗᵐ (Λ (ƛ (` 0)))) •) ⟨ - base-seal-step-fun ι ⟩)
          (⇑ᶜ (id (‵ ι) ↦ id (‵ ι)))
    ∶ id (‵ ι) ↦ id (‵ ι) ⦂ _ ⊒ _
ex7-line716 {ι = ι} =
  ν⊒νᵗ {A = ‵ ι} {A′ = ‵ ι}
    {p = id (‵ ι) ↦ id (‵ ι)}
    {q = id (‵ ι)}
    id-base-fun-cast
    id-base-cast
    ex7-line714

-- cambridge25 Example 7, line 719.
ex7-line719 : ∀ {ι} →
  1 ∣ (0 ꞉ id (‵ ι)) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ var0-fun ⦂ _ ⊒ _
ex7-line719 =
  ƛ⊒ƛᵗ var0-fun-cast (x⊒xᵗ var0-untag-cast Z)

-- cambridge25 Example 7, line 720.
ex7-line720-≈ : ∀ {ι} →
  1 ∣ (0 ꞉ id (‵ ι)) ∷ [] ⊢
    var0-fun
      ≈ proj₁ (_⨟ⁿ_ {wfΣ = base-store-det}
          var0-fun-narrowingᵐ
          (id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex7-line720-≈ =
  endpointsⁿ refl refl refl refl
    idBase-store-narrowing
    wf-store-var-fun-endpoints
    wf-store-var-fun-endpoints
    var0-fun-narrowing
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = base-store-det}
      var0-fun⊒ id-var0-fun⊒))
  where
    var0-fun⊒ = var0-fun-narrowingᵐ

    id-var0-fun⊒ =
      id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl

-- cambridge25 Example 7, line 721.
ex7-line721 : ∀ {ι} →
  1 ∣ (0 ꞉ id (‵ ι)) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ var0-fun ⟩
      ⊒ ƛ (` 0)
    ∶ id (＇ 0) ↦ id (＇ 0) ⦂ _ ⊒ _
ex7-line721 =
  cast-⊒ᵗ id-var0-fun-cast base-store-det
    var0-fun-narrowingᵐ
    (id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl)
    ex7-line720-≈ ex7-line719

-- cambridge25 Example 7, line 723.
ex7-line723 : ∀ {ι} →
  1 ∣ (0 ꞉ id (‵ ι)) ∷ [] ∣ []
    ⊢ ((ƛ (` 0)) ⟨ var0-fun ⟩)
        ⟨ - base-seal-step-fun ι ⟩
      ⊒ (ƛ (` 0)) ⟨ - base-seal-step-fun ι ⟩
    ∶ id (‵ ι) ↦ id (‵ ι) ⦂ _ ⊒ _
ex7-line723 {ι = ι} =
  cast+⊒cast+-derivedᵗ
    {p = id (＇ 0) ↦ id (＇ 0)}
    {q = id (‵ ι) ↦ id (‵ ι)}
    {r = base-seal-step-fun ι}
    {s = base-seal-step-fun ι}
    {t = base-seal-step-fun ι}
    id-var0-fun-cast
    id-base-fun-cast
    base-store-det
    (id-base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = ι})
    (base-seal-step-fun-narrowingᵐ {ι = ι})
    ex7-downcast-left-≈
    base-store-det
    (base-seal-step-fun-narrowingᵐ {ι = ι})
    (id-var0-fun-narrowingᵐ {μ = seal-or-idᵈ} refl)
    ex7-downcast-right-≈
    ex7-line721

------------------------------------------------------------------------
-- Example 8
------------------------------------------------------------------------

-- cambridge25 Example 8, line 820 side condition (i), left half:
-- `(ι!→ι?) ⨾ (α♯→α♭) ≈ α!→α?`.
ex8-line820-left-≈ :
  1 ∣ (0 ꞉ base-untag `ℕ) ∷ [] ⊢
    proj₁ (_⨟ⁿ_ {wfΣ = base-store-det}
      (base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `ℕ})
      (base-seal-step-fun-narrowingᵐ {ι = `ℕ}))
      ≈ var0-fun
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex8-line820-left-≈ =
  endpointsⁿ refl refl refl refl
    base-untag-store-narrowing
    wf-store-var-fun-endpoints
    wf-store-var-fun-endpoints
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = base-store-det}
      base-fun⊒ base-seal-step-fun⊒))
    var0-fun-narrowing
  where
    base-fun⊒ =
      base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `ℕ}

    base-seal-step-fun⊒ =
      base-seal-step-fun-narrowingᵐ {ι = `ℕ}

-- cambridge25 Example 8, line 820 side condition (i), right half:
-- `α!→α? ≈ (α!→α?) ⨾ (id_α→id_α)`.
ex8-line820-right-≈ :
  1 ∣ (0 ꞉ base-untag `ℕ) ∷ [] ⊢
    var0-fun
      ≈ proj₁ (_⨟ⁿ_ {wfΣ = star-store-det}
          var0-fun-narrowingᵐ
          (id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl))
      ∶ (★ ⇒ ★) ⊒ (＇ 0 ⇒ ＇ 0)
ex8-line820-right-≈ =
  endpointsⁿ refl refl refl refl
    base-untag-store-narrowing
    wf-store-var-fun-endpoints
    wf-store-var-fun-endpoints
    var0-fun-narrowing
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = star-store-det}
      var0-fun⊒ id-var0-fun⊒))
  where
    var0-fun⊒ = var0-fun-narrowingᵐ

    id-var0-fun⊒ =
      id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl

-- cambridge25 Example 8, line 818.
ex8-idα :
  1 ∣ (0 ꞉ base-untag `ℕ) ∷ [] ∣ []
    ⊢ ƛ (` 0) ⊒ ƛ (` 0)
    ∶ id (＇ 0) ↦ id (＇ 0) ⦂ _ ⊒ _
ex8-idα =
  ƛ⊒ƛᵗ id-var0-fun-cast (x⊒xᵗ id-var0-cast Z)

-- cambridge25 Example 8, line 820.
ex8-line820 :
  1 ∣ (0 ꞉ base-untag `ℕ) ∷ [] ∣ []
    ⊢ (ƛ (` 0)) ⟨ - var0-fun ⟩
      ⊒ (ƛ (` 0)) ⟨ - base-seal-step-fun `ℕ ⟩
    ∶ base-fun `ℕ ⦂ _ ⊒ _
ex8-line820 =
  ⊒cast+ᵗ
    {q = base-fun `ℕ}
    {r = var0-fun}
    {s = base-seal-step-fun `ℕ}
    base-fun-cast
    base-store-det
    (base-fun-narrowingᵐ {μ = seal-or-idᵈ} {ι = `ℕ})
    (base-seal-step-fun-narrowingᵐ {ι = `ℕ})
    ex8-line820-left-≈
    (cast+⊒ᵗ
      {p = id (＇ 0) ↦ id (＇ 0)}
      {r = var0-fun}
      {t = var0-fun}
      id-var0-fun-cast
      var0-fun-cast
      star-store-det
      var0-fun-narrowingᵐ
      (id-var0-fun-narrowingᵐ {μ = tag-or-idᵈ} refl)
      ex8-line820-right-≈
      ex8-idα)

-- cambridge25 Example 8, line 821 argument premise.
ex8-c★⊒c-right-≈ :
  1 ∣ (0 ꞉ base-untag `ℕ) ∷ [] ⊢
    base-untag `ℕ
      ≈ proj₁ (_⨟ⁿ_ {wfΣ = star-store-det}
          (base-untag-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ})
          (id-base-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ}))
      ∶ ★ ⊒ ‵ `ℕ
ex8-c★⊒c-right-≈ =
  endpointsⁿ refl refl refl refl
    base-untag-store-narrowing
    wf★-base-endpoints
    wf★-base-endpoints
    base-untag-narrowing
    (_ , proj₂ (_⨟ⁿ_ {wfΣ = star-store-det}
      base-untag⊒ id-base⊒))
  where
    base-untag⊒ =
      base-untag-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ}

    id-base⊒ =
      id-base-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ}

ex8-c★⊒c :
  1 ∣ (0 ꞉ base-untag `ℕ) ∷ [] ∣ []
    ⊢ c★ ⊒ $ (κℕ 0) ∶ base-untag `ℕ ⦂ _ ⊒ _
ex8-c★⊒c =
  cast+⊒ᵗ
    {p = id (‵ `ℕ)}
    {r = base-untag `ℕ}
    {t = base-untag `ℕ}
    {A = ★}
    {B = ‵ `ℕ}
    id-base-cast
    base-untag-cast
    star-store-det
    (base-untag-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ})
    (id-base-narrowingᵐ {μ = tag-or-idᵈ} {ι = `ℕ})
    ex8-c★⊒c-right-≈
    (κ⊒κᵗ (κℕ 0))

-- cambridge25 Example 8, line 823.
ex8-line823 :
  1 ∣ (0 ꞉ base-untag `ℕ) ∷ [] ∣ []
    ⊢ ((ƛ (` 0)) ⟨ - var0-fun ⟩) · c★
      ⊒ ((ƛ (` 0)) ⟨ - base-seal-step-fun `ℕ ⟩) · $ (κℕ 0)
    ∶ base-untag `ℕ ⦂ _ ⊒ _
ex8-line823 =
  ·⊒·ᵗ base-fun-cast ex8-line820 ex8-c★⊒c
