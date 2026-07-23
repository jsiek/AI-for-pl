module proof.Core.Properties.DualRawProperties where

-- File Charter:
--   * The raw computed by the witness-directed duals
--     (`NarrowWiden.dualⁿ`/`dualʷ` and their cross/strict variants)
--     is determined by the raw coercion and the action environment
--     alone: it equals the total raw-level functions
--     `dualRawⁿ`/`dualRawʷ` below, which mirror the witness duals'
--     case tree — including the collapsing tag-to-seal/seal-to-tag
--     branches — by raw shape.  (The witness dual is NOT the
--     `Coercions.dual` operator: on collapsed sequences the two
--     disagree, so the raw-level mirror has to carry the same
--     collapses.)
--   * Corollaries: dual raws are determined across witnesses of any
--     sort (proving, for the mediated surface, the statement the old
--     two-store surface postulates as `dualʷ-raw-determined`), and
--     dual raws commute with type renaming over an action-environment
--     renaming relation (`ActionRename`).
--   * Everything here is proved.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans; sym)

open import Types
open import Coercions
open import NarrowWiden

------------------------------------------------------------------------
-- The raw dual functions
------------------------------------------------------------------------

-- One function per polarity: all four narrowing witness sorts
-- (`Narrowing`, `StrictNarrowing`, `CrossNarrowing`,
-- `StrictCrossNarrowing`) compute the same dual raw, and likewise for
-- the widening sorts.  On raws no witness inhabits, the value is
-- junk, chosen renaming-naturally so the commutation lemma below
-- needs no side conditions.

mutual
  dualRawⁿ : DualActionEnv → Coercion → Coercion
  dualRawⁿ η (id A) = id A
  dualRawⁿ η (c ︔ d) = dualRawSeqⁿ η c d
  dualRawⁿ η (c ↦ d) = dualRawʷ η c ↦ dualRawⁿ η d
  dualRawⁿ η (`∀ c) = `∀ (dualRawⁿ (extᵃ η) c)
  dualRawⁿ η (G !) = G !
  dualRawⁿ η (G ？) = dualUntag η G
  dualRawⁿ η (seal A α) = dualSeal η A α
  dualRawⁿ η (unseal α A) = unseal α A
  dualRawⁿ η (gen A c) = inst A (dualRawⁿ (genᵃ η) c)
  dualRawⁿ η (inst B c) = gen B (dualRawⁿ (instᵃ η) c)

  -- A narrowing sequence witness either seals on the right
  -- (`_︔seal_`) or untags on the left (`_？︔_`); the seal shape wins
  -- the dispatch because the untag witness's tail (a strict cross
  -- narrowing) cannot be a seal.
  dualRawSeqⁿ : DualActionEnv → Coercion → Coercion → Coercion
  dualRawSeqⁿ η c (seal A α) with η α
  ... | normal = unseal α A ︔ dualRawⁿ η c
  ... | tag-to-seal = unseal α A ︔ dualRawⁿ η c
  ... | seal-to-tag = (＇ α) !
  dualRawSeqⁿ η c d = dualRawUntagSeqⁿ η c d

  dualRawUntagSeqⁿ : DualActionEnv → Coercion → Coercion → Coercion
  dualRawUntagSeqⁿ η ((＇ α) ？) d with η α
  ... | normal = dualRawⁿ η d ︔ ((＇ α) !)
  ... | tag-to-seal = unseal α ★
  ... | seal-to-tag = dualRawⁿ η d ︔ ((＇ α) !)
  dualRawUntagSeqⁿ η (G ？) d = dualRawⁿ η d ︔ (G !)
  dualRawUntagSeqⁿ η c d = dualRawⁿ η d ︔ dualRawⁿ η c

  dualRawʷ : DualActionEnv → Coercion → Coercion
  dualRawʷ η (id A) = id A
  dualRawʷ η (c ︔ d) = dualRawSeqʷ η c d
  dualRawʷ η (c ↦ d) = dualRawⁿ η c ↦ dualRawʷ η d
  dualRawʷ η (`∀ c) = `∀ (dualRawʷ (extᵃ η) c)
  dualRawʷ η (G !) = dualTag η G
  dualRawʷ η (G ？) = G ？
  dualRawʷ η (seal A α) = seal A α
  dualRawʷ η (unseal α A) = dualUnseal η α A
  dualRawʷ η (gen A c) = inst A (dualRawʷ (genᵃ η) c)
  dualRawʷ η (inst B c) = gen B (dualRawʷ (instᵃ η) c)

  -- A widening sequence witness either unseals on the left
  -- (`unseal︔_`) or tags on the right (`_︔_!`); the unseal shape
  -- wins the dispatch because the tag witness's head (a strict cross
  -- widening) cannot be an unseal.
  dualRawSeqʷ : DualActionEnv → Coercion → Coercion → Coercion
  dualRawSeqʷ η (unseal α A) d with η α
  ... | normal = dualRawʷ η d ︔ seal A α
  ... | tag-to-seal = dualRawʷ η d ︔ seal A α
  ... | seal-to-tag = (＇ α) ？
  dualRawSeqʷ η c d = dualRawTagSeqʷ η c d

  dualRawTagSeqʷ : DualActionEnv → Coercion → Coercion → Coercion
  dualRawTagSeqʷ η c ((＇ α) !) with η α
  ... | normal = ((＇ α) ？) ︔ dualRawʷ η c
  ... | tag-to-seal = seal ★ α
  ... | seal-to-tag = ((＇ α) ？) ︔ dualRawʷ η c
  dualRawTagSeqʷ η c (G !) = (G ？) ︔ dualRawʷ η c
  dualRawTagSeqʷ η c d = dualRawʷ η d ︔ dualRawʷ η c

------------------------------------------------------------------------
-- Dispatch reductions
------------------------------------------------------------------------

-- The sequence dispatchers step to their second stage when the
-- witness pins the discriminating factor away from the seal/unseal
-- shape.

dualRawSeqⁿ-nonseal :
  ∀ η c {d} →
  StrictCrossNarrowing d →
  dualRawSeqⁿ η c d ≡ dualRawUntagSeqⁿ η c d
dualRawSeqⁿ-nonseal η c (cn-funˡ _ _) = refl
dualRawSeqⁿ-nonseal η c (cn-funʳ _ _) = refl
dualRawSeqⁿ-nonseal η c (cn-all _) = refl

dualRawSeqʷ-nonunseal :
  ∀ η {c} →
  StrictCrossWidening c →
  ∀ d →
  dualRawSeqʷ η c d ≡ dualRawTagSeqʷ η c d
dualRawSeqʷ-nonunseal η (cw-funˡ _ _) d = refl
dualRawSeqʷ-nonunseal η (cw-funʳ _ _) d = refl
dualRawSeqʷ-nonunseal η (cw-all _) d = refl

------------------------------------------------------------------------
-- The witness-directed duals compute the raw dual
------------------------------------------------------------------------

mutual
  dualCrossⁿ-raw :
    ∀ η {c} (w : CrossNarrowing c) →
    proj₁ (dualCrossNarrowing η w) ≡ dualRawⁿ η c
  dualCrossⁿ-raw η (id-＇ α) = refl
  dualCrossⁿ-raw η (id-‵ ι) = refl
  dualCrossⁿ-raw η (sʷ ↦ tⁿ) =
    cong₂ _↦_ (dualʷ-raw η sʷ) (dualⁿ-raw η tⁿ)
  dualCrossⁿ-raw η (`∀ sⁿ) =
    cong `∀ (dualⁿ-raw (extᵃ η) sⁿ)

  dualStrictCrossⁿ-raw :
    ∀ η {c} (w : StrictCrossNarrowing c) →
    proj₁ (dualStrictCrossNarrowing η w) ≡ dualRawⁿ η c
  dualStrictCrossⁿ-raw η (cn-funˡ sʷ tⁿ) =
    cong₂ _↦_ (dualStrictʷ-raw η sʷ) (dualⁿ-raw η tⁿ)
  dualStrictCrossⁿ-raw η (cn-funʳ sʷ tⁿ) =
    cong₂ _↦_ (dualʷ-raw η sʷ) (dualStrictⁿ-raw η tⁿ)
  dualStrictCrossⁿ-raw η (cn-all sⁿ) =
    cong `∀ (dualStrictⁿ-raw (extᵃ η) sⁿ)

  dualⁿ-raw :
    ∀ η {c} (w : Narrowing c) →
    proj₁ (dualⁿ η w) ≡ dualRawⁿ η c
  dualⁿ-raw η (cross gⁿ) = dualCrossⁿ-raw η gⁿ
  dualⁿ-raw η id★ = refl
  dualⁿ-raw η (gen {A = A} safe) =
    cong (inst A)
      (trans
        (instSafeⁿ-raw (genᵃ η) safe)
        (dualⁿ-raw (genᵃ η) (genSafe→narrowing safe)))
  dualⁿ-raw η (untag (＇ α)) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualⁿ-raw η (untag (‵ ι)) = refl
  dualⁿ-raw η (untag ★⇒★) = refl
  dualⁿ-raw η (_？︔_ (＇ α) gⁿ)
    with dualRawSeqⁿ-nonseal η ((＇ α) ？) gⁿ
  ... | eq with η α
  ...   | normal =
    trans
      (cong (_︔ ((＇ α) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym eq)
  ...   | tag-to-seal = sym eq
  ...   | seal-to-tag =
    trans
      (cong (_︔ ((＇ α) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym eq)
  dualⁿ-raw η (_？︔_ (‵ ι) gⁿ) =
    trans
      (cong (_︔ ((‵ ι) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym (dualRawSeqⁿ-nonseal η ((‵ ι) ？) gⁿ))
  dualⁿ-raw η (_？︔_ ★⇒★ gⁿ) =
    trans
      (cong (_︔ ((★ ⇒ ★) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym (dualRawSeqⁿ-nonseal η ((★ ⇒ ★) ？) gⁿ))
  dualⁿ-raw η (fun-untag-gen {A = A} safe) =
    cong (λ d → inst A d ︔ ((★ ⇒ ★) !))
      (trans
        (instSafeⁿ-raw (genᵃ η) safe)
        (dualⁿ-raw (genᵃ η) (genSafe→narrowing safe)))
  dualⁿ-raw η (sealⁿ A α) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualⁿ-raw η (_︔seal_ {A = A} sⁿ α) with η α
  ... | normal = cong (unseal α A ︔_) (dualStrictⁿ-raw η sⁿ)
  ... | tag-to-seal = cong (unseal α A ︔_) (dualStrictⁿ-raw η sⁿ)
  ... | seal-to-tag = refl

  dualStrictⁿ-raw :
    ∀ η {c} (w : StrictNarrowing c) →
    proj₁ (dualStrictⁿ η w) ≡ dualRawⁿ η c
  dualStrictⁿ-raw η (strict-crossⁿ gⁿ) = dualStrictCrossⁿ-raw η gⁿ
  dualStrictⁿ-raw η (strict-gen {A = A} safe) =
    cong (inst A)
      (trans
        (instSafeⁿ-raw (genᵃ η) safe)
        (dualⁿ-raw (genᵃ η) (genSafe→narrowing safe)))
  dualStrictⁿ-raw η (strict-untag (＇ α)) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualStrictⁿ-raw η (strict-untag (‵ ι)) = refl
  dualStrictⁿ-raw η (strict-untag ★⇒★) = refl
  dualStrictⁿ-raw η (strict-untag-seq (＇ α) gⁿ)
    with dualRawSeqⁿ-nonseal η ((＇ α) ？) gⁿ
  ... | eq with η α
  ...   | normal =
    trans
      (cong (_︔ ((＇ α) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym eq)
  ...   | tag-to-seal = sym eq
  ...   | seal-to-tag =
    trans
      (cong (_︔ ((＇ α) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym eq)
  dualStrictⁿ-raw η (strict-untag-seq (‵ ι) gⁿ) =
    trans
      (cong (_︔ ((‵ ι) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym (dualRawSeqⁿ-nonseal η ((‵ ι) ？) gⁿ))
  dualStrictⁿ-raw η (strict-untag-seq ★⇒★ gⁿ) =
    trans
      (cong (_︔ ((★ ⇒ ★) !)) (dualStrictCrossⁿ-raw η gⁿ))
      (sym (dualRawSeqⁿ-nonseal η ((★ ⇒ ★) ？) gⁿ))
  dualStrictⁿ-raw η (strict-fun-untag-gen {A = A} safe) =
    cong (λ d → inst A d ︔ ((★ ⇒ ★) !))
      (trans
        (instSafeⁿ-raw (genᵃ η) safe)
        (dualⁿ-raw (genᵃ η) (genSafe→narrowing safe)))
  dualStrictⁿ-raw η (strict-seal A α) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualStrictⁿ-raw η (strict-seal-seq {A = A} sⁿ α) with η α
  ... | normal = cong (unseal α A ︔_) (dualStrictⁿ-raw η sⁿ)
  ... | tag-to-seal = cong (unseal α A ︔_) (dualStrictⁿ-raw η sⁿ)
  ... | seal-to-tag = refl

  dualCrossʷ-raw :
    ∀ η {c} (w : CrossWidening c) →
    proj₁ (dualCrossWidening η w) ≡ dualRawʷ η c
  dualCrossʷ-raw η (id-＇ α) = refl
  dualCrossʷ-raw η (id-‵ ι) = refl
  dualCrossʷ-raw η (sⁿ ↦ tʷ) =
    cong₂ _↦_ (dualⁿ-raw η sⁿ) (dualʷ-raw η tʷ)
  dualCrossʷ-raw η (`∀ sʷ) =
    cong `∀ (dualʷ-raw (extᵃ η) sʷ)

  dualStrictCrossʷ-raw :
    ∀ η {c} (w : StrictCrossWidening c) →
    proj₁ (dualStrictCrossWidening η w) ≡ dualRawʷ η c
  dualStrictCrossʷ-raw η (cw-funˡ sⁿ tʷ) =
    cong₂ _↦_ (dualStrictⁿ-raw η sⁿ) (dualʷ-raw η tʷ)
  dualStrictCrossʷ-raw η (cw-funʳ sⁿ tʷ) =
    cong₂ _↦_ (dualⁿ-raw η sⁿ) (dualStrictʷ-raw η tʷ)
  dualStrictCrossʷ-raw η (cw-all sʷ) =
    cong `∀ (dualStrictʷ-raw (extᵃ η) sʷ)

  dualʷ-raw :
    ∀ η {c} (w : Widening c) →
    proj₁ (dualʷ η w) ≡ dualRawʷ η c
  dualʷ-raw η (cross gʷ) = dualCrossʷ-raw η gʷ
  dualʷ-raw η id★ = refl
  dualʷ-raw η (inst {B = B} safe) =
    cong (gen B)
      (trans
        (instSafeʷ-raw (instᵃ η) safe)
        (dualʷ-raw (instᵃ η) (instSafe→widening safe)))
  dualʷ-raw η (tag (＇ α)) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualʷ-raw η (tag (‵ ι)) = refl
  dualʷ-raw η (tag ★⇒★) = refl
  dualʷ-raw η (_︔_! {g = g} gʷ (＇ α))
    with dualRawSeqʷ-nonunseal η gʷ ((＇ α) !)
  ... | eq with η α
  ...   | normal =
    trans
      (cong (((＇ α) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym eq)
  ...   | tag-to-seal = sym eq
  ...   | seal-to-tag =
    trans
      (cong (((＇ α) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym eq)
  dualʷ-raw η (_︔_! gʷ (‵ ι)) =
    trans
      (cong (((‵ ι) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym (dualRawSeqʷ-nonunseal η gʷ ((‵ ι) !)))
  dualʷ-raw η (_︔_! gʷ ★⇒★) =
    trans
      (cong (((★ ⇒ ★) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym (dualRawSeqʷ-nonunseal η gʷ ((★ ⇒ ★) !)))
  dualʷ-raw η (inst-fun-tag {B = B} safe) =
    cong (λ d → ((★ ⇒ ★) ？) ︔ gen B d)
      (trans
        (instSafeʷ-raw (instᵃ η) safe)
        (dualʷ-raw (instᵃ η) (instSafe→widening safe)))
  dualʷ-raw η (unsealʷ α A) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualʷ-raw η (unseal︔_ α {A = A} sʷ) with η α
  ... | normal = cong (_︔ seal A α) (dualStrictʷ-raw η sʷ)
  ... | tag-to-seal = cong (_︔ seal A α) (dualStrictʷ-raw η sʷ)
  ... | seal-to-tag = refl

  dualStrictʷ-raw :
    ∀ η {c} (w : StrictWidening c) →
    proj₁ (dualStrictʷ η w) ≡ dualRawʷ η c
  dualStrictʷ-raw η (strict-crossʷ gʷ) = dualStrictCrossʷ-raw η gʷ
  dualStrictʷ-raw η (strict-inst {B = B} safe) =
    cong (gen B)
      (trans
        (instSafeʷ-raw (instᵃ η) safe)
        (dualʷ-raw (instᵃ η) (instSafe→widening safe)))
  dualStrictʷ-raw η (strict-tag (＇ α)) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualStrictʷ-raw η (strict-tag (‵ ι)) = refl
  dualStrictʷ-raw η (strict-tag ★⇒★) = refl
  dualStrictʷ-raw η (strict-tag-seq gʷ (＇ α))
    with dualRawSeqʷ-nonunseal η gʷ ((＇ α) !)
  ... | eq with η α
  ...   | normal =
    trans
      (cong (((＇ α) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym eq)
  ...   | tag-to-seal = sym eq
  ...   | seal-to-tag =
    trans
      (cong (((＇ α) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym eq)
  dualStrictʷ-raw η (strict-tag-seq gʷ (‵ ι)) =
    trans
      (cong (((‵ ι) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym (dualRawSeqʷ-nonunseal η gʷ ((‵ ι) !)))
  dualStrictʷ-raw η (strict-tag-seq gʷ ★⇒★) =
    trans
      (cong (((★ ⇒ ★) ？) ︔_) (dualStrictCrossʷ-raw η gʷ))
      (sym (dualRawSeqʷ-nonunseal η gʷ ((★ ⇒ ★) !)))
  dualStrictʷ-raw η (strict-inst-fun-tag {B = B} safe) =
    cong (λ d → ((★ ⇒ ★) ？) ︔ gen B d)
      (trans
        (instSafeʷ-raw (instᵃ η) safe)
        (dualʷ-raw (instᵃ η) (instSafe→widening safe)))
  dualStrictʷ-raw η (strict-unseal α A) with η α
  ... | normal = refl
  ... | tag-to-seal = refl
  ... | seal-to-tag = refl
  dualStrictʷ-raw η (strict-unseal-seq α {A = A} sʷ) with η α
  ... | normal = cong (_︔ seal A α) (dualStrictʷ-raw η sʷ)
  ... | tag-to-seal = cong (_︔ seal A α) (dualStrictʷ-raw η sʷ)
  ... | seal-to-tag = refl

------------------------------------------------------------------------
-- Determinacy corollaries
------------------------------------------------------------------------

-- The dual raw does not depend on the witness — of any sort.  The
-- widening instance is the statement the old two-store surface
-- postulates from the removed separated-store DGG prototype.

dualⁿ-raw-determined :
  ∀ η {c} (w₁ w₂ : Narrowing c) →
  proj₁ (dualⁿ η w₁) ≡ proj₁ (dualⁿ η w₂)
dualⁿ-raw-determined η w₁ w₂ =
  trans (dualⁿ-raw η w₁) (sym (dualⁿ-raw η w₂))

dualʷ-raw-determined :
  ∀ η {c} (w₁ w₂ : Widening c) →
  proj₁ (dualʷ η w₁) ≡ proj₁ (dualʷ η w₂)
dualʷ-raw-determined η w₁ w₂ =
  trans (dualʷ-raw η w₁) (sym (dualʷ-raw η w₂))

------------------------------------------------------------------------
-- Renaming commutation
------------------------------------------------------------------------

-- Renaming a coercion and taking its dual raw commute, over a
-- renaming relation between the action environments.  The relation
-- extends under all three binder actions, and the identity instance
-- `ActionRename ρ normalᵃ normalᵃ` holds by `refl`.

ActionRename : Renameᵗ → DualActionEnv → DualActionEnv → Set
ActionRename ρ η η′ = ∀ α → η′ (ρ α) ≡ η α

-- The environments are explicit throughout this section: they only
-- ever occur applied (never as patterns), so Agda cannot recover them
-- from the goal.

ActionRename-ext :
  ∀ ρ η η′ →
  ActionRename ρ η η′ →
  ActionRename (extᵗ ρ) (extᵃ η) (extᵃ η′)
ActionRename-ext ρ η η′ rel zero = refl
ActionRename-ext ρ η η′ rel (suc α) = rel α

ActionRename-gen :
  ∀ ρ η η′ →
  ActionRename ρ η η′ →
  ActionRename (extᵗ ρ) (genᵃ η) (genᵃ η′)
ActionRename-gen ρ η η′ rel zero = refl
ActionRename-gen ρ η η′ rel (suc α) = rel α

ActionRename-inst :
  ∀ ρ η η′ →
  ActionRename ρ η η′ →
  ActionRename (extᵗ ρ) (instᵃ η) (instᵃ η′)
ActionRename-inst ρ η η′ rel zero = refl
ActionRename-inst ρ η η′ rel (suc α) = rel α

dualUntag-renameᵗ :
  ∀ ρ η η′ →
  ActionRename ρ η η′ →
  ∀ G →
  dualUntag η′ (renameᵗ ρ G) ≡ renameᶜ ρ (dualUntag η G)
dualUntag-renameᵗ ρ η η′ rel (＇ α) rewrite rel α with η α
... | normal = refl
... | tag-to-seal = refl
... | seal-to-tag = refl
dualUntag-renameᵗ ρ η η′ rel (‵ ι) = refl
dualUntag-renameᵗ ρ η η′ rel ★ = refl
dualUntag-renameᵗ ρ η η′ rel (A ⇒ B) = refl
dualUntag-renameᵗ ρ η η′ rel (`∀ A) = refl

dualTag-renameᵗ :
  ∀ ρ η η′ →
  ActionRename ρ η η′ →
  ∀ G →
  dualTag η′ (renameᵗ ρ G) ≡ renameᶜ ρ (dualTag η G)
dualTag-renameᵗ ρ η η′ rel (＇ α) rewrite rel α with η α
... | normal = refl
... | tag-to-seal = refl
... | seal-to-tag = refl
dualTag-renameᵗ ρ η η′ rel (‵ ι) = refl
dualTag-renameᵗ ρ η η′ rel ★ = refl
dualTag-renameᵗ ρ η η′ rel (A ⇒ B) = refl
dualTag-renameᵗ ρ η η′ rel (`∀ A) = refl

dualSeal-renameᵗ :
  ∀ ρ η η′ →
  ActionRename ρ η η′ →
  ∀ A α →
  dualSeal η′ (renameᵗ ρ A) (ρ α) ≡ renameᶜ ρ (dualSeal η A α)
dualSeal-renameᵗ ρ η η′ rel A α rewrite rel α with η α
... | normal = refl
... | tag-to-seal = refl
... | seal-to-tag = refl

dualUnseal-renameᵗ :
  ∀ ρ η η′ →
  ActionRename ρ η η′ →
  ∀ α A →
  dualUnseal η′ (ρ α) (renameᵗ ρ A) ≡ renameᶜ ρ (dualUnseal η α A)
dualUnseal-renameᵗ ρ η η′ rel α A rewrite rel α with η α
... | normal = refl
... | tag-to-seal = refl
... | seal-to-tag = refl

mutual
  dualRawⁿ-renameᶜ :
    ∀ ρ η η′ →
    ActionRename ρ η η′ →
    ∀ c →
    dualRawⁿ η′ (renameᶜ ρ c) ≡ renameᶜ ρ (dualRawⁿ η c)
  dualRawⁿ-renameᶜ ρ η η′ rel (id A) = refl
  dualRawⁿ-renameᶜ ρ η η′ rel (c ︔ d) =
    dualRawSeqⁿ-renameᶜ ρ η η′ rel c d
  dualRawⁿ-renameᶜ ρ η η′ rel (c ↦ d) =
    cong₂ _↦_
      (dualRawʷ-renameᶜ ρ η η′ rel c)
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
  dualRawⁿ-renameᶜ ρ η η′ rel (`∀ c) =
    cong `∀
      (dualRawⁿ-renameᶜ (extᵗ ρ) (extᵃ η) (extᵃ η′)
        (ActionRename-ext ρ η η′ rel) c)
  dualRawⁿ-renameᶜ ρ η η′ rel (G !) = refl
  dualRawⁿ-renameᶜ ρ η η′ rel (G ？) = dualUntag-renameᵗ ρ η η′ rel G
  dualRawⁿ-renameᶜ ρ η η′ rel (seal A α) =
    dualSeal-renameᵗ ρ η η′ rel A α
  dualRawⁿ-renameᶜ ρ η η′ rel (unseal α A) = refl
  dualRawⁿ-renameᶜ ρ η η′ rel (gen A c) =
    cong (inst _)
      (dualRawⁿ-renameᶜ (extᵗ ρ) (genᵃ η) (genᵃ η′)
        (ActionRename-gen ρ η η′ rel) c)
  dualRawⁿ-renameᶜ ρ η η′ rel (inst B c) =
    cong (gen _)
      (dualRawⁿ-renameᶜ (extᵗ ρ) (instᵃ η) (instᵃ η′)
        (ActionRename-inst ρ η η′ rel) c)

  dualRawSeqⁿ-renameᶜ :
    ∀ ρ η η′ →
    ActionRename ρ η η′ →
    ∀ c d →
    dualRawSeqⁿ η′ (renameᶜ ρ c) (renameᶜ ρ d)
      ≡ renameᶜ ρ (dualRawSeqⁿ η c d)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (seal A α) rewrite rel α with η α
  ... | normal =
    cong (unseal (ρ α) (renameᵗ ρ A) ︔_)
      (dualRawⁿ-renameᶜ ρ η η′ rel c)
  ... | tag-to-seal =
    cong (unseal (ρ α) (renameᵗ ρ A) ︔_)
      (dualRawⁿ-renameᶜ ρ η η′ rel c)
  ... | seal-to-tag = refl
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (id A) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (id A)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (d₁ ︔ d₂) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (d₁ ︔ d₂)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (d₁ ↦ d₂) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (d₁ ↦ d₂)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (`∀ d) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (`∀ d)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (G !) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (G !)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (G ？) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (G ？)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (unseal α A) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (unseal α A)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (gen A d) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (gen A d)
  dualRawSeqⁿ-renameᶜ ρ η η′ rel c (inst B d) =
    dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel c (inst B d)

  dualRawUntagSeqⁿ-renameᶜ :
    ∀ ρ η η′ →
    ActionRename ρ η η′ →
    ∀ c d →
    dualRawUntagSeqⁿ η′ (renameᶜ ρ c) (renameᶜ ρ d)
      ≡ renameᶜ ρ (dualRawUntagSeqⁿ η c d)
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel ((＇ α) ？) d
      rewrite rel α with η α
  ... | normal =
    cong (_︔ ((＇ (ρ α)) !)) (dualRawⁿ-renameᶜ ρ η η′ rel d)
  ... | tag-to-seal = refl
  ... | seal-to-tag =
    cong (_︔ ((＇ (ρ α)) !)) (dualRawⁿ-renameᶜ ρ η η′ rel d)
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel ((‵ ι) ？) d =
    cong (_︔ ((‵ ι) !)) (dualRawⁿ-renameᶜ ρ η η′ rel d)
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (★ ？) d =
    cong (_︔ (★ !)) (dualRawⁿ-renameᶜ ρ η η′ rel d)
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel ((A ⇒ B) ？) d =
    cong (_︔ ((renameᵗ ρ A ⇒ renameᵗ ρ B) !))
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel ((`∀ A) ？) d =
    cong (_︔ ((`∀ (renameᵗ (extᵗ ρ) A)) !))
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (id A) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (id A))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (c₁ ︔ c₂) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (c₁ ︔ c₂))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (c₁ ↦ c₂) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (c₁ ↦ c₂))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (`∀ c) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (`∀ c))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (G !) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (G !))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (seal A α) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (seal A α))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (unseal α A) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (unseal α A))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (gen A c) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (gen A c))
  dualRawUntagSeqⁿ-renameᶜ ρ η η′ rel (inst B c) d =
    cong₂ _︔_
      (dualRawⁿ-renameᶜ ρ η η′ rel d)
      (dualRawⁿ-renameᶜ ρ η η′ rel (inst B c))

  dualRawʷ-renameᶜ :
    ∀ ρ η η′ →
    ActionRename ρ η η′ →
    ∀ c →
    dualRawʷ η′ (renameᶜ ρ c) ≡ renameᶜ ρ (dualRawʷ η c)
  dualRawʷ-renameᶜ ρ η η′ rel (id A) = refl
  dualRawʷ-renameᶜ ρ η η′ rel (c ︔ d) =
    dualRawSeqʷ-renameᶜ ρ η η′ rel c d
  dualRawʷ-renameᶜ ρ η η′ rel (c ↦ d) =
    cong₂ _↦_
      (dualRawⁿ-renameᶜ ρ η η′ rel c)
      (dualRawʷ-renameᶜ ρ η η′ rel d)
  dualRawʷ-renameᶜ ρ η η′ rel (`∀ c) =
    cong `∀
      (dualRawʷ-renameᶜ (extᵗ ρ) (extᵃ η) (extᵃ η′)
        (ActionRename-ext ρ η η′ rel) c)
  dualRawʷ-renameᶜ ρ η η′ rel (G !) = dualTag-renameᵗ ρ η η′ rel G
  dualRawʷ-renameᶜ ρ η η′ rel (G ？) = refl
  dualRawʷ-renameᶜ ρ η η′ rel (seal A α) = refl
  dualRawʷ-renameᶜ ρ η η′ rel (unseal α A) =
    dualUnseal-renameᵗ ρ η η′ rel α A
  dualRawʷ-renameᶜ ρ η η′ rel (gen A c) =
    cong (inst _)
      (dualRawʷ-renameᶜ (extᵗ ρ) (genᵃ η) (genᵃ η′)
        (ActionRename-gen ρ η η′ rel) c)
  dualRawʷ-renameᶜ ρ η η′ rel (inst B c) =
    cong (gen _)
      (dualRawʷ-renameᶜ (extᵗ ρ) (instᵃ η) (instᵃ η′)
        (ActionRename-inst ρ η η′ rel) c)

  dualRawSeqʷ-renameᶜ :
    ∀ ρ η η′ →
    ActionRename ρ η η′ →
    ∀ c d →
    dualRawSeqʷ η′ (renameᶜ ρ c) (renameᶜ ρ d)
      ≡ renameᶜ ρ (dualRawSeqʷ η c d)
  dualRawSeqʷ-renameᶜ ρ η η′ rel (unseal α A) d rewrite rel α
      with η α
  ... | normal =
    cong (_︔ seal (renameᵗ ρ A) (ρ α))
      (dualRawʷ-renameᶜ ρ η η′ rel d)
  ... | tag-to-seal =
    cong (_︔ seal (renameᵗ ρ A) (ρ α))
      (dualRawʷ-renameᶜ ρ η η′ rel d)
  ... | seal-to-tag = refl
  dualRawSeqʷ-renameᶜ ρ η η′ rel (id A) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (id A) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (c₁ ︔ c₂) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (c₁ ︔ c₂) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (c₁ ↦ c₂) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (c₁ ↦ c₂) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (`∀ c) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (`∀ c) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (G !) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (G !) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (G ？) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (G ？) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (seal A α) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (seal A α) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (gen A c) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (gen A c) d
  dualRawSeqʷ-renameᶜ ρ η η′ rel (inst B c) d =
    dualRawTagSeqʷ-renameᶜ ρ η η′ rel (inst B c) d

  dualRawTagSeqʷ-renameᶜ :
    ∀ ρ η η′ →
    ActionRename ρ η η′ →
    ∀ c d →
    dualRawTagSeqʷ η′ (renameᶜ ρ c) (renameᶜ ρ d)
      ≡ renameᶜ ρ (dualRawTagSeqʷ η c d)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c ((＇ α) !)
      rewrite rel α with η α
  ... | normal =
    cong (((＇ (ρ α)) ？) ︔_) (dualRawʷ-renameᶜ ρ η η′ rel c)
  ... | tag-to-seal = refl
  ... | seal-to-tag =
    cong (((＇ (ρ α)) ？) ︔_) (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c ((‵ ι) !) =
    cong (((‵ ι) ？) ︔_) (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (★ !) =
    cong ((★ ？) ︔_) (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c ((A ⇒ B) !) =
    cong (((renameᵗ ρ A ⇒ renameᵗ ρ B) ？) ︔_)
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c ((`∀ A) !) =
    cong (((`∀ (renameᵗ (extᵗ ρ) A)) ？) ︔_)
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (id A) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (id A))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (d₁ ︔ d₂) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (d₁ ︔ d₂))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (d₁ ↦ d₂) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (d₁ ↦ d₂))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (`∀ d) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (`∀ d))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (G ？) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (G ？))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (seal A α) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (seal A α))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (unseal α A) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (unseal α A))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (gen A d) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (gen A d))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
  dualRawTagSeqʷ-renameᶜ ρ η η′ rel c (inst B d) =
    cong₂ _︔_
      (dualRawʷ-renameᶜ ρ η η′ rel (inst B d))
      (dualRawʷ-renameᶜ ρ η η′ rel c)
