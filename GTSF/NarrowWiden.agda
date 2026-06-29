-- This is based on the cambridge25 notes.

module NarrowWiden where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using
  (ℕ; _<_; _≤_; _+_; _∸_; zero; suc; z<s; s<s; z≤n; s≤s;
   s≤s⁻¹)
open import Data.Nat.Properties using
  (_≟_; ≤-refl; ≤-trans; +-assoc; +-comm; +-mono-≤; +-monoʳ-≤;
   +-monoˡ-≤; +-suc; m+[n∸m]≡n; m≤m+n; m≤n+m; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; cong; cong₂; inspect; sym; trans; [_])
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Store using (StoreIncl; StoreIncl-drop)
open import Coercions
open import proof.CoercionProperties
  using
    ( ModeRename
    ; coercion-mode-relax
    ; coercion-renameᵗᵐ
    ; coercion-weakenᵐ
    )
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-suc
    ; occurs-raise
    ; occurs-raise-fresh
    ; renameᵗ-ground
    )

------------------------------------------------------------------------
-- Narrowing and Widening Grammar
------------------------------------------------------------------------

mutual
  data CrossNarrowing : Coercion → Set where
    id-＇ : (α : TyVar) →
      CrossNarrowing (id (＇ α))

    id-‵ : (ι : Base) →
      CrossNarrowing (id (‵ ι))

    _↦_ : ∀ {s t} →
      Widening s →
      Narrowing t →
      CrossNarrowing (s ↦ t)

    `∀ : ∀ {s} →
      Narrowing s →
      CrossNarrowing (`∀ s)

  data StrictCrossNarrowing : Coercion → Set where
    cn-funˡ : ∀ {s t} →
      StrictWidening s →
      Narrowing t →
      StrictCrossNarrowing (s ↦ t)

    cn-funʳ : ∀ {s t} →
      Widening s →
      StrictNarrowing t →
      StrictCrossNarrowing (s ↦ t)

    cn-all : ∀ {s} →
      StrictNarrowing s →
      StrictCrossNarrowing (`∀ s)

  data Narrowing : Coercion → Set where
    cross : ∀ {g} →
      CrossNarrowing g →
      Narrowing g

    id★ :
      Narrowing (id ★)

    gen : ∀ {A s} →
      Narrowing s →
      Narrowing (gen A s)

    untag : ∀ {G} →
      Ground G →
      Narrowing (G ？)

    _？︔_ : ∀ {G g} →
      Ground G →
      StrictCrossNarrowing g →
      Narrowing ((G ？) ︔ g)

    sealⁿ : (A : Ty) →
      (α : TyVar) →
      Narrowing (seal A α)

    _︔seal_ : ∀ {A s} →
      StrictNarrowing s →
      (α : TyVar) →
      Narrowing (s ︔ seal A α)

  data StrictNarrowing : Coercion → Set where
    strict-crossⁿ : ∀ {g} →
      StrictCrossNarrowing g →
      StrictNarrowing g

    strict-gen : ∀ {A s} →
      Narrowing s →
      StrictNarrowing (gen A s)

    strict-untag : ∀ {G} →
      Ground G →
      StrictNarrowing (G ？)

    strict-untag-seq : ∀ {G g} →
      Ground G →
      StrictCrossNarrowing g →
      StrictNarrowing ((G ？) ︔ g)

    strict-seal : (A : Ty) →
      (α : TyVar) →
      StrictNarrowing (seal A α)

    strict-seal-seq : ∀ {A s} →
      StrictNarrowing s →
      (α : TyVar) →
      StrictNarrowing (s ︔ seal A α)

  data CrossWidening : Coercion → Set where
    id-＇ : (α : TyVar) →
      CrossWidening (id (＇ α))

    id-‵ : (ι : Base) →
      CrossWidening (id (‵ ι))

    _↦_ : ∀ {s t} →
      Narrowing s →
      Widening t →
      CrossWidening (s ↦ t)

    `∀ : ∀ {s} →
      Widening s →
      CrossWidening (`∀ s)

  data StrictCrossWidening : Coercion → Set where
    cw-funˡ : ∀ {s t} →
      StrictNarrowing s →
      Widening t →
      StrictCrossWidening (s ↦ t)

    cw-funʳ : ∀ {s t} →
      Narrowing s →
      StrictWidening t →
      StrictCrossWidening (s ↦ t)

    cw-all : ∀ {s} →
      StrictWidening s →
      StrictCrossWidening (`∀ s)

  data Widening : Coercion → Set where
    cross : ∀ {g} →
      CrossWidening g →
      Widening g

    id★ :
      Widening (id ★)

    inst : ∀ {B s} →
      Widening s →
      Widening (inst B s)

    tag : ∀ {G} →
      Ground G →
      Widening (G !)

    _︔_! : ∀ {G g} →
      StrictCrossWidening g →
      Ground G →
      Widening (g ︔ (G !))

    unsealʷ : (α : TyVar) →
      (A : Ty) →
      Widening (unseal α A)

    unseal︔_ : (α : TyVar) → ∀ {A s} →
      StrictWidening s →
      Widening (unseal α A ︔ s)

  data StrictWidening : Coercion → Set where
    strict-crossʷ : ∀ {g} →
      StrictCrossWidening g →
      StrictWidening g

    strict-inst : ∀ {B s} →
      Widening s →
      StrictWidening (inst B s)

    strict-tag : ∀ {G} →
      Ground G →
      StrictWidening (G !)

    strict-tag-seq : ∀ {G g} →
      StrictCrossWidening g →
      Ground G →
      StrictWidening (g ︔ (G !))

    strict-unseal : (α : TyVar) →
      (A : Ty) →
      StrictWidening (unseal α A)

    strict-unseal-seq : (α : TyVar) → ∀ {A s} →
      StrictWidening s →
      StrictWidening (unseal α A ︔ s)

mutual
  strictCrossⁿ→cross :
    ∀ {c} →
    StrictCrossNarrowing c →
    CrossNarrowing c
  strictCrossⁿ→cross (cn-funˡ sˢ tⁿ) =
    strictʷ→widen sˢ ↦ tⁿ
  strictCrossⁿ→cross (cn-funʳ sʷ tˢ) =
    sʷ ↦ strictⁿ→narrow tˢ
  strictCrossⁿ→cross (cn-all sˢ) =
    `∀ (strictⁿ→narrow sˢ)

  strictⁿ→narrow :
    ∀ {c} →
    StrictNarrowing c →
    Narrowing c
  strictⁿ→narrow (strict-crossⁿ gˢ) =
    cross (strictCrossⁿ→cross gˢ)
  strictⁿ→narrow (strict-gen sⁿ) = gen sⁿ
  strictⁿ→narrow (strict-untag gG) = untag gG
  strictⁿ→narrow (strict-untag-seq gG gˢ) = gG ？︔ gˢ
  strictⁿ→narrow (strict-seal A α) = sealⁿ A α
  strictⁿ→narrow (strict-seal-seq sˢ α) = sˢ ︔seal α

  strictCrossʷ→cross :
    ∀ {c} →
    StrictCrossWidening c →
    CrossWidening c
  strictCrossʷ→cross (cw-funˡ sˢ tʷ) =
    strictⁿ→narrow sˢ ↦ tʷ
  strictCrossʷ→cross (cw-funʳ sⁿ tˢ) =
    sⁿ ↦ strictʷ→widen tˢ
  strictCrossʷ→cross (cw-all sˢ) =
    `∀ (strictʷ→widen sˢ)

  strictʷ→widen :
    ∀ {c} →
    StrictWidening c →
    Widening c
  strictʷ→widen (strict-crossʷ gˢ) =
    cross (strictCrossʷ→cross gˢ)
  strictʷ→widen (strict-inst sʷ) = inst sʷ
  strictʷ→widen (strict-tag gG) = tag gG
  strictʷ→widen (strict-tag-seq gˢ gG) = gˢ ︔ gG !
  strictʷ→widen (strict-unseal α A) = unsealʷ α A
  strictʷ→widen (strict-unseal-seq α sˢ) = unseal︔_ α sˢ

------------------------------------------------------------------------
-- Grammar-directed duality for narrowing and widening
------------------------------------------------------------------------

mutual
  dualCrossNarrowing :
    DualActionEnv →
    ∀ {c} →
    CrossNarrowing c →
    ∃[ d ] CrossWidening d
  dualCrossNarrowing η (id-＇ α) = id (＇ α) , id-＇ α
  dualCrossNarrowing η (id-‵ ι) = id (‵ ι) , id-‵ ι
  dualCrossNarrowing η (sʷ ↦ tⁿ) =
    (proj₁ sⁿ ↦ proj₁ tʷ) , (proj₂ sⁿ ↦ proj₂ tʷ)
    where
      sⁿ = dualʷ η sʷ
      tʷ = dualⁿ η tⁿ
  dualCrossNarrowing η (`∀ sⁿ) =
    `∀ (proj₁ sʷ) , `∀ (proj₂ sʷ)
    where
      sʷ = dualⁿ (extᵃ η) sⁿ

  dualStrictCrossNarrowing :
    DualActionEnv →
    ∀ {c} →
    StrictCrossNarrowing c →
    ∃[ d ] StrictCrossWidening d
  dualStrictCrossNarrowing η (cn-funˡ sʷ tⁿ) =
    (proj₁ sⁿ ↦ proj₁ tʷ) , cw-funˡ (proj₂ sⁿ) (proj₂ tʷ)
    where
      sⁿ = dualStrictʷ η sʷ
      tʷ = dualⁿ η tⁿ
  dualStrictCrossNarrowing η (cn-funʳ sʷ tⁿ) =
    (proj₁ sⁿ ↦ proj₁ tʷ) , cw-funʳ (proj₂ sⁿ) (proj₂ tʷ)
    where
      sⁿ = dualʷ η sʷ
      tʷ = dualStrictⁿ η tⁿ
  dualStrictCrossNarrowing η (cn-all sⁿ) =
    `∀ (proj₁ sʷ) , cw-all (proj₂ sʷ)
    where
      sʷ = dualStrictⁿ (extᵃ η) sⁿ

  dualⁿ :
    DualActionEnv →
    ∀ {c} →
    Narrowing c →
    ∃[ d ] Widening d
  dualⁿ η (cross gⁿ) =
    proj₁ gʷ , cross (proj₂ gʷ)
    where
      gʷ = dualCrossNarrowing η gⁿ
  dualⁿ η id★ = id ★ , id★
  dualⁿ η (gen {A = A} sⁿ) =
    inst A (proj₁ sʷ) , inst (proj₂ sʷ)
    where
      sʷ = dualⁿ (genᵃ η) sⁿ
  dualⁿ η (untag (＇ α)) with η α
  dualⁿ η (untag (＇ α)) | normal = (＇ α) ! , tag (＇ α)
  dualⁿ η (untag (＇ α)) | tag-to-seal = unseal α ★ , unsealʷ α ★
  dualⁿ η (untag (＇ α)) | seal-to-tag = (＇ α) ! , tag (＇ α)
  dualⁿ η (untag (‵ ι)) = (‵ ι) ! , tag (‵ ι)
  dualⁿ η (untag ★⇒★) = (★ ⇒ ★) ! , tag ★⇒★
  dualⁿ η ((＇ α) ？︔ gⁿ) with η α
  dualⁿ η ((＇ α) ？︔ gⁿ) | normal =
    (proj₁ gʷ ︔ ((＇ α) !)) , (proj₂ gʷ ︔ (＇ α) !)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualⁿ η ((＇ α) ？︔ gⁿ) | tag-to-seal =
    unseal α ★ , unsealʷ α ★
  dualⁿ η ((＇ α) ？︔ gⁿ) | seal-to-tag =
    (proj₁ gʷ ︔ ((＇ α) !)) , (proj₂ gʷ ︔ (＇ α) !)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualⁿ η ((‵ ι) ？︔ gⁿ) =
    (proj₁ gʷ ︔ ((‵ ι) !)) , (proj₂ gʷ ︔ (‵ ι) !)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualⁿ η (★⇒★ ？︔ gⁿ) =
    (proj₁ gʷ ︔ ((★ ⇒ ★) !)) , (proj₂ gʷ ︔ ★⇒★ !)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualⁿ η (sealⁿ A α) with η α
  dualⁿ η (sealⁿ A α) | normal = unseal α A , unsealʷ α A
  dualⁿ η (sealⁿ A α) | tag-to-seal = unseal α A , unsealʷ α A
  dualⁿ η (sealⁿ A α) | seal-to-tag = (＇ α) ! , tag (＇ α)
  dualⁿ η (_︔seal_ {A = A} sⁿ α) with η α
  dualⁿ η (_︔seal_ {A = A} sⁿ α) | normal =
    (unseal α A ︔ proj₁ sʷ) , unseal︔_ α (proj₂ sʷ)
    where
      sʷ = dualStrictⁿ η sⁿ
  dualⁿ η (_︔seal_ {A = A} sⁿ α) | tag-to-seal =
    (unseal α A ︔ proj₁ sʷ) , unseal︔_ α (proj₂ sʷ)
    where
      sʷ = dualStrictⁿ η sⁿ
  dualⁿ η (_︔seal_ {A = A} sⁿ α) | seal-to-tag =
    (＇ α) ! , tag (＇ α)

  dualStrictⁿ :
    DualActionEnv →
    ∀ {c} →
    StrictNarrowing c →
    ∃[ d ] StrictWidening d
  dualStrictⁿ η (strict-crossⁿ gⁿ) =
    proj₁ gʷ , strict-crossʷ (proj₂ gʷ)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualStrictⁿ η (strict-gen {A = A} sⁿ) =
    inst A (proj₁ sʷ) , strict-inst (proj₂ sʷ)
    where
      sʷ = dualⁿ (genᵃ η) sⁿ
  dualStrictⁿ η (strict-untag (＇ α)) with η α
  dualStrictⁿ η (strict-untag (＇ α)) | normal =
    (＇ α) ! , strict-tag (＇ α)
  dualStrictⁿ η (strict-untag (＇ α)) | tag-to-seal =
    unseal α ★ , strict-unseal α ★
  dualStrictⁿ η (strict-untag (＇ α)) | seal-to-tag =
    (＇ α) ! , strict-tag (＇ α)
  dualStrictⁿ η (strict-untag (‵ ι)) = (‵ ι) ! , strict-tag (‵ ι)
  dualStrictⁿ η (strict-untag ★⇒★) = (★ ⇒ ★) ! , strict-tag ★⇒★
  dualStrictⁿ η (strict-untag-seq (＇ α) gⁿ) with η α
  dualStrictⁿ η (strict-untag-seq (＇ α) gⁿ) | normal =
    (proj₁ gʷ ︔ ((＇ α) !)) , strict-tag-seq (proj₂ gʷ) (＇ α)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualStrictⁿ η (strict-untag-seq (＇ α) gⁿ) | tag-to-seal =
    unseal α ★ , strict-unseal α ★
  dualStrictⁿ η (strict-untag-seq (＇ α) gⁿ) | seal-to-tag =
    (proj₁ gʷ ︔ ((＇ α) !)) , strict-tag-seq (proj₂ gʷ) (＇ α)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualStrictⁿ η (strict-untag-seq (‵ ι) gⁿ) =
    (proj₁ gʷ ︔ ((‵ ι) !)) , strict-tag-seq (proj₂ gʷ) (‵ ι)
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualStrictⁿ η (strict-untag-seq ★⇒★ gⁿ) =
    (proj₁ gʷ ︔ ((★ ⇒ ★) !)) , strict-tag-seq (proj₂ gʷ) ★⇒★
    where
      gʷ = dualStrictCrossNarrowing η gⁿ
  dualStrictⁿ η (strict-seal A α) with η α
  dualStrictⁿ η (strict-seal A α) | normal =
    unseal α A , strict-unseal α A
  dualStrictⁿ η (strict-seal A α) | tag-to-seal =
    unseal α A , strict-unseal α A
  dualStrictⁿ η (strict-seal A α) | seal-to-tag =
    (＇ α) ! , strict-tag (＇ α)
  dualStrictⁿ η (strict-seal-seq {A = A} sⁿ α) with η α
  dualStrictⁿ η (strict-seal-seq {A = A} sⁿ α) | normal =
    (unseal α A ︔ proj₁ sʷ) , strict-unseal-seq α (proj₂ sʷ)
    where
      sʷ = dualStrictⁿ η sⁿ
  dualStrictⁿ η (strict-seal-seq {A = A} sⁿ α) | tag-to-seal =
    (unseal α A ︔ proj₁ sʷ) , strict-unseal-seq α (proj₂ sʷ)
    where
      sʷ = dualStrictⁿ η sⁿ
  dualStrictⁿ η (strict-seal-seq {A = A} sⁿ α) | seal-to-tag =
    (＇ α) ! , strict-tag (＇ α)

  dualCrossWidening :
    DualActionEnv →
    ∀ {c} →
    CrossWidening c →
    ∃[ d ] CrossNarrowing d
  dualCrossWidening η (id-＇ α) = id (＇ α) , id-＇ α
  dualCrossWidening η (id-‵ ι) = id (‵ ι) , id-‵ ι
  dualCrossWidening η (sⁿ ↦ tʷ) =
    (proj₁ sʷ ↦ proj₁ tⁿ) , (proj₂ sʷ ↦ proj₂ tⁿ)
    where
      sʷ = dualⁿ η sⁿ
      tⁿ = dualʷ η tʷ
  dualCrossWidening η (`∀ sʷ) =
    `∀ (proj₁ sⁿ) , `∀ (proj₂ sⁿ)
    where
      sⁿ = dualʷ (extᵃ η) sʷ

  dualStrictCrossWidening :
    DualActionEnv →
    ∀ {c} →
    StrictCrossWidening c →
    ∃[ d ] StrictCrossNarrowing d
  dualStrictCrossWidening η (cw-funˡ sⁿ tʷ) =
    (proj₁ sʷ ↦ proj₁ tⁿ) , cn-funˡ (proj₂ sʷ) (proj₂ tⁿ)
    where
      sʷ = dualStrictⁿ η sⁿ
      tⁿ = dualʷ η tʷ
  dualStrictCrossWidening η (cw-funʳ sⁿ tʷ) =
    (proj₁ sʷ ↦ proj₁ tⁿ) , cn-funʳ (proj₂ sʷ) (proj₂ tⁿ)
    where
      sʷ = dualⁿ η sⁿ
      tⁿ = dualStrictʷ η tʷ
  dualStrictCrossWidening η (cw-all sʷ) =
    `∀ (proj₁ sⁿ) , cn-all (proj₂ sⁿ)
    where
      sⁿ = dualStrictʷ (extᵃ η) sʷ

  dualʷ :
    DualActionEnv →
    ∀ {c} →
    Widening c →
    ∃[ d ] Narrowing d
  dualʷ η (cross gʷ) =
    proj₁ gⁿ , cross (proj₂ gⁿ)
    where
      gⁿ = dualCrossWidening η gʷ
  dualʷ η id★ = id ★ , id★
  dualʷ η (inst {B = B} sʷ) =
    gen B (proj₁ sⁿ) , gen (proj₂ sⁿ)
    where
      sⁿ = dualʷ (instᵃ η) sʷ
  dualʷ η (tag (＇ α)) with η α
  dualʷ η (tag (＇ α)) | normal = (＇ α) ？ , untag (＇ α)
  dualʷ η (tag (＇ α)) | tag-to-seal = seal ★ α , sealⁿ ★ α
  dualʷ η (tag (＇ α)) | seal-to-tag = (＇ α) ？ , untag (＇ α)
  dualʷ η (tag (‵ ι)) = (‵ ι) ？ , untag (‵ ι)
  dualʷ η (tag ★⇒★) = (★ ⇒ ★) ？ , untag ★⇒★
  dualʷ η (gʷ ︔ (＇ α) !) with η α
  dualʷ η (gʷ ︔ (＇ α) !) | normal =
    (((＇ α) ？) ︔ proj₁ gⁿ) , ((＇ α) ？︔ proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualʷ η (gʷ ︔ (＇ α) !) | tag-to-seal =
    seal ★ α , sealⁿ ★ α
  dualʷ η (gʷ ︔ (＇ α) !) | seal-to-tag =
    (((＇ α) ？) ︔ proj₁ gⁿ) , ((＇ α) ？︔ proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualʷ η (gʷ ︔ (‵ ι) !) =
    (((‵ ι) ？) ︔ proj₁ gⁿ) , ((‵ ι) ？︔ proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualʷ η (gʷ ︔ ★⇒★ !) =
    (((★ ⇒ ★) ？) ︔ proj₁ gⁿ) , (★⇒★ ？︔ proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualʷ η (unsealʷ α A) with η α
  dualʷ η (unsealʷ α A) | normal = seal A α , sealⁿ A α
  dualʷ η (unsealʷ α A) | tag-to-seal = seal A α , sealⁿ A α
  dualʷ η (unsealʷ α A) | seal-to-tag = (＇ α) ？ , untag (＇ α)
  dualʷ η (unseal︔_ α {A = A} sʷ) with η α
  dualʷ η (unseal︔_ α {A = A} sʷ) | normal =
    (proj₁ sⁿ ︔ seal A α) , (proj₂ sⁿ ︔seal α)
    where
      sⁿ = dualStrictʷ η sʷ
  dualʷ η (unseal︔_ α {A = A} sʷ) | tag-to-seal =
    (proj₁ sⁿ ︔ seal A α) , (proj₂ sⁿ ︔seal α)
    where
      sⁿ = dualStrictʷ η sʷ
  dualʷ η (unseal︔_ α {A = A} sʷ) | seal-to-tag =
    (＇ α) ？ , untag (＇ α)

  dualStrictʷ :
    DualActionEnv →
    ∀ {c} →
    StrictWidening c →
    ∃[ d ] StrictNarrowing d
  dualStrictʷ η (strict-crossʷ gʷ) =
    proj₁ gⁿ , strict-crossⁿ (proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualStrictʷ η (strict-inst {B = B} sʷ) =
    gen B (proj₁ sⁿ) , strict-gen (proj₂ sⁿ)
    where
      sⁿ = dualʷ (instᵃ η) sʷ
  dualStrictʷ η (strict-tag (＇ α)) with η α
  dualStrictʷ η (strict-tag (＇ α)) | normal =
    (＇ α) ？ , strict-untag (＇ α)
  dualStrictʷ η (strict-tag (＇ α)) | tag-to-seal =
    seal ★ α , strict-seal ★ α
  dualStrictʷ η (strict-tag (＇ α)) | seal-to-tag =
    (＇ α) ？ , strict-untag (＇ α)
  dualStrictʷ η (strict-tag (‵ ι)) = (‵ ι) ？ , strict-untag (‵ ι)
  dualStrictʷ η (strict-tag ★⇒★) = (★ ⇒ ★) ？ , strict-untag ★⇒★
  dualStrictʷ η (strict-tag-seq gʷ (＇ α)) with η α
  dualStrictʷ η (strict-tag-seq gʷ (＇ α)) | normal =
    (((＇ α) ？) ︔ proj₁ gⁿ) , strict-untag-seq (＇ α) (proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualStrictʷ η (strict-tag-seq gʷ (＇ α)) | tag-to-seal =
    seal ★ α , strict-seal ★ α
  dualStrictʷ η (strict-tag-seq gʷ (＇ α)) | seal-to-tag =
    (((＇ α) ？) ︔ proj₁ gⁿ) , strict-untag-seq (＇ α) (proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualStrictʷ η (strict-tag-seq gʷ (‵ ι)) =
    (((‵ ι) ？) ︔ proj₁ gⁿ) , strict-untag-seq (‵ ι) (proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualStrictʷ η (strict-tag-seq gʷ ★⇒★) =
    (((★ ⇒ ★) ？) ︔ proj₁ gⁿ) , strict-untag-seq ★⇒★ (proj₂ gⁿ)
    where
      gⁿ = dualStrictCrossWidening η gʷ
  dualStrictʷ η (strict-unseal α A) with η α
  dualStrictʷ η (strict-unseal α A) | normal =
    seal A α , strict-seal A α
  dualStrictʷ η (strict-unseal α A) | tag-to-seal =
    seal A α , strict-seal A α
  dualStrictʷ η (strict-unseal α A) | seal-to-tag =
    (＇ α) ？ , strict-untag (＇ α)
  dualStrictʷ η (strict-unseal-seq α {A = A} sʷ) with η α
  dualStrictʷ η (strict-unseal-seq α {A = A} sʷ) | normal =
    (proj₁ sⁿ ︔ seal A α) , strict-seal-seq (proj₂ sⁿ) α
    where
      sⁿ = dualStrictʷ η sʷ
  dualStrictʷ η (strict-unseal-seq α {A = A} sʷ) | tag-to-seal =
    (proj₁ sⁿ ︔ seal A α) , strict-seal-seq (proj₂ sⁿ) α
    where
      sⁿ = dualStrictʷ η sʷ
  dualStrictʷ η (strict-unseal-seq α {A = A} sʷ) | seal-to-tag =
    (＇ α) ？ , strict-untag (＇ α)

------------------------------------------------------------------------
-- Well-Typed Mode-Indexed Narrowing and Widening
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶_⊒_
infix 4 _∣_∣_⊢_∶_⊑_
infix 4 _∣_⊢_∶_⊒_

_∣_∣_⊢_∶_⊒_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × Narrowing c

_∣_∣_⊢_∶_⊑_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × Widening c

_∣_⊢_∶_⊒_ : TyCtx → Store → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ A ⊒ B =
  ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B

infix 4 _∣_⊢_∶ᶜ_⊒_

_∣_⊢_∶ᶜ_⊒_ : TyCtx → Store → Coercion → Ty → Ty → Set
Δ ∣ Σ ⊢ c ∶ᶜ A ⊒ B =
  tag-or-idᵈ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B

infix 4 _∣_∣_⊢ᶜ_∶_⊒_
infix 4 _∣_∣_⊢ᶜ_∶_⊑_

_∣_∣_⊢ᶜ_∶_⊒_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ᶜ c ∶ A ⊒ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossNarrowing c

_∣_∣_⊢ᶜ_∶_⊑_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ᶜ c ∶ A ⊑ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × CrossWidening c

------------------------------------------------------------------------
-- Structural lemmas for typed narrowing and widening
------------------------------------------------------------------------

modeRename-suc-ext :
  ∀ {μ} →
  ModeRename suc μ (extᵈ μ)
modeRename-suc-ext {μ = μ} X = modeIncl-refl {μ = μ} X

modeRename-suc-gen :
  ∀ {μ} →
  ModeRename suc μ (genᵈ μ)
modeRename-suc-gen {μ = μ} X = modeIncl-refl {μ = μ} X

modeRename-suc-inst :
  ∀ {μ} →
  ModeRename suc μ (instᵈ μ)
modeRename-suc-inst {μ = μ} X = modeIncl-refl {μ = μ} X

modeIncl-ext-gen :
  ∀ {μ} →
  ModeIncl (extᵈ μ) (genᵈ μ)
modeIncl-ext-gen zero = refl
modeIncl-ext-gen {μ = μ} (suc X) = modeIncl-refl {μ = μ} X

modeIncl-ext-inst :
  ∀ {μ} →
  ModeIncl (extᵈ μ) (instᵈ μ)
modeIncl-ext-inst zero = refl
modeIncl-ext-inst {μ = μ} (suc X) = modeIncl-refl {μ = μ} X

mutual
  renameCrossNarrowing :
    ∀ ρ {c} →
    CrossNarrowing c →
    CrossNarrowing (renameᶜ ρ c)
  renameCrossNarrowing ρ (id-＇ α) = id-＇ (ρ α)
  renameCrossNarrowing ρ (id-‵ ι) = id-‵ ι
  renameCrossNarrowing ρ (sʷ ↦ tⁿ) =
    renameʷ ρ sʷ ↦ renameⁿ ρ tⁿ
  renameCrossNarrowing ρ (`∀ sⁿ) =
    `∀ (renameⁿ (extᵗ ρ) sⁿ)

  renameStrictCrossNarrowing :
    ∀ ρ {c} →
    StrictCrossNarrowing c →
    StrictCrossNarrowing (renameᶜ ρ c)
  renameStrictCrossNarrowing ρ (cn-funˡ sʷ tⁿ) =
    cn-funˡ (renameStrictʷ ρ sʷ) (renameⁿ ρ tⁿ)
  renameStrictCrossNarrowing ρ (cn-funʳ sʷ tⁿ) =
    cn-funʳ (renameʷ ρ sʷ) (renameStrictⁿ ρ tⁿ)
  renameStrictCrossNarrowing ρ (cn-all sⁿ) =
    cn-all (renameStrictⁿ (extᵗ ρ) sⁿ)

  renameⁿ :
    ∀ ρ {c} →
    Narrowing c →
    Narrowing (renameᶜ ρ c)
  renameⁿ ρ (cross gⁿ) = cross (renameCrossNarrowing ρ gⁿ)
  renameⁿ ρ id★ = id★
  renameⁿ ρ (gen sⁿ) = gen (renameⁿ (extᵗ ρ) sⁿ)
  renameⁿ ρ (untag gG) = untag (renameᵗ-ground ρ gG)
  renameⁿ ρ (gG ？︔ gⁿ) =
    renameᵗ-ground ρ gG ？︔ renameStrictCrossNarrowing ρ gⁿ
  renameⁿ ρ (sealⁿ A α) = sealⁿ (renameᵗ ρ A) (ρ α)
  renameⁿ ρ (_︔seal_ sⁿ α) = renameStrictⁿ ρ sⁿ ︔seal ρ α

  renameStrictⁿ :
    ∀ ρ {c} →
    StrictNarrowing c →
    StrictNarrowing (renameᶜ ρ c)
  renameStrictⁿ ρ (strict-crossⁿ gⁿ) =
    strict-crossⁿ (renameStrictCrossNarrowing ρ gⁿ)
  renameStrictⁿ ρ (strict-gen sⁿ) =
    strict-gen (renameⁿ (extᵗ ρ) sⁿ)
  renameStrictⁿ ρ (strict-untag gG) =
    strict-untag (renameᵗ-ground ρ gG)
  renameStrictⁿ ρ (strict-untag-seq gG gⁿ) =
    strict-untag-seq
      (renameᵗ-ground ρ gG)
      (renameStrictCrossNarrowing ρ gⁿ)
  renameStrictⁿ ρ (strict-seal A α) =
    strict-seal (renameᵗ ρ A) (ρ α)
  renameStrictⁿ ρ (strict-seal-seq sⁿ α) =
    strict-seal-seq (renameStrictⁿ ρ sⁿ) (ρ α)

  renameCrossWidening :
    ∀ ρ {c} →
    CrossWidening c →
    CrossWidening (renameᶜ ρ c)
  renameCrossWidening ρ (id-＇ α) = id-＇ (ρ α)
  renameCrossWidening ρ (id-‵ ι) = id-‵ ι
  renameCrossWidening ρ (sⁿ ↦ tʷ) =
    renameⁿ ρ sⁿ ↦ renameʷ ρ tʷ
  renameCrossWidening ρ (`∀ sʷ) =
    `∀ (renameʷ (extᵗ ρ) sʷ)

  renameStrictCrossWidening :
    ∀ ρ {c} →
    StrictCrossWidening c →
    StrictCrossWidening (renameᶜ ρ c)
  renameStrictCrossWidening ρ (cw-funˡ sⁿ tʷ) =
    cw-funˡ (renameStrictⁿ ρ sⁿ) (renameʷ ρ tʷ)
  renameStrictCrossWidening ρ (cw-funʳ sⁿ tʷ) =
    cw-funʳ (renameⁿ ρ sⁿ) (renameStrictʷ ρ tʷ)
  renameStrictCrossWidening ρ (cw-all sʷ) =
    cw-all (renameStrictʷ (extᵗ ρ) sʷ)

  renameʷ :
    ∀ ρ {c} →
    Widening c →
    Widening (renameᶜ ρ c)
  renameʷ ρ (cross gʷ) = cross (renameCrossWidening ρ gʷ)
  renameʷ ρ id★ = id★
  renameʷ ρ (inst sʷ) = inst (renameʷ (extᵗ ρ) sʷ)
  renameʷ ρ (tag gG) = tag (renameᵗ-ground ρ gG)
  renameʷ ρ (gʷ ︔ gG !) =
    renameStrictCrossWidening ρ gʷ ︔ renameᵗ-ground ρ gG !
  renameʷ ρ (unsealʷ α A) = unsealʷ (ρ α) (renameᵗ ρ A)
  renameʷ ρ (unseal︔_ α sʷ) =
    unseal︔_ (ρ α) (renameStrictʷ ρ sʷ)

  renameStrictʷ :
    ∀ ρ {c} →
    StrictWidening c →
    StrictWidening (renameᶜ ρ c)
  renameStrictʷ ρ (strict-crossʷ gʷ) =
    strict-crossʷ (renameStrictCrossWidening ρ gʷ)
  renameStrictʷ ρ (strict-inst sʷ) =
    strict-inst (renameʷ (extᵗ ρ) sʷ)
  renameStrictʷ ρ (strict-tag gG) =
    strict-tag (renameᵗ-ground ρ gG)
  renameStrictʷ ρ (strict-tag-seq gʷ gG) =
    strict-tag-seq
      (renameStrictCrossWidening ρ gʷ)
      (renameᵗ-ground ρ gG)
  renameStrictʷ ρ (strict-unseal α A) =
    strict-unseal (ρ α) (renameᵗ ρ A)
  renameStrictʷ ρ (strict-unseal-seq α sʷ) =
    strict-unseal-seq (ρ α) (renameStrictʷ ρ sʷ)

narrow-mode-relax :
  ∀ {μ ν Δ Σ A B c} →
  ModeIncl μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  ν ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B
narrow-mode-relax incl (c⊢ , cⁿ) =
  coercion-mode-relax incl c⊢ , cⁿ

widen-mode-relax :
  ∀ {μ ν Δ Σ A B c} →
  ModeIncl μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  ν ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B
widen-mode-relax incl (c⊢ , cʷ) =
  coercion-mode-relax incl c⊢ , cʷ

narrow-weaken :
  ∀ {μ Δ Δ′ Σ Σ′ A B c} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A ⊒ B
narrow-weaken Δ≤Δ′ incl (c⊢ , cⁿ) =
  coercion-weakenᵐ Δ≤Δ′ incl c⊢ , cⁿ

widen-weaken :
  ∀ {μ Δ Δ′ Σ Σ′ A B c} →
  Δ ≤ Δ′ →
  StoreIncl Σ Σ′ →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  μ ∣ Δ′ ∣ Σ′ ⊢ c ∶ A ⊑ B
widen-weaken Δ≤Δ′ incl (c⊢ , cʷ) =
  coercion-weakenᵐ Δ≤Δ′ incl c⊢ , cʷ

narrow-renameᵗ :
  ∀ {μ ν Δ Δ′ Σ A B c ρ} →
  TyRenameWf Δ Δ′ ρ →
  ModeRename ρ μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ
    ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
narrow-renameᵗ {ρ = ρ} hρ hμ (c⊢ , cⁿ) =
  coercion-renameᵗᵐ hρ hμ c⊢ , renameⁿ ρ cⁿ

widen-renameᵗ :
  ∀ {μ ν Δ Δ′ Σ A B c ρ} →
  TyRenameWf Δ Δ′ ρ →
  ModeRename ρ μ ν →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  ν ∣ Δ′ ∣ renameStoreᵗ ρ Σ
    ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊑ renameᵗ ρ B
widen-renameᵗ {ρ = ρ} hρ hμ (c⊢ , cʷ) =
  coercion-renameᵗᵐ hρ hμ c⊢ , renameʷ ρ cʷ

narrow-⇑ᵗ-gen :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  genᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
narrow-⇑ᵗ-gen = narrow-renameᵗ TyRenameWf-suc modeRename-suc-gen

widen-⇑ᵗ-inst :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  instᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ-inst = widen-renameᵗ TyRenameWf-suc modeRename-suc-inst

widen-⇑ᵗ-inst-cons :
  ∀ {μ Δ Σ A B c} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
  instᵈ μ ∣ suc Δ ∣ (zero , ★) ∷ ⟰ᵗ Σ
    ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
widen-⇑ᵗ-inst-cons c⊑ =
  coercion-weakenᵐ ≤-refl StoreIncl-drop (proj₁ c⊑′) ,
  proj₂ c⊑′
  where
    c⊑′ = widen-⇑ᵗ-inst c⊑

mutual
  narrow-src-wf :
    ∀ {μ Δ Σ A B c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    WfTy Δ A
  narrow-src-wf (cast-id hA ok , cross (id-＇ α)) = hA
  narrow-src-wf (cast-id hA ok , cross (id-‵ ι)) = hA
  narrow-src-wf
      (cast-fun s⊢ t⊢ , cross (sʷ ↦ tⁿ)) =
    wf⇒ (widen-tgt-wf (s⊢ , sʷ)) (narrow-src-wf (t⊢ , tⁿ))
  narrow-src-wf (cast-all s⊢ , cross (`∀ sⁿ)) =
    wf∀ (narrow-src-wf (s⊢ , sⁿ))
  narrow-src-wf (cast-id hA ok , id★) = hA
  narrow-src-wf (cast-gen hA occ s⊢ , gen sⁿ) = hA
  narrow-src-wf (cast-untag hG gG ok , untag gG′) = wf★
  narrow-src-wf
      (cast-seq (cast-untag hG gG ok) s⊢ , gG′ ？︔ sⁿ) =
    wf★
  narrow-src-wf (cast-seal hA α∈Σ ok , sealⁿ A α) = hA
  narrow-src-wf
      (cast-seq s⊢ (cast-seal hA α∈Σ ok) , _︔seal_ sⁿ α) =
    narrow-src-wf (s⊢ , strictⁿ→narrow sⁿ)

  widen-tgt-wf :
    ∀ {μ Δ Σ A B c} →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    WfTy Δ B
  widen-tgt-wf (cast-id hA ok , cross (id-＇ α)) = hA
  widen-tgt-wf (cast-id hA ok , cross (id-‵ ι)) = hA
  widen-tgt-wf
      (cast-fun s⊢ t⊢ , cross (sⁿ ↦ tʷ)) =
    wf⇒ (narrow-src-wf (s⊢ , sⁿ)) (widen-tgt-wf (t⊢ , tʷ))
  widen-tgt-wf (cast-all s⊢ , cross (`∀ sʷ)) =
    wf∀ (widen-tgt-wf (s⊢ , sʷ))
  widen-tgt-wf (cast-id hA ok , id★) = hA
  widen-tgt-wf (cast-inst hB occ s⊢ , inst sʷ) = hB
  widen-tgt-wf (cast-tag hG gG ok , tag gG′) = wf★
  widen-tgt-wf
      (cast-seq s⊢ (cast-tag hG gG ok) , sʷ ︔ gG′ !) =
    wf★
  widen-tgt-wf (cast-unseal hA α∈Σ ok , unsealʷ α A) = hA
  widen-tgt-wf
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ) =
    widen-tgt-wf (s⊢ , strictʷ→widen sʷ)

------------------------------------------------------------------------
-- Occurrence preservation for shifted-store composition
------------------------------------------------------------------------

StoreNoOccurs : TyVar → Store → Set
StoreNoOccurs α Σ =
  ∀ {β A} →
  (β , A) ∈ Σ →
  occurs α A ≡ false

StoreNoOccurs-⟰ᵗ :
  ∀ {α Σ} →
  StoreNoOccurs α Σ →
  StoreNoOccurs (suc α) (⟰ᵗ Σ)
StoreNoOccurs-⟰ᵗ {Σ = []} noOcc ()
StoreNoOccurs-⟰ᵗ {α = α} {Σ = (β , A) ∷ Σ} noOcc (here refl) =
  trans (occurs-raise zero α A) (noOcc (here refl))
StoreNoOccurs-⟰ᵗ {Σ = (β , A) ∷ Σ} noOcc (there α∈Σ) =
  StoreNoOccurs-⟰ᵗ (λ β∈Σ → noOcc (there β∈Σ)) α∈Σ

StoreNoOccurs-zero-⟰ᵗ :
  ∀ {Σ} →
  StoreNoOccurs zero (⟰ᵗ Σ)
StoreNoOccurs-zero-⟰ᵗ {Σ = []} ()
StoreNoOccurs-zero-⟰ᵗ {Σ = (α , A) ∷ Σ} (here refl) =
  occurs-raise-fresh zero A
StoreNoOccurs-zero-⟰ᵗ {Σ = (α , A) ∷ Σ} (there α∈Σ) =
  StoreNoOccurs-zero-⟰ᵗ α∈Σ

StoreNoOccurs-inst :
  ∀ {α Σ} →
  StoreNoOccurs α Σ →
  StoreNoOccurs (suc α) ((zero , ★) ∷ ⟰ᵗ Σ)
StoreNoOccurs-inst noOcc (here refl) = refl
StoreNoOccurs-inst noOcc (there α∈Σ) = StoreNoOccurs-⟰ᵗ noOcc α∈Σ

occurs-true-false⊥ :
  ∀ {b} →
  b ≡ true →
  b ≡ false →
  ⊥
occurs-true-false⊥ refl ()

∨-trueʳⁿʷ :
  ∀ b →
  b ∨ true ≡ true
∨-trueʳⁿʷ true = refl
∨-trueʳⁿʷ false = refl

mutual
  narrowing-source-occurs :
    ∀ {μ Δ Σ A B c α} →
    StoreNoOccurs α Σ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    occurs α A ≡ true →
    occurs α B ≡ true
  narrowing-source-occurs noOcc
      (cast-id hA ok , cross (id-＇ β)) occ = occ
  narrowing-source-occurs noOcc
      (cast-id hA ok , cross (id-‵ ι)) ()
  narrowing-source-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sʷ ↦ tⁿ))
      occ
      with occurs α A | inspect (occurs α) A
         | occurs α B | inspect (occurs α) B
  narrowing-source-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sʷ ↦ tⁿ))
      occ | true | [ eqA ] | _ | _ rewrite
        widening-target-occurs {A = A′} {B = A} noOcc
          (s⊢ , sʷ) eqA =
    refl
  narrowing-source-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sʷ ↦ tⁿ))
      occ | false | _ | true | [ eqB ] rewrite
        narrowing-source-occurs {A = B} {B = B′} noOcc
          (t⊢ , tⁿ) eqB =
    ∨-trueʳⁿʷ (occurs α A′)
  narrowing-source-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sʷ ↦ tⁿ))
      () | false | _ | false | _
  narrowing-source-occurs {α = α} noOcc
      (cast-all s⊢ , cross (`∀ sⁿ)) occ =
    narrowing-source-occurs (StoreNoOccurs-⟰ᵗ noOcc) (s⊢ , sⁿ) occ
  narrowing-source-occurs noOcc (cast-id hA ok , id★) ()
  narrowing-source-occurs {α = α} noOcc
      (cast-gen {A = A} hA occB s⊢ , gen sⁿ) occ =
    narrowing-source-occurs (StoreNoOccurs-⟰ᵗ noOcc) (s⊢ , sⁿ)
      (trans (occurs-raise zero α A) occ)
  narrowing-source-occurs noOcc (cast-untag hG gG ok , untag gG′) ()
  narrowing-source-occurs noOcc
      (cast-seq (cast-untag hG gG ok) s⊢ , gG′ ？︔ sⁿ) ()
  narrowing-source-occurs {α = α} noOcc
      (cast-seal {α = β} hA β∈Σ ok , sealⁿ A β)
      occ
      with α ≟ β
  narrowing-source-occurs {α = α} noOcc
      (cast-seal {α = .α} hA β∈Σ ok , sealⁿ A .α)
      occ | yes refl =
    refl
  narrowing-source-occurs {α = α} noOcc
      (cast-seal {α = β} hA β∈Σ ok , sealⁿ A β)
      occ | no α≢β =
    ⊥-elim (occurs-true-false⊥ occ (noOcc β∈Σ))
  narrowing-source-occurs {α = α} noOcc
      (cast-seq s⊢ (cast-seal {α = β} hA β∈Σ ok) ,
       _︔seal_ sⁿ β)
      occ
      with α ≟ β
  narrowing-source-occurs {α = α} noOcc
      (cast-seq s⊢ (cast-seal {α = .α} hA β∈Σ ok) ,
       _︔seal_ sⁿ .α)
      occ | yes refl =
    refl
  narrowing-source-occurs {α = α} noOcc
      (cast-seq s⊢ (cast-seal {α = β} hA β∈Σ ok) ,
       _︔seal_ sⁿ β)
      occ | no α≢β =
    ⊥-elim
      (occurs-true-false⊥
        (narrowing-source-occurs noOcc (s⊢ , strictⁿ→narrow sⁿ) occ)
        (noOcc β∈Σ))

  widening-target-occurs :
    ∀ {μ Δ Σ A B c α} →
    StoreNoOccurs α Σ →
    μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    occurs α B ≡ true →
    occurs α A ≡ true
  widening-target-occurs noOcc
      (cast-id hA ok , cross (id-＇ β)) occ = occ
  widening-target-occurs noOcc
      (cast-id hA ok , cross (id-‵ ι)) ()
  widening-target-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sⁿ ↦ tʷ))
      occ
      with occurs α A′ | inspect (occurs α) A′
         | occurs α B′ | inspect (occurs α) B′
  widening-target-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sⁿ ↦ tʷ))
      occ | true | [ eqA′ ] | _ | _ rewrite
        narrowing-source-occurs {A = A′} {B = A} noOcc
          (s⊢ , sⁿ) eqA′ =
    refl
  widening-target-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sⁿ ↦ tʷ))
      occ | false | _ | true | [ eqB′ ] rewrite
        widening-target-occurs {A = B} {B = B′} noOcc
          (t⊢ , tʷ) eqB′ =
    ∨-trueʳⁿʷ (occurs α A)
  widening-target-occurs {α = α} noOcc
      (cast-fun {A = A} {A′ = A′} {B = B} {B′ = B′}
       s⊢ t⊢ , cross (sⁿ ↦ tʷ))
      () | false | _ | false | _
  widening-target-occurs {α = α} noOcc
      (cast-all s⊢ , cross (`∀ sʷ)) occ =
    widening-target-occurs (StoreNoOccurs-⟰ᵗ noOcc) (s⊢ , sʷ) occ
  widening-target-occurs noOcc (cast-id hA ok , id★) ()
  widening-target-occurs {α = α} noOcc
      (cast-inst {B = B} hB occA s⊢ , inst sʷ) occ =
    widening-target-occurs (StoreNoOccurs-inst noOcc) (s⊢ , sʷ)
      (trans (occurs-raise zero α B) occ)
  widening-target-occurs noOcc (cast-tag hG gG ok , tag gG′) ()
  widening-target-occurs noOcc
      (cast-seq s⊢ (cast-tag hG gG ok) , sʷ ︔ gG′ !) ()
  widening-target-occurs {α = α} noOcc
      (cast-unseal {α = β} hA β∈Σ ok , unsealʷ β A)
      occ
      with α ≟ β
  widening-target-occurs {α = α} noOcc
      (cast-unseal {α = .α} hA β∈Σ ok , unsealʷ .α A)
      occ | yes refl =
    refl
  widening-target-occurs {α = α} noOcc
      (cast-unseal {α = β} hA β∈Σ ok , unsealʷ β A)
      occ | no α≢β =
    ⊥-elim (occurs-true-false⊥ occ (noOcc β∈Σ))
  widening-target-occurs {α = α} noOcc
      (cast-seq (cast-unseal {α = β} hA β∈Σ ok) s⊢ ,
       unseal︔_ β sʷ)
      occ
      with α ≟ β
  widening-target-occurs {α = α} noOcc
      (cast-seq (cast-unseal {α = .α} hA β∈Σ ok) s⊢ ,
       unseal︔_ .α sʷ)
      occ | yes refl =
    refl
  widening-target-occurs {α = α} noOcc
      (cast-seq (cast-unseal {α = β} hA β∈Σ ok) s⊢ ,
       unseal︔_ β sʷ)
      occ | no α≢β =
    ⊥-elim
      (occurs-true-false⊥
        (widening-target-occurs noOcc (s⊢ , strictʷ→widen sʷ) occ)
        (noOcc β∈Σ))

------------------------------------------------------------------------
-- Context imprecision
------------------------------------------------------------------------

-- σ,π  ::=  ∅ | σ, α:=p | σ, α:=A | σ, α:=☆

data StNrw : Set where
  _꞉_ : TyVar → Coercion → StNrw
  _꞉=_⊒ : TyVar → Ty → StNrw
  ⊒_꞉=☆ : TyVar → StNrw

StoreNrw : Set
StoreNrw = List StNrw

srcStoreⁿ : StoreNrw → Store
srcStoreⁿ [] = []
srcStoreⁿ ((X ꞉ p) ∷ σ) = (X , src p) ∷ srcStoreⁿ σ
srcStoreⁿ ((X ꞉= A ⊒) ∷ σ) = srcStoreⁿ σ
srcStoreⁿ ((⊒ X ꞉=☆) ∷ σ) = (X , ★) ∷ srcStoreⁿ σ

⇑ʷ : StNrw → StNrw
⇑ʷ (X ꞉ p) = suc X ꞉ ⇑ᶜ p
⇑ʷ (X ꞉= A ⊒) = suc X ꞉= ⇑ᵗ A ⊒
⇑ʷ (⊒ X ꞉=☆) = ⊒ suc X ꞉=☆

⇑ˢ : StoreNrw → StoreNrw
⇑ˢ = map ⇑ʷ

-- σ ꞉ Σ ⊑ Σ′

data _⊢_꞉_⊑ˢ_ : TyCtx → StoreNrw → Store → Store → Set where
  ⊑ˢ-nil : ∀{Δ}
     ------------------
    → Δ ⊢ [] ꞉ [] ⊑ˢ []
  
  ⊑ˢ-left : ∀{Δ}{Σ Σ′}{A : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     -----------------------------------------
    → Δ ⊢ (X ꞉= A ⊒ ∷ σ) ꞉ ((X , A) ∷ Σ) ⊑ˢ Σ′

  ⊑ˢ-right : ∀{Δ}{Σ Σ′}{X : TyVar}{σ}
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     ---------------------------------------
    → Δ ⊢ (⊒ X ꞉=☆ ∷ σ) ꞉ Σ ⊑ˢ ((X , ★) ∷ Σ′)
    
  ⊑ˢ-both : ∀{Δ}{Σ Σ′}{s}{A A′ : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → WfTy Δ A′
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ A′
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     ---------------------------------------------------
    → Δ ⊢ (X ꞉ s ∷ σ) ꞉ ((X , A) ∷ Σ) ⊑ˢ ((X , A′) ∷ Σ′)

-- σ ꞉ Σ ⊒ Σ′

data _⊢_꞉_⊒ˢ_ : TyCtx → StoreNrw → Store → Store → Set where
  ⊒ˢ-nil : ∀{Δ}
     ------------------
    → Δ ⊢ [] ꞉ [] ⊒ˢ []

  ⊒ˢ-right : ∀{Δ}{Σ Σ′}{A : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′
     -----------------------------------------
    → Δ ⊢ (X ꞉= A ⊒ ∷ σ) ꞉ Σ ⊒ˢ ((X , A) ∷ Σ′)

  ⊒ˢ-left : ∀{Δ}{Σ Σ′}{X : TyVar}{σ}
    → Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′
     ---------------------------------------
    → Δ ⊢ (⊒ X ꞉=☆ ∷ σ) ꞉ ((X , ★) ∷ Σ) ⊒ˢ Σ′

  ⊒ˢ-both : ∀{Δ}{Σ Σ′}{s}{A A′ : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → WfTy Δ A′
    → Δ ∣ Σ ⊢ s ∶ A ⊒ A′
    → Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′
     ---------------------------------------------------
    → Δ ⊢ (X ꞉ s ∷ σ) ꞉ ((X , A) ∷ Σ) ⊒ˢ ((X , A′) ∷ Σ′)
    

-- γ

CtxNrw : Set
CtxNrw = List Coercion

-- Γ ⊑ Γ′

data _∣_⊢_꞉_⊑ᵍ_ : TyCtx → Store → CtxNrw → Ctx → Ctx → Set where
  ⊑ᵍ-nil : ∀{Δ}{Σ} → Δ ∣ Σ ⊢ [] ꞉ [] ⊑ᵍ []
  
  ⊑ᵍ-cons : ∀{Δ}{Σ}{γ : CtxNrw}{Γ Γ′ : Ctx}{s}{A B : Ty}
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B
    → Δ ∣ Σ ⊢ γ ꞉ Γ ⊑ᵍ Γ′
     -------------------------------------
    → Δ ∣ Σ ⊢ (s ∷ γ)꞉ (A ∷ Γ) ⊑ᵍ (B ∷ Γ′)


------------------------------------------------------------------------
-- Narrowing and Widening Equivalence
------------------------------------------------------------------------

data WfTyˢ : TyCtx → Store → Ty → Set where
  wfVarᵗ : ∀ {Δ Σ X} →
    X < Δ →
    WfTyˢ Δ Σ (＇ X)

  wfVarˢ : ∀ {Δ Σ α A} →
    (α , A) ∈ Σ →
    WfTyˢ Δ Σ (＇ α)

  wfBaseˢ : ∀ {Δ Σ ι} →
    WfTyˢ Δ Σ (‵ ι)

  wf★ˢ : ∀ {Δ Σ} →
    WfTyˢ Δ Σ ★

  wf⇒ˢ : ∀ {Δ Σ A B} →
    WfTyˢ Δ Σ A →
    WfTyˢ Δ Σ B →
    WfTyˢ Δ Σ (A ⇒ B)

  wf∀ˢ : ∀ {Δ Σ A} →
    WfTyˢ (suc Δ) (⟰ᵗ Σ) A →
    WfTyˢ Δ Σ (`∀ A)

EndpointWf : TyCtx → Store → Ty → Ty → Set
EndpointWf Δ Σ A B = WfTyˢ Δ Σ A × WfTyˢ Δ Σ B

infix 4 _∣_⊢_≈_∶_⊒_
infix 4 _∣_⊢_≈_∶_⊑_

data _∣_⊢_≈_∶_⊒_ :
    TyCtx → StoreNrw → Coercion → Coercion → Ty → Ty → Set where

  endpointsⁿ : ∀{Δ σ Σ Σ′ A B s t}
    → src s ≡ A
    → tgt s ≡ B
    → src t ≡ A
    → tgt t ≡ B
    → Δ ⊢ σ ꞉ Σ′ ⊒ˢ Σ
    → EndpointWf Δ Σ A B
    → EndpointWf Δ Σ′ A B
    → Δ ∣ Σ ⊢ s ∶ A ⊒ B
    → Δ ∣ Σ′ ⊢ t ∶ A ⊒ B
     ---------------------------
    → Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B

data _∣_⊢_≈_∶_⊑_ :
    TyCtx → StoreNrw → Coercion → Coercion → Ty → Ty → Set where

  endpoints : ∀{Δ σ Σ Σ′ A B s t}
    → src s ≡ A
    → tgt s ≡ B
    → src t ≡ A
    → tgt t ≡ B
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
    → EndpointWf Δ Σ A B
    → EndpointWf Δ Σ′ A B
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B
    → ∃[ μ ] μ ∣ Δ ∣ Σ′ ⊢ t ∶ A ⊑ B
     ---------------------------
    → Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B
