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

  data Narrowing : Coercion → Set where
    cross : ∀ {g} →
      CrossNarrowing g →
      Narrowing g

    id★ :
      Narrowing (id ★)

    gen : ∀ {A s} →
      Narrowing s →
      Narrowing (gen A s)

    _？︔_ : ∀ {G g} →
      Ground G →
      CrossNarrowing g →
      Narrowing ((G ？) ︔ g)

    _︔seal_ : ∀ {A s} →
      Narrowing s →
      (α : TyVar) →
      Narrowing (s ︔ seal A α)

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

  data Widening : Coercion → Set where
    cross : ∀ {g} →
      CrossWidening g →
      Widening g

    id★ :
      Widening (id ★)

    inst : ∀ {B s} →
      Widening s →
      Widening (inst B s)

    _︔_! : ∀ {G g} →
      CrossWidening g →
      Ground G →
      Widening (g ︔ (G !))

    unseal︔_ : (α : TyVar) → ∀ {A s} →
      Widening s →
      Widening (unseal α A ︔ s)

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
  dualⁿ η ((＇ α) ？︔ gⁿ) with η α
  dualⁿ η ((＇ α) ？︔ gⁿ) | normal =
    (proj₁ gʷ ︔ ((＇ α) !)) , (proj₂ gʷ ︔ (＇ α) !)
    where
      gʷ = dualCrossNarrowing η gⁿ
  dualⁿ η ((＇ α) ？︔ gⁿ) | tag-to-seal =
    (unseal α ★ ︔ id ★) , unseal︔_ α id★
  dualⁿ η ((＇ α) ？︔ gⁿ) | seal-to-tag =
    (proj₁ gʷ ︔ ((＇ α) !)) , (proj₂ gʷ ︔ (＇ α) !)
    where
      gʷ = dualCrossNarrowing η gⁿ
  dualⁿ η ((‵ ι) ？︔ gⁿ) =
    (proj₁ gʷ ︔ ((‵ ι) !)) , (proj₂ gʷ ︔ (‵ ι) !)
    where
      gʷ = dualCrossNarrowing η gⁿ
  dualⁿ η (★⇒★ ？︔ gⁿ) =
    (proj₁ gʷ ︔ ((★ ⇒ ★) !)) , (proj₂ gʷ ︔ ★⇒★ !)
    where
      gʷ = dualCrossNarrowing η gⁿ
  dualⁿ η (_︔seal_ {A = A} sⁿ α) with η α
  dualⁿ η (_︔seal_ {A = A} sⁿ α) | normal =
    (unseal α A ︔ proj₁ sʷ) , unseal︔_ α (proj₂ sʷ)
    where
      sʷ = dualⁿ η sⁿ
  dualⁿ η (_︔seal_ {A = A} sⁿ α) | tag-to-seal =
    (unseal α A ︔ proj₁ sʷ) , unseal︔_ α (proj₂ sʷ)
    where
      sʷ = dualⁿ η sⁿ
  dualⁿ η (_︔seal_ {A = A} sⁿ α) | seal-to-tag =
    (id (＇ α) ︔ ((＇ α) !)) , (id-＇ α ︔ (＇ α) !)

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
  dualʷ η (gʷ ︔ (＇ α) !) with η α
  dualʷ η (gʷ ︔ (＇ α) !) | normal =
    (((＇ α) ？) ︔ proj₁ gⁿ) , ((＇ α) ？︔ proj₂ gⁿ)
    where
      gⁿ = dualCrossWidening η gʷ
  dualʷ η (gʷ ︔ (＇ α) !) | tag-to-seal =
    (id ★ ︔ seal ★ α) , (id★ ︔seal α)
  dualʷ η (gʷ ︔ (＇ α) !) | seal-to-tag =
    (((＇ α) ？) ︔ proj₁ gⁿ) , ((＇ α) ？︔ proj₂ gⁿ)
    where
      gⁿ = dualCrossWidening η gʷ
  dualʷ η (gʷ ︔ (‵ ι) !) =
    (((‵ ι) ？) ︔ proj₁ gⁿ) , ((‵ ι) ？︔ proj₂ gⁿ)
    where
      gⁿ = dualCrossWidening η gʷ
  dualʷ η (gʷ ︔ ★⇒★ !) =
    (((★ ⇒ ★) ？) ︔ proj₁ gⁿ) , (★⇒★ ？︔ proj₂ gⁿ)
    where
      gⁿ = dualCrossWidening η gʷ
  dualʷ η (unseal︔_ α {A = A} sʷ) with η α
  dualʷ η (unseal︔_ α {A = A} sʷ) | normal =
    (proj₁ sⁿ ︔ seal A α) , (proj₂ sⁿ ︔seal α)
    where
      sⁿ = dualʷ η sʷ
  dualʷ η (unseal︔_ α {A = A} sʷ) | tag-to-seal =
    (proj₁ sⁿ ︔ seal A α) , (proj₂ sⁿ ︔seal α)
    where
      sⁿ = dualʷ η sʷ
  dualʷ η (unseal︔_ α {A = A} sʷ) | seal-to-tag =
    (((＇ α) ？) ︔ id (＇ α)) , ((＇ α) ？︔ id-＇ α)

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

  renameⁿ :
    ∀ ρ {c} →
    Narrowing c →
    Narrowing (renameᶜ ρ c)
  renameⁿ ρ (cross gⁿ) = cross (renameCrossNarrowing ρ gⁿ)
  renameⁿ ρ id★ = id★
  renameⁿ ρ (gen sⁿ) = gen (renameⁿ (extᵗ ρ) sⁿ)
  renameⁿ ρ (gG ？︔ gⁿ) =
    renameᵗ-ground ρ gG ？︔ renameCrossNarrowing ρ gⁿ
  renameⁿ ρ (_︔seal_ sⁿ α) = renameⁿ ρ sⁿ ︔seal ρ α

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

  renameʷ :
    ∀ ρ {c} →
    Widening c →
    Widening (renameᶜ ρ c)
  renameʷ ρ (cross gʷ) = cross (renameCrossWidening ρ gʷ)
  renameʷ ρ id★ = id★
  renameʷ ρ (inst sʷ) = inst (renameʷ (extᵗ ρ) sʷ)
  renameʷ ρ (gʷ ︔ gG !) =
    renameCrossWidening ρ gʷ ︔ renameᵗ-ground ρ gG !
  renameʷ ρ (unseal︔_ α sʷ) = unseal︔_ (ρ α) (renameʷ ρ sʷ)

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
  narrow-src-wf
      (cast-seq (cast-untag hG gG ok) s⊢ , gG′ ？︔ sⁿ) =
    wf★
  narrow-src-wf
      (cast-seq s⊢ (cast-seal hA α∈Σ ok) , _︔seal_ sⁿ α) =
    narrow-src-wf (s⊢ , sⁿ)

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
  widen-tgt-wf
      (cast-seq s⊢ (cast-tag hG gG ok) , sʷ ︔ gG′ !) =
    wf★
  widen-tgt-wf
      (cast-seq (cast-unseal hA α∈Σ ok) s⊢ , unseal︔_ α sʷ) =
    widen-tgt-wf (s⊢ , sʷ)

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
  narrowing-source-occurs noOcc
      (cast-seq (cast-untag hG gG ok) s⊢ , gG′ ？︔ sⁿ) ()
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
        (narrowing-source-occurs noOcc (s⊢ , sⁿ) occ)
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
  widening-target-occurs noOcc
      (cast-seq s⊢ (cast-tag hG gG ok) , sʷ ︔ gG′ !) ()
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
        (widening-target-occurs noOcc (s⊢ , sʷ) occ)
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
