-- This is based on the cambridge22 notes.

module NarrowWiden where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using
  (ℕ; _<_; _≤_; _+_; _∸_; zero; suc; z<s; s<s; z≤n; s≤s;
   s≤s⁻¹)
open import Data.Nat.Properties using
  (_≟_; ≤-refl; ≤-trans; +-assoc; +-comm; +-mono-≤; +-monoʳ-≤;
   +-monoˡ-≤; +-suc; m+[n∸m]≡n; m≤m+n; m≤n+m; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (subst; cong; cong₂; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Coercions
open import proof.TypeProperties
  using
    ( TyRenameWf
    ; TyRenameWf-ext
    ; TyRenameWf-suc
    ; renameᵗ-ground
    ; renameᵗ-preserves-WfTy
    ; renameᵗ-ext-suc-comm
    ; renameStoreᵗ-ext-suc-comm
    )

------------------------------------------------------------------------
-- Narrowing and Widening Grammar
------------------------------------------------------------------------

mutual
  data CrossNarrowing : Coercion → Set where
    id-＇ : ∀ {α} →
      CrossNarrowing (id (＇ α))

    id-‵ : ∀ {ι} →
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

    _︔seal : ∀ {A α s} →
      Narrowing s →
      Narrowing (s ︔ seal A α)

  data CrossWidening : Coercion → Set where
    id-＇ : ∀ {α} →
      CrossWidening (id (＇ α))

    id-‵ : ∀ {ι} →
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

    unseal︔_ : ∀ {α A s} →
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
  dualCrossNarrowing η (id-＇ {α}) = id (＇ α) , id-＇
  dualCrossNarrowing η (id-‵ {ι}) = id (‵ ι) , id-‵
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
    (unseal α ★ ︔ id ★) , unseal︔ id★
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
  dualⁿ η (_︔seal {A = A} {α = α} sⁿ) with η α
  dualⁿ η (_︔seal {A = A} {α = α} sⁿ) | normal =
    (unseal α A ︔ proj₁ sʷ) , unseal︔ proj₂ sʷ
    where
      sʷ = dualⁿ η sⁿ
  dualⁿ η (_︔seal {A = A} {α = α} sⁿ) | tag-to-seal =
    (unseal α A ︔ proj₁ sʷ) , unseal︔ proj₂ sʷ
    where
      sʷ = dualⁿ η sⁿ
  dualⁿ η (_︔seal {A = A} {α = α} sⁿ) | seal-to-tag =
    (id (＇ α) ︔ ((＇ α) !)) , (id-＇ ︔ (＇ α) !)

  dualCrossWidening :
    DualActionEnv →
    ∀ {c} →
    CrossWidening c →
    ∃[ d ] CrossNarrowing d
  dualCrossWidening η (id-＇ {α}) = id (＇ α) , id-＇
  dualCrossWidening η (id-‵ {ι}) = id (‵ ι) , id-‵
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
    (id ★ ︔ seal ★ α) , (id★ ︔seal)
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
  dualʷ η (unseal︔_ {α = α} {A = A} sʷ) with η α
  dualʷ η (unseal︔_ {α = α} {A = A} sʷ) | normal =
    (proj₁ sⁿ ︔ seal A α) , (proj₂ sⁿ ︔seal)
    where
      sⁿ = dualʷ η sʷ
  dualʷ η (unseal︔_ {α = α} {A = A} sʷ) | tag-to-seal =
    (proj₁ sⁿ ︔ seal A α) , (proj₂ sⁿ ︔seal)
    where
      sⁿ = dualʷ η sʷ
  dualʷ η (unseal︔_ {α = α} {A = A} sʷ) | seal-to-tag =
    (((＇ α) ？) ︔ id (＇ α)) , ((＇ α) ？︔ id-＇)

------------------------------------------------------------------------
-- Well-Typed Mode-Indexed Narrowing and Widening
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_∶_⊒_
infix 4 _∣_∣_⊢_∶_⊑_

_∣_∣_⊢_∶_⊒_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × Narrowing c

_∣_∣_⊢_∶_⊑_ : ModeEnv → TyCtx → Store → Coercion → Ty → Ty → Set
μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊑ B =
  (μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B) × Widening c

------------------------------------------------------------------------
-- Context widening
------------------------------------------------------------------------

-- σ,π  ::=  ∅ | σ, α:=p | σ, α:=A | σ, α:=☆

data StWid : Set where
  _꞉_ : TyVar → Coercion → StWid
  _꞉=_⊑ : TyVar → Ty → StWid
  ⊑_꞉=☆ : TyVar → StWid

StoreWid : Set
StoreWid = List StWid

⇑ʷ : StWid → StWid
⇑ʷ (X ꞉ p) = suc X ꞉ ⇑ᶜ p
⇑ʷ (X ꞉= A ⊑) = suc X ꞉= ⇑ᵗ A ⊑
⇑ʷ (⊑ X ꞉=☆) = ⊑ suc X ꞉=☆

⇑ˢ : StoreWid → StoreWid
⇑ˢ = map ⇑ʷ

-- σ ꞉ Σ ⊑ Σ′

data _⊢_꞉_⊑ˢ_ : TyCtx → StoreWid → Store → Store → Set where
  ⊑ˢ-nil : ∀{Δ}
     ------------------
    → Δ ⊢ [] ꞉ [] ⊑ˢ []
  
  ⊑ˢ-left : ∀{Δ}{Σ Σ′}{A : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     -----------------------------------------
    → Δ ⊢ (X ꞉= A ⊑ ∷ σ) ꞉ ((X , A) ∷ Σ) ⊑ˢ Σ′

  ⊑ˢ-right : ∀{Δ}{Σ Σ′}{X : TyVar}{σ}
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     ---------------------------------------
    → Δ ⊢ (⊑ X ꞉=☆ ∷ σ) ꞉ Σ ⊑ˢ ((X , ★) ∷ Σ′)
    
  ⊑ˢ-both : ∀{Δ}{Σ Σ′}{s}{A A′ : Ty}{X : TyVar}{σ}
    → WfTy Δ A
    → WfTy Δ A′
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ A′
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
     ---------------------------------------------------
    → Δ ⊢ (X ꞉ s ∷ σ) ꞉ ((X , A) ∷ Σ) ⊑ˢ ((X , A′) ∷ Σ′)
    

-- γ

CtxWid : Set
CtxWid = List Coercion

-- Γ ⊑ Γ′

data _∣_⊢_꞉_⊑ᵍ_ : TyCtx → Store → CtxWid → Ctx → Ctx → Set where
  ⊑ᵍ-nil : ∀{Δ}{Σ} → Δ ∣ Σ ⊢ [] ꞉ [] ⊑ᵍ []
  
  ⊑ᵍ-cons : ∀{Δ}{Σ}{γ : CtxWid}{Γ Γ′ : Ctx}{s}{A B : Ty}
    → ∃[ μ ] μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ B
    → Δ ∣ Σ ⊢ γ ꞉ Γ ⊑ᵍ Γ′
     -------------------------------------
    → Δ ∣ Σ ⊢ (s ∷ γ)꞉ (A ∷ Γ) ⊑ᵍ (B ∷ Γ′)


------------------------------------------------------------------------
-- Narrowing and Widening Equivalence
------------------------------------------------------------------------

infix 4 _⊨_≈id_

data _⊨_≈id_ : StoreWid → TyVar → Ty → Set where
  ≈id-id : ∀{σ α A}
    → (α ꞉ id A) ∈ σ
      ----------------
    → σ ⊨ α ≈id A

  ≈id-exact : ∀{σ α A}
    → (α ꞉= A ⊑) ∈ σ
      ----------------
    → σ ⊨ α ≈id A

infix 4 _∣_⊢_≈_∶_⊒_
infix 4 _∣_⊢_≈_∶_⊑_

mutual
  data _∣_⊢_≈_∶_⊒_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    id≈idⁿ : ∀{Δ σ A}{aA : Atom A}
      → WfTy Δ A
       -------------------------------
      → Δ ∣ σ ⊢ id A ≈ id A ∶ A ⊒ A

    ↦≈↦ⁿ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ s′ ∶ A′ ⊑ A
      → Δ ∣ σ ⊢ t ≈ t′ ∶ B ⊒ B′
       -------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ (s′ ↦ t′) ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)

    ∀≈∀ⁿ : ∀{Δ σ A B s t}
      → suc Δ ∣ ⇑ˢ σ ⊢ s ≈ t ∶ A ⊒ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ (`∀ s) ≈ (`∀ t) ∶ (`∀ A) ⊒ (`∀ B)

    ν≈νⁿ : ∀{Δ σ A B s t}
      → WfTy Δ A
      → suc Δ ∣ ⇑ˢ σ ⊢ s ≈ t ∶ ⇑ᵗ A ⊒ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ gen A s ≈ gen A t ∶ A ⊒ (`∀ B)

    ?≈?ⁿ : ∀{Δ σ G B s t}
      → WfTy Δ G
      → Ground G
      → Δ ∣ σ ⊢ s ≈ t ∶ G ⊒ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ ((G ？) ︔ s) ≈ ((G ？) ︔ t) ∶ ★ ⊒ B

    ?≈seal★ⁿ : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ (id ★ ︔ seal ★ α) ∶ ★ ⊒ ＇ α

    seal★≈?ⁿ : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id ★ ︔ seal ★ α)
          ≈ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

    ?≈sealGⁿ : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ (((G ？) ︔ id G) ︔ seal G α) ∶ ★ ⊒ ＇ α

    sealG≈?ⁿ : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((G ？) ︔ id G) ︔ seal G α)
          ≈ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

  data _∣_⊢_≈_∶_⊑_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    id≈id : ∀{Δ σ A}{aA : Atom A}
      → WfTy Δ A
       ------------------------------
      → Δ ∣ σ ⊢ id A ≈ id A ∶ A ⊑ A

    !≈! : ∀{Δ σ A G g g′}
      → WfTy Δ G
      → Ground G
      → Δ ∣ σ ⊢ g ≈ g′ ∶ A ⊑ G
       ------------------------------------------------
      → Δ ∣ σ ⊢ (g ︔ (G !)) ≈ (g′ ︔ (G !)) ∶ A ⊑ ★

    !≈unseal★ : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ (unseal α ★ ︔ id ★) ∶ ＇ α ⊑ ★

    unseal★≈! : ∀{Δ σ α}
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (unseal α ★ ︔ id ★)
          ≈ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★

    !≈unsealG : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ ((unseal α G ︔ id G) ︔ (G !)) ∶ ＇ α ⊑ ★

    unsealG≈! : ∀{Δ σ α G}{aG : Atom G}
      → WfTy Δ G
      → Ground G
      → (α ꞉ id G) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ ((unseal α G ︔ id G) ︔ (G !))
          ≈ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★

    ↦≈↦ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ s′ ∶ A′ ⊒ A
      → Δ ∣ σ ⊢ t ≈ t′ ∶ B ⊑ B′
       ------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ (s′ ↦ t′) ∶ (A ⇒ B) ⊑ (A′ ⇒ B′)

    ∀≈∀ : ∀{Δ σ A B s t}
      → suc Δ ∣ ⇑ˢ σ ⊢ s ≈ t ∶ A ⊑ B
       -----------------------------------------------
      → Δ ∣ σ ⊢ (`∀ s) ≈ (`∀ t) ∶ (`∀ A) ⊑ (`∀ B)

    ν≈ν : ∀{Δ σ A B s t}
      → WfTy Δ B
      → suc Δ ∣ (0 ꞉ id ★) ∷ ⇑ˢ σ ⊢ s ≈ t ∶ A ⊑ ⇑ᵗ B
       ------------------------------------------------
      → Δ ∣ σ ⊢ inst B s ≈ inst B t ∶ (`∀ A) ⊑ B

------------------------------------------------------------------------
-- Term-narrowing cast side-condition equivalence
------------------------------------------------------------------------

infix 4 _∣_⊢_≈ᵗ_∶_⊒_
infix 4 _∣_⊢_≈ᵗ_∶_⊑_

mutual
  data _∣_⊢_≈ᵗ_∶_⊒_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    ≈ᵗ-oldⁿ : ∀{Δ σ A B s t}
      → Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B
       -------------------------------
      → Δ ∣ σ ⊢ s ≈ᵗ t ∶ A ⊒ B

    ↦≈↦ᵗⁿ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ᵗ s′ ∶ A′ ⊑ A
      → Δ ∣ σ ⊢ t ≈ᵗ t′ ∶ B ⊒ B′
       -------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ᵗ (s′ ↦ t′) ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)

    ?≈seal★ᵗⁿ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ᵗ (id ★ ︔ seal ★ α) ∶ ★ ⊒ ＇ α

    seal★≈?ᵗⁿ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id ★ ︔ seal ★ α)
          ≈ᵗ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

    ?≈sealGᵗⁿ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ᵗ (((G ？) ︔ id G) ︔ seal G α) ∶ ★ ⊒ ＇ α

    sealG≈?ᵗⁿ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((G ？) ︔ id G) ︔ seal G α)
          ≈ᵗ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

  data _∣_⊢_≈ᵗ_∶_⊑_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    ≈ᵗ-old : ∀{Δ σ A B s t}
      → Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B
       ------------------------------
      → Δ ∣ σ ⊢ s ≈ᵗ t ∶ A ⊑ B

    ↦≈↦ᵗ : ∀{Δ σ A A′ B B′ s t s′ t′}
      → Δ ∣ σ ⊢ s ≈ᵗ s′ ∶ A′ ⊒ A
      → Δ ∣ σ ⊢ t ≈ᵗ t′ ∶ B ⊑ B′
       ------------------------------------------------
      → Δ ∣ σ ⊢ (s ↦ t) ≈ᵗ (s′ ↦ t′) ∶ (A ⇒ B) ⊑ (A′ ⇒ B′)

    !≈unseal★ᵗ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ᵗ (unseal α ★ ︔ id ★) ∶ ＇ α ⊑ ★

    unseal★≈!ᵗ : ∀{Δ σ α}
      → σ ⊨ α ≈id ★
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (unseal α ★ ︔ id ★)
          ≈ᵗ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★

    !≈unsealGᵗ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ᵗ ((unseal α G ︔ id G) ︔ (G !)) ∶ ＇ α ⊑ ★

    unsealG≈!ᵗ : ∀{Δ σ α G}
      → WfTy Δ G
      → Ground G
      → σ ⊨ α ≈id G
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ ((unseal α G ︔ id G) ︔ (G !))
          ≈ᵗ (id (＇ α) ︔ ((＇ α) !)) ∶ ＇ α ⊑ ★
