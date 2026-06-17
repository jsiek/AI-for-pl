-- This is based on the cambridge22 notes.

module NarrowWiden where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (subst)
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
-- Narrowing and Widening
------------------------------------------------------------------------

infix 4 _∣_⊢_∶_⊒_
infix 4 _∣_⊢_∶_⊑_

mutual
  data _∣_⊢_∶_⊒_ : TyCtx → Store → Coercion → Ty → Ty → Set where

    nrw-id : ∀{Δ : TyCtx}{Σ : Store}{A : Ty}
      → WfTy Δ A
      → Atom A
       ---------------------
      → Δ ∣ Σ ⊢ id A ∶ A ⊒ A

    nrw-fun : ∀{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
      → Δ ∣ Σ ⊢ s ∶ A′ ⊑ A
      → Δ ∣ Σ ⊢ t ∶ B ⊒ B′
       ---------------------------------------
      → Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) ⊒ (A′ ⇒ B′)

    nrw-all : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊒ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) ⊒ (`∀ B)

    -- ν
    nrw-gen : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → WfTy Δ A
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ ⇑ᵗ A ⊒ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (gen A s) ∶ A ⊒ (`∀ B)

    nrw-untag : ∀{Δ : TyCtx}{Σ : Store}{G B : Ty}{g}
      → WfTy Δ G
      → Ground G
      → Δ ∣ Σ ⊢ g ∶ G ⊒ B
       -----------------------------
      → Δ ∣ Σ ⊢ ((G ？) ︔ g) ∶ ★ ⊒ B

    -- α♯ 
    nrw-seal : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A A′ : Ty}{s}
      → WfTy Δ A′
      → (α , A′) ∈ Σ
      → Δ ∣ Σ ⊢ s ∶ A ⊒ A′
       ------------------------------------
      → Δ ∣ Σ ⊢ (s ︔ seal A′ α) ∶ A ⊒ (＇ α)


  data _∣_⊢_∶_⊑_ : TyCtx → Store → Coercion → Ty → Ty → Set where

    wid-id : ∀{Δ : TyCtx}{Σ : Store}{A : Ty}
      → WfTy Δ A
      → Atom A
       ---------------------
      → Δ ∣ Σ ⊢ id A ∶ A ⊑ A

    wid-fun : ∀{Δ : TyCtx}{Σ : Store}{A A′ B B′ : Ty}{s t : Coercion}
      → Δ ∣ Σ ⊢ s ∶ A′ ⊒ A
      → Δ ∣ Σ ⊢ t ∶ B ⊑ B′
       ---------------------------------------
      → Δ ∣ Σ ⊢ (s ↦ t) ∶ (A ⇒ B) ⊑ (A′ ⇒ B′)

    wid-all : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → suc Δ ∣ ⟰ᵗ Σ ⊢ s ∶ A ⊑ B
       ----------------------------------
      → Δ ∣ Σ ⊢ (`∀ s) ∶ (`∀ A) ⊑ (`∀ B)

    -- ν̅ 
    wid-inst : ∀{Δ : TyCtx}{Σ : Store}{A B : Ty}{s : Coercion}
      → WfTy Δ B
      → suc Δ ∣ (0 , ★) ∷ ⟰ᵗ Σ ⊢ s ∶ A ⊑ ⇑ᵗ B
       ----------------------------------------
      → Δ ∣ Σ ⊢ (inst B s) ∶ (`∀ A) ⊑ B

    wid-tag : ∀{Δ : TyCtx}{Σ : Store}{A G : Ty}{g : Coercion}
      → WfTy Δ G
      → Ground G
      → Δ ∣ Σ ⊢ g ∶ A ⊑ G
       ----------------------------
      → Δ ∣ Σ ⊢ (g ︔ (G !)) ∶ A ⊑ ★

    -- α♭
    wid-unseal : ∀{Δ : TyCtx}{Σ : Store}{α : TyVar}{A′ B : Ty}{s : Coercion}
      → WfTy Δ A′
      → (α , A′) ∈ Σ
      → Δ ∣ Σ ⊢ s ∶ A′ ⊑ B
       ---------------------------------------
      → Δ ∣ Σ ⊢ (unseal α A′ ︔ s) ∶ (＇ α) ⊑ B


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
    → Δ ∣ Σ ⊢ s ∶ A ⊑ A′
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
    → Δ ∣ Σ ⊢ s ∶ A ⊑ B
    → Δ ∣ Σ ⊢ γ ꞉ Γ ⊑ᵍ Γ′
     -------------------------------------
    → Δ ∣ Σ ⊢ (s ∷ γ)꞉ (A ∷ Γ) ⊑ᵍ (B ∷ Γ′)


------------------------------------------------------------------------
-- Narrowing and Widening Equivalence
------------------------------------------------------------------------

private
  renameᵗ-atom :
    ∀ ρ {A} →
    Atom A →
    Atom (renameᵗ ρ A)
  renameᵗ-atom ρ (＇ α) = ＇ (ρ α)
  renameᵗ-atom ρ (‵ ι) = ‵ ι
  renameᵗ-atom ρ ★ = ★

  ∈-renameStoreᵗ :
    ∀ ρ {Σ α A} →
    (α , A) ∈ Σ →
    (ρ α , renameᵗ ρ A) ∈ renameStoreᵗ ρ Σ
  ∈-renameStoreᵗ ρ (here refl) = here refl
  ∈-renameStoreᵗ ρ (there x∈) = there (∈-renameStoreᵗ ρ x∈)

  mutual
    narrow-renameᵗ :
      ∀ {Δ Δ′ Σ A B c ρ} →
      TyRenameWf Δ Δ′ ρ →
      Δ ∣ Σ ⊢ c ∶ A ⊒ B →
      Δ′ ∣ renameStoreᵗ ρ Σ
        ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊒ renameᵗ ρ B
    narrow-renameᵗ hρ (nrw-id hA atA) =
      nrw-id (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-atom _ atA)
    narrow-renameᵗ hρ (nrw-fun s t) =
      nrw-fun (widen-renameᵗ hρ s) (narrow-renameᵗ hρ t)
    narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (nrw-all s) =
      nrw-all
        (subst
          (λ Σ′ → suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (narrow-renameᵗ (TyRenameWf-ext hρ) s))
    narrow-renameᵗ {Δ′ = Δ′} {Σ = Σ} {A = A} {ρ = ρ}
        hρ (nrw-gen hA s) =
      nrw-gen
        (renameᵗ-preserves-WfTy hA hρ)
        (subst
          (λ T → suc Δ′ ∣ ⟰ᵗ (renameStoreᵗ ρ Σ)
            ⊢ renameᶜ (extᵗ ρ) _ ∶ T ⊒ _)
          (renameᵗ-ext-suc-comm ρ A)
          (subst
            (λ Σ′ → suc Δ′ ∣ Σ′
              ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊒ _)
            (renameStoreᵗ-ext-suc-comm ρ Σ)
            (narrow-renameᵗ (TyRenameWf-ext hρ) s)))
    narrow-renameᵗ hρ (nrw-untag hG gG s) =
      nrw-untag
        (renameᵗ-preserves-WfTy hG hρ)
        (renameᵗ-ground _ gG)
        (narrow-renameᵗ hρ s)
    narrow-renameᵗ hρ (nrw-seal hA′ α∈Σ s) =
      nrw-seal
        (renameᵗ-preserves-WfTy hA′ hρ)
        (∈-renameStoreᵗ _ α∈Σ)
        (narrow-renameᵗ hρ s)

    widen-renameᵗ :
      ∀ {Δ Δ′ Σ A B c ρ} →
      TyRenameWf Δ Δ′ ρ →
      Δ ∣ Σ ⊢ c ∶ A ⊑ B →
      Δ′ ∣ renameStoreᵗ ρ Σ
        ⊢ renameᶜ ρ c ∶ renameᵗ ρ A ⊑ renameᵗ ρ B
    widen-renameᵗ hρ (wid-id hA atA) =
      wid-id (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-atom _ atA)
    widen-renameᵗ hρ (wid-fun s t) =
      wid-fun (narrow-renameᵗ hρ s) (widen-renameᵗ hρ t)
    widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {ρ = ρ} hρ (wid-all s) =
      wid-all
        (subst
          (λ Σ′ → suc Δ′ ∣ Σ′
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
          (renameStoreᵗ-ext-suc-comm ρ Σ)
          (widen-renameᵗ (TyRenameWf-ext hρ) s))
    widen-renameᵗ {Δ′ = Δ′} {Σ = Σ} {B = B} {ρ = ρ}
        hρ (wid-inst hB s) =
      wid-inst
        (renameᵗ-preserves-WfTy hB hρ)
        (subst
          (λ T → suc Δ′
            ∣ (zero , ★) ∷ ⟰ᵗ (renameStoreᵗ ρ Σ)
            ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ T)
          (renameᵗ-ext-suc-comm ρ B)
          (subst
            (λ Σ′ → suc Δ′ ∣ (zero , ★) ∷ Σ′
              ⊢ renameᶜ (extᵗ ρ) _ ∶ _ ⊑ _)
            (renameStoreᵗ-ext-suc-comm ρ Σ)
            (widen-renameᵗ (TyRenameWf-ext hρ) s)))
    widen-renameᵗ hρ (wid-tag hG gG s) =
      wid-tag
        (renameᵗ-preserves-WfTy hG hρ)
        (renameᵗ-ground _ gG)
        (widen-renameᵗ hρ s)
    widen-renameᵗ hρ (wid-unseal hA′ α∈Σ s) =
      wid-unseal
        (renameᵗ-preserves-WfTy hA′ hρ)
        (∈-renameStoreᵗ _ α∈Σ)
        (widen-renameᵗ hρ s)

  narrow-⇑ᵗ :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊒ B →
    suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
  narrow-⇑ᵗ = narrow-renameᵗ TyRenameWf-suc

  widen-⇑ᵗ :
    ∀ {Δ Σ A B c} →
    Δ ∣ Σ ⊢ c ∶ A ⊑ B →
    suc Δ ∣ ⟰ᵗ Σ ⊢ ⇑ᶜ c ∶ ⇑ᵗ A ⊑ ⇑ᵗ B
  widen-⇑ᵗ = widen-renameᵗ TyRenameWf-suc

  StoreWid-⇑ˢ :
    ∀ {Δ σ Σ Σ′} →
    Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′ →
    suc Δ ⊢ ⇑ˢ σ ꞉ ⟰ᵗ Σ ⊑ˢ ⟰ᵗ Σ′
  StoreWid-⇑ˢ ⊑ˢ-nil = ⊑ˢ-nil
  StoreWid-⇑ˢ (⊑ˢ-left hA σ⊢) =
    ⊑ˢ-left (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
      (StoreWid-⇑ˢ σ⊢)
  StoreWid-⇑ˢ (⊑ˢ-right σ⊢) =
    ⊑ˢ-right (StoreWid-⇑ˢ σ⊢)
  StoreWid-⇑ˢ (⊑ˢ-both hA hA′ s⊢ σ⊢) =
    ⊑ˢ-both
      (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
      (renameᵗ-preserves-WfTy hA′ TyRenameWf-suc)
      (widen-⇑ᵗ s⊢)
      (StoreWid-⇑ˢ σ⊢)

  StoreWid-id★∈ :
    ∀ {Δ σ Σ Σ′ α} →
    Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′ →
    (α ꞉ id ★) ∈ σ →
    (α , ★) ∈ Σ × (α , ★) ∈ Σ′
  StoreWid-id★∈ ⊑ˢ-nil ()
  StoreWid-id★∈ (⊑ˢ-left hA σ⊢) (there α∈σ)
      with StoreWid-id★∈ σ⊢ α∈σ
  StoreWid-id★∈ (⊑ˢ-left hA σ⊢) (there α∈σ)
      | α∈Σ , α∈Σ′ =
    there α∈Σ , α∈Σ′
  StoreWid-id★∈ (⊑ˢ-right σ⊢) (there α∈σ)
      with StoreWid-id★∈ σ⊢ α∈σ
  StoreWid-id★∈ (⊑ˢ-right σ⊢) (there α∈σ)
      | α∈Σ , α∈Σ′ =
    α∈Σ , there α∈Σ′
  StoreWid-id★∈ (⊑ˢ-both hA hA′ (wid-id h★ at★) σ⊢) (here refl) =
    here refl , here refl
  StoreWid-id★∈ (⊑ˢ-both hA hA′ s⊢ σ⊢) (there α∈σ)
      with StoreWid-id★∈ σ⊢ α∈σ
  StoreWid-id★∈ (⊑ˢ-both hA hA′ s⊢ σ⊢) (there α∈σ)
      | α∈Σ , α∈Σ′ =
    there α∈Σ , there α∈Σ′

infix 4 _∣_⊢_≈_∶_⊒_
infix 4 _∣_⊢_≈_∶_⊑_

mutual
  data _∣_⊢_≈_∶_⊒_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    id≈idⁿ : ∀{Δ σ A}
      → WfTy Δ A
      → Atom A
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

    ?≈sealⁿ : ∀{Δ σ α}
      → WfTy Δ (＇ α)
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (((＇ α) ？) ︔ id (＇ α))
          ≈ (id ★ ︔ seal ★ α) ∶ ★ ⊒ ＇ α

    seal≈?ⁿ : ∀{Δ σ α}
      → WfTy Δ (＇ α)
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id ★ ︔ seal ★ α)
          ≈ (((＇ α) ？) ︔ id (＇ α)) ∶ ★ ⊒ ＇ α

  data _∣_⊢_≈_∶_⊑_ :
      TyCtx → StoreWid → Coercion → Coercion → Ty → Ty → Set where

    id≈id : ∀{Δ σ A}
      → WfTy Δ A
      → Atom A
       ------------------------------
      → Δ ∣ σ ⊢ id A ≈ id A ∶ A ⊑ A

    !≈! : ∀{Δ σ A G g g′}
      → WfTy Δ G
      → Ground G
      → Δ ∣ σ ⊢ g ≈ g′ ∶ A ⊑ G
       ------------------------------------------------
      → Δ ∣ σ ⊢ (g ︔ (G !)) ≈ (g′ ︔ (G !)) ∶ A ⊑ ★

    !≈unseal : ∀{Δ σ α}
      → WfTy Δ (＇ α)
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (id (＇ α) ︔ ((＇ α) !))
          ≈ (unseal α ★ ︔ id ★) ∶ ＇ α ⊑ ★

    unseal≈! : ∀{Δ σ α}
      → WfTy Δ (＇ α)
      → (α ꞉ id ★) ∈ σ
       ---------------------------------------------------------
      → Δ ∣ σ ⊢ (unseal α ★ ︔ id ★)
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

mutual
  ≈ⁿ-sound :
    ∀{Δ}{σ : StoreWid}{Σ Σ′ : Store}{s t : Coercion}{A B : Ty}
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
    → Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B
    → Δ ∣ Σ ⊢ s ∶ A ⊒ B × Δ ∣ Σ′ ⊢ t ∶ A ⊒ B
  ≈ⁿ-sound σ⊢ (id≈idⁿ hA atA) =
    nrw-id hA atA , nrw-id hA atA
  ≈ⁿ-sound σ⊢ (↦≈↦ⁿ s≈ t≈) with ≈-sound σ⊢ s≈ | ≈ⁿ-sound σ⊢ t≈
  ≈ⁿ-sound σ⊢ (↦≈↦ⁿ s≈ t≈) | s⊢ , s′⊢ | t⊢ , t′⊢ =
    nrw-fun s⊢ t⊢ , nrw-fun s′⊢ t′⊢
  ≈ⁿ-sound σ⊢ (∀≈∀ⁿ s≈) with ≈ⁿ-sound (StoreWid-⇑ˢ σ⊢) s≈
  ≈ⁿ-sound σ⊢ (∀≈∀ⁿ s≈) | s⊢ , t⊢ =
    nrw-all s⊢ , nrw-all t⊢
  ≈ⁿ-sound σ⊢ (ν≈νⁿ hA s≈) with ≈ⁿ-sound (StoreWid-⇑ˢ σ⊢) s≈
  ≈ⁿ-sound σ⊢ (ν≈νⁿ hA s≈) | s⊢ , t⊢ =
    nrw-gen hA s⊢ , nrw-gen hA t⊢
  ≈ⁿ-sound σ⊢ (?≈?ⁿ hG gG s≈) with ≈ⁿ-sound σ⊢ s≈
  ≈ⁿ-sound σ⊢ (?≈?ⁿ hG gG s≈) | s⊢ , t⊢ =
    nrw-untag hG gG s⊢ , nrw-untag hG gG t⊢
  ≈ⁿ-sound σ⊢ (?≈sealⁿ hα α∈σ) with StoreWid-id★∈ σ⊢ α∈σ
  ≈ⁿ-sound σ⊢ (?≈sealⁿ hα α∈σ) | α∈Σ , α∈Σ′ =
    nrw-untag hα (＇ _) (nrw-id hα (＇ _)) ,
    nrw-seal wf★ α∈Σ′ (nrw-id wf★ ★)
  ≈ⁿ-sound σ⊢ (seal≈?ⁿ hα α∈σ) with StoreWid-id★∈ σ⊢ α∈σ
  ≈ⁿ-sound σ⊢ (seal≈?ⁿ hα α∈σ) | α∈Σ , α∈Σ′ =
    nrw-seal wf★ α∈Σ (nrw-id wf★ ★) ,
    nrw-untag hα (＇ _) (nrw-id hα (＇ _))

  ≈-sound :
    ∀{Δ}{σ : StoreWid}{Σ Σ′ : Store}{s t : Coercion}{A B : Ty}
    → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
    → Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B
    → Δ ∣ Σ ⊢ s ∶ A ⊑ B × Δ ∣ Σ′ ⊢ t ∶ A ⊑ B
  ≈-sound σ⊢ (id≈id hA atA) =
    wid-id hA atA , wid-id hA atA
  ≈-sound σ⊢ (!≈! hG gG g≈) with ≈-sound σ⊢ g≈
  ≈-sound σ⊢ (!≈! hG gG g≈) | g⊢ , g′⊢ =
    wid-tag hG gG g⊢ , wid-tag hG gG g′⊢
  ≈-sound σ⊢ (!≈unseal hα α∈σ) with StoreWid-id★∈ σ⊢ α∈σ
  ≈-sound σ⊢ (!≈unseal hα α∈σ) | α∈Σ , α∈Σ′ =
    wid-tag hα (＇ _) (wid-id hα (＇ _)) ,
    wid-unseal wf★ α∈Σ′ (wid-id wf★ ★)
  ≈-sound σ⊢ (unseal≈! hα α∈σ) with StoreWid-id★∈ σ⊢ α∈σ
  ≈-sound σ⊢ (unseal≈! hα α∈σ) | α∈Σ , α∈Σ′ =
    wid-unseal wf★ α∈Σ (wid-id wf★ ★) ,
    wid-tag hα (＇ _) (wid-id hα (＇ _))
  ≈-sound σ⊢ (↦≈↦ s≈ t≈) with ≈ⁿ-sound σ⊢ s≈ | ≈-sound σ⊢ t≈
  ≈-sound σ⊢ (↦≈↦ s≈ t≈) | s⊢ , s′⊢ | t⊢ , t′⊢ =
    wid-fun s⊢ t⊢ , wid-fun s′⊢ t′⊢
  ≈-sound σ⊢ (∀≈∀ s≈) with ≈-sound (StoreWid-⇑ˢ σ⊢) s≈
  ≈-sound σ⊢ (∀≈∀ s≈) | s⊢ , t⊢ =
    wid-all s⊢ , wid-all t⊢
  ≈-sound σ⊢ (ν≈ν hB s≈)
      with ≈-sound
        (⊑ˢ-both wf★ wf★ (wid-id wf★ ★) (StoreWid-⇑ˢ σ⊢))
        s≈
  ≈-sound σ⊢ (ν≈ν hB s≈) | s⊢ , t⊢ =
    wid-inst hB s⊢ , wid-inst hB t⊢

≈-sanity : ∀{Δ}{σ : StoreWid}{Σ Σ′ : Store}{s t : Coercion}{A B : Ty}
  → Δ ⊢ σ ꞉ Σ ⊑ˢ Σ′
  → Δ ∣ σ ⊢ s ≈ t ∶ A ⊑ B
  → ∃[ A ] ∃[ B ] Δ ∣ Σ ⊢ s ∶ A ⊑ B × Δ ∣ Σ′ ⊢ t ∶ A ⊑ B
≈-sanity σ⊢ s≈ with ≈-sound σ⊢ s≈
≈-sanity σ⊢ s≈ | s⊢ , t⊢ = _ , _ , s⊢ , t⊢
