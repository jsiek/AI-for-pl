module strong.Conversion where

-- Strong System F v7 — normal-form lists of conversion heads.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (_≟_; _<?_)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; substᵗ; renameᵗ; extᵗ)
open import strong.RepresentationTypes using (Anchor; Renameᴿ; extᴿ)
open import strong.Ctx

------------------------------------------------------------------------
-- Syntax
------------------------------------------------------------------------

mutual
  data Head : Set where
    seal   : Anchor → Head
    unseal : Anchor → Head
    _↦_    : Conv → Conv → Head
    all    : Conv → Head

  data Conv : Set where
    id  : Ty → Conv
    _∷ᶜ_ : Head → Conv → Conv

infixr 7 _↦_
infixr 6 _∷ᶜ_

mutual
  renHead : Renameᵗ → Renameᴿ → Head → Head
  renHead ρ σ (seal α)   = seal (σ α)
  renHead ρ σ (unseal α) = unseal (σ α)
  renHead ρ σ (c ↦ d)    = renConv ρ σ c ↦ renConv ρ σ d
  renHead ρ σ (all c)    = all (renConv (extᵗ ρ) (extᴿ σ) c)

  renConv : Renameᵗ → Renameᴿ → Conv → Conv
  renConv ρ σ (id A)   = id (renameᵗ ρ A)
  renConv ρ σ (h ∷ᶜ c) = renHead ρ σ h ∷ᶜ renConv ρ σ c

heads : Conv → List Head
heads (id A)   = []
heads (h ∷ᶜ c) = h ∷ heads c

target : Conv → Ty
target (id A)   = A
target (h ∷ᶜ c) = target c

attach : List Head → Ty → Conv
attach []       A = id A
attach (h ∷ hs) A = h ∷ᶜ attach hs A

------------------------------------------------------------------------
-- Type-variable closing and canonical conversions
------------------------------------------------------------------------

closeEnv : ℕ → Ty → ℕ → Ty
closeEnv X S Y with X ≟ Y
closeEnv X S Y | yes _ = S
closeEnv X S Y | no _ with X <? Y
closeEnv X S Y | no _ | yes _ = ` (Y ∸ 1)
closeEnv X S Y | no _ | no  _ = ` Y

closeAt : ℕ → Ty → Ty → Ty
closeAt X S A = substᵗ (closeEnv X S) A

mutual
  revTy : ℕ → Anchor → Ty → Ty → Conv
  revTy X α S (` Y) with X ≟ Y
  revTy X α S (` Y) | yes _ = unseal α ∷ᶜ id S
  revTy X α S (` Y) | no  _ = id (closeAt X S (` Y))
  revTy X α S `ℕ      = id `ℕ
  revTy X α S `𝔹      = id `𝔹
  revTy X α S (A ⇒ B) =
    (concTy X α S A ↦ revTy X α S B) ∷ᶜ id (closeAt X S (A ⇒ B))
  revTy X α S (`∀ A)  =
    all (revTy (suc X) (suc α) (renameᵗ suc S) A)
      ∷ᶜ id (closeAt X S (`∀ A))

  concTy : ℕ → Anchor → Ty → Ty → Conv
  concTy X α S (` Y) with X ≟ Y
  concTy X α S (` Y) | yes _ = seal α ∷ᶜ id (` X)
  concTy X α S (` Y) | no  _ = id (` Y)
  concTy X α S `ℕ      = id `ℕ
  concTy X α S `𝔹      = id `𝔹
  concTy X α S (A ⇒ B) =
    (revTy X α S A ↦ concTy X α S B) ∷ᶜ id (A ⇒ B)
  concTy X α S (`∀ A)  =
    all (concTy (suc X) (suc α) (renameᵗ suc S) A) ∷ᶜ id (`∀ A)

------------------------------------------------------------------------
-- Normalizing composition
------------------------------------------------------------------------

mutual
  weightHead : Head → ℕ
  weightHead (seal α)   = 1
  weightHead (unseal α) = 1
  weightHead (c ↦ d)    = suc (weight c + weight d)
  weightHead (all c)    = suc (weight c)

  weight : Conv → ℕ
  weight (id A)   = 1
  weight (h ∷ᶜ c) = suc (weightHead h + weight c)

weightHeads : List Head → ℕ
weightHeads []       = zero
weightHeads (h ∷ hs) = weightHead h + weightHeads hs

mutual
  fuseFuel : ℕ → Head → Head → Maybe (List Head)
  fuseFuel zero h k = nothing
  fuseFuel (suc n) (seal α) (unseal β) with α ≟ β
  fuseFuel (suc n) (seal α) (unseal β) | yes _ = just []
  fuseFuel (suc n) (seal α) (unseal β) | no  _ = nothing
  fuseFuel (suc n) (unseal α) (seal β) with α ≟ β
  fuseFuel (suc n) (unseal α) (seal β) | yes _ = just []
  fuseFuel (suc n) (unseal α) (seal β) | no  _ = nothing
  fuseFuel (suc n) (s₁ ↦ t₁) (s₂ ↦ t₂) =
    just ((composeFuel n s₂ s₁ ↦ composeFuel n t₁ t₂) ∷ [])
  fuseFuel (suc n) (all s) (all t) =
    just (all (composeFuel n s t) ∷ [])
  fuseFuel (suc n) _ _ = nothing

  scanFuel : ℕ → List Head → List Head → List Head
  scanFuel zero s hs = reverse s ++ hs
  scanFuel (suc n) s [] = reverse s
  scanFuel (suc n) [] (h ∷ hs) = scanFuel n (h ∷ []) hs
  scanFuel (suc n) (h ∷ s) (k ∷ hs) with fuseFuel n h k
  scanFuel (suc n) (h ∷ s) (k ∷ hs) | nothing =
    scanFuel n (k ∷ h ∷ s) hs
  scanFuel (suc n) (h ∷ s) (k ∷ hs) | just [] = scanFuel n s hs
  scanFuel (suc n) (h ∷ s) (k ∷ hs) | just (r ∷ rs) =
    scanFuel n s (r ∷ rs ++ hs)

  composeFuel : ℕ → Conv → Conv → Conv
  composeFuel zero c d = attach (heads c ++ heads d) (target d)
  composeFuel (suc n) c d =
    attach (scanFuel n [] (heads c ++ heads d)) (target d)

fuse : Head → Head → Maybe (List Head)
fuse h k = fuseFuel (suc (2 * (weightHead h + weightHead k))) h k

contract : List Head → List Head
contract hs = scanFuel (suc (2 * weightHeads hs)) [] hs

_⨟_ : Conv → Conv → Conv
c ⨟ d = attach (contract (heads c ++ heads d)) (target d)

infixl 5 _⨟_

mutual
  instReveal : ℕ → Anchor → Ty → Conv → Conv
  instReveal X α S (id A) = revTy X α S A
  instReveal X α S (h ∷ᶜ c) =
    attach (contract (instRevealHead X α S h ∷ heads (instReveal X α S c)))
           (target (instReveal X α S c))

  instConceal : ℕ → Anchor → Ty → Conv → Conv
  instConceal X α S (id A) = concTy X α S A
  instConceal X α S (h ∷ᶜ c) =
    attach (contract (instConcealHead X α S h ∷ heads (instConceal X α S c)))
           (target (instConceal X α S c))

  instRevealHead : ℕ → Anchor → Ty → Head → Head
  instRevealHead X α S (seal β)   = seal β
  instRevealHead X α S (unseal β) = unseal β
  instRevealHead X α S (c ↦ d) =
    instConceal X α S c ↦ instReveal X α S d
  instRevealHead X α S (all c) =
    all (instReveal (suc X) (suc α) (renameᵗ suc S) c)

  instConcealHead : ℕ → Anchor → Ty → Head → Head
  instConcealHead X α S (seal β)   = seal β
  instConcealHead X α S (unseal β) = unseal β
  instConcealHead X α S (c ↦ d) =
    instReveal X α S c ↦ instConceal X α S d
  instConcealHead X α S (all c) =
    all (instConceal (suc X) (suc α) (renameᵗ suc S) c)

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    Δ₁ Δ₂ Δ₃ : Ctxᵗ
    A B C D : Ty
    R : strong.RepresentationTypes.RepTy
    X : ℕ
    α : Anchor
    c d : Conv
    h : Head

infix 4 _⊢̂_∶_⇝_⊣_
infix 4 _⊢_∶_⇝_⊣_
mutual
  data _⊢̂_∶_⇝_⊣_ : Ctxᵗ → Head → Ty → Ty → Ctxᵗ → Set where
    conv-seal : ∀ {S}
      → Δ₂ ∋n X := α → Δ₂ ∋r α := R → Δ₁ ⊢ R ⇓ S
      → Δ₁ ⊢̂ seal α ∶ S ⇝ ` X ⊣ Δ₂
    conv-unseal : ∀ {S}
      → Δ₁ ∋n X := α → Δ₁ ∋r α := R → Δ₂ ⊢ R ⇓ S
      → Δ₁ ⊢̂ unseal α ∶ ` X ⇝ S ⊣ Δ₂
    conv-fun : ∀ {s t A′ B′}
      → Δ₂ ⊢ s ∶ A′ ⇝ A ⊣ Δ₁ → Δ₁ ⊢ t ∶ B ⇝ B′ ⊣ Δ₂
      → Δ₁ ⊢̂ s ↦ t ∶ A ⇒ B ⇝ A′ ⇒ B′ ⊣ Δ₂
    conv-all : ∀ {s}
      → (name zero ∷ abst ∷ Δ₁) ⊢ s ∶ A ⇝ B
          ⊣ (name zero ∷ abst ∷ Δ₂)
      → Δ₁ ⊢̂ all s ∶ `∀ A ⇝ `∀ B ⊣ Δ₂

  data _⊢_∶_⇝_⊣_ : Ctxᵗ → Conv → Ty → Ty → Ctxᵗ → Set where
    conv-id : SameTy zero Δ₁ A Δ₂ B
      → Δ₁ ⊢ id B ∶ A ⇝ B ⊣ Δ₂
    conv-cons : Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊢ c ∶ B ⇝ C ⊣ Δ₃
      → Δ₁ ⊢ h ∷ᶜ c ∶ A ⇝ C ⊣ Δ₃

------------------------------------------------------------------------
-- Normal forms and views
------------------------------------------------------------------------

mutual
  data NFHead : Head → Set where
    nf-seal   : NFHead (seal α)
    nf-unseal : NFHead (unseal α)
    nf-fun    : NF c → NF d → NFHead (c ↦ d)
    nf-all    : NF c → NFHead (all c)

  data IrreducibleAfter (h : Head) : Conv → Set where
    irr-id   : ∀ {A} → IrreducibleAfter h (id A)
    irr-cons : ∀ {k c} → fuse h k ≡ nothing
             → IrreducibleAfter h (k ∷ᶜ c)

  data NF : Conv → Set where
    nf-id   : ∀ {A} → NF (id A)
    nf-cons : NFHead h → NF c → IrreducibleAfter h c → NF (h ∷ᶜ c)

arr : Conv → Maybe (Conv × Conv)
arr (id (A ⇒ B))             = just (id A , id B)
arr ((c ↦ d) ∷ᶜ id (A ⇒ B)) = just (c , d)
arr _                         = nothing

allView : Conv → Maybe Conv
allView (id (`∀ A))         = just (id A)
allView (all c ∷ᶜ id (`∀ A)) = just c
allView _                    = nothing

private
  nested-cancel :
    contract (unseal 0 ∷ unseal 1 ∷ seal 1 ∷ seal 0 ∷ []) ≡ []
  nested-cancel = Relation.Binary.PropositionalEquality.refl

  arrow-fuse :
    contract
      ((id `ℕ ↦ id `ℕ) ∷ (id `ℕ ↦ id `ℕ) ∷ [])
      ≡ ((id `ℕ ↦ id `ℕ) ∷ [])
  arrow-fuse = Relation.Binary.PropositionalEquality.refl

  composition-assoc :
    (((unseal 0 ∷ᶜ unseal 1 ∷ᶜ id `ℕ)
       ⨟ (seal 1 ∷ᶜ id `ℕ))
       ⨟ (seal 0 ∷ᶜ id `ℕ))
      ≡ ((unseal 0 ∷ᶜ unseal 1 ∷ᶜ id `ℕ)
         ⨟ ((seal 1 ∷ᶜ id `ℕ) ⨟ (seal 0 ∷ᶜ id `ℕ)))
  composition-assoc = Relation.Binary.PropositionalEquality.refl
