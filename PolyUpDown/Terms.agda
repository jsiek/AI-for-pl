module Terms where

-- File Charter:
--   * Intrinsically typed term syntax for PolyUpDown.
--   * Core term constructors and structural actions on terms
--     (type-variable renaming/substitution and seal renaming).
--   * Terms cast through `_at[_]_`, carrying direction (`up`/`down`),
--     explicit permission sets, and the corresponding widening/narrowing
--     witnesses directly.
-- Note to self:
--   * Keep reduction and metatheory in separate modules; this file should stay
--     focused on syntax and structural actions on syntax.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Subset using (_∈_; _∉_)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; here; there)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import Types
open import TypeProperties
open import Ctx
  using
    ( renameLookup
    ; substLookup
    ; map-substᵗ-⤊ᵗ
    ; map-substᵗ-⤊ˢ
    ; map-renameᵗ-⤊ᵗ
    ; map-renameᵗ-⤊ˢ
    ; map-renameˢ-⤊ᵗ
    ; map-renameˢ-⤊ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-ctx )
open import Store
  using
    ( substStoreᵗ
    ; renameStoreᵗ-ext-⟰ᵗ
    ; substStoreᵗ-ext-⟰ᵗ
    ; renameStoreˢ-ext-⟰ᵗ
    ; renameStoreᵗ-cons-⟰ˢ
    ; substStoreᵗ-cons-⟰ˢ
    ; renameStoreˢ-cons-⟰ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-store
    ; substLookupᵗ to substLookupᵗ-store
    )
open import UpDown

------------------------------------------------------------------------
-- Constants, primitive operators, and permission environments
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : ∀{Δ}{Ψ} → Const → Ty Δ Ψ
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : ∀{Δ}{Ψ} → Prim → Ty Δ Ψ
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

every : (Ψ : SealCtx) → Vec Bool Ψ
every zero = []
every (suc Ψ) = true ∷ every Ψ

none : (Ψ : SealCtx) → Vec Bool Ψ
none zero = []
none (suc Ψ) = false ∷ none Ψ

every-member : ∀{Ψ} (α : Seal Ψ) → ⌊ α ⌋ ∈ every Ψ
every-member Zˢ = here
every-member (Sˢ α) = there (every-member α)

none-excluded : ∀{Ψ} (α : Seal Ψ) → ⌊ α ⌋ ∉ none Ψ
none-excluded Zˢ ()
none-excluded (Sˢ α) (there p) = none-excluded α p

RenOk-every :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenOk ρ (every Ψ) (every Ψ′)
RenOk-every ρ {α} _ = every-member (ρ α)

RenOk-none :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenOk ρ (none Ψ) (none Ψ′)
RenOk-none ρ {α} p = ⊥-elim (none-excluded α p)

RenOk-any-every :
  ∀{Ψ}{Ψ′}{P : Vec Bool Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  RenOk ρ P (every Ψ′)
RenOk-any-every ρ {α} _ = every-member (ρ α)

------------------------------------------------------------------------
-- Intrinsic terms
------------------------------------------------------------------------

⤊ᵗ : ∀{Δ}{Ψ} → Ctx Δ Ψ → Ctx (suc Δ) Ψ
⤊ᵗ Γ = map (renameᵗ Sᵗ) Γ

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _•_[_]
infix  5 ν:=_∙_
infixl 6 _⊕[_]_
infix  8 _at[_]_
infix  9 `_
infix  4 _∣_∣_∣_⊢_

data Direction : Set where
  up down : Direction

Cast :
  ∀{Δ}{Ψ} →
  Direction →
  Store Δ Ψ →
  Vec Bool Ψ →
  Vec Bool Ψ →
  Ty Δ Ψ →
  Ty Δ Ψ →
  Set
Cast up Σ Φ Ξ A B = Σ ∣ Φ ∣ Ξ ⊢ A ⊑ B
Cast down Σ Φ Ξ A B = Σ ∣ Φ ∣ Ξ ⊢ A ⊒ B

data _∣_∣_∣_⊢_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Δ Ψ) (Γ : Ctx Δ Ψ) : Ty Δ Ψ → Set where
  `_        : ∀{A : Ty Δ Ψ}{x : Var} →
              Γ ∋ x ⦂ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

  ƛ_⇒_      : ∀{B : Ty Δ Ψ} →
              (A : Ty Δ Ψ) →
              Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B)

  _·_       : ∀{A B : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (A ⇒ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  Λ_        : ∀{A : Ty (suc Δ) Ψ} →
              (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A)

  _•_[_]    : ∀{A : Ty (suc Δ) Ψ}{B}{C : Ty Δ Ψ} →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (`∀ A) →
              (α : Seal Ψ) →
              Σ ∋ˢ α ⦂ C →
              B ≡ (A [ ｀ α ]ᵗ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  ν:=_∙_    : ∀{B : Ty Δ Ψ} →
              (A : Ty Δ Ψ) →
              Δ ∣ (suc Ψ) ∣ ((Zˢ , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ B) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ B

  $         : ∀ {A}
              (κ : Const) →
              constTy κ ≡ A →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

  _⊕[_]_    :
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              (op : Prim) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ) →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (‵ `ℕ)

  at        : ∀{A B : Ty Δ Ψ}{Φ Ξ : Vec Bool Ψ} →
              {C D : Ty Δ Ψ} →
              (M : Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ C) →
              (d : Direction) →
              (p : Cast d Σ Φ Ξ A B) →
              C ≡ A →
              D ≡ B →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ D

  blame     : ∀{A : Ty Δ Ψ} →
              Label →
              Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A

pattern _at[_]_ M d p = at M d p refl refl

------------------------------------------------------------------------
-- Structural actions on terms
------------------------------------------------------------------------

cast⊢ :
  ∀{Δ}{Ψ}{Σ Σ′ : Store Δ Ψ}{Γ Γ′ : Ctx Δ Ψ}{A A′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Γ ≡ Γ′ →
  A ≡ A′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ′ ⊢ A′
cast⊢ refl refl refl M = M

renameᵗ-constTy :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (κ : Const) →
  renameᵗ ρ (constTy {Δ}{Ψ} κ) ≡ constTy κ
renameᵗ-constTy ρ (κℕ n) = refl

substᵗ-constTy :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (κ : Const) →
  substᵗ σ (constTy {Δ}{Ψ} κ) ≡ constTy κ
substᵗ-constTy σ (κℕ n) = refl

renameˢ-constTy :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (κ : Const) →
  renameˢ ρ (constTy {Δ}{Ψ} κ) ≡ constTy κ
renameˢ-constTy ρ (κℕ n) = refl

renameCastᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B}
  (d : Direction) (ρ : Renameᵗ Δ Δ′) →
  Cast d Σ Φ Ξ A B →
  Cast d (renameStoreᵗ ρ Σ) Φ Ξ (renameᵗ ρ A) (renameᵗ ρ B)
renameCastᵗ up ρ p = ⊑-renameᵗ ρ p
renameCastᵗ down ρ p = ⊒-renameᵗ ρ p

substCastᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B}
  (d : Direction) (σ : Substᵗ Δ Δ′ Ψ) →
  Cast d Σ Φ Ξ A B →
  Cast d (substStoreᵗ σ Σ) Φ Ξ (substᵗ σ A) (substᵗ σ B)
substCastᵗ up σ p = ⊑-substᵗ σ p
substCastᵗ down σ p = ⊒-substᵗ σ p

renameCastˢ :
  ∀{Δ}{Ψ}{Ψ′}{Σ : Store Δ Ψ}{Φ Ξ : Vec Bool Ψ}{A B}
  (d : Direction) (ρ : Renameˢ Ψ Ψ′) →
  Cast d Σ Φ Ξ A B →
  Cast d (renameStoreˢ ρ Σ) (every Ψ′) (every Ψ′) (renameˢ ρ A) (renameˢ ρ B)
renameCastˢ up ρ p = ⊑-renameˢ ρ (RenOk-any-every ρ) (RenOk-any-every ρ) p
renameCastˢ down ρ p = ⊒-renameˢ ρ (RenOk-any-every ρ) (RenOk-any-every ρ) p

renameᵗ-term :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameᵗ Δ Δ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ′ ∣ Ψ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ ⊢ renameᵗ ρ A
renameᵗ-term ρ (` h) = ` (renameLookupᵗ-ctx ρ h)
renameᵗ-term ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗ-term ρ M
renameᵗ-term ρ (L · M) = renameᵗ-term ρ L · renameᵗ-term ρ M
renameᵗ-term {Σ = Σ} {Γ = Γ} ρ (Λ_ {A = A} M) =
  Λ (cast⊢
       (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
       (map-renameᵗ-⤊ᵗ ρ Γ)
       refl
       (renameᵗ-term (extᵗ ρ) M))
renameᵗ-term ρ (_•_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameᵗ-[]ᵗ-seal ρ A α))
      (cong (renameᵗ ρ) (sym eq)))
    ((renameᵗ-term ρ M • α [ renameLookupᵗ-store ρ h ]) refl)
renameᵗ-term {Σ = Σ} {Γ = Γ} ρ (ν:=_∙_ {B = B} A M) =
  ν:= renameᵗ ρ A ∙
    cast⊢
      (renameStoreᵗ-cons-⟰ˢ ρ A Σ)
      (map-renameᵗ-⤊ˢ ρ Γ)
      (renameᵗ-⇑ˢ ρ B)
      (renameᵗ-term ρ M)
renameᵗ-term ρ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameᵗ-constTy ρ κ))
      (cong (renameᵗ ρ) eq))
    ($ κ refl)
renameᵗ-term ρ (L ⊕[ op ] M) = renameᵗ-term ρ L ⊕[ op ] renameᵗ-term ρ M
renameᵗ-term ρ (M at[ d ] p) = renameᵗ-term ρ M at[ d ] renameCastᵗ d ρ p
renameᵗ-term ρ (blame ℓ) = blame ℓ

substᵗ-term :
  ∀ {Δ}{Δ′}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (σ : Substᵗ Δ Δ′ Ψ) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ∣ map (substᵗ σ) Γ ⊢ substᵗ σ A
substᵗ-term σ (` h) = ` (substLookup σ h)
substᵗ-term σ (ƛ A ⇒ M) = ƛ substᵗ σ A ⇒ substᵗ-term σ M
substᵗ-term σ (L · M) = substᵗ-term σ L · substᵗ-term σ M
substᵗ-term {Σ = Σ} {Γ = Γ} σ (Λ_ {A = A} M) =
  Λ (cast⊢
       (substStoreᵗ-ext-⟰ᵗ σ Σ)
       (map-substᵗ-⤊ᵗ σ Γ)
       refl
       (substᵗ-term (extsᵗ σ) M))
substᵗ-term σ (_•_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (substᵗ-[]ᵗ-seal σ A α))
      (cong (substᵗ σ) (sym eq)))
    ((substᵗ-term σ M • α [ substLookupᵗ-store σ h ]) refl)
substᵗ-term {Σ = Σ} {Γ = Γ} σ (ν:=_∙_ {B = B} A M) =
  ν:= substᵗ σ A ∙
    cast⊢
      (substStoreᵗ-cons-⟰ˢ σ A Σ)
      (map-substᵗ-⤊ˢ σ Γ)
      (substᵗ-⇑ˢ σ B)
      (substᵗ-term (liftSubstˢ σ) M)
substᵗ-term σ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (substᵗ-constTy σ κ))
      (cong (substᵗ σ) eq))
    ($ κ refl)
substᵗ-term σ (L ⊕[ op ] M) = substᵗ-term σ L ⊕[ op ] substᵗ-term σ M
substᵗ-term σ (M at[ d ] p) = substᵗ-term σ M at[ d ] substCastᵗ d σ p
substᵗ-term σ (blame ℓ) = blame ℓ

renameˢ-term :
  ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  (ρ : Renameˢ Ψ Ψ′) →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ∣ map (renameˢ ρ) Γ ⊢ renameˢ ρ A
renameˢ-term ρ (` h) = ` (renameLookup ρ h)
renameˢ-term ρ (ƛ A ⇒ M) = ƛ renameˢ ρ A ⇒ renameˢ-term ρ M
renameˢ-term ρ (L · M) = renameˢ-term ρ L · renameˢ-term ρ M
renameˢ-term {Σ = Σ} {Γ = Γ} ρ (Λ_ {A = A} M) =
  Λ (cast⊢
       (renameStoreˢ-ext-⟰ᵗ ρ Σ)
       (map-renameˢ-⤊ᵗ ρ Γ)
       refl
       (renameˢ-term ρ M))
renameˢ-term ρ (_•_[_] {A = A} {B = B} M α h eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameˢ-[]ᵗ-seal ρ A α))
      (cong (renameˢ ρ) (sym eq)))
    ((renameˢ-term ρ M • (ρ α) [ renameLookupˢ ρ h ]) refl)
renameˢ-term {Σ = Σ} {Γ = Γ} ρ (ν:=_∙_ {B = B} A M) =
  ν:= renameˢ ρ A ∙
    cast⊢
      (renameStoreˢ-cons-⟰ˢ ρ A Σ)
      (map-renameˢ-⤊ˢ ρ Γ)
      (renameˢ-ext-⇑ˢ ρ B)
      (renameˢ-term (extˢ ρ) M)
renameˢ-term ρ ($ κ eq) =
  cast⊢
    refl
    refl
    (trans
      (sym (renameˢ-constTy ρ κ))
      (cong (renameˢ ρ) eq))
    ($ κ refl)
renameˢ-term ρ (L ⊕[ op ] M) = renameˢ-term ρ L ⊕[ op ] renameˢ-term ρ M
renameˢ-term ρ (M at[ d ] p) = renameˢ-term ρ M at[ d ] renameCastˢ d ρ p
renameˢ-term ρ (blame ℓ) = blame ℓ

infix 8 ⇑ˢᵐ_
⇑ˢᵐ_ :
  ∀ {Δ}{Ψ}{Σ : Store Δ Ψ}{Γ : Ctx Δ Ψ}{A : Ty Δ Ψ} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ A →
  Δ ∣ (suc Ψ) ∣ (⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ (⇑ˢ A)
⇑ˢᵐ M = renameˢ-term Sˢ M
