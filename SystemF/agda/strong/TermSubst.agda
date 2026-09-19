module strong.TermSubst where

-- Strong System F -- renaming and term substitution.
--
-- Ordinary type variables and representation variables have distinct de
-- Bruijn universes. Consequently, syntax-level type renaming carries two
-- maps:
--
--   * the ordinary map renames term annotations, type arguments, conversion
--     names, and the positions carried by `lock` and `unlock`;
--   * the representation map renames morphism payloads and the
--     representation-variable occurrence carried by every change.
--
-- The term-variable operations remain ordinary. Boundaries are term-closed,
-- so term renaming and substitution do not descend into a wrapper.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; subst)

open import strong.Types
  using (Ty; `ℕ; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms

------------------------------------------------------------------------
-- 1. Paired type-level renaming
------------------------------------------------------------------------

record TyRename : Set where
  constructor ren²
  field
    ordinary : Renameᵗ
    represent : Renameᵗ
open TyRename public

idᵗ : Renameᵗ
idᵗ X = X

id² : TyRename
id² = ren² idᵗ idᵗ

extN : ℕ → Renameᵗ → Renameᵗ
extN zero    ρ = ρ
extN (suc n) ρ = extᵗ (extN n ρ)

underΛ-ren : TyRename → TyRename
underΛ-ren (ren² ρᵗ ρʳ) = ren² (extᵗ ρᵗ) (extᵗ ρʳ)

underReps-ren : ℕ → TyRename → TyRename
underReps-ren n (ren² ρᵗ ρʳ) = ren² ρᵗ (extN n ρʳ)

renᶠ² : Renameᵗ → Renameᵗ → Change → Change
renᶠ² ρᵗ ρʳ (lock X α)   = lock (ρᵗ X) (ρʳ α)
renᶠ² ρᵗ ρʳ (unlock X α) = unlock (ρᵗ X) (ρʳ α)

renᶠ : Renameᵗ → Change → Change
renᶠ ρ = renᶠ² ρ ρ

renᴮ² : TyRename → CtxMorph → CtxMorph
renᴮ² (ren² ρᵗ ρʳ) Θ =
  morph (map (renameᵗ ρʳ) (binds Θ))
        (map (renᶠ² ρᵗ (extN (numBinds Θ) ρʳ)) (changes Θ))

-- The one-map specialization is retained for callers where both universes
-- move in lockstep, such as weakening under an ordinary `Λ`.
renᴮ : Renameᵗ → CtxMorph → CtxMorph
renᴮ ρ = renᴮ² (ren² ρ ρ)

numBinds-ren² : (ρ : TyRename) (Θ : CtxMorph)
  → numBinds (renᴮ² ρ Θ) ≡ numBinds Θ
numBinds-ren² ρ Θ = map-length (binds Θ)
  where
  map-length : ∀ {A B : Set} (xs : List A) {f : A → B}
    → length (map f xs) ≡ length xs
  map-length []       = refl
  map-length (_ ∷ xs) = cong suc (map-length xs)

numBinds-ren : (ρ : Renameᵗ) (Θ : CtxMorph)
  → numBinds (renᴮ ρ Θ) ≡ numBinds Θ
numBinds-ren ρ Θ = numBinds-ren² (ren² ρ ρ) Θ

-- Concrete separation check. Weakening TyBeta under `Λ` moves its ordinary
-- insertion point from 0 to 1, but its representation occurrence stays 0
-- because that occurrence is bound by TyBeta's own `bindR`.
TyBetaMorph-ren-Λ : renᴮ² (ren² suc suc) TyBetaMorph
  ≡ morph (`ℕ ∷ []) (unlock 1 0 ∷ [])
TyBetaMorph-ren-Λ = refl

------------------------------------------------------------------------
-- 2. Renaming terms
------------------------------------------------------------------------

renᴹ² : TyRename → Term → Term
renᴹ² ρ (` x)          = ` x
renᴹ² ρ ($ n)          = $ n
renᴹ² ρ `true           = `true
renᴹ² ρ `false          = `false
renᴹ² ρ (ƛ A ∙ N)      = ƛ renameᵗ (ordinary ρ) A ∙ renᴹ² ρ N
renᴹ² ρ (L · M)        = renᴹ² ρ L · renᴹ² ρ M
renᴹ² ρ (Λ N)          = Λ (renᴹ² (underΛ-ren ρ) N)
renᴹ² ρ (L ·[ B , A ]) =
  renᴹ² ρ L ·[ renameᵗ (extᵗ (ordinary ρ)) B
             , renameᵗ (ordinary ρ) A ]
renᴹ² ρ (M ⟪ Θ , c ⟫) =
  renᴹ² (underReps-ren (numBinds Θ) ρ) M
    ⟪ renᴮ² ρ Θ , renᶜ (ordinary ρ) c ⟫

renᴹ : Renameᵗ → Term → Term
renᴹ ρ = renᴹ² (ren² ρ ρ)

wkN : ℕ → Renameᵗ
wkN zero    X = X
wkN (suc n) X = suc (wkN n X)

wkᴹ : ℕ → Term → Term
wkᴹ n = renᴹ (wkN n)

-- Crossing a term-level type binder weakens both free universes. The newly
-- bound ordinary variable names the newly bound abstract representation.
⇑ᴹ : Term → Term
⇑ᴹ = renᴹ² (ren² suc suc)

------------------------------------------------------------------------
-- 3. Term-variable renaming
------------------------------------------------------------------------

extⁿ : (ℕ → ℕ) → ℕ → ℕ
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renⁿ : (ℕ → ℕ) → Term → Term
renⁿ ρ (` x)          = ` (ρ x)
renⁿ ρ ($ n)          = $ n
renⁿ ρ `true           = `true
renⁿ ρ `false          = `false
renⁿ ρ (ƛ A ∙ N)      = ƛ A ∙ renⁿ (extⁿ ρ) N
renⁿ ρ (L · M)        = renⁿ ρ L · renⁿ ρ M
renⁿ ρ (Λ N)          = Λ (renⁿ ρ N)
renⁿ ρ (L ·[ B , A ]) = renⁿ ρ L ·[ B , A ]
renⁿ ρ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

shiftᵐ : Term → Term
shiftᵐ = renⁿ suc

∋-extⁿ : ∀ {Γ Γ′ A x B} {ρ : ℕ → ℕ}
  → (∀ {y C} → Γ ∋ y ⦂ C → Γ′ ∋ ρ y ⦂ C)
  → (A ∷ Γ) ∋ x ⦂ B
  → (A ∷ Γ′) ∋ extⁿ ρ x ⦂ B
∋-extⁿ h here      = here
∋-extⁿ h (there d) = there (h d)

------------------------------------------------------------------------
-- 4. Type-binder transport of term contexts
------------------------------------------------------------------------

∋-map⁻ : ∀ {f : Ty → Ty} {Γ x A′}
  → map f Γ ∋ x ⦂ A′
  → ∃[ A ] ((A′ ≡ f A) × (Γ ∋ x ⦂ A))
∋-map⁻ {Γ = []} ()
∋-map⁻ {Γ = A ∷ Γ} here = A , refl , here
∋-map⁻ {Γ = A ∷ Γ} (there d) with ∋-map⁻ d
∋-map⁻ {Γ = A ∷ Γ} (there d) | B , eq , q = B , eq , there q

∋-⤊ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⤊ Γ ∋ x ⦂ ⇑ᵗ A
∋-⤊ here      = here
∋-⤊ (there d) = there (∋-⤊ d)

⤊-∋ⁿ : ∀ {ρ : ℕ → ℕ} {Γ Γ′}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → (∀ {x A} → ⤊ Γ ∋ x ⦂ A → ⤊ Γ′ ∋ ρ x ⦂ A)
⤊-∋ⁿ h d with ∋-map⁻ d
⤊-∋ⁿ h d | A , refl , q = ∋-⤊ (h q)

⊢renⁿ : ∀ {Δ Γ Γ′ M A} {ρ : ℕ → ℕ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ∣ Γ′ ⊢ renⁿ ρ M ⦂ A
⊢renⁿ h (⊢` d) = ⊢` (h d)
⊢renⁿ h ⊢$ = ⊢$
⊢renⁿ h ⊢true = ⊢true
⊢renⁿ h ⊢false = ⊢false
⊢renⁿ h (⊢ƛ w ⊢N) = ⊢ƛ w (⊢renⁿ (∋-extⁿ h) ⊢N)
⊢renⁿ h (⊢· ⊢L ⊢M) = ⊢· (⊢renⁿ h ⊢L) (⊢renⁿ h ⊢M)
⊢renⁿ h (⊢Λ ⊢N) = ⊢Λ (⊢renⁿ (⤊-∋ⁿ h) ⊢N)
⊢renⁿ h (⊢·[] ⊢L w) = ⊢·[] (⊢renⁿ h ⊢L) w
⊢renⁿ h (env mwᵥ ⊢M ⊢c sameᵢ sameₑ wE) =
  env mwᵥ ⊢M ⊢c sameᵢ sameₑ wE

renⁿ-id : (ρ : ℕ → ℕ) → (∀ x → ρ x ≡ x)
  → (M : Term) → renⁿ ρ M ≡ M
renⁿ-id ρ h (` x) = cong `_ (h x)
renⁿ-id ρ h ($ n) = refl
renⁿ-id ρ h `true = refl
renⁿ-id ρ h `false = refl
renⁿ-id ρ h (ƛ A ∙ N) = cong (ƛ A ∙_) (renⁿ-id (extⁿ ρ) ext-id N)
  where
  ext-id : ∀ x → extⁿ ρ x ≡ x
  ext-id zero    = refl
  ext-id (suc x) = cong suc (h x)
renⁿ-id ρ h (L · M) = cong₂ _·_ (renⁿ-id ρ h L) (renⁿ-id ρ h M)
renⁿ-id ρ h (Λ N) = cong Λ_ (renⁿ-id ρ h N)
renⁿ-id ρ h (L ·[ B , A ]) =
  cong (λ L′ → L′ ·[ B , A ]) (renⁿ-id ρ h L)
renⁿ-id ρ h (M ⟪ Θ , c ⟫) = refl

⊢weakenⁿ : ∀ {Δ Γ M A}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ∣ Γ ⊢ M ⦂ A
⊢weakenⁿ {Γ = Γ} {M = M} {A = A} ⊢M =
  subst (λ N → _ ∣ Γ ⊢ N ⦂ A)
        (renⁿ-id idᵗ (λ x → refl) M)
        (⊢renⁿ (λ ()) ⊢M)

------------------------------------------------------------------------
-- 5. Term substitution
------------------------------------------------------------------------

data Img : Set where
  ivar : ℕ → Img
  ival : Term → Ty → Img

imgTm : Img → Term
imgTm (ivar x)   = ` x
imgTm (ival W A) = W

shiftᴵ : Img → Img
shiftᴵ (ivar x)   = ivar (suc x)
shiftᴵ (ival W A) = ival W A

-- A value crossing `Λ` is weakened only in the free representation
-- universe and wrapped in the binder's dual. The lock removes the fresh
-- ordinary variable, so the surviving ordinary indices retain their old
-- positions; representation occurrences move past the new abstract binder.
crossΛᴹ : Term → Ty → Term
crossΛᴹ W A =
  renᴹ² (ren² idᵗ suc) W
    ⟪ morph [] (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫

-- Variables cross a type binder unchanged. Closed value images acquire the
-- frame-exact wrapper above, and their ordinary type spelling is weakened.
⇑ᴵ : Img → Img
⇑ᴵ (ivar x)   = ivar x
⇑ᴵ (ival W A) = ival (crossΛᴹ W A) (⇑ᵗ A)

extᴵ : (ℕ → Img) → ℕ → Img
extᴵ σ zero    = ivar zero
extᴵ σ (suc x) = shiftᴵ (σ x)

substᵐ : (ℕ → Img) → Term → Term
substᵐ σ (` x)          = imgTm (σ x)
substᵐ σ ($ n)          = $ n
substᵐ σ `true           = `true
substᵐ σ `false          = `false
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᴵ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ (λ x → ⇑ᴵ (σ x)) N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

infix 8 _[_∶_]ᵐ
_[_∶_]ᵐ : Term → Term → Ty → Term
N [ W ∶ A ]ᵐ =
  substᵐ (λ { zero → ival W A ; (suc x) → ivar x }) N

------------------------------------------------------------------------
-- 6. Typed images away from type-context transport
------------------------------------------------------------------------

infix 3 _∣_⊢ⁱ_⦂_
data _∣_⊢ⁱ_⦂_ : Ctxᵗ → Ctx → Img → Ty → Set where
  ⊢ivar : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ⁱ ivar x ⦂ A
  ⊢ival : ∀ {Δ Γ W A} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A
    → Δ ∣ Γ ⊢ⁱ ival W A ⦂ A

⊢imgTm : ∀ {Δ Γ i A}
  → Δ ∣ Γ ⊢ⁱ i ⦂ A
  → Δ ∣ Γ ⊢ imgTm i ⦂ A
⊢imgTm (⊢ivar d) = ⊢` d
⊢imgTm (⊢ival w ⊢W) = ⊢weakenⁿ ⊢W

shiftᴵ-⊢ : ∀ {Δ Γ i A B}
  → Δ ∣ Γ ⊢ⁱ i ⦂ B
  → Δ ∣ A ∷ Γ ⊢ⁱ shiftᴵ i ⦂ B
shiftᴵ-⊢ (⊢ivar d) = ⊢ivar (there d)
shiftᴵ-⊢ (⊢ival w ⊢W) = ⊢ival w ⊢W

extᴵ-⊢ : ∀ {σ : ℕ → Img} {Δ Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ B)
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B
        → Δ ∣ (A ∷ Γ′) ⊢ⁱ extᴵ σ x ⦂ B)
extᴵ-⊢ h here      = ⊢ivar here
extᴵ-⊢ h (there d) = shiftᴵ-⊢ (h d)
