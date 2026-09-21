module strong-rep-var.TermSubst where

-- File Charter:
--   * RENAMING AND SUBSTITUTION ON TERMS.  §1 is the PAIRED type-level
--     renaming `TyRename = ren² ordinary represent` with `renᶠ²`,
--     `renᴮ²` and the specializations `renᶠ`/`renᴮ`, plus
--     `underΛ-ren`/`underReps-ren` and the arity facts
--     `numBinds-ren²`/`numBinds-ren`.  §2 is `renᴹ²` on terms, the
--     REPRESENTATION-ONLY traversal `renᴹᴿ`, their agreement
--     (`renᴹ²-ord-id`, via `renᶠ²-ord-id`/`renᴮ²-ord-id`), and the
--     derived `renᴹ`, `wkN`, `wkᴹ`, `⇑ᴹ`.  §3 is term-variable
--     renaming `extⁿ`/`renⁿ`/`shiftᵐ` with `⊢renⁿ` and `⊢weakenⁿ`; §4
--     the `⤊` transport lemmas; §5 substitution — `Img`, `crossΛᴹ`,
--     `⇑ᴵ`, `extᴵ`, `substᵐ` and `_[_∶_]ᵐ`; §6 typed images
--     `_∣_⊢ⁱ_⦂_` with `⊢imgTm`, `shiftᴵ-⊢`, `extᴵ-⊢`.
--   * WHAT IS DELIBERATELY ONE LAYER DOWN.  `extN` is strong-rep-var.Ctx §8
-- and
--     the representation-only `renᶠᴿ`/`renᴮᴿ` are strong-rep-var.Boundary
--     §2/§3, beside the syntax they act on, because the
--     representation-renaming metatheory of strong-rep-var.Boundary §3d is
--     stated over them and cannot import this module.  Reduction is
--     strong-rep-var.Reduction; the typing transport for `renᴹᴿ` and `crossΛᴹ`
--     is strong-rep-var.proof.RepWeaken (`rep-weaken-⊢`, `cross-Λ-⊢`), not
--     here — §3's `⊢renⁿ` is the TERM-variable half only.
--   * THREE LAWS A READER MUST KNOW.  (1) Boundaries are TERM-CLOSED
--     (strong-rep-var.Terms `env`), so `renⁿ` and `substᵐ` do NOT descend into
--     `_⟪_,_⟫` and `⊢renⁿ` reuses the boundary's derivation unchanged.
--     (2) A type renaming carries TWO independent maps, and the
--     ordinary one never moves a representation occurrence:
--     `TyBetaBoundary-ren-Λ` is the concrete separation check, and
--     `renᴹ²-ord-id` is the general statement that an
--     ordinary-identity `renᴹ²` IS `renᴹᴿ` (notes/DECISIONS.md,
--     2026-09-20, representation-only renaming is its own traversal).
--     (3) Beta is FRAME-EXACT: a closed value image crossing a `Λ` is
--     wrapped in that binder's DUAL with an identity conversion at the
--     argument's type (`crossΛᴹ`, used by `⇑ᴵ`), which is why
--     `_[_∶_]ᵐ` carries the `ƛ`'s own annotation instead of shifting.
--
-- Ordinary type variables and representation variables have distinct de
-- Bruijn universes. Consequently, syntax-level type renaming carries two
-- maps:
--
--   * the ordinary map renames term annotations, type arguments, conversion
--     names, and the positions carried by `lock` and `unlock`;
--   * the representation map renames boundary scope payloads and the
--     representation-variable occurrence carried by every change.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; subst)

open import strong-rep-var.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-var.Ctx
open import strong-rep-var.Conversion
open import strong-rep-var.Boundary
open import strong-rep-var.Terms

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

-- `extN` (renaming underneath n binders) and the representation-only
-- `renᶠᴿ`/`renᴮᴿ` live one layer down — `extN` in strong-rep-var.Ctx §8 and
-- the
-- two renamings in strong-rep-var.Boundary §2/§3, beside the syntax they act
-- on —
-- because the representation-renaming metatheory of strong-rep-var.Boundary
-- §3d
-- is stated over them and cannot import this module.

underΛ-ren : TyRename → TyRename
underΛ-ren (ren² ρᵗ ρʳ) = ren² (extᵗ ρᵗ) (extᵗ ρʳ)

underReps-ren : ℕ → TyRename → TyRename
underReps-ren n (ren² ρᵗ ρʳ) = ren² ρᵗ (extN n ρʳ)

renᶠ² : Renameᵗ → Renameᵗ → Change → Change
renᶠ² ρᵗ ρʳ (lock X α)   = lock (ρᵗ X) (ρʳ α)
renᶠ² ρᵗ ρʳ (unlock X α) = unlock (ρᵗ X) (ρʳ α)

renᶠ : Renameᵗ → Change → Change
renᶠ ρ = renᶠ² ρ ρ

renᴮ² : TyRename → Boundary → Boundary
renᴮ² (ren² ρᵗ ρʳ) Θ =
  boundary (map (renameᵗ ρʳ) (binds Θ))
        (map (renᶠ² ρᵗ (extN (numBinds Θ) ρʳ)) (changes Θ))

-- The one-map specialization is retained for callers where both universes
-- move in lockstep, such as weakening under an ordinary `Λ`.
renᴮ : Renameᵗ → Boundary → Boundary
renᴮ ρ = renᴮ² (ren² ρ ρ)

numBinds-ren² : (ρ : TyRename) (Θ : Boundary)
  → numBinds (renᴮ² ρ Θ) ≡ numBinds Θ
numBinds-ren² ρ Θ = map-length (binds Θ)
  where
  map-length : ∀ {A B : Set} (xs : List A) {f : A → B}
    → length (map f xs) ≡ length xs
  map-length []       = refl
  map-length (_ ∷ xs) = cong suc (map-length xs)

numBinds-ren : (ρ : Renameᵗ) (Θ : Boundary)
  → numBinds (renᴮ ρ Θ) ≡ numBinds Θ
numBinds-ren ρ Θ = numBinds-ren² (ren² ρ ρ) Θ

-- Concrete separation check. Weakening TyBeta under `Λ` moves its ordinary
-- insertion point from 0 to 1, but its representation occurrence stays 0
-- because that occurrence is bound by TyBeta's own `bindR`.
TyBetaBoundary-ren-Λ : renᴮ² (ren² suc suc) TyBetaBoundary
  ≡ boundary (`ℕ ∷ []) (unlock 1 0 ∷ [])
TyBetaBoundary-ren-Λ = refl

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

renᴹᴿ : Renameᵗ → Term → Term
renᴹᴿ ρ (` x)          = ` x
renᴹᴿ ρ ($ n)          = $ n
renᴹᴿ ρ `true           = `true
renᴹᴿ ρ `false          = `false
renᴹᴿ ρ (ƛ A ∙ N)      = ƛ A ∙ renᴹᴿ ρ N
renᴹᴿ ρ (L · M)        = renᴹᴿ ρ L · renᴹᴿ ρ M
renᴹᴿ ρ (Λ N)          = Λ (renᴹᴿ (extᵗ ρ) N)
renᴹᴿ ρ (L ·[ B , A ]) = renᴹᴿ ρ L ·[ B , A ]
renᴹᴿ ρ (M ⟪ Θ , c ⟫) =
  renᴹᴿ (extN (numBinds Θ) ρ) M ⟪ renᴮᴿ ρ Θ , c ⟫

extᵗ-pointwise-id : ∀ {ρ} → (∀ X → ρ X ≡ X)
  → ∀ X → extᵗ ρ X ≡ X
extᵗ-pointwise-id h zero    = refl
extᵗ-pointwise-id h (suc X) = cong suc (h X)

renameᵗ-pointwise-id : ∀ {ρ} → (∀ X → ρ X ≡ X)
  → ∀ A → renameᵗ ρ A ≡ A
renameᵗ-pointwise-id h (` X) = cong `_ (h X)
renameᵗ-pointwise-id h `ℕ = refl
renameᵗ-pointwise-id h `𝔹 = refl
renameᵗ-pointwise-id h (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-pointwise-id h A) (renameᵗ-pointwise-id h B)
renameᵗ-pointwise-id h (`∀ A) =
  cong `∀ (renameᵗ-pointwise-id (extᵗ-pointwise-id h) A)

renᶜ-pointwise-id : ∀ {ρ} → (∀ X → ρ X ≡ X)
  → ∀ c → renᶜ ρ c ≡ c
renᶜ-pointwise-id h (id A) = cong id (renameᵗ-pointwise-id h A)
renᶜ-pointwise-id h (seal X) = cong seal (h X)
renᶜ-pointwise-id h (unseal X) = cong unseal (h X)
renᶜ-pointwise-id h (s ↦ t) =
  cong₂ _↦_ (renᶜ-pointwise-id h s) (renᶜ-pointwise-id h t)
renᶜ-pointwise-id h (`∀ s) =
  cong `∀ (renᶜ-pointwise-id (extᵗ-pointwise-id h) s)

renᶠ²-ord-id : ∀ {ρᵗ ρʳ} → (∀ X → ρᵗ X ≡ X)
  → ∀ δ → renᶠ² ρᵗ ρʳ δ ≡ renᶠᴿ ρʳ δ
renᶠ²-ord-id {ρʳ = ρʳ} h (lock X α) =
  cong (λ X′ → lock X′ (ρʳ α)) (h X)
renᶠ²-ord-id {ρʳ = ρʳ} h (unlock X α) =
  cong (λ X′ → unlock X′ (ρʳ α)) (h X)

renᴮ²-ord-id : ∀ {ρᵗ ρʳ} → (∀ X → ρᵗ X ≡ X)
  → ∀ Θ → renᴮ² (ren² ρᵗ ρʳ) Θ ≡ renᴮᴿ ρʳ Θ
renᴮ²-ord-id {ρᵗ} {ρʳ} h (boundary Rs χ) =
  cong (boundary (map (renameᵗ ρʳ) Rs)) (changes-id χ)
  where
  changes-id : ∀ χ
    → map (renᶠ² ρᵗ (extN (length Rs) ρʳ)) χ
        ≡ map (renᶠᴿ (extN (length Rs) ρʳ)) χ
  changes-id [] = refl
  changes-id (δ ∷ χ) =
    cong₂ _∷_ (renᶠ²-ord-id h δ) (changes-id χ)

renᴹ²-ord-id : ∀ {ρᵗ ρʳ} → (∀ X → ρᵗ X ≡ X) → ∀ M
  → renᴹ² (ren² ρᵗ ρʳ) M ≡ renᴹᴿ ρʳ M
renᴹ²-ord-id h (` x) = refl
renᴹ²-ord-id h ($ n) = refl
renᴹ²-ord-id h `true = refl
renᴹ²-ord-id h `false = refl
renᴹ²-ord-id h (ƛ A ∙ N) =
  cong₂ ƛ_∙_ (renameᵗ-pointwise-id h A) (renᴹ²-ord-id h N)
renᴹ²-ord-id h (L · M) =
  cong₂ _·_ (renᴹ²-ord-id h L) (renᴹ²-ord-id h M)
renᴹ²-ord-id h (Λ N) =
  cong Λ_ (renᴹ²-ord-id (extᵗ-pointwise-id h) N)
renᴹ²-ord-id {ρᵗ} {ρʳ} h (L ·[ B , A ]) =
  trans
    (cong₂ (λ L′ B′ → L′ ·[ B′ , renameᵗ ρᵗ A ])
           (renᴹ²-ord-id h L)
           (renameᵗ-pointwise-id (extᵗ-pointwise-id h) B))
    (cong (λ A′ → renᴹᴿ ρʳ L ·[ B , A′ ])
          (renameᵗ-pointwise-id h A))
renᴹ²-ord-id {ρᵗ} {ρʳ} h (M ⟪ Θ , c ⟫) =
  trans
    (cong (λ M′ →
             M′ ⟪ renᴮ² (ren² ρᵗ ρʳ) Θ , renᶜ ρᵗ c ⟫)
          (renᴹ²-ord-id h M))
    (trans
      (cong (λ Θ′ → renᴹᴿ (extN (numBinds Θ) ρʳ) M
                         ⟪ Θ′ , renᶜ ρᵗ c ⟫)
            (renᴮ²-ord-id h Θ))
      (cong (λ c′ → renᴹᴿ (extN (numBinds Θ) ρʳ) M
                         ⟪ renᴮᴿ ρʳ Θ , c′ ⟫)
            (renᶜ-pointwise-id h c)))

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

extⁿ : (Var → Var) → Var → Var
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renⁿ : (Var → Var) → Term → Term
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

∋-extⁿ : ∀ {Γ Γ′ A x B} {ρ : Var → Var}
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

⤊-∋ⁿ : ∀ {ρ : Var → Var} {Γ Γ′}
  → (∀ {x A} → Γ ∋ x ⦂ A → Γ′ ∋ ρ x ⦂ A)
  → (∀ {x A} → ⤊ Γ ∋ x ⦂ A → ⤊ Γ′ ∋ ρ x ⦂ A)
⤊-∋ⁿ h d with ∋-map⁻ d
⤊-∋ⁿ h d | A , refl , q = ∋-⤊ (h q)

⊢renⁿ : ∀ {Δ Γ Γ′ M A} {ρ : Var → Var}
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

renⁿ-id : (ρ : Var → Var) → (∀ x → ρ x ≡ x)
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
  ivar : Var → Img
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
    ⟪ boundary [] (lock 0 0 ∷ []) , mkId (⇑ᵗ A) ⟫

-- Variables cross a type binder unchanged. Closed value images acquire the
-- frame-exact wrapper above, and their ordinary type spelling is weakened.
⇑ᴵ : Img → Img
⇑ᴵ (ivar x)   = ivar x
⇑ᴵ (ival W A) = ival (crossΛᴹ W A) (⇑ᵗ A)

extᴵ : (Var → Img) → Var → Img
extᴵ σ zero    = ivar zero
extᴵ σ (suc x) = shiftᴵ (σ x)

substᵐ : (Var → Img) → Term → Term
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

extᴵ-⊢ : ∀ {σ : Var → Img} {Δ Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ B)
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B
        → Δ ∣ (A ∷ Γ′) ⊢ⁱ extᴵ σ x ⦂ B)
extᴵ-⊢ h here      = ⊢ivar here
extᴵ-⊢ h (there d) = shiftᴵ-⊢ (h d)
