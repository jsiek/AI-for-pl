module Denot.Denotation where

-- File Charter:
--   * The denotation of GTSFImp cast terms in the graph model
--     (`Denot.GraphModel`; notes/denotational-dgg.md, Section 9, step 2).
--   * `⟦ M ⟧ θ ρ n`: the results of M under a representation environment
--     θ (type variables to seals), a term environment ρ, starting at seal
--     counter n.  A seal created at counter n is n; it is `bind`'s new
--     type variable.
--   * Allocation is mirrored exactly, because soundness is subject
--     expansion (`⟦ N ⟧ ⊆ ⟦ M ⟧`, as in PolyG) and results carry their
--     final counter:
--       type application   one seal; its body starts one later;
--       `inst` cast        two seals: `α := ★`, then the value's own
--                          instantiation at `α`;
--       ∀-conversion       two seals per instantiation: the proxy's, then
--                          the inner value's instantiation at it.
--   * The type application reveals with the very conversion term that
--     reduction produces, `〖 0 , ⇑ᵗ A ↑ B 〗`.  A ∀-conversion's inner
--     instantiation reveals on its source body type, which is not a
--     subterm of the conversion; `revV`/`conV` give that reveal by
--     recursion on the type.  Its representation is always a type
--     variable, so replacing it keeps the type's shape and the recursion
--     is structural.  (`proof/Denot` relates `revV` to `〖_,_↑_〗`.)
--   * Representations: a type variable denotes a seal, or `★` inside an
--     `inst` cast, where reduction substitutes `★` for the instantiated
--     variable (`c [ ★/0 ]ᶜ`); a tag or projection at such a variable is
--     the identity, as `subst-to-star-var` makes it.
--   * Casts at `bot-elim` act as `∀ᶜ (X !)`; no closed value has type
--     `∀X.X`, so this choice is never observed.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency
open import Conversion
open import CastTerms
open import Primitives using (Const)
open import Denot.GraphModel

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

data Rep : Set where
  sealʳ : Seal → Rep
  starʳ : Rep

REnv : TyCtx → Set
REnv Δ = TyVar Δ → Rep

infixr 5 _•ʳ_ _•_

_•ʳ_ : ∀ {Δ} → Rep → REnv Δ → REnv (sucℕ Δ)
(r •ʳ θ) zero = r
(r •ʳ θ) (suc X) = θ X

Env : Set₁
Env = ℕ → 𝒱

_•_ : 𝒱 → Env → Env
(D • ρ) zeroℕ = D
(D • ρ) (sucℕ x) = ρ x

θ₀ : REnv zeroℕ
θ₀ ()

ρ₀ : Env
ρ₀ x v = ⊥

------------------------------------------------------------------------
-- Representation-level seals and tags
------------------------------------------------------------------------

unsealR : Rep → 𝒱 → 𝒱
unsealR (sealʳ σ) D = unsealᴾ σ D
unsealR starʳ D = D

sealR : Rep → 𝒱 → 𝒱
sealR (sealʳ σ) D = sealᴾ σ D
sealR starʳ D = D

-- tagging with a ground; a variable represented by ★ does not tag
injR : ∀ {Δ} {G : Ty Δ} → Ground G → REnv Δ → 𝒱 → 𝒱
injR (＇ X) θ D with θ X
injR (＇ X) θ D | sealʳ σ = injᴾ (gσ σ) D
injR (＇ X) θ D | starʳ = D
injR (‵ ι) θ D = injᴾ (gι ι) D
injR ★⇒★ θ D = injᴾ g⇒ D
injR ∀★ θ D = injᴾ g∀ D

-- projecting to a ground
projR : ∀ {Δ} {G : Ty Δ} → Ground G → REnv Δ → 𝒱 → ℕ → ℛ
projR (＇ X) θ D m with θ X
projR (＇ X) θ D m | sealʳ σ = proj (gσ σ) D m
projR (＇ X) θ D m | starʳ = retᴿ D m
projR (‵ ι) θ D m = proj (gι ι) D m
projR ★⇒★ θ D m = proj g⇒ D m
projR ∀★ θ D m = proj g∀ D m

------------------------------------------------------------------------
-- Proxies
------------------------------------------------------------------------

-- a function proxy: arguments through `a`, results through `b`
funProxy : (𝒱 → ℕ → ℛ) → (𝒱 → ℕ → ℛ) → 𝒱 → ℕ → ℛ
funProxy a b E m =
  guard νλ E (retᴿ (Λᶠ (λ E′ m′ →
    a E′ m′ ≫= λ E₁ m₁ → (E ●[ m₁ ] E₁) ≫= b)) m)

-- a ∀ proxy for a conversion: its instantiation at σ instantiates the
-- inner value at the next seal, reveals that seal on the source body
-- (`inner`), then converts the body (`body`)
convAllProxy : (Seal → 𝒱 → ℕ → ℛ) → (Seal → 𝒱 → ℕ → ℛ) → 𝒱 → ℕ → ℛ
convAllProxy inner body E m =
  guard ν∀ E (retᴿ (Λᴾ (λ σ →
    (E ◆ sucℕ σ) ≫= λ E₁ m₁ → inner σ E₁ m₁ ≫= body σ)) m)

------------------------------------------------------------------------
-- Reveal and conceal at one variable, by recursion on the type
------------------------------------------------------------------------

-- `revV C X θ` is the denotation of `〖 X , R ↑ C 〗` for R a type
-- variable or ★; `conV C X θ` that of `makeConceal X R C`.
mutual
  revV : ∀ {Δ} → Ty Δ → TyVar Δ → REnv Δ → 𝒱 → ℕ → ℛ
  revV (＇ Y) X θ E m with X ≟ Y
  revV (＇ Y) X θ E m | yes _ = retᴿ (unsealR (θ X) E) m
  revV (＇ Y) X θ E m | no _ = retᴿ E m
  revV (‵ ι) X θ E m = retᴿ E m
  revV ★ X θ E m = retᴿ E m
  revV (A ⇒ B) X θ = funProxy (conV A X θ) (revV B X θ)
  revV (`∀ A) X θ =
    convAllProxy
      (λ σ → revV A zero (sealʳ (sucℕ σ) •ʳ θ))
      (λ σ → revV A (suc X) (sealʳ σ •ʳ θ))

  conV : ∀ {Δ} → Ty Δ → TyVar Δ → REnv Δ → 𝒱 → ℕ → ℛ
  conV (＇ Y) X θ E m with X ≟ Y
  conV (＇ Y) X θ E m | yes _ = retᴿ (sealR (θ X) E) m
  conV (＇ Y) X θ E m | no _ = retᴿ E m
  conV (‵ ι) X θ E m = retᴿ E m
  conV ★ X θ E m = retᴿ E m
  conV (A ⇒ B) X θ = funProxy (revV A X θ) (conV B X θ)
  conV (`∀ A) X θ =
    convAllProxy
      (λ σ → revV A zero (sealʳ (sucℕ σ) •ʳ θ))
      (λ σ → conV A (suc X) (sealʳ σ •ʳ θ))

------------------------------------------------------------------------
-- Conversions
------------------------------------------------------------------------

mutual
  ⟦_⟧↑ : ∀ {Δ A B} → Conv↑ Δ A B → REnv Δ → 𝒱 → ℕ → ℛ
  ⟦ unseal X R ⟧↑ θ E m = retᴿ (unsealR (θ X) E) m
  ⟦ c ↦↑ d ⟧↑ θ = funProxy (⟦ c ⟧↓ θ) (⟦ d ⟧↑ θ)
  ⟦ `∀↑_ {A = C} c ⟧↑ θ =
    convAllProxy
      (λ σ → revV C zero (sealʳ (sucℕ σ) •ʳ θ))
      (λ σ → ⟦ c ⟧↑ (sealʳ σ •ʳ θ))
  ⟦ id↑ A ⟧↑ θ E m = retᴿ E m

  ⟦_⟧↓ : ∀ {Δ A B} → Conv↓ Δ A B → REnv Δ → 𝒱 → ℕ → ℛ
  ⟦ seal X R ⟧↓ θ E m = retᴿ (sealR (θ X) E) m
  ⟦ c ↦↓ d ⟧↓ θ = funProxy (⟦ c ⟧↑ θ) (⟦ d ⟧↓ θ)
  ⟦ `∀↓_ {A = C} c ⟧↓ θ =
    convAllProxy
      (λ σ → revV C zero (sealʳ (sucℕ σ) •ʳ θ))
      (λ σ → ⟦ c ⟧↓ (sealʳ σ •ʳ θ))
  ⟦ id↓ A ⟧↓ θ E m = retᴿ E m

------------------------------------------------------------------------
-- Casts
------------------------------------------------------------------------

⟦_⟧ᶜ : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty Δ}
  → μ ⊢ A ∼ B → REnv Δ → 𝒱 → ℕ → ℛ
⟦ id a ⟧ᶜ θ E m = retᴿ E m
⟦ c ↦ d ⟧ᶜ θ = funProxy (⟦ c ⟧ᶜ θ) (⟦ d ⟧ᶜ θ)
⟦ ∀ᶜ c ⟧ᶜ θ E m =
  guard ν∀ E (retᴿ (Λᴾ (λ σ → (E ◆ σ) ≫= ⟦ c ⟧ᶜ (sealʳ σ •ʳ θ))) m)
⟦ _! ⦃ Gᵍ ⦄ c ⟧ᶜ θ E m =
  ⟦ c ⟧ᶜ θ E m ≫= λ E₁ m₁ → retᴿ (injR Gᵍ θ E₁) m₁
⟦ ？_ ⦃ Gᵍ ⦄ c ⟧ᶜ θ E m = projR Gᵍ θ E m ≫= ⟦ c ⟧ᶜ θ
-- reduction (β-inst) creates α := ★ at m, instantiates the value at α
-- (creating m + 1), reveals both, and casts with α read as ★
⟦ (inst_ {A = A} c) B≢★ ⟧ᶜ θ E m =
  (E ◆ sucℕ m) ≫= λ E₁ m₁ →
  ⟦ 〖 zero , ＇ suc zero ↑ renameᵗ (extᵗ suc) A 〗 ⟧↑
    (sealʳ (sucℕ m) •ʳ sealʳ m •ʳ θ) E₁ m₁ ≫= λ E₂ m₂ →
  ⟦ 〖 zero , ★ ↑ A 〗 ⟧↑ (sealʳ m •ʳ θ) E₂ m₂ ≫=
  ⟦ c ⟧ᶜ (starʳ •ʳ θ)
-- a gen value; its instantiation at σ casts with the gen variable as σ
⟦ (gen c) A≢★ ⟧ᶜ θ E m =
  retᴿ (Λᴾ (λ σ → ⟦ c ⟧ᶜ (sealʳ σ •ʳ θ) E (sucℕ σ))) m
⟦ bot-elim ⟧ᶜ θ E m =
  guard ν∀ E (retᴿ (Λᴾ (λ σ →
    (E ◆ σ) ≫= λ E₁ m₁ → retᴿ (injᴾ (gσ σ) E₁) m₁)) m)
⟦ bot-intro ⟧ᶜ θ E m = errᴿ

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

⟦_⟧ : ∀ {Δ} → Term Δ → REnv Δ → Env → ℕ → ℛ
⟦ ` x ⟧ θ ρ n = retᴿ (ρ x) n
⟦ ƛ M ⟧ θ ρ n = retᴿ (Λᶠ (λ E m → ⟦ M ⟧ θ (E • ρ) m)) n
⟦ L · M ⟧ θ ρ n =
  ⟦ L ⟧ θ ρ n ≫= λ F n₁ → ⟦ M ⟧ θ ρ n₁ ≫= λ E n₂ → F ●[ n₂ ] E
⟦ Λ M ⟧ θ ρ n = retᴿ (Λᴾ (λ σ → ⟦ M ⟧ (sealʳ σ •ʳ θ) ρ (sucℕ σ))) n
-- the instantiation creates seal n₁; reduction then reveals it on B
⟦ M ⦂∀ B [ A ] ⟧ θ ρ n =
  ⟦ M ⟧ θ ρ n ≫= λ F n₁ →
  (F ◆ n₁) ≫= ⟦ 〖 zero , ⇑ᵗ A ↑ B 〗 ⟧↑ (sealʳ n₁ •ʳ θ)
⟦ $ κ ⟧ θ ρ n = retᴿ ⌈ vconst κ ⌉ n
⟦ L ⊕[ op ] M ⟧ θ ρ n =
  ⟦ L ⟧ θ ρ n ≫= λ D n₁ → ⟦ M ⟧ θ ρ n₁ ≫= λ E n₂ → retᴿ (δᴾ op D E) n₂
⟦ M ⟨ c ⟩ ⟧ θ ρ n = ⟦ M ⟧ θ ρ n ≫= ⟦ c ⟧ᶜ θ
⟦ M ↑ c ⟧ θ ρ n = ⟦ M ⟧ θ ρ n ≫= ⟦ c ⟧↑ θ
⟦ M ↓ c ⟧ θ ρ n = ⟦ M ⟧ θ ρ n ≫= ⟦ c ⟧↓ θ
⟦ blame ⟧ θ ρ n = errᴿ
