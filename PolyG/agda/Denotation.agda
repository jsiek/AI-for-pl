module Denotation where

-- File Charter:
--   * The denotation of PolyCν terms in the graph model (GraphModel.agda;
--     PolyG/notes/denotational-graduality.md, Section 4).
--   * ⟦ M ⟧ θ ρ n: the results of M under a seal environment θ (type
--     variables to seals), an environment ρ (term variables to sets of
--     values), starting at seal counter n.  A runtime seal name
--     `tseal σ` denotes σ.
--   * Casts never change the counter.  Instantiation creates the seal
--     equal to the current counter, and its body starts one later.

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)

open import Types
open import Terms
open import GraphModel
open import GradualityDefinitions using (Observation; bool-obs; other-obs)

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

-- seal environments: type variables to seals
SEnv : Set
SEnv = Var → Seal

infixr 5 _•ᵗ_ _•_

_•ᵗ_ : Seal → SEnv → SEnv
(σ •ᵗ θ) zero = σ
(σ •ᵗ θ) (suc i) = θ i

Env : Set₁
Env = ℕ → 𝒱

_•_ : 𝒱 → Env → Env
(D • ρ) zero = D
(D • ρ) (suc x) = ρ x

-- the environments of a closed term
θ₀ : SEnv
θ₀ i = zero

ρ₀ : Env
ρ₀ x v = ⊥

------------------------------------------------------------------------
-- Names and grounds
------------------------------------------------------------------------

⟦_⟧ₙ : Name → SEnv → Seal
⟦ tvar i ⟧ₙ θ = θ i
⟦ tseal σ ⟧ₙ θ = σ

⟦_⟧ᴳ : Ground → SEnv → Ground
⟦ G‵ α ⟧ᴳ θ = G‵ (tseal (⟦ α ⟧ₙ θ))
⟦ G𝔹 ⟧ᴳ θ = G𝔹
⟦ G⇒ ⟧ᴳ θ = G⇒
⟦ G∀ ⟧ᴳ θ = G∀

-- a precision derivation with its type variables replaced by their
-- seals (a closed derivation)
⟦_⟧ᵖ : Prec → SEnv → Prec
⟦ p ⟧ᵖ θ = substᵖ (λ i → tseal (θ i)) p

------------------------------------------------------------------------
-- Casts
------------------------------------------------------------------------

⟦_,_⟧ᶜ : Dir → Prec → SEnv → 𝒱 → ℕ → ℛ
⟦ d , ★⊑ ⟧ᶜ θ E m = retᴿ E m
⟦ d , 𝔹⊑ ⟧ᶜ θ E m = retᴿ E m
⟦ d , ‵⊑ α ⟧ᶜ θ E m = retᴿ E m
⟦ d , p ⇒⊑ q ⟧ᶜ θ E m =
  guard νλ E (retᴿ (Λ (λ E′ m′ →
    ⟦ flip d , p ⟧ᶜ θ E′ m′ ≫= λ E₁ m₁ →
    (E ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ)) m)
⟦ d , ∀⊑ p ⟧ᶜ θ E m =
  guard ν∀ E (retᴿ (Λᴾ (λ σ → (E ◆ σ) ≫= ⟦ d , p ⟧ᶜ (σ •ᵗ θ))) m)
⟦ up , tag G p ⟧ᶜ θ E m =
  ⟦ up , p ⟧ᶜ θ E m ≫= λ E₁ m₁ → retᴿ (injᴾ (⟦ G ⟧ᴳ θ) E₁) m₁
⟦ down , tag G p ⟧ᶜ θ E m = proj (⟦ G ⟧ᴳ θ) E m ≫= ⟦ down , p ⟧ᶜ θ

-- a stack of casts, outermost first
⟦_⟧ˢ : Stack → SEnv → ℛ → ℛ
⟦ [] ⟧ˢ θ R = R
⟦ (d , p) ∷ cs ⟧ˢ θ R = ⟦ cs ⟧ˢ θ R ≫= ⟦ d , p ⟧ᶜ θ

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

⟦_⟧ : Term → SEnv → Env → ℕ → ℛ
⟦ ` x ⟧ θ ρ n = retᴿ (ρ x) n
⟦ ℧ ⟧ θ ρ n = errᴿ
⟦ true ⟧ θ ρ n = retᴿ ⌈ vtrue ⌉ n
⟦ false ⟧ θ ρ n = retᴿ ⌈ vfalse ⌉ n
⟦ if L M N ⟧ θ ρ n =
  ⟦ L ⟧ θ ρ n ≫= λ E m → condᴿ E (⟦ M ⟧ θ ρ m) (⟦ N ⟧ θ ρ m)
⟦ ƛ A M ⟧ θ ρ n = retᴿ (Λ (λ E m → ⟦ M ⟧ θ (E • ρ) m)) n
⟦ L · M ⟧ θ ρ n =
  ⟦ L ⟧ θ ρ n ≫= λ F n₁ → ⟦ M ⟧ θ ρ n₁ ≫= λ E n₂ → F ●[ n₂ ] E
⟦ letv M N ⟧ θ ρ n = ⟦ M ⟧ θ ρ n ≫= λ E m → ⟦ N ⟧ θ (E • ρ) m
⟦ seal α M ⟧ θ ρ n =
  ⟦ M ⟧ θ ρ n ≫= λ E m → retᴿ (sealᴾ (⟦ α ⟧ₙ θ) E) m
⟦ unseal α M ⟧ θ ρ n =
  ⟦ M ⟧ θ ρ n ≫= λ E m → retᴿ (unsealᴾ (⟦ α ⟧ₙ θ) E) m
⟦ is G M ⟧ θ ρ n =
  ⟦ M ⟧ θ ρ n ≫= λ E m → retᴿ (testᴾ (⟦ G ⟧ᴳ θ) E) m
⟦ inj G M ⟧ θ ρ n =
  ⟦ M ⟧ θ ρ n ≫= λ E m → retᴿ (injᴾ (⟦ G ⟧ᴳ θ) E) m
⟦ cast d p M ⟧ θ ρ n = ⟦ M ⟧ θ ρ n ≫= ⟦ d , p ⟧ᶜ θ
⟦ Λν cs M ⟧ θ ρ n =
  retᴿ (Λᴾ (λ σ → ⟦ cs ⟧ˢ (σ •ᵗ θ) (⟦ M ⟧ (σ •ᵗ θ) ρ (suc σ)))) n
⟦ inst M B N ⟧ θ ρ n =
  ⟦ M ⟧ θ ρ n ≫= λ F n₁ →
  (F ◆ n₁) ≫= λ E n₂ →
  ⟦ N ⟧ (n₁ •ᵗ θ) (E • ρ) n₂

------------------------------------------------------------------------
-- Observations of denotational values
------------------------------------------------------------------------

obs : Val → Observation
obs vtrue = bool-obs true
obs vfalse = bool-obs false
obs (sealᵛ σ v) = obs v
obs (injᵛ G v) = obs v
obs (U ⟼ r at m) = other-obs
obs (σ ⟼∀ r) = other-obs
obs νλ = other-obs
obs ν∀ = other-obs
