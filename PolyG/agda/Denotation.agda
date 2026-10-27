module Denotation where

-- File Charter:
--   * The denotation of PolyCν terms in the graph model (GraphModel.agda;
--     PolyG/notes/denotational-graduality.md, Section 4).
--   * ⟦ M ⟧ S δ ρ n: the results of M given the labels S of the seals
--     created before evaluation starts, a type environment δ (type
--     variables to seals with their labels), an environment ρ (term
--     variables to sets of values), starting at seal counter n.
--   * Casts and tags only need seal numbers (an SEnv).
--   * Casts never change the counter.  Instantiation creates the seal
--     equal to the current counter, and its body starts one later.

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Types
open import Terms
open import GraphModel
open import GradualityDefinitions using (Observation; bool-obs; other-obs)

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

-- seal environments: type variables to seals (used by casts and tags)
SEnv : Set
SEnv = Var → Seal

-- type environments: type variables to seals with their labels
TEnv : Set
TEnv = Var → Seal × Prec

-- seal labels: the label of each seal created before evaluation starts
SLab : Set
SLab = Seal → Prec

infixr 5 _•ᵗ_ _•_

_•ᵗ_ : ∀ {X : Set} → X → (Var → X) → Var → X
(σ •ᵗ δ) zero = σ
(σ •ᵗ δ) (suc i) = δ i

⌊_⌋ᵗ : TEnv → SEnv
⌊ δ ⌋ᵗ i = proj₁ (δ i)

Env : Set₁
Env = ℕ → 𝒱

_•_ : 𝒱 → Env → Env
(D • ρ) zero = D
(D • ρ) (suc x) = ρ x

-- the environments of a closed term
δ₀ : TEnv
δ₀ i = zero , 𝔹⊑

ρ₀ : Env
ρ₀ x v = ⊥

------------------------------------------------------------------------
-- Names, grounds and types
------------------------------------------------------------------------

-- the seal a name stands for
⟦_⟧# : Name → SEnv → Seal
⟦ tvar i ⟧# θ = θ i
⟦ tseal σ ⟧# θ = σ

-- the seal a name stands for, with its label
⟦_⟧ₙ : Name → SLab → TEnv → Seal × Prec
⟦ tvar i ⟧ₙ S δ = δ i
⟦ tseal σ ⟧ₙ S δ = σ , S σ

⟦_⟧ᴳ : Ground → SEnv → Ground
⟦ G‵ α ⟧ᴳ θ = G‵ (tseal (⟦ α ⟧# θ))
⟦ G𝔹 ⟧ᴳ θ = G𝔹
⟦ G⇒ ⟧ᴳ θ = G⇒
⟦ G∀ ⟧ᴳ θ = G∀

-- a label with its type variables replaced by their seals
⟦_⟧ˡ : Prec → SEnv → Prec
⟦ ℓ ⟧ˡ θ = substᵖ (λ i → tseal (θ i)) ℓ

------------------------------------------------------------------------
-- Casts
------------------------------------------------------------------------

⟦_,_⟧ᶜ : Dir → Prec → SEnv → 𝒱 → ℕ → ℛ
⟦ d , ★⊑ ⟧ᶜ θ E m = retᴿ E m
⟦ d , 𝔹⊑ ⟧ᶜ θ E m = retᴿ E m
⟦ d , ‵⊑ α ⟧ᶜ θ E m = retᴿ E m
⟦ d , p ⇒⊑ q ⟧ᶜ θ E m =
  guard E (retᴿ (Λ (λ E′ m′ →
    ⟦ flip d , p ⟧ᶜ θ E′ m′ ≫= λ E₁ m₁ →
    (E ●[ m₁ ] E₁) ≫= ⟦ d , q ⟧ᶜ θ)) m)
⟦ d , ∀⊑ p ⟧ᶜ θ E m =
  guard E (retᴿ (Λᴾ (λ σB → (E ◆ σB) ≫= ⟦ d , p ⟧ᶜ (proj₁ σB •ᵗ θ))) m)
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

⟦_⟧ : Term → SLab → TEnv → Env → ℕ → ℛ
⟦ ` x ⟧ S δ ρ n = retᴿ (ρ x) n
⟦ ℧ ⟧ S δ ρ n = errᴿ
⟦ true ⟧ S δ ρ n = retᴿ ⌈ vtrue ⌉ n
⟦ false ⟧ S δ ρ n = retᴿ ⌈ vfalse ⌉ n
⟦ if L M N ⟧ S δ ρ n =
  ⟦ L ⟧ S δ ρ n ≫= λ E m → condᴿ E (⟦ M ⟧ S δ ρ m) (⟦ N ⟧ S δ ρ m)
⟦ ƛ A M ⟧ S δ ρ n = retᴿ (Λ (λ E m → ⟦ M ⟧ S δ (E • ρ) m)) n
⟦ L · M ⟧ S δ ρ n =
  ⟦ L ⟧ S δ ρ n ≫= λ F n₁ → ⟦ M ⟧ S δ ρ n₁ ≫= λ E n₂ → F ●[ n₂ ] E
⟦ letv M N ⟧ S δ ρ n = ⟦ M ⟧ S δ ρ n ≫= λ E m → ⟦ N ⟧ S δ (E • ρ) m
⟦ seal α M ⟧ S δ ρ n =
  ⟦ M ⟧ S δ ρ n ≫= λ E m →
  retᴿ (sealᴾ (proj₁ (⟦ α ⟧ₙ S δ)) (proj₂ (⟦ α ⟧ₙ S δ)) E) m
⟦ unseal α M ⟧ S δ ρ n =
  ⟦ M ⟧ S δ ρ n ≫= λ E m →
  retᴿ (unsealᴾ (proj₁ (⟦ α ⟧ₙ S δ)) (proj₂ (⟦ α ⟧ₙ S δ)) E) m
⟦ is G M ⟧ S δ ρ n =
  ⟦ M ⟧ S δ ρ n ≫= λ E m → retᴿ (testᴾ (⟦ G ⟧ᴳ ⌊ δ ⌋ᵗ) E) m
⟦ inj G M ⟧ S δ ρ n =
  ⟦ M ⟧ S δ ρ n ≫= λ E m → retᴿ (injᴾ (⟦ G ⟧ᴳ ⌊ δ ⌋ᵗ) E) m
⟦ cast d p M ⟧ S δ ρ n = ⟦ M ⟧ S δ ρ n ≫= ⟦ d , p ⟧ᶜ ⌊ δ ⌋ᵗ
⟦ Λν cs M ⟧ S δ ρ n =
  retᴿ (Λᴾ (λ σB →
    ⟦ cs ⟧ˢ (proj₁ σB •ᵗ ⌊ δ ⌋ᵗ)
      (⟦ M ⟧ S (σB •ᵗ δ) ρ (suc (proj₁ σB))))) n
⟦ inst M B ℓ N ⟧ S δ ρ n =
  ⟦ M ⟧ S δ ρ n ≫= λ F n₁ →
  (F ◆ (n₁ , ⟦ ℓ ⟧ˡ ⌊ δ ⌋ᵗ)) ≫= λ E n₂ →
  ⟦ N ⟧ S ((n₁ , ⟦ ℓ ⟧ˡ ⌊ δ ⌋ᵗ) •ᵗ δ) (E • ρ) n₂

------------------------------------------------------------------------
-- Observations of denotational values
------------------------------------------------------------------------

obs : Val → Observation
obs vtrue = bool-obs true
obs vfalse = bool-obs false
obs (sealᵛ σ B v) = obs v
obs (injᵛ G v) = obs v
obs (U ⟼ r at m) = other-obs
obs (σB ⟼∀ r) = other-obs
obs ν = other-obs
