module proof.Determinism where

-- File Charter:
--   * Determinism of PolyCν reduction (untyped):
--     `—→-deterministic`, together with `value-irreducible` (values do
--     not step) and `℧-irreducible` (℧ does not step).
--   * The key fact is unique decomposition into frames (`plug-inj`),
--     stated over the inductive view `Plug F M T` of `T ≡ plug F M`, so
--     that Agda's unifier discards incompatible frame/term pairs.
--   * Consumed by the top-level TypeSafety.agda.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)
open import Relation.Nullary using (¬_)

open import Types
open import Terms
open import Reduction

------------------------------------------------------------------------
-- Plugging, as an inductive relation
------------------------------------------------------------------------

data Plug : Frame → Term → Term → Set where
  p-if     : ∀ {L M N} → Plug (if□ M N) L (if L M N)
  p-□·     : ∀ {L M} → Plug (□· M) L (L · M)
  p-app    : ∀ {V v M} → Plug (app□ V v) M (V · M)
  p-letv   : ∀ {M N} → Plug (letv□ N) M (letv M N)
  p-seal   : ∀ {α M} → Plug (seal□ α) M (seal α M)
  p-unseal : ∀ {α M} → Plug (unseal□ α) M (unseal α M)
  p-is     : ∀ {G M} → Plug (is□ G) M (is G M)
  p-inj    : ∀ {G M} → Plug (inj□ G) M (inj G M)
  p-cast   : ∀ {d p M} → Plug (cast□ d p) M (cast d p M)
  p-inst   : ∀ {B ℓ N M} → Plug (inst□ B ℓ N) M (inst M B ℓ N)

plug-Plug : ∀ F M → Plug F M (plug F M)
plug-Plug (if□ M N) L = p-if
plug-Plug (□· M) L = p-□·
plug-Plug (app□ V v) M = p-app
plug-Plug (letv□ N) M = p-letv
plug-Plug (seal□ α) M = p-seal
plug-Plug (unseal□ α) M = p-unseal
plug-Plug (is□ G) M = p-is
plug-Plug (inj□ G) M = p-inj
plug-Plug (cast□ d p) M = p-cast
plug-Plug (inst□ B ℓ N) M = p-inst

≡-Plug : ∀ {T M} F → T ≡ plug F M → Plug F M T
≡-Plug F refl = plug-Plug F _

-- unique decomposition: a term is the plugging of at most one frame
-- around a non-value
plug-inj : ∀ {F F′ M M′ T}
  → Plug F M T
  → Plug F′ M′ T
  → ¬ Value M
  → ¬ Value M′
  → M ≡ M′ × (∀ N → plug F N ≡ plug F′ N)
plug-inj p-if p-if nv nv′ = refl , λ N → refl
plug-inj p-□· p-□· nv nv′ = refl , λ N → refl
plug-inj p-□· (p-app {v = v}) nv nv′ = ⊥-elim (nv v)
plug-inj (p-app {v = v}) p-□· nv nv′ = ⊥-elim (nv′ v)
plug-inj p-app p-app nv nv′ = refl , λ N → refl
plug-inj p-letv p-letv nv nv′ = refl , λ N → refl
plug-inj p-seal p-seal nv nv′ = refl , λ N → refl
plug-inj p-unseal p-unseal nv nv′ = refl , λ N → refl
plug-inj p-is p-is nv nv′ = refl , λ N → refl
plug-inj p-inj p-inj nv nv′ = refl , λ N → refl
plug-inj p-cast p-cast nv nv′ = refl , λ N → refl
plug-inj p-inst p-inst nv nv′ = refl , λ N → refl

------------------------------------------------------------------------
-- Irreducible terms
------------------------------------------------------------------------

℧-not-value : ¬ Value ℧
℧-not-value ()

-- a value is never a frame around ℧
value-not-plug-℧ : ∀ {F T} → Value T → Plug F ℧ T → ⊥
value-not-plug-℧ (V-seal ()) p-seal
value-not-plug-℧ (V-inj ()) p-inj
value-not-plug-℧ (V-cast⇒ ()) p-cast

value-irreducible : ∀ {Σ Σ′ V N} → Value V → ¬ (Σ ▷ V —→ Σ′ ▷ N)
value-not-plug-step : ∀ {Σ Σ′ F M N T}
  → Value T → Plug F M T → ¬ (Σ ▷ M —→ Σ′ ▷ N)

value-irreducible v (ξξ F refl refl s) =
  value-not-plug-step v (plug-Plug F _) s
value-irreducible v (ξξ-℧ F refl) = value-not-plug-℧ v (plug-Plug F ℧)
value-irreducible () (β-letv v)
value-irreducible () (β-unseal v)
value-irreducible () (β-is-yes v)
value-irreducible () (β-is-no v G≢H)
value-irreducible () β-if-true
value-irreducible () β-if-false
value-irreducible () (β-ƛ v)
value-irreducible () (β-cast⇒ v w)
value-irreducible () β-inst
value-irreducible (V-cast⇒ v) (β-id () w)
value-irreducible () (β-tag-up v)
value-irreducible () (β-tag-down v)
value-irreducible () (β-tag-down-℧ v G≢H)
value-irreducible () β-cast∀

value-not-plug-step (V-seal v) p-seal s = value-irreducible v s
value-not-plug-step (V-inj v) p-inj s = value-irreducible v s
value-not-plug-step (V-cast⇒ v) p-cast s = value-irreducible v s

℧-irreducible : ∀ {Σ Σ′ N} → ¬ (Σ ▷ ℧ —→ Σ′ ▷ N)
℧-irreducible (ξξ F eq refl s) = no-plug (plug-Plug F _) eq
  where
  no-plug : ∀ {F M T} → Plug F M T → ℧ ≡ T → ⊥
  no-plug p-if ()
  no-plug p-□· ()
  no-plug p-app ()
  no-plug p-letv ()
  no-plug p-seal ()
  no-plug p-unseal ()
  no-plug p-is ()
  no-plug p-inj ()
  no-plug p-cast ()
  no-plug p-inst ()
℧-irreducible (ξξ-℧ F eq) = no-plug (plug-Plug F ℧) eq
  where
  no-plug : ∀ {F M T} → Plug F M T → ℧ ≡ T → ⊥
  no-plug p-if ()
  no-plug p-□· ()
  no-plug p-app ()
  no-plug p-letv ()
  no-plug p-seal ()
  no-plug p-unseal ()
  no-plug p-is ()
  no-plug p-inj ()
  no-plug p-cast ()
  no-plug p-inst ()

stepping-not-value : ∀ {Σ Σ′ M N} → Σ ▷ M —→ Σ′ ▷ N → ¬ Value M
stepping-not-value s v = value-irreducible v s

------------------------------------------------------------------------
-- Determinism
------------------------------------------------------------------------

—→-deterministic : ∀ {Σ Σ₁ Σ₂ M N₁ N₂}
  → Σ ▷ M —→ Σ₁ ▷ N₁
  → Σ ▷ M —→ Σ₂ ▷ N₂
  → Σ₁ ≡ Σ₂ × N₁ ≡ N₂

-- a step inside a frame determines every step of the whole term
det-ξ : ∀ {Σ Σ₁ Σ₂ F M N₁ T N₂}
  → Plug F M T
  → Σ ▷ M —→ Σ₁ ▷ N₁
  → Σ ▷ T —→ Σ₂ ▷ N₂
  → Σ₁ ≡ Σ₂ × plug F N₁ ≡ N₂

-- a frame around ℧ determines every step of the whole term
det-℧ : ∀ {Σ Σ₂ F T N₂}
  → Plug F ℧ T
  → Σ ▷ T —→ Σ₂ ▷ N₂
  → Σ ≡ Σ₂ × ℧ ≡ N₂

swap : ∀ {A B : Set}{a a′ : A}{b b′ : B}
  → a ≡ a′ × b ≡ b′ → a′ ≡ a × b′ ≡ b
swap (refl , refl) = refl , refl

—→-deterministic (ξξ F refl refl s₁) s₂ = det-ξ (plug-Plug F _) s₁ s₂
—→-deterministic (ξξ-℧ F refl) s₂ = det-℧ (plug-Plug F ℧) s₂
—→-deterministic s₁ (ξξ F eq refl s₂) = swap (det-ξ (≡-Plug F eq) s₂ s₁)
—→-deterministic s₁ (ξξ-℧ F eq) = swap (det-℧ (≡-Plug F eq) s₁)
—→-deterministic (β-letv v) (β-letv v′) = refl , refl
—→-deterministic (β-unseal v) (β-unseal v′) = refl , refl
—→-deterministic (β-is-yes v) (β-is-yes v′) = refl , refl
—→-deterministic (β-is-yes v) (β-is-no v′ G≢G) = ⊥-elim (G≢G refl)
—→-deterministic (β-is-no v G≢G) (β-is-yes v′) = ⊥-elim (G≢G refl)
—→-deterministic (β-is-no v G≢H) (β-is-no v′ G≢H′) = refl , refl
—→-deterministic β-if-true β-if-true = refl , refl
—→-deterministic β-if-false β-if-false = refl , refl
—→-deterministic (β-ƛ v) (β-ƛ v′) = refl , refl
—→-deterministic (β-cast⇒ v w) (β-cast⇒ v′ w′) = refl , refl
—→-deterministic β-inst β-inst = refl , refl
—→-deterministic (β-id a v) (β-id a′ v′) = refl , refl
—→-deterministic (β-id () v) (β-tag-up v′)
—→-deterministic (β-id () v) (β-tag-down v′)
—→-deterministic (β-id () v) (β-tag-down-℧ v′ G≢H)
—→-deterministic (β-id () v) β-cast∀
—→-deterministic (β-tag-up v) (β-id () v′)
—→-deterministic (β-tag-up v) (β-tag-up v′) = refl , refl
—→-deterministic (β-tag-down v) (β-id () v′)
—→-deterministic (β-tag-down v) (β-tag-down v′) = refl , refl
—→-deterministic (β-tag-down v) (β-tag-down-℧ v′ G≢G) = ⊥-elim (G≢G refl)
—→-deterministic (β-tag-down-℧ v G≢H) (β-id () v′)
—→-deterministic (β-tag-down-℧ v G≢G) (β-tag-down v′) = ⊥-elim (G≢G refl)
—→-deterministic (β-tag-down-℧ v G≢H) (β-tag-down-℧ v′ G≢H′) = refl , refl
—→-deterministic β-cast∀ (β-id () v′)
—→-deterministic β-cast∀ β-cast∀ = refl , refl

det-ξ p s₁ (ξξ F′ refl refl s₂)
  with plug-inj p (plug-Plug F′ _) (stepping-not-value s₁)
                (stepping-not-value s₂)
det-ξ p s₁ (ξξ F′ refl refl s₂) | refl , F≡F′
  with —→-deterministic s₁ s₂
det-ξ p s₁ (ξξ F′ refl refl s₂) | refl , F≡F′ | refl , refl =
  refl , F≡F′ _
det-ξ p s₁ (ξξ-℧ F′ refl)
  with plug-inj p (plug-Plug F′ ℧) (stepping-not-value s₁) ℧-not-value
det-ξ p s₁ (ξξ-℧ F′ refl) | refl , F≡F′ = ⊥-elim (℧-irreducible s₁)
det-ξ p-letv s₁ (β-letv v) = ⊥-elim (value-irreducible v s₁)
det-ξ p-unseal s₁ (β-unseal v) = ⊥-elim (value-irreducible (V-seal v) s₁)
det-ξ p-is s₁ (β-is-yes v) = ⊥-elim (value-irreducible (V-inj v) s₁)
det-ξ p-is s₁ (β-is-no v G≢H) = ⊥-elim (value-irreducible (V-inj v) s₁)
det-ξ p-if s₁ β-if-true = ⊥-elim (value-irreducible V-true s₁)
det-ξ p-if s₁ β-if-false = ⊥-elim (value-irreducible V-false s₁)
det-ξ p-□· s₁ (β-ƛ v) = ⊥-elim (value-irreducible V-ƛ s₁)
det-ξ p-app s₁ (β-ƛ v) = ⊥-elim (value-irreducible v s₁)
det-ξ p-□· s₁ (β-cast⇒ v w) = ⊥-elim (value-irreducible (V-cast⇒ v) s₁)
det-ξ p-app s₁ (β-cast⇒ v w) = ⊥-elim (value-irreducible w s₁)
det-ξ p-inst s₁ β-inst = ⊥-elim (value-irreducible V-Λν s₁)
det-ξ p-cast s₁ (β-id a v) = ⊥-elim (value-irreducible v s₁)
det-ξ p-cast s₁ (β-tag-up v) = ⊥-elim (value-irreducible v s₁)
det-ξ p-cast s₁ (β-tag-down v) = ⊥-elim (value-irreducible (V-inj v) s₁)
det-ξ p-cast s₁ (β-tag-down-℧ v G≢H) =
  ⊥-elim (value-irreducible (V-inj v) s₁)
det-ξ p-cast s₁ β-cast∀ = ⊥-elim (value-irreducible V-Λν s₁)

det-℧ p (ξξ F′ refl refl s₂)
  with plug-inj p (plug-Plug F′ _) ℧-not-value (stepping-not-value s₂)
det-℧ p (ξξ F′ refl refl s₂) | refl , F≡F′ = ⊥-elim (℧-irreducible s₂)
det-℧ p (ξξ-℧ F′ refl) = refl , refl
det-℧ p-letv (β-letv ())
det-℧ () β-if-true
det-℧ () β-if-false
det-℧ p-app (β-ƛ ())
det-℧ p-app (β-cast⇒ v ())
det-℧ () β-inst
det-℧ p-cast (β-id a ())
det-℧ p-cast (β-tag-up ())
det-℧ () (β-tag-down v)
det-℧ () (β-tag-down-℧ v G≢H)
det-℧ () β-cast∀
