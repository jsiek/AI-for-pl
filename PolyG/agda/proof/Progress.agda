module proof.Progress where

-- File Charter:
--   * Canonical forms for closed PolyCν values at the types 𝔹, A ⇒ B,
--     ‵ α, ★ and ∀ν A.
--   * Progress: a closed well-typed term is a value, is ℧, or steps.
--   * Consumed by the top-level TypeSafety.agda.

open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import Terms
open import Reduction
open import Typing

------------------------------------------------------------------------
-- Canonical forms
------------------------------------------------------------------------

data Bool𝔹 : Term → Set where
  c-true  : Bool𝔹 true
  c-false : Bool𝔹 false

canonical-𝔹 : ∀ {Σ Δ V}
  → Value V → Σ ∣ Δ ∣ [] ⊢ V ⦂ 𝔹 → Bool𝔹 V
canonical-𝔹 V-true ⊢true = c-true
canonical-𝔹 V-false ⊢false = c-false
canonical-𝔹 (V-cast⇒ v) (⊢up () ⊢V)
canonical-𝔹 (V-cast⇒ v) (⊢down () ⊢V)

data Fun : Term → Set where
  c-ƛ     : ∀ {A M} → Fun (ƛ A M)
  c-cast⇒ : ∀ {d p q V} → Value V → Fun (cast d (p ⇒⊑ q) V)

canonical-⇒ : ∀ {Σ Δ V A B}
  → Value V → Σ ∣ Δ ∣ [] ⊢ V ⦂ A ⇒ B → Fun V
canonical-⇒ V-ƛ (⊢ƛ ⊢M) = c-ƛ
canonical-⇒ (V-cast⇒ v) ⊢V = c-cast⇒ v

data Sealed (α : Name) : Term → Set where
  c-seal : ∀ {V} → Value V → Sealed α (seal α V)

canonical-‵ : ∀ {Σ Δ V α}
  → Value V → Σ ∣ Δ ∣ [] ⊢ V ⦂ ‵ α → Sealed α V
canonical-‵ (V-seal v) (⊢seal nt ⊢V) = c-seal v
canonical-‵ (V-cast⇒ v) (⊢up () ⊢V)
canonical-‵ (V-cast⇒ v) (⊢down () ⊢V)

data Injected : Term → Set where
  c-inj : ∀ {G V} → Value V → Injected (inj G V)

canonical-★ : ∀ {Σ Δ V}
  → Value V → Σ ∣ Δ ∣ [] ⊢ V ⦂ ★ → Injected V
canonical-★ (V-inj v) (⊢inj wfG ⊢V) = c-inj v
canonical-★ (V-cast⇒ v) (⊢up () ⊢V)
canonical-★ (V-cast⇒ v) (⊢down () ⊢V)

data Proxy : Term → Set where
  c-Λν : ∀ {cs M} → Proxy (Λν cs M)

canonical-∀ : ∀ {Σ Δ V A}
  → Value V → Σ ∣ Δ ∣ [] ⊢ V ⦂ ∀ν A → Proxy V
canonical-∀ V-Λν (⊢Λν ⊢M) = c-Λν
canonical-∀ (V-cast⇒ v) (⊢up () ⊢V)
canonical-∀ (V-cast⇒ v) (⊢down () ⊢V)

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

data Progress (Σ : Store) (M : Term) : Set where
  done  : Value M → Progress Σ M
  blame : M ≡ ℧ → Progress Σ M
  step  : ∀ {Σ′ N} → Σ ▷ M —→ Σ′ ▷ N → Progress Σ M

progress-plug : ∀ {Σ M} F
  → (Value M → Progress Σ (plug F M))
  → Progress Σ M
  → Progress Σ (plug F M)
progress-plug F k (done v) = k v
progress-plug F k (blame refl) = step (ξ-℧ F)
progress-plug F k (step s) = step (ξ F s)

progress-cast : ∀ {Σ Δ d p V C}
  → Value V
  → Σ ∣ Δ ∣ [] ⊢ cast d p V ⦂ C
  → Progress Σ (cast d p V)
progress-cast v (⊢up ⊑★ ⊢V) = step (β-id at★ v)
progress-cast v (⊢up (⊑tag wfG p⊢) ⊢V) = step (β-tag-up v)
progress-cast v (⊢up (⊑‵ wfα) ⊢V) = step (β-id at‵ v)
progress-cast v (⊢up ⊑𝔹 ⊢V) = step (β-id at𝔹 v)
progress-cast v (⊢up (⊑⇒ p⊢ q⊢) ⊢V) = done (V-cast⇒ v)
progress-cast v (⊢up (⊑∀ p⊢) ⊢V) with canonical-∀ v ⊢V
progress-cast v (⊢up (⊑∀ p⊢) ⊢V) | c-Λν = step β-cast∀
progress-cast v (⊢down ⊑★ ⊢V) = step (β-id at★ v)
progress-cast v (⊢down (⊑tag {G = G} wfG p⊢) ⊢V) with canonical-★ v ⊢V
progress-cast v (⊢down (⊑tag {G = G} wfG p⊢) ⊢V) | c-inj {G = H} w
  with G ≟G H
progress-cast v (⊢down (⊑tag {G = G} wfG p⊢) ⊢V) | c-inj {G = H} w
  | yes refl = step (β-tag-down w)
progress-cast v (⊢down (⊑tag {G = G} wfG p⊢) ⊢V) | c-inj {G = H} w
  | no G≢H = step (β-tag-down-℧ w G≢H)
progress-cast v (⊢down (⊑‵ wfα) ⊢V) = step (β-id at‵ v)
progress-cast v (⊢down ⊑𝔹 ⊢V) = step (β-id at𝔹 v)
progress-cast v (⊢down (⊑⇒ p⊢ q⊢) ⊢V) = done (V-cast⇒ v)
progress-cast v (⊢down (⊑∀ p⊢) ⊢V) with canonical-∀ v ⊢V
progress-cast v (⊢down (⊑∀ p⊢) ⊢V) | c-Λν = step β-cast∀

progress : ∀ {Σ M A} → Σ ∣ [] ∣ [] ⊢ M ⦂ A → Progress Σ M
progress (⊢` ())
progress ⊢℧ = blame refl
progress ⊢true = done V-true
progress ⊢false = done V-false
progress (⊢if ⊢L ⊢M ⊢N) = progress-plug (if□ _ _) k (progress ⊢L)
  where
  k : Value _ → Progress _ (if _ _ _)
  k v with canonical-𝔹 v ⊢L
  k v | c-true = step β-if-true
  k v | c-false = step β-if-false
progress (⊢ƛ ⊢M) = done V-ƛ
progress (⊢· ⊢L ⊢M) = progress-plug (□· _) k (progress ⊢L)
  where
  k : Value _ → Progress _ (_ · _)
  k v = progress-plug (app□ _ v) k′ (progress ⊢M)
    where
    k′ : Value _ → Progress _ (_ · _)
    k′ w with canonical-⇒ v ⊢L
    k′ w | c-ƛ = step (β-ƛ w)
    k′ w | c-cast⇒ v′ = step (β-cast⇒ v′ w)
progress (⊢letv ⊢M ⊢N) =
  progress-plug (letv□ _) (λ v → step (β-letv v)) (progress ⊢M)
progress (⊢seal nt ⊢M) =
  progress-plug (seal□ _) (λ v → done (V-seal v)) (progress ⊢M)
progress (⊢unseal nt ⊢M) = progress-plug (unseal□ _) k (progress ⊢M)
  where
  k : Value _ → Progress _ (unseal _ _)
  k v with canonical-‵ v ⊢M
  k v | c-seal w = step (β-unseal w)
progress (⊢is {G = G} wfG ⊢M) = progress-plug (is□ G) k (progress ⊢M)
  where
  k : Value _ → Progress _ (is G _)
  k v with canonical-★ v ⊢M
  k v | c-inj {G = H} w with G ≟G H
  k v | c-inj {G = H} w | yes refl = step (β-is-yes w)
  k v | c-inj {G = H} w | no G≢H = step (β-is-no w G≢H)
progress (⊢inj wfG ⊢M) =
  progress-plug (inj□ _) (λ v → done (V-inj v)) (progress ⊢M)
progress (⊢up p⊢ ⊢M) =
  progress-plug (cast□ up _) (λ v → progress-cast v (⊢up p⊢ ⊢M))
                (progress ⊢M)
progress (⊢down p⊢ ⊢M) =
  progress-plug (cast□ down _) (λ v → progress-cast v (⊢down p⊢ ⊢M))
                (progress ⊢M)
progress (⊢Λν ⊢M) = done V-Λν
progress (⊢inst ⊢M wfB ⊢N) =
  progress-plug (inst□ _ _) k (progress ⊢M)
  where
  k : Value _ → Progress _ (inst _ _ _)
  k v with canonical-∀ v ⊢M
  k v | c-Λν = step β-inst
