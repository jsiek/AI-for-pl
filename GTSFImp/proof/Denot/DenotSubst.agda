module proof.Denot.DenotSubst where

-- File Charter:
--   * Term renaming and term substitution lemmas for the GTSFImp
--     denotation, ported from PolyG's `proof/DenotSubst`.  Each is an
--     equivalence (`≐ᴿ`, both inclusions).
--       - ⟦⟧-rename: ⟦ rename r M ⟧ θ ρ ≐ ⟦ M ⟧ θ ρ′ when ρ (r x) and
--         ρ′ x are equal sets;
--       - ⟦⟧-subst: ⟦ subst σ M ⟧ θ ρ ≐ ⟦ M ⟧ θ ρ′ when each ⟦ σ x ⟧ θ ρ m
--         is retᴿ (ρ′ x) m;
--       - ⟦⟧-[]: the instance for β.
--   * Under a `Λ`, a substitution is shifted (`liftˢ`, `⇑ᵗᵐ`); the
--     renaming lemma `shift-term` (proof/Denot/DenotRename) covers it.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (TyVar; ⇑ᵗ)
open import Conversion using (〖_,_↑_〗)
open import Data.Fin using () renaming (zero to fzero)
open import CastTerms
open import Denot.GraphModel
open import Denot.Denotation
open import proof.Denot.DenotProps
open import proof.Denot.DenotRename

infix 4 _≐_

_≐_ : 𝒱 → 𝒱 → Set
D ≐ E = D ⊆ E × E ⊆ D

≐-refl : ∀ {D} → D ≐ D
≐-refl = ⊆-refl , ⊆-refl

≐ᴿ-refl : ∀ {R} → R ≐ᴿ R
≐ᴿ-refl = ⊆ᴿ-refl , ⊆ᴿ-refl

≐ᴿ-sym : ∀ {R S} → R ≐ᴿ S → S ≐ᴿ R
≐ᴿ-sym (r , l) = l , r

≐ᴿ-trans : ∀ {R S T} → R ≐ᴿ S → S ≐ᴿ T → R ≐ᴿ T
≐ᴿ-trans (r₁ , l₁) (r₂ , l₂) = ⊆ᴿ-trans r₁ r₂ , ⊆ᴿ-trans l₂ l₁

ret-≐ : ∀ {D E n} → D ≐ E → retᴿ D n ≐ᴿ retᴿ E n
ret-≐ (r , l) = retᴿ-mono r , retᴿ-mono l

-- a bind whose continuations are related by monotone inclusions both ways
bind-≐ : ∀ {R R′ K K′} → R ≐ᴿ R′
  → (∀ {D D′} m → D ⊆ D′ → K D m ⊆ᴿ K′ D′ m)
  → (∀ {D D′} m → D ⊆ D′ → K′ D m ⊆ᴿ K D′ m)
  → (R ≫= K) ≐ᴿ (R′ ≫= K′)
bind-≐ = ≫=-≐

------------------------------------------------------------------------
-- Term renaming
------------------------------------------------------------------------

-- the environments agree through the renaming, in both directions
RenEnv : Rename → Env → Env → Set
RenEnv r ρ ρ′ = ∀ x → ρ (r x) ≐ ρ′ x

ext-RenEnv : ∀ {r ρ ρ′ D D′} → D ≐ D′ → RenEnv r ρ ρ′
  → RenEnv (ext r) (D • ρ) (D′ • ρ′)
ext-RenEnv D≐ h zero = D≐
ext-RenEnv D≐ h (suc x) = h x

-- one direction, by induction on the term
rename-dir : ∀ {Δ} (M : Term Δ) {θ ρ ρ′ n} (r : Rename)
  → (∀ x → ρ (r x) ⊆ ρ′ x)
  → ⟦ rename r M ⟧ θ ρ n ⊆ᴿ ⟦ M ⟧ θ ρ′ n
rename-dir (` x) r h = retᴿ-mono (h x)
rename-dir (ƛ M) {ρ = ρ} {ρ′} r h =
  retᴿ-mono (Λᶠ-mono (λ D m →
    rename-dir M {ρ = D • ρ} {ρ′ = D • ρ′} (ext r) h′))
  where
  h′ : ∀ {D} x → (D • ρ) (ext r x) ⊆ (D • ρ′) x
  h′ zero = ⊆-refl
  h′ (suc x) = h x
rename-dir (L · M) r h =
  ≫=-mono (rename-dir L r h) (λ n₁ F⊆ →
    ≫=-mono (rename-dir M r h) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
rename-dir (Λ M) r h = retᴿ-mono (Λᴾ-mono (λ σ → rename-dir M r h))
rename-dir (M ⦂∀ B [ A ]) {θ = θ} r h =
  ≫=-mono (rename-dir M r h) (λ n₁ F⊆ →
    ≫=-mono (◆-mono F⊆) (conv↑-mono 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ n₁ •ʳ θ)))
rename-dir ($ κ) r h = ⊆ᴿ-refl
rename-dir (L ⊕[ op ] M) r h =
  ≫=-mono (rename-dir L r h) (λ n₁ D⊆ →
    ≫=-mono (rename-dir M r h) (λ n₂ E⊆ → retᴿ-mono (δᴾ-mono D⊆ E⊆)))
rename-dir (M ⟨ c ⟩) {θ = θ} r h =
  ≫=-mono (rename-dir M r h) (cast-mono c θ)
rename-dir (M ↑ c) {θ = θ} r h =
  ≫=-mono (rename-dir M r h) (conv↑-mono c θ)
rename-dir (M ↓ c) {θ = θ} r h =
  ≫=-mono (rename-dir M r h) (conv↓-mono c θ)
rename-dir blame r h = ⊆ᴿ-refl

-- the other direction
rename-dir⁻ : ∀ {Δ} (M : Term Δ) {θ ρ ρ′ n} (r : Rename)
  → (∀ x → ρ′ x ⊆ ρ (r x))
  → ⟦ M ⟧ θ ρ′ n ⊆ᴿ ⟦ rename r M ⟧ θ ρ n
rename-dir⁻ (` x) r h = retᴿ-mono (h x)
rename-dir⁻ (ƛ M) {ρ = ρ} {ρ′} r h =
  retᴿ-mono (Λᶠ-mono (λ D m →
    rename-dir⁻ M {ρ = D • ρ} {ρ′ = D • ρ′} (ext r) h′))
  where
  h′ : ∀ {D} x → (D • ρ′) x ⊆ (D • ρ) (ext r x)
  h′ zero = ⊆-refl
  h′ (suc x) = h x
rename-dir⁻ (L · M) r h =
  ≫=-mono (rename-dir⁻ L r h) (λ n₁ F⊆ →
    ≫=-mono (rename-dir⁻ M r h) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
rename-dir⁻ (Λ M) r h = retᴿ-mono (Λᴾ-mono (λ σ → rename-dir⁻ M r h))
rename-dir⁻ (M ⦂∀ B [ A ]) {θ = θ} r h =
  ≫=-mono (rename-dir⁻ M r h) (λ n₁ F⊆ →
    ≫=-mono (◆-mono F⊆) (conv↑-mono 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ n₁ •ʳ θ)))
rename-dir⁻ ($ κ) r h = ⊆ᴿ-refl
rename-dir⁻ (L ⊕[ op ] M) r h =
  ≫=-mono (rename-dir⁻ L r h) (λ n₁ D⊆ →
    ≫=-mono (rename-dir⁻ M r h) (λ n₂ E⊆ → retᴿ-mono (δᴾ-mono D⊆ E⊆)))
rename-dir⁻ (M ⟨ c ⟩) {θ = θ} r h =
  ≫=-mono (rename-dir⁻ M r h) (cast-mono c θ)
rename-dir⁻ (M ↑ c) {θ = θ} r h =
  ≫=-mono (rename-dir⁻ M r h) (conv↑-mono c θ)
rename-dir⁻ (M ↓ c) {θ = θ} r h =
  ≫=-mono (rename-dir⁻ M r h) (conv↓-mono c θ)
rename-dir⁻ blame r h = ⊆ᴿ-refl

⟦⟧-rename : ∀ {Δ} (M : Term Δ) {θ ρ ρ′ n} (r : Rename)
  → RenEnv r ρ ρ′
  → ⟦ rename r M ⟧ θ ρ n ≐ᴿ ⟦ M ⟧ θ ρ′ n
⟦⟧-rename M r h =
  rename-dir M r (λ x → proj₁ (h x)) , rename-dir⁻ M r (λ x → proj₂ (h x))

------------------------------------------------------------------------
-- Term substitution
------------------------------------------------------------------------

-- each substituted term denotes the value of the environment
SubEnv : ∀ {Δ} → Subst Δ → REnv Δ → Env → Env → Set
SubEnv σ θ ρ ρ′ = ∀ x m → ⟦ σ x ⟧ θ ρ m ≐ᴿ retᴿ (ρ′ x) m

exts-SubEnv : ∀ {Δ} (σ : Subst Δ) {θ ρ ρ′ D D′} → D ≐ D′
  → SubEnv σ θ ρ ρ′ → SubEnv (exts σ) θ (D • ρ) (D′ • ρ′)
exts-SubEnv σ D≐ h zero m = ret-≐ D≐
exts-SubEnv σ {θ} {ρ} D≐ h (suc x) m =
  ≐ᴿ-trans (⟦⟧-rename (σ x) {ρ′ = ρ} suc (λ y → ≐-refl)) (h x m)

liftˢ-SubEnv : ∀ {Δ} (σ : Subst Δ) {θ ρ ρ′} (r : Rep)
  → SubEnv σ θ ρ ρ′ → SubEnv (liftˢ σ) (r •ʳ θ) ρ ρ′
liftˢ-SubEnv σ {θ} {ρ} r h x m =
  ≐ᴿ-trans (≐ᴿ-sym (shift-term (σ x) θ r ρ m)) (h x m)

⟦⟧-subst : ∀ {Δ} (M : Term Δ) {θ ρ ρ′ n} (σ : Subst Δ)
  → SubEnv σ θ ρ ρ′
  → ⟦ subst σ M ⟧ θ ρ n ≐ᴿ ⟦ M ⟧ θ ρ′ n
⟦⟧-subst (` x) {n = n} σ h = h x n
⟦⟧-subst (ƛ M) σ h =
  retᴿ-mono (Λᶠ-mono (λ D m →
    proj₁ (⟦⟧-subst M (exts σ) (exts-SubEnv σ ≐-refl h)))) ,
  retᴿ-mono (Λᶠ-mono (λ D m →
    proj₂ (⟦⟧-subst M (exts σ) (exts-SubEnv σ ≐-refl h))))
⟦⟧-subst (L · M) σ h =
  ≫=-≐ (⟦⟧-subst L σ h)
    (λ n₁ F⊆ → ≫=-mono (proj₁ (⟦⟧-subst M σ h)) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
    (λ n₁ F⊆ → ≫=-mono (proj₂ (⟦⟧-subst M σ h)) (λ n₂ E⊆ → ●-mono F⊆ E⊆))
⟦⟧-subst (Λ M) σ h =
  retᴿ-mono (Λᴾ-mono (λ s →
    proj₁ (⟦⟧-subst M (liftˢ σ) (liftˢ-SubEnv σ (sealʳ s) h)))) ,
  retᴿ-mono (Λᴾ-mono (λ s →
    proj₂ (⟦⟧-subst M (liftˢ σ) (liftˢ-SubEnv σ (sealʳ s) h))))
⟦⟧-subst (M ⦂∀ B [ A ]) {θ = θ} σ h =
  ≫=-≐ (⟦⟧-subst M σ h)
    (λ n₁ F⊆ → ≫=-mono (◆-mono F⊆)
                 (conv↑-mono 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ n₁ •ʳ θ)))
    (λ n₁ F⊆ → ≫=-mono (◆-mono F⊆)
                 (conv↑-mono 〖 fzero , ⇑ᵗ A ↑ B 〗 (sealʳ n₁ •ʳ θ)))
⟦⟧-subst ($ κ) σ h = ≐ᴿ-refl
⟦⟧-subst (L ⊕[ op ] M) σ h =
  ≫=-≐ (⟦⟧-subst L σ h)
    (λ n₁ D⊆ → ≫=-mono (proj₁ (⟦⟧-subst M σ h))
                 (λ n₂ E⊆ → retᴿ-mono (δᴾ-mono D⊆ E⊆)))
    (λ n₁ D⊆ → ≫=-mono (proj₂ (⟦⟧-subst M σ h))
                 (λ n₂ E⊆ → retᴿ-mono (δᴾ-mono D⊆ E⊆)))
⟦⟧-subst (M ⟨ c ⟩) {θ = θ} σ h =
  ≫=-≐ (⟦⟧-subst M σ h) (cast-mono c θ) (cast-mono c θ)
⟦⟧-subst (M ↑ c) {θ = θ} σ h =
  ≫=-≐ (⟦⟧-subst M σ h) (conv↑-mono c θ) (conv↑-mono c θ)
⟦⟧-subst (M ↓ c) {θ = θ} σ h =
  ≫=-≐ (⟦⟧-subst M σ h) (conv↓-mono c θ) (conv↓-mono c θ)
⟦⟧-subst blame σ h = ≐ᴿ-refl

-- substituting a single value whose denotation is retᴿ D at every
-- counter
⟦⟧-[] : ∀ {Δ} (N : Term Δ) {θ ρ D n} V
  → (∀ m → ⟦ V ⟧ θ ρ m ≐ᴿ retᴿ D m)
  → ⟦ N [ V ] ⟧ θ ρ n ≐ᴿ ⟦ N ⟧ θ (D • ρ) n
⟦⟧-[] N V hV = ⟦⟧-subst N (singleSub V) h
  where
  h : SubEnv (singleSub V) _ _ (_ • _)
  h zero m = hV m
  h (suc x) m = ≐ᴿ-refl
