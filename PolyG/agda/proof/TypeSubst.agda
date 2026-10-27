module proof.TypeSubst where

-- File Charter:
--   * Syntactic lemmas about substituting names for type variables
--     (substₙ, substᵗ, substG, substᵖ, substˢ, substᵀ): congruence,
--     fusion, identity on well-formed types, the shift/extension
--     commutation, and `(⇑ᵗ A) [ α ]ᵗ ≡ A`.
--   * Well-formedness (WfName, WfTy, WfGround) and the precision typing
--     judgment `n ⊢ p ⦂ A ⊑ B` are preserved by substitutions that map
--     the variables in scope to well-formed names.
--   * How `stack` interacts with term renaming, term substitution and
--     name substitution.
--   * Store lookups: extension, the seal `length Σ`, uniqueness.
--   * Consumed by proof/TypingSubst.agda and proof/Preservation.agda.

open import Data.List using (List; []; _∷_; map; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types
open import Terms
open import Typing using (Ctx; ⤊)

------------------------------------------------------------------------
-- Congruence
------------------------------------------------------------------------

infix 4 _≗ₙ_

_≗ₙ_ : NSubst → NSubst → Set
σ ≗ₙ τ = ∀ i → σ i ≡ τ i

extₙ-cong : ∀ {σ τ} → σ ≗ₙ τ → extₙ σ ≗ₙ extₙ τ
extₙ-cong eq zero = refl
extₙ-cong eq (suc i) = cong ⇑ₙ (eq i)

substₙ-cong : ∀ {σ τ} → σ ≗ₙ τ → ∀ α → substₙ σ α ≡ substₙ τ α
substₙ-cong eq (tvar i) = eq i
substₙ-cong eq (tseal s) = refl

substᵗ-cong : ∀ {σ τ} → σ ≗ₙ τ → ∀ A → substᵗ σ A ≡ substᵗ τ A
substᵗ-cong eq (‵ α) = cong ‵_ (substₙ-cong eq α)
substᵗ-cong eq 𝔹 = refl
substᵗ-cong eq ★ = refl
substᵗ-cong eq (A ⇒ B) = cong₂ _⇒_ (substᵗ-cong eq A) (substᵗ-cong eq B)
substᵗ-cong eq (∀ν A) = cong ∀ν (substᵗ-cong (extₙ-cong eq) A)

------------------------------------------------------------------------
-- Fusion: substᵗ τ ∘ substᵗ σ is substᵗ ρ when ρ agrees with σ ⨟ τ
------------------------------------------------------------------------

substₙ-⇑ₙ : ∀ τ α → substₙ (extₙ τ) (⇑ₙ α) ≡ ⇑ₙ (substₙ τ α)
substₙ-⇑ₙ τ (tvar i) = refl
substₙ-⇑ₙ τ (tseal s) = refl

extₙ-fuse : ∀ {σ τ ρ}
  → (∀ i → substₙ τ (σ i) ≡ ρ i)
  → ∀ i → substₙ (extₙ τ) (extₙ σ i) ≡ extₙ ρ i
extₙ-fuse {σ} {τ} eq zero = refl
extₙ-fuse {σ} {τ} eq (suc i) = trans (substₙ-⇑ₙ τ (σ i)) (cong ⇑ₙ (eq i))

substₙ-fuse : ∀ {σ τ ρ}
  → (∀ i → substₙ τ (σ i) ≡ ρ i)
  → ∀ α → substₙ τ (substₙ σ α) ≡ substₙ ρ α
substₙ-fuse eq (tvar i) = eq i
substₙ-fuse eq (tseal s) = refl

substᵗ-fuse : ∀ {σ τ ρ}
  → (∀ i → substₙ τ (σ i) ≡ ρ i)
  → ∀ A → substᵗ τ (substᵗ σ A) ≡ substᵗ ρ A
substᵗ-fuse eq (‵ α) = cong ‵_ (substₙ-fuse eq α)
substᵗ-fuse eq 𝔹 = refl
substᵗ-fuse eq ★ = refl
substᵗ-fuse eq (A ⇒ B) = cong₂ _⇒_ (substᵗ-fuse eq A) (substᵗ-fuse eq B)
substᵗ-fuse eq (∀ν A) = cong ∀ν (substᵗ-fuse (extₙ-fuse eq) A)

------------------------------------------------------------------------
-- Identity
------------------------------------------------------------------------

substᵗ-id : ∀ {σ} → σ ≗ₙ tvar → ∀ A → substᵗ σ A ≡ A
substᵗ-id {σ} eq A =
  trans (substᵗ-cong eq A) (substᵗ-tvar A)
  where
  ext-tvar : extₙ tvar ≗ₙ tvar
  ext-tvar zero = refl
  ext-tvar (suc i) = refl

  substᵗ-tvar : ∀ A → substᵗ tvar A ≡ A
  substᵗ-tvar (‵ tvar i) = refl
  substᵗ-tvar (‵ tseal s) = refl
  substᵗ-tvar 𝔹 = refl
  substᵗ-tvar ★ = refl
  substᵗ-tvar (A ⇒ B) = cong₂ _⇒_ (substᵗ-tvar A) (substᵗ-tvar B)
  substᵗ-tvar (∀ν A) =
    cong ∀ν (trans (substᵗ-cong ext-tvar A) (substᵗ-tvar A))

-- a well-formed type is fixed by a substitution that fixes its
-- variables
substᵗ-wf-id : ∀ {n σ A}
  → (∀ {i} → i < n → σ i ≡ tvar i)
  → WfTy n A
  → substᵗ σ A ≡ A
substᵗ-wf-id {σ = σ} eq (wf‵ {tvar i} i<n) = cong ‵_ (eq i<n)
substᵗ-wf-id eq (wf‵ {tseal s} tt) = refl
substᵗ-wf-id eq wf𝔹 = refl
substᵗ-wf-id eq wf★ = refl
substᵗ-wf-id eq (wf⇒ wfA wfB) =
  cong₂ _⇒_ (substᵗ-wf-id eq wfA) (substᵗ-wf-id eq wfB)
substᵗ-wf-id {σ = σ} eq (wf∀ wfA) = cong ∀ν (substᵗ-wf-id eq′ wfA)
  where
  eq′ : ∀ {i} → i < suc _ → extₙ σ i ≡ tvar i
  eq′ {zero} i<n = refl
  eq′ {suc i} (s≤s i<n) = cong ⇑ₙ (eq i<n)

-- closed types are fixed by every substitution
closed-subst : ∀ {σ A} → WfTy 0 A → substᵗ σ A ≡ A
closed-subst = substᵗ-wf-id (λ ())

------------------------------------------------------------------------
-- Shifting and single substitution
------------------------------------------------------------------------

-- instantiating a shifted type undoes the shift
⇑ᵗ-[]ᵗ : ∀ A α → (⇑ᵗ A) [ α ]ᵗ ≡ A
⇑ᵗ-[]ᵗ A α = trans (substᵗ-fuse {ρ = tvar} (λ i → refl) A)
                   (substᵗ-id (λ i → refl) A)

substᵗ-⇑ᵗ-ρ : ∀ σ i → substₙ ↑ₙ (σ i) ≡ substₙ (extₙ σ) (↑ₙ i)
substᵗ-⇑ᵗ-ρ σ i with σ i
substᵗ-⇑ᵗ-ρ σ i | tvar j = refl
substᵗ-⇑ᵗ-ρ σ i | tseal s = refl

-- extension commutes with shifting
ext-⇑ᵗ : ∀ σ A → substᵗ (extₙ σ) (⇑ᵗ A) ≡ ⇑ᵗ (substᵗ σ A)
ext-⇑ᵗ σ A =
  trans (substᵗ-fuse {ρ = λ i → ⇑ₙ (σ i)} (λ i → refl) A)
        (sym (substᵗ-fuse (λ i → sym (⇑ₙ-is-↑ (σ i))) A))
  where
  ⇑ₙ-is-↑ : ∀ α → ⇑ₙ α ≡ substₙ ↑ₙ α
  ⇑ₙ-is-↑ (tvar i) = refl
  ⇑ₙ-is-↑ (tseal s) = refl

-- moving a context under a binder commutes with substitution
map-ext-⤊ : ∀ σ (Γ : Ctx)
  → map (substᵗ (extₙ σ)) (⤊ Γ) ≡ ⤊ (map (substᵗ σ) Γ)
map-ext-⤊ σ [] = refl
map-ext-⤊ σ (A ∷ Γ) = cong₂ _∷_ (ext-⇑ᵗ σ A) (map-ext-⤊ σ Γ)

groundTy-subst : ∀ σ G → substᵗ σ (groundTy G) ≡ groundTy (substG σ G)
groundTy-subst σ (G‵ α) = refl
groundTy-subst σ G𝔹 = refl
groundTy-subst σ G⇒ = refl
groundTy-subst σ G∀ = refl

------------------------------------------------------------------------
-- Well-formedness under substitution
------------------------------------------------------------------------

WfName-⇑ₙ : ∀ {n α} → WfName n α → WfName (suc n) (⇑ₙ α)
WfName-⇑ₙ {α = tvar i} i<n = s≤s i<n
WfName-⇑ₙ {α = tseal s} tt = tt

WfName-ext : ∀ {n m σ}
  → (∀ {i} → i < n → WfName m (σ i))
  → ∀ {i} → i < suc n → WfName (suc m) (extₙ σ i)
WfName-ext wfσ {zero} i<n = s≤s z≤n
WfName-ext wfσ {suc i} (s≤s i<n) = WfName-⇑ₙ (wfσ i<n)

WfName-subst : ∀ {n m σ α}
  → (∀ {i} → i < n → WfName m (σ i))
  → WfName n α
  → WfName m (substₙ σ α)
WfName-subst {α = tvar i} wfσ i<n = wfσ i<n
WfName-subst {α = tseal s} wfσ tt = tt

WfTy-subst : ∀ {n m σ A}
  → (∀ {i} → i < n → WfName m (σ i))
  → WfTy n A
  → WfTy m (substᵗ σ A)
WfTy-subst wfσ (wf‵ wfα) = wf‵ (WfName-subst wfσ wfα)
WfTy-subst wfσ wf𝔹 = wf𝔹
WfTy-subst wfσ wf★ = wf★
WfTy-subst wfσ (wf⇒ wfA wfB) = wf⇒ (WfTy-subst wfσ wfA) (WfTy-subst wfσ wfB)
WfTy-subst wfσ (wf∀ wfA) = wf∀ (WfTy-subst (WfName-ext wfσ) wfA)

WfGround-subst : ∀ {n m σ G}
  → (∀ {i} → i < n → WfName m (σ i))
  → WfGround n G
  → WfGround m (substG σ G)
WfGround-subst wfσ (wfG‵ wfα) = wfG‵ (WfName-subst wfσ wfα)
WfGround-subst wfσ wfG𝔹 = wfG𝔹
WfGround-subst wfσ wfG⇒ = wfG⇒
WfGround-subst wfσ wfG∀ = wfG∀

⊑-subst : ∀ {n m σ p A B}
  → (∀ {i} → i < n → WfName m (σ i))
  → n ⊢ p ⦂ A ⊑ B
  → m ⊢ substᵖ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
⊑-subst wfσ ⊑★ = ⊑★
⊑-subst {σ = σ} wfσ (⊑tag {G = G} wfG p⊢) =
  ⊑tag (WfGround-subst wfσ wfG)
       (substEq (λ T → _ ⊢ _ ⦂ _ ⊑ T) (groundTy-subst σ G)
                (⊑-subst wfσ p⊢))
⊑-subst wfσ (⊑‵ wfα) = ⊑‵ (WfName-subst wfσ wfα)
⊑-subst wfσ ⊑𝔹 = ⊑𝔹
⊑-subst wfσ (⊑⇒ p⊢ q⊢) = ⊑⇒ (⊑-subst wfσ p⊢) (⊑-subst wfσ q⊢)
⊑-subst wfσ (⊑∀ p⊢) = ⊑∀ (⊑-subst (WfName-ext wfσ) p⊢)

------------------------------------------------------------------------
-- Stacks of casts
------------------------------------------------------------------------

stack-substᵀ : ∀ σ cs M
  → substᵀ σ (stack cs M) ≡ stack (substˢ σ cs) (substᵀ σ M)
stack-substᵀ σ [] M = refl
stack-substᵀ σ ((d , p) ∷ cs) M = cong (cast d (substᵖ σ p))
                                       (stack-substᵀ σ cs M)

stack-rename : ∀ ρ cs M → rename ρ (stack cs M) ≡ stack cs (rename ρ M)
stack-rename ρ [] M = refl
stack-rename ρ ((d , p) ∷ cs) M = cong (cast d p) (stack-rename ρ cs M)

stack-subst : ∀ σ cs M → subst σ (stack cs M) ≡ stack cs (subst σ M)
stack-subst σ [] M = refl
stack-subst σ ((d , p) ∷ cs) M = cong (cast d p) (stack-subst σ cs M)

------------------------------------------------------------------------
-- Store lookups
------------------------------------------------------------------------

∋ˢ-++ : ∀ {Σ s A} Θ → Σ ∋ˢ s ⦂ A → (Σ ++ Θ) ∋ˢ s ⦂ A
∋ˢ-++ Θ Zˢ = Zˢ
∋ˢ-++ Θ (Sˢ h) = Sˢ (∋ˢ-++ Θ h)

∋ˢ-length : ∀ Σ {B ℓ} → (Σ ++ ((B , ℓ) ∷ [])) ∋ˢ length Σ ⦂ B
∋ˢ-length [] = Zˢ
∋ˢ-length (e ∷ Σ) = Sˢ (∋ˢ-length Σ)

∋ˢ-unique : ∀ {Σ s A B} → Σ ∋ˢ s ⦂ A → Σ ∋ˢ s ⦂ B → A ≡ B
∋ˢ-unique Zˢ Zˢ = refl
∋ˢ-unique (Sˢ h) (Sˢ h′) = ∋ˢ-unique h h′

∋ˢ-< : ∀ {Σ s A} → Σ ∋ˢ s ⦂ A → s < length Σ
∋ˢ-< Zˢ = s≤s z≤n
∋ˢ-< (Sˢ h) = s≤s (∋ˢ-< h)
