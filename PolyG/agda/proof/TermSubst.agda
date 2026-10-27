module proof.TermSubst where

-- File Charter:
--   * Syntactic lemmas about the term-level operations of Terms.agda:
--       - names for type variables in grounds, precisions, stacks and
--         terms (substG, substᵖ, substˢ, substᵀ): congruence, fusion,
--         identity, and `(⇑ᵀ M) [ α ]ᵀ ≡ M`;
--       - term renaming and substitution: congruence, fusion in all four
--         combinations, identity, and commutation with substᵀ;
--       - the three substitution facts that reduction of a closed
--         instance of a term needs (subst-β, subst-⇑ˢ-open,
--         subst-exts-⇑ˢ-open).
--   * Consumed by proof/DenotAdequacy.agda.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Types
open import Terms
open import proof.TypeSubst
  using (_≗ₙ_; extₙ-cong; substₙ-cong; substᵗ-cong; substₙ-⇑ₙ; extₙ-fuse;
         substₙ-fuse; substᵗ-fuse; substᵗ-id)

------------------------------------------------------------------------
-- Congruence for functions of several arguments
------------------------------------------------------------------------

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′}
  → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

------------------------------------------------------------------------
-- Names in grounds, precisions and stacks
------------------------------------------------------------------------

substG-cong : ∀ {σ τ} → σ ≗ₙ τ → ∀ G → substG σ G ≡ substG τ G
substG-cong eq (G‵ α) = cong G‵ (substₙ-cong eq α)
substG-cong eq G𝔹 = refl
substG-cong eq G⇒ = refl
substG-cong eq G∀ = refl

substᵖ-cong : ∀ {σ τ} → σ ≗ₙ τ → ∀ p → substᵖ σ p ≡ substᵖ τ p
substᵖ-cong eq ★⊑ = refl
substᵖ-cong eq (tag G p) = cong₂ tag (substG-cong eq G) (substᵖ-cong eq p)
substᵖ-cong eq (‵⊑ α) = cong ‵⊑ (substₙ-cong eq α)
substᵖ-cong eq 𝔹⊑ = refl
substᵖ-cong eq (p ⇒⊑ q) = cong₂ _⇒⊑_ (substᵖ-cong eq p) (substᵖ-cong eq q)
substᵖ-cong eq (∀⊑ p) = cong ∀⊑ (substᵖ-cong (extₙ-cong eq) p)

substˢ-cong : ∀ {σ τ} → σ ≗ₙ τ → ∀ cs → substˢ σ cs ≡ substˢ τ cs
substˢ-cong eq [] = refl
substˢ-cong eq ((d , p) ∷ cs) =
  cong₂ (λ q cs′ → (d , q) ∷ cs′) (substᵖ-cong eq p) (substˢ-cong eq cs)

substG-fuse : ∀ {σ τ ρ}
  → (∀ i → substₙ τ (σ i) ≡ ρ i)
  → ∀ G → substG τ (substG σ G) ≡ substG ρ G
substG-fuse eq (G‵ α) = cong G‵ (substₙ-fuse eq α)
substG-fuse eq G𝔹 = refl
substG-fuse eq G⇒ = refl
substG-fuse eq G∀ = refl

substᵖ-fuse : ∀ {σ τ ρ}
  → (∀ i → substₙ τ (σ i) ≡ ρ i)
  → ∀ p → substᵖ τ (substᵖ σ p) ≡ substᵖ ρ p
substᵖ-fuse eq ★⊑ = refl
substᵖ-fuse eq (tag G p) = cong₂ tag (substG-fuse eq G) (substᵖ-fuse eq p)
substᵖ-fuse eq (‵⊑ α) = cong ‵⊑ (substₙ-fuse eq α)
substᵖ-fuse eq 𝔹⊑ = refl
substᵖ-fuse eq (p ⇒⊑ q) =
  cong₂ _⇒⊑_ (substᵖ-fuse eq p) (substᵖ-fuse eq q)
substᵖ-fuse eq (∀⊑ p) = cong ∀⊑ (substᵖ-fuse (extₙ-fuse eq) p)

substˢ-fuse : ∀ {σ τ ρ}
  → (∀ i → substₙ τ (σ i) ≡ ρ i)
  → ∀ cs → substˢ τ (substˢ σ cs) ≡ substˢ ρ cs
substˢ-fuse eq [] = refl
substˢ-fuse eq ((d , p) ∷ cs) =
  cong₂ (λ q cs′ → (d , q) ∷ cs′) (substᵖ-fuse eq p) (substˢ-fuse eq cs)

-- identity

extₙ-id : ∀ {σ} → σ ≗ₙ tvar → extₙ σ ≗ₙ tvar
extₙ-id eq zero = refl
extₙ-id eq (suc i) = cong ⇑ₙ (eq i)

substₙ-id : ∀ {σ} → σ ≗ₙ tvar → ∀ α → substₙ σ α ≡ α
substₙ-id eq (tvar i) = eq i
substₙ-id eq (tseal s) = refl

substG-id : ∀ {σ} → σ ≗ₙ tvar → ∀ G → substG σ G ≡ G
substG-id eq (G‵ α) = cong G‵ (substₙ-id eq α)
substG-id eq G𝔹 = refl
substG-id eq G⇒ = refl
substG-id eq G∀ = refl

substᵖ-id : ∀ {σ} → σ ≗ₙ tvar → ∀ p → substᵖ σ p ≡ p
substᵖ-id eq ★⊑ = refl
substᵖ-id eq (tag G p) = cong₂ tag (substG-id eq G) (substᵖ-id eq p)
substᵖ-id eq (‵⊑ α) = cong ‵⊑ (substₙ-id eq α)
substᵖ-id eq 𝔹⊑ = refl
substᵖ-id eq (p ⇒⊑ q) = cong₂ _⇒⊑_ (substᵖ-id eq p) (substᵖ-id eq q)
substᵖ-id eq (∀⊑ p) = cong ∀⊑ (substᵖ-id (extₙ-id eq) p)

substˢ-id : ∀ {σ} → σ ≗ₙ tvar → ∀ cs → substˢ σ cs ≡ cs
substˢ-id eq [] = refl
substˢ-id eq ((d , p) ∷ cs) =
  cong₂ (λ q cs′ → (d , q) ∷ cs′) (substᵖ-id eq p) (substˢ-id eq cs)

------------------------------------------------------------------------
-- Names in terms
------------------------------------------------------------------------

substᵀ-cong : ∀ {σ τ} → σ ≗ₙ τ → ∀ M → substᵀ σ M ≡ substᵀ τ M
substᵀ-cong eq (` x) = refl
substᵀ-cong eq ℧ = refl
substᵀ-cong eq true = refl
substᵀ-cong eq false = refl
substᵀ-cong eq (if L M N) =
  cong₃ if (substᵀ-cong eq L) (substᵀ-cong eq M) (substᵀ-cong eq N)
substᵀ-cong eq (ƛ A M) = cong₂ ƛ (substᵗ-cong eq A) (substᵀ-cong eq M)
substᵀ-cong eq (L · M) = cong₂ _·_ (substᵀ-cong eq L) (substᵀ-cong eq M)
substᵀ-cong eq (letv M N) =
  cong₂ letv (substᵀ-cong eq M) (substᵀ-cong eq N)
substᵀ-cong eq (seal α M) =
  cong₂ seal (substₙ-cong eq α) (substᵀ-cong eq M)
substᵀ-cong eq (unseal α M) =
  cong₂ unseal (substₙ-cong eq α) (substᵀ-cong eq M)
substᵀ-cong eq (is G M) = cong₂ is (substG-cong eq G) (substᵀ-cong eq M)
substᵀ-cong eq (inj G M) = cong₂ inj (substG-cong eq G) (substᵀ-cong eq M)
substᵀ-cong eq (cast d p M) =
  cong₂ (cast d) (substᵖ-cong eq p) (substᵀ-cong eq M)
substᵀ-cong eq (Λν cs M) =
  cong₂ Λν (substˢ-cong (extₙ-cong eq) cs)
           (substᵀ-cong (extₙ-cong eq) M)
substᵀ-cong eq (inst M B N) =
  cong₃ inst (substᵀ-cong eq M) (substᵗ-cong eq B)
             (substᵀ-cong (extₙ-cong eq) N)

substᵀ-fuse : ∀ {σ τ ρ}
  → (∀ i → substₙ τ (σ i) ≡ ρ i)
  → ∀ M → substᵀ τ (substᵀ σ M) ≡ substᵀ ρ M
substᵀ-fuse eq (` x) = refl
substᵀ-fuse eq ℧ = refl
substᵀ-fuse eq true = refl
substᵀ-fuse eq false = refl
substᵀ-fuse eq (if L M N) =
  cong₃ if (substᵀ-fuse eq L) (substᵀ-fuse eq M) (substᵀ-fuse eq N)
substᵀ-fuse eq (ƛ A M) = cong₂ ƛ (substᵗ-fuse eq A) (substᵀ-fuse eq M)
substᵀ-fuse eq (L · M) = cong₂ _·_ (substᵀ-fuse eq L) (substᵀ-fuse eq M)
substᵀ-fuse eq (letv M N) =
  cong₂ letv (substᵀ-fuse eq M) (substᵀ-fuse eq N)
substᵀ-fuse eq (seal α M) =
  cong₂ seal (substₙ-fuse eq α) (substᵀ-fuse eq M)
substᵀ-fuse eq (unseal α M) =
  cong₂ unseal (substₙ-fuse eq α) (substᵀ-fuse eq M)
substᵀ-fuse eq (is G M) = cong₂ is (substG-fuse eq G) (substᵀ-fuse eq M)
substᵀ-fuse eq (inj G M) =
  cong₂ inj (substG-fuse eq G) (substᵀ-fuse eq M)
substᵀ-fuse eq (cast d p M) =
  cong₂ (cast d) (substᵖ-fuse eq p) (substᵀ-fuse eq M)
substᵀ-fuse eq (Λν cs M) =
  cong₂ Λν (substˢ-fuse (extₙ-fuse eq) cs)
           (substᵀ-fuse (extₙ-fuse eq) M)
substᵀ-fuse eq (inst M B N) =
  cong₃ inst (substᵀ-fuse eq M) (substᵗ-fuse eq B)
             (substᵀ-fuse (extₙ-fuse eq) N)

substᵀ-id : ∀ {σ} → σ ≗ₙ tvar → ∀ M → substᵀ σ M ≡ M
substᵀ-id eq (` x) = refl
substᵀ-id eq ℧ = refl
substᵀ-id eq true = refl
substᵀ-id eq false = refl
substᵀ-id eq (if L M N) =
  cong₃ if (substᵀ-id eq L) (substᵀ-id eq M) (substᵀ-id eq N)
substᵀ-id eq (ƛ A M) = cong₂ ƛ (substᵗ-id eq A) (substᵀ-id eq M)
substᵀ-id eq (L · M) = cong₂ _·_ (substᵀ-id eq L) (substᵀ-id eq M)
substᵀ-id eq (letv M N) = cong₂ letv (substᵀ-id eq M) (substᵀ-id eq N)
substᵀ-id eq (seal α M) = cong₂ seal (substₙ-id eq α) (substᵀ-id eq M)
substᵀ-id eq (unseal α M) =
  cong₂ unseal (substₙ-id eq α) (substᵀ-id eq M)
substᵀ-id eq (is G M) = cong₂ is (substG-id eq G) (substᵀ-id eq M)
substᵀ-id eq (inj G M) = cong₂ inj (substG-id eq G) (substᵀ-id eq M)
substᵀ-id eq (cast d p M) =
  cong₂ (cast d) (substᵖ-id eq p) (substᵀ-id eq M)
substᵀ-id eq (Λν cs M) =
  cong₂ Λν (substˢ-id (extₙ-id eq) cs) (substᵀ-id (extₙ-id eq) M)
substᵀ-id eq (inst M B N) =
  cong₃ inst (substᵀ-id eq M) (substᵗ-id eq B) (substᵀ-id (extₙ-id eq) N)

-- instantiating a shifted term undoes the shift
⇑ᵀ-open : ∀ M α → (⇑ᵀ M) [ α ]ᵀ ≡ M
⇑ᵀ-open M α = trans (substᵀ-fuse {ρ = tvar} (λ i → refl) M)
                    (substᵀ-id (λ i → refl) M)

-- extension commutes with shifting
ext-⇑ᵀ : ∀ σ M → substᵀ (extₙ σ) (⇑ᵀ M) ≡ ⇑ᵀ (substᵀ σ M)
ext-⇑ᵀ σ M =
  trans (substᵀ-fuse {ρ = λ i → ⇑ₙ (σ i)} (λ i → refl) M)
        (sym (substᵀ-fuse (λ i → sym (⇑ₙ-is-↑ (σ i))) M))
  where
  ⇑ₙ-is-↑ : ∀ α → ⇑ₙ α ≡ substₙ ↑ₙ α
  ⇑ₙ-is-↑ (tvar i) = refl
  ⇑ₙ-is-↑ (tseal s) = refl

------------------------------------------------------------------------
-- Term renaming
------------------------------------------------------------------------

ext-cong : ∀ {r r′ : Rename}
  → (∀ x → r x ≡ r′ x) → ∀ x → ext r x ≡ ext r′ x
ext-cong eq zero = refl
ext-cong eq (suc x) = cong suc (eq x)

rename-cong : ∀ {r r′ : Rename} M
  → (∀ x → r x ≡ r′ x) → rename r M ≡ rename r′ M
rename-cong (` x) eq = cong `_ (eq x)
rename-cong ℧ eq = refl
rename-cong true eq = refl
rename-cong false eq = refl
rename-cong (if L M N) eq =
  cong₃ if (rename-cong L eq) (rename-cong M eq) (rename-cong N eq)
rename-cong (ƛ A M) eq = cong (ƛ A) (rename-cong M (ext-cong eq))
rename-cong (L · M) eq = cong₂ _·_ (rename-cong L eq) (rename-cong M eq)
rename-cong (letv M N) eq =
  cong₂ letv (rename-cong M eq) (rename-cong N (ext-cong eq))
rename-cong (seal α M) eq = cong (seal α) (rename-cong M eq)
rename-cong (unseal α M) eq = cong (unseal α) (rename-cong M eq)
rename-cong (is G M) eq = cong (is G) (rename-cong M eq)
rename-cong (inj G M) eq = cong (inj G) (rename-cong M eq)
rename-cong (cast d p M) eq = cong (cast d p) (rename-cong M eq)
rename-cong (Λν cs M) eq = cong (Λν cs) (rename-cong M eq)
rename-cong (inst M B N) eq =
  cong₂ (λ M′ N′ → inst M′ B N′)
    (rename-cong M eq) (rename-cong N (ext-cong eq))

rename-rename : ∀ (r r′ : Rename) M
  → rename r (rename r′ M) ≡ rename (λ x → r (r′ x)) M
rename-rename r r′ (` x) = refl
rename-rename r r′ ℧ = refl
rename-rename r r′ true = refl
rename-rename r r′ false = refl
rename-rename r r′ (if L M N) =
  cong₃ if (rename-rename r r′ L) (rename-rename r r′ M)
           (rename-rename r r′ N)
rename-rename r r′ (ƛ A M) =
  cong (ƛ A) (trans (rename-rename (ext r) (ext r′) M)
                    (rename-cong M ext-ext))
  where
  ext-ext : ∀ x → ext r (ext r′ x) ≡ ext (λ y → r (r′ y)) x
  ext-ext zero = refl
  ext-ext (suc x) = refl
rename-rename r r′ (L · M) =
  cong₂ _·_ (rename-rename r r′ L) (rename-rename r r′ M)
rename-rename r r′ (letv M N) =
  cong₂ letv (rename-rename r r′ M)
    (trans (rename-rename (ext r) (ext r′) N) (rename-cong N ext-ext))
  where
  ext-ext : ∀ x → ext r (ext r′ x) ≡ ext (λ y → r (r′ y)) x
  ext-ext zero = refl
  ext-ext (suc x) = refl
rename-rename r r′ (seal α M) = cong (seal α) (rename-rename r r′ M)
rename-rename r r′ (unseal α M) = cong (unseal α) (rename-rename r r′ M)
rename-rename r r′ (is G M) = cong (is G) (rename-rename r r′ M)
rename-rename r r′ (inj G M) = cong (inj G) (rename-rename r r′ M)
rename-rename r r′ (cast d p M) = cong (cast d p) (rename-rename r r′ M)
rename-rename r r′ (Λν cs M) = cong (Λν cs) (rename-rename r r′ M)
rename-rename r r′ (inst M B N) =
  cong₂ (λ M′ N′ → inst M′ B N′) (rename-rename r r′ M)
    (trans (rename-rename (ext r) (ext r′) N) (rename-cong N ext-ext))
  where
  ext-ext : ∀ x → ext r (ext r′ x) ≡ ext (λ y → r (r′ y)) x
  ext-ext zero = refl
  ext-ext (suc x) = refl

-- renaming term variables commutes with substituting type variables
rename-substᵀ : ∀ (r : Rename) τ M
  → rename r (substᵀ τ M) ≡ substᵀ τ (rename r M)
rename-substᵀ r τ (` x) = refl
rename-substᵀ r τ ℧ = refl
rename-substᵀ r τ true = refl
rename-substᵀ r τ false = refl
rename-substᵀ r τ (if L M N) =
  cong₃ if (rename-substᵀ r τ L) (rename-substᵀ r τ M)
           (rename-substᵀ r τ N)
rename-substᵀ r τ (ƛ A M) =
  cong (ƛ (substᵗ τ A)) (rename-substᵀ (ext r) τ M)
rename-substᵀ r τ (L · M) =
  cong₂ _·_ (rename-substᵀ r τ L) (rename-substᵀ r τ M)
rename-substᵀ r τ (letv M N) =
  cong₂ letv (rename-substᵀ r τ M) (rename-substᵀ (ext r) τ N)
rename-substᵀ r τ (seal α M) =
  cong (seal (substₙ τ α)) (rename-substᵀ r τ M)
rename-substᵀ r τ (unseal α M) =
  cong (unseal (substₙ τ α)) (rename-substᵀ r τ M)
rename-substᵀ r τ (is G M) = cong (is (substG τ G)) (rename-substᵀ r τ M)
rename-substᵀ r τ (inj G M) =
  cong (inj (substG τ G)) (rename-substᵀ r τ M)
rename-substᵀ r τ (cast d p M) =
  cong (cast d (substᵖ τ p)) (rename-substᵀ r τ M)
rename-substᵀ r τ (Λν cs M) =
  cong (Λν (substˢ (extₙ τ) cs)) (rename-substᵀ r (extₙ τ) M)
rename-substᵀ r τ (inst M B N) =
  cong₂ (λ M′ N′ → inst M′ (substᵗ τ B) N′)
    (rename-substᵀ r τ M) (rename-substᵀ (ext r) (extₙ τ) N)

------------------------------------------------------------------------
-- Term substitution
------------------------------------------------------------------------

exts-cong : ∀ {σ τ : Subst}
  → (∀ x → σ x ≡ τ x) → ∀ x → exts σ x ≡ exts τ x
exts-cong eq zero = refl
exts-cong eq (suc x) = cong (rename suc) (eq x)

⇑ˢ-cong : ∀ {σ τ : Subst}
  → (∀ x → σ x ≡ τ x) → ∀ x → ⇑ˢ σ x ≡ ⇑ˢ τ x
⇑ˢ-cong eq x = cong ⇑ᵀ (eq x)

subst-cong : ∀ {σ τ : Subst} M
  → (∀ x → σ x ≡ τ x) → subst σ M ≡ subst τ M
subst-cong (` x) eq = eq x
subst-cong ℧ eq = refl
subst-cong true eq = refl
subst-cong false eq = refl
subst-cong (if L M N) eq =
  cong₃ if (subst-cong L eq) (subst-cong M eq) (subst-cong N eq)
subst-cong (ƛ A M) eq = cong (ƛ A) (subst-cong M (exts-cong eq))
subst-cong (L · M) eq = cong₂ _·_ (subst-cong L eq) (subst-cong M eq)
subst-cong (letv M N) eq =
  cong₂ letv (subst-cong M eq) (subst-cong N (exts-cong eq))
subst-cong (seal α M) eq = cong (seal α) (subst-cong M eq)
subst-cong (unseal α M) eq = cong (unseal α) (subst-cong M eq)
subst-cong (is G M) eq = cong (is G) (subst-cong M eq)
subst-cong (inj G M) eq = cong (inj G) (subst-cong M eq)
subst-cong (cast d p M) eq = cong (cast d p) (subst-cong M eq)
subst-cong (Λν cs M) eq = cong (Λν cs) (subst-cong M (⇑ˢ-cong eq))
subst-cong (inst M B N) eq =
  cong₂ (λ M′ N′ → inst M′ B N′)
    (subst-cong M eq) (subst-cong N (exts-cong (⇑ˢ-cong eq)))

subst-rename : ∀ (τ : Subst) (r : Rename) M
  → subst τ (rename r M) ≡ subst (λ x → τ (r x)) M
subst-rename τ r (` x) = refl
subst-rename τ r ℧ = refl
subst-rename τ r true = refl
subst-rename τ r false = refl
subst-rename τ r (if L M N) =
  cong₃ if (subst-rename τ r L) (subst-rename τ r M) (subst-rename τ r N)
subst-rename τ r (ƛ A M) =
  cong (ƛ A) (trans (subst-rename (exts τ) (ext r) M)
                    (subst-cong M exts-ext))
  where
  exts-ext : ∀ x → exts τ (ext r x) ≡ exts (λ y → τ (r y)) x
  exts-ext zero = refl
  exts-ext (suc x) = refl
subst-rename τ r (L · M) =
  cong₂ _·_ (subst-rename τ r L) (subst-rename τ r M)
subst-rename τ r (letv M N) =
  cong₂ letv (subst-rename τ r M)
    (trans (subst-rename (exts τ) (ext r) N) (subst-cong N exts-ext))
  where
  exts-ext : ∀ x → exts τ (ext r x) ≡ exts (λ y → τ (r y)) x
  exts-ext zero = refl
  exts-ext (suc x) = refl
subst-rename τ r (seal α M) = cong (seal α) (subst-rename τ r M)
subst-rename τ r (unseal α M) = cong (unseal α) (subst-rename τ r M)
subst-rename τ r (is G M) = cong (is G) (subst-rename τ r M)
subst-rename τ r (inj G M) = cong (inj G) (subst-rename τ r M)
subst-rename τ r (cast d p M) = cong (cast d p) (subst-rename τ r M)
subst-rename τ r (Λν cs M) = cong (Λν cs) (subst-rename (⇑ˢ τ) r M)
subst-rename τ r (inst M B N) =
  cong₂ (λ M′ N′ → inst M′ B N′) (subst-rename τ r M)
    (trans (subst-rename (exts (⇑ˢ τ)) (ext r) N)
           (subst-cong N exts-ext))
  where
  exts-ext : ∀ x
    → exts (⇑ˢ τ) (ext r x) ≡ exts (⇑ˢ (λ y → τ (r y))) x
  exts-ext zero = refl
  exts-ext (suc x) = refl

rename-subst : ∀ (r : Rename) (τ : Subst) M
  → rename r (subst τ M) ≡ subst (λ x → rename r (τ x)) M
rename-subst r τ (` x) = refl
rename-subst r τ ℧ = refl
rename-subst r τ true = refl
rename-subst r τ false = refl
rename-subst r τ (if L M N) =
  cong₃ if (rename-subst r τ L) (rename-subst r τ M) (rename-subst r τ N)
rename-subst r τ (ƛ A M) =
  cong (ƛ A) (trans (rename-subst (ext r) (exts τ) M)
                    (subst-cong M (ext-exts r τ)))
  where
  ext-exts : ∀ r τ x
    → rename (ext r) (exts τ x) ≡ exts (λ y → rename r (τ y)) x
  ext-exts r τ zero = refl
  ext-exts r τ (suc x) =
    trans (rename-rename (ext r) suc (τ x))
          (sym (rename-rename suc r (τ x)))
rename-subst r τ (L · M) =
  cong₂ _·_ (rename-subst r τ L) (rename-subst r τ M)
rename-subst r τ (letv M N) =
  cong₂ letv (rename-subst r τ M)
    (trans (rename-subst (ext r) (exts τ) N)
           (subst-cong N (ext-exts r τ)))
  where
  ext-exts : ∀ r τ x
    → rename (ext r) (exts τ x) ≡ exts (λ y → rename r (τ y)) x
  ext-exts r τ zero = refl
  ext-exts r τ (suc x) =
    trans (rename-rename (ext r) suc (τ x))
          (sym (rename-rename suc r (τ x)))
rename-subst r τ (seal α M) = cong (seal α) (rename-subst r τ M)
rename-subst r τ (unseal α M) = cong (unseal α) (rename-subst r τ M)
rename-subst r τ (is G M) = cong (is G) (rename-subst r τ M)
rename-subst r τ (inj G M) = cong (inj G) (rename-subst r τ M)
rename-subst r τ (cast d p M) = cong (cast d p) (rename-subst r τ M)
rename-subst r τ (Λν cs M) =
  cong (Λν cs) (trans (rename-subst r (⇑ˢ τ) M)
                      (subst-cong M (λ x → rename-substᵀ r ↑ₙ (τ x))))
rename-subst r τ (inst M B N) =
  cong₂ (λ M′ N′ → inst M′ B N′) (rename-subst r τ M)
    (trans (rename-subst (ext r) (exts (⇑ˢ τ)) N) (subst-cong N eq))
  where
  eq : ∀ x → rename (ext r) (exts (⇑ˢ τ) x)
           ≡ exts (⇑ˢ (λ y → rename r (τ y))) x
  eq zero = refl
  eq (suc x) =
    trans (rename-rename (ext r) suc (⇑ᵀ (τ x)))
      (trans (sym (rename-rename suc r (⇑ᵀ (τ x))))
             (cong (rename suc) (rename-substᵀ r ↑ₙ (τ x))))

-- substituting type variables commutes with substituting term variables
substᵀ-subst : ∀ ρ (σ : Subst) M
  → substᵀ ρ (subst σ M) ≡ subst (λ x → substᵀ ρ (σ x)) (substᵀ ρ M)
substᵀ-subst ρ σ (` x) = refl
substᵀ-subst ρ σ ℧ = refl
substᵀ-subst ρ σ true = refl
substᵀ-subst ρ σ false = refl
substᵀ-subst ρ σ (if L M N) =
  cong₃ if (substᵀ-subst ρ σ L) (substᵀ-subst ρ σ M)
           (substᵀ-subst ρ σ N)
substᵀ-subst ρ σ (ƛ A M) =
  cong (ƛ (substᵗ ρ A))
    (trans (substᵀ-subst ρ (exts σ) M)
           (subst-cong (substᵀ ρ M) (exts-substᵀ ρ σ)))
  where
  exts-substᵀ : ∀ ρ σ x
    → substᵀ ρ (exts σ x) ≡ exts (λ y → substᵀ ρ (σ y)) x
  exts-substᵀ ρ σ zero = refl
  exts-substᵀ ρ σ (suc x) = sym (rename-substᵀ suc ρ (σ x))
substᵀ-subst ρ σ (L · M) =
  cong₂ _·_ (substᵀ-subst ρ σ L) (substᵀ-subst ρ σ M)
substᵀ-subst ρ σ (letv M N) =
  cong₂ letv (substᵀ-subst ρ σ M)
    (trans (substᵀ-subst ρ (exts σ) N)
           (subst-cong (substᵀ ρ N) (exts-substᵀ ρ σ)))
  where
  exts-substᵀ : ∀ ρ σ x
    → substᵀ ρ (exts σ x) ≡ exts (λ y → substᵀ ρ (σ y)) x
  exts-substᵀ ρ σ zero = refl
  exts-substᵀ ρ σ (suc x) = sym (rename-substᵀ suc ρ (σ x))
substᵀ-subst ρ σ (seal α M) =
  cong (seal (substₙ ρ α)) (substᵀ-subst ρ σ M)
substᵀ-subst ρ σ (unseal α M) =
  cong (unseal (substₙ ρ α)) (substᵀ-subst ρ σ M)
substᵀ-subst ρ σ (is G M) = cong (is (substG ρ G)) (substᵀ-subst ρ σ M)
substᵀ-subst ρ σ (inj G M) =
  cong (inj (substG ρ G)) (substᵀ-subst ρ σ M)
substᵀ-subst ρ σ (cast d p M) =
  cong (cast d (substᵖ ρ p)) (substᵀ-subst ρ σ M)
substᵀ-subst ρ σ (Λν cs M) =
  cong (Λν (substˢ (extₙ ρ) cs))
    (trans (substᵀ-subst (extₙ ρ) (⇑ˢ σ) M)
           (subst-cong (substᵀ (extₙ ρ) M) (λ x → ext-⇑ᵀ ρ (σ x))))
substᵀ-subst ρ σ (inst M B N) =
  cong₂ (λ M′ N′ → inst M′ (substᵗ ρ B) N′)
    (substᵀ-subst ρ σ M)
    (trans (substᵀ-subst (extₙ ρ) (exts (⇑ˢ σ)) N)
           (subst-cong (substᵀ (extₙ ρ) N) eq))
  where
  eq : ∀ x → substᵀ (extₙ ρ) (exts (⇑ˢ σ) x)
           ≡ exts (⇑ˢ (λ y → substᵀ ρ (σ y))) x
  eq zero = refl
  eq (suc x) =
    trans (sym (rename-substᵀ suc (extₙ ρ) (⇑ᵀ (σ x))))
          (cong (rename suc) (ext-⇑ᵀ ρ (σ x)))

⇑ᵀ-subst : ∀ (σ : Subst) M → ⇑ᵀ (subst σ M) ≡ subst (⇑ˢ σ) (⇑ᵀ M)
⇑ᵀ-subst σ M = substᵀ-subst ↑ₙ σ M

subst-subst : ∀ (τ σ : Subst) M
  → subst τ (subst σ M) ≡ subst (λ x → subst τ (σ x)) M
subst-subst τ σ (` x) = refl
subst-subst τ σ ℧ = refl
subst-subst τ σ true = refl
subst-subst τ σ false = refl
subst-subst τ σ (if L M N) =
  cong₃ if (subst-subst τ σ L) (subst-subst τ σ M) (subst-subst τ σ N)
subst-subst τ σ (ƛ A M) =
  cong (ƛ A) (trans (subst-subst (exts τ) (exts σ) M)
                    (subst-cong M (exts-exts τ σ)))
  where
  exts-exts : ∀ τ σ x
    → subst (exts τ) (exts σ x) ≡ exts (λ y → subst τ (σ y)) x
  exts-exts τ σ zero = refl
  exts-exts τ σ (suc x) =
    trans (subst-rename (exts τ) suc (σ x))
          (sym (rename-subst suc τ (σ x)))
subst-subst τ σ (L · M) =
  cong₂ _·_ (subst-subst τ σ L) (subst-subst τ σ M)
subst-subst τ σ (letv M N) =
  cong₂ letv (subst-subst τ σ M)
    (trans (subst-subst (exts τ) (exts σ) N)
           (subst-cong N (exts-exts τ σ)))
  where
  exts-exts : ∀ τ σ x
    → subst (exts τ) (exts σ x) ≡ exts (λ y → subst τ (σ y)) x
  exts-exts τ σ zero = refl
  exts-exts τ σ (suc x) =
    trans (subst-rename (exts τ) suc (σ x))
          (sym (rename-subst suc τ (σ x)))
subst-subst τ σ (seal α M) = cong (seal α) (subst-subst τ σ M)
subst-subst τ σ (unseal α M) = cong (unseal α) (subst-subst τ σ M)
subst-subst τ σ (is G M) = cong (is G) (subst-subst τ σ M)
subst-subst τ σ (inj G M) = cong (inj G) (subst-subst τ σ M)
subst-subst τ σ (cast d p M) = cong (cast d p) (subst-subst τ σ M)
subst-subst τ σ (Λν cs M) =
  cong (Λν cs) (trans (subst-subst (⇑ˢ τ) (⇑ˢ σ) M)
                      (subst-cong M (λ x → sym (⇑ᵀ-subst τ (σ x)))))
subst-subst τ σ (inst M B N) =
  cong₂ (λ M′ N′ → inst M′ B N′) (subst-subst τ σ M)
    (trans (subst-subst (exts (⇑ˢ τ)) (exts (⇑ˢ σ)) N)
           (subst-cong N eq))
  where
  eq : ∀ x → subst (exts (⇑ˢ τ)) (exts (⇑ˢ σ) x)
           ≡ exts (⇑ˢ (λ y → subst τ (σ y))) x
  eq zero = refl
  eq (suc x) =
    trans (subst-rename (exts (⇑ˢ τ)) suc (⇑ᵀ (σ x)))
      (trans (sym (rename-subst suc (⇑ˢ τ) (⇑ᵀ (σ x))))
             (cong (rename suc) (sym (⇑ᵀ-subst τ (σ x)))))

exts-id : ∀ x → exts `_ x ≡ ` x
exts-id zero = refl
exts-id (suc x) = refl

subst-id : ∀ M → subst `_ M ≡ M
subst-id (` x) = refl
subst-id ℧ = refl
subst-id true = refl
subst-id false = refl
subst-id (if L M N) = cong₃ if (subst-id L) (subst-id M) (subst-id N)
subst-id (ƛ A M) =
  cong (ƛ A) (trans (subst-cong M exts-id) (subst-id M))
subst-id (L · M) = cong₂ _·_ (subst-id L) (subst-id M)
subst-id (letv M N) =
  cong₂ letv (subst-id M) (trans (subst-cong N exts-id) (subst-id N))
subst-id (seal α M) = cong (seal α) (subst-id M)
subst-id (unseal α M) = cong (unseal α) (subst-id M)
subst-id (is G M) = cong (is G) (subst-id M)
subst-id (inj G M) = cong (inj G) (subst-id M)
subst-id (cast d p M) = cong (cast d p) (subst-id M)
subst-id (Λν cs M) = cong (Λν cs) (subst-id M)
subst-id (inst M B N) =
  cong₂ (λ M′ N′ → inst M′ B N′) (subst-id M)
    (trans (subst-cong N exts-id) (subst-id N))

------------------------------------------------------------------------
-- Substitution facts used by reduction of closed instances
------------------------------------------------------------------------

infixr 5 _•ˢ_

_•ˢ_ : Term → Subst → Subst
(W •ˢ σ) zero = W
(W •ˢ σ) (suc x) = σ x

subst-β : ∀ (σ : Subst) W N → (subst (exts σ) N) [ W ] ≡ subst (W •ˢ σ) N
subst-β σ W N =
  trans (subst-subst (single W) (exts σ) N) (subst-cong N single-exts)
  where
  single-exts : ∀ x → subst (single W) (exts σ x) ≡ (W •ˢ σ) x
  single-exts zero = refl
  single-exts (suc x) =
    trans (subst-rename (single W) suc (σ x)) (subst-id (σ x))

subst-⇑ˢ-open : ∀ (σ : Subst) M α
  → (subst (⇑ˢ σ) M) [ α ]ᵀ ≡ subst σ (M [ α ]ᵀ)
subst-⇑ˢ-open σ M α =
  trans (substᵀ-subst (singleₙ α) (⇑ˢ σ) M)
        (subst-cong (M [ α ]ᵀ) (λ x → ⇑ᵀ-open (σ x) α))

subst-exts-⇑ˢ-open : ∀ (σ : Subst) N α
  → (subst (exts (⇑ˢ σ)) N) [ α ]ᵀ ≡ subst (exts σ) (N [ α ]ᵀ)
subst-exts-⇑ˢ-open σ N α =
  trans (substᵀ-subst (singleₙ α) (exts (⇑ˢ σ)) N)
        (subst-cong (N [ α ]ᵀ) eq)
  where
  eq : ∀ x → substᵀ (singleₙ α) (exts (⇑ˢ σ) x) ≡ exts σ x
  eq zero = refl
  eq (suc x) =
    trans (sym (rename-substᵀ suc (singleₙ α) (⇑ᵀ (σ x))))
          (cong (rename suc) (⇑ᵀ-open (σ x) α))
