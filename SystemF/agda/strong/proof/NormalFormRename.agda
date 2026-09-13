module strong.proof.NormalFormRename where

-- Strong System F v7 — renaming anchors preserves normal forms.
--
-- `⊢ν` demands `NF c`, so every rule that carries a boundary under new
-- anchors must re-establish normality of the renamed conversion.  It holds
-- because the only thing `fuse` inspects about an anchor is whether two of
-- them are EQUAL, and an injective renaming decides that the same way.
-- Structure — and hence `weight`, and hence the fuel — is untouched.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types using (Ty; Renameᵗ; extᵗ)
open import strong.RepresentationTypes using (Anchor; Renameᴿ; extᴿ)
open import strong.Conversion

Injᴿ : Renameᴿ → Set
Injᴿ ρ = ∀ α β → ρ α ≡ ρ β → α ≡ β

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

extᴿ-inj : ∀ {ρ} → Injᴿ ρ → Injᴿ (extᴿ ρ)
extᴿ-inj inj zero zero eq = refl
extᴿ-inj inj (suc α) (suc β) eq = cong suc (inj α β (suc-inj eq))

------------------------------------------------------------------------
-- What `fuse` does at the two anchor heads
------------------------------------------------------------------------

fuse-seal-unseal-same : ∀ α → fuse (seal α) (unseal α) ≡ just []
fuse-seal-unseal-same α with α ≟ α
fuse-seal-unseal-same α | yes _ = refl
fuse-seal-unseal-same α | no ne = ⊥-elim (ne refl)

fuse-unseal-seal-same : ∀ α → fuse (unseal α) (seal α) ≡ just []
fuse-unseal-seal-same α with α ≟ α
fuse-unseal-seal-same α | yes _ = refl
fuse-unseal-seal-same α | no ne = ⊥-elim (ne refl)

fuse-seal-unseal-diff : ∀ α β → ¬ (α ≡ β)
  → fuse (seal α) (unseal β) ≡ nothing
fuse-seal-unseal-diff α β ne with α ≟ β
fuse-seal-unseal-diff α β ne | yes p = ⊥-elim (ne p)
fuse-seal-unseal-diff α β ne | no _ = refl

fuse-unseal-seal-diff : ∀ α β → ¬ (α ≡ β)
  → fuse (unseal α) (seal β) ≡ nothing
fuse-unseal-seal-diff α β ne with α ≟ β
fuse-unseal-seal-diff α β ne | yes p = ⊥-elim (ne p)
fuse-unseal-seal-diff α β ne | no _ = refl

-- Reading the anchors back OUT of a failure to fuse.
seal-unseal-≢ : ∀ α β → fuse (seal α) (unseal β) ≡ nothing → ¬ (α ≡ β)
seal-unseal-≢ α .α eq refl
  with trans (sym (fuse-seal-unseal-same α)) eq
seal-unseal-≢ α .α eq refl | ()

unseal-seal-≢ : ∀ α β → fuse (unseal α) (seal β) ≡ nothing → ¬ (α ≡ β)
unseal-seal-≢ α .α eq refl
  with trans (sym (fuse-unseal-seal-same α)) eq
unseal-seal-≢ α .α eq refl | ()

------------------------------------------------------------------------
-- Failure to fuse survives renaming
------------------------------------------------------------------------

fuse-ren-nothing : ∀ {ρᵗ ρ} → Injᴿ ρ → ∀ h k → fuse h k ≡ nothing
  → fuse (renHead ρᵗ ρ h) (renHead ρᵗ ρ k) ≡ nothing
fuse-ren-nothing inj (seal α) (seal β) eq = refl
fuse-ren-nothing {ρ = ρ} inj (seal α) (unseal β) eq =
  fuse-seal-unseal-diff (ρ α) (ρ β)
    (λ e → seal-unseal-≢ α β eq (inj α β e))
fuse-ren-nothing inj (seal α) (c ↦ d) eq = refl
fuse-ren-nothing inj (seal α) (all c) eq = refl
fuse-ren-nothing {ρ = ρ} inj (unseal α) (seal β) eq =
  fuse-unseal-seal-diff (ρ α) (ρ β)
    (λ e → unseal-seal-≢ α β eq (inj α β e))
fuse-ren-nothing inj (unseal α) (unseal β) eq = refl
fuse-ren-nothing inj (unseal α) (c ↦ d) eq = refl
fuse-ren-nothing inj (unseal α) (all c) eq = refl
fuse-ren-nothing inj (c ↦ d) (seal β) eq = refl
fuse-ren-nothing inj (c ↦ d) (unseal β) eq = refl
-- The two structural heads ALWAYS fuse, so the hypothesis is absurd.
fuse-ren-nothing inj (c₁ ↦ d₁) (c₂ ↦ d₂) ()
fuse-ren-nothing inj (c ↦ d) (all e) eq = refl
fuse-ren-nothing inj (all c) (seal β) eq = refl
fuse-ren-nothing inj (all c) (unseal β) eq = refl
fuse-ren-nothing inj (all c) (d ↦ e) eq = refl
fuse-ren-nothing inj (all c) (all d) ()

------------------------------------------------------------------------
-- Normal forms
------------------------------------------------------------------------

mutual
  NFHead-ren : ∀ {ρᵗ ρ h} → Injᴿ ρ → NFHead h → NFHead (renHead ρᵗ ρ h)
  NFHead-ren inj nf-seal = nf-seal
  NFHead-ren inj nf-unseal = nf-unseal
  NFHead-ren inj (nf-fun a b) = nf-fun (NF-ren inj a) (NF-ren inj b)
  NFHead-ren inj (nf-all a) = nf-all (NF-ren (extᴿ-inj inj) a)

  irr-ren : ∀ {ρᵗ ρ h c} → Injᴿ ρ → IrreducibleAfter h c
    → IrreducibleAfter (renHead ρᵗ ρ h) (renConv ρᵗ ρ c)
  irr-ren inj irr-id = irr-id
  irr-ren {h = h} inj (irr-cons {k = k} eq) =
    irr-cons (fuse-ren-nothing inj h k eq)

  NF-ren : ∀ {ρᵗ ρ c} → Injᴿ ρ → NF c → NF (renConv ρᵗ ρ c)
  NF-ren inj nf-id = nf-id
  NF-ren inj (nf-cons nh nc irr) =
    nf-cons (NFHead-ren inj nh) (NF-ren inj nc) (irr-ren inj irr)
