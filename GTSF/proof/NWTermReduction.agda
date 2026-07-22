module proof.NWTermReduction where

-- File Charter:
--   * Defines the syntactic invariant that every coercion occurrence in a Nu
--     term is a narrowing or a widening.
--   * Proves that the invariant is preserved by pure and store-change
--     reduction.
--   * Depends on the positive strict NarrowWiden grammar for decomposition of
--     sequence, function, quantifier, gen, and inst coercions.

open import Data.Nat using (zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden

NWCoercion : Coercion → Set
NWCoercion c = Narrowing c ⊎ Widening c

data NWTerm : Term → Set where
  nw-` : ∀ {x} →
    NWTerm (` x)

  nw-ƛ : ∀ {M} →
    NWTerm M →
    NWTerm (ƛ M)

  nw-· : ∀ {L M} →
    NWTerm L →
    NWTerm M →
    NWTerm (L · M)

  nw-Λ : ∀ {M} →
    NWTerm M →
    NWTerm (Λ M)

  nw-• : ∀ {M} →
    NWTerm M →
    NWTerm (M •)

  nw-ν : ∀ {A M c} →
    NWTerm M →
    NWCoercion c →
    NWTerm (ν A M c)

  nw-$ : ∀ {κ} →
    NWTerm ($ κ)

  nw-⊕ : ∀ {L op M} →
    NWTerm L →
    NWTerm M →
    NWTerm (L ⊕[ op ] M)

  nw-⟨⟩ : ∀ {M c} →
    NWTerm M →
    NWCoercion c →
    NWTerm (M ⟨ c ⟩)

  nw-blame :
    NWTerm blame

renameᶜ-preserves-NWCoercion :
  ∀ ρ {c} →
  NWCoercion c →
  NWCoercion (renameᶜ ρ c)
renameᶜ-preserves-NWCoercion ρ (inj₁ cⁿ) = inj₁ (renameⁿ ρ cⁿ)
renameᶜ-preserves-NWCoercion ρ (inj₂ cʷ) = inj₂ (renameʷ ρ cʷ)

⇑ᶜ-preserves-NWCoercion :
  ∀ {c} →
  NWCoercion c →
  NWCoercion (⇑ᶜ c)
⇑ᶜ-preserves-NWCoercion = renameᶜ-preserves-NWCoercion suc

renameᵗᵐ-preserves-NWTerm :
  ∀ ρ {M} →
  NWTerm M →
  NWTerm (renameᵗᵐ ρ M)
renameᵗᵐ-preserves-NWTerm ρ nw-` = nw-`
renameᵗᵐ-preserves-NWTerm ρ (nw-ƛ nwM) =
  nw-ƛ (renameᵗᵐ-preserves-NWTerm ρ nwM)
renameᵗᵐ-preserves-NWTerm ρ (nw-· nwL nwM) =
  nw-· (renameᵗᵐ-preserves-NWTerm ρ nwL)
       (renameᵗᵐ-preserves-NWTerm ρ nwM)
renameᵗᵐ-preserves-NWTerm ρ (nw-Λ nwM) =
  nw-Λ (renameᵗᵐ-preserves-NWTerm (extᵗ ρ) nwM)
renameᵗᵐ-preserves-NWTerm ρ (nw-• nwM) =
  nw-• (renameᵗᵐ-preserves-NWTerm ρ nwM)
renameᵗᵐ-preserves-NWTerm ρ (nw-ν nwM nwc) =
  nw-ν
    (renameᵗᵐ-preserves-NWTerm ρ nwM)
    (renameᶜ-preserves-NWCoercion (extᵗ ρ) nwc)
renameᵗᵐ-preserves-NWTerm ρ nw-$ = nw-$
renameᵗᵐ-preserves-NWTerm ρ (nw-⊕ nwL nwM) =
  nw-⊕ (renameᵗᵐ-preserves-NWTerm ρ nwL)
       (renameᵗᵐ-preserves-NWTerm ρ nwM)
renameᵗᵐ-preserves-NWTerm ρ (nw-⟨⟩ nwM nwc) =
  nw-⟨⟩
    (renameᵗᵐ-preserves-NWTerm ρ nwM)
    (renameᶜ-preserves-NWCoercion ρ nwc)
renameᵗᵐ-preserves-NWTerm ρ nw-blame = nw-blame

⇑ᵗᵐ-preserves-NWTerm :
  ∀ {M} →
  NWTerm M →
  NWTerm (⇑ᵗᵐ M)
⇑ᵗᵐ-preserves-NWTerm = renameᵗᵐ-preserves-NWTerm suc

renameˣᵐ-preserves-NWTerm :
  ∀ ρ {M} →
  NWTerm M →
  NWTerm (renameˣᵐ ρ M)
renameˣᵐ-preserves-NWTerm ρ nw-` = nw-`
renameˣᵐ-preserves-NWTerm ρ (nw-ƛ nwM) =
  nw-ƛ (renameˣᵐ-preserves-NWTerm (extʳ ρ) nwM)
renameˣᵐ-preserves-NWTerm ρ (nw-· nwL nwM) =
  nw-· (renameˣᵐ-preserves-NWTerm ρ nwL)
       (renameˣᵐ-preserves-NWTerm ρ nwM)
renameˣᵐ-preserves-NWTerm ρ (nw-Λ nwM) =
  nw-Λ (renameˣᵐ-preserves-NWTerm ρ nwM)
renameˣᵐ-preserves-NWTerm ρ (nw-• nwM) =
  nw-• (renameˣᵐ-preserves-NWTerm ρ nwM)
renameˣᵐ-preserves-NWTerm ρ (nw-ν nwM nwc) =
  nw-ν (renameˣᵐ-preserves-NWTerm ρ nwM) nwc
renameˣᵐ-preserves-NWTerm ρ nw-$ = nw-$
renameˣᵐ-preserves-NWTerm ρ (nw-⊕ nwL nwM) =
  nw-⊕ (renameˣᵐ-preserves-NWTerm ρ nwL)
       (renameˣᵐ-preserves-NWTerm ρ nwM)
renameˣᵐ-preserves-NWTerm ρ (nw-⟨⟩ nwM nwc) =
  nw-⟨⟩ (renameˣᵐ-preserves-NWTerm ρ nwM) nwc
renameˣᵐ-preserves-NWTerm ρ nw-blame = nw-blame

NWSubst : Substˣ → Set
NWSubst σ = ∀ x → NWTerm (σ x)

extˢˣ-preserves-NWSubst :
  ∀ {σ} →
  NWSubst σ →
  NWSubst (extˢˣ σ)
extˢˣ-preserves-NWSubst nwσ zero = nw-`
extˢˣ-preserves-NWSubst nwσ (suc x) =
  renameˣᵐ-preserves-NWTerm suc (nwσ x)

↑ᵗᵐ-preserves-NWSubst :
  ∀ {σ} →
  NWSubst σ →
  NWSubst (↑ᵗᵐ σ)
↑ᵗᵐ-preserves-NWSubst nwσ x =
  ⇑ᵗᵐ-preserves-NWTerm (nwσ x)

substˣᵐ-preserves-NWTerm :
  ∀ {σ M} →
  NWSubst σ →
  NWTerm M →
  NWTerm (substˣᵐ σ M)
substˣᵐ-preserves-NWTerm nwσ nw-` = nwσ _
substˣᵐ-preserves-NWTerm nwσ (nw-ƛ nwM) =
  nw-ƛ (substˣᵐ-preserves-NWTerm (extˢˣ-preserves-NWSubst nwσ) nwM)
substˣᵐ-preserves-NWTerm nwσ (nw-· nwL nwM) =
  nw-· (substˣᵐ-preserves-NWTerm nwσ nwL)
       (substˣᵐ-preserves-NWTerm nwσ nwM)
substˣᵐ-preserves-NWTerm nwσ (nw-Λ nwM) =
  nw-Λ (substˣᵐ-preserves-NWTerm (↑ᵗᵐ-preserves-NWSubst nwσ) nwM)
substˣᵐ-preserves-NWTerm nwσ (nw-• nwM) =
  nw-• (substˣᵐ-preserves-NWTerm nwσ nwM)
substˣᵐ-preserves-NWTerm nwσ (nw-ν nwM nwc) =
  nw-ν (substˣᵐ-preserves-NWTerm nwσ nwM) nwc
substˣᵐ-preserves-NWTerm nwσ nw-$ = nw-$
substˣᵐ-preserves-NWTerm nwσ (nw-⊕ nwL nwM) =
  nw-⊕ (substˣᵐ-preserves-NWTerm nwσ nwL)
       (substˣᵐ-preserves-NWTerm nwσ nwM)
substˣᵐ-preserves-NWTerm nwσ (nw-⟨⟩ nwM nwc) =
  nw-⟨⟩ (substˣᵐ-preserves-NWTerm nwσ nwM) nwc
substˣᵐ-preserves-NWTerm nwσ nw-blame = nw-blame

singleEnv-preserves-NWSubst :
  ∀ {V} →
  NWTerm V →
  NWSubst (singleEnv V)
singleEnv-preserves-NWSubst nwV zero = nwV
singleEnv-preserves-NWSubst nwV (suc x) = nw-`

single-subst-preserves-NWTerm :
  ∀ {M V} →
  NWTerm M →
  NWTerm V →
  NWTerm (M [ V ])
single-subst-preserves-NWTerm nwM nwV =
  substˣᵐ-preserves-NWTerm (singleEnv-preserves-NWSubst nwV) nwM

nw-seq-left :
  ∀ {p q} →
  NWCoercion (p ︔ q) →
  NWCoercion p
nw-seq-left (inj₁ (gG ？︔ gⁿ)) = inj₁ (untag gG)
nw-seq-left (inj₁ (fun-untag-gen safe)) = inj₁ (untag ★⇒★)
nw-seq-left (inj₁ (_︔seal_ sⁿ α)) = inj₁ (strictⁿ→narrow sⁿ)
nw-seq-left (inj₂ (gʷ ︔ gG !)) =
  inj₂ (cross (strictCrossʷ→cross gʷ))
nw-seq-left (inj₂ (inst-fun-tag safe)) = inj₂ (inst safe)
nw-seq-left (inj₂ (unseal︔_ α {A = A} sʷ)) =
  inj₂ (unsealʷ α A)

nw-seq-right :
  ∀ {p q} →
  NWCoercion (p ︔ q) →
  NWCoercion q
nw-seq-right (inj₁ (gG ？︔ gⁿ)) =
  inj₁ (cross (strictCrossⁿ→cross gⁿ))
nw-seq-right (inj₁ (fun-untag-gen safe)) = inj₁ (gen safe)
nw-seq-right (inj₁ (_︔seal_ {A = A} sⁿ α)) =
  inj₁ (sealⁿ A α)
nw-seq-right (inj₂ (gʷ ︔ gG !)) = inj₂ (tag gG)
nw-seq-right (inj₂ (inst-fun-tag safe)) = inj₂ (tag ★⇒★)
nw-seq-right (inj₂ (unseal︔_ α sʷ)) =
  inj₂ (strictʷ→widen sʷ)

nw-fun-left :
  ∀ {p q} →
  NWCoercion (p ↦ q) →
  NWCoercion p
nw-fun-left (inj₁ (cross (pʷ ↦ qⁿ))) = inj₂ pʷ
nw-fun-left (inj₂ (cross (pⁿ ↦ qʷ))) = inj₁ pⁿ

nw-fun-right :
  ∀ {p q} →
  NWCoercion (p ↦ q) →
  NWCoercion q
nw-fun-right (inj₁ (cross (pʷ ↦ qⁿ))) = inj₁ qⁿ
nw-fun-right (inj₂ (cross (pⁿ ↦ qʷ))) = inj₂ qʷ

nw-all-body :
  ∀ {c} →
  NWCoercion (`∀ c) →
  NWCoercion c
nw-all-body (inj₁ (cross (`∀ cⁿ))) = inj₁ cⁿ
nw-all-body (inj₂ (cross (`∀ cʷ))) = inj₂ cʷ

nw-gen-body :
  ∀ {A c} →
  NWCoercion (gen A c) →
  NWCoercion c
nw-gen-body (inj₁ (gen safe)) = inj₁ (genSafe→narrowing safe)
nw-gen-body (inj₂ (cross ()))

nw-inst-body :
  ∀ {A c} →
  NWCoercion (inst A c) →
  NWCoercion c
nw-inst-body (inj₁ (cross ()))
nw-inst-body (inj₂ (inst safe)) = inj₂ (instSafe→widening safe)

applyCoercion-preserves-NWCoercion :
  ∀ χ {c} →
  NWCoercion c →
  NWCoercion (applyCoercion χ c)
applyCoercion-preserves-NWCoercion keep nwc = nwc
applyCoercion-preserves-NWCoercion (bind A) nwc =
  ⇑ᶜ-preserves-NWCoercion nwc

applyCoercionUnderTyBinder-preserves-NWCoercion :
  ∀ χ {c} →
  NWCoercion c →
  NWCoercion (applyCoercionUnderTyBinder χ c)
applyCoercionUnderTyBinder-preserves-NWCoercion keep nwc = nwc
applyCoercionUnderTyBinder-preserves-NWCoercion (bind A) nwc =
  renameᶜ-preserves-NWCoercion (extᵗ suc) nwc

applyTerm-preserves-NWTerm :
  ∀ χ {M} →
  NWTerm M →
  NWTerm (applyTerm χ M)
applyTerm-preserves-NWTerm keep nwM = nwM
applyTerm-preserves-NWTerm (bind A) nwM = ⇑ᵗᵐ-preserves-NWTerm nwM

pure-step-preserves-NWTerm :
  ∀ {M N} →
  M —→ N →
  NWTerm M →
  NWTerm N
pure-step-preserves-NWTerm δ-⊕ (nw-⊕ nw-$ nw-$) = nw-$
pure-step-preserves-NWTerm (β vV) (nw-· (nw-ƛ nwN) nwV) =
  single-subst-preserves-NWTerm nwN nwV
pure-step-preserves-NWTerm (β-Λ• vV) (nw-• (nw-Λ nwV)) =
  renameᵗᵐ-preserves-NWTerm (singleRenameᵗ zero) nwV
pure-step-preserves-NWTerm (β-∀• vV) (nw-• (nw-⟨⟩ nwV nwc)) =
  nw-⟨⟩ (nw-• nwV)
    (renameᶜ-preserves-NWCoercion (singleRenameᵗ zero)
      (nw-all-body nwc))
pure-step-preserves-NWTerm (β-gen• vV) (nw-• (nw-⟨⟩ nwV nwc)) =
  nw-⟨⟩ nwV
    (renameᶜ-preserves-NWCoercion (singleRenameᵗ zero)
      (nw-gen-body nwc))
pure-step-preserves-NWTerm (β-id vV) (nw-⟨⟩ nwV nwc) = nwV
pure-step-preserves-NWTerm (β-seq vV) (nw-⟨⟩ nwV nwc) =
  nw-⟨⟩ (nw-⟨⟩ nwV (nw-seq-left nwc)) (nw-seq-right nwc)
pure-step-preserves-NWTerm (β-↦ vV vW)
    (nw-· (nw-⟨⟩ nwV nwc) nwW) =
  nw-⟨⟩ (nw-· nwV (nw-⟨⟩ nwW (nw-fun-left nwc)))
    (nw-fun-right nwc)
pure-step-preserves-NWTerm (β-inst vV) (nw-⟨⟩ nwV nwc) =
  nw-ν nwV (nw-inst-body nwc)
pure-step-preserves-NWTerm (tag-untag-ok vV)
    (nw-⟨⟩ (nw-⟨⟩ nwV nwc₁) nwc₂) =
  nwV
pure-step-preserves-NWTerm (tag-untag-bad vV G≢H)
    (nw-⟨⟩ (nw-⟨⟩ nwV nwc₁) nwc₂) =
  nw-blame
pure-step-preserves-NWTerm (seal-unseal vV)
    (nw-⟨⟩ (nw-⟨⟩ nwV nwc₁) nwc₂) =
  nwV
pure-step-preserves-NWTerm blame-·₁ (nw-· nw-blame nwM) = nw-blame
pure-step-preserves-NWTerm (blame-·₂ vV) (nw-· nwV nw-blame) = nw-blame
pure-step-preserves-NWTerm blame-• (nw-• nw-blame) = nw-blame
pure-step-preserves-NWTerm blame-⟨⟩ (nw-⟨⟩ nw-blame nwc) = nw-blame
pure-step-preserves-NWTerm blame-⊕₁ (nw-⊕ nw-blame nwM) = nw-blame
pure-step-preserves-NWTerm (blame-⊕₂ vV) (nw-⊕ nwV nw-blame) = nw-blame

step-preserves-NWTerm :
  ∀ {M N χ} →
  M —→[ χ ] N →
  NWTerm M →
  NWTerm N
step-preserves-NWTerm (pure-step red) nwM =
  pure-step-preserves-NWTerm red nwM
step-preserves-NWTerm (ν-step vV noV) (nw-ν nwV nwc) =
  nw-⟨⟩ (nw-• (⇑ᵗᵐ-preserves-NWTerm nwV)) nwc
step-preserves-NWTerm {χ = χ} (ξ-·₁ red shiftM) (nw-· nwL nwM) =
  nw-· (step-preserves-NWTerm red nwL)
       (applyTerm-preserves-NWTerm χ nwM)
step-preserves-NWTerm {χ = χ} (ξ-·₂ vV shiftV red) (nw-· nwV nwM) =
  nw-· (applyTerm-preserves-NWTerm χ nwV)
       (step-preserves-NWTerm red nwM)
step-preserves-NWTerm {χ = χ} (ξ-⟨⟩ red) (nw-⟨⟩ nwM nwc) =
  nw-⟨⟩ (step-preserves-NWTerm red nwM)
    (applyCoercion-preserves-NWCoercion χ nwc)
step-preserves-NWTerm {χ = χ} (ξ-ν red) (nw-ν nwM nwc) =
  nw-ν (step-preserves-NWTerm red nwM)
    (applyCoercionUnderTyBinder-preserves-NWCoercion χ nwc)
step-preserves-NWTerm blame-ν (nw-ν nw-blame nwc) = nw-blame
step-preserves-NWTerm {χ = χ} (ξ-⊕₁ red shiftM) (nw-⊕ nwL nwM) =
  nw-⊕ (step-preserves-NWTerm red nwL)
       (applyTerm-preserves-NWTerm χ nwM)
step-preserves-NWTerm {χ = χ} (ξ-⊕₂ vV shiftV red) (nw-⊕ nwL nwM) =
  nw-⊕ (applyTerm-preserves-NWTerm χ nwL)
       (step-preserves-NWTerm red nwM)
