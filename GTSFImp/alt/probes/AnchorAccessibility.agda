module alt.probes.AnchorAccessibility where

-- File Charter:
--   * Defines the probe-local anchor-accessibility relation proposed for
--     `⊢reveal`: walking down a telescope may cross live begins, lexical
--     binders, and ν entries, but an end jumps to its matching begin and
--     hides every entry born inside that closed region.
--   * Defines a syntax-directed certificate that every reveal/conceal node
--     in a term names an accessible anchor; its conceal constructor also
--     records the live-anchor lookup used by `⊢conceal`.
--   * Checks the U49 discriminator: the young ν in the ended pocket is
--     inaccessible, while the older anchor below that pocket remains
--     accessible.
--   * Companion probes cover both U40 traces, the U44 escape/projection
--     traces, the live escape/re-entry spine, wrapper rules, ν dissolution,
--     and the proposed conceal-meets-ν pair.
--   * Installing the reveal premise would create preservation obligations
--     where β-Λ/β-gen mint crossings; β-reveal-⇒/β-conceal-⇒ and both
--     ScTyWrap rules re-situate them; NUTYWRAP exchanges ν with `,typ`; and
--     the proposed ν-push-conceal/ν-gc-conceal pair exchanges or removes ν
--     across an ended crossing.  NUWRAP leaves the telescope order fixed and
--     const-ν
--     is crossing-free; ξ rules retain their enclosing node telescope.

open import Data.Bool using (Bool; false; true)
open import Data.Fin using (zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; ¬_; yes; no)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Consistency
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
import alt.probes.U49PocketStrengthensCounterexample as U49

------------------------------------------------------------------------
-- Probe-local accessibility
------------------------------------------------------------------------

infix 4 _∈acc_

mutual
  allInaccessible : ∀ Θ → Vec.Vec Bool Θ
  allInaccessible zero = Vec.[]
  allInaccessible (suc Θ) = false Vec.∷ allInaccessible Θ

  accessibleAnchors : ∀ {Θ Δ σ} → TyEnv Θ Δ σ → Vec.Vec Bool Θ
  accessibleAnchors ∅ = Vec.[]
  accessibleAnchors (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) =
    accessibleAnchors Ψ
  accessibleAnchors (Ψ ,typ) = accessibleAnchors Ψ
  accessibleAnchors (Ψ ,:= A) = true Vec.∷ accessibleAnchors Ψ
  accessibleAnchors (Ψ ,end[ Y ]) = belowBinder Ψ Y

  -- While closing a region, every ν crossed before the matching binder is
  -- hidden.  Earlier anchors retain the accessibility computed below that
  -- binder.  Crossing an older end restores its deleted variable position.
  belowBinder : ∀ {Θ Δ σ}
    → TyEnv Θ Δ σ → TyVar Δ → Vec.Vec Bool Θ
  belowBinder ∅ ()
  belowBinder (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) X with Y ≟ X
  belowBinder (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) .Y | yes refl =
    accessibleAnchors Ψ
  belowBinder (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) X | no Y≢X =
    belowBinder Ψ (punchOut Y X Y≢X)
  belowBinder {Θ = Θ} (Ψ ,typ) zero = allInaccessible Θ
  belowBinder (Ψ ,typ) (suc X) = belowBinder Ψ X
  belowBinder (Ψ ,:= A) X = false Vec.∷ belowBinder Ψ X
  belowBinder (Ψ ,end[ Y ]) X = belowBinder Ψ (punchIn Y X)

_∈acc_ : ∀ {Θ Δ σ} → TyVar Θ → TyEnv Θ Δ σ → Set
α ∈acc Ψ = Vec.lookup (accessibleAnchors Ψ) α ≡ true

∈acc? : ∀ {Θ Δ σ} (α : TyVar Θ) (Ψ : TyEnv Θ Δ σ)
  → Dec (α ∈acc Ψ)
∈acc? α Ψ with Vec.lookup (accessibleAnchors Ψ) α
∈acc? α Ψ | false = no (λ ())
∈acc? α Ψ | true = yes refl

------------------------------------------------------------------------
-- Every crossing in a raw term is accessible at its node telescope
------------------------------------------------------------------------

data AllAccessible : ∀ {Θ Δ σ}
    → TyEnv Θ Δ σ → Term Θ Δ → Set where
  acc-` : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {x}
      ------------------
    → AllAccessible Ψ (` x)

  acc-ƛ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ} {M}
    → AllAccessible Ψ M
      ------------------------
    → AllAccessible Ψ (ƛ A ˙ M)

  acc-· : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {L M}
    → AllAccessible Ψ L
    → AllAccessible Ψ M
      -----------------------
    → AllAccessible Ψ (L · M)

  acc-Λ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {M}
    → AllAccessible (Ψ ,typ) M
      --------------------
    → AllAccessible Ψ (Λ M)

  acc-• : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {M}
      {B : Ty (suc Δ)} {A : Ty Δ}
    → AllAccessible Ψ M
      --------------------------------
    → AllAccessible Ψ (M ⦂∀ B [ A ])

  acc-$ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {κ}
      ------------------
    → AllAccessible Ψ ($ κ)

  acc-⊕ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {L M op}
    → AllAccessible Ψ L
    → AllAccessible Ψ M
      -----------------------------
    → AllAccessible Ψ (L ⊕[ op ] M)

  acc-⟨⟩ : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {M μ A B}
      {c : μ ⊢ A ∼ B}
    → AllAccessible Ψ M
      -------------------------
    → AllAccessible Ψ (M ⟨ c ⟩)

  acc-reveal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      {M : Term Θ (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal} {fresh : α ∉ᵛ σ}
    → α ∈acc Ψ
    → AllAccessible (Ψ ,begin[ Y ≔ α ]⟨ fresh ⟩) M
      ---------------------------------------
    → AllAccessible Ψ (M ↑[ Y ≔ α ] c)

  acc-conceal : ∀ {Θ Δ σ} {Ψ : TyEnv Θ (suc Δ) σ}
      {M : Term Θ Δ} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Vec.lookup σ Y ≡ just α
    → α ∈acc Ψ
    → AllAccessible (Ψ ,end[ Y ]) M
      ---------------------------------------
    → AllAccessible Ψ (M ↓[ Y ≔ α ] c)

  acc-ν : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ} {A : Ty Δ} {M}
    → AllAccessible (Ψ ,:= A) M
      -------------------------
    → AllAccessible Ψ (ν[ A ] M)

  acc-blame : ∀ {Θ Δ σ} {Ψ : TyEnv Θ Δ σ}
      -----------------
    → AllAccessible Ψ blame

------------------------------------------------------------------------
-- U49: an end hides the young ν but not the anchor below the region
------------------------------------------------------------------------

u49-young-inaccessible : ¬ (zero ∈acc U49.pocketEnv)
u49-young-inaccessible ()

u49-old-accessible : suc zero ∈acc U49.pocketEnv
u49-old-accessible = refl
