module strong.Unfold where

-- Strong System F — KNOWLEDGE UNFOLDING and the UNFOLDING CONGRUENCE.
--
-- (notes/DualLicenseDesign.md §4, and the "(a″) PROBE VERDICT" of
-- notes/DECISIONS.md; ported from notes/old/UnfoldProbe.agda §1–§2 and
-- notes/old/UpToProbe.agda §1/§7.)
--
-- WHY.  Knowledge entries are kept RAW (a reveal's rep is stored as written,
-- so the external face ρᵇ and the entry agree), and instead every KNOWLEDGE
-- COMPARISON is taken up to unfolding.  Two chained entries — W:=Y over
-- Y:=𝔹 — carry the same knowledge as W:=𝔹, and the dual's rebuild differs
-- from the original context by exactly such an unfolding.  Syntactic
-- equality cannot see that; ≈Δ̄ can.
--
--   unfoldᵉ Γ A     Zdancewic's Δ̄ applied to A: every revealed variable
--                   replaced by its (recursively unfolded) representation.
--                   The recursion is on the CONTEXT — an entry `rvld B`
--                   stores a type over its own TAIL — so it is well founded
--                   for free (no termination pragma).
--   A ≈Δ̄⟨ Γ ⟩ B    the two types have the same unfolding in Γ.
--
-- DESIGN CHOICE (UpToProbe §1): ≈Δ̄ IS the propositional equality of
-- unfoldings, wrapped in one constructor (≈unf) purely so that the type
-- former is rigid and Γ/A/B are inferable.  Three payoffs, all cashed out
-- below: (1) equivalence and congruence are free — ≈-refl/sym/trans are
-- refl/sym/trans under the wrapper and ≈-⇒ / ≈-∀ are THEOREMS; (2) every
-- witness is refl-checkable and every refutation a one-line absurd pattern;
-- (3) the renaming transport (≈-ren) is a statement about unfSub, identical
-- for either presentation.
--
-- An `xrvld` entry is treated as ABSTRACT here: its rep lives one level OUT,
-- so it is not a type this context can resolve (DualLicenseProbe's fgt³).

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; rename-cong; subst-id; sub-sub;
         rename-subst; rename-subst-commute; rename-rename-commute)
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _↓_;
         _∋_:=_; here; skip-abst; skip-rvld; skip-xrvld)

private
  variable
    Γ Γ₁ Γ₂ Δ Δ' : TCtx
    A B C : Ty
    X : ℕ

------------------------------------------------------------------------
-- The unfolding operator
------------------------------------------------------------------------

-- unfSub Γ : the fully-resolved image of each variable of Γ, as a Γ-type.
-- An `rvld B` entry stores B over its own tail, so B is unfolded in the tail
-- and shifted back up by one.  `abst` and `xrvld` slots are left alone.
unfSub : TCtx → Substᵗ
unfSub []            X       = ` X
unfSub (abst    ∷ Γ) zero    = ` zero
unfSub (abst    ∷ Γ) (suc X) = ⇑ᵗ (unfSub Γ X)
unfSub (rvld B  ∷ Γ) zero    = ⇑ᵗ (substᵗ (unfSub Γ) B)
unfSub (rvld B  ∷ Γ) (suc X) = ⇑ᵗ (unfSub Γ X)
unfSub (xrvld B ∷ Γ) zero    = ` zero
unfSub (xrvld B ∷ Γ) (suc X) = ⇑ᵗ (unfSub Γ X)

unfoldᵉ : TCtx → Ty → Ty
unfoldᵉ Γ A = substᵗ (unfSub Γ) A

-- upᵉ Y : the lift that carries a (Γ ↓ Y)-type up to a Γ-type.  Kept here so
-- that the prefix lemmas below do not have to reach into strong.Boundary
-- (where the same map is called `upRep`).
upᵉ : ℕ → Ty → Ty
upᵉ Y = renameᵗ (λ i → suc Y + i)

------------------------------------------------------------------------
-- The unfolding congruence  A ≈Δ̄⟨ Γ ⟩ B
--
-- The CONTEXT argument is always the context over which BOTH sides are read;
-- every use in the development says which context that is at the point of
-- use.
------------------------------------------------------------------------

infix 4 _≈Δ̄⟨_⟩_
data _≈Δ̄⟨_⟩_ : Ty → TCtx → Ty → Set where
  ≈unf : unfoldᵉ Γ A ≡ unfoldᵉ Γ B → A ≈Δ̄⟨ Γ ⟩ B

≈unf⁻ : A ≈Δ̄⟨ Γ ⟩ B → unfoldᵉ Γ A ≡ unfoldᵉ Γ B
≈unf⁻ (≈unf e) = e

≈-refl : A ≈Δ̄⟨ Γ ⟩ A
≈-refl = ≈unf refl

≈-sym : A ≈Δ̄⟨ Γ ⟩ B → B ≈Δ̄⟨ Γ ⟩ A
≈-sym (≈unf e) = ≈unf (sym e)

≈-trans : A ≈Δ̄⟨ Γ ⟩ B → B ≈Δ̄⟨ Γ ⟩ C → A ≈Δ̄⟨ Γ ⟩ C
≈-trans (≈unf e₁) (≈unf e₂) = ≈unf (trans e₁ e₂)

-- syntactic equality is the strongest form of ≈ (soundness of every
-- comparison the design had before the relaxation)
≡→≈ : A ≡ B → A ≈Δ̄⟨ Γ ⟩ B
≡→≈ {Γ = Γ} e = ≈unf (cong (unfoldᵉ Γ) e)

≈-⇒ : ∀ {A' B'} → A ≈Δ̄⟨ Γ ⟩ A' → B ≈Δ̄⟨ Γ ⟩ B'
    → (A ⇒ B) ≈Δ̄⟨ Γ ⟩ (A' ⇒ B')
≈-⇒ (≈unf e₁) (≈unf e₂) = ≈unf (cong₂ _⇒_ e₁ e₂)

-- the ∀ case: going under a binder is going under a fresh ABSTRACT entry
unfSub-exts : ∀ (Γ₀ : TCtx) X → extsᵗ (unfSub Γ₀) X ≡ unfSub (abst ∷ Γ₀) X
unfSub-exts Γ₀ zero    = refl
unfSub-exts Γ₀ (suc X) = refl

≈-∀ : A ≈Δ̄⟨ abst ∷ Γ ⟩ B → (`∀ A) ≈Δ̄⟨ Γ ⟩ (`∀ B)
≈-∀ {A = A} {Γ = Γ} {B = B} (≈unf e) =
  ≈unf (cong `∀ (trans (subst-cong (unfSub-exts Γ) A)
                       (trans e (sym (subst-cong (unfSub-exts Γ) B)))))

------------------------------------------------------------------------
-- Monotonicity in the context.  `Absorbs Δ Δ′` says Δ′'s unfolding
-- swallows Δ's (Δ′ resolves at least what Δ resolves, the same way); then
-- every ≈ at Δ is an ≈ at Δ′.
------------------------------------------------------------------------

Absorbs : TCtx → TCtx → Set
Absorbs Δ Δ' = ∀ X → unfoldᵉ Δ' (unfSub Δ X) ≡ unfSub Δ' X

unf-absorb : ∀ (Δ₀ Δ₁ : TCtx) → Absorbs Δ₀ Δ₁ → ∀ A
           → unfoldᵉ Δ₁ (unfoldᵉ Δ₀ A) ≡ unfoldᵉ Δ₁ A
unf-absorb Δ₀ Δ₁ h A =
  trans (sub-sub (unfSub Δ₀) (unfSub Δ₁) A) (subst-cong h A)

≈-mono : ∀ (Δ₀ Δ₁ : TCtx) → Absorbs Δ₀ Δ₁
       → A ≈Δ̄⟨ Δ₀ ⟩ B → A ≈Δ̄⟨ Δ₁ ⟩ B
≈-mono {A = A} {B = B} Δ₀ Δ₁ h (≈unf e) =
  ≈unf (trans (sym (unf-absorb Δ₀ Δ₁ h A))
              (trans (cong (unfoldᵉ Δ₁) e) (unf-absorb Δ₀ Δ₁ h B)))

------------------------------------------------------------------------
-- THE TWO PREFIX LEMMAS.  They are what turns the renaming transport from a
-- new top-level hypothesis into a consequence of the ∋:= transport that
-- ⊢renameᵀ already carries (strong.BReduction, UnfRen≈-hk).
--
--   unfSub-↓    reading a variable ABOVE slot Y is reading it in Y's own
--               prefix and lifting back — so unfolding is prefix-local;
--   unfSub-dich every slot either unfolds to ITSELF (abst, xrvld, or out of
--               range) or is KNOWLEDGE, and then its unfolding is the lift
--               of the unfolded rep read in its own prefix.
------------------------------------------------------------------------

-- the shared inductive step: shift the prefix reading up by one more slot
up-step : ∀ (Δ₀ : TCtx) Y i
        → ⇑ᵗ (unfSub Δ₀ (suc Y + i)) ≡ upᵉ (suc Y) (unfSub (Δ₀ ↓ Y) i)

unfSub-↓ : ∀ (Δ₀ : TCtx) Y i
         → unfSub Δ₀ (suc Y + i) ≡ upᵉ Y (unfSub (Δ₀ ↓ Y) i)
unfSub-↓ []               Y       i = refl
unfSub-↓ (abst    ∷ Δ₀)   zero    i = refl
unfSub-↓ (rvld B  ∷ Δ₀)   zero    i = refl
unfSub-↓ (xrvld B ∷ Δ₀)   zero    i = refl
unfSub-↓ (abst    ∷ Δ₀)   (suc Y) i = up-step Δ₀ Y i
unfSub-↓ (rvld B  ∷ Δ₀)   (suc Y) i = up-step Δ₀ Y i
unfSub-↓ (xrvld B ∷ Δ₀)   (suc Y) i = up-step Δ₀ Y i

up-step Δ₀ Y i =
  trans (cong ⇑ᵗ (unfSub-↓ Δ₀ Y i))
        (rename-rename-commute (λ k → suc Y + k) suc
                               (unfSub (Δ₀ ↓ Y) i))

dich-step : ∀ (Δ₀ : TCtx) X B
  → unfSub Δ₀ X ≡ upᵉ X (unfoldᵉ (Δ₀ ↓ X) B)
  → ⇑ᵗ (unfSub Δ₀ X) ≡ upᵉ (suc X) (unfoldᵉ (Δ₀ ↓ X) B)

unfSub-dich : ∀ (Δ₀ : TCtx) X
  → (unfSub Δ₀ X ≡ ` X)
  ⊎ (Σ Ty λ B → (Δ₀ ∋ X := B)
                × (unfSub Δ₀ X ≡ upᵉ X (unfoldᵉ (Δ₀ ↓ X) B)))
unfSub-dich []              X    = inj₁ refl
unfSub-dich (abst    ∷ Δ₀)  zero = inj₁ refl
unfSub-dich (xrvld B ∷ Δ₀)  zero = inj₁ refl
unfSub-dich (rvld B  ∷ Δ₀)  zero = inj₂ (B , here , refl)
unfSub-dich (abst ∷ Δ₀) (suc X) with unfSub-dich Δ₀ X
unfSub-dich (abst ∷ Δ₀) (suc X) | inj₁ e = inj₁ (cong ⇑ᵗ e)
unfSub-dich (abst ∷ Δ₀) (suc X) | inj₂ (B , p , e) =
  inj₂ (B , skip-abst p , dich-step Δ₀ X B e)
unfSub-dich (rvld C ∷ Δ₀) (suc X) with unfSub-dich Δ₀ X
unfSub-dich (rvld C ∷ Δ₀) (suc X) | inj₁ e = inj₁ (cong ⇑ᵗ e)
unfSub-dich (rvld C ∷ Δ₀) (suc X) | inj₂ (B , p , e) =
  inj₂ (B , skip-rvld p , dich-step Δ₀ X B e)
unfSub-dich (xrvld C ∷ Δ₀) (suc X) with unfSub-dich Δ₀ X
unfSub-dich (xrvld C ∷ Δ₀) (suc X) | inj₁ e = inj₁ (cong ⇑ᵗ e)
unfSub-dich (xrvld C ∷ Δ₀) (suc X) | inj₂ (B , p , e) =
  inj₂ (B , skip-xrvld p , dich-step Δ₀ X B e)

dich-step Δ₀ X B e =
  trans (cong ⇑ᵗ e)
        (rename-rename-commute (λ k → suc X + k) suc
                               (unfoldᵉ (Δ₀ ↓ X) B))

-- COROLLARY.  Unfolding commutes with the prefix lift: reading a lifted
-- prefix type in Δ is reading it in the prefix and lifting.
unf-up : ∀ (Δ₀ : TCtx) Y C
       → unfoldᵉ Δ₀ (upᵉ Y C) ≡ upᵉ Y (unfoldᵉ (Δ₀ ↓ Y) C)
unf-up Δ₀ Y C =
  trans (rename-subst-commute (λ i → suc Y + i) (unfSub Δ₀) C)
    (trans (subst-cong (unfSub-↓ Δ₀ Y) C)
           (sym (rename-subst (λ i → suc Y + i) (unfSub (Δ₀ ↓ Y)) C)))

-- the same lemma keyed on the LOOKUP, which is the form the renaming
-- transport consumes
unfSub-know : ∀ (Δ₀ : TCtx) {X B} → Δ₀ ∋ X := B
            → unfSub Δ₀ X ≡ upᵉ X (unfoldᵉ (Δ₀ ↓ X) B)
unfSub-know (rvld B ∷ Δ₀)  here           = refl
unfSub-know (abst ∷ Δ₀)  {suc X} {B} (skip-abst p) =
  dich-step Δ₀ X B (unfSub-know Δ₀ p)
unfSub-know (rvld C ∷ Δ₀)  {suc X} {B} (skip-rvld p) =
  dich-step Δ₀ X B (unfSub-know Δ₀ p)
unfSub-know (xrvld C ∷ Δ₀) {suc X} {B} (skip-xrvld p) =
  dich-step Δ₀ X B (unfSub-know Δ₀ p)

------------------------------------------------------------------------
-- IDEMPOTENCE, WITHOUT A CONTEXT-WELL-FORMEDNESS PREMISE.  unfSub is
-- defined by recursion on the CONTEXT, so each of its images is already
-- fully resolved: a second unfolding is a no-op.  (UnfoldProbe proved this
-- via KNF and needed ⊢ Γ; keyed on unfSub's own recursion it needs
-- nothing.)  This is what makes weakening by a fresh abstract slot an
-- instance of the congruence transport.
------------------------------------------------------------------------

-- going under one entry: unfolding commutes with the shift
unf-shift : ∀ (E : TyEntry) (Δ₀ : TCtx) T
          → unfoldᵉ (E ∷ Δ₀) (⇑ᵗ T) ≡ ⇑ᵗ (unfoldᵉ Δ₀ T)
unf-shift abst Δ₀ T =
  trans (rename-subst-commute suc (unfSub (abst ∷ Δ₀)) T)
        (sym (rename-subst suc (unfSub Δ₀) T))
unf-shift (rvld B) Δ₀ T =
  trans (rename-subst-commute suc (unfSub (rvld B ∷ Δ₀)) T)
        (sym (rename-subst suc (unfSub Δ₀) T))
unf-shift (xrvld B) Δ₀ T =
  trans (rename-subst-commute suc (unfSub (xrvld B ∷ Δ₀)) T)
        (sym (rename-subst suc (unfSub Δ₀) T))

unf-self : ∀ (Δ₀ : TCtx) → Absorbs Δ₀ Δ₀
unf-self []              X       = refl
unf-self (abst ∷ Δ₀)     zero    = refl
unf-self (xrvld B ∷ Δ₀)  zero    = refl
unf-self (rvld B ∷ Δ₀)   zero    =
  trans (unf-shift (rvld B) Δ₀ (unfoldᵉ Δ₀ B))
        (cong ⇑ᵗ (unf-absorb Δ₀ Δ₀ (unf-self Δ₀) B))
unf-self (abst ∷ Δ₀)     (suc X) =
  trans (unf-shift abst Δ₀ (unfSub Δ₀ X)) (cong ⇑ᵗ (unf-self Δ₀ X))
unf-self (rvld B ∷ Δ₀)   (suc X) =
  trans (unf-shift (rvld B) Δ₀ (unfSub Δ₀ X)) (cong ⇑ᵗ (unf-self Δ₀ X))
unf-self (xrvld B ∷ Δ₀)  (suc X) =
  trans (unf-shift (xrvld B) Δ₀ (unfSub Δ₀ X)) (cong ⇑ᵗ (unf-self Δ₀ X))

unf-idem : ∀ (Δ₀ : TCtx) A → unfoldᵉ Δ₀ (unfoldᵉ Δ₀ A) ≡ unfoldᵉ Δ₀ A
unf-idem Δ₀ = unf-absorb Δ₀ Δ₀ (unf-self Δ₀)

------------------------------------------------------------------------
-- THE RENAMING TRANSPORT (UpToProbe §7).  The OPERATOR unfoldᵉ does not
-- commute with renaming under the hypotheses ⊢renameᵀ carries (an ABSTRACT
-- slot may land on a REVEALED one, and unfolding notices — ¬UnfRen-hk).
-- The CONGRUENCE transports with strictly less: the hypothesis in ABSORBED
-- form, which is exactly what holds at the abstract-to-revealed step, and
-- which strong.BReduction derives from the ∋:= transport (UnfRen≈-hk).
------------------------------------------------------------------------

UnfRen≈ : (ℕ → ℕ) → TCtx → TCtx → Set
UnfRen≈ ρ Γ₁ Γ₂ = ∀ X → unfoldᵉ Γ₂ (renameᵗ ρ (unfSub Γ₁ X)) ≡ unfSub Γ₂ (ρ X)

-- the workhorse: a renamed unfolding may be re-read in the target
unf-ren-step : ∀ {ρ} (Γ₁ Γ₂ : TCtx) → UnfRen≈ ρ Γ₁ Γ₂ → ∀ T
             → unfoldᵉ Γ₂ (renameᵗ ρ (unfoldᵉ Γ₁ T))
               ≡ unfoldᵉ Γ₂ (renameᵗ ρ T)
unf-ren-step {ρ} Γ₁ Γ₂ h T =
  trans (cong (substᵗ (unfSub Γ₂)) (rename-subst ρ (unfSub Γ₁) T))
    (trans (sub-sub (λ X → renameᵗ ρ (unfSub Γ₁ X)) (unfSub Γ₂) T)
      (trans (subst-cong h T)
             (sym (rename-subst-commute ρ (unfSub Γ₂) T))))

≈-ren : ∀ {ρ} (Γ₁ Γ₂ : TCtx) → UnfRen≈ ρ Γ₁ Γ₂
      → A ≈Δ̄⟨ Γ₁ ⟩ B → renameᵗ ρ A ≈Δ̄⟨ Γ₂ ⟩ renameᵗ ρ B
≈-ren {A = A} {B = B} {ρ = ρ} Γ₁ Γ₂ h (≈unf e) =
  ≈unf (trans (sym (unf-ren-step Γ₁ Γ₂ h A))
              (trans (cong (λ T → unfoldᵉ Γ₂ (renameᵗ ρ T)) e)
                     (unf-ren-step Γ₁ Γ₂ h B)))

-- the ABSTRACT slot — the case that breaks the operator form — is FREE for
-- the absorbed one: an abstract (or exterior-read, or out-of-range) slot
-- unfolds to itself, so the equation becomes an identity.
UnfRen≈-fix : ∀ (ρ : ℕ → ℕ) (Γ₀ Γ₃ : TCtx) X → unfSub Γ₀ X ≡ ` X
            → unfoldᵉ Γ₃ (renameᵗ ρ (unfSub Γ₀ X)) ≡ unfSub Γ₃ (ρ X)
UnfRen≈-fix ρ Γ₀ Γ₃ X e = cong (λ T → unfoldᵉ Γ₃ (renameᵗ ρ T)) e

------------------------------------------------------------------------
-- Sanity checks
------------------------------------------------------------------------

private
  -- chained knowledge collapses:  W:=Y (0) , Y:=𝔹 (1) , X:=ℕ (2)
  Γch : TCtx
  Γch = rvld (` 0) ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

  _ : unfoldᵉ Γch (` 0) ≡ `𝔹
  _ = refl

  _ : unfoldᵉ Γch (` 0 ⇒ ` 2) ≡ (`𝔹 ⇒ `ℕ)
  _ = refl

  -- the two ROUTES to one piece of knowledge agree up to ≈, in the ambient
  -- over which both entries are read (UpToProbe's routes-agree≈)
  _ : (` 0) ≈Δ̄⟨ Γch ⟩ (` 1)
  _ = ≈unf refl

  -- unfolding is the IDENTITY on an abstract variable …
  _ : unfoldᵉ (abst ∷ rvld `𝔹 ∷ []) (` 0) ≡ ` 0
  _ = refl

  -- … and on an EXTERIOR-READ one (its rep is not a type of this context)
  _ : unfoldᵉ (xrvld (` 0) ∷ []) (` 0) ≡ ` 0
  _ = refl

  -- knowledge that GENUINELY differs is not bridged:  W unfolds to ℕ, not
  -- to ∀Z.Z→Z  (UpToProbe's far-bad)
  ¬≈-far : ¬ ((`∀ (` 0 ⇒ ` 0)) ≈Δ̄⟨ rvld (` 0) ∷ rvld `ℕ ∷ [] ⟩ (` 0))
  ¬≈-far (≈unf ())

  -- the NEAR-bad that must be ADMITTED: W's knowledge by the other route
  _ : `ℕ ≈Δ̄⟨ rvld (` 0) ∷ rvld `ℕ ∷ [] ⟩ (` 0)
  _ = ≈unf refl
