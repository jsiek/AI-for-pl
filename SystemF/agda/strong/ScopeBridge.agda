module strong.ScopeBridge where

-- Strong System F — the "context-wf ⇒ typing ⇒ Scoped" bridge (PLAN.md §3b).
--
-- The TyBeta preservation case builds a boundary  rvl A ∷ []  around the body
-- of a Λ, and the (env) rule then demands  Scoped (baseS (rvl A ∷ []) Δ) B
-- for the body's type B.  Nothing in the reduction relation carries that
-- fact, so it must be RECOVERED from typing.  Three moves do that:
--
--   1. typing gives well-formedness
--        ⊢ty-wf    : Δ ⊢* Γₜ → Δ ∣ Γₜ ⊢ M ⦂ A → Δ ⊢ A
--   2. well-formedness gives scoping
--        wf→Scoped : Δ ⊢ B → (∋tv ⊆ ∋ok) → Scoped Ψ B
--   3. the TyBeta boundary is all-ok     allOk-∋ok : (abst ∷ Δ) ∋tv X
--                                               → baseS (rvl A ∷ []) Δ ∋ok X
--
-- and composes them into  scB-bridge.  Step 1 needs substitution to preserve
-- well-formedness (wf-subst / wf-subst-sc) because the ⊢·[] and (env) cases
-- hand back a substituted type; for (env) that substitution is the
-- reveal-resolve ρᵇ, whose per-index well-formedness is ρᵇ-lookup-wf — and,
-- with the PARALLEL reveal block, that is a plain lookup into bwf↑.
--
-- Everything here is about the type context only; no reduction is imported.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _×_; _,_; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import strong.Types
open import strong.TypeSubst using (single-subst-def)
open import strong.Context
open import strong.Weakening using (wf-⇑-abst)
open import strong.Boundary

-- Δ, A, B, C, X, x are generalizable variables exported by strong.Context.
private
  variable
    Δ′ Ψᵗ : TCtx
    Γₜ : Ctx
    Ψ : SCtx
    Θ : BCtx
    σ : Substᵗ
    B₀ : Ty
    M : Term
    i j k r : ℕ

------------------------------------------------------------------------
-- Substitution preserves well-formedness
------------------------------------------------------------------------

-- The lookup hypothesis is transported under `∀ by extsᵗ: index 0 becomes the
-- fresh abstract variable, and a shifted image is weakened by wf-⇑-abst.
wf-subst : (∀ {X} → Δ ∋tv X → Δ′ ⊢ σ X)
  → Δ ⊢ A
  → Δ′ ⊢ substᵗ σ A
wf-subst h (wf-var p) = h p
wf-subst h wf-ℕ       = wf-ℕ
wf-subst h wf-𝔹       = wf-𝔹
wf-subst h (wf-⇒ a b) = wf-⇒ (wf-subst h a) (wf-subst h b)
wf-subst {Δ = Δ} {Δ′ = Δ′} {σ = σ} h (wf-∀ {A = A₀} a) =
  wf-∀ (wf-subst h-ext a)
  where
  h-ext : ∀ {X} → (abst ∷ Δ) ∋tv X → (abst ∷ Δ′) ⊢ extsᵗ σ X
  h-ext here-abst      = wf-var here-abst
  h-ext (skip-abst p)  = wf-⇑-abst (h p)

-- the single-substitution corollary, used by the ⊢·[] case of ⊢ty-wf
wf-[]ᵗ : (abst ∷ Δ) ⊢ B → Δ ⊢ A → Δ ⊢ B [ A ]ᵗ
wf-[]ᵗ {Δ = Δ} {B = B} {A = A} wfB wfA =
  subst (λ T → Δ ⊢ T) (sym (single-subst-def B A)) (wf-subst h wfB)
  where
  h : ∀ {X} → (abst ∷ Δ) ∋tv X → Δ ⊢ singleTyEnv A X
  h here-abst     = wfA
  h (skip-abst p) = wf-var p

-- The Scoped-indexed variant: the substitution need only be well formed at the
-- ACCESSIBLE slots (mirrors subst-cong-sc in strong.Boundary).
wf-subst-sc : Scoped Ψ A
  → (∀ X → Ψ ∋ok X → Δ′ ⊢ σ X)
  → Δ′ ⊢ substᵗ σ A
wf-subst-sc (sc-var p) h  = h _ p
wf-subst-sc sc-ℕ h        = wf-ℕ
wf-subst-sc sc-𝔹 h        = wf-𝔹
wf-subst-sc (sc-⇒ sA sB) h =
  wf-⇒ (wf-subst-sc sA h) (wf-subst-sc sB h)
wf-subst-sc {Ψ = Ψ} {Δ′ = Δ′} {σ = σ} (sc-∀ sA) h =
  wf-∀ (wf-subst-sc sA h-ext)
  where
  h-ext : ∀ X → (ok ∷ Ψ) ∋ok X → (abst ∷ Δ′) ⊢ extsᵗ σ X
  h-ext zero    hereᵒ      = wf-var here-abst
  h-ext (suc X) (thereᵒ p) = wf-⇑-abst (h X p)

------------------------------------------------------------------------
-- Accessibility-stack arithmetic:  baseS Θ Δ ∋ok X  splits at revs Θ
------------------------------------------------------------------------

-- an accessible slot is an index into the stack
∋ok-length : Ψ ∋ok X → X < length Ψ
∋ok-length hereᵒ      = s≤s z≤n
∋ok-length (thereᵒ p) = s≤s (∋ok-length p)

-- slotsᴳ has one slot per Δ entry, whatever the slots are
slotsᴳ-length : (Θ : BCtx) (k : ℕ) (Δ : TCtx)
  → length (slotsᴳ Θ k Δ) ≡ length Δ
slotsᴳ-length Θ k []      = refl
slotsᴳ-length Θ k (E ∷ Δ) = cong suc (slotsᴳ-length Θ (suc k) Δ)

-- every index below the length is in scope — the entry's flavour is irrelevant
<length→∋tv : X < length Δ → Δ ∋tv X
<length→∋tv {X = zero}  {Δ = abst ∷ Δ}   lt       = here-abst
<length→∋tv {X = zero}  {Δ = rvld A ∷ Δ} lt       = here-rvld
<length→∋tv {X = suc X} {Δ = abst ∷ Δ}   (s≤s lt) =
  skip-abst (<length→∋tv lt)
<length→∋tv {X = suc X} {Δ = rvld A ∷ Δ} (s≤s lt) =
  skip-rvld (<length→∋tv lt)

-- an accessible Γ-slot names a type variable of Δ
slotsᴳ-∋tv : (Θ : BCtx) (k : ℕ) → slotsᴳ Θ k Δ ∋ok X → Δ ∋tv X
slotsᴳ-∋tv {Δ = Δ} {X = X} Θ k p =
  <length→∋tv (subst (X <_) (slotsᴳ-length Θ k Δ) (∋ok-length p))

-- the reveal prefix / Γ-slot case split, phrased on the raw append.  The
-- prefix is now PER ENTRY (revSlots): a REP-LESS reveal's slot is `blk`, so
-- it cannot be accessible at all — the `rvl⋆` clause is absurd.
revSlots-view : (Θ : BCtx) (Ψ : SCtx) (X : ℕ) → (revSlots Θ ++ Ψ) ∋ok X
  → (X < revs Θ) ⊎ (∃ λ i → (X ≡ revs Θ + i) × Ψ ∋ok i)
revSlots-view []            Ψ X       p = inj₂ (X , refl , p)
revSlots-view (rvl A ∷ Θ)   Ψ zero    p = inj₁ (s≤s z≤n)
revSlots-view (rvl A ∷ Θ)   Ψ (suc X) (thereᵒ p)
  with revSlots-view Θ Ψ X p
revSlots-view (rvl A ∷ Θ) Ψ (suc X) (thereᵒ p) | inj₁ lt =
  inj₁ (s≤s lt)
revSlots-view (rvl A ∷ Θ) Ψ (suc X) (thereᵒ p) | inj₂ (i , eq , q) =
  inj₂ (i , cong suc eq , q)
revSlots-view (rvl⋆ ∷ Θ)    Ψ zero    ()
revSlots-view (rvl⋆ ∷ Θ)    Ψ (suc X) (thereᵒ p)
  with revSlots-view Θ Ψ X p
revSlots-view (rvl⋆ ∷ Θ) Ψ (suc X) (thereᵒ p) | inj₁ lt =
  inj₁ (s≤s lt)
revSlots-view (rvl⋆ ∷ Θ) Ψ (suc X) (thereᵒ p) | inj₂ (i , eq , q) =
  inj₂ (i , cong suc eq , q)
revSlots-view (cnc Y A ∷ Θ) Ψ X       p = revSlots-view Θ Ψ X p

------------------------------------------------------------------------
-- The external face ρᵇ is well formed, index by index
------------------------------------------------------------------------

-- a deep index passes through unchanged (conceals do not touch the exterior)
ρᵇ-deep : (Θ : BCtx) (i : ℕ) → ρᵇ Θ (revs Θ + i) ≡ ` i
ρᵇ-deep []            i = refl
ρᵇ-deep (rvl A ∷ Θ)   i = ρᵇ-deep Θ i
ρᵇ-deep (rvl⋆ ∷ Θ)    i = ρᵇ-deep Θ i
ρᵇ-deep (cnc X A ∷ Θ) i = ρᵇ-deep Θ i

-- a reveal-prefix index resolves to that reveal's EXTERNAL FACE, which under
-- the PARALLEL reveal block is the STORED rep — so this is a plain LOOKUP,
-- discharged by bwf↑'s own premise Δ ⊢ A.  A REP-LESS reveal's face is the
-- dummy `ℕ, well formed anywhere.
ρᵇ-lo : ∀ {Δ Ψᵗ Θ} (Ξ : BCtx) → Bwf Δ Ψᵗ Θ Ξ
      → (X : ℕ) → X < revs Ξ → Δ ⊢ ρᵇ Ξ X
ρᵇ-lo []            bwf[]              X       ()
ρᵇ-lo (rvl A ∷ Ξ)   (bwf↑ wfA b) zero          lt = wfA
ρᵇ-lo (rvl A ∷ Ξ)   (bwf↑ wfA b) (suc X) (s≤s lt) = ρᵇ-lo Ξ b X lt
ρᵇ-lo (rvl⋆ ∷ Ξ)    (bwf⋆ b)     zero          lt = wf-ℕ
ρᵇ-lo (rvl⋆ ∷ Ξ)    (bwf⋆ b)     (suc X) (s≤s lt) = ρᵇ-lo Ξ b X lt
ρᵇ-lo (cnc Y A ∷ Ξ) (bwf↓ k rev wfA b) X       lt = ρᵇ-lo Ξ b X lt

ρᵇ-lookup-wf : Δ ∣ Ψᵗ ⊢ᵇ Θ → (X : ℕ) → baseS Θ Δ ∋ok X → Δ ⊢ ρᵇ Θ X
ρᵇ-lookup-wf {Δ = Δ} {Θ = Θ} bwf X p
  with revSlots-view Θ (slotsᴳ Θ 0 Δ) X p
ρᵇ-lookup-wf {Δ = Δ} {Θ = Θ} bwf X p | inj₁ lt =
  ρᵇ-lo Θ bwf X lt
ρᵇ-lookup-wf {Δ = Δ} {Θ = Θ} bwf X p | inj₂ (i , refl , q) =
  subst (λ T → Δ ⊢ T) (sym (ρᵇ-deep Θ i)) (wf-var (slotsᴳ-∋tv Θ 0 q))

-- the (env) rule's result type is well formed in the exterior
env-ext-wf : Δ ∣ intOf Δ Θ ⊢ᵇ Θ
  → Scoped (baseS Θ Δ) B₀
  → Δ ⊢ substᵗ (ρᵇ Θ) B₀
env-ext-wf bwf sc = wf-subst-sc sc (ρᵇ-lookup-wf bwf)

------------------------------------------------------------------------
-- Typing gives well-formedness of the type
------------------------------------------------------------------------

⊢*-∋ : Δ ⊢* Γₜ → Γₜ ∋ x ⦂ A → Δ ⊢ A
⊢*-∋ (wfA ⊢∷ ⊢Γ) here      = wfA
⊢*-∋ (wfA ⊢∷ ⊢Γ) (there p) = ⊢*-∋ ⊢Γ p

⊢*-⤊ : Δ ⊢* Γₜ → (abst ∷ Δ) ⊢* ⤊ Γₜ
⊢*-⤊ ⊢[]          = ⊢[]
⊢*-⤊ (wfA ⊢∷ ⊢Γ) = wf-⇑-abst wfA ⊢∷ ⊢*-⤊ ⊢Γ

-- The term context must be known well formed: the ⊢` case pulls its type out
-- of Γₜ, so induction on the typing derivation alone cannot produce it.
⊢ty-wf : Δ ⊢* Γₜ → Δ ∣ Γₜ ⊢ M ⦂ A → Δ ⊢ A
⊢ty-wf ⊢Γ (⊢` p)          = ⊢*-∋ ⊢Γ p
⊢ty-wf ⊢Γ ⊢$              = wf-ℕ
⊢ty-wf ⊢Γ (⊢ƛ wfA ⊢N)     = wf-⇒ wfA (⊢ty-wf (wfA ⊢∷ ⊢Γ) ⊢N)
⊢ty-wf ⊢Γ (⊢· ⊢L ⊢M)      with ⊢ty-wf ⊢Γ ⊢L
⊢ty-wf ⊢Γ (⊢· ⊢L ⊢M) | wf-⇒ wfA wfB = wfB
⊢ty-wf ⊢Γ (⊢Λ ⊢N)         = wf-∀ (⊢ty-wf (⊢*-⤊ ⊢Γ) ⊢N)
⊢ty-wf ⊢Γ (⊢·[] ⊢L wfA)   with ⊢ty-wf ⊢Γ ⊢L
⊢ty-wf ⊢Γ (⊢·[] ⊢L wfA) | wf-∀ wfB = wf-[]ᵗ wfB wfA
⊢ty-wf ⊢Γ (env bwf sc ⊢M) = env-ext-wf bwf sc

------------------------------------------------------------------------
-- Well-formedness gives scoping
------------------------------------------------------------------------

wf→Scoped : Δ ⊢ B → (∀ {X} → Δ ∋tv X → Ψ ∋ok X) → Scoped Ψ B
wf→Scoped (wf-var p) h  = sc-var (h p)
wf→Scoped wf-ℕ h        = sc-ℕ
wf→Scoped wf-𝔹 h        = sc-𝔹
wf→Scoped (wf-⇒ a b) h  = sc-⇒ (wf→Scoped a h) (wf→Scoped b h)
wf→Scoped {Δ = Δ} {Ψ = Ψ} (wf-∀ {A = A₀} a) h =
  sc-∀ (wf→Scoped a h-ext)
  where
  h-ext : ∀ {X} → (abst ∷ Δ) ∋tv X → (ok ∷ Ψ) ∋ok X
  h-ext here-abst     = hereᵒ
  h-ext (skip-abst p) = thereᵒ (h p)

------------------------------------------------------------------------
-- The TyBeta boundary  rvl A ∷ []  has an all-ok accessibility stack
------------------------------------------------------------------------

-- cmax (rvl A ∷ []) = 0 and  0 ≤? i  is always `yes z≤n`, so slotAt reduces to
-- `ok` for an ABSTRACT index i — no lemma about _≤?_ is needed.
slotAt-rvl : ∀ {A} (i : ℕ) → slotAt (rvl A ∷ []) i ≡ ok
slotAt-rvl i = refl

slotsᴳ-allOk : ∀ {A} (k : ℕ) → Δ ∋tv X → slotsᴳ (rvl A ∷ []) k Δ ∋ok X
slotsᴳ-allOk k here-abst      = hereᵒ
slotsᴳ-allOk k here-rvld      = hereᵒ
slotsᴳ-allOk k (skip-abst p)  = thereᵒ (slotsᴳ-allOk (suc k) p)
slotsᴳ-allOk k (skip-rvld p)  = thereᵒ (slotsᴳ-allOk (suc k) p)

-- baseS (rvl A ∷ []) Δ = ok ∷ slotsᴳ (rvl A ∷ []) 0 Δ, definitionally
allOk-∋ok : (abst ∷ Δ) ∋tv X → baseS (rvl A ∷ []) Δ ∋ok X
allOk-∋ok here-abst     = hereᵒ
allOk-∋ok (skip-abst p) = thereᵒ (slotsᴳ-allOk 0 p)

------------------------------------------------------------------------
-- The bridge:  TyBeta's  scB  obligation
------------------------------------------------------------------------

-- The Λ body is typed at term context ⤊ [] = [], one abstract variable deeper
-- than the exterior; its type is therefore scoped over the reveal boundary's
-- (all-ok) accessibility stack.
scB-bridge : (abst ∷ Δ) ∣ [] ⊢ M ⦂ B → Scoped (baseS (rvl A ∷ []) Δ) B
scB-bridge ⊢V = wf→Scoped (⊢ty-wf ⊢[] ⊢V) allOk-∋ok

------------------------------------------------------------------------
-- Sanity checks
------------------------------------------------------------------------

private
  -- the polymorphic identity's body:  λx:X. x  :  X → X  at Δ = abst ∷ []
  ⊢id : (abst ∷ []) ∣ [] ⊢ ƛ ` 0 ∙ ` 0 ⦂ (` 0 ⇒ ` 0)
  ⊢id = ⊢ƛ (wf-var here-abst) (⊢` here)

  -- the bridge computes the expected derivation, on the nose
  _ : scB-bridge {Δ = []} {B = ` 0 ⇒ ` 0} {A = `ℕ} ⊢id
      ≡ sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)
  _ = refl

  -- a Δ-entry deeper than the Λ variable stays accessible: at
  -- Δ = rvld `ℕ ∷ [],
  -- the body λx:Y. x uses index 1, which lands in the Γ-slot part of baseS.
  ⊢idY : (abst ∷ rvld `ℕ ∷ []) ∣ [] ⊢ ƛ ` 1 ∙ ` 0 ⦂ (` 1 ⇒ ` 1)
  ⊢idY = ⊢ƛ (wf-var (skip-abst here-rvld)) (⊢` here)

  _ : scB-bridge {Δ = rvld `ℕ ∷ []} {B = ` 1 ⇒ ` 1} {A = `𝔹} ⊢idY
      ≡ sc-⇒ (sc-var (thereᵒ hereᵒ)) (sc-var (thereᵒ hereᵒ))
  _ = refl

  -- ⊢ty-wf on an (env) wrapper: the external face of Example 8's boundary
  _ : Γ₈ ⊢ (` 0 ⇒ ` 0)
  _ = ⊢ty-wf ⊢[]
        (env (bwf↓ (skip-abst here) refl wf-ℕ
               (bwf↑ (wf-var here-abst) bwf[]))
             (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
             (⊢ƛ (wf-var here-abst) (⊢` here)))

  -- the PARALLEL face, on Boundary's example ↑Y:=Y′ , ↑Y′:=𝔹 over Δch = Y′:=𝔹:
  -- Y's external face is the exterior variable Y′ (NOT 𝔹, as the reverted
  -- telescope would have folded it), and ρᵇ-lookup-wf is now a lookup
  _ : Δch ⊢ ` 0
  _ = ρᵇ-lookup-wf {Δ = Δch} {Ψᵗ = intOf Δch Θch} {Θ = Θch}
                   (bwf↑ (wf-var here-rvld) (bwf↑ wf-𝔹 bwf[])) 0 hereᵒ
