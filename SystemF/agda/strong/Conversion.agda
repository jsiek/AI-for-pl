module strong.Conversion where

-- Strong System F — CONVERSIONS, the FACE half of the boundary.
--
-- The grammar and the names are GTSF's (see GTSF/Conversion.agda,
-- GTSF/Coercions.agda): id / seal / unseal / _↦_ / `∀.  The echo is
-- deliberate — Jeremy's Q3 answer was "use Conversion for relating the
-- interior face to the exterior face", and this is that judgement, with
-- GTSF's two mutually defined directions (↑ˢ / ↓ˢ) merged into ONE family
-- indexed by a POLARITY (`conv-fun` flips on domains).
--
-- Conversions are REP-FREE by construction: `seal` and `unseal` carry a
-- NAME, never a spelling, and the rep is read by an OWNER LOOKUP on the
-- type context (`Δ ∋ X := A`).  That is what makes Q4's cancel face-equation
-- definitional (proof/CancelFaces.agda) and what makes both transports
-- below hypothesis-free.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.Ctx

private
  variable
    Δ Δ′ : Ctxᵗ
    A A′ B B′ : Ty
    X Y : ℕ
    ρ : Renameᵗ

------------------------------------------------------------------------
-- 1.  The grammar
------------------------------------------------------------------------

-- `id A` is restricted to BASE TYPES AND VARIABLES by the typing judgment
-- (conv-id / conv-idv) and by the classification in strong.Terms (A-idb
-- needs Base A, I-idv needs a variable payload); compound identities stay
-- structural (`idc` below).
data Conv : Set where
  id     : Ty → Conv          -- ACTIVE at a base type, INERT at a variable
  seal   : ℕ → Conv           -- seal   at the owner named        INERT
  unseal : ℕ → Conv           -- unseal at the owner named        ACTIVE
  _↦_    : Conv → Conv → Conv -- s ↦ t, contravariant domain      INERT
  `∀     : Conv → Conv        -- ∀ s                              INERT

infixr 7 _↦_

renᶜ : Renameᵗ → Conv → Conv
renᶜ ρ (id A)      = id (renameᵗ ρ A)
renᶜ ρ (seal X)    = seal (ρ X)
renᶜ ρ (unseal X)  = unseal (ρ X)
renᶜ ρ (s ↦ t)     = renᶜ ρ s ↦ renᶜ ρ t
renᶜ ρ (`∀ s)      = `∀ (renᶜ (extᵗ ρ) s)

-- Polarity.  `↑ˢ` unseals at positive positions (a REVEAL face), `↓ˢ` seals
-- at positive positions (a CONCEAL face), and `conv-fun` flips on domains.
data Pol : Set where
  ↑ˢ ↓ˢ : Pol

flip : Pol → Pol
flip ↑ˢ = ↓ˢ
flip ↓ˢ = ↑ˢ

flip-flip : (p : Pol) → flip (flip p) ≡ p
flip-flip ↑ˢ = refl
flip-flip ↓ˢ = refl

------------------------------------------------------------------------
-- 2.  The typing judgment
------------------------------------------------------------------------

-- Δ ⊢ c ∶ A ⇝ B ∙ p   —   c converts the INTERIOR face A to the EXTERIOR
-- face B, both read on the type context Δ (the FACE CONTEXT: the type context at which the
-- boundary's owners are live).  Every rep is read by NAME from Δ.
infix 4 _⊢_∶_⇝_∙_
data _⊢_∶_⇝_∙_ : Ctxᵗ → Conv → Ty → Ty → Pol → Set where

  conv-id : ∀ {p} → Base A
      --------------------------------
    → Δ ⊢ id A ∶ A ⇝ A ∙ p

  conv-idv : ∀ {p} → Δ ∋tv X
      --------------------------------
    → Δ ⊢ id (` X) ∶ ` X ⇝ ` X ∙ p

  -- REVEAL: the interior sees the abstract name, the exterior its rep.
  conv-unseal : Δ ∋ X := A
      --------------------------------
    → Δ ⊢ unseal X ∶ ` X ⇝ A ∙ ↑ˢ

  -- CONCEAL: the interior sees the rep, the exterior the abstract name.
  -- THE SOUNDNESS GATE: a seal must cite a LIVE OWNER on its type context.
  conv-seal : Δ ∋ X := A
      --------------------------------
    → Δ ⊢ seal X ∶ A ⇝ ` X ∙ ↓ˢ

  conv-fun : ∀ {p s t}
    → Δ ⊢ s ∶ A′ ⇝ A ∙ flip p → Δ ⊢ t ∶ B ⇝ B′ ∙ p
      ----------------------------------------------
    → Δ ⊢ s ↦ t ∶ (A ⇒ B) ⇝ (A′ ⇒ B′) ∙ p

  conv-all : ∀ {p s} → (abst ∷ Δ) ⊢ s ∶ A ⇝ B ∙ p
      --------------------------------------
    → Δ ⊢ `∀ s ∶ `∀ A ⇝ `∀ B ∙ p

------------------------------------------------------------------------
-- 3.  The identity conversion at an arbitrary type
------------------------------------------------------------------------

idc : Ty → Conv
idc (` X)   = id (` X)
idc `ℕ      = id `ℕ
idc `𝔹      = id `𝔹
idc (A ⇒ B) = idc A ↦ idc B
idc (`∀ A)  = `∀ (idc A)

idc-⊢ : ∀ {p} → Δ ⊢ᵗ A → Δ ⊢ idc A ∶ A ⇝ A ∙ p
idc-⊢ (wf-var tv)  = conv-idv tv
idc-⊢ wf-ℕ         = conv-id base-ℕ
idc-⊢ wf-𝔹         = conv-id base-𝔹
idc-⊢ (wf-⇒ wA wB) = conv-fun (idc-⊢ wA) (idc-⊢ wB)
idc-⊢ (wf-∀ wA)    = conv-all (idc-⊢ wA)

------------------------------------------------------------------------
-- 4.  TRANSPORT I — type context renaming (the ⊢renameᵗ analogue)
------------------------------------------------------------------------

-- A context-indexed conversion typing moves along ANY type context renaming, with NO
-- hypothesis beyond `Ren` itself: no SkelEq, no starOnly, no unfolding, no
-- second chance.  The `conv-unseal`/`conv-seal` cases are literally
-- `ren-kn` — the name is carried, and the rep comes back out of the target
-- type context already renamed.
conv-ren : ∀ {p c} → Ren ρ Δ Δ′
  → Δ  ⊢ c ∶ A ⇝ B ∙ p
    -----------------------------------------------------------
  → Δ′ ⊢ renᶜ ρ c ∶ renameᵗ ρ A ⇝ renameᵗ ρ B ∙ p
conv-ren {ρ = ρ} r (conv-id bA)
  rewrite base-ren {A = _} {ρ = ρ} bA  = conv-id bA
conv-ren r (conv-idv tv)     = conv-idv (ren-tv r tv)
conv-ren r (conv-unseal d)   = conv-unseal (ren-kn r d)
conv-ren r (conv-seal d)     = conv-seal (ren-kn r d)
conv-ren r (conv-fun s t)    = conv-fun (conv-ren r s) (conv-ren r t)
conv-ren r (conv-all s)      = conv-all (conv-ren (ren-ext r) s)

------------------------------------------------------------------------
-- 5.  TRANSPORT II — knowledge refinement (the ⊢retag analogue)
------------------------------------------------------------------------

-- Knowledge refinement preserves conversion typing with the FACES
-- UNCHANGED — no ≈, no unfolding, no retagging of the types.
conv-⊑ : ∀ {p c} → Δ ⊑ Δ′
  → Δ  ⊢ c ∶ A ⇝ B ∙ p
    ------------------------
  → Δ′ ⊢ c ∶ A ⇝ B ∙ p
conv-⊑ ls (conv-id bA)     = conv-id bA
conv-⊑ ls (conv-idv tv)    = conv-idv (⊑-tv ls tv)
conv-⊑ ls (conv-unseal d)  = conv-unseal (⊑-kn ls d)
conv-⊑ ls (conv-seal d)    = conv-seal (⊑-kn ls d)
conv-⊑ ls (conv-fun s t)   = conv-fun (conv-⊑ ls s) (conv-⊑ ls t)
conv-⊑ ls (conv-all s)     = conv-all (conv-⊑ (le∷ le-aa ls) s)

------------------------------------------------------------------------
-- 6.  Face inversions
------------------------------------------------------------------------

-- Every rep a face mentions IS the owner's rep — there is no second
-- spelling, which is why the §9m ≡/≈ gap cannot arise.
seal-face-is-the-owners-rep : ∀ {p}
  → Δ ⊢ seal X ∶ A ⇝ B ∙ p → Δ ∋ X := A
seal-face-is-the-owners-rep (conv-seal d) = d

unseal-face-is-the-owners-rep : ∀ {p}
  → Δ ⊢ unseal X ∶ A ⇝ B ∙ p → Δ ∋ X := B
unseal-face-is-the-owners-rep (conv-unseal d) = d

conv-unseal-src : ∀ {p} → Δ ⊢ unseal X ∶ A ⇝ B ∙ p → A ≡ ` X
conv-unseal-src (conv-unseal _) = refl

conv-seal-tgt : ∀ {p} → Δ ⊢ seal X ∶ A ⇝ B ∙ p → B ≡ ` X
conv-seal-tgt (conv-seal _) = refl

conv-idv-src : ∀ {p} → Δ ⊢ id (` X) ∶ A ⇝ B ∙ p → A ≡ ` X
conv-idv-src (conv-idv _) = refl

conv-idv-tgt : ∀ {p} → Δ ⊢ id (` X) ∶ A ⇝ B ∙ p → B ≡ ` X
conv-idv-tgt (conv-idv _) = refl

conv-id-base-src : ∀ {C p} → Base A → Δ ⊢ id A ∶ B ⇝ C ∙ p → B ≡ A
conv-id-base-src bA (conv-id _)  = refl
conv-id-base-src () (conv-idv _)

conv-id-refl : ∀ {C p} → Δ ⊢ id A ∶ B ⇝ C ∙ p → B ≡ C
conv-id-refl (conv-id _)  = refl
conv-id-refl (conv-idv _) = refl
