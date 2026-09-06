module strong.Conversion where

-- Strong System F — CONVERSIONS, the `c` of a boundary `M ⟪ Θ , c ⟫`.
--
-- The grammar and the names are GTSF's (see GTSF/Conversion.agda,
-- GTSF/Coercions.agda): id / seal / unseal / _↦_ / `∀.  The echo is
-- deliberate — Jeremy's Q3 answer was "use Conversion for relating the
-- interior type to the exterior type", and this is that judgement, with
-- GTSF's two mutually defined directions merged into ONE family.
--
-- NO POLARITY (Jeremy's ruling, 2026-09-06).  The judgement carried a
-- global index `p` that fixed `unseal` to a REVEAL position and `seal` to
-- a CONCEAL one, flipping on `conv-fun`'s domain.  It is REDUNDANT: the
-- discipline it enforced is PER TYPE VARIABLE, and `env` already enforces
-- it with the FRAMES — a LOCKED X is masked in `interior`, so it cannot sit
-- on the interior side of a leaf, and a BOUND X is not in the image of
-- `shiftBy`, so it cannot sit on the exterior side.  Dropping `p` is what
-- makes TyPeelR's preservation case a theorem at every ∀ conversion
-- rather than only at a reveal one (proof/Preserve.preserve-TyPeelR).
--
-- Conversions are REP-FREE by construction: `seal` and `unseal` carry a
-- NAME, never a spelling, and the rep is read by an OWNER LOOKUP on the
-- type context (`Δ ∋ X := A`).  That is what makes Q4's cancel type
-- equation definitional (proof/MoveScope.agda) and what makes both transports
-- below hypothesis-free.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
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
-- structural (`mkId` below).
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

------------------------------------------------------------------------
-- 2.  The typing judgment
------------------------------------------------------------------------

-- Δ ⊢ c ∶ A ⇝ B   —   c converts the SOURCE type A to the TARGET type
-- B, both read on the type context Δ (the CONVERSION CONTEXT: the type
-- context at which the boundary's owners are live).  Every rep is read by
-- NAME from Δ.  `conv-fun` is CONTRAVARIANT in its domain — that is the
-- only trace the retired polarity index leaves.
infix 4 _⊢_∶_⇝_
data _⊢_∶_⇝_ : Ctxᵗ → Conv → Ty → Ty → Set where

  conv-id : Base A
      --------------------------------
    → Δ ⊢ id A ∶ A ⇝ A

  conv-idv : Δ ∋tv X
      --------------------------------
    → Δ ⊢ id (` X) ∶ ` X ⇝ ` X

  -- REVEAL: the interior sees the abstract name, the exterior its rep.
  conv-unseal : Δ ∋ X := A
      --------------------------------
    → Δ ⊢ unseal X ∶ ` X ⇝ A

  -- CONCEAL: the interior sees the rep, the exterior the abstract name.
  -- THE SOUNDNESS GATE: a seal must cite a LIVE OWNER on its type context.
  conv-seal : Δ ∋ X := A
      --------------------------------
    → Δ ⊢ seal X ∶ A ⇝ ` X

  conv-fun : ∀ {s t}
    → Δ ⊢ s ∶ A′ ⇝ A → Δ ⊢ t ∶ B ⇝ B′
      ----------------------------------------------
    → Δ ⊢ s ↦ t ∶ (A ⇒ B) ⇝ (A′ ⇒ B′)

  conv-all : ∀ {s} → (abst ∷ Δ) ⊢ s ∶ A ⇝ B
      --------------------------------------
    → Δ ⊢ `∀ s ∶ `∀ A ⇝ `∀ B

------------------------------------------------------------------------
-- 3.  The identity conversion at an arbitrary type
------------------------------------------------------------------------

mkId : Ty → Conv
mkId (` X)   = id (` X)
mkId `ℕ      = id `ℕ
mkId `𝔹      = id `𝔹
mkId (A ⇒ B) = mkId A ↦ mkId B
mkId (`∀ A)  = `∀ (mkId A)

mkId-⊢ : Δ ⊢ᵗ A → Δ ⊢ mkId A ∶ A ⇝ A
mkId-⊢ (wf-var tv)  = conv-idv tv
mkId-⊢ wf-ℕ         = conv-id base-ℕ
mkId-⊢ wf-𝔹         = conv-id base-𝔹
mkId-⊢ (wf-⇒ wA wB) = conv-fun (mkId-⊢ wA) (mkId-⊢ wB)
mkId-⊢ (wf-∀ wA)    = conv-all (mkId-⊢ wA)

------------------------------------------------------------------------
-- 4.  TRANSPORT I — type context renaming (the ⊢renameᵗ analogue)
------------------------------------------------------------------------

-- A context-indexed conversion typing moves along ANY type context renaming, with NO
-- hypothesis beyond `Ren` itself: no SkelEq, no starOnly, no unfolding, no
-- second chance.  The `conv-unseal`/`conv-seal` cases are literally
-- `ren-kn` — the name is carried, and the rep comes back out of the target
-- type context already renamed.
conv-ren : ∀ {c} → Ren ρ Δ Δ′
  → Δ  ⊢ c ∶ A ⇝ B
    -----------------------------------------------
  → Δ′ ⊢ renᶜ ρ c ∶ renameᵗ ρ A ⇝ renameᵗ ρ B
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

-- Knowledge refinement preserves conversion typing with the SOURCE AND
-- TARGET TYPES UNCHANGED — no ≈, no unfolding, no retagging of the types.
conv-⊑ : ∀ {c} → Δ ⊑ Δ′
  → Δ  ⊢ c ∶ A ⇝ B
    ------------------------
  → Δ′ ⊢ c ∶ A ⇝ B
conv-⊑ ls (conv-id bA)     = conv-id bA
conv-⊑ ls (conv-idv tv)    = conv-idv (⊑-tv ls tv)
conv-⊑ ls (conv-unseal d)  = conv-unseal (⊑-kn ls d)
conv-⊑ ls (conv-seal d)    = conv-seal (⊑-kn ls d)
conv-⊑ ls (conv-fun s t)   = conv-fun (conv-⊑ ls s) (conv-⊑ ls t)
conv-⊑ ls (conv-all s)     = conv-all (conv-⊑ (le∷ le-aa ls) s)

------------------------------------------------------------------------
-- 6.  Conversion inversions
------------------------------------------------------------------------

-- Every rep a conversion mentions IS the owner's rep — there is no second
-- spelling, which is why the §9m ≡/≈ gap cannot arise.
seal-source-is-rep :
  Δ ⊢ seal X ∶ A ⇝ B → Δ ∋ X := A
seal-source-is-rep (conv-seal d) = d

unseal-target-is-rep :
  Δ ⊢ unseal X ∶ A ⇝ B → Δ ∋ X := B
unseal-target-is-rep (conv-unseal d) = d

conv-unseal-src : Δ ⊢ unseal X ∶ A ⇝ B → A ≡ ` X
conv-unseal-src (conv-unseal _) = refl

conv-seal-tgt : Δ ⊢ seal X ∶ A ⇝ B → B ≡ ` X
conv-seal-tgt (conv-seal _) = refl

conv-idv-src : Δ ⊢ id (` X) ∶ A ⇝ B → A ≡ ` X
conv-idv-src (conv-idv _) = refl

conv-idv-tgt : Δ ⊢ id (` X) ∶ A ⇝ B → B ≡ ` X
conv-idv-tgt (conv-idv _) = refl

conv-id-base-src : ∀ {C} → Base A → Δ ⊢ id A ∶ B ⇝ C → B ≡ A
conv-id-base-src bA (conv-id _)  = refl
conv-id-base-src () (conv-idv _)

conv-id-refl : ∀ {C} → Δ ⊢ id A ∶ B ⇝ C → B ≡ C
conv-id-refl (conv-id _)  = refl
conv-id-refl (conv-idv _) = refl

-- A ∀ conversion's body, as an inversion that does NOT have to see
-- through `shiftBy`: `env` pins the target type to `shiftBy (numBinds Θ) Bₑ`,
-- which is a stuck term, so TyPeelR's premise is recovered by this lemma rather
-- than by matching `conv-all` directly.
conv-all-inv : ∀ {s A B} → Δ ⊢ `∀ s ∶ A ⇝ B
  → Σ[ A₀ ∈ Ty ] Σ[ B₀ ∈ Ty ]
      ((A ≡ `∀ A₀) × (B ≡ `∀ B₀) × ((abst ∷ Δ) ⊢ s ∶ A₀ ⇝ B₀))
conv-all-inv (conv-all ⊢s) = _ , _ , refl , refl , ⊢s

------------------------------------------------------------------------
-- 7.  THE TYPES ARE A FUNCTION OF THE CONVERSION AND THE TYPE CONTEXT
------------------------------------------------------------------------

-- A conversion determines BOTH its types: `id` carries its own, a
-- `seal`/`unseal` reads its rep by the owner lookup (`∋:=-det`), and
-- `↦`/`` `∀ `` are structural.  This is what makes TyPeelR deterministic even
-- though its pushed-in annotation is premise-determined rather than
-- syntactic (strong.Reduction, `det`).
conv-types-unique : ∀ {c A A′ B B′}
  → Δ ⊢ c ∶ A  ⇝ B
  → Δ ⊢ c ∶ A′ ⇝ B′
    ----------------------
  → (A ≡ A′) × (B ≡ B′)
conv-types-unique (conv-id b)     (conv-id b′)     = refl , refl
conv-types-unique (conv-id ())    (conv-idv tv′)
conv-types-unique (conv-idv tv)   (conv-id ())
conv-types-unique (conv-idv tv)   (conv-idv tv′)   = refl , refl
conv-types-unique (conv-unseal d) (conv-unseal d′) = refl , ∋:=-det d d′
conv-types-unique (conv-seal d)   (conv-seal d′)   = ∋:=-det d d′ , refl
conv-types-unique (conv-fun s t)  (conv-fun s′ t′)
  with conv-types-unique s s′ | conv-types-unique t t′
... | refl , refl | refl , refl = refl , refl
conv-types-unique (conv-all s)    (conv-all s′)
  with conv-types-unique s s′
... | refl , refl = refl , refl

conv-src-unique : ∀ {c A A′ B B′}
  → Δ ⊢ c ∶ A ⇝ B → Δ ⊢ c ∶ A′ ⇝ B′ → A ≡ A′
conv-src-unique ⊢c ⊢c′ with conv-types-unique ⊢c ⊢c′
... | eq , _ = eq
