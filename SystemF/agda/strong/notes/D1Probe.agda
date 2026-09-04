module strong.notes.D1Probe where

-- ADVERSARIAL DESIGN PROBE for DEVIATION (D1) — the comparison-free
-- (bwf-↓x) (notes/DECISIONS.md "THE X-LICENSE INSTALL … (D1)";
-- notes/DualLicenseDesign.md §5; notes/InstallGauntlet.agda §7b).
--
-- Everything is run against the LIVE strong.* modules; notes/InstallGauntlet
-- is imported read-only for its shapes (Γ★, Θ★, dualᵛ, Δw, ρ₁, Θ★w, and the
-- ¬x-rep-match-ren≈ witness).  Nothing here is re-derived that is already
-- proven there.
--
-- CONTENTS
--   §1  THE ROOT CAUSE, FORMALLY.  xrep-transport / cnc-transport on the
--       general shapes; the coincidence lemma for non-absorbed renamings;
--       the general ABSORPTION theorem (intRen-suc-id) and the structural
--       fact that every x-entry sits on a boundary with a conceal, so the
--       absorption is FORCED, not accidental; two divergence witnesses and
--       one class-boundary witness where the comparison survives.
--   §2  THE REBUILD-RELATIVE COMPARISON (Jeremy's re-alignment instinct).
--       RepMatchᴿ; xrep-stored (general); holds at every dual's birth ON
--       THE NOSE; REFUTED under an absorbed renaming, with the deeper
--       reason (the rebuild is not even ≼≈-above the renamed exterior).
--   §3  FACES: neither face law mentions the entry (citation only).
--   §4  MERGE-CANCEL, the real consumer.  cancel-agree-x: the ENTRY side is
--       pinned (theorem) but the CONCEAL side is free — and the free side
--       is not a hygiene matter: ⊢Tg exports a ℕ at a Λ-bound variable, and
--       ⊢Tbad resurrects `bad` through the x-clause.  The deleting cancel
--       has NO agreed rep on such a pair, machine-checked as a face failure.
--   §5  THE TOPLAS THREE-AGENT ADVERSARY, in our syntax.  Their shape does
--       not reach our cancel clause at all (it is conceal-of-conceal), and
--       our merge on it keeps both agents' knowledge.  The adversary that
--       DOES bite is ours, from §4.
--   §6  APPEND-ONLY + FACES-AGREE STRIP.  Both refuted: append-only leaves
--       a conceal index with nowhere to point (¬bwf-append), and the strip
--       needs an interior→exterior retyping it cannot have (¬⊢strip).

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat using (_<?_; _≤?_)
open import Data.Nat.Properties using (m+n∸m≡n)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans)
open import strong.Types
open import strong.Context
open import strong.Unfold
open import strong.Boundary
open import strong.BReduction
open import strong.notes.InstallGauntlet

------------------------------------------------------------------------
-- §0.  WHAT IS COMPARED, AND WHERE EACH COPY LIVES.
--
-- (bwf-↓x)'s two reps, with their homes spelled out (this is the whole of
-- Jeremy's question (2)):
--
--   Δ            the boundary Θ's exterior
--   Ψ = intOf Δ Θ   its interior; slot j carries  xrvld A′  with A′ a
--                   Δ-TYPE ("readable one level OUT")
--   Θᵈ           a boundary whose exterior is Ψ (for Wrap, the dual)
--   Ψᵈ = intOf Ψ Θᵈ  its interior; a conceal ↓j:=A of Θᵈ has A a Ψᵈ-TYPE
--
-- So A′ : Δ and A : Ψᵈ.  notes/DualLicenseDesign.md §2 says "the homes
-- align … both live over Ψ"; they do NOT.  They are identified only by the
-- REBUILD Δ ≼≈ Ψᵈ (strong.DualDef's DualInt≈), which holds AT THE DUAL'S
-- BIRTH and is not a renaming-stable identification.  §1 turns that into
-- the divergence characterisation and §2 into the verdict.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §1.  THE ROOT CAUSE, FORMALLY
--
-- §1.1  The two transports, on the general shapes.  ⊢renameᵀ's hypotheses
-- (Mono ρ, the ∋tv / ∋:= / ∋:=x transports) move the two copies by DIFFERENT
-- maps, and the split is visible in one line of strong.BReduction:
--
--     entRen₂ ρ f (rvld A)  = rvld  (renameᵗ f A)      f = interior
--     entRen₂ ρ f (xrvld A) = xrvld (renameᵗ ρ A)      ρ = EXTERIOR
--
-- so an x-rep moves by the exterior ρ (and ∋:=x-int hands exactly that on
-- in the reveal block), while renᴮ moves a conceal rep by the INDUCED
-- INTERIOR renaming ir.
------------------------------------------------------------------------

-- the x-entry's copy: recomputed from renᴮ's image of the STORED reveal rep,
-- i.e. moved by ρ.  (Composed out of the live ⟦⟧-ren; nothing new.)
xrep-transport : ∀ {ρ} → Mono ρ → ∀ Θ j A → j < revs Θ
  → ⟦ Θ ⟧ᴴ j A ≡ xrvld A
  → ⟦ renᴮ ρ (intRen ρ Θ) Θ ⟧ᴴ j (renameᵗ ρ A) ≡ xrvld (renameᵗ ρ A)
xrep-transport {ρ} mono Θ j A lt e =
  trans (⟦⟧-ren mono Θ j A lt)
        (cong (entRen₂ ρ (restrictRen j (intRen ρ Θ))) e)

-- the term's copy: moved by the interior renaming ir, whatever ir is
cnc-transport : ∀ (ρ ir : ℕ → ℕ) X A Ξ
  → renᴮ ρ ir (cnc X A ∷ Ξ) ≡ cnc (ρ X) (renameᵗ ir A) ∷ renᴮ ρ ir Ξ
cnc-transport ρ ir X A Ξ = refl

------------------------------------------------------------------------
-- §1.2  THE COINCIDENCE LEMMA.  The two copies stay equal exactly when the
-- two maps agree on the REP'S SUPPORT — its free variables, binder-aware.
------------------------------------------------------------------------

data AgOn (f g : ℕ → ℕ) : Ty → Set where
  ag-var : ∀ {X} → f X ≡ g X                 → AgOn f g (` X)
  ag-ℕ   :                                     AgOn f g `ℕ
  ag-𝔹   :                                     AgOn f g `𝔹
  ag-⇒   : ∀ {A B} → AgOn f g A → AgOn f g B → AgOn f g (A ⇒ B)
  ag-∀   : ∀ {A} → AgOn (extᵗ f) (extᵗ g) A  → AgOn f g (`∀ A)

-- CLOSED reps agree with everything — remember this for §4
ag-closed⇒ : ∀ {f g} → AgOn f g (`ℕ ⇒ `ℕ)
ag-closed⇒ = ag-⇒ ag-ℕ ag-ℕ

rename-agree : ∀ {f g} A → AgOn f g A → renameᵗ f A ≡ renameᵗ g A
rename-agree (` X)   (ag-var e)   = cong `_ e
rename-agree `ℕ      ag-ℕ         = refl
rename-agree `𝔹      ag-𝔹         = refl
rename-agree (A ⇒ B) (ag-⇒ a b)   = cong₂ _⇒_ (rename-agree A a)
                                              (rename-agree B b)
rename-agree (`∀ A)  (ag-∀ a)     = cong `∀ (rename-agree A a)

-- THE COINCIDENCE.  ir the interior renaming, ρ the exterior one: where they
-- agree on the rep's support, the x-rep's copy and the conceal's copy move
-- together and a rep comparison would survive the renaming.
xcnc-coincide : ∀ {ρ ir} A → AgOn ir ρ A → renameᵗ ir A ≡ renameᵗ ρ A
xcnc-coincide A ag = rename-agree A ag

------------------------------------------------------------------------
-- §1.3  ABSORPTION, IN GENERAL.  For the weakening ρ = suc that every
-- ⊢renameᵀ use at a Λ performs, the induced interior renaming of ANY
-- boundary that conceals something is the IDENTITY — it absorbs the shift.
-- (restrictRen c suc is pointwise the identity; strong.BReduction says so
-- for hk-suc, and here it is the whole divergence.)
------------------------------------------------------------------------

restrictRen-suc : ∀ c j → restrictRen c suc j ≡ j
restrictRen-suc c j = m+n∸m≡n (suc (suc c)) j

liftⁿ-pt-id : ∀ r (f : ℕ → ℕ) → (∀ j → f j ≡ j) → ∀ j → liftⁿ r f j ≡ j
liftⁿ-pt-id zero    f h j       = h j
liftⁿ-pt-id (suc r) f h zero    = refl
liftⁿ-pt-id (suc r) f h (suc j) = cong suc (liftⁿ-pt-id r f h j)

-- THE ABSORPTION THEOREM
intRen-suc-id : ∀ Θ c → cmax Θ ≡ suc c → ∀ j → intRen suc Θ j ≡ j
intRen-suc-id Θ c e j
  rewrite e = liftⁿ-pt-id (revs Θ) (restrictRen c suc) (restrictRen-suc c) j

-- … AND IT IS FORCED, NOT ACCIDENTAL.  An x-entry is minted only where the
-- rep's reading is inexpressible; the operative guard is `bfree`, and a
-- bfree failure means the rep names a BLOCKED slot, which only a conceal can
-- create.  So every boundary carrying an x-entry has cmax > 0, and by
-- intRen-suc-id its interior renaming absorbs every weakening.
-- (The other guard, dfree, can fail only when a CONCEAL rep reaches a reveal
-- slot — also a conceal.  Only the bfree half is proven here.)
bfree-needs-conceal : ∀ Θ d A → bfree Θ d A ≡ false → 0 < cmax Θ
bfree-needs-conceal Θ d (` X) e with X <? d
bfree-needs-conceal Θ d (` X) () | yes _
bfree-needs-conceal Θ d (` X) e  | no  _ with cmax Θ ≤? (X ∸ d)
bfree-needs-conceal Θ d (` X) () | no _ | yes _
bfree-needs-conceal Θ d (` X) e  | no _ | no ¬le = go (cmax Θ) ¬le
  where go : ∀ c → ¬ (c ≤ X ∸ d) → 0 < c
        go zero    ¬p = ⊥-elim (¬p z≤n)
        go (suc c) ¬p = s≤s z≤n
bfree-needs-conceal Θ d `ℕ ()
bfree-needs-conceal Θ d `𝔹 ()
bfree-needs-conceal Θ d (A ⇒ B) e with bfree Θ d A in eA
bfree-needs-conceal Θ d (A ⇒ B) e | false =
  bfree-needs-conceal Θ d A eA
bfree-needs-conceal Θ d (A ⇒ B) e | true  =
  bfree-needs-conceal Θ d B e
bfree-needs-conceal Θ d (`∀ A) e = bfree-needs-conceal Θ (suc d) A e

-- E★′'s own x-entry, through the general theorem: the entry exists because
-- bfree fails, hence Θ★ conceals, hence intRen suc Θ★ is the identity.
_ : bfree Θ★ 0 (` 0) ≡ false
_ = refl

Θ★-conceals : 0 < cmax Θ★
Θ★-conceals = bfree-needs-conceal Θ★ 0 (` 0) refl

absorbed-Θ★ : ∀ j → intRen suc Θ★ j ≡ j
absorbed-Θ★ = intRen-suc-id Θ★ 1 refl

------------------------------------------------------------------------
-- §1.4  DIVERGENCE WITNESS 1 — §7b, re-derived through §1.1–§1.3 rather
-- than by computation.  ρ = suc moves the x-rep ` 0 ↦ ` 1 while ir = id
-- freezes the conceal rep, and NEITHER comparison form survives
-- (¬x-rep-match-ren≈ is InstallGauntlet's; it is cited, not re-proven).
------------------------------------------------------------------------

-- the x-rep, by xrep-transport (Θ★w = renᴮ suc ρ₁ Θ★, ρ₁ = intRen suc Θ★)
xrep-moved : ⟦ Θ★w ⟧ᴴ 0 (renameᵗ suc (` 0)) ≡ xrvld (` 1)
xrep-moved = xrep-transport Mono-suc Θ★ 0 (` 0) (s≤s z≤n) refl

-- the conceal rep, by cnc-transport, at ir = intRen ρ₁ dualᵛ — the identity
-- (dualᵛ conceals slot 0, so §1.3 applies to it too, one level down)
dualᵛ-conceals : 0 < cmax dualᵛ
dualᵛ-conceals = s≤s z≤n

cncrep-frozen : renᴮ ρ₁ (intRen ρ₁ dualᵛ) (cnc 0 (` 0) ∷ [])
              ≡ cnc 0 (` 0) ∷ []
cncrep-frozen = refl

-- the two maps DISAGREE on the rep's support {0}: ρ 0 = 1, ir 0 = 0
¬AgOn-suc : ¬ (AgOn (intRen ρ₁ dualᵛ) suc (` 0))
¬AgOn-suc (ag-var ())

-- and the comparison fails in both forms (InstallGauntlet §7b, cited)
div₁-≡ : ¬ (intOf Δw Θ★w ∋ 0 :=x (` 0))
div₁-≡ = ¬x-rep-match-ren

div₁-≈ : ¬ ((` 0) ≈Δ̄⟨ intOf Δw Θ★w ⟩ (` 1))
div₁-≈ = ¬x-rep-match-ren≈

------------------------------------------------------------------------
-- §1.5  DIVERGENCE WITNESS 2 — a SECOND shape, so the class boundary is
-- visible: a DEEPER conceal (cmax = 3) and a rep at a deeper index.  Same
-- verdict, same cause; the displacement is ρ's, of size 1, at a different
-- slot — so the divergence is not an artefact of Θ★'s indices.
------------------------------------------------------------------------

Γ² : TCtx                              -- U(0) , Y(1) , X:=ℕ(2)
Γ² = abst ∷ abst ∷ rvld `ℕ ∷ []

Θ² : BCtx                              -- ↑Z:=Y , ↓X:=ℕ , with U,Y both dropped
Θ² = rvl (` 1) ∷ cnc 2 `ℕ ∷ []

_ : cmax Θ² ≡ 3
_ = refl

_ : intOf Γ² Θ² ≡ xrvld (` 1) ∷ []     -- the x-entry, at rep ` 1
_ = refl

Θ²-conceals : 0 < cmax Θ²
Θ²-conceals = bfree-needs-conceal Θ² 0 (` 1) refl

absorbed-Θ² : ∀ j → intRen suc Θ² j ≡ j
absorbed-Θ² = intRen-suc-id Θ² 2 refl

Θ²w : BCtx
Θ²w = renᴮ suc (intRen suc Θ²) Θ²

_ : Θ²w ≡ rvl (` 2) ∷ cnc 3 `ℕ ∷ []
_ = refl

_ : intOf (abst ∷ Γ²) Θ²w ≡ xrvld (` 2) ∷ []    -- x-rep moved ` 1 ↦ ` 2 …
_ = refl

-- … while the interior renaming that would move a conceal rep is the
-- identity, so the frozen rep ` 1 is compared against ` 2
div₂-≡ : ¬ (intOf (abst ∷ Γ²) Θ²w ∋ 0 :=x (` 1))
div₂-≡ ()

div₂-≈ : ¬ ((` 1) ≈Δ̄⟨ intOf (abst ∷ Γ²) Θ²w ⟩ (` 2))
div₂-≈ (≈unf ())

------------------------------------------------------------------------
-- §1.6  THE CLASS BOUNDARY — a renaming that is NOT absorbed on the rep's
-- support, where the comparison SURVIVES.  Insert the fresh slot DEEPER
-- than cmax: ρ = liftⁿ 2 suc keeps slots 0,1 fixed, so it agrees with the
-- induced interior renaming exactly on the rep's support {0}.
------------------------------------------------------------------------

ρ³ : ℕ → ℕ
ρ³ = liftⁿ 2 suc

Mono-ρ³ : Mono ρ³
Mono-ρ³ = Mono-liftⁿ 2 Mono-suc

_ : ρ³ 0 ≡ 0
_ = refl

_ : intRen ρ³ Θ★ 0 ≡ 0                 -- agrees with ρ³ at the rep's slot
_ = refl

AgOn-ρ³ : AgOn (intRen ρ³ Θ★) ρ³ (` 0)
AgOn-ρ³ = ag-var refl

conv-ρ³ : renameᵗ (intRen ρ³ Θ★) (` 0) ≡ renameᵗ ρ³ (` 0)
conv-ρ³ = xcnc-coincide (` 0) AgOn-ρ³

-- and the comparison the design wanted DOES hold after this renaming
Θ★³ : BCtx
Θ★³ = renᴮ ρ³ (intRen ρ³ Θ★) Θ★

Δ³ : TCtx                              -- Γ★ with a fresh slot inserted DEEPER
Δ³ = abst ∷ rvld `ℕ ∷ abst ∷ []

_ : Θ★³ ≡ rvl (` 0) ∷ cnc 1 `ℕ ∷ []
_ = refl

_ : intOf Δ³ Θ★³ ≡ xrvld (` 0) ∷ abst ∷ []
_ = refl

conv-ok³ : intOf Δ³ Θ★³ ∋ 0 :=x (` 0)
conv-ok³ = herex

-- VERDICT (§1).  CONFIRMED, and sharper than hypothesised.  The divergence
-- class is exactly
--
--     { ρ | the induced interior renaming differs from ρ
--           on the rep's support }                              (§1.2)
--
-- and by §1.3 it CONTAINS EVERY WEAKENING: an x-entry exists only on a
-- boundary that conceals (bfree-needs-conceal), and on such a boundary
-- intRen suc is the identity (intRen-suc-id) while ρ = suc displaces the
-- x-rep.  §1.6 shows the class is proper — a renaming that touches only
-- slots below the rep leaves the comparison intact — so the failure is not
-- "renaming" but "renaming that the conceal's frame absorbs".

------------------------------------------------------------------------
-- §2.  THE REBUILD-RELATIVE COMPARISON
--
-- Jeremy's instinct: compare in the coordinates where the two reps are
-- ACTUALLY USED TOGETHER, namely Θᵈ's interior intOf Ψ Θᵈ (the rebuild),
-- transporting the x-rep in along DualInt≈'s Δ ≼≈ intOf Ψ Θᵈ (which is
-- index-preserving, so the transport is the identity on syntax).
------------------------------------------------------------------------

RepMatchᴿ : TCtx → BCtx → ℕ → Ty → Set
RepMatchᴿ Ψ Θᵈ Z A =
  Σ Ty λ A′ → (Ψ ∋ Z :=x A′) × (A ≈Δ̄⟨ intOf Ψ Θᵈ ⟩ A′)

------------------------------------------------------------------------
-- §2.1  (a) IT HOLDS AT EVERY DUAL'S BIRTH, on the nose.  The general fact:
-- an x-lookup inside a boundary's reveal block returns the STORED reveal rep
-- ρᵇ Ξ k — the exact analogue of the pre-install `cancel-agree`
-- (notes/old/GroundedProbe.agda §4) for the x-entry form.
------------------------------------------------------------------------

xrep-stored : ∀ Θ j Ξ {Γ : TCtx} {A′} k → k < revs Ξ
            → (revEnts Θ j Ξ ++ Γ) ∋ k :=x A′ → A′ ≡ ρᵇ Ξ k
xrep-stored Θ j []            k       ()       p
xrep-stored Θ j (rvl A ∷ Ξ)   zero    lt       p with expr Θ j A
xrep-stored Θ j (rvl A ∷ Ξ)   zero    lt herex | false = refl
xrep-stored Θ j (rvl A ∷ Ξ)   zero    lt ()    | true
xrep-stored Θ j (rvl A ∷ Ξ)   (suc k) (s≤s lt) (skipx p) =
  xrep-stored Θ (suc j) Ξ k lt p
xrep-stored Θ j (rvl⋆ ∷ Ξ)    zero    lt       ()
xrep-stored Θ j (rvl⋆ ∷ Ξ)    (suc k) (s≤s lt) (skipx p) =
  xrep-stored Θ (suc j) Ξ k lt p
xrep-stored Θ j (cnc X A ∷ Ξ) k       lt       p =
  xrep-stored Θ j Ξ k lt p
xrep-stored Θ j (cnc⋆ X ∷ Ξ)  k       lt       p =
  xrep-stored Θ j Ξ k lt p

-- THE BIRTH THEOREM.  The dual's conceal at slot k carries ρᵇ Θ k
-- (cncOfRevs), the x-entry at slot k records ρᵇ Θ k (xrep-stored): the two
-- copies are SYNTACTICALLY EQUAL, so every form of the comparison holds.
RepMatchᴿ-birth : ∀ {Δ : TCtx} Θ k {A′} → k < revs Θ
  → intOf Δ Θ ∋ k :=x A′
  → RepMatchᴿ (intOf Δ Θ) (dualᴳ Δ Θ) k (ρᵇ Θ k)
RepMatchᴿ-birth Θ k {A′} lt p =
  A′ , p , ≡→≈ (sym (xrep-stored Θ 0 Θ k lt p))

-- the same at the syntactic strength, which is what (D1) gave up
xrep-birth-≡ : ∀ {Δ : TCtx} Θ k {A′} → k < revs Θ
  → intOf Δ Θ ∋ k :=x A′ → A′ ≡ ρᵇ Θ k
xrep-birth-≡ Θ k lt p = xrep-stored Θ 0 Θ k lt p

-- E★′'s instance
_ : RepMatchᴿ (intOf Γ★ Θ★) (dualᴳ Γ★ Θ★) 0 (` 0)
_ = RepMatchᴿ-birth {Δ = Γ★} Θ★ 0 (s≤s z≤n) xlic-E★′

------------------------------------------------------------------------
-- §2.2  (b) IT IS NOT ⊢renameᵀ-STABLE.  Under §1's absorbed weakening the
-- conceal rep is frozen at ` 0 while the x-rep moves to ` 1, and the rebuild
-- reads ` 0 as the Λ-bound Y and ` 1 as X:=ℕ — so the two differ even up to
-- unfolding IN THE REBUILD'S OWN COORDINATES.
------------------------------------------------------------------------

Ψw : TCtx                              -- the renamed interior
Ψw = intOf Δw Θ★w

_ : Ψw ≡ xrvld (` 1) ∷ []
_ = refl

rebuildw : TCtx                        -- the renamed dual's interior
rebuildw = intOf Ψw (renᴮ ρ₁ (intRen ρ₁ dualᵛ) dualᵛ)

_ : rebuildw ≡ Γ★                      -- it rebuilds Γ★, NOT Δw
_ = refl

-- the rebuild-relative comparison, REFUTED
¬RepMatchᴿ-ren : ¬ ((` 0) ≈Δ̄⟨ rebuildw ⟩ (` 1))
¬RepMatchᴿ-ren (≈unf ())

-- THE DEEPER REASON, and why no re-alignment can exist: the identification
-- of the two homes is DualInt≈'s Δ ≼≈ intOf Ψ Θᵈ, and after the weakening
-- that statement is not merely unproven but FALSE — the renamed exterior has
-- one slot more than the rebuild (≼≈ preserves length).  The dual's frame
-- width is cmax, frozen at its birth; a weakening of the exterior is exactly
-- what it cannot follow.  (This is notes/DualLicenseDesign.md §5's
-- ¬dual-ren-comm, in the form that matters for the comparison.)
¬rebuild-ren : ¬ (Δw ≼≈ rebuildw)
¬rebuild-ren (≼≈abst (≼≈abst ()))

_ : length Δw ≡ 3
_ = refl

_ : length rebuildw ≡ 2
_ = refl

-- VERDICT (§2).  (a) YES — at every dual's birth the two reps are
-- syntactically equal (RepMatchᴿ-birth / xrep-birth-≡), so the comparison is
-- free there in ANY form.  (b) NO — it is not ⊢renameᵀ-stable, and the
-- obstruction is not the choice of congruence but the coordinate systems
-- themselves: after an absorbed weakening there is no context over which
-- both reps are readable (¬rebuild-ren).  D1 IS STRUCTURAL: as long as
-- boundary well-formedness must survive ⊢renameᵀ with the hypotheses it
-- carries, the license cannot compare.  What CAN be recovered is §2.1 as a
-- BIRTH-TIME side condition on the dual construction (see §4's verdict).

------------------------------------------------------------------------
-- §3.  FACES — neither face law consumes rep-equals-entry.  CITED, not
-- re-proven: strong.BReduction's two dual face laws take (env)'s scope
-- premise and nothing else — no Bwf, no entry, no rep.
--
--   ρᵇ-dual-ty : Scoped (baseS Θ Δ) B
--              → substᵗ (ρᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B)
--                ≡ substᵗ (γᵇ Θ) B
--   γᵇ-dual-ty : Scoped (baseS Θ Δ) B
--              → substᵗ (γᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B)
--                ≡ substᵗ (ρᵇ Θ) B
--
-- Their types are re-stated here so the claim is machine-checked: if either
-- needed the rep, these definitions would not typecheck.
------------------------------------------------------------------------

faces-need-no-rep-ρ : ∀ {Δ : TCtx} Γ B Θ → Scoped (baseS Θ Δ) B
  → substᵗ (ρᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (γᵇ Θ) B
faces-need-no-rep-ρ = ρᵇ-dual-ty

faces-need-no-rep-γ : ∀ {Δ : TCtx} Γ B Θ → Scoped (baseS Θ Δ) B
  → substᵗ (γᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (ρᵇ Θ) B
faces-need-no-rep-γ = γᵇ-dual-ty

------------------------------------------------------------------------
-- §4.  MERGE-CANCEL, THE REAL CONSUMER
--
-- The cancel clause of Decision 3's  Θ₁ ⊕ Θ₂  (notes/old/MergeProbe.agda §1,
-- adapted here to the live four entry forms): a conceal of Θ₁ whose index is
-- one of Θ₂'s REVEALS cancels against that reveal and BOTH entries vanish.
-- Its soundness obligation is `cancel-agree`: the two reps of the cancelling
-- pair must be the same type, since the merged boundary type has to be
-- rewritten through that one agreed rep.
------------------------------------------------------------------------

mapL : BCtx → BCtx → BCtx              -- Θ₁'s entries, re-based Ψ₂ → Δ
mapL Θ₂ []             = []
mapL Θ₂ (rvl A ∷ Θ)    = rvl (substᵗ (outSub Θ₂) A) ∷ mapL Θ₂ Θ
mapL Θ₂ (rvl⋆ ∷ Θ)     = rvl⋆ ∷ mapL Θ₂ Θ
mapL Θ₂ (cnc X A ∷ Θ)  with X <? revs Θ₂
mapL Θ₂ (cnc X A ∷ Θ)  | yes _ = mapL Θ₂ Θ          -- *** CANCEL ***
mapL Θ₂ (cnc X A ∷ Θ)  | no  _ =
  cnc (cmax Θ₂ + (X ∸ revs Θ₂)) A ∷ mapL Θ₂ Θ
mapL Θ₂ (cnc⋆ X ∷ Θ)   with X <? revs Θ₂
mapL Θ₂ (cnc⋆ X ∷ Θ)   | yes _ = mapL Θ₂ Θ          -- *** CANCEL (⋆) ***
mapL Θ₂ (cnc⋆ X ∷ Θ)   | no  _ =
  cnc⋆ (cmax Θ₂ + (X ∸ revs Θ₂)) ∷ mapL Θ₂ Θ

mapR : BCtx → ℕ → BCtx → BCtx          -- Θ₂'s entries, re-based to Ψ₁
mapR Θ₁ j []            = []
mapR Θ₁ j (rvl A ∷ Θ)   with j <? cmax Θ₁
mapR Θ₁ j (rvl A ∷ Θ)   | yes _ = mapR Θ₁ (suc j) Θ
mapR Θ₁ j (rvl A ∷ Θ)   | no  _ = rvl A ∷ mapR Θ₁ (suc j) Θ
mapR Θ₁ j (rvl⋆ ∷ Θ)    with j <? cmax Θ₁
mapR Θ₁ j (rvl⋆ ∷ Θ)    | yes _ = mapR Θ₁ (suc j) Θ
mapR Θ₁ j (rvl⋆ ∷ Θ)    | no  _ = rvl⋆ ∷ mapR Θ₁ (suc j) Θ
mapR Θ₁ j (cnc X A ∷ Θ) = cnc X (substᵗ (rdSub Θ₁) A) ∷ mapR Θ₁ j Θ
mapR Θ₁ j (cnc⋆ X ∷ Θ)  = cnc⋆ X ∷ mapR Θ₁ j Θ

infixl 5 _⊕_
_⊕_ : BCtx → BCtx → BCtx
Θ₁ ⊕ Θ₂ = mapL Θ₂ Θ₁ ++ mapR Θ₁ 0 Θ₂

------------------------------------------------------------------------
-- §4.1  cancel-agree, ORDINARY.  Sanity: the plain cancel pair composes to
-- the EMPTY boundary, both faces agree, and redex and contractum type — so
-- Drop∅ finishes the job.  (This is MergeProbe §4b on the live judgment.)
------------------------------------------------------------------------

Θ1c Θ2c : BCtx
Θ1c = cnc 0 `ℕ ∷ []
Θ2c = rvl `ℕ ∷ []

_ : Θ1c ⊕ Θ2c ≡ []
_ = refl

⊢redex-c : [] ∣ [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ ⦂ `ℕ
⊢redex-c = env (bwf↑ wf-ℕ bwf[]) (sc-var hereᵒ)
               (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

⊢merged-c : [] ∣ [] ⊢ ($ 7) ⟪ Θ1c ⊕ Θ2c , `ℕ ⟫ ⦂ `ℕ
⊢merged-c = env bwf[] sc-ℕ ⊢$

-- and the AUTHORITY question, on this pair: the cancelled variable is Θ₂'s
-- OWN fresh reveal slot, which exists in nobody's context but Θ₂'s interior
-- — so no third party can be deprived of it.  The interiors compose exactly
-- (MergeProbe's ⊕-int, general; here by computation):
_ : intOf [] (Θ1c ⊕ Θ2c) ≡ intOf (intOf [] Θ2c) Θ1c
_ = refl

------------------------------------------------------------------------
-- §4.2  cancel-agree-x: THE ENTRY SIDE IS PINNED, THE CONCEAL SIDE IS FREE.
--
-- Pinned: §2.1's xrep-stored says the x-entry at a reveal slot records
-- exactly ρᵇ Θ₂ k.  That is the whole of what a bwf↓x derivation tells us:
--
--   bwf↓x :  Γ ∋ X :=x A′  →  starOnly Θ 0 A ≡ true  →  Ψ ⊢ A  →  …
--
-- Nothing relates A to A′.  And that is NOT a bookkeeping matter, because
-- `starOnly Θ d `ℕ = true` — a CLOSED rep claims nothing syntactically while
-- asserting "X is ℕ" semantically.  (The same hole is in the probes' original
-- interior form absOnly, which is also satisfied by every closed rep, so
-- notes/DualLicenseDesign.md §3's "the admitted residue is abstract-to-
-- abstract aliasing" understates what the clause admits.)
------------------------------------------------------------------------

Θg : BCtx                              -- ↓Z:=ℕ at E★′'s own x-slot
Θg = cnc 0 `ℕ ∷ []

starOnly-ground : starOnly Θg 0 `ℕ ≡ true
starOnly-ground = refl

-- the inner half: 7 acquires the ABSTRACT type Z, licensed by (bwf-↓x)
⊢gnd : Γz ∣ [] ⊢ ($ 7) ⟪ Θg , ` 0 ⟫ ⦂ ` 0
⊢gnd = env (bwf↓x herex refl wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$

-- *** THE X-CANCEL ADVERSARY ***  the same tower shape as E★′'s, with the
-- dual's rep Y replaced by the closed ℕ: a ℕ literal exported at the
-- Λ-BOUND Y.  It types.
Tg : Term
Tg = (($ 7) ⟪ Θg , ` 0 ⟫) ⟪ Θ★ , ` 0 ⟫

⊢Tg : Γ★ ∣ [] ⊢ Tg ⦂ ` 0
⊢Tg = env bwf-Θ★ (sc-var hereᵒ) ⊢gnd

-- the two reps of the cancelling pair, and their DISAGREEMENT: the entry
-- records ` 0 (= Y), the conceal carries `ℕ
entry-rep : (` 0) ≡ ρᵇ Θ★ 0
entry-rep = xrep-birth-≡ {Δ = Γ★} Θ★ 0 (s≤s z≤n) xlic-E★′

¬cancel-agree-x : ¬ (_≡_ {A = Ty} `ℕ (ρᵇ Θ★ 0))
¬cancel-agree-x ()

-- … and they do not agree up to unfolding either, in the rebuild (§2's
-- coordinates) or in the exterior
¬cancel-agree-x≈ : ¬ (`ℕ ≈Δ̄⟨ intOf Γz dualᵛ ⟩ (` 0))
¬cancel-agree-x≈ (≈unf ())

------------------------------------------------------------------------
-- §4.3  SO THE DELETING CANCEL HAS NO AGREED REP.  On the x-pair the
-- composite loses the slot, and the merged wrapper would need a boundary
-- type that is `ℕ internally and the variable ` 0 externally.  After the
-- delete there is no slot left to carry that: the composite's ρᵇ is the
-- identity (no reveals), so the boundary type must BE ` 0 — whose composite
-- slot is BLOCKED, so it is not even Scoped.  Merge is refuted here, and the
-- premise it is missing is exactly the one (D1) dropped.
------------------------------------------------------------------------

Θmx : BCtx
Θmx = Θg ⊕ Θ★

_ : Θmx ≡ cnc 1 `ℕ ∷ []                -- the Z slot is GONE
_ = refl

_ : baseS Θmx Γ★ ≡ blk ∷ ok ∷ []
_ = refl

-- no boundary type can name the cancelled slot …
¬Scoped-mx : ¬ Scoped (baseS Θmx Γ★) (` 0)
¬Scoped-mx (sc-var ())

-- … and the only candidate that gives the right EXTERNAL type is ` 0, whose
-- internal face is ` 0, not the `ℕ the body has (so even ignoring scope, no
-- rewriting through "the agreed rep" exists)
_ : substᵗ (ρᵇ Θmx) (` 0) ≡ ` 0
_ = refl

¬face-int-mx : ¬ (substᵗ (γᵇ Θmx) (` 0) ≡ `ℕ)
¬face-int-mx ()

------------------------------------------------------------------------
-- §4.4  THE POST-RENAMING ADVERSARY, on the LEGITIMATE pair.  Even where
-- the reps DO agree at birth — E★'s tower, the reachable Merge redex
-- (($ 5) ⟪ dualᵛ , ℕ ⟫) ⟪ Θ★ , ℕ ⟫ of InstallGauntlet §2 — an absorbed
-- weakening leaves them disagreeing in every available sense: syntactically
-- (§1.4), in the rebuild's coordinates (§2.2), and in the renamed exterior.
-- So "the reps agree" is a BIRTH-TIME property only; a Merge that fires
-- after a weakening cannot appeal to it.
------------------------------------------------------------------------

Θmg : BCtx                             -- E★'s tower, merged
Θmg = dualᵛ ⊕ Θ★

_ : Θmg ≡ rvl⋆ ∷ rvl `ℕ ∷ cnc 1 `ℕ ∷ []
_ = refl

-- the merged tower types, at the same type as the redex: the AGREEING pair
-- merges soundly (both boundary types are closed, so nothing has to be
-- rewritten through the cancelled slot)
⊢merged-★ : Γ★ ∣ [] ⊢ ($ 5) ⟪ Θmg , `ℕ ⟫ ⦂ `ℕ
⊢merged-★ =
  env (bwf⋆ (bwf↑ wf-ℕ (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[])))
      sc-ℕ ⊢$

-- but after the weakening the pair's reps have parted (cited from §1.4/§2.2)
post-ren-≢ : ¬ (intOf Δw Θ★w ∋ 0 :=x (` 0))
post-ren-≢ = div₁-≡

post-ren-≉ : ¬ ((` 0) ≈Δ̄⟨ rebuildw ⟩ (` 1))
post-ren-≉ = ¬RepMatchᴿ-ren

------------------------------------------------------------------------
-- §4.5  HOW BAD IS §4.2?  As bad as `bad`.  Replace Γ★'s Λ-bound Y by a
-- variable the exterior KNOWS to be ∀Z.Z→Z: the reveal's rep is then a
-- BLOCKED variable, so its reading is inexpressible, so the interior entry
-- is the x-one and (bwf-↓) — whose Reversal≈ premise refutes `bad`
-- (strong.Boundary's ¬⊢bad) — never runs.  `bad`'s own configuration comes
-- back through the x-clause.
------------------------------------------------------------------------

Δbad : TCtx                            -- X := ∀Z.Z→Z (0) , V := ℕ (1)
Δbad = rvld ∀ZZ ∷ rvld `ℕ ∷ []

_ : intOf Δbad Θ★ ≡ xrvld (` 0) ∷ []
_ = refl

bwf-Θ★bad : Δbad ∣ intOf Δbad Θ★ ⊢ᵇ Θ★
bwf-Θ★bad = bwf↑ (wf-var here-rvld)
                 (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ bwf[])

⊢Tbad : Δbad ∣ [] ⊢ Tg ⦂ ` 0
⊢Tbad = env bwf-Θ★bad (sc-var hereᵒ) ⊢gnd

-- the exterior's knowledge about the slot the ℕ was exported at
know-bad : Δbad ∋ 0 := ∀ZZ
know-bad = here

-- and the comparison (D1) dropped would have refused it, in EITHER form
would-refute-≡ : ¬ (_≡_ {A = Ty} `ℕ (` 0))
would-refute-≡ ()

would-refute-≈ : ¬ (`ℕ ≈Δ̄⟨ Δbad ⟩ (` 0))
would-refute-≈ (≈unf ())

-- REACHABILITY.  ⊢Tg lives at Γ★, where Y is Λ-bound; ⊢retag≈ — the very
-- transport TyBeta performs when the Λ is instantiated — carries it into a
-- context that KNOWS Y, and the tower survives unchanged.
Γ𝔹 : TCtx
Γ𝔹 = rvld `𝔹 ∷ rvld `ℕ ∷ []

Γ★≼Γ𝔹 : Γ★ ≼≈ Γ𝔹
Γ★≼Γ𝔹 = ≼≈abst (≼≈rvld ≼≈[] ≈-refl)

⊢Tg-instantiated : Γ𝔹 ∣ [] ⊢ Tg ⦂ ` 0
⊢Tg-instantiated = ⊢retag≈ Γ★≼Γ𝔹 ⊢Tg

know-𝔹 : Γ𝔹 ∋ 0 := `𝔹
know-𝔹 = here

-- VERDICT (§4).  cancel-agree-x is REFUTED, and by a term the LANDED system
-- types: ⊢Tg / ⊢Tbad.  A deleting cancel is therefore unjustifiable for
-- x-pairs — not because authority is lost (§5) but because there is no
-- agreed rep to rewrite the boundary type through (§4.3).  The two are the
-- same defect: Merge's cancel wants exactly the premise (D1) dropped.

------------------------------------------------------------------------
-- §5.  THE TOPLAS THREE-AGENT ADVERSARY (p. 1048–49; notes/
-- SyntacticTypeAbstraction.md §0's never-delete warning), IN OUR SYNTAX.
--
--   δ_i(t) = int ,  δ_j(s) = t ,  δ_k = ⊥ ,  the k-term ⌈⌈3_i⌉^t_i⌉^s_j
--
-- becomes: a context that holds both agents' knowledge, s := t over t := ℕ
-- (their chain), and two nested boundaries, the inner hiding t at ℕ and the
-- outer hiding s at t.  Collapsing the term to either single-agent form is
-- what they refute; only ⌈3⌉^s_{ij} — both contributions kept — is admissible.
------------------------------------------------------------------------

Δ₃ : TCtx                              -- s := t (0) , t := ℕ (1)
Δ₃ = rvld (` 0) ∷ rvld `ℕ ∷ []

Θo Θi : BCtx
Θo = cnc 0 (` 0) ∷ []                  -- agent j: hide s, rep t
Θi = cnc 0 `ℕ ∷ []                     -- agent i: hide t, rep ℕ

_ : intOf Δ₃ Θo ≡ rvld `ℕ ∷ []         -- Θo's interior: only t := ℕ survives
_ = refl

T₃ : Term
T₃ = (($ 3) ⟪ Θi , ` 0 ⟫) ⟪ Θo , ` 0 ⟫

⊢T₃ : Δ₃ ∣ [] ⊢ T₃ ⦂ ` 0
⊢T₃ = env (bwf↓ here (≡→≈ refl) (wf-var here-rvld) bwf[])
          (sc-var hereᵒ)
          (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

-- *** THEIR COUNTEREXAMPLE DOES NOT REACH OUR CANCEL CLAUSE. ***  Cancel
-- fires only on an inner CONCEAL of an outer REVEAL; theirs is
-- conceal-of-conceal, so ⊕ APPENDS both entries — and the middle agent's
-- contribution survives as the pushed-in rep.
_ : Θi ⊕ Θo ≡ cnc 1 `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

-- both hidings are still there, and the merged term types at the same type;
-- the middle authority ("s is t") is what discharges the second conceal's
-- reversal premise, through the chain in Δ₃ — the ≈Δ̄ congruence's own job
mid-authority : `ℕ ≈Δ̄⟨ Δ₃ ⟩ (` 1)
mid-authority = ≈unf refl

⊢merged₃ : Δ₃ ∣ [] ⊢ ($ 3) ⟪ Θi ⊕ Θo , ` 0 ⟫ ⦂ ` 0
⊢merged₃ =
  env (bwf↓ (skip-rvld here) (≡→≈ refl) wf-ℕ
            (bwf↓ here mid-authority wf-ℕ bwf[]))
      (sc-var hereᵒ) ⊢$

------------------------------------------------------------------------
-- §5.1  THE BRIDGING VARIANT THAT DOES FIRE THE CANCEL — and why the delete
-- is authority-PRESERVING there.  Give the outer boundary a reveal ↑X:=ℕ AND
-- a conceal whose rep NAMES that reveal (boundary simultaneity (i)): the
-- middle entry then genuinely bridges across the cancelled slot.  When the
-- inner ↓X:=ℕ cancels it, mapR rewrites the bridging rep through the AGREED
-- rep, so nothing dangles and both faces survive.
------------------------------------------------------------------------

Θ₂b Θ₁b : BCtx
Θ₂b = rvl `ℕ ∷ cnc 1 (` 0) ∷ []        -- ↑X:=ℕ , ↓V:=X   (V = Γ★'s slot 1)
Θ₁b = cnc 0 `ℕ ∷ []                    -- ↓X:=ℕ           (the cancel partner)

_ : intOf Γ★ Θ₂b ≡ rvld `ℕ ∷ []
_ = refl

⊢Tb : Γ★ ∣ [] ⊢ (($ 3) ⟪ Θ₁b , ` 0 ⟫) ⟪ Θ₂b , ` 0 ⟫ ⦂ `ℕ
⊢Tb = env (bwf↑ wf-ℕ (bwf↓ (skip-abst here) (≡→≈ refl)
                          (wf-var here-rvld) bwf[]))
          (sc-var hereᵒ)
          (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

-- the cancel fires, and the BRIDGING rep ` 0 is rewritten to the agreed ℕ
_ : Θ₁b ⊕ Θ₂b ≡ cnc 1 `ℕ ∷ []
_ = refl

⊢merged-b : Γ★ ∣ [] ⊢ ($ 3) ⟪ Θ₁b ⊕ Θ₂b , `ℕ ⟫ ⦂ `ℕ
⊢merged-b = env (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]) sc-ℕ ⊢$

-- VERDICT (§5).  Our deleting cancel is NOT hit by their counterexample: the
-- cancelled variable is the outer boundary's OWN fresh reveal (their "t ∉
-- Dom(δ_i)" observation, in our indices it is an index < revs Θ₂ that exists
-- only inside Θ₂'s interior), and where a sibling entry bridges across it,
-- mapR's push-in rewrites the bridge through the agreed rep (§5.1).  What
-- DOES break the delete is our own x-clause: §4.3, where there is no agreed
-- rep at all.  So the fix Merge needs is not "append instead of delete" (see
-- §6) but the comparison of §2.1.

------------------------------------------------------------------------
-- §6.  THE D1-DODGING ROUTE: APPEND-ONLY MERGE + FACES-AGREE STRIP
------------------------------------------------------------------------

-- §6.1  APPEND-ONLY IS NOT AVAILABLE TO US.  Zdancewic's [8] can append
-- because his entries are (agent, partial map) pairs over a GLOBAL type-
-- variable namespace.  Ours are de Bruijn indices read in the EXTERIOR: an
-- inner conceal of an outer reveal points at a slot that exists only in the
-- composite's own reveal block, and no conceal index can point there.
-- Keeping both entries yields a boundary that NO exterior admits.

Θ⊞ : BCtx                              -- the cancel pair, appended
Θ⊞ = cnc 0 `ℕ ∷ rvl `ℕ ∷ []

¬bwf-append : ∀ {Ψ : TCtx} → Bwf [] Ψ Θ⊞ Θ⊞ → ⊥
¬bwf-append (bwf↓  () _ _ _)
¬bwf-append (bwf↓x () _ _ _)

-- (and it is not an artefact of Δ = []: the conceal index would have to name
-- a slot of Δ, while the reveal it cancels is by construction FRESH — the
-- indices are in different spaces.)

------------------------------------------------------------------------
-- §6.2  THE FACES-AGREE STRIP.  A boundary whose two faces agree on its own
-- boundary type is inert on the TYPE …
------------------------------------------------------------------------

FacesAgree : BCtx → Ty → Set
FacesAgree Θ B₀ = substᵗ (γᵇ Θ) B₀ ≡ substᵗ (ρᵇ Θ) B₀

-- … and on the towers the condition does hold.  E★'s merged tower (§4.4):
strip-★ : FacesAgree Θmg `ℕ
strip-★ = refl

-- so E★'s tower DOES collapse to the bare value: merge (§4.4) then strip —
-- and the stripped value retypes in the exterior
⊢strip-★ : Γ★ ∣ [] ⊢ $ 5 ⦂ `ℕ
⊢strip-★ = ⊢$

-- E★′'s dual-wrapped argument, likewise: both faces of dualᵛ at its own
-- boundary type are ` 0 ⇒ ℕ, and argY retypes in Γz
strip-E★′ : FacesAgree dualᵛ (` 2 ⇒ `ℕ)
strip-E★′ = refl

⊢strip-E★′ : Γz ∣ [] ⊢ argY ⦂ (` 0 ⇒ `ℕ)
⊢strip-E★′ = ⊢ƛ (wf-var here-xrvld) ⊢$

------------------------------------------------------------------------
-- §6.3  … BUT THE STRIP'S OWN SORE.  Faces-agree is a condition on the
-- boundary TYPE ONLY; the BODY may still depend on the boundary's reveal
-- slots — through its own nested boundaries, which read their conceal
-- indices in the interior.  Here Θs = ↑X:=ℕ is inert on B₀ = ℕ, the body
-- types inside, and the contractum is UNTYPABLE.
------------------------------------------------------------------------

Θs : BCtx
Θs = rvl `ℕ ∷ []

bodys : Term                           -- (λx:X. 5) (7 ⟪ ↓X:=ℕ , X ⟫) : ℕ
bodys = (ƛ ` 0 ∙ ($ 5)) · (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫)

_ : intOf [] Θs ≡ rvld `ℕ ∷ []
_ = refl

⊢bodys : (rvld `ℕ ∷ []) ∣ [] ⊢ bodys ⦂ `ℕ
⊢bodys = ⊢· (⊢ƛ (wf-var here-rvld) ⊢$)
            (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

strip-s : FacesAgree Θs `ℕ             -- the side condition HOLDS …
strip-s = refl

⊢redex-s : [] ∣ [] ⊢ bodys ⟪ Θs , `ℕ ⟫ ⦂ `ℕ
⊢redex-s = env (bwf↑ wf-ℕ bwf[]) sc-ℕ ⊢bodys

-- … and the contractum does not type: the body's own conceal ↓X:=ℕ has no
-- slot X in the exterior.  So the faces-agree strip is UNSOUND as stated;
-- the premise it really needs is "the body retypes in the exterior", which
-- for a boundary with reveals fails, i.e. it collapses back to Drop∅.
¬⊢strip : ¬ ([] ∣ [] ⊢ bodys ⦂ `ℕ)
¬⊢strip (⊢· _ (env (bwf↓  () _ _ _) _ _))
¬⊢strip (⊢· _ (env (bwf↓x () _ _ _) _ _))

-- VERDICT (§6).  NOT a real alternative.  Append-only merge is structurally
-- unavailable in the de Bruijn/whole-Γ formulation (¬bwf-append), and the
-- faces-agree strip is unsound without an interior→exterior retyping premise
-- (¬⊢strip) that only Θ = ∅ satisfies in general — i.e. Drop∅, which is
-- already adopted.  The towers DO collapse (§6.2), but by DELETING merge +
-- strip-at-a-closed-boundary-type, which needs §4's cancel-agree anyway.

------------------------------------------------------------------------
-- §7.  THE REPAIR THAT SURVIVES §1: COMPARE SKELETONS.
--
-- §1's obstruction is precise: the two copies move by two different
-- renamings.  A comparison is therefore ⊢renameᵀ-stable iff it is invariant
-- under renaming EACH SIDE INDEPENDENTLY — and there is such a comparison
-- strictly between "nothing" (D1) and "≡ / ≈Δ̄" (refuted): equality of
-- SKELETONS, the type structure with variable identities forgotten.
--
--   * stable for FREE, under arbitrary independent renamings (skel-ren has
--     no hypotheses at all — no Mono, no transport, no absorption side
--     condition), so it can be a premise of Bwf;
--   * strong enough to refute §4.2/§4.5 (a CLOSED rep has a different
--     skeleton from the variable the entry recorded);
--   * weak enough to admit every gauntlet item the x-clause exists for
--     (E★′, E★, the ⊢3s-alias residue, and a COMPOUND blocked rep such as
--     ↑Z:=(Y⇒ℕ) whose dual conceals at (V⇒ℕ) — the case a "rep must be a
--     rep-less reveal VARIABLE" premise would have over-restricted);
--   * orthogonal to `starOnly`, which keeps refuting ⊢3n-adv (whose rep IS
--     the recorded one, so it passes SkelEq — exactly as it passes ≡ and ≈).
------------------------------------------------------------------------

data SkelEq : Ty → Ty → Set where
  sk-var : ∀ {X Y}                        → SkelEq (` X) (` Y)
  sk-ℕ   :                                  SkelEq `ℕ `ℕ
  sk-𝔹   :                                  SkelEq `𝔹 `𝔹
  sk-⇒   : ∀ {A B A′ B′} → SkelEq A A′ → SkelEq B B′
                                          → SkelEq (A ⇒ B) (A′ ⇒ B′)
  sk-∀   : ∀ {A A′} → SkelEq A A′         → SkelEq (`∀ A) (`∀ A′)

-- *** THE STABILITY THEOREM ***  no hypotheses: f and g are unrelated.
-- This is what ≡ and ≈Δ̄ cannot have (§1.4, §2.2).
skel-ren : ∀ {A B} (f g : ℕ → ℕ)
         → SkelEq A B → SkelEq (renameᵗ f A) (renameᵗ g B)
skel-ren f g sk-var       = sk-var
skel-ren f g sk-ℕ         = sk-ℕ
skel-ren f g sk-𝔹         = sk-𝔹
skel-ren f g (sk-⇒ a b)   = sk-⇒ (skel-ren f g a) (skel-ren f g b)
skel-ren f g (sk-∀ a)     = sk-∀ (skel-ren (extᵗ f) (extᵗ g) a)

-- THE REPAIRED CLAUSE, verbatim (Γ ∣ Ψ ⊢ Θ, one premise added):
--
--   (bwf-↓x)   Γ ∋ X :=ˣ A′        starOnly Θ 0 A ≡ true
--              SkelEq A A′         Ψ ⊢ A
--              ──────────────────────────────────────────
--              Γ ∣ Ψ ⊢ ↓X:=A , Θ
--
-- Its ⊢renameᵀ case needs ONE thing from the x-transport hypothesis that
-- ⊢renameᵀ does not yet promise: today `hx` gives only EXISTENCE of the
-- target's rep (Σ Ty λ A″ → Δ' ∋ ρ X :=x A″), because (bwf-↓x) does not
-- compare it.  With the premise back, hx must also say that A″ has A′'s
-- SKELETON — which is strictly weaker than DualLicenseDesign §5(i)'s
-- rejected XRen hypothesis (it does not say WHICH renaming), and which both
-- live instances already satisfy (§7.1).

-- (i) it HOLDS where the design needs it: E★′'s dual conceal ↓Z:=Y against
--     the recorded Z:=ˣY
skel-E★′ : SkelEq (` 0) (` 0)
skel-E★′ = sk-var

-- (ii) it SURVIVES the renaming that killed ≡ and ≈ (§1.4): the frozen
--      conceal rep ` 0 against the moved x-rep ` 1
skel-survives-ren : SkelEq (renameᵗ (intRen ρ₁ dualᵛ) (` 0))
                           (renameᵗ suc (` 0))
skel-survives-ren = skel-ren (intRen ρ₁ dualᵛ) suc skel-E★′

_ : SkelEq (` 0) (` 1)
_ = skel-survives-ren

-- (iii) it REFUTES §4.2/§4.5 — the ground rep against the recorded variable
¬skel-Tg : ¬ (SkelEq `ℕ (` 0))
¬skel-Tg ()

-- so ⊢gnd, ⊢Tg, ⊢Tbad, and with them §4.3's unmergeable cancel pair, all go
-- away, while the whole starOnly gauntlet is untouched:
skel-adv : SkelEq (` 0) (` 0)          -- ⊢3n-adv still passes the comparison
skel-adv = sk-var

_ : ¬ (starOnly Ξadv 0 (` 0) ≡ true)   -- … and is still refuted by starOnly
_ = ¬starOnly-adv

-- (iv) it admits a COMPOUND blocked rep, which a "rep is a ⋆-reveal
--      variable" premise would have refused
skel-compound : SkelEq (` 0 ⇒ `ℕ) (` 1 ⇒ `ℕ)
skel-compound = sk-⇒ sk-var sk-ℕ

-- and it is a genuine weakening of both refuted forms, so nothing that held
-- before is lost
≡→skel : ∀ A → SkelEq A A
≡→skel (` X)   = sk-var
≡→skel `ℕ      = sk-ℕ
≡→skel `𝔹      = sk-𝔹
≡→skel (A ⇒ B) = sk-⇒ (≡→skel A) (≡→skel B)
≡→skel (`∀ A)  = sk-∀ (≡→skel A)

------------------------------------------------------------------------
-- §7.1  THE ONE HYPOTHESIS STRENGTHENING, AND THAT IT IS FREE.  Both live
-- x-transports already move an x-rep by a RENAMING, so both preserve
-- skeletons: `hx-suc` carries the entry across verbatim, and ∋:=x-int's
-- reveal-block branch produces renameᵗ ρ A′.
------------------------------------------------------------------------

SkelX : (ℕ → ℕ) → TCtx → TCtx → Set    -- the strengthened hx
SkelX ρ Δ Δ' = ∀ {X A′} → Δ ∋ X :=x A′
             → Σ Ty λ A″ → (Δ' ∋ ρ X :=x A″) × SkelEq A′ A″

skel-ren-r : ∀ (f : ℕ → ℕ) A → SkelEq A (renameᵗ f A)
skel-ren-r f (` X)   = sk-var
skel-ren-r f `ℕ      = sk-ℕ
skel-ren-r f `𝔹      = sk-𝔹
skel-ren-r f (A ⇒ B) = sk-⇒ (skel-ren-r f A) (skel-ren-r f B)
skel-ren-r f (`∀ A)  = sk-∀ (skel-ren-r (extᵗ f) A)

-- instance 1: the weakening ⇑ᵀ uses (strong.BReduction's hx-suc)
SkelX-suc : ∀ {Δ : TCtx} {E} → SkelX suc Δ (E ∷ Δ)
SkelX-suc {A′ = A′} p = A′ , skipx p , ≡→skel A′

-- instance 2: the (env) recursion, in the reveal block — the branch where
-- the rep genuinely MOVES, by the exterior ρ (§1.1)
SkelX-mv : ∀ {ρ : ℕ → ℕ} {Δ Δ' : TCtx} {X A′}
         → Δ' ∋ ρ X :=x renameᵗ ρ A′
         → Σ Ty λ A″ → (Δ' ∋ ρ X :=x A″) × SkelEq A′ A″
SkelX-mv {ρ} {A′ = A′} q = renameᵗ ρ A′ , q , skel-ren-r ρ A′

-- so the repaired (bwf-↓x)'s renaming case closes with
--     bwf↓x (proj₁ (proj₂ (hx p)))
--           (trans (starOnly-ren Θ 0 A) so)
--           (skel-trans (skel-ren (intRen ρ Θ) (λ i → i) sk) …)
-- i.e. skeleton transitivity against hx's own SkelEq — recorded here so the
-- install has the shape:
skel-trans : ∀ {A B C} → SkelEq A B → SkelEq B C → SkelEq A C
skel-trans sk-var     sk-var     = sk-var
skel-trans sk-ℕ       sk-ℕ       = sk-ℕ
skel-trans sk-𝔹       sk-𝔹       = sk-𝔹
skel-trans (sk-⇒ a b) (sk-⇒ c d) = sk-⇒ (skel-trans a c) (skel-trans b d)
skel-trans (sk-∀ a)   (sk-∀ c)   = sk-∀ (skel-trans a c)

------------------------------------------------------------------------
-- §8.  RANKED RECOMMENDATION
--
-- 1. REPAIR THE COMPARISON, in the SKELETON form (§7).  It is the only form
--    §1 permits, it costs one premise and one hypothesis-free lemma, it
--    closes the admission hole §4.2 opened (which is a soundness matter, not
--    hygiene: ⊢Tbad is `bad`'s configuration and ⊢Tg-instantiated shows the
--    retag reaches it), and it leaves (D2)/(D3) exactly as they are.
--    Together with §2.1 — the dual's two copies are SYNTACTICALLY equal at
--    birth, a theorem needing nothing — this also discharges Merge's
--    cancel-agree for x-pairs, so the DELETING cancel can stay.
--
-- 2. ACCEPT (D1) + DELETING CANCEL — only if 1 is rejected, and then only
--    with §4.2 fixed some other way, because as it stands the deleting
--    cancel is refuted on a term the system types (§4.3) and, once
--    depth-1 values land, that term is a stuck Merge redex.
--
-- 3. ACCEPT (D1) + APPEND-ONLY — REFUTED as an option (§6.1): our conceal
--    indices are exterior-relative, so an appended composite is not a
--    well-formed boundary over any exterior, and the faces-agree strip that
--    would replace the delete is unsound without a retyping premise only
--    Θ = ∅ satisfies (§6.3).
--
-- Also worth recording for the TOPLAS follow-on: their never-delete warning
-- does NOT apply to us (§5) — the cancelled slot is the outer boundary's own
-- fresh reveal, and a sibling entry bridging across it is rewritten through
-- the agreed rep (§5.1).  The charge against our cancel is entirely §4's.
------------------------------------------------------------------------
