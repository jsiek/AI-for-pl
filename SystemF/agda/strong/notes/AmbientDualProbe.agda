module strong.notes.AmbientDualProbe where

-- DESIGN FEASIBILITY PROBE (not part of the development) for DECISIONS.md
-- "Decision 4, continued": candidate (A), the AMBIENT DUAL.
--
-- Instead of W3's term traversal ⇓, Wrap's dual takes the AMBIENT type
-- context Γ (the exterior of the boundary being dualised) as a second
-- argument:
--
--     dualᴳ : TCtx → BCtx → BCtx
--
-- For each slot i < cmax Θ that Θ drops:  if Θ CONCEALS i with rep A,
-- emit the reveal ↑i:=A (exactly today's repOf/dualᵇ); otherwise i is
-- BLOCKED, and we COPY Γ's own entry — `rvld B` ⇒ a reveal carrying the
-- interior reading of B, `abst` ⇒ a rep-less abstract reveal.  Reveals of
-- Θ become conceals as today (cncOfRevs).
--
-- Contents
--   §0  the rep-less abstract reveal, and the ᴳ-variants of ReversalProbe's
--       intOfR / ⊢ᵇʳ / ⊢ʳ (nothing here edits any other file)
--   §1  dualᴳ, and the revised rules it asks for (comment only)
--   §2  general laws: revs/cmax of the dual, and dual-read-backᴳ — the
--       reversal premise for the dual's conceals survives verbatim    ✓
--   §3  RESULT 1.  Decision 4's program P at its Wrap redex           ✓
--   §4  RESULT 2.  Example E, traced with PLAIN TyBeta/TyWrap         ✓
--   §5  RESULT 3.  the Λ-bound star                                   ✓
--   §6  RESULT 4.  reversal-premise compatibility; ¬⊢dualΘnʳ revisited
--       and a NEW counterexample (a copied entry naming a dropped slot)
--   §7  RESULT 5.  locality bookkeeping (comment only)

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties
  using (_≟_; ⊔-assoc; +-identityʳ; +-suc; m+n≮m; m+n∸m≡n; ≤⇒≯)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import strong.Types
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         _∋_:=_; here; Ctx; _∋_⦂_; there; ⤊)
open import strong.Boundary
open import strong.BReduction
  using (Value; GVal; V-$; V-G; V-⟪⟫; G-ƛ; G-Λ; _-→_;
         TyBeta; Beta; TyWrap; Wrap; ξ-·-l; ξ-·-r; ξ-·[]; ξ-Λ; ξ-⟪⟫;
         ⇑ᵀ; dualᵇ; swapᵇ; repOf; rvlsOf; cncOfRevs; shiftReps;
         revs-cncOfRevs; cmax-cncOfRevs0;
         γcnc-conc; γcnc-kept; isConc-<; acc-of; slotsᴳ-ok)
open import strong.notes.GroundedProbe
  using (Δ8′; Θn)
open import strong.notes.MergeProbe using (_⊕_; outSub)
open import strong.notes.ReversalProbe
  using (isOk; bfree; dnT; rdRep; ⟦_⟧ᵉ;
         outRead; upRep; Reversal; outSub-lo; outSub-hi; rdRep-γcnc)

private
  variable
    Δ Ψ Γ : TCtx
    Γₜ : Ctx
    A B C B₀ A₀ : Ty
    M N : Term
    Θ Ξ : BCtx
    x n X j : ℕ

------------------------------------------------------------------------
-- §0.  The rep-less abstract reveal, and the ᴳ-variant judgements.
--
-- In the real design the abstract reveal is a THIRD BEntry constructor
-- (`↑Y`, no rep).  BEntry cannot be extended from here (Term embeds
-- BCtx), so the probe encodes it as `rvl ★ᴳ` for a reserved marker type
-- ★ᴳ = ∀Z.Z, and forks exactly one function — the interior reading — to
-- send it to `abst`.  Everything else (γᵇ, ρᵇ, revs, cmax, baseS,
-- Scoped) is reused unchanged; ρᵇ's image at such a slot is the marker,
-- a DUMMY external face, sound for the same reason today's dualᵇ dummy
-- is: (env)'s Scoped premise on the redex keeps B₁ from naming a slot
-- the boundary drops without concealing (see §7).
------------------------------------------------------------------------

★ᴳ : Ty
★ᴳ = `∀ (` 0)

isBlkr : Ty → Bool
isBlkr (` X)            = false
isBlkr `ℕ               = false
isBlkr `𝔹               = false
isBlkr (A ⇒ B)          = false
isBlkr (`∀ (` zero))    = true
isBlkr (`∀ (` (suc X))) = false
isBlkr (`∀ `ℕ)          = false
isBlkr (`∀ `𝔹)          = false
isBlkr (`∀ (A ⇒ B))     = false
isBlkr (`∀ (`∀ A))      = false

-- the interior entry of the reveal at interior slot j
⟦_⟧ᴳ : BCtx → ℕ → Ty → TyEntry
⟦ Θ ⟧ᴳ j A = if isBlkr A then abst else ⟦ Θ ⟧ᵉ j A

revEntsᴳ : BCtx → ℕ → BCtx → TCtx
revEntsᴳ Θ j []            = []
revEntsᴳ Θ j (rvl A   ∷ Ξ) = ⟦ Θ ⟧ᴳ j A ∷ revEntsᴳ Θ (suc j) Ξ
revEntsᴳ Θ j (cnc X A ∷ Ξ) = revEntsᴳ Θ j Ξ

intOfᴳ : TCtx → BCtx → TCtx
intOfᴳ Δ Θ = revEntsᴳ Θ 0 Θ ++ dropN (cmax Θ) Δ

-- same SHAPE as intOf, so γᵇ / ρᵇ / baseS are reusable unchanged
len-revEntsᴳ : ∀ Θ j Ξ → length (revEntsᴳ Θ j Ξ) ≡ revs Ξ
len-revEntsᴳ Θ j []            = refl
len-revEntsᴳ Θ j (rvl A   ∷ Ξ) = cong suc (len-revEntsᴳ Θ (suc j) Ξ)
len-revEntsᴳ Θ j (cnc X A ∷ Ξ) = len-revEntsᴳ Θ j Ξ

-- boundary well-formedness: ReversalProbe's ⊢ᵇʳ verbatim, over intOfᴳ.
-- (In the real design bwf↑ᴳ on a rep-less ↑Y carries NO premise at all;
-- here `Δ ⊢ ★ᴳ` is derivable, so one constructor suffices.)
data Bwfᴳ (Δ Ψ : TCtx) (Θ : BCtx) : BCtx → Set where
  bwf[]ᴳ : Bwfᴳ Δ Ψ Θ []
  bwf↑ᴳ  : ∀ {A Ξ} → Δ ⊢ A → Bwfᴳ Δ Ψ Θ Ξ → Bwfᴳ Δ Ψ Θ (rvl A ∷ Ξ)
  bwf↓ᴳ  : ∀ {X A A₀ Ξ}
         → Δ ∋ X := A₀ → Reversal Θ X A A₀ → Ψ ⊢ A
         → Bwfᴳ Δ Ψ Θ Ξ → Bwfᴳ Δ Ψ Θ (cnc X A ∷ Ξ)

infix 4 _∣_⊢ᵇᴳ_
_∣_⊢ᵇᴳ_ : TCtx → TCtx → BCtx → Set
Δ ∣ Ψ ⊢ᵇᴳ Θ = Bwfᴳ Δ Ψ Θ Θ

infix 3 _∣_⊢ᴳ_⦂_
data _∣_⊢ᴳ_⦂_ : TCtx → Ctx → Term → Ty → Set where
  ⊢`ᴳ   : Γₜ ∋ x ⦂ A → Δ ∣ Γₜ ⊢ᴳ ` x ⦂ A
  ⊢$ᴳ   : Δ ∣ Γₜ ⊢ᴳ $ n ⦂ `ℕ
  ⊢ƛᴳ   : Δ ⊢ A → Δ ∣ A ∷ Γₜ ⊢ᴳ N ⦂ B → Δ ∣ Γₜ ⊢ᴳ ƛ A ∙ N ⦂ (A ⇒ B)
  ⊢·ᴳ   : Δ ∣ Γₜ ⊢ᴳ M ⦂ (A ⇒ B) → Δ ∣ Γₜ ⊢ᴳ N ⦂ A → Δ ∣ Γₜ ⊢ᴳ M · N ⦂ B
  ⊢Λᴳ   : (abst ∷ Δ) ∣ ⤊ Γₜ ⊢ᴳ N ⦂ C → Δ ∣ Γₜ ⊢ᴳ Λ N ⦂ `∀ C
  ⊢·[]ᴳ : Δ ∣ Γₜ ⊢ᴳ M ⦂ `∀ B → Δ ⊢ A → Δ ∣ Γₜ ⊢ᴳ M ·[ B , A ] ⦂ B [ A ]ᵗ
  envᴳ  : Δ ∣ intOfᴳ Δ Θ ⊢ᵇᴳ Θ
        → Scoped (baseS Θ Δ) B₀
        → intOfᴳ Δ Θ ∣ [] ⊢ᴳ M ⦂ substᵗ (γᵇ Θ) B₀
          ---------------------------------------------------
        → Δ ∣ Γₜ ⊢ᴳ M ⟪ Θ , B₀ ⟫ ⦂ substᵗ (ρᵇ Θ) B₀

------------------------------------------------------------------------
-- §1.  THE AMBIENT DUAL.
--
-- Index home of a COPIED entry.  Γ's entry at slot i is `rvld B` with B
-- a type over Γ's TAIL below i (strong.Context's ∋:= is tail-relative),
-- i.e. over Γ ↓ i.  The dual's reveal reps must live over the dual's
-- EXTERIOR, which is Θ's interior Ψ = intOfᴳ Γ Θ.  The transport is
-- therefore, in two steps and both already present:
--
--     Γ ↓ i  --upRep i-->  Γ  --rdRep Θ-->  Ψ
--
-- so the copied rep is  rdRep Θ (upRep i B)  — exactly the type W3's
-- inserted conceal ↓Z:=⟦A⟧ carries (ReversalProbe.W3-insert), but
-- computed at the DUAL instead of pushed into the term.
--
-- SIDE CONDITION (see §6): rdRep Θ is only meaningful on types naming no
-- BLOCKED slot of Θ, so the copy is exact only when B names no slot that
-- Θ drops without concealing.  When it does, the copy is junk — the new
-- counterexample of §6.
------------------------------------------------------------------------

entAt : TCtx → ℕ → TyEntry            -- Γ's entry at slot i (abst if none)
entAt []      i       = abst
entAt (E ∷ Γ) zero    = E
entAt (E ∷ Γ) (suc i) = entAt Γ i

repᴳ : TCtx → BCtx → ℕ → Ty           -- the dual's rep for dropped slot i
repᴳ Γ Θ i with isConc i Θ
repᴳ Γ Θ i | true  = repOf i Θ                     -- concealed: as today
repᴳ Γ Θ i | false with entAt Γ i
repᴳ Γ Θ i | false | abst   = ★ᴳ                   -- blocked, Λ-bound
repᴳ Γ Θ i | false | rvld B = rdRep Θ (upRep i B)  -- blocked, knowledge

rvlsᴳ : ℕ → ℕ → TCtx → BCtx → BCtx
rvlsᴳ zero    s Γ Θ = []
rvlsᴳ (suc k) s Γ Θ = rvl (repᴳ Γ Θ s) ∷ rvlsᴳ k (suc s) Γ Θ

dualᴳ : TCtx → BCtx → BCtx
dualᴳ Γ Θ = rvlsᴳ (cmax Θ) 0 Γ Θ ++ cncOfRevs 0 Θ

-- the ambient dual refines dualᵇ: identical at every CONCEALED slot,
-- and dualᵇ is the special case "Γ unknown" (every dropped slot ℕ).
repᴳ-conc : ∀ Γ Θ i → isConc i Θ ≡ true → repᴳ Γ Θ i ≡ repOf i Θ
repᴳ-conc Γ Θ i c with isConc i Θ | c
repᴳ-conc Γ Θ i c | true  | _  = refl
repᴳ-conc Γ Θ i c | false | ()

------------------------------------------------------------------------
-- §2.  General laws.  The dual has the same shape as dualᵇ, and
-- ReversalProbe's `dual-read-back` — the theorem that the dual's
-- conceals meet the reversal premise — survives VERBATIM, because the
-- two duals differ only at BLOCKED slots, which no Scoped type names.
------------------------------------------------------------------------

revs-app : ∀ Θ Ξ → revs (Θ ++ Ξ) ≡ revs Θ + revs Ξ
revs-app []            Ξ = refl
revs-app (rvl A ∷ Θ)   Ξ = cong suc (revs-app Θ Ξ)
revs-app (cnc X A ∷ Θ) Ξ = revs-app Θ Ξ

cmax-app : ∀ Θ Ξ → cmax (Θ ++ Ξ) ≡ cmax Θ ⊔ cmax Ξ
cmax-app []            Ξ = refl
cmax-app (rvl A ∷ Θ)   Ξ = cmax-app Θ Ξ
cmax-app (cnc X A ∷ Θ) Ξ =
  trans (cong (suc X ⊔_) (cmax-app Θ Ξ))
        (sym (⊔-assoc (suc X) (cmax Θ) (cmax Ξ)))

revs-rvlsᴳ : ∀ k s Γ Θ → revs (rvlsᴳ k s Γ Θ) ≡ k
revs-rvlsᴳ zero    s Γ Θ = refl
revs-rvlsᴳ (suc k) s Γ Θ = cong suc (revs-rvlsᴳ k (suc s) Γ Θ)

cmax-rvlsᴳ : ∀ k s Γ Θ → cmax (rvlsᴳ k s Γ Θ) ≡ 0
cmax-rvlsᴳ zero    s Γ Θ = refl
cmax-rvlsᴳ (suc k) s Γ Θ = cmax-rvlsᴳ k (suc s) Γ Θ

revs-dualᴳ : ∀ Γ Θ → revs (dualᴳ Γ Θ) ≡ cmax Θ
revs-dualᴳ Γ Θ =
  trans (revs-app (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ))
    (trans (cong₂ _+_ (revs-rvlsᴳ (cmax Θ) 0 Γ Θ) (revs-cncOfRevs 0 Θ))
           (+-identityʳ (cmax Θ)))

cmax-dualᴳ : ∀ Γ Θ → cmax (dualᴳ Γ Θ) ≡ revs Θ
cmax-dualᴳ Γ Θ =
  trans (cmax-app (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ))
    (trans (cong (_⊔ cmax (cncOfRevs 0 Θ)) (cmax-rvlsᴳ (cmax Θ) 0 Γ Θ))
           (cmax-cncOfRevs0 Θ))

ρᵇ-rvlsᴳ-lo : ∀ k s Γ Θ Ξ i → i < k
            → ρᵇ (rvlsᴳ k s Γ Θ ++ Ξ) i ≡ repᴳ Γ Θ (s + i)
ρᵇ-rvlsᴳ-lo zero    s Γ Θ Ξ i       ()
ρᵇ-rvlsᴳ-lo (suc k) s Γ Θ Ξ zero    lt =
  cong (repᴳ Γ Θ) (sym (+-identityʳ s))
ρᵇ-rvlsᴳ-lo (suc k) s Γ Θ Ξ (suc i) (s≤s lt) =
  trans (ρᵇ-rvlsᴳ-lo k (suc s) Γ Θ Ξ i lt)
        (cong (repᴳ Γ Θ) (sym (+-suc s i)))

ρᵇ-dualᴳ-lo : ∀ Γ Θ i → i < cmax Θ → ρᵇ (dualᴳ Γ Θ) i ≡ repᴳ Γ Θ i
ρᵇ-dualᴳ-lo Γ Θ i lt =
  ρᵇ-rvlsᴳ-lo (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ) i lt

-- the ambient dual's read-back map IS the interior reading map, at every
-- ACCESSIBLE slot (the only ones (env)'s Scoped premise lets a type name)
outSub-dualᴳ : ∀ Γ Θ X → slotAt Θ X ≡ ok
             → outSub (dualᴳ Γ Θ) X ≡ γcnc (revs Θ) (cmax Θ) Θ X
outSub-dualᴳ Γ Θ X e with acc-of Θ X e
outSub-dualᴳ Γ Θ X e | inj₁ le =
  trans (outSub-hi (dualᴳ Γ Θ) X
          (λ lt → ≤⇒≯ le (subst (X <_) (revs-dualᴳ Γ Θ) lt)))
        (trans (cong₂ (λ a b → ` (a + (X ∸ b)))
                      (cmax-dualᴳ Γ Θ) (revs-dualᴳ Γ Θ))
               (sym (γcnc-kept (revs Θ) (cmax Θ) Θ X le)))
outSub-dualᴳ Γ Θ X e | inj₂ c =
  trans (outSub-lo (dualᴳ Γ Θ) X
          (subst (X <_) (sym (revs-dualᴳ Γ Θ)) (isConc-< Θ X c)))
        (trans (ρᵇ-dualᴳ-lo Γ Θ X (isConc-< Θ X c))
               (trans (repᴳ-conc Γ Θ X c)
                      (sym (γcnc-conc (revs Θ) (cmax Θ) Θ X c))))

dual-read-backᴳ : ∀ (Γ : TCtx) Θ A → Scoped (slotsᴳ Θ 0 Γ) A
                → outRead (dualᴳ Γ Θ) A ≡ rdRep Θ A
dual-read-backᴳ Γ Θ A sc =
  trans (subst-cong-sc sc
          (λ X okp → outSub-dualᴳ Γ Θ X (slotsᴳ-ok Θ Γ 0 X okp)))
        (sym (rdRep-γcnc Θ A))

dual-cnc-Reversalᴳ : ∀ (Γ : TCtx) Θ j A
  → Scoped (slotsᴳ Θ 0 Γ) A
  → upRep j (dnT (suc j) (rdRep Θ A)) ≡ rdRep Θ A
  → Reversal (dualᴳ Γ Θ) j A (dnT (suc j) (rdRep Θ A))
dual-cnc-Reversalᴳ Γ Θ j A sc rt =
  trans (dual-read-backᴳ Γ Θ A sc) (sym rt)

------------------------------------------------------------------------
-- §3.  RESULT 1.  Decision 4's program P, at its Wrap redex.
--
--   Γw = Y:=𝔹 , X:=ℕ          (both REVEALED; Y shallower)
--   Θh = ↓X:=ℕ                (the PLAIN sealed boundary; NO W3 anywhere)
--   h  = (λx:ℕ.x) ⟪ Θh , X→X ⟫      Y is BLOCKED in Θh, and it carries 𝔹
--   Wd = (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↓Y:=𝔹 , X ⟫      uses Y's knowledge
--   R  = h · Wd : X                            the Wrap redex
------------------------------------------------------------------------

Γw : TCtx
Γw = rvld `𝔹 ∷ rvld `ℕ ∷ []

Θh : BCtx
Θh = cnc 1 `ℕ ∷ []

Wd : Term
Wd = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ cnc 0 `𝔹 ∷ [] , ` 1 ⟫

h : Term
h = (ƛ `ℕ ∙ ` 0) ⟪ Θh , ` 1 ⇒ ` 1 ⟫

⊢Wd : ∀ {Γₜ} → Γw ∣ Γₜ ⊢ᴳ Wd ⦂ ` 1
⊢Wd = envᴳ (bwf↓ᴳ here refl wf-𝔹 bwf[]ᴳ)
           (sc-var (thereᵒ hereᵒ))
           (envᴳ (bwf↓ᴳ here refl wf-ℕ bwf[]ᴳ) (sc-var hereᵒ) ⊢$ᴳ)

⊢h : ∀ {Γₜ} → Γw ∣ Γₜ ⊢ᴳ h ⦂ (` 1 ⇒ ` 1)
⊢h = envᴳ (bwf↓ᴳ (skip-rvld here) refl wf-ℕ bwf[]ᴳ)
          (sc-⇒ (sc-var (thereᵒ hereᵒ)) (sc-var (thereᵒ hereᵒ)))
          (⊢ƛᴳ wf-ℕ (⊢`ᴳ here))

⊢R : Γw ∣ [] ⊢ᴳ h · Wd ⦂ ` 1
⊢R = ⊢·ᴳ ⊢h ⊢Wd

_ : baseS Θh Γw ≡ blk ∷ ok ∷ []            -- Y blocked, but REVEALED at 𝔹
_ = refl

-- (a) the ambient dual COPIES Y's knowledge, where dualᵇ invents ℕ
_ : dualᴳ Γw Θh ≡ rvl `𝔹 ∷ rvl `ℕ ∷ []
_ = refl

_ : dualᵇ Θh ≡ rvl `ℕ ∷ rvl `ℕ ∷ []
_ = refl

-- (b) … so its interior is Γw ON THE NOSE (dualᵇ's is not)
dual-int-P : intOfᴳ (intOfᴳ Γw Θh) (dualᴳ Γw Θh) ≡ Γw
dual-int-P = refl

_ : intOfᴳ (intOfᴳ Γw Θh) (dualᵇ Θh) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

-- (c) the Wrap contractum, with dualᴳ in place of dualᵇ, TYPES.
--     (swapᵇ Θh = id on the frame here, so B₁ is unchanged.)
-- the CURRENT rule fires with dualᵇ (and fixes the frame index for us):
_ : h · Wd -→ (Wd ⟪ dualᵇ Θh , ` 1 ⟫) ⟪ Θh , ` 1 ⟫
_ = Wrap (V-⟪⟫ (V-⟪⟫ V-$))

Rᴰ : Term
Rᴰ = (Wd ⟪ dualᴳ Γw Θh , ` 1 ⟫) ⟪ Θh , ` 1 ⟫

⊢Rᴰ : Γw ∣ [] ⊢ᴳ Rᴰ ⦂ ` 1
⊢Rᴰ =
  envᴳ (bwf↓ᴳ (skip-rvld here) refl wf-ℕ bwf[]ᴳ)
       (sc-var (thereᵒ hereᵒ))
       (envᴳ (bwf↑ᴳ wf-𝔹 (bwf↑ᴳ wf-ℕ bwf[]ᴳ))
             (sc-var (thereᵒ hereᵒ))
             ⊢Wd)

-- (d) for contrast: with dualᵇ the contractum is ILL TYPED — Wd's outer
--     conceal ↓Y:=𝔹 meets the invented knowledge Y:=ℕ.
¬⊢Wd-dualᵇ : ¬ ((rvld `ℕ ∷ rvld `ℕ ∷ []) ∣ [] ⊢ᴳ Wd ⦂ ` 1)
¬⊢Wd-dualᵇ (envᴳ (bwf↓ᴳ here () _ _) _ _)

------------------------------------------------------------------------
-- §4.  RESULT 2.  Example E, the case that forced W3's deep traversal.
--
--   E = (ΛX. λf:(X→X). ΛY. (ΛZ. λz:X. f z) [ℕ]) [ℕ] (λn:ℕ.n) [𝔹] 3
--
-- The gadget (ΛZ. …)[ℕ] is a type abstraction BETWEEN ΛY and the sealed
-- value, evaluated under the Λ by ξ-Λ before Y's TyWrap fires; W3's ⇓
-- would have to cross it (and λz, and an application).  Traced below
-- with PLAIN TyBeta/TyWrap — no insertion anywhere.
------------------------------------------------------------------------

idℕ : Term
idℕ = ƛ `ℕ ∙ ` 0

srcE : Term
srcE = Λ (ƛ (` 0 ⇒ ` 0) ∙
            Λ ((Λ (ƛ ` 2 ∙ (` 1 · ` 0))) ·[ ` 2 ⇒ ` 2 , `ℕ ]))

BsrcE : Ty
BsrcE = (` 0 ⇒ ` 0) ⇒ `∀ (` 1 ⇒ ` 1)

E0 : Term
E0 = ((srcE ·[ BsrcE , `ℕ ]) · idℕ) ·[ `ℕ ⇒ `ℕ , `𝔹 ] · ($ 3)

⊢srcE : [] ∣ [] ⊢ᴳ srcE ⦂ `∀ BsrcE
⊢srcE =
  ⊢Λᴳ (⊢ƛᴳ (wf-⇒ (wf-var here-abst) (wf-var here-abst))
        (⊢Λᴳ (⊢·[]ᴳ (⊢Λᴳ (⊢ƛᴳ (wf-var (skip-abst (skip-abst here-abst)))
                              (⊢·ᴳ (⊢`ᴳ (there here)) (⊢`ᴳ here))))
                    wf-ℕ)))

⊢E0 : [] ∣ [] ⊢ᴳ E0 ⦂ `ℕ
⊢E0 = ⊢·ᴳ (⊢·[]ᴳ (⊢·ᴳ (⊢·[]ᴳ ⊢srcE wf-ℕ) (⊢ƛᴳ wf-ℕ (⊢`ᴳ here))) wf-𝔹) ⊢$ᴳ

Θx : BCtx                       -- ↑X:=ℕ
Θx = rvl `ℕ ∷ []

fE : Term                       -- the SEALED value, under ΛY and ΛZ
fE = idℕ ⟪ cnc 2 `ℕ ∷ [] , ` 2 ⇒ ` 2 ⟫

ΘfE : BCtx                      -- its boundary: ↓X:=ℕ, plain
ΘfE = cnc 2 `ℕ ∷ []

E1 : Term
E1 = (((ƛ (` 0 ⇒ ` 0) ∙
          Λ ((Λ (ƛ ` 2 ∙ (` 1 · ` 0))) ·[ ` 2 ⇒ ` 2 , `ℕ ]))
        ⟪ Θx , BsrcE ⟫) · idℕ) ·[ `ℕ ⇒ `ℕ , `𝔹 ] · ($ 3)

_ : E0 -→ E1
_ = ξ-·-l (ξ-·[] (ξ-·-l (TyBeta (V-G G-ƛ))))

E2 : Term
E2 = ((Λ ((Λ (ƛ ` 2 ∙ (fE · ` 0))) ·[ ` 2 ⇒ ` 2 , `ℕ ]))
       ⟪ Θx , `∀ (` 1 ⇒ ` 1) ⟫) ·[ `ℕ ⇒ `ℕ , `𝔹 ] · ($ 3)

_ : E1 -→ E2
_ = ξ-·-l (ξ-·[] (Wrap (V-G G-ƛ)))

Θz : BCtx                       -- ↑Z:=ℕ, minted by TyBeta UNDER the ΛY
Θz = rvl `ℕ ∷ []

E3 : Term
E3 = ((Λ ((ƛ ` 2 ∙ (fE · ` 0)) ⟪ Θz , ` 2 ⇒ ` 2 ⟫))
       ⟪ Θx , `∀ (` 1 ⇒ ` 1) ⟫) ·[ `ℕ ⇒ `ℕ , `𝔹 ] · ($ 3)

_ : E2 -→ E3
_ = ξ-·-l (ξ-·[] (ξ-⟪⟫ (ξ-Λ (TyBeta (V-G G-ƛ)))))

-- NOTE (the difference from the W3 trace): the sealed boundary is still
-- the PLAIN ↓X:=ℕ, in which Z is now blocked; W3 would have inserted
-- ↓Z:=ℕ here, crossing λz and an application to do it.
Θyx : BCtx                      -- ↑Y:=𝔹 , ↑X:=ℕ   (TyWrap's direct combine)
Θyx = rvl `𝔹 ∷ rvl `ℕ ∷ []

E4 : Term
E4 = (((ƛ ` 2 ∙ (fE · ` 0)) ⟪ Θz , ` 2 ⇒ ` 2 ⟫) ⟪ Θyx , ` 1 ⇒ ` 1 ⟫)
     · ($ 3)

_ : E3 -→ E4
_ = ξ-·-l (TyWrap (V-⟪⟫ (V-G G-ƛ)))

-- … and TyWrap leaves the sealed boundary UNCHANGED (still ↓X:=ℕ).

-- E4 is a MERGE redex, not a Wrap redex (a wrapper-bodied wrapper at a
-- ⇒ face), and Merge is not yet a rule of strong.BReduction.  Both sides
-- type; MergeProbe's ⊕ delivers exactly the merged boundary, and since
-- cmax Θz = 0 the two frames coincide, so B₀ is unchanged.
ΘmE : BCtx                      -- ↑Z:=ℕ , ↑Y:=𝔹 , ↑X:=ℕ
ΘmE = rvl `ℕ ∷ rvl `𝔹 ∷ rvl `ℕ ∷ []

_ : Θz ⊕ Θyx ≡ ΘmE
_ = refl

ΓE : TCtx                       -- Z:=ℕ , Y:=𝔹 , X:=ℕ  — the ambient Γ
ΓE = rvld `ℕ ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

_ : intOfᴳ [] ΘmE ≡ ΓE
_ = refl

_ : intOfᴳ [] Θyx ≡ rvld `𝔹 ∷ rvld `ℕ ∷ []
_ = refl

⊢fE : ∀ {Γₜ} → ΓE ∣ Γₜ ⊢ᴳ fE ⦂ (` 2 ⇒ ` 2)
⊢fE = envᴳ (bwf↓ᴳ (skip-rvld (skip-rvld here)) refl wf-ℕ bwf[]ᴳ)
           (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ)))
                 (sc-var (thereᵒ (thereᵒ hereᵒ))))
           (⊢ƛᴳ wf-ℕ (⊢`ᴳ here))

-- both sides of the Merge, at the same type ℕ→ℕ
⊢E4fun : [] ∣ [] ⊢ᴳ
         ((ƛ ` 2 ∙ (fE · ` 0)) ⟪ Θz , ` 2 ⇒ ` 2 ⟫) ⟪ Θyx , ` 1 ⇒ ` 1 ⟫
         ⦂ (`ℕ ⇒ `ℕ)
⊢E4fun =
  envᴳ (bwf↑ᴳ wf-𝔹 (bwf↑ᴳ wf-ℕ bwf[]ᴳ))
       (sc-⇒ (sc-var (thereᵒ hereᵒ)) (sc-var (thereᵒ hereᵒ)))
       (envᴳ (bwf↑ᴳ wf-ℕ bwf[]ᴳ)
             (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ)))
                   (sc-var (thereᵒ (thereᵒ hereᵒ))))
             (⊢ƛᴳ (wf-var (skip-rvld (skip-rvld here-rvld)))
                  (⊢·ᴳ ⊢fE (⊢`ᴳ here))))

⊢E5fun : [] ∣ [] ⊢ᴳ (ƛ ` 2 ∙ (fE · ` 0)) ⟪ ΘmE , ` 2 ⇒ ` 2 ⟫ ⦂ (`ℕ ⇒ `ℕ)
⊢E5fun =
  envᴳ (bwf↑ᴳ wf-ℕ (bwf↑ᴳ wf-𝔹 (bwf↑ᴳ wf-ℕ bwf[]ᴳ)))
       (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ)))
             (sc-var (thereᵒ (thereᵒ hereᵒ))))
       (⊢ƛᴳ (wf-var (skip-rvld (skip-rvld here-rvld)))
            (⊢·ᴳ ⊢fE (⊢`ᴳ here)))

E5 : Term
E5 = ((ƛ ` 2 ∙ (fE · ` 0)) ⟪ ΘmE , ` 2 ⇒ ` 2 ⟫) · ($ 3)

W₃ : Term                       -- the argument, pushed in through the dual
W₃ = ($ 3) ⟪ dualᴳ [] ΘmE , ` 2 ⟫

_ : dualᴳ [] ΘmE ≡ cnc 0 `ℕ ∷ cnc 1 `𝔹 ∷ cnc 2 `ℕ ∷ []
_ = refl

E6 : Term
E6 = ((fE · W₃) ⟪ ΘmE , ` 2 ⟫)

_ : E5 -→ ((fE · (($ 3) ⟪ dualᵇ ΘmE , ` 2 ⟫)) ⟪ ΘmE , ` 2 ⟫)
_ = Wrap V-$

_ : dualᵇ ΘmE ≡ dualᴳ [] ΘmE            -- no dropped slots: duals agree
_ = refl

⊢W₃ : ∀ {Γₜ} → ΓE ∣ Γₜ ⊢ᴳ W₃ ⦂ ` 2
⊢W₃ = envᴳ (bwf↓ᴳ here refl wf-ℕ
             (bwf↓ᴳ (skip-rvld here) refl wf-𝔹
               (bwf↓ᴳ (skip-rvld (skip-rvld here)) refl wf-ℕ bwf[]ᴳ)))
           (sc-var (thereᵒ (thereᵒ hereᵒ)))
           ⊢$ᴳ

-- THE TARGET WRAP: the sealed value fE (boundary ↓X:=ℕ) meets W₃, at
-- ambient Γ = ΓE, with Z AND Y blocked and both carrying knowledge.
_ : baseS ΘfE ΓE ≡ blk ∷ blk ∷ ok ∷ []
_ = refl

-- the ambient dual copies BOTH knowledge entries …
dualE : BCtx
dualE = dualᴳ ΓE ΘfE

_ : dualE ≡ rvl `ℕ ∷ rvl `𝔹 ∷ rvl `ℕ ∷ []
_ = refl

_ : dualᵇ ΘfE ≡ rvl `ℕ ∷ rvl `ℕ ∷ rvl `ℕ ∷ []       -- Y invented as ℕ
_ = refl

-- … and rebuilds ΓE on the nose (dualᵇ does not)
dual-int-E : intOfᴳ (intOfᴳ ΓE ΘfE) dualE ≡ ΓE
dual-int-E = refl

_ : intOfᴳ (intOfᴳ ΓE ΘfE) (dualᵇ ΘfE)
    ≡ rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

-- the CURRENT rule fires here, with dualᵇ (Wrap consumes the ƛ, so the
-- contractum is the wrapped argument itself):
_ : E6 -→ ((W₃ ⟪ dualᵇ ΘfE , ` 2 ⟫) ⟪ ΘfE , ` 2 ⟫) ⟪ ΘmE , ` 2 ⟫
_ = ξ-⟪⟫ (Wrap (V-⟪⟫ V-$))

E7 : Term                       -- the contractum, ambient dual, ZERO ⇓
E7 = ((W₃ ⟪ dualE , ` 2 ⟫) ⟪ ΘfE , ` 2 ⟫) ⟪ ΘmE , ` 2 ⟫

⊢E7 : [] ∣ [] ⊢ᴳ E7 ⦂ `ℕ
⊢E7 =
  envᴳ (bwf↑ᴳ wf-ℕ (bwf↑ᴳ wf-𝔹 (bwf↑ᴳ wf-ℕ bwf[]ᴳ)))
       (sc-var (thereᵒ (thereᵒ hereᵒ)))
       (envᴳ (bwf↓ᴳ (skip-rvld (skip-rvld here)) refl wf-ℕ bwf[]ᴳ)
             (sc-var (thereᵒ (thereᵒ hereᵒ)))
             (envᴳ (bwf↑ᴳ wf-ℕ (bwf↑ᴳ wf-𝔹 (bwf↑ᴳ wf-ℕ bwf[]ᴳ)))
                   (sc-var (thereᵒ (thereᵒ hereᵒ)))
                   ⊢W₃))

-- with dualᵇ instead, W₃'s conceal ↓Y:=𝔹 has nothing to match: ill typed
¬⊢W₃-dualᵇ : ¬ ((rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []) ∣ [] ⊢ᴳ W₃ ⦂ ` 2)
¬⊢W₃-dualᵇ (envᴳ (bwf↓ᴳ here _ _ (bwf↓ᴳ (skip-rvld here) () _ _)) _ _)

------------------------------------------------------------------------
-- §5.  RESULT 3.  The Λ-BOUND STAR.
--
--   S = (ΛX. λf:(X→X). λw:X. ΛY. f w) [ℕ] (λn:ℕ.n) 3
--
-- The inner Wrap fires UNDER the un-eliminated ΛY (via ξ-Λ), so the
-- ambient Γ★ = Y (abstract) , X:=ℕ.  The dual must rebuild Y ABSTRACT.
------------------------------------------------------------------------

srcS : Term
srcS = Λ (ƛ (` 0 ⇒ ` 0) ∙ (ƛ ` 0 ∙ Λ (` 1 · ` 0)))

BsrcS : Ty
BsrcS = (` 0 ⇒ ` 0) ⇒ (` 0 ⇒ `∀ (` 1))

S0 : Term
S0 = ((srcS ·[ BsrcS , `ℕ ]) · idℕ) · ($ 3)

⊢srcS : [] ∣ [] ⊢ᴳ srcS ⦂ `∀ BsrcS
⊢srcS =
  ⊢Λᴳ (⊢ƛᴳ (wf-⇒ (wf-var here-abst) (wf-var here-abst))
        (⊢ƛᴳ (wf-var here-abst)
          (⊢Λᴳ (⊢·ᴳ (⊢`ᴳ (there here)) (⊢`ᴳ here)))))

⊢S0 : [] ∣ [] ⊢ᴳ S0 ⦂ `∀ `ℕ
⊢S0 = ⊢·ᴳ (⊢·ᴳ (⊢·[]ᴳ ⊢srcS wf-ℕ) (⊢ƛᴳ wf-ℕ (⊢`ᴳ here))) ⊢$ᴳ

fS : Term                       -- the sealed value, shifted under ΛY
fS = idℕ ⟪ cnc 1 `ℕ ∷ [] , ` 1 ⇒ ` 1 ⟫

Θ★ : BCtx
Θ★ = cnc 1 `ℕ ∷ []

S1 : Term
S1 = (((ƛ (` 0 ⇒ ` 0) ∙ (ƛ ` 0 ∙ Λ (` 1 · ` 0))) ⟪ Θx , BsrcS ⟫)
      · idℕ) · ($ 3)

_ : S0 -→ S1
_ = ξ-·-l (ξ-·-l (TyBeta (V-G G-ƛ)))

S2 : Term
S2 = ((ƛ ` 0 ∙ Λ (fS · ` 0)) ⟪ Θx , ` 0 ⇒ `∀ (` 1) ⟫) · ($ 3)

_ : S1 -→ S2
_ = ξ-·-l (Wrap (V-G G-ƛ))

W₄ : Term
W₄ = ($ 3) ⟪ cnc 1 `ℕ ∷ [] , ` 1 ⟫        -- ⇑ᵀ of  3 ⟪ ↓X:=ℕ , X ⟫

S3 : Term
S3 = (Λ (fS · W₄)) ⟪ Θx , `∀ (` 1) ⟫

_ : S2 -→ S3
_ = Wrap V-$

-- the ambient context at the inner Wrap: ξ-⟪⟫ gives Θx's interior, ξ-Λ
-- adds the abstract Y.
Γ★ : TCtx
Γ★ = abst ∷ rvld `ℕ ∷ []

_ : abst ∷ intOfᴳ [] Θx ≡ Γ★
_ = refl

_ : baseS Θ★ Γ★ ≡ blk ∷ ok ∷ []           -- Y blocked, and ABSTRACT
_ = refl

-- the dual emits the REP-LESS ABSTRACT REVEAL at Y …
_ : dualᴳ Γ★ Θ★ ≡ rvl ★ᴳ ∷ rvl `ℕ ∷ []
_ = refl

-- … and rebuilds Γ★ exactly: abstract against abstract.
dual-int-S : intOfᴳ (intOfᴳ Γ★ Θ★) (dualᴳ Γ★ Θ★) ≡ Γ★
dual-int-S = refl

-- dualᵇ instead REVEALS Y at the dummy ℕ — no type error here (W₄ does
-- not mention Y), but the rebuilt context is unsound knowledge.
_ : intOfᴳ (intOfᴳ Γ★ Θ★) (dualᵇ Θ★) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

⊢W₄ : ∀ {Γₜ} → Γ★ ∣ Γₜ ⊢ᴳ W₄ ⦂ ` 1
⊢W₄ = envᴳ (bwf↓ᴳ (skip-abst here) refl wf-ℕ bwf[]ᴳ)
           (sc-var (thereᵒ hereᵒ)) ⊢$ᴳ

⊢fS : ∀ {Γₜ} → Γ★ ∣ Γₜ ⊢ᴳ fS ⦂ (` 1 ⇒ ` 1)
⊢fS = envᴳ (bwf↓ᴳ (skip-abst here) refl wf-ℕ bwf[]ᴳ)
           (sc-⇒ (sc-var (thereᵒ hereᵒ)) (sc-var (thereᵒ hereᵒ)))
           (⊢ƛᴳ wf-ℕ (⊢`ᴳ here))

⊢S4redex : Γ★ ∣ [] ⊢ᴳ fS · W₄ ⦂ ` 1
⊢S4redex = ⊢·ᴳ ⊢fS ⊢W₄

-- the CURRENT rule, under ξ-⟪⟫ ξ-Λ, with dualᵇ:
_ : S3 -→ (Λ ((W₄ ⟪ dualᵇ Θ★ , ` 1 ⟫) ⟪ Θ★ , ` 1 ⟫)) ⟪ Θx , `∀ (` 1) ⟫
_ = ξ-⟪⟫ (ξ-Λ (Wrap (V-⟪⟫ V-$)))

S4 : Term                        -- the contractum, ambient dual
S4 = (W₄ ⟪ dualᴳ Γ★ Θ★ , ` 1 ⟫) ⟪ Θ★ , ` 1 ⟫

⊢S4 : Γ★ ∣ [] ⊢ᴳ S4 ⦂ ` 1
⊢S4 = envᴳ (bwf↓ᴳ (skip-abst here) refl wf-ℕ bwf[]ᴳ)
           (sc-var (thereᵒ hereᵒ))
           (envᴳ (bwf↑ᴳ (wf-∀ (wf-var here-abst)) (bwf↑ᴳ wf-ℕ bwf[]ᴳ))
                 (sc-var (thereᵒ hereᵒ))
                 ⊢W₄)

------------------------------------------------------------------------
-- §6.  RESULT 4.  Reversal-premise compatibility, and the two sores.
--
-- (a) The CONCEALS of dualᴳ Γ Θ are Θ's reveals turned around; §2's
--     dual-read-backᴳ / dual-cnc-Reversalᴳ prove they meet the reversal
--     premise over the new exterior, GENERALLY, for reps naming no
--     blocked slot — the same statement as ReversalProbe's dualᵇ version
--     (the two duals differ only at blocked slots).
--
-- (b) The bwf↑-side condition on the KNOWLEDGE-COPYING reveals is
--     `Ψ ⊢ repᴳ Γ Θ i` with Ψ = intOfᴳ Γ Θ.  Concealed slots inherit it
--     from Θ's own bwf↓; ★ᴳ satisfies it always; a copied `rvld B`
--     satisfies it exactly when rdRep Θ (upRep i B) is Ψ-scoped, i.e.
--     when B names no slot Θ BLOCKS.  On P (𝔹) and on E (ℕ, 𝔹) the reps
--     are closed and it holds; §6c is the counterexample.
------------------------------------------------------------------------

-- §6a.  ¬⊢dualΘnʳ under the ambient dual: NOT dissolved.
--   Θn = ↑Z:=Y , ↓X:=ℕ   over  Δ8′ = Y(abst) , X:=ℕ
_ : intOfᴳ Δ8′ Θn ≡ abst ∷ []               -- Z's entry: abst (Decision 1)
_ = refl

-- the ambient dual DOES improve the reveal block — Y comes back abstract
-- instead of revealed at the dummy ℕ …
_ : dualᴳ Δ8′ Θn ≡ rvl ★ᴳ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
_ = refl

_ : dualᵇ Θn ≡ rvl `ℕ ∷ rvl `ℕ ∷ cnc 0 (` 0) ∷ []
_ = refl

-- … and the rebuilt interior is now Δ8′ ON THE NOSE, which dualᵇ's was
-- not (it revealed Y at ℕ):
_ : intOfᴳ (intOfᴳ Δ8′ Θn) (dualᴳ Δ8′ Θn) ≡ Δ8′
_ = refl

-- BUT the dual's CONCEAL ↓Z:=Y is still unlicensed: the exterior of the
-- dual is Θn's interior, whose entry for Z is `abst` (its rep Y names a
-- blocked slot), so there is no knowledge Z:=A₀ to meet.  rdRep is never
-- even reached: ⟦_⟧ᵉ's bfree guard fires first.  The obstruction is
-- STRUCTURAL, not about the dual — "Z is Y" is simply not expressible in
-- a context that dropped Y — so candidate (A) does NOT dissolve it.
_ : bfree Θn 0 (` 0) ≡ false
_ = refl

¬knows-Z : ¬ (Σ Ty λ A₀ → (abst ∷ []) ∋ 0 := A₀)
¬knows-Z (A₀ , ())

¬⊢dualᴳΘn : ∀ {Ψ} → ¬ ((abst ∷ []) ∣ Ψ ⊢ᵇᴳ dualᴳ Δ8′ Θn)
¬⊢dualᴳΘn (bwf↑ᴳ _ (bwf↑ᴳ _ (bwf↓ᴳ () _ _ _)))

-- §6b.  NEW COUNTEREXAMPLE.  A copied entry whose rep names ANOTHER
-- dropped slot.  This is reachable: it is P's own nested trace, where
-- TyBeta mints ↑Y:=Y′ and so the ambient context carries Y:=Y′ over
-- Y′:=𝔹 (DECISIONS, Decision 4, the line "exterior Γ = Y:=Y′ , Y′:=𝔹 ,
-- X:=ℕ").  Θ = ↓X:=ℕ drops BOTH Y and Y′.
Γp : TCtx                       -- Y:=Y′ , Y′:=𝔹 , X:=ℕ
Γp = rvld (` 0) ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

Θp : BCtx
Θp = cnc 2 `ℕ ∷ []

-- Y's entry ` 0 (= Y′) is a type over Γp ↓ 0, and Y′ is BLOCKED by Θp,
-- so rdRep hands back a junk index instead of a Ψ-type: the copy is
-- ` 0, which the dual's exterior [] does not even have.
_ : dualᴳ Γp Θp ≡ rvl (` 0) ∷ rvl `𝔹 ∷ rvl `ℕ ∷ []
_ = refl

¬⊢dualᴳΓp : ∀ {Ψ} → ¬ ([] ∣ Ψ ⊢ᵇᴳ dualᴳ Γp Θp)
¬⊢dualᴳΓp (bwf↑ᴳ (wf-var ()) _)

-- and the rebuild misses Γp (the copied entry is re-read as ` 2):
_ : intOfᴳ (intOfᴳ Γp Θp) (dualᴳ Γp Θp)
    ≡ rvld (` 2) ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []
_ = refl

-- THE REPAIR that already exists: unfold the entry first.  A Merge of
-- the two nested reveal boundaries replaces Y:=Y′ by Y:=𝔹 (DECISIONS'
-- own observation on P), and then the ambient dual is exact:
Γp′ : TCtx                      -- Y:=𝔹 , Y′:=𝔹 , X:=ℕ
Γp′ = rvld `𝔹 ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

_ : dualᴳ Γp′ Θp ≡ rvl `𝔹 ∷ rvl `𝔹 ∷ rvl `ℕ ∷ []
_ = refl

_ : intOfᴳ (intOfᴳ Γp′ Θp) (dualᴳ Γp′ Θp) ≡ Γp′
_ = refl

-- The alternative repair (no Merge): let the dual's REVEAL BLOCK be read
-- TELESCOPICALLY — reveal i's rep a type over the exterior extended by
-- the reveals BELOW it, so that the copy of Y:=Y′ may name the dual's
-- own rebuild of Y′.  That is a change to (bwf-↑), which today demands
-- `Δ ⊢ A` for every reveal rep.  Note that ` 0 IS the right telescope
-- entry here; only the reading is wrong.
_ : entAt Γp 0 ≡ rvld (` 0)
_ = refl

------------------------------------------------------------------------
-- §7.  RESULT 5.  Locality bookkeeping (STATED, not proved).
--
-- Reduction becomes knowledge-indexed, mirroring the Δ of typing:
--
--     Γ ⊢ M -→ M′
--
--   (Wrap)   Γ ⊢ ((ƛ A′ ∙ N) ⟪ Θ , B₁ ⇒ B₂ ⟫) · W
--              -→ (N [ W ⟪ dualᴳ Γ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫ ]ᵐ)
--                   ⟪ Θ , B₂ ⟫
--
--   (ξ-⟪⟫)   intOfᴳ Γ Θ ⊢ M -→ M′   ⟹   Γ ⊢ M ⟪ Θ , B₀ ⟫ -→ M′ ⟪ Θ , B₀ ⟫
--   (ξ-Λ)    abst ∷ Γ ⊢ N -→ N′      ⟹   Γ ⊢ Λ N -→ Λ N′
--   (ξ-·-l, ξ-·-r, ξ-·[])            Γ unchanged
--
-- TyBeta / TyWrap / Beta do not read Γ; only Wrap does.  §3–§5 check
-- exactly the Γ that these ξ rules deliver (§5's Γ★ is spelled out).
--
-- Where the Γ-index leaks:
--   * Preservation becomes  Δ ∣ [] ⊢ M ⦂ A → Δ ⊢ M -→ M′ → Δ ∣ [] ⊢ M′ ⦂ A
--     — the SAME Δ on both judgements, so the ξ cases must show that the
--     reduction's Γ-extension is the typing's Δ-extension: intOfᴳ for
--     ξ-⟪⟫, `abst ∷` for ξ-Λ.  Both hold definitionally as stated.
--   * Progress becomes  Δ ∣ [] ⊢ M ⦂ A → Value M ⊎ Σ M′ (Δ ⊢ M -→ M′);
--     the Wrap case must produce dualᴳ Δ Θ, so the canonical-forms lemma
--     has to thread Δ (today's is Δ-free).
--   * DETERMINISM and the evaluator: -→ is no longer a relation on terms
--     alone, so `Eval`/`⟶*` are indexed by Γ; the top level uses Γ = [].
--   * The scope premise: baseS must mark a slot rebuilt by a REP-LESS
--     reveal as `blk`, so that (env)'s Scoped premise keeps B₁ from
--     naming it (its ρᵇ image is the dummy ★ᴳ).  Wrap's own B₁ already
--     cannot: it is Scoped over baseS Θ Γ, in which the slot is blocked,
--     and swapᵇ carries that block to the dual's reveal slot.
------------------------------------------------------------------------
