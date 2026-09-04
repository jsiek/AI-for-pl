module strong.BReduction where

-- Reduction for the tight dual boundary (B₀) design, one rule at a time.
-- Each rule: the rule, a worked typed example, and its preservation case.
-- Preservation is stated at runtime term contexts ([]).
--
-- Reduction is KNOWLEDGE-INDEXED (notes/DECISIONS.md, Decision 4's ambient
-- dual): the judgement is  Δ ⊢ M -→ M′, mirroring the Δ of typing.  ξ-⟪⟫
-- extends the index by the boundary's interior and ξ-Λ by an abstract entry;
-- every other rule passes Δ through.  Only Peel reads it — its dual copies
-- the ambient context's own entry at each slot the boundary drops without
-- concealing, so no knowledge is ever lost and no term traversal is needed.

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; _⊔_; s≤s; z≤n; _<?_; _≤?_)
open import Data.Nat.Properties
  using (m≤m+n; m+[n∸m]≡n; +-monoʳ-<; +-cancelˡ-<; ≤-trans; <⇒≤; ≤-refl;
         _≟_; <-cmp; <-irrefl; ≰⇒>; m≤n⇒m<n∨m≡n; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m;
         m+n∸m≡n; m+n≮m; +-identityʳ; +-suc; +-assoc; +-comm;
         0∸n≡0; m≤n⇒m∸n≡0; ∸-monoˡ-<; ≮⇒≥; n≤0⇒n≡0;
         ∸-distribʳ-⊔; +-distribˡ-⊔;
         ⊔-assoc; ⊔-comm; ⊔-identityʳ; ⊔-lub; m≤m⊔n;
         n≤1+n; suc-injective; m≤n⊔m; ≤⇒≯; +-cancelˡ-≡; ≤-pred;
         +-cancelˡ-≤; +-monoʳ-≤; +-∸-assoc; ∸-+-assoc)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Relation.Nullary using (Dec; yes; no; ¬_; ⌊_⌋)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; subst; subst₂; cong; cong₂)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; rename-cong; rename-rename-commute; rename-[]ᵗ-commute;
         rename-subst; rename-subst-commute; exts-sub-cons; cons-sub;
         subst-id; sub-sub)
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; xrvld; _↓_; _⊢_;
         wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀; entAt;
         _∋tv_; here-abst; here-rvld; here-xrvld;
         skip-abst; skip-rvld; skip-xrvld; _∋_:=_; here; ∋:=→∋tv;
         _∋_:=x_; herex; skipx; ∋:=x→∋tv;
         Ctx; _∋_⦂_; there; ⤊)
open import strong.Weakening using (wf-rename-fv; fv-scope; wf-⇑-abst)
open import strong.Unfold
  using (unfSub; unfoldᵉ; upᵉ; _≈Δ̄⟨_⟩_; ≈unf; ≈unf⁻;
         ≈-refl; ≈-sym; ≈-trans; ≡→≈; ≈-⇒; ≈-∀;
         Absorbs; unf-absorb; ≈-mono; UnfRen≈; ≈-ren; unf-ren-step;
         UnfRen≈-fix; unfSub-↓; unfSub-dich; unfSub-know; unf-up;
         unf-shift; unf-self; unf-idem)
open import strong.Boundary

private
  variable
    Δ : TCtx
    A A′ B C B₀ B₁ B₂ : Ty
    L L′ M M′ N N′ V W F : Term
    Θ Θ₁ Θ₂ : BCtx
    n x : ℕ

------------------------------------------------------------------------
-- Term-variable substitution (for Beta).  Identity on wrappers: a wrapped value
-- is term-closed (its body is typed at []), so no term variable reaches inside.
------------------------------------------------------------------------

extⁿ : (ℕ → ℕ) → (ℕ → ℕ)
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renameᵀᵐ : (ℕ → ℕ) → Term → Term
renameᵀᵐ ρ (` x)          = ` (ρ x)
renameᵀᵐ ρ ($ n)          = $ n
renameᵀᵐ ρ (ƛ A ∙ N)      = ƛ A ∙ renameᵀᵐ (extⁿ ρ) N
renameᵀᵐ ρ (L · M)        = renameᵀᵐ ρ L · renameᵀᵐ ρ M
renameᵀᵐ ρ (Λ N)          = Λ (renameᵀᵐ ρ N)
renameᵀᵐ ρ (L ·[ B , A ]) = renameᵀᵐ ρ L ·[ B , A ]
renameᵀᵐ ρ (M ⟪ Θ , B₀ ⟫) = M ⟪ Θ , B₀ ⟫

-- Renaming a wrapper's type variables (ρ : Γ → Γ').  A REVEAL rep is a type
-- over the PLAIN exterior (the parallel reveal block), so it renames by ρ
-- itself, as do conceal indices; B₀ lives over the boundary frame
-- (reveals ++ Γ) so it renames by liftⁿ (revs Θ) ρ; the body
-- and conceal reps live over the interior, which renames by intRen —
-- identity below a conceal that absorbs ρ (a conceal restricts to Γ↓X, and
-- restrictRen X ρ is the induced renaming on Γ↓X).
liftⁿ : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
liftⁿ zero    ρ = ρ
liftⁿ (suc r) ρ = extᵗ (liftⁿ r ρ)

restrictRen : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
restrictRen X ρ j = ρ (suc X + j) ∸ suc (ρ X)

-- interior renaming (whole-Γ): a SINGLE restriction at cmax (deepRen), lifted
-- past the reveal variables.  restrictRen c is the induced renaming on Γ↓c.
deepRen : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
deepRen zero    ρ = ρ
deepRen (suc c) ρ = restrictRen c ρ

intRen : (ℕ → ℕ) → BCtx → (ℕ → ℕ)
intRen ρ Θ = liftⁿ (revs Θ) (deepRen (cmax Θ) ρ)

-- A cnc⋆ renames its INDEX only: there is no rep to rename
-- (StarConcealProbe §6, ren-⋆-index).
renᴮ : (ℕ → ℕ) → (ℕ → ℕ) → BCtx → BCtx
renᴮ ρ ir []            = []
renᴮ ρ ir (rvl A ∷ Θ)   = rvl (renameᵗ ρ A) ∷ renᴮ ρ ir Θ
renᴮ ρ ir (rvl⋆ ∷ Θ)    = rvl⋆ ∷ renᴮ ρ ir Θ
renᴮ ρ ir (cnc X A ∷ Θ) = cnc (ρ X) (renameᵗ ir A) ∷ renᴮ ρ ir Θ
renᴮ ρ ir (cnc⋆ X ∷ Θ)  = cnc⋆ (ρ X) ∷ renᴮ ρ ir Θ

-- Shifting the conceal reps.  TyWrap grows the interior by ONE fresh variable
-- (the new reveal), so the conceal reps — which live over the WHOLE interior
-- — must be renamed by suc.  Reveal reps are exterior and untouched, so
-- neither face's reveal side moves.
shiftReps : BCtx → BCtx
shiftReps []            = []
shiftReps (rvl A ∷ Θ)   = rvl A ∷ shiftReps Θ
shiftReps (rvl⋆ ∷ Θ)    = rvl⋆ ∷ shiftReps Θ
shiftReps (cnc X A ∷ Θ) = cnc X (renameᵗ suc A) ∷ shiftReps Θ
shiftReps (cnc⋆ X ∷ Θ)  = cnc⋆ X ∷ shiftReps Θ

revs-shiftReps : ∀ Θ → revs (shiftReps Θ) ≡ revs Θ
revs-shiftReps []            = refl
revs-shiftReps (rvl A ∷ Θ)   = cong suc (revs-shiftReps Θ)
revs-shiftReps (rvl⋆ ∷ Θ)    = cong suc (revs-shiftReps Θ)
revs-shiftReps (cnc X A ∷ Θ) = revs-shiftReps Θ
revs-shiftReps (cnc⋆ X ∷ Θ)  = revs-shiftReps Θ

cmax-shiftReps : ∀ Θ → cmax (shiftReps Θ) ≡ cmax Θ
cmax-shiftReps []            = refl
cmax-shiftReps (rvl A ∷ Θ)   = cmax-shiftReps Θ
cmax-shiftReps (rvl⋆ ∷ Θ)    = cmax-shiftReps Θ
cmax-shiftReps (cnc X A ∷ Θ) = cong (suc X ⊔_) (cmax-shiftReps Θ)
cmax-shiftReps (cnc⋆ X ∷ Θ)  = cong (suc X ⊔_) (cmax-shiftReps Θ)

------------------------------------------------------------------------
-- The AMBIENT dual boundary.  Θᵈ = dualᴳ Γ Θ turns the boundary inside out:
-- its exterior is intOf Γ Θ and its interior REBUILDS Γ.  Every REVEAL of Θ
-- becomes a CONCEAL of Θᵈ at its interior index, carrying its EXTERNAL FACE
-- — which, under the PARALLEL reveal block, is the rep AS STORED (a Γ-type,
-- and a conceal rep lives over the dual's interior = Γ); every Γ-slot
-- 0 … cmax Θ ∸ 1 that Θ dropped becomes a REVEAL of Θᵈ, whose rep is
--
--   * Θ's own conceal rep for that slot, if Θ conceals it — already a type
--     over the dual's exterior, so it is copied unchanged (the telescopic
--     lift by k dissolves with the parallel reading);
--   * otherwise the slot is BLOCKED, and the dual COPIES Γ's own entry —
--     a `rvld B` becomes a reveal at B, an `abst` becomes the REP-LESS
--     reveal rvl⋆.  Copying is what keeps the rebuild exact: dualᵇ, which
--     invented a dummy rep at every blocked slot, lost the knowledge and
--     broke preservation (notes/old/AmbientDualProbe.agda §3, §5).
--
-- Γ's entry at slot i is a type over Γ ↓ i, whose k = cmax Θ ∸ suc i
-- shallowest slots are the DEEPER slots the dual rebuilds and whose rest is
-- the kept part of Γ.  A rep over the dual's PLAIN exterior may not name the
-- former (that is CHAINED knowledge — AmbientDualProbe §6b, the case the
-- reverted telescope was buying), so the copy is guarded by `dfree 0 k`: the
-- knowledge is copied when the rep names no other dropped slot, and
-- otherwise the dual falls back to the rep-less rvl⋆.  Resolving a chained
-- rep would need the SAME knowledge-closure operator as candidate (a) for
-- (R2); until that is ruled on, the widened fallback's obligation lives
-- inside strong.DualDef's DualRep≈ / DualInt≈ parameters.
------------------------------------------------------------------------

repOf : ℕ → BCtx → Ty            -- the rep Θ conceals slot i at (`ℕ if none)
repOf i []            = `ℕ
repOf i (rvl A ∷ Θ)   = repOf i Θ
repOf i (rvl⋆ ∷ Θ)    = repOf i Θ
repOf i (cnc⋆ X ∷ Θ)  = repOf i Θ
repOf i (cnc X A ∷ Θ) with i ≟ X
repOf i (cnc X A ∷ Θ) | yes _ = A
repOf i (cnc X A ∷ Θ) | no  _ = repOf i Θ

-- a copied knowledge rep, moved from Γ ↓ i to the dual's exterior: its first
-- k indices are dropped by dnT (legitimate exactly when dfree 0 k holds) and
-- the rest lands above the reveal block Θ keeps
copyRep : ℕ → ℕ → Ty → Ty
copyRep k n B = renameᵗ (n +_) (dnT k B)

-- the SECOND-CHANCE COPY (candidate (a″), UpToProbe §4 / entᴳ≈).  A CHAINED
-- rep — one naming another slot the boundary drops — is not expressible over
-- the dual's plain exterior, so the raw copy's `dfree 0 k` guard refuses it
-- and the knowledge used to be LOST to rvl⋆ (BReduction's Γp / Pc's site).
-- The dual now RETRIES with the rep UNFOLDED IN ITS OWN TAIL Γ ↓ i, which
-- collapses the chain; the copy then differs from Γ's entry by exactly one
-- unfolding, which is what _≼≈_ compares.
unfEnt : TCtx → ℕ → Ty → Ty
unfEnt Γ i B = unfoldᵉ (Γ ↓ i) B

entᴳ : TCtx → BCtx → ℕ → ℕ → BEntry   -- Γ, Θ, slot i, deeper dual reveals k
entᴳ Γ Θ i k with isConc i Θ
entᴳ Γ Θ i k | true  = rvl (repOf i Θ)
entᴳ Γ Θ i k | false with entAt Γ i
entᴳ Γ Θ i k | false | abst     = rvl⋆
entᴳ Γ Θ i k | false | xrvld B  = rvl⋆
entᴳ Γ Θ i k | false | rvld B with dfree 0 k B
entᴳ Γ Θ i k | false | rvld B | true  = rvl (copyRep k (revs Θ) B)
entᴳ Γ Θ i k | false | rvld B | false with dfree 0 k (unfEnt Γ i B)
entᴳ Γ Θ i k | false | rvld B | false | true  =
  rvl (copyRep k (revs Θ) (unfEnt Γ i B))
entᴳ Γ Θ i k | false | rvld B | false | false = rvl⋆

rvlsᴳ : ℕ → ℕ → TCtx → BCtx → BCtx    -- k reveals, for dropped slots s, s+1, …
rvlsᴳ zero    s Γ Θ = []
rvlsᴳ (suc k) s Γ Θ = entᴳ Γ Θ s k ∷ rvlsᴳ k (suc s) Γ Θ

-- The dual's CONCEAL block, ENTRY-INDEPENDENT (notes/DualLicenseDesign.md §2;
-- DualLicenseProbe's cncOfRevs³).  Every REP-CARRYING reveal is licensable —
-- by (bwf-↓) when the interior knows the slot, by (bwf-↓x) when it only
-- x-knows it — so the block no longer has to CONSULT the interior entry to
-- choose between cnc and cnc⋆, as the cnc⋆ probe's version did.  The one
-- change from today's live block is the rvl⋆ case: it emits cnc⋆, not the
-- INVENTED rep `cnc j ℕ`, which nothing licenses (StarConcealProbe §4.3,
-- ¬DualCnc-rvl⋆).
cncOfRevs : ℕ → BCtx → BCtx      -- conceal each reveal var, at j, j+1, …
cncOfRevs j []            = []
cncOfRevs j (rvl A ∷ Θ)   = cnc j A ∷ cncOfRevs (suc j) Θ
cncOfRevs j (rvl⋆ ∷ Θ)    = cnc⋆ j ∷ cncOfRevs (suc j) Θ
cncOfRevs j (cnc X A ∷ Θ) = cncOfRevs j Θ
cncOfRevs j (cnc⋆ X ∷ Θ)  = cncOfRevs j Θ

dualᴳ : TCtx → BCtx → BCtx
dualᴳ Γ Θ = rvlsᴳ (cmax Θ) 0 Γ Θ ++ cncOfRevs 0 Θ

-- The two boundary frames hold the same slots in a different order:
-- [reveals of Θ][dropped Γ-slots][kept Γ-slots] becomes
-- [dropped Γ-slots][reveals of Θ][kept Γ-slots], so a boundary type read
-- over Θ's frame is transported to Θᵈ's frame by this block swap.
swapIdx : ℕ → ℕ → ℕ → ℕ
swapIdx r c X with X <? r
swapIdx r c X | yes _ = c + X
swapIdx r c X | no  _ with (X ∸ r) <? c
swapIdx r c X | no _ | yes _ = X ∸ r
swapIdx r c X | no _ | no  _ = X

swapᵇ : BCtx → ℕ → ℕ
swapᵇ Θ = swapIdx (revs Θ) (cmax Θ)

------------------------------------------------------------------------
-- THE KNOWLEDGE ORDERING _≼≈_ (its lemmas, and the design commentary that
-- motivates the four clauses, are further down at the ⊢retag≈ block).  It
-- is DECLARED here because Merge's premise mentions it and the reduction
-- relation mentions Merge.
------------------------------------------------------------------------

infix 4 _≼≈_
data _≼≈_ : TCtx → TCtx → Set where
  ≼≈[]    : [] ≼≈ []
  ≼≈abst  : ∀ {Δ Δ' E} → Δ ≼≈ Δ' → (abst ∷ Δ) ≼≈ (E ∷ Δ')
  ≼≈xrvld : ∀ {Δ Δ' A} → Δ ≼≈ Δ' → (xrvld A ∷ Δ) ≼≈ (xrvld A ∷ Δ')
  ≼≈rvld  : ∀ {Δ Δ' A B} → Δ ≼≈ Δ' → A ≈Δ̄⟨ Δ' ⟩ B
          → (rvld A ∷ Δ) ≼≈ (rvld B ∷ Δ')

------------------------------------------------------------------------
-- MERGE: THE COMPOSITE BOUNDARY  Θ₁ ⊕ Θ₂  (Decision 3; ported from
-- notes/old/MergeProbe.agda §1 to the LIVE entry forms).
--
-- Θ₂ sits OUTSIDE Θ₁ — the redex is  (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ — so
-- Θ₁'s exterior is Θ₂'s interior Ψ₂ = intOf Δ Θ₂, and the composite's
-- exterior is Δ while its interior is Θ₁'s interior Ψ₁.  Two maps move a
-- Ψ₂-type to the two ends, and BOTH are already live:
--
--   outSub Θ₂ :  Ψ₂-index ↦ Δ-type    (strong.Boundary — the read-back the
--                reversal premise runs on: a Θ₂-reveal ↦ its stored rep, a
--                kept slot ↦ its exterior index)
--   rdSub  Θ₁ :  Ψ₂-index ↦ Ψ₁-type   (strong.Boundary — γcnc, the interior
--                reading: a Θ₁-conceal ↦ its rep, a kept slot ↦ its
--                interior index)
--
-- ⊕ is  mapL Θ₂ Θ₁ ++ mapR Θ₁ 0 Θ₂, entry by entry:
--
--   * Θ₁'s REVEALS stay reveals with their reps PUSHED OUT through Θ₂ (a
--     reveal's rep is read in the PLAIN exterior, which is now Δ).  A
--     rep-less rvl⋆ stays rvl⋆ — there is no rep to push, and the slot
--     stays blocked, which is what it was.
--   * Θ₁'s CONCEAL of a slot Θ₂ REVEALS cancels — BOTH entries vanish (the
--     deleting clause: mapL drops the conceal, mapR drops that reveal).
--     A cnc⋆ of a Θ₂-reveal cancels the same way (its slot carried no rep
--     on either side).  For the MIXED pairs see the note below.
--   * Θ₁'s conceals of INHERITED exterior slots RE-INDEX from Ψ₂ to Δ: the
--     Ψ₂-index X ≥ revs Θ₂ is the Δ-index cmax Θ₂ + (X ∸ revs Θ₂).  Their
--     reps already live over Ψ₁ = the composite's interior, so they are
--     copied unchanged.
--   * Θ₂'s CONCEALS (and cnc⋆) stay at their Δ-indices, with their reps
--     pushed IN through Θ₁ (they now live over Ψ₁) — exactly where the old
--     mapR put them.
--
-- THE MIXED CANCEL PAIRS.  A cnc⋆ of a rvl (Θ₁ ⋆-conceals a slot Θ₂
-- revealed WITH a rep) and a cnc of a rvl⋆ (Θ₁ conceals at a rep a slot Θ₂
-- revealed rep-lessly) both cancel here as well — the clause is on the
-- INDEX, not on the flavours.  Neither can carry knowledge across the
-- cancel: a cnc⋆ asserts nothing (bwf-⋆↓'s only premise is that the slot
-- exists) and a rvl⋆'s slot is `blk` in baseS, so no boundary type names
-- it and the composite's faces never consult it.  The cancel is therefore
-- sound on all four combinations; only the rvl/cnc pair transports a rep,
-- and that is the pair cancel-agree is about.
------------------------------------------------------------------------

inSub : BCtx → Substᵗ                  -- Ψ₂-index ↦ Ψ₁-type
inSub = rdSub

mapL : BCtx → BCtx → BCtx              -- mapL Θ₂ Θ₁ : Θ₁'s entries, moved
mapL Θ₂ []            = []
mapL Θ₂ (rvl A ∷ Θ)   = rvl (substᵗ (outSub Θ₂) A) ∷ mapL Θ₂ Θ
mapL Θ₂ (rvl⋆ ∷ Θ)    = rvl⋆ ∷ mapL Θ₂ Θ
mapL Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
mapL Θ₂ (cnc X A ∷ Θ) | yes _ = mapL Θ₂ Θ                    -- CANCEL
mapL Θ₂ (cnc X A ∷ Θ) | no  _ =
  cnc (cmax Θ₂ + (X ∸ revs Θ₂)) A ∷ mapL Θ₂ Θ
mapL Θ₂ (cnc⋆ X ∷ Θ)  with X <? revs Θ₂
mapL Θ₂ (cnc⋆ X ∷ Θ)  | yes _ = mapL Θ₂ Θ                    -- CANCEL (⋆)
mapL Θ₂ (cnc⋆ X ∷ Θ)  | no  _ =
  cnc⋆ (cmax Θ₂ + (X ∸ revs Θ₂)) ∷ mapL Θ₂ Θ

mapR : BCtx → ℕ → BCtx → BCtx          -- mapR Θ₁ j Θ₂ : Θ₂'s entries, moved
mapR Θ₁ j []            = []
mapR Θ₁ j (rvl A ∷ Θ)   with j <? cmax Θ₁
mapR Θ₁ j (rvl A ∷ Θ)   | yes _ = mapR Θ₁ (suc j) Θ          -- CANCELLED
mapR Θ₁ j (rvl A ∷ Θ)   | no  _ = rvl A ∷ mapR Θ₁ (suc j) Θ
mapR Θ₁ j (rvl⋆ ∷ Θ)    with j <? cmax Θ₁
mapR Θ₁ j (rvl⋆ ∷ Θ)    | yes _ = mapR Θ₁ (suc j) Θ          -- CANCELLED
mapR Θ₁ j (rvl⋆ ∷ Θ)    | no  _ = rvl⋆ ∷ mapR Θ₁ (suc j) Θ
mapR Θ₁ j (cnc X A ∷ Θ) = cnc X (substᵗ (inSub Θ₁) A) ∷ mapR Θ₁ j Θ
mapR Θ₁ j (cnc⋆ X ∷ Θ)  = cnc⋆ X ∷ mapR Θ₁ j Θ

infixl 6 _⊕_
_⊕_ : BCtx → BCtx → BCtx
Θ₁ ⊕ Θ₂ = mapL Θ₂ Θ₁ ++ mapR Θ₁ 0 Θ₂

------------------------------------------------------------------------
-- THE FRAME MAPS.  ⊕'s frame is
--   [reveals of Θ₁][surviving reveals of Θ₂][Δ]
-- of reveal width R⊕ and dropping C⊕ exterior slots (revs-⊕ / cmax-⊕
-- below).  up⊕ embeds Ψ₁ back into that frame; mrg₁ carries Θ₁'s frame
-- into it and mrg₂ carries Θ₂'s.  Both are SUBSTITUTIONS, not renamings:
-- a slot killed by the cancel clause must be replaced by the agreed rep.
------------------------------------------------------------------------

R⊕ C⊕ : BCtx → BCtx → ℕ
R⊕ Θ₁ Θ₂ = revs Θ₁ + (revs Θ₂ ∸ cmax Θ₁)
C⊕ Θ₁ Θ₂ = cmax Θ₂ + (cmax Θ₁ ∸ revs Θ₂)

upF : ℕ → ℕ → ℕ → ℕ                    -- Ψ₁-index ↦ ⊕-frame index
upF R C j with j <? R
upF R C j | yes _ = j
upF R C j | no  _ = R + (C + (j ∸ R))

up⊕ : BCtx → BCtx → ℕ → ℕ
up⊕ Θ₁ Θ₂ = upF (R⊕ Θ₁ Θ₂) (C⊕ Θ₁ Θ₂)

mrgΨ : BCtx → BCtx → ℕ → Ty            -- a Ψ₂-index, into ⊕'s frame
mrgΨ Θ₁ Θ₂ X with X <? revs Θ₂
mrgΨ Θ₁ Θ₂ X | yes _ with X <? cmax Θ₁
mrgΨ Θ₁ Θ₂ X | yes _ | yes _ =
  renameᵗ (up⊕ Θ₁ Θ₂) (repOf X Θ₁)                     -- CANCELLED slot
mrgΨ Θ₁ Θ₂ X | yes _ | no  _ = ` (revs Θ₁ + (X ∸ cmax Θ₁))
mrgΨ Θ₁ Θ₂ X | no  _ = ` (R⊕ Θ₁ Θ₂ + (cmax Θ₂ + (X ∸ revs Θ₂)))

mrg₁ : BCtx → BCtx → Substᵗ            -- Θ₁'s frame ↦ ⊕'s frame
mrg₁ Θ₁ Θ₂ j with j <? revs Θ₁
mrg₁ Θ₁ Θ₂ j | yes _ = ` j
mrg₁ Θ₁ Θ₂ j | no  _ = mrgΨ Θ₁ Θ₂ (j ∸ revs Θ₁)

mrg₂ : BCtx → BCtx → Substᵗ            -- Θ₂'s frame ↦ ⊕'s frame
mrg₂ Θ₁ Θ₂ j with j <? revs Θ₂
mrg₂ Θ₁ Θ₂ j | yes _ with j <? cmax Θ₁
mrg₂ Θ₁ Θ₂ j | yes _ | yes _ =
  renameᵗ (up⊕ Θ₁ Θ₂) (repOf j Θ₁)                     -- CANCELLED slot
mrg₂ Θ₁ Θ₂ j | yes _ | no  _ = ` (revs Θ₁ + (j ∸ cmax Θ₁))
mrg₂ Θ₁ Θ₂ j | no  _ = ` (R⊕ Θ₁ Θ₂ + (j ∸ revs Θ₂))

------------------------------------------------------------------------
-- B₂′ — THE MERGED BOUNDARY TYPE, AND WHAT MERGE ASKS OF THE REDEX.
--
-- Two candidates, the two transports above (MergeProbe §8):
--
--   substᵗ (mrg₁ Θ₁ Θ₂) B₁   -- the INTERNAL face is then FREE (⊕-γ)
--   substᵗ (mrg₂ Θ₁ Θ₂) B₂   -- the EXTERNAL face is then free (⊕-ρ)
--
-- The landed choice is the FIRST (`mrgB`), because the internal face is
-- the one the body's own typing forces and ⊕-γ discharges it as a THEOREM
-- for every redex, whereas the second is refuted outright by any tower
-- whose inner boundary reveals over the outer one (notes/InstallGauntlet
-- §9c: ¬γ-mrg₂-tower).  This DIVERGES from the TOPLAS reading "keep the
-- OUTER boundary type" — see the note in notes.md.
--
-- The external face is then NOT free, and it is not a theorem either: the
-- composite's ρ-face reads B₁'s slots out through Θ₂, which resolves a
-- CONCEAL of Θ₂ to its rep, while the redex's own type keeps the concealed
-- VARIABLE.  The two agree up to one unfolding (≈Δ̄) and NOT
-- syntactically, and preservation needs syntactic agreement — so the
-- equation is a PREMISE of the rule, i.e. an invariant carried by the
-- relation, in the design's own idiom.  notes/InstallGauntlet §9d has the
-- counterexample that makes it a premise rather than a lemma.
--
-- MergeOK collects, in one place, exactly what ⊕ does not supply for the
-- merged wrapper's (env):
--   (1) Θ₁ drops only slots Θ₂ reveals   — ⊕-γ's side condition;
--   (2) the composite is a well-formed boundary over Δ;
--   (3) B₂′ is Scoped over the composite's stack;
--   (4) the contexts compose, in the direction ⊢retag≈ consumes;
--   (5) the composite's EXTERNAL face is the redex's own type.
-- The INTERNAL face is free (⊕-γ) and so is the frame arithmetic
-- (revs-⊕ / cmax-⊕).
------------------------------------------------------------------------

mrgB : BCtx → BCtx → Ty → Ty
mrgB Θ₁ Θ₂ B₁ = substᵗ (mrg₁ Θ₁ Θ₂) B₁

MergeOK : TCtx → BCtx → BCtx → Ty → Ty → Set
MergeOK Δ Θ₁ Θ₂ B₁ B₂ =
    (cmax Θ₁ ≤ revs Θ₂)
  × (Δ ∣ intOf Δ (Θ₁ ⊕ Θ₂) ⊢ᵇ (Θ₁ ⊕ Θ₂))
  × Scoped (baseS (Θ₁ ⊕ Θ₂) Δ) (mrgB Θ₁ Θ₂ B₁)
  × (intOf (intOf Δ Θ₂) Θ₁ ≼≈ intOf Δ (Θ₁ ⊕ Θ₂))
  × (substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (ρᵇ Θ₂) B₂)

renameᵀ : (ℕ → ℕ) → Term → Term          -- rename TYPE variables
renameᵀ ρ (` x)          = ` x
renameᵀ ρ ($ n)          = $ n
renameᵀ ρ (ƛ A ∙ N)      = ƛ (renameᵗ ρ A) ∙ renameᵀ ρ N
renameᵀ ρ (L · M)        = renameᵀ ρ L · renameᵀ ρ M
renameᵀ ρ (Λ N)          = Λ (renameᵀ (extᵗ ρ) N)
renameᵀ ρ (L ·[ B , A ]) = renameᵀ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renameᵀ ρ (M ⟪ Θ , B₀ ⟫) =
  renameᵀ (intRen ρ Θ) M
  ⟪ renᴮ ρ (intRen ρ Θ) Θ , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫

⇑ᵀ : Term → Term
⇑ᵀ = renameᵀ suc

extsᵀᵐ : (ℕ → Term) → (ℕ → Term)
extsᵀᵐ σ zero    = ` zero
extsᵀᵐ σ (suc x) = renameᵀᵐ suc (σ x)

substᵀᵐ : (ℕ → Term) → Term → Term
substᵀᵐ σ (` x)          = σ x
substᵀᵐ σ ($ n)          = $ n
substᵀᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵀᵐ (extsᵀᵐ σ) N
substᵀᵐ σ (L · M)        = substᵀᵐ σ L · substᵀᵐ σ M
substᵀᵐ σ (Λ N)          = Λ (substᵀᵐ (λ x → ⇑ᵀ (σ x)) N)
substᵀᵐ σ (L ·[ B , A ]) = substᵀᵐ σ L ·[ B , A ]
substᵀᵐ σ (M ⟪ Θ , B₀ ⟫) = M ⟪ Θ , B₀ ⟫

infix 8 _[_]ᵐ
_[_]ᵐ : Term → Term → Term
N [ W ]ᵐ = substᵀᵐ (λ { zero → W ; (suc x) → ` x }) N

------------------------------------------------------------------------
-- TyPeel's INNER TYPE-APPLICATION ANNOTATION.
--
-- TyPeel pushes a type application INSIDE the boundary, where the wrapped
-- value has the boundary's INTERNAL face.  A type application carries its
-- ∀-body annotation, and that annotation is FORCED: the body of
--   ⇑ᵗ (substᵗ (γᵇ Θ) (`∀ B₀))
--     =  `∀ (renameᵗ (extᵗ suc) (substᵗ (extsᵗ (γᵇ Θ)) B₀))
-- — the internal face of the ∀ boundary type, weakened by the ONE fresh
-- slot the new reveal adds to the interior.  Nothing here is a choice; it
-- is the type the interior's own (tapp) demands.
------------------------------------------------------------------------

peelB : BCtx → Ty → Ty
peelB Θ B₀ = renameᵗ (extᵗ suc) (substᵗ (extsᵗ (γᵇ Θ)) B₀)

------------------------------------------------------------------------
-- ACTIVE AND INERT BOUNDARIES (Siek & Chen, "Parameterized Cast Calculi
-- and Reusable Meta-theory for Gradually Typed Lambda Calculi", JFP
-- 31(e30), 2021, §3; the mapping is notes/ParameterizedCastCalculi.md).
--
-- A boundary plays the role of the paper's CAST, and its FACE B₀ — read
-- together with Θ's slot kinds — is a DECIDABLE, purely syntactic
-- classifier:
--
--   INERT   the ⇒ and ∀ faces (the paper's CROSS casts: they are
--           decomposed at their USE site, by Peel and by TyWrap/TyPeel,
--           never at rest), and a VARIABLE face ` X that Θ does NOT
--           reveal (revs Θ ≤ X — a conceal slot, or an ambient one).
--           There ρᵇ reads the face back to an ABSTRACT variable, so no
--           elimination can ever consume it and none is needed: these
--           are the SEALED values, `5 ⟪ ↓X:=ℕ , X ⟫`.
--           An inert boundary around a value IS a value (V-⟪⟫) — the
--           paper's `Vcast`, and the discipline this development was
--           missing (notes/DECISIONS.md, Decision 6).
--   ACTIVE  a REVEAL-variable face ` X (X < revs Θ): ρᵇ reads it to the
--           reveal's REP, so the wrapper is concrete outside and
--           ABSTRACT inside, and no elimination can be pushed inward at
--           all (ProgressDef's obstruction) — the nesting must COLLAPSE
--           (Merge).  And the BASE faces ℕ / 𝔹, whose two readings are
--           identical, so the boundary is vacuous on the type and is
--           simply dropped (Drop$) — the paper's `baseNotInert`.
--           An active boundary is NOT a value; it STEPS.
--
-- Θ ≡ [] needs no special case: revs [] = 0, so a variable face is inert
-- there and a base face active, exactly as anywhere else.  That is what
-- retires the standalone Drop∅ (Decision 3's addendum): an empty
-- boundary is classified by its face like every other.
--
-- DETERMINISM FALLS OUT (V-¬-→ / det, below): the collapse rules never
-- fire on a value because their redex's face is active, and Peel /
-- TyWrap / TyPeel need the SYNTACTIC ⇒ / ∀ face, which is inert.
------------------------------------------------------------------------

data Inert : BCtx → Ty → Set where
  I-⇒   : ∀ {Θ A′ B′}             → Inert Θ (A′ ⇒ B′)
  I-∀   : ∀ {Θ B′}                → Inert Θ (`∀ B′)
  I-var : ∀ {Θ X} → revs Θ ≤ X    → Inert Θ (` X)

data Active : BCtx → Ty → Set where
  A-var : ∀ {Θ X} → X < revs Θ    → Active Θ (` X)
  A-ℕ   : ∀ {Θ}                   → Active Θ `ℕ
  A-𝔹   : ∀ {Θ}                   → Active Θ `𝔹

-- the paper's ActiveOrInert: the classification is TOTAL, and decidable
-- by the face's head constructor plus one _≤?_ on the slot index
ActiveOrInert : ∀ Θ B₀ → Active Θ B₀ ⊎ Inert Θ B₀
ActiveOrInert Θ (` X)     with revs Θ ≤? X
ActiveOrInert Θ (` X)     | yes ge = inj₂ (I-var ge)
ActiveOrInert Θ (` X)     | no  hi = inj₁ (A-var (≰⇒> hi))
ActiveOrInert Θ `ℕ        = inj₁ A-ℕ
ActiveOrInert Θ `𝔹        = inj₁ A-𝔹
ActiveOrInert Θ (A′ ⇒ B′) = inj₂ I-⇒
ActiveOrInert Θ (`∀ B′)   = inj₂ I-∀

-- … and never BOTH.  This one fact closes every rule overlap below.
active-not-inert : ∀ {Θ B₀} → Active Θ B₀ → Inert Θ B₀ → ⊥
active-not-inert (A-var lt) (I-var ge) = ≤⇒≯ ge lt

-- INERTNESS IS STABLE UNDER TYPE-VARIABLE RENAMING (what
-- strong.Canonical's Value-renameᵀ needs, since renameᵀ rebuilds the
-- boundary): renaming keeps a face's head constructor, and a NON-REVEALED
-- slot stays non-revealed, because renᴮ preserves the reveal count and
-- liftⁿ maps the ≥-block into itself.
revs-renᴮ : ∀ ρ ir Θ → revs (renᴮ ρ ir Θ) ≡ revs Θ
revs-renᴮ ρ ir []            = refl
revs-renᴮ ρ ir (rvl A ∷ Θ)   = cong suc (revs-renᴮ ρ ir Θ)
revs-renᴮ ρ ir (rvl⋆ ∷ Θ)    = cong suc (revs-renᴮ ρ ir Θ)
revs-renᴮ ρ ir (cnc X A ∷ Θ) = revs-renᴮ ρ ir Θ
revs-renᴮ ρ ir (cnc⋆ X ∷ Θ)  = revs-renᴮ ρ ir Θ

liftⁿ-≥ : ∀ r ρ X → r ≤ X → r ≤ liftⁿ r ρ X
liftⁿ-≥ zero    ρ X       le       = z≤n
liftⁿ-≥ (suc r) ρ (suc X) (s≤s le) = s≤s (liftⁿ-≥ r ρ X le)

Inert-ren : ∀ ρ ir Θ B₀ → Inert Θ B₀
  → Inert (renᴮ ρ ir Θ) (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
Inert-ren ρ ir Θ (A′ ⇒ B′) I-⇒ = I-⇒
Inert-ren ρ ir Θ (`∀ B′)   I-∀ = I-∀
Inert-ren ρ ir Θ (` X) (I-var ge) =
  I-var (subst (_≤ liftⁿ (revs Θ) ρ X) (sym (revs-renᴮ ρ ir Θ))
               (liftⁿ-≥ (revs Θ) ρ X ge))

------------------------------------------------------------------------
-- Values.  V-⟪⟫ now carries the paper's INERT premise.
------------------------------------------------------------------------

data GVal : Term → Set
data Value : Term → Set

data GVal where
  G-ƛ : GVal (ƛ A ∙ N)
  G-Λ : Value V → GVal (Λ V)

data Value where
  V-$  : Value ($ n)
  V-G  : GVal V → Value V
  V-⟪⟫ : Value V → Inert Θ B₀ → Value (V ⟪ Θ , B₀ ⟫)

------------------------------------------------------------------------
-- Reduction.  Γ-INDEXED: the index is the type context in which the redex
-- sits, exactly the Δ of the typing judgement, and only Peel consults it.
------------------------------------------------------------------------

infix 2 _⊢_-→_
data _⊢_-→_ : TCtx → Term → Term → Set where

  -- TyBeta: a boundary is BORN.  The ∀-body B is recorded as the BOUNDARY type;
  -- internal type = B[γ] = B, external type = B[ρ] = B[A]ᵗ.
  TyBeta : Value V
      → Δ ⊢ (Λ V) ·[ B , A ] -→ V ⟪ rvl A ∷ [] , B ⟫

  -- Beta
  Beta : Value W
      → Δ ⊢ (ƛ A ∙ N) · W -→ N [ W ]ᵐ

  -- R1: a wrapped Λ meets a TYPE APPLICATION (the DIRECT-COMBINE form —
  -- notes/DECISIONS.md, Decision 2 as revised).  The elimination CONSUMES the
  -- Λ: the Λ-binder's slot IS the new reveal slot, so the type argument A is
  -- RECORDED as that reveal's rep — never pushed inward, which is what made
  -- the old design unsound (Example 8: A may name a variable the interior
  -- blocks).  There is NO ⇑ᵀ on the term (the design's no-term-shift
  -- principle: a shift forgets which variables a term may not mention); the
  -- CONCEAL REPS do shift, but they are types, and they must, since they live
  -- over the whole interior, which gains the new reveal's variable
  -- (shiftReps).  The type argument A is recorded UNLIFTED: under the
  -- PARALLEL reading a reveal's rep is read in the plain exterior, where A
  -- already lives, so its external face is A on the nose.  (The lift
  -- `renameᵗ (revs Θ +_) A` was forced only by the reverted telescope.)
  -- Λ-bodied only, and it stays that way under PEEL: for a Λ body the
  -- Λ-binder's slot IS the new reveal slot, so nothing moves in the term
  -- and the step is a single one.  A WRAPPER-bodied wrapper at a ∀ face is
  -- TyPeel's redex (the two are syntactically disjoint: `Λ V` vs
  -- `V ⟪ Θ₁ , B₁ ⟫`).
  TyWrap : Value V
      → Δ ⊢ ((Λ V) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ V ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  -- TyPeel (Decision 5, fork (b), the ∀ face) — GENERALIZES TyWrap from a
  -- Λ-bodied wrapper to a WRAPPER-bodied one.  The elimination is pushed
  -- INSIDE the boundary, exactly as Peel pushes an application inside; the
  -- new reveal ↑·:=A is minted on the boundary as in TyWrap, and the INNER
  -- type application instantiates at THE NEW REVEAL'S OWN ABSTRACT VARIABLE
  -- ` 0 — no exterior type is ever pushed inward (Example 8's constraint).
  --
  -- This is the one rule that WEAKENS the wrapped term (⇑ᵀ), and it must:
  -- the new reveal occupies interior slot 0, so a body that was written
  -- over the old interior has every type index one lower than the new
  -- interior's.  ⇑ᵀ is a pure WEAKENING — ⊢renameᵀ at `suc` (⊢⇑ᵀ below) —
  -- not the old "push the type argument inward", which is what Example 8
  -- refuted.  For a Λ body the weakening is unnecessary (the binder's slot
  -- is the reveal's), which is exactly why TyWrap is kept: see
  -- notes/DECISIONS.md, "Decision 5 install" — form (β).
  -- The INERT premise on the inner boundary is the value restriction, not
  -- decoration: without it the redex's body could be an ACTIVE wrapper,
  -- which steps by Merge under ξ-·[] — and TyPeel would clash with it.
  TyPeel : Value V → Inert Θ₁ B₁
      → Δ ⊢ ((V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ , `∀ B₀ ⟫) ·[ B , A ]
        -→ (⇑ᵀ (V ⟪ Θ₁ , B₁ ⟫) ·[ peelB Θ B₀ , ` 0 ])
           ⟪ rvl A ∷ shiftReps Θ , B₀ ⟫

  -- Peel (Decision 5, fork (b), the ⇒ face) — REPLACES Wrap.  A boundary
  -- meets an APPLICATION: the application is pushed INSIDE the boundary by
  -- ONE layer, and the argument crosses inward through the AMBIENT DUAL.
  -- Unlike the old Wrap the ƛ is NOT consumed and there is no
  -- β-substitution: the wrapped value may be ANY value, so the rule is
  -- total at an ⇒ face and progress needs no case analysis of the body.
  -- For a ƛ-bodied V, `Peel` followed by `ξ-⟪⟫ (Beta …)` reproduces
  -- exactly the old Wrap contractum (peel-is-wrap+beta below).
  --
  -- ALL READINGS ARE INWARD (γ-direction, functional): the outward,
  -- relational re-abstraction that a face-directed ⊕ would need is never
  -- performed — which is why the §9g double coincidence, where flattening
  -- is IMPOSSIBLE under any ⊕, simply runs here.
  --
  -- B₁ is read over Θ's boundary frame, so the dual's boundary type is B₁
  -- renamed by the frame permutation swapᵇ.  This is the ONE rule that
  -- reads the ambient Δ: the dual copies Δ's own entry at every slot Θ
  -- drops without concealing.
  Peel : Value V → Value W
      → Δ ⊢ ((V ⟪ Θ , B₁ ⇒ B₂ ⟫) · W)
        -→ (V · (W ⟪ dualᴳ Δ Θ , renameᵗ (swapᵇ Θ) B₁ ⟫)) ⟪ Θ , B₂ ⟫

  -- Merge (Decision 3, RESTRICTED BY DECISION 6 TO AN ACTIVE OUTER FACE)
  -- — the paper's `applyCast` at a REVEAL-VARIABLE face.  A wrapper-bodied
  -- wrapper collapses to ONE boundary.  The composite is Θ₁ ⊕ Θ₂ — Θ₁'s
  -- reveals with their reps pushed out, Θ₁'s conceals of Θ₂-revealed slots
  -- CANCELLED against those reveals, everything else re-indexed — and the
  -- merged boundary type is B₁ carried into the composite's frame (mrgB).
  -- MergeOK carries the five obligations the composite does not discharge
  -- on its own; the INTERNAL face is free (⊕-γ, a theorem).
  --
  -- THE TWO CLASSIFICATION PREMISES ARE THE DECISION-6 INSTALL.  The
  -- OUTER face is ACTIVE, so the redex is NOT a value — which is what
  -- §9j's counterexample cost (a value that steps, and a Peel that
  -- competes with it in argument position).  The INNER face is INERT, so
  -- the body IS a value and ξ-⟪⟫ cannot compete either.  Together they
  -- make Merge disjoint from every other rule.
  Merge : Value V → Inert Θ₁ B₁ → Active Θ₂ B₂
      → MergeOK Δ Θ₁ Θ₂ B₁ B₂
      → Δ ⊢ (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ -→ V ⟪ Θ₁ ⊕ Θ₂ , mrgB Θ₁ Θ₂ B₁ ⟫

  -- Drop$ — the paper's `baseNotInert` clause, and the whole of the
  -- BASE-FACE action set.  At a base face the two readings coincide
  -- (substᵗ σ `ℕ = `ℕ for every σ), so the boundary carries no type
  -- information; but the body must still be typeable in the EXTERIOR Δ,
  -- and that is exactly CancelProbe's lesson (CancelOK's CONTEXT
  -- conjunct is the load-bearing one — a face-only drop is UNSOUND).
  -- The rule is therefore stated on the body it is sound for: a NUMERAL,
  -- which ⊢$ types in any context whatever.  Nothing is lost, because
  -- the sharpened canonical form canon-ℕ says a VALUE of type ℕ is a
  -- numeral and nothing else: a wrapper of type ℕ would need an
  -- ℕ-reading INERT face, and by inert-ext there is none.  So this rule
  -- is TOTAL on well-typed active base-faced wrappers, and no
  -- base-faced merge clause is needed.
  --
  -- Drop∅ is RETIRED, not replaced: an empty boundary is now classified
  -- by its face like any other — `V ⟪ ∅ , B₁ ⇒ B₂ ⟫` and `V ⟪ ∅ , ` X ⟫`
  -- are inert VALUES (revs [] = 0, so every variable face is inert
  -- there), and `($ n) ⟪ ∅ , ℕ ⟫` is this rule's redex.
  Drop$ : Δ ⊢ ($ n) ⟪ Θ , `ℕ ⟫ -→ $ n

  -- ξ (congruence): the evaluation frames, left-to-right call-by-value.
  -- ξ-Λ and ξ-⟪⟫ are not optional bookkeeping: Λ V is a value only when V is
  -- (G-Λ) and V ⟪ Θ , B₀ ⟫ only when V is (V-⟪⟫), so the body of a Λ and the
  -- interior of a boundary must be reduced in place before either is a value
  -- — and each carries the index INTO the sub-term's own context.
  ξ-·-l : Δ ⊢ L -→ L′
        → Δ ⊢ L · M -→ L′ · M

  ξ-·-r : Value V → Δ ⊢ M -→ M′
        → Δ ⊢ V · M -→ V · M′

  ξ-·[] : Δ ⊢ L -→ L′
        → Δ ⊢ L ·[ B , A ] -→ L′ ·[ B , A ]

  ξ-Λ   : (abst ∷ Δ) ⊢ N -→ N′
        → Δ ⊢ Λ N -→ Λ N′

  ξ-⟪⟫  : intOf Δ Θ ⊢ M -→ M′
        → Δ ⊢ M ⟪ Θ , B₀ ⟫ -→ M′ ⟪ Θ , B₀ ⟫

------------------------------------------------------------------------
-- DETERMINISM AND VALUES-DON'T-STEP — *** NOW THEOREMS ***
-- (Jeremy's design law, 2026-09-04; the counterexamples they replace are
-- notes/InstallGauntlet §9j / §9k, restated there as UNIQUENESS proofs).
--
-- Both were FALSE before the Decision-6 install, for one reason: Merge
-- and Drop∅ were the only rules whose LEFT-HAND SIDE WAS A VALUE.  The
-- active/inert split removes that by construction — an active face is
-- not a value, and the collapse rules fire only at active faces — so the
-- whole rule table is pairwise disjoint:
--
--   Beta   vs Peel     bare ƛ vs ⇒-faced wrapper, in function position
--   TyBeta vs TyWrap   bare Λ vs ∀-faced wrapper
--   TyWrap vs TyPeel   Λ-bodied wrapper vs wrapper-bodied wrapper
--   Merge  vs Drop$    wrapper body vs numeral body
--   Merge/Drop$ vs Peel/TyWrap/TyPeel   ACTIVE vs SYNTACTIC ⇒/∀ face
--   collapse vs ξ-⟪⟫   the collapse's body is a value (V-¬-→)
--   ξ frames           left-to-right, each guarded by Value (V-¬-→)
------------------------------------------------------------------------

-- values do not step
V-¬-→ : ∀ {Δ V M′} → Value V → Δ ⊢ V -→ M′ → ⊥
V-¬-→ (V-G (G-Λ v)) (ξ-Λ st)        = V-¬-→ v st
V-¬-→ (V-⟪⟫ v i)    (ξ-⟪⟫ st)       = V-¬-→ v st
V-¬-→ (V-⟪⟫ v i)    (Merge _ _ a _) = active-not-inert a i
V-¬-→ (V-⟪⟫ v ())   Drop$

-- reduction is deterministic
det : ∀ {Δ M M₁ M₂} → Δ ⊢ M -→ M₁ → Δ ⊢ M -→ M₂ → M₁ ≡ M₂

det (TyBeta v)   (TyBeta w)   = refl
det (TyBeta v)   (ξ-·[] st)   = ⊥-elim (V-¬-→ (V-G (G-Λ v)) st)
det (ξ-·[] st)   (TyBeta v)   = ⊥-elim (V-¬-→ (V-G (G-Λ v)) st)

det (Beta v)     (Beta w)     = refl
det (Beta v)     (ξ-·-l st)   = ⊥-elim (V-¬-→ (V-G G-ƛ) st)
det (Beta v)     (ξ-·-r w st) = ⊥-elim (V-¬-→ v st)
det (ξ-·-l st)   (Beta v)     = ⊥-elim (V-¬-→ (V-G G-ƛ) st)
det (ξ-·-r w st) (Beta v)     = ⊥-elim (V-¬-→ v st)

det (TyWrap v)   (TyWrap w)   = refl
det (TyWrap v)   (ξ-·[] st)   =
  ⊥-elim (V-¬-→ (V-⟪⟫ (V-G (G-Λ v)) I-∀) st)
det (ξ-·[] st)   (TyWrap v)   =
  ⊥-elim (V-¬-→ (V-⟪⟫ (V-G (G-Λ v)) I-∀) st)

det (TyPeel v i) (TyPeel w j) = refl
det (TyPeel v i) (ξ-·[] st)   =
  ⊥-elim (V-¬-→ (V-⟪⟫ (V-⟪⟫ v i) I-∀) st)
det (ξ-·[] st)   (TyPeel v i) =
  ⊥-elim (V-¬-→ (V-⟪⟫ (V-⟪⟫ v i) I-∀) st)

det (Peel v w)   (Peel v′ w′) = refl
det (Peel v w)   (ξ-·-l st)   = ⊥-elim (V-¬-→ (V-⟪⟫ v I-⇒) st)
det (Peel v w)   (ξ-·-r u st) = ⊥-elim (V-¬-→ w st)
det (ξ-·-l st)   (Peel v w)   = ⊥-elim (V-¬-→ (V-⟪⟫ v I-⇒) st)
det (ξ-·-r u st) (Peel v w)   = ⊥-elim (V-¬-→ w st)

det (Merge v i a p) (Merge w j b q) = refl
det (Merge v i a p) (ξ-⟪⟫ st)       = ⊥-elim (V-¬-→ (V-⟪⟫ v i) st)
det (ξ-⟪⟫ st)       (Merge v i a p) = ⊥-elim (V-¬-→ (V-⟪⟫ v i) st)

det Drop$            Drop$             = refl
det Drop$            (ξ-⟪⟫ st)         = ⊥-elim (V-¬-→ V-$ st)
det (ξ-⟪⟫ st)        Drop$             = ⊥-elim (V-¬-→ V-$ st)

det (ξ-·-l {M = M} st)  (ξ-·-l st′)  = cong (_· M) (det st st′)
det (ξ-·-l st)          (ξ-·-r v st′) = ⊥-elim (V-¬-→ v st)
det (ξ-·-r v st)        (ξ-·-l st′)   = ⊥-elim (V-¬-→ v st′)
det (ξ-·-r {V = V} v st) (ξ-·-r w st′) = cong (V ·_) (det st st′)
det (ξ-·[] {B = B} {A = A} st) (ξ-·[] st′) =
  cong (_·[ B , A ]) (det st st′)
det (ξ-Λ st)            (ξ-Λ st′)     = cong Λ_ (det st st′)
det (ξ-⟪⟫ {Θ = Θ} {B₀ = B₀} st) (ξ-⟪⟫ st′) =
  cong (_⟪ Θ , B₀ ⟫) (det st st′)

------------------------------------------------------------------------
-- Worked example:  (ΛX. λx:X.x) [X→X, ℕ]  →  (λx:X.x)⟪↑X:=ℕ⟫   (both : ℕ→ℕ)
------------------------------------------------------------------------

⊢redex-Λ : [] ∣ [] ⊢ (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ] ⦂ (`ℕ ⇒ `ℕ)
⊢redex-Λ = ⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))) wf-ℕ

_ : [] ⊢ (Λ (ƛ ` 0 ∙ ` 0)) ·[ (` 0 ⇒ ` 0) , `ℕ ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫
_ = TyBeta (V-G G-ƛ)

⊢contractum-Λ :
  [] ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫ ⦂ (`ℕ ⇒ `ℕ)
⊢contractum-Λ = env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
                    (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- Worked example for Beta:  (λx:ℕ. x) · 5  →  5    (both : ℕ)
------------------------------------------------------------------------

⊢redex-ƛ : [] ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) · ($ 5) ⦂ `ℕ
⊢redex-ƛ = ⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$

_ : [] ⊢ (ƛ `ℕ ∙ ` 0) · ($ 5) -→ $ 5
_ = Beta V-$

⊢contractum-ƛ : [] ∣ [] ⊢ $ 5 ⦂ `ℕ
⊢contractum-ƛ = ⊢$

------------------------------------------------------------------------
-- Worked example for ξ-⟪⟫:  reduce the INTERIOR of a reveal boundary.
--   ((λx:ℕ. x) · 5) ⟪ ↑X:=ℕ , B₀=ℕ ⟫  →  5 ⟪ ↑X:=ℕ , B₀=ℕ ⟫   (both : ℕ)
-- The interior context is  X:=ℕ ∣ []  (one reveal, no conceal); B₀ = ℕ has
-- no free variable, so both faces are ℕ: the boundary is inert on the type.
------------------------------------------------------------------------

⊢redex-bnd : [] ∣ [] ⊢ ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢redex-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ (⊢· (⊢ƛ wf-ℕ (⊢` here)) ⊢$)

_ : [] ⊢ ((ƛ `ℕ ∙ ` 0) · $ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
    -→ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫
_ = ξ-⟪⟫ (Beta V-$)

⊢contractum-bnd : [] ∣ [] ⊢ ($ 5) ⟪ rvl `ℕ ∷ [] , `ℕ ⟫ ⦂ `ℕ
⊢contractum-bnd = env (bwf↑ wf-ℕ bwf[]) sc-ℕ ⊢$

------------------------------------------------------------------------
-- Worked example for TyWrap (R1), on the NEW-DESIGN ANALOGUE OF EXAMPLE 8.
-- Example 8 (notes/old/Scratch7-9) is the closed program whose 4th step
-- made the OLD design ill-typed: a value concealed on X (index 1) is
-- TYPE-APPLIED to
-- the SHALLOWER Λ-bound Y (index 0), which the interior blocks.  Under the
-- combined boundary the same redex steps to a WELL-TYPED term, because Y is
-- recorded as a REVEAL rep (read in the exterior) instead of being pushed
-- into the interior.
--
--   ((ΛZ. λz:Z. z) ⟪ ↓X:=ℕ , ∀(Z→Z) ⟫) ·[ Z→Z , Y ]    : Y→Y
--     →  (λz:Z. z) ⟪ ↑Z:=Y , ↓X:=ℕ , Z→Z ⟫             : Y→Y
--
-- The Λ is consumed: its binder's slot becomes the reveal slot, whose rep is
-- the type argument Y.  Nothing moves in the term (no ⇑ᵀ).
--
-- Δ8 must now KNOW X (the reversal premise licenses a conceal only against
-- the exterior's own knowledge), so X is revealed at ℕ and Y is Λ-bound.
------------------------------------------------------------------------

polyid : Term
polyid = Λ (ƛ ` 0 ∙ ` 0)

Δ8 : TCtx                     -- Y (Λ-bound, index 0), X:=ℕ (index 1)
Δ8 = abst ∷ rvld `ℕ ∷ []

Θ8 : BCtx                       -- conceal X (index 1), rep ℕ
Θ8 = cnc 1 `ℕ ∷ []

_ : intOf Δ8 Θ8 ≡ []
_ = refl

_ : baseS Θ8 Δ8 ≡ blk ∷ ok ∷ []          -- Y is BLOCKED inside
_ = refl

⊢redex-R1 : Δ8 ∣ [] ⊢ (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
                      ⦂ (` 0 ⇒ ` 0)
⊢redex-R1 =
  ⊢·[] (env (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
       (wf-var here-abst)

-- polyid is Λ (ƛ ` 0 ∙ ` 0), so the rule's Value premise is the Λ-BODY's:
-- V-G G-ƛ, not the whole polyid's V-G (G-Λ …)
_ : Δ8 ⊢ (polyid ⟪ Θ8 , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
_ = TyWrap (V-G G-ƛ)

-- the new reveal's rep is the BLOCKED, Λ-BOUND Y, so neither the raw
-- reading nor the ambient unfolding is available and the fallback chain
-- lands on the EXTERIOR-READ entry  Z :=ˣ Y  (it used to land on `abst`,
-- which is what left E★′'s Wrap stuck)
_ : intOf Δ8 (rvl (` 0) ∷ shiftReps Θ8) ≡ xrvld (` 0) ∷ []
_ = refl

⊢contractum-R1 :
  Δ8 ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ shiftReps Θ8 , ` 0 ⇒ ` 0 ⟫
            ⦂ (` 0 ⇒ ` 0)
⊢contractum-R1 =
  env (bwf↑ (wf-var here-abst)
            (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-xrvld) (⊢` here))

------------------------------------------------------------------------
-- Worked example for TyWrap over a boundary that ALREADY REVEALS — the case
-- the reverted telescope needed a rep lift for.  Under the parallel reading
-- the type argument is recorded VERBATIM: it is an exterior type and a
-- reveal's rep is read in the plain exterior, so nothing moves.
--
--   Δt = X:=𝔹            Θt = ↑Z:=ℕ            (revs Θt = 1)
--   ((ΛW. λw:W. w) ⟪ Θt , ∀(W→W) ⟫) ·[ W→W , X ]      : X→X
--     →  (λw:W. w) ⟪ ↑W:=X , ↑Z:=ℕ , W→W ⟫
--
-- The new reveal's rep is ` 0 = X (a Δt index, NOT lifted past ↑Z), and its
-- interior entry is the KNOWLEDGE W:=` 1 — X's interior slot read over the
-- entry's own tail, which the reading ⟦·⟧ computes either way.
------------------------------------------------------------------------

Δt : TCtx
Δt = rvld `𝔹 ∷ []

Θt : BCtx
Θt = rvl `ℕ ∷ []

_ : intOf Δt Θt ≡ rvld `ℕ ∷ rvld `𝔹 ∷ []
_ = refl

⊢redex-R1t : Δt ∣ [] ⊢ (polyid ⟪ Θt , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
                       ⦂ (` 0 ⇒ ` 0)
⊢redex-R1t =
  ⊢·[] (env (bwf↑ wf-ℕ bwf[])
            (sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)))
            (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
       (wf-var here-rvld)

_ : Δt ⊢ (polyid ⟪ Θt , ∀ZZ ⟫) ·[ ` 0 ⇒ ` 0 , ` 0 ]
    -→ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ rvl `ℕ ∷ [] , ` 0 ⇒ ` 0 ⟫
_ = TyWrap (V-G G-ƛ)

-- the new reveal's external face is the type argument itself …
_ : ρᵇ (rvl (` 0) ∷ rvl `ℕ ∷ []) 0 ≡ ` 0
_ = refl

-- … and its interior entry is still X's interior slot, over its own tail
_ : intOf Δt (rvl (` 0) ∷ rvl `ℕ ∷ [])
    ≡ rvld (` 1) ∷ rvld `ℕ ∷ rvld `𝔹 ∷ []
_ = refl

⊢contractum-R1t :
  Δt ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl (` 0) ∷ rvl `ℕ ∷ [] , ` 0 ⇒ ` 0 ⟫
            ⦂ (` 0 ⇒ ` 0)
⊢contractum-R1t =
  env (bwf↑ (wf-var here-rvld) (bwf↑ wf-ℕ bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- Worked example for Peel, on a MIXED boundary — one reveal AND one
-- conceal, the shape R1 produces (⊢contractum-R1 above), and the case a
-- "restrict R2 to cmax Θ = 0" design would not cover.
--
--   ((λz:Z. z) ⟪ ↑Z:=ℕ , ↓X:=ℕ ; Z→Z ⟫) · 3                        : ℕ
--     →  (3 ⟪ dualᴳ Δm Θm , X ⟫) ⟪ ↑Z:=ℕ , ↓X:=ℕ ; Z ⟫             : ℕ
--
-- The ƛ is consumed and its body ` 0 is substituted for, so the contractum is
-- the dual-wrapped argument under the original boundary.
--
-- Exterior Δm = [Y , X:=ℕ]; the interior is [Z:=ℕ] and Y is BLOCKED there.
-- The AMBIENT dual is [↑⋆ , ↑ℕ , ↓Z:=ℕ]: the blocked Y is Λ-BOUND in Δm, so
-- the dual re-introduces it with the REP-LESS reveal (dualᵇ used to invent
-- the knowledge Y:=ℕ there), X comes back at its conceal rep, and the reveal
-- variable Z is concealed at its external face.  swapᵇ Θm sends Θm's frame
-- [Z , Y , X] slot 0 (Z) to slot 2 of the dual's frame [X , Y , Z], so the
-- dual's boundary type is ` 2.
------------------------------------------------------------------------

Δm : TCtx                       -- Y (Λ-bound, index 0), X:=ℕ (index 1)
Δm = abst ∷ rvld `ℕ ∷ []

Θm : BCtx                       -- reveal Z:=ℕ, conceal X (index 1)
Θm = rvl `ℕ ∷ cnc 1 `ℕ ∷ []

_ : intOf Δm Θm ≡ rvld `ℕ ∷ []
_ = refl

_ : baseS Θm Δm ≡ ok ∷ blk ∷ ok ∷ []          -- Y is blocked
_ = refl

_ : dualᴳ Δm Θm ≡ rvl⋆ ∷ rvl `ℕ ∷ cnc 0 `ℕ ∷ []
_ = refl

-- the dual's interior is Δm ON THE NOSE (the rep-less reveal rebuilds the
-- Λ-bound Y as abstract, which is exactly Δm's entry)
_ : intOf (intOf Δm Θm) (dualᴳ Δm Θm) ≡ Δm
_ = refl

_ : swapᵇ Θm 0 ≡ 2
_ = refl

⊢redex-R2m : Δm ∣ [] ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3) ⦂ `ℕ
⊢redex-R2m =
  ⊢· (env (bwf↑ wf-ℕ (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))
          (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
          (⊢ƛ (wf-var here-rvld) (⊢` here)))
     ⊢$

-- PEEL, then the ordinary Beta INSIDE the boundary.  The peel step moves
-- the application inward and wraps the argument in the dual; the ƛ is
-- still there, and Beta consumes it one step later — the two steps
-- together are exactly the old Wrap contractum (the ƛ's body is ` 0, so
-- N [ … ]ᵐ IS the wrapped argument, definitionally).
peel-R2m : Δm ⊢ ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3)
    -→ ((ƛ ` 0 ∙ ` 0) · (($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫)) ⟪ Θm , ` 0 ⟫
peel-R2m = Peel (V-G G-ƛ) V-$

peel-is-wrap+beta :
  intOf Δm Θm ⊢ (ƛ ` 0 ∙ ` 0) · (($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫)
    -→ ($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫
peel-is-wrap+beta = Beta (V-⟪⟫ V-$ (I-var (s≤s (s≤s z≤n))))

_ : Δm ⊢ ((ƛ ` 0 ∙ ` 0) · (($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫)) ⟪ Θm , ` 0 ⟫
    -→ (($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫
_ = ξ-⟪⟫ peel-is-wrap+beta

⊢contractum-R2m :
  Δm ∣ [] ⊢ (($ 3) ⟪ dualᴳ Δm Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫ ⦂ `ℕ
⊢contractum-R2m =
  env (bwf↑ wf-ℕ (bwf↓ (skip-abst here) (≡→≈ refl) wf-ℕ bwf[]))
      (sc-var hereᵒ)
      (env (bwf⋆ (bwf↑ wf-ℕ (bwf↓ here (≡→≈ refl) wf-ℕ bwf[])))
           (sc-var (thereᵒ (thereᵒ hereᵒ)))
           ⊢$)

------------------------------------------------------------------------
-- THE CHAINED-KNOWLEDGE DUAL, REPAIRED BY THE SECOND-CHANCE COPY
-- (notes/old/AmbientDualProbe.agda §6b — the residue (R1) the reverted
-- telescope was buying; UpToProbe §4, entᴳ≈).  Γp = Y:=Y′ , Y′:=𝔹 , X:=ℕ is
-- reachable — TyBeta turns a Λ-bound Y into Y:=Y′ without renaming — and
-- Θp = ↓X:=ℕ drops all three.  Γp's entry for Y is the CHAIN "Y is Y′", and
-- Θp drops Y′ too, so the RAW copy's `dfree 0 k` guard refuses it and the
-- knowledge USED TO BE LOST to the rep-less rvl⋆.
--
-- Now the dual RETRIES with the rep unfolded in Y's own tail (Y′:=𝔹 , X:=ℕ),
-- which collapses the chain to 𝔹 — a type over the dual's plain exterior —
-- so the copy goes through and the knowledge SURVIVES.  The rebuild is Γp
-- up to exactly one unfolding at slot 0, which is what _≼≈_ compares
-- (notes/InstallGauntlet.agda §5's DualInt-Γq); syntactic entry equality
-- orders the two in NEITHER direction.
------------------------------------------------------------------------

Γp : TCtx                       -- Y:=Y′ , Y′:=𝔹 , X:=ℕ
Γp = rvld (` 0) ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

Θp : BCtx
Θp = cnc 2 `ℕ ∷ []

-- ALL THREE slots are copied now: Y at its UNFOLDED rep 𝔹
_ : dualᴳ Γp Θp ≡ rvl `𝔹 ∷ rvl `𝔹 ∷ rvl `ℕ ∷ []
_ = refl

_ : intOf Γp Θp ≡ []
_ = refl

-- still WELL FORMED — every rep it carries is a plain-exterior type
⊢dualᴳΓp : [] ∣ intOf [] (dualᴳ Γp Θp) ⊢ᵇ dualᴳ Γp Θp
⊢dualᴳΓp = bwf↑ wf-𝔹 (bwf↑ wf-𝔹 (bwf↑ wf-ℕ bwf[]))

-- … and the rebuild carries KNOWLEDGE at every slot, differing from Γp only
-- by the collapsed chain at slot 0
Γp′ : TCtx
Γp′ = rvld `𝔹 ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

_ : intOf (intOf Γp Θp) (dualᴳ Γp Θp) ≡ Γp′
_ = refl

------------------------------------------------------------------------
-- renameᵀ through a boundary, verified on ⇑ᵀ of the non-spurious ($7)⟪Θ₈, X⟫.
-- Under ⇑ᵀ (new abstract W at Γ-index 0):  conceal index 1 ↦ 2, reveal rep ` 0
-- (=Y) ↦ ` 1, B₀ = X = ` 2 ↦ ` 3 (bframe lift), body 7 unchanged (the
-- conceal absorbs the shift, so intRen = id).
------------------------------------------------------------------------

_ : ⇑ᵀ (($ 7) ⟪ Θ₈ , ` 2 ⟫) ≡ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫
_ = refl

-- ⊢renameᵀ on this instance: the renamed wrapper types at abst ∷ Γ₈ with the
-- renamed external type ` 2 (= renameᵗ suc of the original external ` 1 = X).
-- The conceal's reversal premise moves with it: both sides are still ℕ.
_ : (abst ∷ Γ₈) ∣ [] ⊢ ($ 7) ⟪ cnc 2 `ℕ ∷ rvl (` 1) ∷ [] , ` 3 ⟫ ⦂ ` 2
_ = env (bwf↓ (skip-abst (skip-abst here)) (≡→≈ refl) wf-ℕ
             (bwf↑ (wf-var (skip-abst here-abst)) bwf[]))
        (sc-var (thereᵒ (thereᵒ (thereᵒ hereᵒ)))) ⊢$

------------------------------------------------------------------------
-- Type-variable renaming preserves typing  (⊢renameᵀ)
------------------------------------------------------------------------

∋-map : ∀ {ρ} {Γₜ : Ctx} {x A}
      → Γₜ ∋ x ⦂ A → map (renameᵗ ρ) Γₜ ∋ x ⦂ renameᵗ ρ A
∋-map here      = here
∋-map (there p) = there (∋-map p)

wf-ren : ∀ {ρ Δ Δ'} {A : Ty}
       → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Δ ⊢ A → Δ' ⊢ renameᵗ ρ A
wf-ren h wfA = wf-rename-fv (λ y → h (fv-scope wfA y)) wfA

ext-h : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
      → (∀ {X} → (abst ∷ Δ) ∋tv X → (abst ∷ Δ') ∋tv extᵗ ρ X)
ext-h h here-abst    = here-abst
ext-h h (skip-abst p) = skip-abst (h p)

⤊-ren : ∀ {ρ} (Γₜ : Ctx)
      → map (renameᵗ (extᵗ ρ)) (⤊ Γₜ) ≡ ⤊ (map (renameᵗ ρ) Γₜ)
⤊-ren []            = refl
⤊-ren {ρ} (A ∷ Γₜ) = cong₂ _∷_ pt (⤊-ren Γₜ)
  where pt : renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
        pt = trans (rename-rename-commute suc (extᵗ ρ) A)
                   (sym (rename-rename-commute ρ suc A))

-- ↓ / ∋tv bridge: a variable of the existential scope Δ↓X is variable suc X + Y
-- of Δ, and back.  (Needed for the interior commutation.)
↓-∋ : ∀ {Δ} X {Y} → (Δ ↓ X) ∋tv Y → Δ ∋tv (suc X + Y)
↓-∋ {[]}        X       ()
↓-∋ {abst   ∷ Δ} zero    p = skip-abst p
↓-∋ {rvld A ∷ Δ} zero    p = skip-rvld p
↓-∋ {abst   ∷ Δ} (suc X) p = skip-abst (↓-∋ X p)
↓-∋ {rvld A ∷ Δ} (suc X) p = skip-rvld (↓-∋ X p)
↓-∋ {xrvld A ∷ Δ} zero    p = skip-xrvld p
↓-∋ {xrvld A ∷ Δ} (suc X) p = skip-xrvld (↓-∋ X p)

↓-∋⁻ : ∀ {Δ} X {Z} → Δ ∋tv (suc X + Z) → (Δ ↓ X) ∋tv Z
↓-∋⁻ {[]}        X       ()
↓-∋⁻ {abst   ∷ Δ} zero    (skip-abst p) = p
↓-∋⁻ {rvld A ∷ Δ} zero    (skip-rvld p) = p
↓-∋⁻ {abst   ∷ Δ} (suc X) (skip-abst p) = ↓-∋⁻ X p
↓-∋⁻ {rvld A ∷ Δ} (suc X) (skip-rvld p) = ↓-∋⁻ X p
↓-∋⁻ {xrvld A ∷ Δ} zero    (skip-xrvld p) = p
↓-∋⁻ {xrvld A ∷ Δ} (suc X) (skip-xrvld p) = ↓-∋⁻ X p

-- Mono = strictly monotone renaming (the shape of every renaming that arises:
-- weakenings and their lifts).  restrictRen preserves it.
Mono : (ℕ → ℕ) → Set
Mono ρ = ∀ {a b} → a < b → ρ a < ρ b

-- extᵗ preserves monotonicity, so ⊢renameᵀ can recurse under a Λ.
Mono-extᵗ : ∀ {ρ} → Mono ρ → Mono (extᵗ ρ)
Mono-extᵗ mono {zero}  {suc _} _         = s≤s z≤n
Mono-extᵗ mono {suc _} {suc _} (s≤s a<b) = s≤s (mono a<b)

∸-strict : ∀ {c p q} → c ≤ p → p < q → (p ∸ c) < (q ∸ c)
∸-strict {c} {p} {q} c≤p p<q =
  +-cancelˡ-< c _ _
    (subst₂ _<_ (sym (m+[n∸m]≡n c≤p)) (sym (m+[n∸m]≡n c≤q)) p<q)
  where c≤q : c ≤ q
        c≤q = ≤-trans c≤p (<⇒≤ p<q)

------------------------------------------------------------------------
-- liftⁿ / prepId below and above the reveal prefix, and the view that
-- splits a boundary-frame index into "reveal prefix" or "deep".
------------------------------------------------------------------------

liftⁿ-lo : ∀ r ρ X → X < r → liftⁿ r ρ X ≡ X
liftⁿ-lo zero    ρ X       ()
liftⁿ-lo (suc r) ρ zero    _         = refl
liftⁿ-lo (suc r) ρ (suc X) (s≤s X<r) = cong suc (liftⁿ-lo r ρ X X<r)

liftⁿ-hi : ∀ r ρ i → liftⁿ r ρ (r + i) ≡ r + ρ i
liftⁿ-hi zero    ρ i = refl
liftⁿ-hi (suc r) ρ i = cong suc (liftⁿ-hi r ρ i)

prepId-lo : ∀ r (σ : Substᵗ) X → X < r → prepId r σ X ≡ ` X
prepId-lo r σ X X<r with X <? r
prepId-lo r σ X X<r | yes _   = refl
prepId-lo r σ X X<r | no ¬X<r = ⊥-elim (¬X<r X<r)

prepId-hi : ∀ r (σ : Substᵗ) i → prepId r σ (r + i) ≡ σ i
prepId-hi r σ i with (r + i) <? r
prepId-hi r σ i | yes lt = ⊥-elim (m+n≮m r i lt)
prepId-hi r σ i | no  _  = cong σ (m+n∸m≡n r i)

-- prepId-hi with the reveal count supplied up to an equation (needed
-- because γᵇ of a renamed boundary mentions revs (renᴮ …), not revs Θ)
prepId-hi′ : ∀ r r' (σ : Substᵗ) i → r' ≡ r → prepId r' σ (r + i) ≡ σ i
prepId-hi′ r .r σ i refl = prepId-hi r σ i

split : ∀ r X → (X < r) ⊎ (Σ ℕ λ i → X ≡ r + i)
split zero    X       = inj₂ (X , refl)
split (suc r) zero    = inj₁ (s≤s z≤n)
split (suc r) (suc X) with split r X
split (suc r) (suc X) | inj₁ X<r        = inj₁ (s≤s X<r)
split (suc r) (suc X) | inj₂ (i , X≡ri) = inj₂ (i , cong suc X≡ri)

------------------------------------------------------------------------
-- external commutation: renaming commutes with the external projection ρᵇ.
-- Under the PARALLEL reveal block this is a plain LOOKUP at every slot — a
-- reveal's image is its rep as stored, which renᴮ renames by ρ itself.
------------------------------------------------------------------------

ρᵇ-comm : ∀ ρ ir Θ X
        → ρᵇ (renᴮ ρ ir Θ) (liftⁿ (revs Θ) ρ X) ≡ renameᵗ ρ (ρᵇ Θ X)
ρᵇ-comm ρ ir []            X       = refl
ρᵇ-comm ρ ir (rvl A ∷ Θ)   zero    = refl
ρᵇ-comm ρ ir (rvl A ∷ Θ)   (suc Y) = ρᵇ-comm ρ ir Θ Y
ρᵇ-comm ρ ir (rvl⋆ ∷ Θ)    zero    = refl
ρᵇ-comm ρ ir (rvl⋆ ∷ Θ)    (suc Y) = ρᵇ-comm ρ ir Θ Y
ρᵇ-comm ρ ir (cnc X A ∷ Θ) Y       = ρᵇ-comm ρ ir Θ Y
ρᵇ-comm ρ ir (cnc⋆ X ∷ Θ)  Y       = ρᵇ-comm ρ ir Θ Y

C-ext : ∀ ρ ir Θ B₀
      → substᵗ (ρᵇ (renᴮ ρ ir Θ)) (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
        ≡ renameᵗ ρ (substᵗ (ρᵇ Θ) B₀)
C-ext ρ ir Θ B₀ =
  trans (rename-subst-commute (liftⁿ (revs Θ) ρ) (ρᵇ (renᴮ ρ ir Θ)) B₀)
    (trans (subst-cong (ρᵇ-comm ρ ir Θ) B₀)
           (sym (rename-subst ρ (ρᵇ Θ) B₀)))

-- lookup preservation through one restriction Δ↓X (needed for the interior)
h-restrict : ∀ {ρ Δ Δ'} X
  → (∀ {Y} → Δ ∋tv Y → Δ' ∋tv ρ Y) → Mono ρ
  → ∀ {Y} → (Δ ↓ X) ∋tv Y → (Δ' ↓ ρ X) ∋tv restrictRen X ρ Y
h-restrict {ρ} X h mono {Y} p =
  ↓-∋⁻ (ρ X) (subst (λ n → _ ∋tv n) eq (h (↓-∋ X p)))
  where
    lt : suc (ρ X) ≤ ρ (suc X + Y)
    lt = mono (m≤m+n (suc X) Y)
    eq : ρ (suc X + Y) ≡ suc (ρ X) + restrictRen X ρ Y
    eq = sym (m+[n∸m]≡n lt)

------------------------------------------------------------------------
-- Monotonicity toolbox.  Mono is injective, and it survives every
-- combinator the interior renaming intRen is built from.
------------------------------------------------------------------------

Mono→inj : ∀ {ρ} → Mono ρ → ∀ {a b} → ρ a ≡ ρ b → a ≡ b
Mono→inj {ρ} mono {a} {b} eq with <-cmp a b
Mono→inj {ρ} mono {a} {b} eq | tri< a<b _ _ =
  ⊥-elim (<-irrefl eq (mono a<b))
Mono→inj {ρ} mono {a} {b} eq | tri≈ _ a≡b _ = a≡b
Mono→inj {ρ} mono {a} {b} eq | tri> _ _ b<a =
  ⊥-elim (<-irrefl (sym eq) (mono b<a))

Mono→≤ : ∀ {ρ} → Mono ρ → ∀ {a b} → a ≤ b → ρ a ≤ ρ b
Mono→≤ mono a≤b with m≤n⇒m<n∨m≡n a≤b
Mono→≤ mono a≤b | inj₁ a<b  = <⇒≤ (mono a<b)
Mono→≤ mono a≤b | inj₂ refl = ≤-refl

Mono-restrictRen : ∀ {ρ} X → Mono ρ → Mono (restrictRen X ρ)
Mono-restrictRen {ρ} X mono {a} {b} a<b =
  ∸-strict (mono (m≤m+n (suc X) a)) (mono (+-monoʳ-< (suc X) a<b))

Mono-deepRen : ∀ {ρ} c → Mono ρ → Mono (deepRen c ρ)
Mono-deepRen zero    mono = mono
Mono-deepRen (suc c) mono = Mono-restrictRen c mono

Mono-liftⁿ : ∀ {ρ} r → Mono ρ → Mono (liftⁿ r ρ)
Mono-liftⁿ zero    mono = mono
Mono-liftⁿ (suc r) mono = Mono-extᵗ (Mono-liftⁿ r mono)

Mono-intRen : ∀ {ρ} Θ → Mono ρ → Mono (intRen ρ Θ)
Mono-intRen Θ mono = Mono-liftⁿ (revs Θ) (Mono-deepRen (cmax Θ) mono)

------------------------------------------------------------------------
-- renᴮ keeps the reveal count and the reveal KINDS, and (for a Mono ρ)
-- sends the deepest conceal index X to ρ X — so cmax has one of two shapes
-- after renaming.
------------------------------------------------------------------------

revs-ren : ∀ ρ ir Θ → revs (renᴮ ρ ir Θ) ≡ revs Θ
revs-ren ρ ir []            = refl
revs-ren ρ ir (rvl A ∷ Θ)   = cong suc (revs-ren ρ ir Θ)
revs-ren ρ ir (rvl⋆ ∷ Θ)    = cong suc (revs-ren ρ ir Θ)
revs-ren ρ ir (cnc X A ∷ Θ) = revs-ren ρ ir Θ
revs-ren ρ ir (cnc⋆ X ∷ Θ)  = revs-ren ρ ir Θ

revSlots-ren : ∀ ρ ir Θ → revSlots (renᴮ ρ ir Θ) ≡ revSlots Θ
revSlots-ren ρ ir []            = refl
revSlots-ren ρ ir (rvl A ∷ Θ)   = cong (ok ∷_) (revSlots-ren ρ ir Θ)
revSlots-ren ρ ir (rvl⋆ ∷ Θ)    = cong (blk ∷_) (revSlots-ren ρ ir Θ)
revSlots-ren ρ ir (cnc X A ∷ Θ) = revSlots-ren ρ ir Θ
revSlots-ren ρ ir (cnc⋆ X ∷ Θ)  = revSlots-ren ρ ir Θ

⊔-mono-comm : ∀ {ρ} → Mono ρ → ∀ a b → ρ (a ⊔ b) ≡ ρ a ⊔ ρ b
⊔-mono-comm {ρ} mono a b with a ≤? b
⊔-mono-comm {ρ} mono a b | yes a≤b =
  trans (cong ρ (m≤n⇒m⊔n≡n a≤b)) (sym (m≤n⇒m⊔n≡n (Mono→≤ mono a≤b)))
⊔-mono-comm {ρ} mono a b | no ¬a≤b =
  trans (cong ρ (m≥n⇒m⊔n≡m b≤a)) (sym (m≥n⇒m⊔n≡m (Mono→≤ mono b≤a)))
  where b≤a : b ≤ a
        b≤a = <⇒≤ (≰⇒> ¬a≤b)

-- the two possible shapes of cmax under renaming
data CmaxV (ρ ir : ℕ → ℕ) (Θ : BCtx) : Set where
  cm-0 : cmax Θ ≡ 0 → cmax (renᴮ ρ ir Θ) ≡ 0 → CmaxV ρ ir Θ
  cm-s : ∀ X → cmax Θ ≡ suc X → cmax (renᴮ ρ ir Θ) ≡ suc (ρ X)
       → CmaxV ρ ir Θ

cmax-ren : ∀ {ρ} → Mono ρ → ∀ ir Θ → CmaxV ρ ir Θ
cmax-ren mono ir [] = cm-0 refl refl
cmax-ren mono ir (rvl A ∷ Θ) with cmax-ren mono ir Θ
cmax-ren mono ir (rvl A ∷ Θ) | cm-0 e e'   = cm-0 e e'
cmax-ren mono ir (rvl A ∷ Θ) | cm-s Y e e' = cm-s Y e e'
cmax-ren mono ir (rvl⋆ ∷ Θ) with cmax-ren mono ir Θ
cmax-ren mono ir (rvl⋆ ∷ Θ) | cm-0 e e'   = cm-0 e e'
cmax-ren mono ir (rvl⋆ ∷ Θ) | cm-s Y e e' = cm-s Y e e'
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) with cmax-ren mono ir Θ
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-0 e e' =
  cm-s X (cong (λ n → suc X ⊔ n) e) (cong (λ n → suc (ρ X) ⊔ n) e')
cmax-ren {ρ} mono ir (cnc X A ∷ Θ) | cm-s Y e e' =
  cm-s (X ⊔ Y) (cong (λ n → suc X ⊔ n) e)
       (trans (cong (λ n → suc (ρ X) ⊔ n) e')
              (cong suc (sym (⊔-mono-comm mono X Y))))
cmax-ren {ρ} mono ir (cnc⋆ X ∷ Θ) with cmax-ren mono ir Θ
cmax-ren {ρ} mono ir (cnc⋆ X ∷ Θ) | cm-0 e e' =
  cm-s X (cong (λ n → suc X ⊔ n) e) (cong (λ n → suc (ρ X) ⊔ n) e')
cmax-ren {ρ} mono ir (cnc⋆ X ∷ Θ) | cm-s Y e e' =
  cm-s (X ⊔ Y) (cong (λ n → suc X ⊔ n) e)
       (trans (cong (λ n → suc (ρ X) ⊔ n) e')
              (cong suc (sym (⊔-mono-comm mono X Y))))

------------------------------------------------------------------------
-- Decidable/Bool plumbing for isConc (whose cons case is ⌊ i ≟ X ⌋ ∨ …).
------------------------------------------------------------------------

⌊⌋-true : ∀ {P : Set} (d : Dec P) → ⌊ d ⌋ ≡ true → P
⌊⌋-true (yes p) _  = p
⌊⌋-true (no ¬p) ()

⌊⌋-of : ∀ {P : Set} (d : Dec P) → P → ⌊ d ⌋ ≡ true
⌊⌋-of (yes _) _ = refl
⌊⌋-of (no ¬p) p = ⊥-elim (¬p p)

⌊⌋-false : ∀ {P : Set} (d : Dec P) → ¬ P → ⌊ d ⌋ ≡ false
⌊⌋-false (yes p) ¬p = ⊥-elim (¬p p)
⌊⌋-false (no  _) _  = refl

∨-true : ∀ (b₁ b₂ : Bool) → (b₁ ∨ b₂) ≡ true → (b₁ ≡ true) ⊎ (b₂ ≡ true)
∨-true true  b₂ e = inj₁ refl
∨-true false b₂ e = inj₂ e

isConc-cons : ∀ i X A Θ → isConc i (cnc X A ∷ Θ) ≡ true
            → (i ≡ X) ⊎ (isConc i Θ ≡ true)
isConc-cons i X A Θ c with ∨-true ⌊ i ≟ X ⌋ (isConc i Θ) c
isConc-cons i X A Θ c | inj₁ t = inj₁ (⌊⌋-true (i ≟ X) t)
isConc-cons i X A Θ c | inj₂ t = inj₂ t

isConc-here : ∀ i X A Θ → i ≡ X → isConc i (cnc X A ∷ Θ) ≡ true
isConc-here i X A Θ p = cong (λ b → b ∨ isConc i Θ) (⌊⌋-of (i ≟ X) p)

isConc-there : ∀ i X A Θ → isConc i Θ ≡ true → isConc i (cnc X A ∷ Θ) ≡ true
isConc-there i X A Θ c =
  trans (cong (λ b → ⌊ i ≟ X ⌋ ∨ b) c) (∨-zeroʳ ⌊ i ≟ X ⌋)

-- a concealed index stays concealed after renaming (indices move by ρ)
isConc-ren : ∀ ρ ir Θ i → isConc i Θ ≡ true
           → isConc (ρ i) (renᴮ ρ ir Θ) ≡ true
isConc-ren ρ ir []            i ()
isConc-ren ρ ir (rvl A ∷ Θ)   i c = isConc-ren ρ ir Θ i c
isConc-ren ρ ir (rvl⋆ ∷ Θ)    i c = isConc-ren ρ ir Θ i c
isConc-ren ρ ir (cnc X A ∷ Θ) i c with isConc-cons i X A Θ c
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₁ p =
  isConc-here (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ) (cong ρ p)
isConc-ren ρ ir (cnc X A ∷ Θ) i c | inj₂ t =
  isConc-there (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ)
               (isConc-ren ρ ir Θ i t)
isConc-ren ρ ir (cnc⋆ X ∷ Θ)  i c = isConc-ren ρ ir Θ i c

-- … and, since ρ is injective, ONLY a concealed one does
isConc-ren-inv : ∀ {ρ} → Mono ρ → ∀ ir Θ i
               → isConc (ρ i) (renᴮ ρ ir Θ) ≡ true → isConc i Θ ≡ true
isConc-ren-inv mono ir []            i ()
isConc-ren-inv mono ir (rvl A ∷ Θ)   i c = isConc-ren-inv mono ir Θ i c
isConc-ren-inv mono ir (rvl⋆ ∷ Θ)    i c = isConc-ren-inv mono ir Θ i c
isConc-ren-inv {ρ} mono ir (cnc X A ∷ Θ) i c
  with isConc-cons (ρ i) (ρ X) (renameᵗ ir A) (renᴮ ρ ir Θ) c
isConc-ren-inv {ρ} mono ir (cnc X A ∷ Θ) i c | inj₁ q =
  isConc-here i X A Θ (Mono→inj mono q)
isConc-ren-inv {ρ} mono ir (cnc X A ∷ Θ) i c | inj₂ t =
  isConc-there i X A Θ (isConc-ren-inv mono ir Θ i t)
isConc-ren-inv mono ir (cnc⋆ X ∷ Θ)  i c = isConc-ren-inv mono ir Θ i c

------------------------------------------------------------------------
-- The accessibility bridge: baseS Θ Δ ∋ok (revs Θ + i) says exactly that
-- i is a KEPT (cmax Θ ≤ i) or CONCEALED index of Δ — the two cases where
-- γcnc commutes with renaming.  Both directions are needed.  The reveal
-- prefix is now PER ENTRY (revSlots), a rep-less reveal being blocked.
------------------------------------------------------------------------

ok≢blk : ok ≡ blk → ⊥
ok≢blk ()

∋ok-head : ∀ {s Ψ} → (s ∷ Ψ) ∋ok zero → s ≡ ok
∋ok-head hereᵒ = refl

∋ok-tail : ∀ {s Ψ j} → (s ∷ Ψ) ∋ok suc j → Ψ ∋ok j
∋ok-tail (thereᵒ p) = p

∋ok-≡ : ∀ {Ψ X X'} → X ≡ X' → Ψ ∋ok X → Ψ ∋ok X'
∋ok-≡ refl p = p

∋tv-tail : ∀ {E Γ j} → (E ∷ Γ) ∋tv suc j → Γ ∋tv j
∋tv-tail (skip-abst p)  = p
∋tv-tail (skip-rvld p)  = p
∋tv-tail (skip-xrvld p) = p

revS-drop : ∀ Θ {Ψ i} → (revSlots Θ ++ Ψ) ∋ok (revs Θ + i) → Ψ ∋ok i
revS-drop []            p = p
revS-drop (rvl A ∷ Θ)   p = revS-drop Θ (∋ok-tail p)
revS-drop (rvl⋆ ∷ Θ)    p = revS-drop Θ (∋ok-tail p)
revS-drop (cnc X A ∷ Θ) p = revS-drop Θ p
revS-drop (cnc⋆ X ∷ Θ)  p = revS-drop Θ p

revS-add : ∀ Θ {Ψ i} → Ψ ∋ok i → (revSlots Θ ++ Ψ) ∋ok (revs Θ + i)
revS-add []            p = p
revS-add (rvl A ∷ Θ)   p = thereᵒ (revS-add Θ p)
revS-add (rvl⋆ ∷ Θ)    p = thereᵒ (revS-add Θ p)
revS-add (cnc X A ∷ Θ) p = revS-add Θ p
revS-add (cnc⋆ X ∷ Θ)  p = revS-add Θ p

-- a reveal slot that IS accessible stays accessible whatever follows it
revS-lo : ∀ Θ {Ψ Ψ'} X → X < revs Θ
        → (revSlots Θ ++ Ψ) ∋ok X → (revSlots Θ ++ Ψ') ∋ok X
revS-lo []            X       ()       p
revS-lo (rvl A ∷ Θ)   zero    lt       p = hereᵒ
revS-lo (rvl A ∷ Θ)   (suc X) (s≤s lt) p =
  thereᵒ (revS-lo Θ X lt (∋ok-tail p))
revS-lo (rvl⋆ ∷ Θ)    zero    lt       p =
  ⊥-elim (ok≢blk (sym (∋ok-head p)))
revS-lo (rvl⋆ ∷ Θ)    (suc X) (s≤s lt) p =
  thereᵒ (revS-lo Θ X lt (∋ok-tail p))
revS-lo (cnc Y A ∷ Θ) X       lt       p = revS-lo Θ X lt p
revS-lo (cnc⋆ Y ∷ Θ)  X       lt       p = revS-lo Θ X lt p

-- transport of a reveal slot along a boundary renaming (revSlots is stable)
revS-≡ : ∀ Θ Θ' {Ψ Ψ'} → revSlots Θ ≡ revSlots Θ' → ∀ X → X < revs Θ
       → (revSlots Θ ++ Ψ) ∋ok X → (revSlots Θ' ++ Ψ') ∋ok X
revS-≡ Θ Θ' {Ψ} {Ψ'} e X lt p =
  subst (λ S → (S ++ Ψ') ∋ok X) e (revS-lo Θ X lt p)

slotsᴳ-ok : ∀ Θ Γ k j → slotsᴳ Θ k Γ ∋ok j → slotAt Θ (k + j) ≡ ok
slotsᴳ-ok Θ []      k j ()
slotsᴳ-ok Θ (E ∷ Γ) k zero    p rewrite +-identityʳ k = ∋ok-head p
slotsᴳ-ok Θ (E ∷ Γ) k (suc j) p rewrite +-suc k j =
  slotsᴳ-ok Θ Γ (suc k) j (∋ok-tail p)

slotsᴳ-∋tv : ∀ Θ Γ k j → slotsᴳ Θ k Γ ∋ok j → Γ ∋tv j
slotsᴳ-∋tv Θ []            k j       ()
slotsᴳ-∋tv Θ (abst ∷ Γ)    k zero    p = here-abst
slotsᴳ-∋tv Θ (rvld A ∷ Γ)  k zero    p = here-rvld
slotsᴳ-∋tv Θ (abst ∷ Γ)    k (suc j) p =
  skip-abst (slotsᴳ-∋tv Θ Γ (suc k) j (∋ok-tail p))
slotsᴳ-∋tv Θ (rvld A ∷ Γ)  k (suc j) p =
  skip-rvld (slotsᴳ-∋tv Θ Γ (suc k) j (∋ok-tail p))
slotsᴳ-∋tv Θ (xrvld A ∷ Γ) k zero    p = here-xrvld
slotsᴳ-∋tv Θ (xrvld A ∷ Γ) k (suc j) p =
  skip-xrvld (slotsᴳ-∋tv Θ Γ (suc k) j (∋ok-tail p))

slotsᴳ-add : ∀ Θ Γ k j → Γ ∋tv j → slotAt Θ (k + j) ≡ ok
           → slotsᴳ Θ k Γ ∋ok j
slotsᴳ-add Θ []      k j       ()  e
slotsᴳ-add Θ (E ∷ Γ) k zero    q   e =
  subst (λ s → (s ∷ slotsᴳ Θ (suc k) Γ) ∋ok zero)
        (sym (trans (cong (slotAt Θ) (sym (+-identityʳ k))) e)) hereᵒ
slotsᴳ-add Θ (E ∷ Γ) k (suc j) q   e =
  thereᵒ (slotsᴳ-add Θ Γ (suc k) j (∋tv-tail q)
                     (trans (cong (slotAt Θ) (sym (+-suc k j))) e))

if-ok : ∀ (b : Bool) → b ≡ true → (if b then ok else blk) ≡ ok
if-ok true  _  = refl
if-ok false ()

if-acc : ∀ (b : Bool) → (b ≡ true) ⊎ ((if b then ok else blk) ≡ blk)
if-acc true  = inj₁ refl
if-acc false = inj₂ refl

slotAt-acc : ∀ Θ i
  → (cmax Θ ≤ i) ⊎ ((isConc i Θ ≡ true) ⊎ (slotAt Θ i ≡ blk))
slotAt-acc Θ i with cmax Θ ≤? i
slotAt-acc Θ i | yes le = inj₁ le
slotAt-acc Θ i | no ¬le with if-acc (isConc i Θ)
slotAt-acc Θ i | no ¬le | inj₁ c = inj₂ (inj₁ c)
slotAt-acc Θ i | no ¬le | inj₂ b = inj₂ (inj₂ b)

acc-of : ∀ Θ i → slotAt Θ i ≡ ok → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
acc-of Θ i e with slotAt-acc Θ i
acc-of Θ i e | inj₁ le         = inj₁ le
acc-of Θ i e | inj₂ (inj₁ c)   = inj₂ c
acc-of Θ i e | inj₂ (inj₂ bk)  = ⊥-elim (ok≢blk (trans (sym e) bk))

slotAt-hi : ∀ Θ i → cmax Θ ≤ i → slotAt Θ i ≡ ok
slotAt-hi Θ i le with cmax Θ ≤? i
slotAt-hi Θ i le | yes _   = refl
slotAt-hi Θ i le | no ¬le  = ⊥-elim (¬le le)

slotAt-conc : ∀ Θ i → isConc i Θ ≡ true → slotAt Θ i ≡ ok
slotAt-conc Θ i c with cmax Θ ≤? i
slotAt-conc Θ i c | yes _  = refl
slotAt-conc Θ i c | no ¬le = if-ok (isConc i Θ) c

acc-slotAt : ∀ Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true) → slotAt Θ i ≡ ok
acc-slotAt Θ i (inj₁ le) = slotAt-hi Θ i le
acc-slotAt Θ i (inj₂ c)  = slotAt-conc Θ i c

baseS-acc : ∀ {Δ} Θ i → baseS Θ Δ ∋ok (revs Θ + i)
          → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
baseS-acc {Δ} Θ i p =
  acc-of Θ i (slotsᴳ-ok Θ Δ 0 i (revS-drop Θ p))

baseS-∋tv : ∀ {Δ} Θ i → baseS Θ Δ ∋ok (revs Θ + i) → Δ ∋tv i
baseS-∋tv {Δ} Θ i p = slotsᴳ-∋tv Θ Δ 0 i (revS-drop Θ p)

baseS-ok : ∀ {Δ} Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true) → Δ ∋tv i
         → baseS Θ Δ ∋ok (revs Θ + i)
baseS-ok {Δ} Θ i acc q =
  revS-add Θ (slotsᴳ-add Θ Δ 0 i q (acc-slotAt Θ i acc))

------------------------------------------------------------------------
-- Internal commutation.  The deep part of γᵇ is γcnc, which commutes
-- with ρ at kept and concealed indices (it does NOT at blocked ones —
-- that is exactly what the (env) scope premise rules out).
------------------------------------------------------------------------

deep-eq : ∀ {ρ} m m' → m ≡ 0 → m' ≡ 0 → ∀ j → m ≤ j
        → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m)
deep-eq {ρ} m m' e e' j le =
  trans (cong (λ n → ρ j ∸ n) e')
        (cong (λ n → deepRen n ρ (j ∸ n)) (sym e))

deep-eq-s : ∀ {ρ} m m' X → m ≡ suc X → m' ≡ suc (ρ X) → ∀ j → m ≤ j
          → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m)
deep-eq-s {ρ} m m' X e e' j le =
  trans (cong (λ n → ρ j ∸ n) e')
    (trans (cong (λ n → ρ n ∸ suc (ρ X)) (sym (m+[n∸m]≡n le')))
           (cong (λ n → deepRen n ρ (j ∸ n)) (sym e)))
  where le' : suc X ≤ j
        le' = subst (λ n → n ≤ j) e le

deep-hyp : ∀ {ρ} → Mono ρ → ∀ Θ j → cmax Θ ≤ j
  → ρ j ∸ cmax (renᴮ ρ (intRen ρ Θ) Θ)
    ≡ deepRen (cmax Θ) ρ (j ∸ cmax Θ)
deep-hyp {ρ} mono Θ j le with cmax-ren mono (intRen ρ Θ) Θ
deep-hyp {ρ} mono Θ j le | cm-0 e e'   = deep-eq (cmax Θ) _ e e' j le
deep-hyp {ρ} mono Θ j le | cm-s X e e' = deep-eq-s (cmax Θ) _ X e e' j le

acc-tail : ∀ m i X A Θ → ¬ (X ≡ i)
  → (m ≤ i) ⊎ (isConc i (cnc X A ∷ Θ) ≡ true)
  → (m ≤ i) ⊎ (isConc i Θ ≡ true)
acc-tail m i X A Θ ne (inj₁ le) = inj₁ le
acc-tail m i X A Θ ne (inj₂ c) with isConc-cons i X A Θ c
acc-tail m i X A Θ ne (inj₂ c) | inj₁ p = ⊥-elim (ne (sym p))
acc-tail m i X A Θ ne (inj₂ c) | inj₂ t = inj₂ t

γcnc-comm : ∀ {ρ} → Mono ρ → ∀ r m m' Θ i
  → (∀ j → m ≤ j → ρ j ∸ m' ≡ deepRen m ρ (j ∸ m))
  → (m ≤ i) ⊎ (isConc i Θ ≡ true)
  → γcnc r m' (renᴮ ρ (liftⁿ r (deepRen m ρ)) Θ) (ρ i)
    ≡ renameᵗ (liftⁿ r (deepRen m ρ)) (γcnc r m Θ i)
γcnc-comm {ρ} mono r m m' [] i hyp (inj₁ le) =
  trans (cong (λ n → ` (r + n)) (hyp i le))
        (cong `_ (sym (liftⁿ-hi r (deepRen m ρ) (i ∸ m))))
γcnc-comm {ρ} mono r m m' [] i hyp (inj₂ ())
γcnc-comm {ρ} mono r m m' (rvl A ∷ Θ) i hyp acc =
  γcnc-comm mono r m m' Θ i hyp acc
γcnc-comm {ρ} mono r m m' (rvl⋆ ∷ Θ) i hyp acc =
  γcnc-comm mono r m m' Θ i hyp acc
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  with X ≟ i | ρ X ≟ ρ i
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | yes refl | yes _ = refl
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | yes p | no ¬q = ⊥-elim (¬q (cong ρ p))
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | no ¬p | yes q = ⊥-elim (¬p (Mono→inj mono q))
γcnc-comm {ρ} mono r m m' (cnc X A ∷ Θ) i hyp acc
  | no ¬p | no ¬q =
  γcnc-comm mono r m m' Θ i hyp (acc-tail m i X A Θ ¬p acc)
-- a cnc⋆ has no γ-image, so it is transparent to the commutation
γcnc-comm {ρ} mono r m m' (cnc⋆ X ∷ Θ) i hyp acc =
  γcnc-comm mono r m m' Θ i hyp acc

-- γᵇ commutes with renaming at every ACCESSIBLE boundary-frame slot.
γᵇ-comm-lo : ∀ {ρ} → Mono ρ → ∀ Θ X → X < revs Θ
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ X)
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ X)
γᵇ-comm-lo {ρ} mono Θ X lt =
  trans (cong (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) (liftⁿ-lo (revs Θ) ρ X lt))
    (trans (prepId-lo (revs (renᴮ ρ (intRen ρ Θ) Θ)) _ X lt')
      (trans (cong `_ (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) X lt)))
             (cong (renameᵗ (intRen ρ Θ))
                   (sym (prepId-lo (revs Θ) _ X lt)))))
  where lt' : X < revs (renᴮ ρ (intRen ρ Θ) Θ)
        lt' = subst (λ n → X < n) (sym (revs-ren ρ (intRen ρ Θ) Θ)) lt

γᵇ-comm-hi : ∀ {ρ Δ} → Mono ρ → ∀ Θ i
  → baseS Θ Δ ∋ok (revs Θ + i)
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ (revs Θ + i))
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ (revs Θ + i))
γᵇ-comm-hi {ρ} mono Θ i okp =
  trans (cong (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) (liftⁿ-hi (revs Θ) ρ i))
    (trans (prepId-hi′ (revs Θ) (revs (renᴮ ρ (intRen ρ Θ) Θ)) _ (ρ i) rr)
      (trans (cong (λ n → γcnc n (cmax (renᴮ ρ (intRen ρ Θ) Θ))
                                 (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)) rr)
        (trans (γcnc-comm mono (revs Θ) (cmax Θ)
                          (cmax (renᴮ ρ (intRen ρ Θ) Θ)) Θ i
                          (deep-hyp mono Θ) (baseS-acc Θ i okp))
               (cong (renameᵗ (intRen ρ Θ))
                     (sym (prepId-hi (revs Θ) _ i))))))
  where rr : revs (renᴮ ρ (intRen ρ Θ) Θ) ≡ revs Θ
        rr = revs-ren ρ (intRen ρ Θ) Θ

γᵇ-comm-ok : ∀ {ρ Δ} → Mono ρ → ∀ Θ X → baseS Θ Δ ∋ok X
  → γᵇ (renᴮ ρ (intRen ρ Θ) Θ) (liftⁿ (revs Θ) ρ X)
    ≡ renameᵗ (intRen ρ Θ) (γᵇ Θ X)
γᵇ-comm-ok mono Θ X okp with split (revs Θ) X
γᵇ-comm-ok mono Θ X okp | inj₁ lt = γᵇ-comm-lo mono Θ X lt
γᵇ-comm-ok mono Θ .(revs Θ + i) okp | inj₂ (i , refl) =
  γᵇ-comm-hi mono Θ i okp

-- internal face: mirrors C-ext, but only at accessible slots (subst-cong-sc)
C-int : ∀ {ρ Δ B₀} → Mono ρ → ∀ Θ → Scoped (baseS Θ Δ) B₀
      → substᵗ (γᵇ (renᴮ ρ (intRen ρ Θ) Θ))
               (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
        ≡ renameᵗ (intRen ρ Θ) (substᵗ (γᵇ Θ) B₀)
C-int {ρ} {Δ} {B₀} mono Θ sc =
  trans (rename-subst-commute (liftⁿ (revs Θ) ρ)
                              (γᵇ (renᴮ ρ (intRen ρ Θ) Θ)) B₀)
    (trans (subst-cong-sc sc (λ X okp → γᵇ-comm-ok mono Θ X okp))
           (sym (rename-subst (intRen ρ Θ) (γᵇ Θ) B₀)))

------------------------------------------------------------------------
-- THE REVERSAL PREMISE TRANSPORTS.  outSub is built from ρᵇ, which commutes
-- with renaming at EVERY slot (ρᵇ-comm) — no scope restriction, the point of
-- the reversal form (notes/old/ReversalProbe.agda §5).
------------------------------------------------------------------------

outSub-lo : ∀ Θ X → X < revs Θ → outSub Θ X ≡ ρᵇ Θ X
outSub-lo Θ X lt with X <? revs Θ
outSub-lo Θ X lt | yes _  = refl
outSub-lo Θ X lt | no ¬lt = ⊥-elim (¬lt lt)

outSub-hi : ∀ Θ X → ¬ (X < revs Θ)
          → outSub Θ X ≡ ` (cmax Θ + (X ∸ revs Θ))
outSub-hi Θ X ¬lt with X <? revs Θ
outSub-hi Θ X ¬lt | yes lt = ⊥-elim (¬lt lt)
outSub-hi Θ X ¬lt | no  _  = refl

outSub-ren : ∀ {ρ} → Mono ρ → ∀ Θ X
  → outSub (renᴮ ρ (intRen ρ Θ) Θ) (intRen ρ Θ X)
    ≡ renameᵗ ρ (outSub Θ X)
outSub-ren {ρ} mono Θ X with split (revs Θ) X
outSub-ren {ρ} mono Θ X | inj₁ lt =
  trans (cong (outSub Θ′) (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) X lt))
    (trans (outSub-lo Θ′ X (subst (X <_) (sym (revs-ren ρ ir Θ)) lt))
      (trans (cong (ρᵇ Θ′) (sym (liftⁿ-lo (revs Θ) ρ X lt)))
        (trans (ρᵇ-comm ρ ir Θ X)
               (cong (renameᵗ ρ) (sym (outSub-lo Θ X lt))))))
  where ir = intRen ρ Θ
        Θ′ = renᴮ ρ (intRen ρ Θ) Θ
outSub-ren {ρ} mono Θ .(revs Θ + i) | inj₂ (i , refl) =
  trans (cong (outSub Θ′) (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) i))
    (trans (outSub-hi Θ′ (revs Θ + d)
             (λ lt → m+n≮m (revs Θ) d
                       (subst (revs Θ + d <_) (revs-ren ρ ir Θ) lt)))
      (trans (cong (λ n → ` (cmax Θ′ + n))
                   (trans (cong (revs Θ + d ∸_) (revs-ren ρ ir Θ))
                          (m+n∸m≡n (revs Θ) d)))
        (trans (cong `_ (key mono))
               (cong (renameᵗ ρ)
                 (sym (trans (outSub-hi Θ (revs Θ + i)
                        (m+n≮m (revs Θ) i))
                      (cong (λ n → ` (cmax Θ + n))
                            (m+n∸m≡n (revs Θ) i))))))))
  where
    ir = intRen ρ Θ
    Θ′ = renᴮ ρ (intRen ρ Θ) Θ
    d  = deepRen (cmax Θ) ρ i
    key : Mono ρ → cmax Θ′ + d ≡ ρ (cmax Θ + i)
    key mo with cmax-ren {ρ} mo ir Θ
    key mo | cm-0 e e′ rewrite e | e′ = refl
    key mo | cm-s Y e e′ rewrite e | e′ =
      m+[n∸m]≡n (mo {Y} {suc Y + i} (m≤m+n (suc Y) i))

Reversal-ren : ∀ {ρ} → Mono ρ → ∀ Θ X A A₀
  → Reversal Θ X A A₀
  → Reversal (renᴮ ρ (intRen ρ Θ) Θ) (ρ X)
             (renameᵗ (intRen ρ Θ) A) (renameᵗ (restrictRen X ρ) A₀)
Reversal-ren {ρ} mono Θ X A A₀ h =
  trans (rename-subst-commute (intRen ρ Θ) (outSub Θ′) A)
    (trans (subst-cong (λ Y → outSub-ren mono Θ Y) A)
      (trans (sym (rename-subst ρ (outSub Θ) A))
        (trans (cong (renameᵗ ρ) h)
          (trans (rename-rename-commute (λ i → suc X + i) ρ A₀)
            (trans (rename-cong eq A₀)
                   (sym (rename-rename-commute (restrictRen X ρ)
                          (λ i → suc (ρ X) + i) A₀)))))))
  where
    Θ′ = renᴮ ρ (intRen ρ Θ) Θ
    eq : ∀ i → ρ (suc X + i) ≡ suc (ρ X) + restrictRen X ρ i
    eq i = sym (m+[n∸m]≡n (mono {X} {suc X + i} (m≤m+n (suc X) i)))

------------------------------------------------------------------------
-- The interior context transports: intOf Δ Θ → intOf Δ' (renᴮ … Θ).
-- Lookup ignores the abst/rvld marker, so only the SHAPE of the reveal
-- block matters here (len-revEnts); the knowledge the entries carry is the
-- business of ∋:=-int below.
------------------------------------------------------------------------

∋tv-≡ : ∀ {Γ Γ' Z Z'} → Γ ≡ Γ' → Z ≡ Z' → Γ ∋tv Z → Γ' ∋tv Z'
∋tv-≡ refl refl p = p

ent-here : ∀ (E : TyEntry) (Γ : TCtx) → (E ∷ Γ) ∋tv zero
ent-here abst      Γ = here-abst
ent-here (rvld A)  Γ = here-rvld
ent-here (xrvld A) Γ = here-xrvld

ent-skip : ∀ (E : TyEntry) {Γ Y} → Γ ∋tv Y → (E ∷ Γ) ∋tv suc Y
ent-skip abst      p = skip-abst p
ent-skip (rvld A)  p = skip-rvld p
ent-skip (xrvld A) p = skip-xrvld p

revE-lo : ∀ Θ j Ξ {Γ : TCtx} Y → Y < revs Ξ
        → (revEnts Θ j Ξ ++ Γ) ∋tv Y
revE-lo Θ j []            Y       ()
revE-lo Θ j (rvl A ∷ Ξ)   zero    lt = ent-here (⟦ Θ ⟧ᴴ j A) _
revE-lo Θ j (rvl A ∷ Ξ)   (suc Y) (s≤s lt) =
  ent-skip (⟦ Θ ⟧ᴴ j A) (revE-lo Θ (suc j) Ξ Y lt)
revE-lo Θ j (rvl⋆ ∷ Ξ)    zero    lt = here-abst
revE-lo Θ j (rvl⋆ ∷ Ξ)    (suc Y) (s≤s lt) =
  skip-abst (revE-lo Θ (suc j) Ξ Y lt)
revE-lo Θ j (cnc X A ∷ Ξ) Y       lt = revE-lo Θ j Ξ Y lt
revE-lo Θ j (cnc⋆ X ∷ Ξ)  Y       lt = revE-lo Θ j Ξ Y lt

revE-hi : ∀ Θ j Ξ {Γ : TCtx} {Z} → Γ ∋tv Z
        → (revEnts Θ j Ξ ++ Γ) ∋tv (revs Ξ + Z)
revE-hi Θ j []            p = p
revE-hi Θ j (rvl A ∷ Ξ)   p =
  ent-skip (⟦ Θ ⟧ᴴ j A) (revE-hi Θ (suc j) Ξ p)
revE-hi Θ j (rvl⋆ ∷ Ξ)    p = skip-abst (revE-hi Θ (suc j) Ξ p)
revE-hi Θ j (cnc X A ∷ Ξ) p = revE-hi Θ j Ξ p
revE-hi Θ j (cnc⋆ X ∷ Ξ)  p = revE-hi Θ j Ξ p

revE-hi⁻ : ∀ Θ j Ξ {Γ : TCtx} {Z}
         → (revEnts Θ j Ξ ++ Γ) ∋tv (revs Ξ + Z) → Γ ∋tv Z
revE-hi⁻ Θ j []            p = p
revE-hi⁻ Θ j (rvl A ∷ Ξ)   p = revE-hi⁻ Θ (suc j) Ξ (∋tv-tail p)
revE-hi⁻ Θ j (rvl⋆ ∷ Ξ)    p = revE-hi⁻ Θ (suc j) Ξ (∋tv-tail p)
revE-hi⁻ Θ j (cnc X A ∷ Ξ) p = revE-hi⁻ Θ j Ξ p
revE-hi⁻ Θ j (cnc⋆ X ∷ Ξ)  p = revE-hi⁻ Θ j Ξ p

-- dropN (suc X) is the existential prefix Δ ↓ X (the conceal interior)
dropN-↓ : ∀ (Γ : TCtx) X → dropN (suc X) Γ ≡ Γ ↓ X
dropN-↓ []             X       = refl
dropN-↓ (abst ∷ Γ)     zero    = refl
dropN-↓ (rvld A ∷ Γ)   zero    = refl
dropN-↓ (abst ∷ Γ)     (suc X) = dropN-↓ Γ X
dropN-↓ (rvld A ∷ Γ)   (suc X) = dropN-↓ Γ X
dropN-↓ (xrvld A ∷ Γ)  zero    = refl
dropN-↓ (xrvld A ∷ Γ)  (suc X) = dropN-↓ Γ X

drop-int : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ {Z}
  → dropN (cmax Θ) Δ ∋tv Z
  → dropN (cmax (renᴮ ρ (intRen ρ Θ) Θ)) Δ' ∋tv deepRen (cmax Θ) ρ Z
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q with cmax-ren mono (intRen ρ Θ) Θ
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q | cm-0 e e' =
  ∋tv-≡ (cong (λ n → dropN n Δ') (sym e'))
        (cong (λ n → deepRen n ρ Z) (sym e))
        (h (∋tv-≡ (cong (λ n → dropN n Δ) e) refl q))
drop-int {ρ} {Δ} {Δ'} h mono Θ {Z} q | cm-s X e e' =
  ∋tv-≡ (trans (sym (dropN-↓ Δ' (ρ X)))
               (cong (λ n → dropN n Δ') (sym e')))
        (cong (λ n → deepRen n ρ Z) (sym e))
        (h-restrict X h mono
          (∋tv-≡ (trans (cong (λ n → dropN n Δ) e) (dropN-↓ Δ X)) refl q))

h-int : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ {Y}
  → intOf Δ Θ ∋tv Y
  → intOf Δ' (renᴮ ρ (intRen ρ Θ) Θ) ∋tv intRen ρ Θ Y
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p with split (revs Θ) Y
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p | inj₁ lt =
  ∋tv-≡ refl (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) Y lt))
        (revE-lo Θ' 0 Θ' Y
          (subst (Y <_) (sym (revs-ren ρ (intRen ρ Θ) Θ)) lt))
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ
h-int {ρ} {Δ} {Δ'} h mono Θ {Y} p | inj₂ (Z , refl) =
  ∋tv-≡ refl
        (trans (cong (_+ deepRen (cmax Θ) ρ Z)
                     (revs-ren ρ (intRen ρ Θ) Θ))
               (sym (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) Z)))
        (revE-hi Θ' 0 Θ'
          (drop-int h mono Θ (revE-hi⁻ Θ 0 Θ p)))
  where Θ' : BCtx
        Θ' = renᴮ ρ (intRen ρ Θ) Θ

------------------------------------------------------------------------
-- The (env) scope premise transports.
------------------------------------------------------------------------

sc-rename : ∀ {Ψ Ψ' ρ₀ A} → (∀ X → Ψ ∋ok X → Ψ' ∋ok ρ₀ X)
          → Scoped Ψ A → Scoped Ψ' (renameᵗ ρ₀ A)
sc-rename t (sc-var p)   = sc-var (t _ p)
sc-rename t sc-ℕ         = sc-ℕ
sc-rename t sc-𝔹         = sc-𝔹
sc-rename t (sc-⇒ sA sB) = sc-⇒ (sc-rename t sA) (sc-rename t sB)
sc-rename {Ψ} {Ψ'} {ρ₀} t (sc-∀ sA) = sc-∀ (sc-rename t-ext sA)
  where t-ext : ∀ X → (ok ∷ Ψ) ∋ok X → (ok ∷ Ψ') ∋ok extᵗ ρ₀ X
        t-ext zero    hereᵒ      = hereᵒ
        t-ext (suc X) (thereᵒ p) = thereᵒ (t X p)

-- a kept index stays kept and a concealed one stays concealed under ρ
acc-ren : ∀ {ρ} → Mono ρ → ∀ Θ i → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
  → (cmax (renᴮ ρ (intRen ρ Θ) Θ) ≤ ρ i)
    ⊎ (isConc (ρ i) (renᴮ ρ (intRen ρ Θ) Θ) ≡ true)
acc-ren {ρ} mono Θ i (inj₁ le) with cmax-ren mono (intRen ρ Θ) Θ
acc-ren {ρ} mono Θ i (inj₁ le) | cm-0 e e' =
  inj₁ (subst (λ n → n ≤ ρ i) (sym e') z≤n)
acc-ren {ρ} mono Θ i (inj₁ le) | cm-s X e e' =
  inj₁ (subst (λ n → n ≤ ρ i) (sym e')
              (mono (subst (λ n → n ≤ i) e le)))
acc-ren {ρ} mono Θ i (inj₂ c) =
  inj₂ (isConc-ren ρ (intRen ρ Θ) Θ i c)

baseS-ren : ∀ {ρ Δ Δ'} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ
  → ∀ X → baseS Θ Δ ∋ok X
  → baseS (renᴮ ρ (intRen ρ Θ) Θ) Δ' ∋ok liftⁿ (revs Θ) ρ X
baseS-ren {ρ} h mono Θ X okp with split (revs Θ) X
baseS-ren {ρ} h mono Θ X okp | inj₁ lt =
  ∋ok-≡ (sym (liftⁿ-lo (revs Θ) ρ X lt))
        (revS-≡ Θ (renᴮ ρ (intRen ρ Θ) Θ)
                (sym (revSlots-ren ρ (intRen ρ Θ) Θ)) X lt okp)
baseS-ren {ρ} h mono Θ .(revs Θ + i) okp | inj₂ (i , refl) =
  ∋ok-≡ (trans (cong (λ n → n + ρ i) (revs-ren ρ (intRen ρ Θ) Θ))
               (sym (liftⁿ-hi (revs Θ) ρ i)))
        (baseS-ok (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)
                  (acc-ren mono Θ i (baseS-acc Θ i okp))
                  (h (baseS-∋tv Θ i okp)))

sc-ren : ∀ {ρ Δ Δ' B₀} → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ → ∀ Θ
  → Scoped (baseS Θ Δ) B₀
  → Scoped (baseS (renᴮ ρ (intRen ρ Θ) Θ) Δ')
           (renameᵗ (liftⁿ (revs Θ) ρ) B₀)
sc-ren h mono Θ sc = sc-rename (baseS-ren h mono Θ) sc

------------------------------------------------------------------------
-- RETAGGING, UP TO THE UNFOLDING CONGRUENCE (candidate (a″); UpToProbe's
-- _≼≈_).  Typing READS the entry flavour — a conceal is licensed against
-- the exterior's knowledge (bwf↓) or against its exterior-read mark
-- (bwf↓x) — so a derivation transports along an ORDERING of contexts, not
-- along equal length.  Four clauses, one per entry form:
--
--   abst  sits below ANYTHING (a Λ-binder's slot becoming a reveal's
--         knowledge slot is exactly this step — TyBeta, TyWrap);
--   xrvld is PRESERVED: an x-entry's whole content is "revealed, but I know
--         nothing here", which a richer context does not satisfy, so the
--         mark may not be traded for knowledge (that is what keeps
--         (bwf-↓x) transportable, and what keeps `bad` refuted — see
--         strong.Boundary);
--   rvld  sits below knowledge that is ≈-EQUAL IN THE TARGET'S OWN TAIL,
--         which is exactly what the ambient dual's rebuild delivers when it
--         collapses a chain (BReduction's Γp / Γp′).
--
-- Syntactic _≼_ orders Γp and Γp′ in NEITHER direction; _≼≈_ orders them
-- both ways.  That is the whole content of the relaxation.
------------------------------------------------------------------------

-- (the four clauses are declared UP FRONT, next to _⊕_ — Merge's premise
-- mentions the ordering and the reduction relation mentions Merge.)

≼≈-refl : ∀ (Δ : TCtx) → Δ ≼≈ Δ
≼≈-refl []             = ≼≈[]
≼≈-refl (abst ∷ Δ)     = ≼≈abst (≼≈-refl Δ)
≼≈-refl (rvld A ∷ Δ)   = ≼≈rvld (≼≈-refl Δ) ≈-refl
≼≈-refl (xrvld A ∷ Δ)  = ≼≈xrvld (≼≈-refl Δ)

≼≈-len : ∀ {Δ Δ'} → Δ ≼≈ Δ' → length Δ ≡ length Δ'
≼≈-len ≼≈[]           = refl
≼≈-len (≼≈abst p)     = cong suc (≼≈-len p)
≼≈-len (≼≈xrvld p)    = cong suc (≼≈-len p)
≼≈-len (≼≈rvld p _)   = cong suc (≼≈-len p)

≼≈-∋tv : ∀ {Δ Δ' X} → Δ ≼≈ Δ' → Δ ∋tv X → Δ' ∋tv X
≼≈-∋tv (≼≈abst {E = abst}    p) here-abst      = here-abst
≼≈-∋tv (≼≈abst {E = rvld A}  p) here-abst      = here-rvld
≼≈-∋tv (≼≈abst {E = xrvld A} p) here-abst      = here-xrvld
≼≈-∋tv (≼≈xrvld p)              here-xrvld     = here-xrvld
≼≈-∋tv (≼≈rvld p _)             here-rvld      = here-rvld
≼≈-∋tv (≼≈abst {E = abst}    p) (skip-abst q)  = skip-abst (≼≈-∋tv p q)
≼≈-∋tv (≼≈abst {E = rvld A}  p) (skip-abst q)  = skip-rvld (≼≈-∋tv p q)
≼≈-∋tv (≼≈abst {E = xrvld A} p) (skip-abst q)  = skip-xrvld (≼≈-∋tv p q)
≼≈-∋tv (≼≈xrvld p)              (skip-xrvld q) = skip-xrvld (≼≈-∋tv p q)
≼≈-∋tv (≼≈rvld p _)             (skip-rvld q)  = skip-rvld (≼≈-∋tv p q)

-- the knowledge lookup a retag must re-establish: the target knows the same
-- variable, with a rep that is ≈-equal in the target's own TAIL
≼≈-∋:= : ∀ {Δ Δ' X A₀} → Δ ≼≈ Δ' → Δ ∋ X := A₀
       → Σ Ty λ A₀' → (Δ' ∋ X := A₀') × (A₀ ≈Δ̄⟨ Δ' ↓ X ⟩ A₀')
≼≈-∋:= (≼≈rvld {B = B} p e)     here          = B , here , e
≼≈-∋:= (≼≈abst {E = abst}    p) (skip-abst q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-abst r , e
≼≈-∋:= (≼≈abst {E = rvld C}  p) (skip-abst q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-rvld r , e
≼≈-∋:= (≼≈abst {E = xrvld C} p) (skip-abst q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-xrvld r , e
≼≈-∋:= (≼≈xrvld p)              (skip-xrvld q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-xrvld r , e
≼≈-∋:= (≼≈rvld p _)             (skip-rvld q) with ≼≈-∋:= p q
... | A₀' , r , e = A₀' , skip-rvld r , e

-- the EXTERIOR-READ lookup rides the ordering unchanged: an x-entry may not
-- trade its mark for knowledge, so the mark and its rep both survive
≼≈-∋:=x : ∀ {Δ Δ' X A′} → Δ ≼≈ Δ' → Δ ∋ X :=x A′ → Δ' ∋ X :=x A′
≼≈-∋:=x (≼≈xrvld p)              herex         = herex
≼≈-∋:=x (≼≈abst {E = abst}    p) (skipx q)     = skipx (≼≈-∋:=x p q)
≼≈-∋:=x (≼≈abst {E = rvld C}  p) (skipx q)     = skipx (≼≈-∋:=x p q)
≼≈-∋:=x (≼≈abst {E = xrvld C} p) (skipx q)     = skipx (≼≈-∋:=x p q)
≼≈-∋:=x (≼≈xrvld p)              (skipx q)     = skipx (≼≈-∋:=x p q)
≼≈-∋:=x (≼≈rvld p _)             (skipx q)     = skipx (≼≈-∋:=x p q)

≼≈-⊢ : ∀ {Δ Δ' A} → Δ ≼≈ Δ' → Δ ⊢ A → Δ' ⊢ A
≼≈-⊢ p (wf-var q) = wf-var (≼≈-∋tv p q)
≼≈-⊢ p wf-ℕ       = wf-ℕ
≼≈-⊢ p wf-𝔹       = wf-𝔹
≼≈-⊢ p (wf-⇒ a b) = wf-⇒ (≼≈-⊢ p a) (≼≈-⊢ p b)
≼≈-⊢ p (wf-∀ a)   = wf-∀ (≼≈-⊢ (≼≈abst p) a)

≼≈-dropN : ∀ c {Δ Δ'} → Δ ≼≈ Δ' → dropN c Δ ≼≈ dropN c Δ'
≼≈-dropN zero    p             = p
≼≈-dropN (suc c) ≼≈[]          = ≼≈[]
≼≈-dropN (suc c) (≼≈abst p)    = ≼≈-dropN c p
≼≈-dropN (suc c) (≼≈xrvld p)   = ≼≈-dropN c p
≼≈-dropN (suc c) (≼≈rvld p _)  = ≼≈-dropN c p

≼≈-app : ∀ (Ψ₀ : TCtx) {Δ Δ'} → Δ ≼≈ Δ' → (Ψ₀ ++ Δ) ≼≈ (Ψ₀ ++ Δ')
≼≈-app []             p = p
≼≈-app (abst ∷ Ψ₀)    p = ≼≈abst (≼≈-app Ψ₀ p)
≼≈-app (xrvld A ∷ Ψ₀) p = ≼≈xrvld (≼≈-app Ψ₀ p)
≼≈-app (rvld A ∷ Ψ₀)  p = ≼≈rvld (≼≈-app Ψ₀ p) ≈-refl

------------------------------------------------------------------------
-- ≼≈ ABSORBS: a richer context resolves at least what the poorer one
-- resolves, the same way — so every ≈ at Δ is an ≈ at Δ′ (≈-mono).  This is
-- what carries the ORDINARY conceal premise across a retag.
------------------------------------------------------------------------

≼≈→Absorbs : ∀ {Δ Δ'} → Δ ≼≈ Δ' → Absorbs Δ Δ'
≼≈→Absorbs ≼≈[]                       X       = refl
≼≈→Absorbs (≼≈abst {E = abst}    p)   zero    = refl
≼≈→Absorbs (≼≈abst {E = rvld C}  p)   zero    = refl
≼≈→Absorbs (≼≈abst {E = xrvld C} p)   zero    = refl
≼≈→Absorbs (≼≈xrvld p)                zero    = refl
≼≈→Absorbs {Δ' = rvld B ∷ Δ₁'} (≼≈rvld {Δ = Δ₁} {A = A} p e) zero =
  trans (unf-shift (rvld B) Δ₁' (unfoldᵉ Δ₁ A))
        (cong ⇑ᵗ (trans (unf-absorb Δ₁ Δ₁' (≼≈→Absorbs p) A) (≈unf⁻ e)))
≼≈→Absorbs {abst ∷ Δ₁} {abst ∷ Δ₁'} (≼≈abst {E = abst} p) (suc X) =
  trans (unf-shift abst Δ₁' (unfSub Δ₁ X)) (cong ⇑ᵗ (≼≈→Absorbs p X))
≼≈→Absorbs {abst ∷ Δ₁} {rvld C ∷ Δ₁'} (≼≈abst {E = rvld C} p) (suc X) =
  trans (unf-shift (rvld C) Δ₁' (unfSub Δ₁ X)) (cong ⇑ᵗ (≼≈→Absorbs p X))
≼≈→Absorbs {abst ∷ Δ₁} {xrvld C ∷ Δ₁'} (≼≈abst {E = xrvld C} p) (suc X) =
  trans (unf-shift (xrvld C) Δ₁' (unfSub Δ₁ X)) (cong ⇑ᵗ (≼≈→Absorbs p X))
≼≈→Absorbs {xrvld A ∷ Δ₁} {xrvld A ∷ Δ₁'} (≼≈xrvld p) (suc X) =
  trans (unf-shift (xrvld A) Δ₁' (unfSub Δ₁ X)) (cong ⇑ᵗ (≼≈→Absorbs p X))
≼≈→Absorbs {rvld A ∷ Δ₁} {rvld B ∷ Δ₁'} (≼≈rvld p e) (suc X) =
  trans (unf-shift (rvld B) Δ₁' (unfSub Δ₁ X)) (cong ⇑ᵗ (≼≈→Absorbs p X))

-- lifting a prefix-level ≈ to the whole context (the rep of a retagged
-- knowledge entry lives in the target's tail)
≈-upRep : ∀ {Δ' : TCtx} X {A₀ A₀'} → A₀ ≈Δ̄⟨ Δ' ↓ X ⟩ A₀'
        → upRep X A₀ ≈Δ̄⟨ Δ' ⟩ upRep X A₀'
≈-upRep {Δ'} X {A₀} {A₀'} (≈unf e) =
  ≈unf (trans (unf-up Δ' X A₀)
              (trans (cong (upᵉ X) e) (sym (unf-up Δ' X A₀'))))

slotsᴳ-len : ∀ Θ k (Γ Γ' : TCtx) → length Γ ≡ length Γ'
           → slotsᴳ Θ k Γ ≡ slotsᴳ Θ k Γ'
slotsᴳ-len Θ k []      []        le = refl
slotsᴳ-len Θ k []      (E' ∷ Γ') ()
slotsᴳ-len Θ k (E ∷ Γ) []        ()
slotsᴳ-len Θ k (E ∷ Γ) (E' ∷ Γ') le =
  cong (slotAt Θ k ∷_) (slotsᴳ-len Θ (suc k) Γ Γ' (suc-injective le))

baseS-len : ∀ Θ (Γ Γ' : TCtx) → length Γ ≡ length Γ'
          → baseS Θ Γ ≡ baseS Θ Γ'
baseS-len Θ Γ Γ' le =
  cong (revSlots Θ ++_) (slotsᴳ-len Θ 0 Γ Γ' le)

------------------------------------------------------------------------
-- THE INTERIOR IS MONOTONE IN THE AMBIENT'S KNOWLEDGE.  This holds ON THE
-- NOSE because the interior computation ⟦·⟧ᴴ consults the BOUNDARY alone:
-- the reveal block is literally the same on both sides, and the kept tail
-- inherits the ordering (≼≈-app / ≼≈-dropN).
--
-- It is also precisely why the ambient unfold retry had to go
-- (strong.Boundary's flagged deviation): with an ambient-dependent entry
-- map this statement is FALSE — a richer ambient resolves a reveal's rep
-- further, and a further-resolved rep may name a slot the boundary BLOCKS,
-- so the raw guard can fail where it succeeded and the two entries move in
-- opposite directions (UpToProbe §7b's ¬⟦⟧ᴴ-ren is the same phenomenon for
-- renaming).  ⊢retag is a knowledge-WEAKENING lemma the design cannot do
-- without — TyBeta turns a Λ-binder's abstract slot into a reveal's
-- knowledge slot — so the ambient had to be dropped, not this lemma.
------------------------------------------------------------------------

≼≈-intOf : ∀ Θ {Δ Δ'} → Δ ≼≈ Δ' → intOf Δ Θ ≼≈ intOf Δ' Θ
≼≈-intOf Θ p = ≼≈-app (revEnts Θ 0 Θ) (≼≈-dropN (cmax Θ) p)

bwf-retag≈ : ∀ {Δ Δ' Ψ Ψ' Θ Ξ} → Δ ≼≈ Δ' → Ψ ≼≈ Ψ'
           → Bwf Δ Ψ Θ Ξ → Bwf Δ' Ψ' Θ Ξ
bwf-retag≈ pΔ pΨ bwf[]                 = bwf[]
bwf-retag≈ pΔ pΨ (bwf↑ {Ξ = Ξ} wfA b)  =
  bwf↑ (≼≈-⊢ pΔ wfA) (bwf-retag≈ pΔ pΨ b)
bwf-retag≈ pΔ pΨ (bwf⋆ b)              = bwf⋆ (bwf-retag≈ pΔ pΨ b)
bwf-retag≈ {Δ' = Δ'} pΔ pΨ (bwf↓ {X} {A} {A₀} p rev wfA b)
  with ≼≈-∋:= pΔ p
bwf-retag≈ {Δ' = Δ'} pΔ pΨ (bwf↓ {X} {A} {A₀} p rev wfA b)
  | A₀' , r , e =
  bwf↓ r (≈-trans (≈-mono _ Δ' (≼≈→Absorbs pΔ) rev) (≈-upRep X e))
       (≼≈-⊢ pΨ wfA) (bwf-retag≈ pΔ pΨ b)
bwf-retag≈ pΔ pΨ (bwf↓x p so sk wfA b) =
  bwf↓x (≼≈-∋:=x pΔ p) so sk (≼≈-⊢ pΨ wfA) (bwf-retag≈ pΔ pΨ b)
bwf-retag≈ pΔ pΨ (bwf⋆↓ p b) =
  bwf⋆↓ (≼≈-∋tv pΔ p) (bwf-retag≈ pΔ pΨ b)

⊢retag≈ : ∀ {Δ Δ' Γₜ M A} → Δ ≼≈ Δ'
        → Δ ∣ Γₜ ⊢ M ⦂ A → Δ' ∣ Γₜ ⊢ M ⦂ A
⊢retag≈ p (⊢` q)        = ⊢` q
⊢retag≈ p ⊢$            = ⊢$
⊢retag≈ p (⊢ƛ wfA ⊢N)   = ⊢ƛ (≼≈-⊢ p wfA) (⊢retag≈ p ⊢N)
⊢retag≈ p (⊢· ⊢L ⊢M)    = ⊢· (⊢retag≈ p ⊢L) (⊢retag≈ p ⊢M)
⊢retag≈ p (⊢Λ ⊢N)       = ⊢Λ (⊢retag≈ (≼≈abst p) ⊢N)
⊢retag≈ p (⊢·[] ⊢L wfA) = ⊢·[] (⊢retag≈ p ⊢L) (≼≈-⊢ p wfA)
⊢retag≈ {Δ} {Δ'} p (env {Θ = Θ} {B₀ = B₀} bwf sc ⊢M) =
  env (bwf-retag≈ p (≼≈-intOf Θ p) bwf)
      (subst (λ Ψ → Scoped Ψ B₀) (baseS-len Θ Δ Δ' (≼≈-len p)) sc)
      (⊢retag≈ (≼≈-intOf Θ p) ⊢M)

------------------------------------------------------------------------
-- Boundary shift (R1).  The face laws of  rvl A ∷ shiftReps Θ  — the
-- boundary TyWrap builds, whose new reveal is the SHALLOWEST one and whose
-- rep is the type argument A ITSELF (a plain-exterior type, read in the
-- plain exterior: the parallel reveal block asks for no lift).  The
-- interior face becomes extsᵗ of the old one AT EVERY SLOT (blocked ones
-- included), so R1 carries no scope side-condition of its own; the
-- exterior face instantiates the ∀ with the type argument A.
------------------------------------------------------------------------

isConc-shift : ∀ i Θ → isConc i (shiftReps Θ) ≡ isConc i Θ
isConc-shift i []            = refl
isConc-shift i (rvl A ∷ Θ)   = isConc-shift i Θ
isConc-shift i (rvl⋆ ∷ Θ)    = isConc-shift i Θ
isConc-shift i (cnc X A ∷ Θ) = cong (⌊ i ≟ X ⌋ ∨_) (isConc-shift i Θ)
isConc-shift i (cnc⋆ X ∷ Θ)  = isConc-shift i Θ

-- shiftReps does not move the reveals, so the EXTERIOR face is untouched
ρᵇ-shift : ∀ Θ X → ρᵇ (shiftReps Θ) X ≡ ρᵇ Θ X
ρᵇ-shift []            X       = refl
ρᵇ-shift (rvl A ∷ Θ)   zero    = refl
ρᵇ-shift (rvl A ∷ Θ)   (suc X) = ρᵇ-shift Θ X
ρᵇ-shift (rvl⋆ ∷ Θ)    zero    = refl
ρᵇ-shift (rvl⋆ ∷ Θ)    (suc X) = ρᵇ-shift Θ X
ρᵇ-shift (cnc X A ∷ Θ) Y       = ρᵇ-shift Θ Y
ρᵇ-shift (cnc⋆ X ∷ Θ)  Y       = ρᵇ-shift Θ Y

γcnc-shift : ∀ r m Θ i
  → γcnc (suc r) m (shiftReps Θ) i ≡ renameᵗ suc (γcnc r m Θ i)
γcnc-shift r m []            i = refl
γcnc-shift r m (rvl A ∷ Θ)   i = γcnc-shift r m Θ i
γcnc-shift r m (rvl⋆ ∷ Θ)    i = γcnc-shift r m Θ i
γcnc-shift r m (cnc X A ∷ Θ) i with X ≟ i
γcnc-shift r m (cnc X A ∷ Θ) i | yes _ = refl
γcnc-shift r m (cnc X A ∷ Θ) i | no  _ = γcnc-shift r m Θ i
γcnc-shift r m (cnc⋆ X ∷ Θ)  i = γcnc-shift r m Θ i

γᵇ-shift-raw : ∀ r c Θ X
  → prepId (suc r) (γcnc (suc r) c (shiftReps Θ)) X
    ≡ extsᵗ (prepId r (γcnc r c Θ)) X
γᵇ-shift-raw r c Θ zero =
  prepId-lo (suc r) (γcnc (suc r) c (shiftReps Θ)) zero (s≤s z≤n)
γᵇ-shift-raw r c Θ (suc j) with split r j
γᵇ-shift-raw r c Θ (suc j) | inj₁ j<r =
  trans (prepId-lo (suc r) (γcnc (suc r) c (shiftReps Θ)) (suc j) (s≤s j<r))
        (cong (renameᵗ suc) (sym (prepId-lo r (γcnc r c Θ) j j<r)))
γᵇ-shift-raw r c Θ (suc j) | inj₂ (i , refl) =
  trans (prepId-hi (suc r) (γcnc (suc r) c (shiftReps Θ)) i)
        (trans (γcnc-shift r c Θ i)
               (cong (renameᵗ suc) (sym (prepId-hi r (γcnc r c Θ) i))))

-- FACE LAW (interior).  Adding the reveal of the type argument and shifting
-- the conceal reps is exactly extsᵗ on the interior face — at EVERY slot.
γᵇ-shift : ∀ A Θ X → γᵇ (rvl A ∷ shiftReps Θ) X ≡ extsᵗ (γᵇ Θ) X
γᵇ-shift A Θ X rewrite revs-shiftReps Θ | cmax-shiftReps Θ =
  γᵇ-shift-raw (revs Θ) (cmax Θ) Θ X

γᵇ-shift-ty : ∀ A Θ B → substᵗ (γᵇ (rvl A ∷ shiftReps Θ)) B
                        ≡ substᵗ (extsᵗ (γᵇ Θ)) B
γᵇ-shift-ty A Θ B = subst-cong (γᵇ-shift A Θ) B

-- the exterior face is the identity on the Γ-part of the boundary frame
ρᵇ-hi : ∀ Θ i → ρᵇ Θ (revs Θ + i) ≡ ` i
ρᵇ-hi []            i = refl
ρᵇ-hi (rvl A ∷ Θ)   i = ρᵇ-hi Θ i
ρᵇ-hi (rvl⋆ ∷ Θ)    i = ρᵇ-hi Θ i
ρᵇ-hi (cnc X A ∷ Θ) i = ρᵇ-hi Θ i
ρᵇ-hi (cnc⋆ X ∷ Θ)  i = ρᵇ-hi Θ i

-- THE EXTERIOR READING OF AN INERT FACE KEEPS ITS HEAD CONSTRUCTOR: ⇒
-- stays ⇒, ∀ stays ∀, and a non-revealed variable reads back to an
-- exterior VARIABLE (ρᵇ-hi).  This is the paper's `InertCross→` and its
-- `baseNotInert` in one statement: an inert boundary can NEVER export a
-- base type, and when it exports an arrow / a ∀ its face is SYNTACTICALLY
-- that arrow / that ∀ — which is what Peel and TyWrap/TyPeel need, and
-- what makes progress's elimination cases total.
inert-ext : ∀ Θ B₀ → Inert Θ B₀
  → (Σ Ty λ A′ → Σ Ty λ B′ →
       (B₀ ≡ (A′ ⇒ B′)) × (substᵗ (ρᵇ Θ) B₀ ≡
                             (substᵗ (ρᵇ Θ) A′ ⇒ substᵗ (ρᵇ Θ) B′)))
  ⊎ (Σ Ty λ B′ → (B₀ ≡ `∀ B′) × (substᵗ (ρᵇ Θ) B₀ ≡
                                   `∀ (substᵗ (extsᵗ (ρᵇ Θ)) B′)))
  ⊎ (Σ ℕ λ i → substᵗ (ρᵇ Θ) B₀ ≡ ` i)
inert-ext Θ (A′ ⇒ B′) I-⇒ = inj₁ (A′ , B′ , refl , refl)
inert-ext Θ (`∀ B′)   I-∀ = inj₂ (inj₁ (B′ , refl , refl))
inert-ext Θ (` X) (I-var ge) =
  inj₂ (inj₂ (X ∸ revs Θ ,
              trans (cong (ρᵇ Θ) (sym (m+[n∸m]≡n ge)))
                    (ρᵇ-hi Θ (X ∸ revs Θ))))

-- `baseNotInert`, both bases: no inert boundary exports ℕ or 𝔹
baseNotInert-ℕ : ∀ Θ B₀ → Inert Θ B₀ → substᵗ (ρᵇ Θ) B₀ ≡ `ℕ → ⊥
baseNotInert-ℕ Θ B₀ i eq with inert-ext Θ B₀ i
baseNotInert-ℕ Θ B₀ i eq | inj₁ (A′ , B′ , refl , e) with trans (sym e) eq
baseNotInert-ℕ Θ B₀ i eq | inj₁ (A′ , B′ , refl , e) | ()
baseNotInert-ℕ Θ B₀ i eq | inj₂ (inj₁ (B′ , refl , e))
  with trans (sym e) eq
baseNotInert-ℕ Θ B₀ i eq | inj₂ (inj₁ (B′ , refl , e)) | ()
baseNotInert-ℕ Θ B₀ i eq | inj₂ (inj₂ (j , e)) with trans (sym e) eq
baseNotInert-ℕ Θ B₀ i eq | inj₂ (inj₂ (j , e)) | ()

baseNotInert-𝔹 : ∀ Θ B₀ → Inert Θ B₀ → substᵗ (ρᵇ Θ) B₀ ≡ `𝔹 → ⊥
baseNotInert-𝔹 Θ B₀ i eq with inert-ext Θ B₀ i
baseNotInert-𝔹 Θ B₀ i eq | inj₁ (A′ , B′ , refl , e) with trans (sym e) eq
baseNotInert-𝔹 Θ B₀ i eq | inj₁ (A′ , B′ , refl , e) | ()
baseNotInert-𝔹 Θ B₀ i eq | inj₂ (inj₁ (B′ , refl , e))
  with trans (sym e) eq
baseNotInert-𝔹 Θ B₀ i eq | inj₂ (inj₁ (B′ , refl , e)) | ()
baseNotInert-𝔹 Θ B₀ i eq | inj₂ (inj₂ (j , e)) with trans (sym e) eq
baseNotInert-𝔹 Θ B₀ i eq | inj₂ (inj₂ (j , e)) | ()

-- FACE LAW (exterior).  The new reveal instantiates the ∀ with A — and its
-- rep IS A, read in the plain exterior, so no lift is resolved.
ρᵇ-shift-ty : ∀ A Θ B
  → substᵗ (ρᵇ (rvl A ∷ shiftReps Θ)) B
    ≡ (substᵗ (extsᵗ (ρᵇ Θ)) B) [ A ]ᵗ
ρᵇ-shift-ty A Θ B =
  trans (subst-cong h B) (sym (exts-sub-cons {σ = ρᵇ Θ} {a = B} {v = A}))
  where
    h : ∀ X → ρᵇ (rvl A ∷ shiftReps Θ) X ≡ cons-sub A (ρᵇ Θ) X
    h zero    = refl
    h (suc X) = ρᵇ-shift Θ X

-- the reversal premise survives the shift: the conceal reps move by suc and
-- the read-back map is unchanged
-- an opaque decision, so that `with` does not unfold outSub in the goal
dec-< : ∀ a b → (a < b) ⊎ (¬ (a < b))
dec-< a b with a <? b
dec-< a b | yes p  = inj₁ p
dec-< a b | no ¬p  = inj₂ ¬p

outSub-shift : ∀ A Θ k
  → outSub (rvl A ∷ shiftReps Θ) (suc k) ≡ outSub Θ k
outSub-shift A Θ k with dec-< k (revs Θ)
outSub-shift A Θ k | inj₁ lt =
  trans (outSub-lo (rvl A ∷ shiftReps Θ) (suc k) lt')
    (trans (ρᵇ-shift Θ k) (sym (outSub-lo Θ k lt)))
  where lt' : suc k < revs (rvl A ∷ shiftReps Θ)
        lt' = subst (λ n → suc k < suc n) (sym (revs-shiftReps Θ)) (s≤s lt)
outSub-shift A Θ k | inj₂ ¬lt =
  trans (outSub-hi (rvl A ∷ shiftReps Θ) (suc k) ¬lt')
    (trans (cong₂ (λ c r → ` (c + (k ∸ r)))
                  (cmax-shiftReps Θ) (revs-shiftReps Θ))
           (sym (outSub-hi Θ k ¬lt)))
  where ¬lt' : ¬ (suc k < revs (rvl A ∷ shiftReps Θ))
        ¬lt' q = ¬lt (subst (λ n → k < n) (revs-shiftReps Θ)
                            (≤-pred′ q))
          where ≤-pred′ : suc k < suc (revs (shiftReps Θ))
                        → k < revs (shiftReps Θ)
                ≤-pred′ (s≤s r) = r

outRead-shift : ∀ A Θ T
              → outRead (rvl A ∷ shiftReps Θ) (renameᵗ suc T) ≡ outRead Θ T
outRead-shift A Θ T =
  trans (rename-subst-commute suc (outSub (rvl A ∷ shiftReps Θ)) T)
        (subst-cong (outSub-shift A Θ) T)

Reversal-shift : ∀ A Θ X T A₀ → Reversal Θ X T A₀
               → Reversal (rvl A ∷ shiftReps Θ) X (renameᵗ suc T) A₀
Reversal-shift A Θ X T A₀ h = trans (outRead-shift A Θ T) h

-- the ≈ form: the read-back is UNCHANGED by the shift (the reveal block is
-- untouched and the conceal reps' shift is absorbed), so the congruence
-- witness is carried across verbatim
Reversal≈-shift : ∀ {Δ : TCtx} A Θ X T A₀ → Reversal≈ Δ Θ X T A₀
                → Reversal≈ Δ (rvl A ∷ shiftReps Θ) X (renameᵗ suc T) A₀
Reversal≈-shift {Δ} A Θ X T A₀ h =
  subst (λ S → S ≈Δ̄⟨ Δ ⟩ upRep X A₀) (sym (outRead-shift A Θ T)) h

-- the starOnly premise survives the shift: shiftReps keeps every rvl⋆ in
-- place, and the new reveal sits BELOW them all, so a rep's variables move
-- by suc exactly as the slots do
revStar-shift : ∀ Θ i → revStar (shiftReps Θ) i ≡ revStar Θ i
revStar-shift []            i       = refl
revStar-shift (rvl A ∷ Θ)   zero    = refl
revStar-shift (rvl A ∷ Θ)   (suc i) = revStar-shift Θ i
revStar-shift (rvl⋆ ∷ Θ)    zero    = refl
revStar-shift (rvl⋆ ∷ Θ)    (suc i) = revStar-shift Θ i
revStar-shift (cnc X A ∷ Θ) i       = revStar-shift Θ i
revStar-shift (cnc⋆ X ∷ Θ)  i       = revStar-shift Θ i

starOnly-shift : ∀ A Θ d B
  → starOnly (rvl A ∷ shiftReps Θ) d (renameᵗ (liftⁿ d suc) B)
    ≡ starOnly Θ d B
starOnly-shift A Θ d (` X) with split d X
starOnly-shift A Θ d (` X) | inj₁ lt
  rewrite liftⁿ-lo d suc X lt | ⌊⌋-of (X <? d) lt = refl
starOnly-shift A Θ d (` .(d + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi d suc i
        | ⌊⌋-false ((d + suc i) <? d) (m+n≮m d (suc i))
        | ⌊⌋-false ((d + i) <? d) (m+n≮m d i)
        | m+n∸m≡n d (suc i)
        | m+n∸m≡n d i = revStar-shift Θ i
starOnly-shift A Θ d `ℕ      = refl
starOnly-shift A Θ d `𝔹      = refl
starOnly-shift A Θ d (B ⇒ C) =
  cong₂ _∧_ (starOnly-shift A Θ d B) (starOnly-shift A Θ d C)
starOnly-shift A Θ d (`∀ B)  = starOnly-shift A Θ (suc d) B

-- an arbitrary entry weakens a well-formed type
wf-⇑ : ∀ {Δ A} (E : TyEntry) → Δ ⊢ A → (E ∷ Δ) ⊢ ⇑ᵗ A
wf-⇑ E wfA = wf-rename-fv (λ y → ent-skip E (fv-scope wfA y)) wfA

-- the boundary stays well formed once the interior gains one variable
bwf-shiftReps : ∀ {Δ Ψ A} (E : TyEntry) Θ Ξ → Bwf Δ Ψ Θ Ξ
  → Bwf Δ (E ∷ Ψ) (rvl A ∷ shiftReps Θ) (shiftReps Ξ)
bwf-shiftReps E Θ []            bwf[]              = bwf[]
bwf-shiftReps E Θ (rvl B ∷ Ξ)   (bwf↑ wfB b)       =
  bwf↑ wfB (bwf-shiftReps E Θ Ξ b)
bwf-shiftReps E Θ (rvl⋆ ∷ Ξ)    (bwf⋆ b)           =
  bwf⋆ (bwf-shiftReps E Θ Ξ b)
bwf-shiftReps {A = A} E Θ (cnc X B ∷ Ξ) (bwf↓ {A₀ = A₀} p rev wfB b) =
  bwf↓ p (Reversal≈-shift A Θ X B A₀ rev) (wf-⇑ E wfB)
       (bwf-shiftReps E Θ Ξ b)
bwf-shiftReps {A = A} E Θ (cnc X B ∷ Ξ) (bwf↓x p so sk wfB b) =
  bwf↓x p (trans (starOnly-shift A Θ 0 B) so) (skel-renˡ suc sk)
        (wf-⇑ E wfB) (bwf-shiftReps E Θ Ξ b)
bwf-shiftReps E Θ (cnc⋆ X ∷ Ξ) (bwf⋆↓ p b) =
  bwf⋆↓ p (bwf-shiftReps E Θ Ξ b)

-- the scope stack just gains one accessible slot for the new reveal, so R1's
-- Scoped obligation IS the sc-∀ inversion of the redex's
slotAt-shift : ∀ A Θ i → slotAt (rvl A ∷ shiftReps Θ) i ≡ slotAt Θ i
slotAt-shift A Θ i with cmax (shiftReps Θ) ≤? i | cmax Θ ≤? i
slotAt-shift A Θ i | yes _ | yes _ = refl
slotAt-shift A Θ i | yes p | no ¬q =
  ⊥-elim (¬q (subst (_≤ i) (cmax-shiftReps Θ) p))
slotAt-shift A Θ i | no ¬p | yes q =
  ⊥-elim (¬p (subst (_≤ i) (sym (cmax-shiftReps Θ)) q))
slotAt-shift A Θ i | no _  | no _ rewrite isConc-shift i Θ = refl

slotsᴳ-shift : ∀ A Θ k (Γ : TCtx)
  → slotsᴳ (rvl A ∷ shiftReps Θ) k Γ ≡ slotsᴳ Θ k Γ
slotsᴳ-shift A Θ k []      = refl
slotsᴳ-shift A Θ k (E ∷ Γ) =
  cong₂ _∷_ (slotAt-shift A Θ k) (slotsᴳ-shift A Θ (suc k) Γ)

revSlots-shift : ∀ Θ → revSlots (shiftReps Θ) ≡ revSlots Θ
revSlots-shift []            = refl
revSlots-shift (rvl A ∷ Θ)   = cong (ok ∷_) (revSlots-shift Θ)
revSlots-shift (rvl⋆ ∷ Θ)    = cong (blk ∷_) (revSlots-shift Θ)
revSlots-shift (cnc X A ∷ Θ) = revSlots-shift Θ
revSlots-shift (cnc⋆ X ∷ Θ)  = revSlots-shift Θ

baseS-shift : ∀ A Θ (Γ : TCtx)
  → baseS (rvl A ∷ shiftReps Θ) Γ ≡ ok ∷ baseS Θ Γ
baseS-shift A Θ Γ =
  cong (ok ∷_)
    (cong₂ _++_ (revSlots-shift Θ) (slotsᴳ-shift A Θ 0 Γ))

-- no lift is needed: over a boundary that already reveals, the type argument
-- is stored verbatim and its external face is itself
_ : ρᵇ (rvl (` 0) ∷ rvl `ℕ ∷ []) 0 ≡ ` 0
_ = refl

------------------------------------------------------------------------
-- Dual boundary, part 1: the SHAPE of dualᴳ.  Its reveal block is the
-- Γ-prefix Θ drops (so revs Θᵈ = cmax Θ) and its conceal block is Θ's own
-- reveals (so cmax Θᵈ = revs Θ) — the two blocks of the frame swap.  Every
-- entry the reveal block produces IS a reveal (with or without a rep), which
-- is all the shape lemmas need to know about entᴳ.
------------------------------------------------------------------------

data RvlE : BEntry → Set where
  is-rvl : ∀ {A} → RvlE (rvl A)
  is-⋆   : RvlE rvl⋆

entᴳ-RvlE : ∀ Γ Θ i k → RvlE (entᴳ Γ Θ i k)
entᴳ-RvlE Γ Θ i k with isConc i Θ
entᴳ-RvlE Γ Θ i k | true  = is-rvl
entᴳ-RvlE Γ Θ i k | false with entAt Γ i
entᴳ-RvlE Γ Θ i k | false | abst     = is-⋆
entᴳ-RvlE Γ Θ i k | false | xrvld B  = is-⋆
entᴳ-RvlE Γ Θ i k | false | rvld B with dfree 0 k B
entᴳ-RvlE Γ Θ i k | false | rvld B | true  = is-rvl
entᴳ-RvlE Γ Θ i k | false | rvld B | false
  with dfree 0 k (unfEnt Γ i B)
entᴳ-RvlE Γ Θ i k | false | rvld B | false | true  = is-rvl
entᴳ-RvlE Γ Θ i k | false | rvld B | false | false = is-⋆

revs-R : ∀ {E} → RvlE E → ∀ Ξ → revs (E ∷ Ξ) ≡ suc (revs Ξ)
revs-R is-rvl Ξ = refl
revs-R is-⋆   Ξ = refl

cmax-R : ∀ {E} → RvlE E → ∀ Ξ → cmax (E ∷ Ξ) ≡ cmax Ξ
cmax-R is-rvl Ξ = refl
cmax-R is-⋆   Ξ = refl

isConc-R : ∀ {E} → RvlE E → ∀ Ξ i → isConc i (E ∷ Ξ) ≡ isConc i Ξ
isConc-R is-rvl Ξ i = refl
isConc-R is-⋆   Ξ i = refl

ρᵇ-R-suc : ∀ {E} → RvlE E → ∀ Ξ n → ρᵇ (E ∷ Ξ) (suc n) ≡ ρᵇ Ξ n
ρᵇ-R-suc is-rvl Ξ n = refl
ρᵇ-R-suc is-⋆   Ξ n = refl

γcnc-R : ∀ {E} → RvlE E → ∀ r m Ξ i → γcnc r m (E ∷ Ξ) i ≡ γcnc r m Ξ i
γcnc-R is-rvl r m Ξ i = refl
γcnc-R is-⋆   r m Ξ i = refl

revS-R-suc : ∀ {E} → RvlE E → ∀ Ξ (S : SCtx) i
           → (revSlots Ξ ++ S) ∋ok i → (revSlots (E ∷ Ξ) ++ S) ∋ok suc i
revS-R-suc is-rvl Ξ S i p = thereᵒ p
revS-R-suc is-⋆   Ξ S i p = thereᵒ p

revs-++ : ∀ Θ₁ Θ₂ → revs (Θ₁ ++ Θ₂) ≡ revs Θ₁ + revs Θ₂
revs-++ []            Θ₂ = refl
revs-++ (rvl A ∷ Θ₁)  Θ₂ = cong suc (revs-++ Θ₁ Θ₂)
revs-++ (rvl⋆ ∷ Θ₁)   Θ₂ = cong suc (revs-++ Θ₁ Θ₂)
revs-++ (cnc X A ∷ Θ₁) Θ₂ = revs-++ Θ₁ Θ₂
revs-++ (cnc⋆ X ∷ Θ₁)  Θ₂ = revs-++ Θ₁ Θ₂

cmax-++ : ∀ Θ₁ Θ₂ → cmax (Θ₁ ++ Θ₂) ≡ cmax Θ₁ ⊔ cmax Θ₂
cmax-++ []            Θ₂ = refl
cmax-++ (rvl A ∷ Θ₁)  Θ₂ = cmax-++ Θ₁ Θ₂
cmax-++ (rvl⋆ ∷ Θ₁)   Θ₂ = cmax-++ Θ₁ Θ₂
cmax-++ (cnc X A ∷ Θ₁) Θ₂ =
  trans (cong (suc X ⊔_) (cmax-++ Θ₁ Θ₂))
        (sym (⊔-assoc (suc X) (cmax Θ₁) (cmax Θ₂)))
cmax-++ (cnc⋆ X ∷ Θ₁)  Θ₂ =
  trans (cong (suc X ⊔_) (cmax-++ Θ₁ Θ₂))
        (sym (⊔-assoc (suc X) (cmax Θ₁) (cmax Θ₂)))

revs-rvlsᴳ : ∀ k s Γ Θ → revs (rvlsᴳ k s Γ Θ) ≡ k
revs-rvlsᴳ zero    s Γ Θ = refl
revs-rvlsᴳ (suc k) s Γ Θ =
  trans (revs-R (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ))
        (cong suc (revs-rvlsᴳ k (suc s) Γ Θ))

cmax-rvlsᴳ : ∀ k s Γ Θ → cmax (rvlsᴳ k s Γ Θ) ≡ 0
cmax-rvlsᴳ zero    s Γ Θ = refl
cmax-rvlsᴳ (suc k) s Γ Θ =
  trans (cmax-R (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ))
        (cmax-rvlsᴳ k (suc s) Γ Θ)

revs-cncOfRevs : ∀ j Θ → revs (cncOfRevs j Θ) ≡ 0
revs-cncOfRevs j []            = refl
revs-cncOfRevs j (rvl A ∷ Θ)   = revs-cncOfRevs (suc j) Θ
revs-cncOfRevs j (rvl⋆ ∷ Θ)    = revs-cncOfRevs (suc j) Θ
revs-cncOfRevs j (cnc X A ∷ Θ) = revs-cncOfRevs j Θ
revs-cncOfRevs j (cnc⋆ X ∷ Θ)  = revs-cncOfRevs j Θ

-- the conceals sit at j … j + revs Θ ∸ 1, so the deepest is j + revs Θ
-- (and there is none at all when Θ has no reveal) — stated ⊔ j to cover
-- both shapes at once
cmax-cncOfRevs : ∀ j Θ → cmax (cncOfRevs j Θ) ⊔ j ≡ j + revs Θ
cmax-cncOfRevs j []            = sym (+-identityʳ j)
cmax-cncOfRevs j (rvl A ∷ Θ)   =
  trans (m≥n⇒m⊔n≡m (≤-trans (n≤1+n j)
                            (m≤m⊔n (suc j) (cmax (cncOfRevs (suc j) Θ)))))
    (trans (⊔-comm (suc j) (cmax (cncOfRevs (suc j) Θ)))
      (trans (cmax-cncOfRevs (suc j) Θ) (sym (+-suc j (revs Θ)))))
cmax-cncOfRevs j (rvl⋆ ∷ Θ)    =
  trans (m≥n⇒m⊔n≡m (≤-trans (n≤1+n j)
                            (m≤m⊔n (suc j) (cmax (cncOfRevs (suc j) Θ)))))
    (trans (⊔-comm (suc j) (cmax (cncOfRevs (suc j) Θ)))
      (trans (cmax-cncOfRevs (suc j) Θ) (sym (+-suc j (revs Θ)))))
cmax-cncOfRevs j (cnc X A ∷ Θ) = cmax-cncOfRevs j Θ
cmax-cncOfRevs j (cnc⋆ X ∷ Θ)  = cmax-cncOfRevs j Θ

cmax-cncOfRevs0 : ∀ Θ → cmax (cncOfRevs 0 Θ) ≡ revs Θ
cmax-cncOfRevs0 Θ =
  trans (sym (⊔-identityʳ (cmax (cncOfRevs 0 Θ)))) (cmax-cncOfRevs 0 Θ)

revs-dual : ∀ Γ Θ → revs (dualᴳ Γ Θ) ≡ cmax Θ
revs-dual Γ Θ =
  trans (revs-++ (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ))
    (trans (cong₂ _+_ (revs-rvlsᴳ (cmax Θ) 0 Γ Θ) (revs-cncOfRevs 0 Θ))
           (+-identityʳ (cmax Θ)))

cmax-dual : ∀ Γ Θ → cmax (dualᴳ Γ Θ) ≡ revs Θ
cmax-dual Γ Θ =
  trans (cmax-++ (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ))
    (trans (cong (_⊔ cmax (cncOfRevs 0 Θ)) (cmax-rvlsᴳ (cmax Θ) 0 Γ Θ))
           (cmax-cncOfRevs0 Θ))

------------------------------------------------------------------------
-- Part 2: the two FACE laws.  On Θ's boundary frame the slot X is sent by
-- swapᵇ to the slot of Θᵈ's frame holding the same variable, and there
--   ρᵇ Θᵈ ∘ swapᵇ Θ = γᵇ Θ    (at ACCESSIBLE slots only)
--   γᵇ Θᵈ ∘ swapᵇ Θ = ρᵇ Θ    (at every slot)
-- The first fails at a blocked slot — the dual re-introduces it from the
-- AMBIENT context while γᵇ aliases it onto a kept variable — which is why
-- R2 goes through subst-cong-sc with (env)'s scope premise.
------------------------------------------------------------------------

sover-hit : ∀ X A σ i → X ≡ i → sover X A σ i ≡ A
sover-hit X A σ i e with X ≟ i
sover-hit X A σ i e | yes _  = refl
sover-hit X A σ i e | no ¬e  = ⊥-elim (¬e e)

sover-miss : ∀ X A σ i → ¬ (X ≡ i) → sover X A σ i ≡ σ i
sover-miss X A σ i ne with X ≟ i
sover-miss X A σ i ne | yes e = ⊥-elim (ne e)
sover-miss X A σ i ne | no _  = refl

j≢j+suc : ∀ j k → ¬ (j ≡ j + suc k)
j≢j+suc zero    k ()
j≢j+suc (suc j) k e = j≢j+suc j k (suc-injective e)

isConc-< : ∀ Θ i → isConc i Θ ≡ true → i < cmax Θ
isConc-< []            i ()
isConc-< (rvl A ∷ Θ)   i c = isConc-< Θ i c
isConc-< (rvl⋆ ∷ Θ)    i c = isConc-< Θ i c
isConc-< (cnc X A ∷ Θ) i c with isConc-cons i X A Θ c
isConc-< (cnc X A ∷ Θ) i c | inj₁ refl = m≤m⊔n (suc i) (cmax Θ)
isConc-< (cnc X A ∷ Θ) i c | inj₂ t =
  ≤-trans (isConc-< Θ i t) (m≤n⊔m (suc X) (cmax Θ))
isConc-< (cnc⋆ X ∷ Θ)  i c =
  ≤-trans (isConc-< Θ i c) (m≤n⊔m (suc X) (cmax Θ))

-- the interior face at a Γ-slot: a concealed one goes to its rep, a kept
-- one to its interior slot
γcnc-conc : ∀ r m Θ i → isConc i Θ ≡ true → γcnc r m Θ i ≡ repOf i Θ
γcnc-conc r m []            i ()
γcnc-conc r m (rvl A ∷ Θ)   i c = γcnc-conc r m Θ i c
γcnc-conc r m (rvl⋆ ∷ Θ)    i c = γcnc-conc r m Θ i c
γcnc-conc r m (cnc X A ∷ Θ) i c with X ≟ i | i ≟ X
γcnc-conc r m (cnc X A ∷ Θ) i c | yes p | yes q = refl
γcnc-conc r m (cnc X A ∷ Θ) i c | yes p | no ¬q = ⊥-elim (¬q (sym p))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | yes q = ⊥-elim (¬p (sym q))
γcnc-conc r m (cnc X A ∷ Θ) i c | no ¬p | no ¬q = γcnc-conc r m Θ i c
γcnc-conc r m (cnc⋆ X ∷ Θ)  i c = γcnc-conc r m Θ i c

γcnc-kept : ∀ r m Θ i → cmax Θ ≤ i → γcnc r m Θ i ≡ ` (r + (i ∸ m))
γcnc-kept r m []            i le = refl
γcnc-kept r m (rvl A ∷ Θ)   i le = γcnc-kept r m Θ i le
γcnc-kept r m (rvl⋆ ∷ Θ)    i le = γcnc-kept r m Θ i le
γcnc-kept r m (cnc X A ∷ Θ) i le =
  trans (sover-miss X A (γcnc r m Θ) i ne)
        (γcnc-kept r m Θ i (≤-trans (m≤n⊔m (suc X) (cmax Θ)) le))
  where
    ne : ¬ (X ≡ i)
    ne p = <-irrefl p (≤-trans (m≤m⊔n (suc X) (cmax Θ)) le)
γcnc-kept r m (cnc⋆ X ∷ Θ)  i le =
  γcnc-kept r m Θ i (≤-trans (m≤n⊔m (suc X) (cmax Θ)) le)

γᵇ-conc : ∀ Θ i → isConc i Θ ≡ true → γᵇ Θ (revs Θ + i) ≡ repOf i Θ
γᵇ-conc Θ i c =
  trans (prepId-hi (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) i)
        (γcnc-conc (revs Θ) (cmax Θ) Θ i c)

γᵇ-kept : ∀ Θ i → cmax Θ ≤ i
        → γᵇ Θ (revs Θ + i) ≡ ` (revs Θ + (i ∸ cmax Θ))
γᵇ-kept Θ i le =
  trans (prepId-hi (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) i)
        (γcnc-kept (revs Θ) (cmax Θ) Θ i le)

-- the exterior face of the DUAL: its reveal block resolves the dropped
-- slots, and everything above it passes through
ρᵇ-cncOfRevs : ∀ j Θ i → ρᵇ (cncOfRevs j Θ) i ≡ ` i
ρᵇ-cncOfRevs j []            i = refl
ρᵇ-cncOfRevs j (rvl A ∷ Θ)   i = ρᵇ-cncOfRevs (suc j) Θ i
ρᵇ-cncOfRevs j (rvl⋆ ∷ Θ)    i = ρᵇ-cncOfRevs (suc j) Θ i
ρᵇ-cncOfRevs j (cnc X A ∷ Θ) i = ρᵇ-cncOfRevs j Θ i
ρᵇ-cncOfRevs j (cnc⋆ X ∷ Θ)  i = ρᵇ-cncOfRevs j Θ i

ρᵇ-rvlsᴳ-hi : ∀ k s Γ Θ Ξ j → ρᵇ (rvlsᴳ k s Γ Θ ++ Ξ) (k + j) ≡ ρᵇ Ξ j
ρᵇ-rvlsᴳ-hi zero    s Γ Θ Ξ j = refl
ρᵇ-rvlsᴳ-hi (suc k) s Γ Θ Ξ j =
  trans (ρᵇ-R-suc (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ ++ Ξ) (k + j))
        (ρᵇ-rvlsᴳ-hi k (suc s) Γ Θ Ξ j)

ρᵇ-dual-hi : ∀ Γ Θ k → ρᵇ (dualᴳ Γ Θ) (cmax Θ + k) ≡ ` k
ρᵇ-dual-hi Γ Θ k =
  trans (ρᵇ-rvlsᴳ-hi (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ) k)
        (ρᵇ-cncOfRevs 0 Θ k)

-- at a CONCEALED slot the dual's reveal carries Θ's own conceal rep, and the
-- PARALLEL external face hands it straight back — no telescope to resolve
ρᵇ-ent-conc : ∀ Γ Θ s k (Ξ : BCtx) → isConc s Θ ≡ true
  → ρᵇ (entᴳ Γ Θ s k ∷ Ξ) zero ≡ repOf s Θ
ρᵇ-ent-conc Γ Θ s k Ξ c with isConc s Θ | c
ρᵇ-ent-conc Γ Θ s k Ξ c | true  | _ = refl
ρᵇ-ent-conc Γ Θ s k Ξ c | false | ()

ρᵇ-rvlsᴳ-conc : ∀ k s Γ Θ i → i < k → isConc (s + i) Θ ≡ true
  → ρᵇ (rvlsᴳ k s Γ Θ ++ cncOfRevs 0 Θ) i ≡ repOf (s + i) Θ
ρᵇ-rvlsᴳ-conc zero    s Γ Θ i       ()       c
ρᵇ-rvlsᴳ-conc (suc k) s Γ Θ zero    lt       c =
  trans (ρᵇ-ent-conc Γ Θ s k (rvlsᴳ k (suc s) Γ Θ ++ cncOfRevs 0 Θ)
          (trans (cong (λ n → isConc n Θ) (sym (+-identityʳ s))) c))
        (cong (λ n → repOf n Θ) (sym (+-identityʳ s)))
ρᵇ-rvlsᴳ-conc (suc k) s Γ Θ (suc i) (s≤s lt) c =
  trans (ρᵇ-R-suc (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ ++ cncOfRevs 0 Θ)
                  i)
        (trans (ρᵇ-rvlsᴳ-conc k (suc s) Γ Θ i lt
                 (trans (cong (λ n → isConc n Θ) (sym (+-suc s i))) c))
               (cong (λ n → repOf n Θ) (sym (+-suc s i))))

ρᵇ-dual-lo : ∀ Γ Θ i → i < cmax Θ → isConc i Θ ≡ true
           → ρᵇ (dualᴳ Γ Θ) i ≡ repOf i Θ
ρᵇ-dual-lo Γ Θ i lt c = ρᵇ-rvlsᴳ-conc (cmax Θ) 0 Γ Θ i lt c

-- the interior face of the DUAL: its conceal block resolves Θ's reveal
-- variables to Θ's own EXTERNAL faces, and everything above it is kept
γcnc-rvlsᴳ : ∀ r m k s Γ Θ Ξ i
  → γcnc r m (rvlsᴳ k s Γ Θ ++ Ξ) i ≡ γcnc r m Ξ i
γcnc-rvlsᴳ r m zero    s Γ Θ Ξ i = refl
γcnc-rvlsᴳ r m (suc k) s Γ Θ Ξ i =
  trans (γcnc-R (entᴳ-RvlE Γ Θ s k) r m
                (rvlsᴳ k (suc s) Γ Θ ++ Ξ) i)
        (γcnc-rvlsᴳ r m k (suc s) Γ Θ Ξ i)

-- RESTRICTED to a REP-CARRYING reveal slot.  The dual conceals a rvl⋆ with
-- cnc⋆, which has NO γ-image (StarConcealProbe §4.5) — and rightly so: a
-- rvl⋆ slot is `blk` in baseS, so no boundary type can name it, and the
-- face law is only ever consumed at accessible slots.
γcnc-cnc-lo : ∀ r m j Θ k → k < revs Θ → revStar Θ k ≡ false
  → γcnc r m (cncOfRevs j Θ) (j + k) ≡ ρᵇ Θ k
γcnc-cnc-lo r m j []            k       ()       ns
γcnc-cnc-lo r m j (rvl A ∷ Θ)   zero    lt       ns =
  sover-hit j A (γcnc r m (cncOfRevs (suc j) Θ)) (j + 0)
            (sym (+-identityʳ j))
γcnc-cnc-lo r m j (rvl A ∷ Θ)   (suc k) (s≤s lt) ns =
  trans (sover-miss j A (γcnc r m (cncOfRevs (suc j) Θ)) (j + suc k)
                    (j≢j+suc j k))
    (trans (cong (γcnc r m (cncOfRevs (suc j) Θ)) (+-suc j k))
           (γcnc-cnc-lo r m (suc j) Θ k lt ns))
γcnc-cnc-lo r m j (rvl⋆ ∷ Θ)    zero    lt       ()
γcnc-cnc-lo r m j (rvl⋆ ∷ Θ)    (suc k) (s≤s lt) ns =
  trans (cong (γcnc r m (cncOfRevs (suc j) Θ)) (+-suc j k))
        (γcnc-cnc-lo r m (suc j) Θ k lt ns)
γcnc-cnc-lo r m j (cnc X A ∷ Θ) k       lt       ns =
  γcnc-cnc-lo r m j Θ k lt ns
γcnc-cnc-lo r m j (cnc⋆ X ∷ Θ)  k       lt       ns =
  γcnc-cnc-lo r m j Θ k lt ns

γcnc-cnc-hi : ∀ r m j Θ i → j + revs Θ ≤ i
  → γcnc r m (cncOfRevs j Θ) i ≡ ` (r + (i ∸ m))
γcnc-cnc-hi r m j []            i le = refl
γcnc-cnc-hi r m j (rvl A ∷ Θ)   i le =
  trans (sover-miss j A (γcnc r m (cncOfRevs (suc j) Θ)) i ne)
        (γcnc-cnc-hi r m (suc j) Θ i le')
  where
    le' : suc j + revs Θ ≤ i
    le' = subst (_≤ i) (+-suc j (revs Θ)) le
    ne : ¬ (j ≡ i)
    ne p = <-irrefl p (≤-trans (s≤s (m≤m+n j (revs Θ))) le')
γcnc-cnc-hi r m j (rvl⋆ ∷ Θ)    i le =
  γcnc-cnc-hi r m (suc j) Θ i (subst (_≤ i) (+-suc j (revs Θ)) le)
γcnc-cnc-hi r m j (cnc X A ∷ Θ) i le = γcnc-cnc-hi r m j Θ i le
γcnc-cnc-hi r m j (cnc⋆ X ∷ Θ)  i le = γcnc-cnc-hi r m j Θ i le

γᵇ-dual-lo : ∀ Γ Θ i → i < cmax Θ → γᵇ (dualᴳ Γ Θ) i ≡ ` i
γᵇ-dual-lo Γ Θ i lt =
  prepId-lo (revs (dualᴳ Γ Θ))
            (γcnc (revs (dualᴳ Γ Θ)) (cmax (dualᴳ Γ Θ)) (dualᴳ Γ Θ)) i
            (subst (i <_) (sym (revs-dual Γ Θ)) lt)

γᵇ-dual-hi : ∀ Γ Θ k
  → γᵇ (dualᴳ Γ Θ) (cmax Θ + k)
    ≡ γcnc (cmax Θ) (revs Θ) (dualᴳ Γ Θ) k
γᵇ-dual-hi Γ Θ k =
  trans (prepId-hi′ (cmax Θ) (revs (dualᴳ Γ Θ))
                    (γcnc (revs (dualᴳ Γ Θ)) (cmax (dualᴳ Γ Θ))
                          (dualᴳ Γ Θ)) k
                    (revs-dual Γ Θ))
        (cong₂ (λ a b → γcnc a b (dualᴳ Γ Θ) k)
               (revs-dual Γ Θ) (cmax-dual Γ Θ))

γcnc-dual-lo : ∀ Γ Θ k → k < revs Θ → revStar Θ k ≡ false
  → γcnc (cmax Θ) (revs Θ) (dualᴳ Γ Θ) k ≡ ρᵇ Θ k
γcnc-dual-lo Γ Θ k lt ns =
  trans (γcnc-rvlsᴳ (cmax Θ) (revs Θ) (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ) k)
        (γcnc-cnc-lo (cmax Θ) (revs Θ) 0 Θ k lt ns)

γcnc-dual-hi : ∀ Γ Θ k → revs Θ ≤ k
  → γcnc (cmax Θ) (revs Θ) (dualᴳ Γ Θ) k ≡ ` (cmax Θ + (k ∸ revs Θ))
γcnc-dual-hi Γ Θ k le =
  trans (γcnc-rvlsᴳ (cmax Θ) (revs Θ) (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ) k)
        (γcnc-cnc-hi (cmax Θ) (revs Θ) 0 Θ k le)

-- the frame permutation, on the three regions of Θ's frame
swap-lo : ∀ r c X → X < r → swapIdx r c X ≡ c + X
swap-lo r c X lt with X <? r
swap-lo r c X lt | yes _  = refl
swap-lo r c X lt | no ¬lt = ⊥-elim (¬lt lt)

swap-mid : ∀ r c i → i < c → swapIdx r c (r + i) ≡ i
swap-mid r c i lt with (r + i) <? r
swap-mid r c i lt | yes p = ⊥-elim (m+n≮m r i p)
swap-mid r c i lt | no ¬p with ((r + i) ∸ r) <? c
swap-mid r c i lt | no ¬p | yes q = m+n∸m≡n r i
swap-mid r c i lt | no ¬p | no ¬q =
  ⊥-elim (¬q (subst (_< c) (sym (m+n∸m≡n r i)) lt))

swap-hi : ∀ r c i → c ≤ i → swapIdx r c (r + i) ≡ r + i
swap-hi r c i le with (r + i) <? r
swap-hi r c i le | yes p = ⊥-elim (m+n≮m r i p)
swap-hi r c i le | no ¬p with ((r + i) ∸ r) <? c
swap-hi r c i le | no ¬p | yes q =
  ⊥-elim (<-irrefl refl (≤-trans (subst (_< c) (m+n∸m≡n r i) q) le))
swap-hi r c i le | no ¬p | no ¬q = refl

-- a kept slot keeps its position: c + (r + (i ∸ c)) = r + i
kept-idx : ∀ r c i → c ≤ i → c + (r + (i ∸ c)) ≡ r + i
kept-idx r c i le =
  trans (sym (+-assoc c r (i ∸ c)))
    (trans (cong (_+ (i ∸ c)) (+-comm c r))
      (trans (+-assoc r c (i ∸ c)) (cong (r +_) (m+[n∸m]≡n le))))

-- FACE LAW (exterior of the dual = interior of Θ), at accessible slots
ρᵇ-dual-swap : ∀ {Δ} Γ Θ X → baseS Θ Δ ∋ok X
             → ρᵇ (dualᴳ Γ Θ) (swapᵇ Θ X) ≡ γᵇ Θ X
ρᵇ-dual-swap Γ Θ X okp with split (revs Θ) X
ρᵇ-dual-swap Γ Θ X okp | inj₁ lt =
  trans (cong (ρᵇ (dualᴳ Γ Θ)) (swap-lo (revs Θ) (cmax Θ) X lt))
    (trans (ρᵇ-dual-hi Γ Θ X)
           (sym (prepId-lo (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) X lt)))
ρᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl)
  with baseS-acc Θ i okp
ρᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₁ le =
  trans (cong (ρᵇ (dualᴳ Γ Θ))
              (trans (swap-hi (revs Θ) (cmax Θ) i le)
                     (sym (kept-idx (revs Θ) (cmax Θ) i le))))
    (trans (ρᵇ-dual-hi Γ Θ (revs Θ + (i ∸ cmax Θ)))
           (sym (γᵇ-kept Θ i le)))
ρᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₂ cc =
  trans (cong (ρᵇ (dualᴳ Γ Θ))
              (swap-mid (revs Θ) (cmax Θ) i (isConc-< Θ i cc)))
    (trans (ρᵇ-dual-lo Γ Θ i (isConc-< Θ i cc) cc) (sym (γᵇ-conc Θ i cc)))

-- the reveal slots a Scoped boundary type can name are exactly the
-- REP-CARRYING ones: a rvl⋆'s slot is `blk`
revS-notStar : ∀ Θ {Ψ : SCtx} k → k < revs Θ
             → (revSlots Θ ++ Ψ) ∋ok k → revStar Θ k ≡ false
revS-notStar []            k       ()       p
revS-notStar (rvl A ∷ Θ)   zero    lt       p = refl
revS-notStar (rvl A ∷ Θ)   (suc k) (s≤s lt) p =
  revS-notStar Θ k lt (∋ok-tail p)
revS-notStar (rvl⋆ ∷ Θ)    zero    lt       p =
  ⊥-elim (ok≢blk (sym (∋ok-head p)))
revS-notStar (rvl⋆ ∷ Θ)    (suc k) (s≤s lt) p =
  revS-notStar Θ k lt (∋ok-tail p)
revS-notStar (cnc X A ∷ Θ) k       lt       p = revS-notStar Θ k lt p
revS-notStar (cnc⋆ X ∷ Θ)  k       lt       p = revS-notStar Θ k lt p

-- FACE LAW (interior of the dual = exterior of Θ), at ACCESSIBLE slots.
-- It used to hold at EVERY slot; with cnc⋆ it holds exactly where (env)'s
-- Scoped premise permits B₀ to look, which is all preservation consumes.
γᵇ-dual-swap : ∀ {Δ} Γ Θ X → baseS Θ Δ ∋ok X
             → γᵇ (dualᴳ Γ Θ) (swapᵇ Θ X) ≡ ρᵇ Θ X
γᵇ-dual-swap Γ Θ X okp with split (revs Θ) X
γᵇ-dual-swap {Δ} Γ Θ X okp | inj₁ lt =
  trans (cong (γᵇ (dualᴳ Γ Θ)) (swap-lo (revs Θ) (cmax Θ) X lt))
        (trans (γᵇ-dual-hi Γ Θ X)
               (γcnc-dual-lo Γ Θ X lt
                 (revS-notStar Θ X lt okp)))
γᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) with cmax Θ ≤? i
γᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | yes le =
  trans (cong (γᵇ (dualᴳ Γ Θ))
              (trans (swap-hi (revs Θ) (cmax Θ) i le)
                     (sym (kept-idx (revs Θ) (cmax Θ) i le))))
    (trans (γᵇ-dual-hi Γ Θ (revs Θ + (i ∸ cmax Θ)))
      (trans (γcnc-dual-hi Γ Θ (revs Θ + (i ∸ cmax Θ))
                           (m≤m+n (revs Θ) (i ∸ cmax Θ)))
        (trans (cong (λ n → ` (cmax Θ + n))
                     (m+n∸m≡n (revs Θ) (i ∸ cmax Θ)))
          (trans (cong `_ (m+[n∸m]≡n le)) (sym (ρᵇ-hi Θ i))))))
γᵇ-dual-swap Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | no ¬le =
  trans (cong (γᵇ (dualᴳ Γ Θ)) (swap-mid (revs Θ) (cmax Θ) i (≰⇒> ¬le)))
        (trans (γᵇ-dual-lo Γ Θ i (≰⇒> ¬le)) (sym (ρᵇ-hi Θ i)))

-- the two face laws as the retypings preservation needs.  The exterior one
-- is scope-restricted (subst-cong-sc with (env)'s premise for B₁).
ρᵇ-dual-ty : ∀ {Δ} Γ B Θ → Scoped (baseS Θ Δ) B
  → substᵗ (ρᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (γᵇ Θ) B
ρᵇ-dual-ty Γ B Θ sc =
  trans (rename-subst-commute (swapᵇ Θ) (ρᵇ (dualᴳ Γ Θ)) B)
        (subst-cong-sc sc (λ X okp → ρᵇ-dual-swap Γ Θ X okp))

γᵇ-dual-ty : ∀ {Δ} Γ B Θ → Scoped (baseS Θ Δ) B
  → substᵗ (γᵇ (dualᴳ Γ Θ)) (renameᵗ (swapᵇ Θ) B) ≡ substᵗ (ρᵇ Θ) B
γᵇ-dual-ty Γ B Θ sc =
  trans (rename-subst-commute (swapᵇ Θ) (γᵇ (dualᴳ Γ Θ)) B)
        (subst-cong-sc sc (λ X okp → γᵇ-dual-swap Γ Θ X okp))

------------------------------------------------------------------------
-- Part 3: the dual's frame is all-accessible where it must be.
------------------------------------------------------------------------

isConc-++ʳ : ∀ i Θ₁ Θ₂ → isConc i Θ₂ ≡ true → isConc i (Θ₁ ++ Θ₂) ≡ true
isConc-++ʳ i []            Θ₂ c = c
isConc-++ʳ i (rvl A ∷ Θ₁)  Θ₂ c = isConc-++ʳ i Θ₁ Θ₂ c
isConc-++ʳ i (rvl⋆ ∷ Θ₁)   Θ₂ c = isConc-++ʳ i Θ₁ Θ₂ c
isConc-++ʳ i (cnc X A ∷ Θ₁) Θ₂ c =
  isConc-there i X A (Θ₁ ++ Θ₂) (isConc-++ʳ i Θ₁ Θ₂ c)
isConc-++ʳ i (cnc⋆ X ∷ Θ₁)  Θ₂ c = isConc-++ʳ i Θ₁ Θ₂ c

isConc-cncOfRevs : ∀ j Θ k → k < revs Θ → revStar Θ k ≡ false
                 → isConc (j + k) (cncOfRevs j Θ) ≡ true
isConc-cncOfRevs j []            k       ()       ns
isConc-cncOfRevs j (rvl A ∷ Θ)   zero    lt       ns =
  isConc-here (j + 0) j A (cncOfRevs (suc j) Θ)
              (+-identityʳ j)
isConc-cncOfRevs j (rvl A ∷ Θ)   (suc k) (s≤s lt) ns =
  isConc-there (j + suc k) j A (cncOfRevs (suc j) Θ)
    (subst (λ n → isConc n (cncOfRevs (suc j) Θ) ≡ true)
           (sym (+-suc j k)) (isConc-cncOfRevs (suc j) Θ k lt ns))
isConc-cncOfRevs j (rvl⋆ ∷ Θ)    zero    lt       ()
isConc-cncOfRevs j (rvl⋆ ∷ Θ)    (suc k) (s≤s lt) ns =
  subst (λ n → isConc n (cncOfRevs (suc j) Θ) ≡ true)
        (sym (+-suc j k)) (isConc-cncOfRevs (suc j) Θ k lt ns)
isConc-cncOfRevs j (cnc X A ∷ Θ) k       lt       ns =
  isConc-cncOfRevs j Θ k lt ns
isConc-cncOfRevs j (cnc⋆ X ∷ Θ)  k       lt       ns =
  isConc-cncOfRevs j Θ k lt ns

isConc-dual : ∀ Γ Θ k → k < revs Θ → revStar Θ k ≡ false
            → isConc k (dualᴳ Γ Θ) ≡ true
isConc-dual Γ Θ k lt ns =
  isConc-++ʳ k (rvlsᴳ (cmax Θ) 0 Γ Θ) (cncOfRevs 0 Θ)
             (isConc-cncOfRevs 0 Θ k lt ns)

dropN-∋tv : ∀ c (Γ : TCtx) i → c ≤ i → Γ ∋tv i → dropN c Γ ∋tv (i ∸ c)
dropN-∋tv zero    Γ       i       le       p = p
dropN-∋tv (suc c) []      i       le       ()
dropN-∋tv (suc c) (E ∷ Γ) zero    ()       p
dropN-∋tv (suc c) (E ∷ Γ) (suc i) (s≤s le) p =
  dropN-∋tv c Γ i le (∋tv-tail p)

revS-ent-ok : ∀ Γ Θ s k Ξ (S : SCtx) → isConc s Θ ≡ true
            → (revSlots (entᴳ Γ Θ s k ∷ Ξ) ++ S) ∋ok zero
revS-ent-ok Γ Θ s k Ξ S c with isConc s Θ | c
revS-ent-ok Γ Θ s k Ξ S c | true  | _  = hereᵒ
revS-ent-ok Γ Θ s k Ξ S c | false | ()

revS-rvlsᴳ-ok : ∀ k s Γ Θ Ξ₀ (S : SCtx) i → i < k
              → isConc (s + i) Θ ≡ true
              → (revSlots (rvlsᴳ k s Γ Θ ++ Ξ₀) ++ S) ∋ok i
revS-rvlsᴳ-ok zero    s Γ Θ Ξ₀ S i       ()       c
revS-rvlsᴳ-ok (suc k) s Γ Θ Ξ₀ S zero    lt       c =
  revS-ent-ok Γ Θ s k (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀) S
              (trans (cong (λ n → isConc n Θ) (sym (+-identityʳ s))) c)
revS-rvlsᴳ-ok (suc k) s Γ Θ Ξ₀ S (suc i) (s≤s lt) c =
  revS-R-suc (entᴳ-RvlE Γ Θ s k) (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀) S i
    (revS-rvlsᴳ-ok k (suc s) Γ Θ Ξ₀ S i lt
      (trans (cong (λ n → isConc n Θ) (sym (+-suc s i))) c))

-- every slot swapᵇ can reach in the dual's frame is ACCESSIBLE
swap-ok : ∀ {Δ} Γ Θ X → baseS Θ Δ ∋ok X
        → baseS (dualᴳ Γ Θ) (intOf Δ Θ) ∋ok swapᵇ Θ X
swap-ok {Δ} Γ Θ X okp with split (revs Θ) X
swap-ok {Δ} Γ Θ X okp | inj₁ lt =
  ∋ok-≡ (trans (cong (_+ X) (revs-dual Γ Θ))
               (sym (swap-lo (revs Θ) (cmax Θ) X lt)))
        (baseS-ok (dualᴳ Γ Θ) X
                  (inj₂ (isConc-dual Γ Θ X lt (revS-notStar Θ X lt okp)))
                  (revE-lo Θ 0 Θ X lt))
swap-ok {Δ} Γ Θ .(revs Θ + i) okp | inj₂ (i , refl)
  with baseS-acc Θ i okp
swap-ok {Δ} Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₁ le =
  ∋ok-≡ (trans (cong (_+ (revs Θ + (i ∸ cmax Θ))) (revs-dual Γ Θ))
          (trans (kept-idx (revs Θ) (cmax Θ) i le)
                 (sym (swap-hi (revs Θ) (cmax Θ) i le))))
        (baseS-ok (dualᴳ Γ Θ) (revs Θ + (i ∸ cmax Θ))
                  (inj₁ (subst (_≤ revs Θ + (i ∸ cmax Θ))
                               (sym (cmax-dual Γ Θ))
                               (m≤m+n (revs Θ) (i ∸ cmax Θ))))
                  (revE-hi Θ 0 Θ
                    (dropN-∋tv (cmax Θ) Δ i le (baseS-∋tv Θ i okp))))
swap-ok {Δ} Γ Θ .(revs Θ + i) okp | inj₂ (i , refl) | inj₂ cc =
  ∋ok-≡ (sym (swap-mid (revs Θ) (cmax Θ) i (isConc-< Θ i cc)))
        (revS-rvlsᴳ-ok (cmax Θ) 0 Γ Θ (cncOfRevs 0 Θ)
                       (slotsᴳ (dualᴳ Γ Θ) 0 (intOf Δ Θ)) i
                       (isConc-< Θ i cc) cc)

sc-dual : ∀ {Δ B} Γ Θ → Scoped (baseS Θ Δ) B
        → Scoped (baseS (dualᴳ Γ Θ) (intOf Δ Θ)) (renameᵗ (swapᵇ Θ) B)
sc-dual Γ Θ sc = sc-rename (λ X okp → swap-ok Γ Θ X okp) sc

------------------------------------------------------------------------
-- Part 4: lengths.  The dual's interior has the same LENGTH as the
-- exterior it rebuilds — the shape half of the context law (the knowledge
-- half is where the Θn residue lives; notes/DECISIONS.md, (R2)).
------------------------------------------------------------------------

len-dropN : ∀ c (Γ : TCtx) → length (dropN c Γ) ≡ length Γ ∸ c
len-dropN zero    Γ       = refl
len-dropN (suc c) []      = refl
len-dropN (suc c) (E ∷ Γ) = len-dropN c Γ

len-++ : ∀ (Ψ₀ Γ : TCtx) → length (Ψ₀ ++ Γ) ≡ length Ψ₀ + length Γ
len-++ []       Γ = refl
len-++ (E ∷ Ψ₀) Γ = cong suc (len-++ Ψ₀ Γ)

len-intOf : ∀ (Γ : TCtx) Θ
          → length (intOf Γ Θ) ≡ revs Θ + (length Γ ∸ cmax Θ)
len-intOf Γ Θ =
  trans (len-++ (revEnts Θ 0 Θ) (dropN (cmax Θ) Γ))
        (cong₂ _+_ (len-revEnts Θ 0 Θ) (len-dropN (cmax Θ) Γ))

len-dual : ∀ (Δ : TCtx) Γ Θ → cmax Θ ≤ length Δ
         → length Δ ≡ length (intOf (intOf Δ Θ) (dualᴳ Γ Θ))
len-dual Δ Γ Θ le =
  sym (trans (len-intOf (intOf Δ Θ) (dualᴳ Γ Θ))
        (trans (cong₂ (λ a b → a + (length (intOf Δ Θ) ∸ b))
                      (revs-dual Γ Θ) (cmax-dual Γ Θ))
          (trans (cong (λ n → cmax Θ + (n ∸ revs Θ)) (len-intOf Δ Θ))
            (trans (cong (cmax Θ +_)
                         (m+n∸m≡n (revs Θ) (length Δ ∸ cmax Θ)))
                   (m+[n∸m]≡n le)))))

-- the deepest conceal is a variable of Δ, so the dropped prefix is no
-- longer than Δ — the side condition len-dual needs
∋tv-len-bound : ∀ {Γ : TCtx} {X} → Γ ∋tv X → suc X ≤ length Γ
∋tv-len-bound here-abst     = s≤s z≤n
∋tv-len-bound here-rvld     = s≤s z≤n
∋tv-len-bound here-xrvld    = s≤s z≤n
∋tv-len-bound (skip-xrvld p) = s≤s (∋tv-len-bound p)
∋tv-len-bound (skip-abst p) = s≤s (∋tv-len-bound p)
∋tv-len-bound (skip-rvld p) = s≤s (∋tv-len-bound p)

bwf-cmax : ∀ {Δ Ψ Θ} Ξ → Bwf Δ Ψ Θ Ξ → cmax Ξ ≤ length Δ
bwf-cmax []            bwf[]             = z≤n
bwf-cmax (rvl A ∷ Ξ)   (bwf↑ wfA b)      = bwf-cmax Ξ b
bwf-cmax (rvl⋆ ∷ Ξ)    (bwf⋆ b)          = bwf-cmax Ξ b
bwf-cmax (cnc X A ∷ Ξ) (bwf↓ p rev wfA b) =
  ⊔-lub (∋tv-len-bound (∋:=→∋tv p)) (bwf-cmax Ξ b)
bwf-cmax (cnc X A ∷ Ξ) (bwf↓x p so sk wfA b) =
  ⊔-lub (∋tv-len-bound (∋:=x→∋tv p)) (bwf-cmax Ξ b)
bwf-cmax (cnc⋆ X ∷ Ξ)  (bwf⋆↓ p b) =
  ⊔-lub (∋tv-len-bound p) (bwf-cmax Ξ b)

------------------------------------------------------------------------
-- Part 5: the dual's well-formedness, block by block.  Its REVEAL block
-- asks that every re-introduced rep be well formed over the dual's PLAIN
-- exterior (the parallel reading); its CONCEAL block asks that the dual's
-- exterior — Θ's interior — KNOW each reveal variable, and that Θ's external
-- face read back to that knowledge.
-- The second is exactly where the (R2) residue lives (a reveal whose rep
-- names a slot its own boundary blocks gets an `abst` interior entry, so
-- there is no knowledge to meet); it is left as a pointwise obligation for
-- the preservation proof rather than being assumed here.
------------------------------------------------------------------------

bwf-++ : ∀ {Γ Ψ Θ} Ξ₁ Ξ₂ → revs Ξ₂ ≡ 0
       → Bwf Γ Ψ Θ Ξ₁ → Bwf Γ Ψ Θ Ξ₂ → Bwf Γ Ψ Θ (Ξ₁ ++ Ξ₂)
bwf-++ []             Ξ₂ e bwf[]              b₂ = b₂
bwf-++ (rvl A ∷ Ξ₁)   Ξ₂ e (bwf↑ wfA b)       b₂ =
  bwf↑ wfA (bwf-++ Ξ₁ Ξ₂ e b b₂)
bwf-++ (rvl⋆ ∷ Ξ₁)    Ξ₂ e (bwf⋆ b)           b₂ =
  bwf⋆ (bwf-++ Ξ₁ Ξ₂ e b b₂)
bwf-++ (cnc X A ∷ Ξ₁) Ξ₂ e (bwf↓ p rev wfA b) b₂ =
  bwf↓ p rev wfA (bwf-++ Ξ₁ Ξ₂ e b b₂)
bwf-++ (cnc X A ∷ Ξ₁) Ξ₂ e (bwf↓x p so sk wfA b) b₂ =
  bwf↓x p so sk wfA (bwf-++ Ξ₁ Ξ₂ e b b₂)
bwf-++ (cnc⋆ X ∷ Ξ₁)  Ξ₂ e (bwf⋆↓ p b) b₂ =
  bwf⋆↓ p (bwf-++ Ξ₁ Ξ₂ e b b₂)

bwf-ent : ∀ {Ψ Δ' Θᵈ} Γ Θ s k Ξ
  → (∀ R → entᴳ Γ Θ s k ≡ rvl R → Ψ ⊢ R)
  → Bwf Ψ Δ' Θᵈ Ξ → Bwf Ψ Δ' Θᵈ (entᴳ Γ Θ s k ∷ Ξ)
bwf-ent Γ Θ s k Ξ h b with isConc s Θ
bwf-ent Γ Θ s k Ξ h b | true  = bwf↑ (h _ refl) b
bwf-ent Γ Θ s k Ξ h b | false with entAt Γ s
bwf-ent Γ Θ s k Ξ h b | false | abst     = bwf⋆ b
bwf-ent Γ Θ s k Ξ h b | false | xrvld B  = bwf⋆ b
bwf-ent Γ Θ s k Ξ h b | false | rvld B with dfree 0 k B
bwf-ent Γ Θ s k Ξ h b | false | rvld B | true  = bwf↑ (h _ refl) b
bwf-ent Γ Θ s k Ξ h b | false | rvld B | false
  with dfree 0 k (unfEnt Γ s B)
bwf-ent Γ Θ s k Ξ h b | false | rvld B | false | true  = bwf↑ (h _ refl) b
bwf-ent Γ Θ s k Ξ h b | false | rvld B | false | false = bwf⋆ b

bwf-rvlsᴳ : ∀ {Ψ Δ' Θᵈ} k s Γ Θ Ξ₀
  → (∀ k' s' R → entᴳ Γ Θ s' k' ≡ rvl R → Ψ ⊢ R)
  → Bwf Ψ Δ' Θᵈ Ξ₀
  → Bwf Ψ Δ' Θᵈ (rvlsᴳ k s Γ Θ ++ Ξ₀)
bwf-rvlsᴳ zero    s Γ Θ Ξ₀ h b = b
bwf-rvlsᴳ (suc k) s Γ Θ Ξ₀ h b =
  bwf-ent Γ Θ s k (rvlsᴳ k (suc s) Γ Θ ++ Ξ₀) (h k s)
    (bwf-rvlsᴳ k (suc s) Γ Θ Ξ₀ h b)

-- WHAT LICENSES ONE DUAL CONCEAL (notes/DualLicenseDesign.md §2).  The
-- dual's conceal block is ENTRY-INDEPENDENT: every rep-carrying reveal is
-- concealed at its stored rep, and the licence comes from whichever clause
-- the interior supports — ordinary knowledge (bwf-↓) or the exterior-read
-- mark (bwf-↓x).  A rep-LESS reveal is concealed by cnc⋆, whose only
-- premise is that the slot exists (cnc⋆-licensed).
CncLic : TCtx → BCtx → ℕ → Ty → Set
CncLic Ψ Θᵈ j A =
    (Σ Ty λ A₀ → (Ψ ∋ j := A₀) × Reversal≈ Ψ Θᵈ j A A₀)
  ⊎ (Σ Ty λ A′ → (Ψ ∋ j :=x A′) × (starOnly Θᵈ 0 A ≡ true)
                 × SkelEq A A′)

-- index bookkeeping as the conceal block's recursion moves inward
shift-lic : ∀ {Ψ Θᵈ} j Ξ (σ : Substᵗ)
  → (∀ k → k < suc (revs Ξ) → CncLic Ψ Θᵈ (j + k) (σ k))
  → ∀ k → k < revs Ξ → CncLic Ψ Θᵈ (suc j + k) (σ (suc k))
shift-lic {Ψ} {Θᵈ} j Ξ σ hk k lt =
  subst (λ n → CncLic Ψ Θᵈ n (σ (suc k))) (+-suc j k)
        (hk (suc k) (s≤s lt))

shift-tv : ∀ {Ψ : TCtx} j Ξ
  → (∀ k → k < suc (revs Ξ) → Ψ ∋tv (j + k))
  → ∀ k → k < revs Ξ → Ψ ∋tv (suc j + k)
shift-tv {Ψ} j Ξ hv k lt =
  subst (λ n → Ψ ∋tv n) (+-suc j k) (hv (suc k) (s≤s lt))

bwf-cncOfRevs : ∀ {Ψ Δ' Θᵈ} j Ξ
  → (∀ k → k < revs Ξ → CncLic Ψ Θᵈ (j + k) (ρᵇ Ξ k))
  → (∀ k → k < revs Ξ → Δ' ⊢ ρᵇ Ξ k)
  → (∀ k → k < revs Ξ → Ψ ∋tv (j + k))
  → Bwf Ψ Δ' Θᵈ (cncOfRevs j Ξ)
bwf-cncOfRevs j []            hk hw hv = bwf[]
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl A ∷ Ξ) hk hw hv with hk 0 (s≤s z≤n)
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl A ∷ Ξ) hk hw hv
  | inj₁ (A₀ , p , rev) =
  bwf↓ (subst (λ n → Ψ ∋ n := A₀) (+-identityʳ j) p)
       (subst (λ n → Reversal≈ Ψ Θᵈ n A A₀) (+-identityʳ j) rev)
       (hw 0 (s≤s z≤n))
       (bwf-cncOfRevs (suc j) Ξ (shift-lic j Ξ (ρᵇ (rvl A ∷ Ξ)) hk)
         (λ k lt → hw (suc k) (s≤s lt)) (shift-tv j Ξ hv))
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl A ∷ Ξ) hk hw hv
  | inj₂ (A′ , p , so , sk) =
  bwf↓x (subst (λ n → Ψ ∋ n :=x A′) (+-identityʳ j) p) so sk
        (hw 0 (s≤s z≤n))
        (bwf-cncOfRevs (suc j) Ξ (shift-lic j Ξ (ρᵇ (rvl A ∷ Ξ)) hk)
          (λ k lt → hw (suc k) (s≤s lt)) (shift-tv j Ξ hv))
bwf-cncOfRevs {Ψ} {Δ'} {Θᵈ} j (rvl⋆ ∷ Ξ) hk hw hv =
  bwf⋆↓ (subst (λ n → Ψ ∋tv n) (+-identityʳ j) (hv 0 (s≤s z≤n)))
        (bwf-cncOfRevs (suc j) Ξ (shift-lic j Ξ (ρᵇ (rvl⋆ ∷ Ξ)) hk)
          (λ k lt → hw (suc k) (s≤s lt)) (shift-tv j Ξ hv))
bwf-cncOfRevs j (cnc X A ∷ Ξ) hk hw hv = bwf-cncOfRevs j Ξ hk hw hv
bwf-cncOfRevs j (cnc⋆ X ∷ Ξ)  hk hw hv = bwf-cncOfRevs j Ξ hk hw hv

------------------------------------------------------------------------
-- KNOWLEDGE INTERIORS TRANSPORT.  The interior's reveal entries carry the
-- interior reading ⟦A⟧ of each reveal's rep, so ⊢renameᵀ's (env) case must
-- show that those entries move with the renaming.  The chain is:
--   slotAt-ren  → bfree-ren      (the blocked-freeness guard is stable)
--   γcnc-comm   → rawRead-ren    (the reading commutes, at accessible slots)
--   dfree-ren   → dnT-ren        (the telescope-ENTRY guard is stable, and
--                                 the down-shift commutes where it holds)
-- and hence ⟦⟧-ren, revEnts-ren, ∋:=-int.
------------------------------------------------------------------------

slot-dich : ∀ (s : Slot) → (s ≡ ok) ⊎ (s ≡ blk)
slot-dich ok  = inj₁ refl
slot-dich blk = inj₂ refl

isOk-ok : ∀ (s : Slot) → isOk s ≡ true → s ≡ ok
isOk-ok ok  e = refl
isOk-ok blk ()

ok-isOk : ∀ (s : Slot) → s ≡ ok → isOk s ≡ true
ok-isOk ok  e = refl
ok-isOk blk ()

mono-lt-inv : ∀ {ρ} → Mono ρ → ∀ {a b} → ρ a < ρ b → a < b
mono-lt-inv {ρ} mono {a} {b} lt with a <? b
mono-lt-inv {ρ} mono {a} {b} lt | yes p  = p
mono-lt-inv {ρ} mono {a} {b} lt | no ¬p  =
  ⊥-elim (<-irrefl refl
           (≤-trans lt (Mono→≤ mono (≤-pred (≰⇒> ¬p)))))

acc-ren-inv : ∀ {ρ} → Mono ρ → ∀ Θ i
  → (cmax (renᴮ ρ (intRen ρ Θ) Θ) ≤ ρ i)
    ⊎ (isConc (ρ i) (renᴮ ρ (intRen ρ Θ) Θ) ≡ true)
  → (cmax Θ ≤ i) ⊎ (isConc i Θ ≡ true)
acc-ren-inv {ρ} mono Θ i (inj₂ c) =
  inj₂ (isConc-ren-inv mono (intRen ρ Θ) Θ i c)
acc-ren-inv {ρ} mono Θ i (inj₁ le) with cmax-ren mono (intRen ρ Θ) Θ
acc-ren-inv {ρ} mono Θ i (inj₁ le) | cm-0 e e' =
  inj₁ (subst (_≤ i) (sym e) z≤n)
acc-ren-inv {ρ} mono Θ i (inj₁ le) | cm-s X e e' =
  inj₁ (subst (_≤ i) (sym e) (mono-lt-inv mono (subst (_≤ ρ i) e' le)))

slotAt-ren : ∀ {ρ} → Mono ρ → ∀ Θ i
           → slotAt (renᴮ ρ (intRen ρ Θ) Θ) (ρ i) ≡ slotAt Θ i
slotAt-ren {ρ} mono Θ i with slot-dich (slotAt Θ i)
slotAt-ren {ρ} mono Θ i | inj₁ e =
  trans (acc-slotAt (renᴮ ρ (intRen ρ Θ) Θ) (ρ i)
                    (acc-ren mono Θ i (acc-of Θ i e)))
        (sym e)
slotAt-ren {ρ} mono Θ i | inj₂ e
  with slot-dich (slotAt (renᴮ ρ (intRen ρ Θ) Θ) (ρ i))
slotAt-ren {ρ} mono Θ i | inj₂ e | inj₂ b = trans b (sym e)
slotAt-ren {ρ} mono Θ i | inj₂ e | inj₁ o =
  ⊥-elim (ok≢blk
    (trans (sym (acc-slotAt Θ i
                  (acc-ren-inv mono Θ i
                    (acc-of (renᴮ ρ (intRen ρ Θ) Θ) (ρ i) o))))
           e))

bfree-ren : ∀ {ρ} → Mono ρ → ∀ Θ d A
  → bfree (renᴮ ρ (intRen ρ Θ) Θ) d (renameᵗ (liftⁿ d ρ) A)
    ≡ bfree Θ d A
bfree-ren {ρ} mono Θ d (` X) with split d X
bfree-ren {ρ} mono Θ d (` X) | inj₁ lt
  rewrite liftⁿ-lo d ρ X lt | ⌊⌋-of (X <? d) lt = refl
bfree-ren {ρ} mono Θ d (` .(d + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi d ρ i =
  cong₂ _∨_
    (trans (⌊⌋-false ((d + ρ i) <? d) (m+n≮m d (ρ i)))
           (sym (⌊⌋-false ((d + i) <? d) (m+n≮m d i))))
    (trans (cong (λ n → isOk (slotAt (renᴮ ρ (intRen ρ Θ) Θ) n))
                 (m+n∸m≡n d (ρ i)))
      (trans (cong isOk (slotAt-ren mono Θ i))
             (cong (λ n → isOk (slotAt Θ n)) (sym (m+n∸m≡n d i)))))
bfree-ren mono Θ d `ℕ      = refl
bfree-ren mono Θ d `𝔹      = refl
bfree-ren mono Θ d (A ⇒ B) =
  cong₂ _∧_ (bfree-ren mono Θ d A) (bfree-ren mono Θ d B)
bfree-ren mono Θ d (`∀ A)  = bfree-ren mono Θ (suc d) A

∧-true : ∀ (b₁ b₂ : Bool) → (b₁ ∧ b₂) ≡ true
       → (b₁ ≡ true) × (b₂ ≡ true)
∧-true true  true  e  = refl , refl
∧-true true  false ()
∧-true false b₂    ()

⌊⌋-iff : ∀ {P Q : Set} (dp : Dec P) (dq : Dec Q)
       → (P → Q) → (Q → P) → ⌊ dp ⌋ ≡ ⌊ dq ⌋
⌊⌋-iff (yes p) (yes q) f g = refl
⌊⌋-iff (yes p) (no ¬q) f g = ⊥-elim (¬q (f p))
⌊⌋-iff (no ¬p) (yes q) f g = ⊥-elim (¬p (g q))
⌊⌋-iff (no ¬p) (no ¬q) f g = refl

exts-step : ∀ (σ' σ : Substᵗ) g m n → σ' m ≡ renameᵗ g (σ n)
          → extsᵗ σ' (suc m) ≡ renameᵗ (extᵗ g) (extsᵗ σ (suc n))
exts-step σ' σ g m n e =
  trans (cong (renameᵗ suc) e)
    (trans (rename-rename-commute g suc (σ n))
           (sym (rename-rename-commute suc (extᵗ g) (σ n))))

-- substitution congruence up to a renaming, restricted by bfree: the two
-- substitutions need only agree at the slots the type may name
bf-cong : ∀ Θ d (σ' σ : Substᵗ) (f g : ℕ → ℕ) A
  → bfree Θ d A ≡ true
  → (∀ X → X < d → σ' (liftⁿ d f X) ≡ renameᵗ g (σ X))
  → (∀ i → slotAt Θ i ≡ ok
         → σ' (liftⁿ d f (d + i)) ≡ renameᵗ g (σ (d + i)))
  → substᵗ σ' (renameᵗ (liftⁿ d f) A) ≡ renameᵗ g (substᵗ σ A)
bf-cong Θ d σ' σ f g (` X) bf h1 h2 with split d X
bf-cong Θ d σ' σ f g (` X) bf h1 h2 | inj₁ lt = h1 X lt
bf-cong Θ d σ' σ f g (` .(d + i)) bf h1 h2 | inj₂ (i , refl) =
  h2 i (isOk-ok (slotAt Θ i)
         (trans (cong (λ n → isOk (slotAt Θ n)) (sym (m+n∸m≡n d i)))
                (trans (sym (cong (λ b → b ∨ isOk (slotAt Θ ((d + i) ∸ d)))
                                  (⌊⌋-false ((d + i) <? d) (m+n≮m d i))))
                       bf)))
bf-cong Θ d σ' σ f g `ℕ bf h1 h2 = refl
bf-cong Θ d σ' σ f g `𝔹 bf h1 h2 = refl
bf-cong Θ d σ' σ f g (A ⇒ B) bf h1 h2 =
  cong₂ _⇒_ (bf-cong Θ d σ' σ f g A (fst (∧-true _ _ bf)) h1 h2)
            (bf-cong Θ d σ' σ f g B (snd (∧-true _ _ bf)) h1 h2)
  where fst : ∀ {P Q : Set} → P × Q → P
        fst (p , q) = p
        snd : ∀ {P Q : Set} → P × Q → Q
        snd (p , q) = q
bf-cong Θ d σ' σ f g (`∀ A) bf h1 h2 =
  cong `∀ (bf-cong Θ (suc d) (extsᵗ σ') (extsᵗ σ) f (extᵗ g) A bf h1' h2')
  where
    h1' : ∀ X → X < suc d
        → extsᵗ σ' (liftⁿ (suc d) f X) ≡ renameᵗ (extᵗ g) (extsᵗ σ X)
    h1' zero    lt       = refl
    h1' (suc X) (s≤s lt) = exts-step σ' σ g (liftⁿ d f X) X (h1 X lt)
    h2' : ∀ i → slotAt Θ i ≡ ok
        → extsᵗ σ' (liftⁿ (suc d) f (suc d + i))
          ≡ renameᵗ (extᵗ g) (extsᵗ σ (suc d + i))
    h2' i okp = exts-step σ' σ g (liftⁿ d f (d + i)) (d + i) (h2 i okp)

-- the reading commutes with renaming.  Parallel: the rep is an EXTERIOR
-- type, so bf-cong is entered at binder depth 0 and its low case is vacuous.
rawRead-ren : ∀ {ρ} → Mono ρ → ∀ Θ A
  → bfree Θ 0 A ≡ true
  → rawRead (renᴮ ρ (intRen ρ Θ) Θ) (renameᵗ ρ A)
    ≡ renameᵗ (intRen ρ Θ) (rawRead Θ A)
rawRead-ren {ρ} mono Θ A bf =
  bf-cong Θ 0 (rdSub Θ') (rdSub Θ) ρ (intRen ρ Θ) A bf (λ X ()) h2
  where
    Θ' = renᴮ ρ (intRen ρ Θ) Θ
    h2 : ∀ i → slotAt Θ i ≡ ok
       → rdSub Θ' (ρ i) ≡ renameᵗ (intRen ρ Θ) (rdSub Θ i)
    h2 i okp =
      trans (cong (λ r → γcnc r (cmax Θ') Θ' (ρ i))
                  (revs-ren ρ (intRen ρ Θ) Θ))
            (γcnc-comm mono (revs Θ) (cmax Θ) (cmax Θ') Θ i
                       (deep-hyp mono Θ) (acc-of Θ i okp))

dfree-ren : ∀ τ → Mono τ → ∀ j → τ j ≡ j → ∀ b T
  → dfree b (suc j) (renameᵗ (liftⁿ b τ) T) ≡ dfree b (suc j) T
dfree-ren τ mono j hj b (` X) with split b X
dfree-ren τ mono j hj b (` X) | inj₁ lt
  rewrite liftⁿ-lo b τ X lt = refl
dfree-ren τ mono j hj b (` .(b + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi b τ i =
  cong₂ _∨_
    (trans (⌊⌋-false ((b + τ i) <? b) (m+n≮m b (τ i)))
           (sym (⌊⌋-false ((b + i) <? b) (m+n≮m b i))))
    (⌊⌋-iff ((b + suc j) ≤? (b + τ i)) ((b + suc j) ≤? (b + i)) fwd bwd)
  where
    fwd : b + suc j ≤ b + τ i → b + suc j ≤ b + i
    fwd le = +-monoʳ-≤ b
               (mono-lt-inv mono
                 (subst (_< τ i) (sym hj) (+-cancelˡ-≤ b _ _ le)))
    bwd : b + suc j ≤ b + i → b + suc j ≤ b + τ i
    bwd le = +-monoʳ-≤ b
               (subst (_< τ i) hj (mono (+-cancelˡ-≤ b _ _ le)))
dfree-ren τ mono j hj b `ℕ      = refl
dfree-ren τ mono j hj b `𝔹      = refl
dfree-ren τ mono j hj b (T ⇒ U) =
  cong₂ _∧_ (dfree-ren τ mono j hj b T) (dfree-ren τ mono j hj b U)
dfree-ren τ mono j hj b (`∀ T)  = dfree-ren τ mono j hj (suc b) T

dnT-ren : ∀ τ j → τ j ≡ j → ∀ b T → dfree b (suc j) T ≡ true
  → renameᵗ (liftⁿ b (_∸ suc j)) (renameᵗ (liftⁿ b τ) T)
    ≡ renameᵗ (liftⁿ b (restrictRen j τ)) (renameᵗ (liftⁿ b (_∸ suc j)) T)
dnT-ren τ j hj b (` X) df with split b X
dnT-ren τ j hj b (` X) df | inj₁ lt
  rewrite liftⁿ-lo b τ X lt | liftⁿ-lo b (_∸ suc j) X lt
        | liftⁿ-lo b (restrictRen j τ) X lt = refl
dnT-ren τ j hj b (` .(b + i)) df | inj₂ (i , refl)
  rewrite liftⁿ-hi b τ i | liftⁿ-hi b (_∸ suc j) (τ i)
        | liftⁿ-hi b (_∸ suc j) i
        | liftⁿ-hi b (restrictRen j τ) (i ∸ suc j) =
  cong (λ n → ` (b + n)) key
  where
    sj≤i : suc j ≤ i
    sj≤i = +-cancelˡ-≤ b _ _
             (⌊⌋-true ((b + suc j) ≤? (b + i))
               (trans (sym (cong (λ c → c ∨ ⌊ (b + suc j) ≤? (b + i) ⌋)
                                 (⌊⌋-false ((b + i) <? b) (m+n≮m b i))))
                      df))
    key : τ i ∸ suc j ≡ restrictRen j τ (i ∸ suc j)
    key = cong₂ _∸_ (cong τ (sym (m+[n∸m]≡n sj≤i))) (cong suc (sym hj))
dnT-ren τ j hj b `ℕ      df = refl
dnT-ren τ j hj b `𝔹      df = refl
dnT-ren τ j hj b (T ⇒ U) df =
  cong₂ _⇒_ (dnT-ren τ j hj b T (fst (∧-true _ _ df)))
            (dnT-ren τ j hj b U (snd (∧-true _ _ df)))
  where fst : ∀ {P Q : Set} → P × Q → P
        fst (p , q) = p
        snd : ∀ {P Q : Set} → P × Q → Q
        snd (p , q) = q
dnT-ren τ j hj b (`∀ T)  df = cong `∀ (dnT-ren τ j hj (suc b) T df)

------------------------------------------------------------------------
-- The interior ENTRIES transport, and hence the interior's knowledge.
------------------------------------------------------------------------

-- TWO renamings, because the two knowledge forms live at DIFFERENT levels
-- (notes/DualLicenseDesign.md §5): a `rvld` rep is a type over its own tail
-- inside the interior, so it moves by the INTERIOR renaming; an `xrvld`
-- rep is a type over the interior's EXTERIOR — it is the reveal's own
-- stored rep — so it moves by the exterior ρ, exactly as renᴮ moves it.
entRen₂ : (ℕ → ℕ) → (ℕ → ℕ) → TyEntry → TyEntry
entRen₂ ρ f abst      = abst
entRen₂ ρ f (rvld A)  = rvld (renameᵗ f A)
entRen₂ ρ f (xrvld A) = xrvld (renameᵗ ρ A)

ent-if : ∀ (b b' : Bool) (T T' A : Ty) (ρ f : ℕ → ℕ)
       → b' ≡ b → (b ≡ true → T' ≡ renameᵗ f T)
       → (if b' then rvld T' else xrvld (renameᵗ ρ A))
         ≡ entRen₂ ρ f (if b then rvld T else xrvld A)
ent-if true  b' T T' A ρ f e₁ e₂ rewrite e₁ = cong rvld (e₂ refl)
ent-if false b' T T' A ρ f e₁ e₂ rewrite e₁ = refl

⟦⟧-ren : ∀ {ρ} → Mono ρ → ∀ Θ j A → j < revs Θ
  → ⟦ renᴮ ρ (intRen ρ Θ) Θ ⟧ᴴ j (renameᵗ ρ A)
    ≡ entRen₂ ρ (restrictRen j (intRen ρ Θ)) (⟦ Θ ⟧ᴴ j A)
⟦⟧-ren {ρ} mono Θ j A lt with bfree Θ 0 A in eb
⟦⟧-ren {ρ} mono Θ j A lt | false
  rewrite trans (bfree-ren mono Θ 0 A) eb = refl
⟦⟧-ren {ρ} mono Θ j A lt | true
  rewrite trans (bfree-ren mono Θ 0 A) eb
        | rawRead-ren mono Θ A eb =
  ent-if (dfree 0 (suc j) (rawRead Θ A))
         (dfree 0 (suc j) (renameᵗ (intRen ρ Θ) (rawRead Θ A)))
         (dnT (suc j) (rawRead Θ A))
         (dnT (suc j) (renameᵗ (intRen ρ Θ) (rawRead Θ A)))
         A ρ
         (restrictRen j (intRen ρ Θ))
         (dfree-ren (intRen ρ Θ) (Mono-intRen Θ mono) j τj 0
                    (rawRead Θ A))
         (λ df → dnT-ren (intRen ρ Θ) j τj 0 (rawRead Θ A) df)
  where τj : intRen ρ Θ j ≡ j
        τj = liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) j lt

mapEnts : (ℕ → TyEntry → TyEntry) → ℕ → TCtx → TCtx
mapEnts f j []      = []
mapEnts f j (E ∷ Ψ) = f j E ∷ mapEnts f (suc j) Ψ

revEnts-ren : ∀ {ρ} → Mono ρ → ∀ Θ j Ξ → j + revs Ξ ≡ revs Θ
  → revEnts (renᴮ ρ (intRen ρ Θ) Θ) j (renᴮ ρ (intRen ρ Θ) Ξ)
    ≡ mapEnts (λ n → entRen₂ ρ (restrictRen n (intRen ρ Θ))) j
              (revEnts Θ j Ξ)
revEnts-ren mono Θ j []            hj = refl
revEnts-ren {ρ} mono Θ j (rvl A ∷ Ξ) hj =
  cong₂ _∷_ eq-head (revEnts-ren mono Θ (suc j) Ξ hd)
  where
    hd : suc j + revs Ξ ≡ revs Θ
    hd = trans (sym (+-suc j (revs Ξ))) hj
    lt : j < revs Θ
    lt = subst (j <_) hd (m≤m+n (suc j) (revs Ξ))
    eq-head : ⟦ renᴮ ρ (intRen ρ Θ) Θ ⟧ᴴ j (renameᵗ ρ A)
              ≡ entRen₂ ρ (restrictRen j (intRen ρ Θ)) (⟦ Θ ⟧ᴴ j A)
    eq-head = ⟦⟧-ren mono Θ j A lt
revEnts-ren {ρ} mono Θ j (rvl⋆ ∷ Ξ) hj =
  cong (abst ∷_) (revEnts-ren mono Θ (suc j) Ξ hd)
  where
    hd : suc j + revs Ξ ≡ revs Θ
    hd = trans (sym (+-suc j (revs Ξ))) hj
revEnts-ren mono Θ j (cnc X A ∷ Ξ) hj = revEnts-ren mono Θ j Ξ hj
revEnts-ren mono Θ j (cnc⋆ X ∷ Ξ)  hj = revEnts-ren mono Θ j Ξ hj

∋:=-cong : ∀ {Δ : TCtx} {X : ℕ} {A B : Ty} → A ≡ B → Δ ∋ X := A → Δ ∋ X := B
∋:=-cong refl p = p

mapEnts-∋:= : ∀ (ρ : ℕ → ℕ) (g : ℕ → ℕ → ℕ) j (Ψ₀ : TCtx)
    {Γ Γ' : TCtx} {Y B}
  → Y < length Ψ₀ → (Ψ₀ ++ Γ) ∋ Y := B
  → (mapEnts (λ n → entRen₂ ρ (g n)) j Ψ₀ ++ Γ')
      ∋ Y := renameᵗ (g (j + Y)) B
mapEnts-∋:= ρ g j []              () p
mapEnts-∋:= ρ g j (rvld A ∷ Ψ₀)   lt here =
  ∋:=-cong (cong (λ n → renameᵗ (g n) A) (sym (+-identityʳ j))) here
mapEnts-∋:= ρ g j (abst ∷ Ψ₀) {Y = suc Y} {B} (s≤s lt) (skip-abst p) =
  ∋:=-cong (cong (λ n → renameᵗ (g n) B) (sym (+-suc j Y)))
           (skip-abst (mapEnts-∋:= ρ g (suc j) Ψ₀ lt p))
mapEnts-∋:= ρ g j (rvld A ∷ Ψ₀) {Y = suc Y} {B} (s≤s lt) (skip-rvld p) =
  ∋:=-cong (cong (λ n → renameᵗ (g n) B) (sym (+-suc j Y)))
           (skip-rvld (mapEnts-∋:= ρ g (suc j) Ψ₀ lt p))
mapEnts-∋:= ρ g j (xrvld A ∷ Ψ₀) {Y = suc Y} {B} (s≤s lt) (skip-xrvld p) =
  ∋:=-cong (cong (λ n → renameᵗ (g n) B) (sym (+-suc j Y)))
           (skip-xrvld (mapEnts-∋:= ρ g (suc j) Ψ₀ lt p))

-- the same, for the EXTERIOR-READ lookup: its rep moves by the exterior ρ
mapEnts-∋:=x : ∀ (ρ : ℕ → ℕ) (g : ℕ → ℕ → ℕ) j (Ψ₀ : TCtx)
    {Γ Γ' : TCtx} {Y A′}
  → Y < length Ψ₀ → (Ψ₀ ++ Γ) ∋ Y :=x A′
  → (mapEnts (λ n → entRen₂ ρ (g n)) j Ψ₀ ++ Γ') ∋ Y :=x renameᵗ ρ A′
mapEnts-∋:=x ρ g j []               () p
mapEnts-∋:=x ρ g j (xrvld A ∷ Ψ₀)   lt herex     = herex
mapEnts-∋:=x ρ g j (abst ∷ Ψ₀)  {Y = suc Y} (s≤s lt) (skipx p) =
  skipx (mapEnts-∋:=x ρ g (suc j) Ψ₀ lt p)
mapEnts-∋:=x ρ g j (rvld A ∷ Ψ₀) {Y = suc Y} (s≤s lt) (skipx p) =
  skipx (mapEnts-∋:=x ρ g (suc j) Ψ₀ lt p)
mapEnts-∋:=x ρ g j (xrvld A ∷ Ψ₀) {Y = suc Y} (s≤s lt) (skipx p) =
  skipx (mapEnts-∋:=x ρ g (suc j) Ψ₀ lt p)

------------------------------------------------------------------------
-- The exterior part: a knowledge entry deeper than the deepest conceal is
-- an entry of Δ itself, and the induced renaming on the interior's tail is
-- the one the exterior hypothesis provides.
------------------------------------------------------------------------

dropN-∋:= : ∀ c (Δ : TCtx) {Z B} → dropN c Δ ∋ Z := B → Δ ∋ (c + Z) := B
dropN-∋:= zero    Δ            p = p
dropN-∋:= (suc c) []           ()
dropN-∋:= (suc c) (abst ∷ Δ)    p = skip-abst (dropN-∋:= c Δ p)
dropN-∋:= (suc c) (rvld A ∷ Δ)  p = skip-rvld (dropN-∋:= c Δ p)
dropN-∋:= (suc c) (xrvld A ∷ Δ) p = skip-xrvld (dropN-∋:= c Δ p)

dropN-∋:=⁻ : ∀ c (Δ : TCtx) {Z B} → Δ ∋ (c + Z) := B → dropN c Δ ∋ Z := B
dropN-∋:=⁻ zero    Δ            p             = p
dropN-∋:=⁻ (suc c) []           ()
dropN-∋:=⁻ (suc c) (abst ∷ Δ)    (skip-abst p)  = dropN-∋:=⁻ c Δ p
dropN-∋:=⁻ (suc c) (rvld A ∷ Δ)  (skip-rvld p)  = dropN-∋:=⁻ c Δ p
dropN-∋:=⁻ (suc c) (xrvld A ∷ Δ) (skip-xrvld p) = dropN-∋:=⁻ c Δ p

ent-skip:= : ∀ (E : TyEntry) {Δ X A} → Δ ∋ X := A → (E ∷ Δ) ∋ suc X := A
ent-skip:= abst      p = skip-abst p
ent-skip:= (rvld B)  p = skip-rvld p
ent-skip:= (xrvld B) p = skip-xrvld p

ent-tail:= : ∀ (E : TyEntry) {Δ X A} → (E ∷ Δ) ∋ suc X := A → Δ ∋ X := A
ent-tail:= abst      (skip-abst p)  = p
ent-tail:= (rvld B)  (skip-rvld p)  = p
ent-tail:= (xrvld B) (skip-xrvld p) = p

revE-hi:= : ∀ Θ j Ξ {Γ : TCtx} {Z B} → Γ ∋ Z := B
          → (revEnts Θ j Ξ ++ Γ) ∋ (revs Ξ + Z) := B
revE-hi:= Θ j []            p = p
revE-hi:= Θ j (rvl A ∷ Ξ)   p =
  ent-skip:= (⟦ Θ ⟧ᴴ j A) (revE-hi:= Θ (suc j) Ξ p)
revE-hi:= Θ j (rvl⋆ ∷ Ξ)    p = skip-abst (revE-hi:= Θ (suc j) Ξ p)
revE-hi:= Θ j (cnc X A ∷ Ξ) p = revE-hi:= Θ j Ξ p
revE-hi:= Θ j (cnc⋆ X ∷ Ξ)  p = revE-hi:= Θ j Ξ p

revE-hi:=⁻ : ∀ Θ j Ξ {Γ : TCtx} {Z B}
           → (revEnts Θ j Ξ ++ Γ) ∋ (revs Ξ + Z) := B → Γ ∋ Z := B
revE-hi:=⁻ Θ j []            p = p
revE-hi:=⁻ Θ j (rvl A ∷ Ξ)   p =
  revE-hi:=⁻ Θ (suc j) Ξ (ent-tail:= (⟦ Θ ⟧ᴴ j A) p)
revE-hi:=⁻ Θ j (rvl⋆ ∷ Ξ)    p =
  revE-hi:=⁻ Θ (suc j) Ξ (ent-tail:= abst p)
revE-hi:=⁻ Θ j (cnc X A ∷ Ξ) p = revE-hi:=⁻ Θ j Ξ p
revE-hi:=⁻ Θ j (cnc⋆ X ∷ Ξ)  p = revE-hi:=⁻ Θ j Ξ p

∸∸-lemma : ∀ a b n → n ≤ b → (a ∸ n) ∸ suc (b ∸ n) ≡ a ∸ suc b
∸∸-lemma a b n le =
  trans (cong (λ m → (a ∸ n) ∸ m) (sym (+-∸-assoc 1 le)))
    (trans (∸-+-assoc a n (suc b ∸ n))
           (cong (a ∸_) (m+[n∸m]≡n (≤-trans le (n≤1+n b)))))

restrict-deep : ∀ {ρ} → Mono ρ → ∀ c Z k
  → restrictRen Z (deepRen c ρ) k ≡ restrictRen (c + Z) ρ k
restrict-deep mono zero    Z k = refl
restrict-deep {ρ} mono (suc X) Z k =
  trans (cong (λ u → (u ∸ suc (ρ X))
                     ∸ suc (ρ (suc X + Z) ∸ suc (ρ X)))
              (cong ρ idx))
        (∸∸-lemma (ρ (suc (suc X + Z) + k)) (ρ (suc X + Z)) (suc (ρ X)) nb)
  where
    idx : suc X + (suc Z + k) ≡ suc (suc X + Z) + k
    idx = cong suc (trans (+-suc X (Z + k))
                          (cong suc (sym (+-assoc X Z k))))
    nb : suc (ρ X) ≤ ρ (suc X + Z)
    nb = mono (m≤m+n (suc X) Z)

+∸+ : ∀ r x y → (r + x) ∸ (r + y) ≡ x ∸ y
+∸+ r x y =
  trans (sym (∸-+-assoc (r + x) r y)) (cong (_∸ y) (m+n∸m≡n r x))

restrict-int : ∀ {ρ} → Mono ρ → ∀ Θ Z k
  → restrictRen (revs Θ + Z) (intRen ρ Θ) k
    ≡ restrictRen (cmax Θ + Z) ρ k
restrict-int {ρ} mono Θ Z k =
  trans (cong₂ _∸_ (trans (cong (intRen ρ Θ) idx)
                          (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ)
                                    (suc Z + k)))
                   (trans (cong suc (liftⁿ-hi (revs Θ)
                                       (deepRen (cmax Θ) ρ) Z))
                          (sym (+-suc (revs Θ) (deepRen (cmax Θ) ρ Z)))))
    (trans (+∸+ (revs Θ) (deepRen (cmax Θ) ρ (suc Z + k))
                (suc (deepRen (cmax Θ) ρ Z)))
           (restrict-deep mono (cmax Θ) Z k))
  where
    idx : suc (revs Θ + Z) + k ≡ revs Θ + (suc Z + k)
    idx = trans (cong suc (+-assoc (revs Θ) Z k))
                (sym (+-suc (revs Θ) (Z + k)))

∋:=-int : ∀ {ρ Δ Δ'} → Mono ρ
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → ∀ Θ {Y B}
  → intOf Δ Θ ∋ Y := B
  → intOf Δ' (renᴮ ρ (intRen ρ Θ) Θ) ∋ intRen ρ Θ Y
      := renameᵗ (restrictRen Y (intRen ρ Θ)) B
∋:=-int {ρ} {Δ} {Δ'} mono hk Θ {Y} {B} p with split (revs Θ) Y
∋:=-int {ρ} {Δ} {Δ'} mono hk Θ {Y} {B} p | inj₁ lt =
  subst (λ Ψ₀ → (Ψ₀ ++ dropN (cmax Θ') Δ')
                ∋ intRen ρ Θ Y := renameᵗ (restrictRen Y (intRen ρ Θ)) B)
        (sym (revEnts-ren mono Θ 0 Θ refl))
        (subst (λ n → (mapEnts (λ m → entRen₂ ρ (restrictRen m (intRen ρ Θ)))
                               0 (revEnts Θ 0 Θ) ++ dropN (cmax Θ') Δ')
                      ∋ n := renameᵗ (restrictRen Y (intRen ρ Θ)) B)
               (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) Y lt))
               (mapEnts-∋:= ρ (λ n → restrictRen n (intRen ρ Θ)) 0
                            (revEnts Θ 0 Θ)
                            (subst (Y <_) (sym (len-revEnts Θ 0 Θ)) lt) p))
  where Θ' = renᴮ ρ (intRen ρ Θ) Θ
∋:=-int {ρ} {Δ} {Δ'} mono hk Θ {.(revs Θ + Z)} {B} p | inj₂ (Z , refl) =
  subst₂ (λ n C → intOf Δ' Θ' ∋ n := C) idx rep
    (revE-hi:= Θ' 0 Θ'
      (dropN-∋:=⁻ (cmax Θ') Δ'
        (subst (λ n → Δ' ∋ n := renameᵗ (restrictRen (cmax Θ + Z) ρ) B)
               (sym key)
               (hk (dropN-∋:= (cmax Θ) Δ (revE-hi:=⁻ Θ 0 Θ p))))))
  where
    Θ' = renᴮ ρ (intRen ρ Θ) Θ
    idx : revs Θ' + deepRen (cmax Θ) ρ Z ≡ intRen ρ Θ (revs Θ + Z)
    idx = trans (cong (_+ deepRen (cmax Θ) ρ Z)
                      (revs-ren ρ (intRen ρ Θ) Θ))
                (sym (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) Z))
    rep : renameᵗ (restrictRen (cmax Θ + Z) ρ) B
        ≡ renameᵗ (restrictRen (revs Θ + Z) (intRen ρ Θ)) B
    rep = rename-cong (λ k → sym (restrict-int mono Θ Z k)) B
    key : cmax Θ' + deepRen (cmax Θ) ρ Z ≡ ρ (cmax Θ + Z)
    key with cmax-ren mono (intRen ρ Θ) Θ
    key | cm-0 e e′ rewrite e | e′ = refl
    key | cm-s W e e′ rewrite e | e′ =
      m+[n∸m]≡n (mono {W} {suc W + Z} (m≤m+n (suc W) Z))

------------------------------------------------------------------------
-- THE CONGRUENCE TRANSPORTS UNDER THE HYPOTHESES ⊢renameᵀ ALREADY CARRIES
-- (notes/DualLicenseDesign.md §5(ii); UpToProbe §7).  The OPERATOR unfoldᵉ
-- does NOT commute with renaming under those hypotheses (¬UnfRen-hk: an
-- ABSTRACT slot may land on a REVEALED one, and unfolding notices).  The
-- CONGRUENCE does, and with NO NEW TOP-LEVEL HYPOTHESIS: the ABSORBED form
-- UnfRen≈ follows from Mono plus the ∋:= transport `hk` alone.
--
-- The proof is the two-case read-off of unfSub (strong.Unfold's
-- unfSub-dich): a slot that unfolds to ITSELF — abstract, exterior-read, or
-- out of range — makes the equation an identity, and a KNOWLEDGE slot is
-- handed to hk, whose renamed rep is read in the slot's own PREFIX.  The
-- recursion is therefore on the prefix, measured by the context's length.
------------------------------------------------------------------------

len-↓≤ : ∀ (Δ₀ : TCtx) X → length (Δ₀ ↓ X) ≤ length Δ₀
len-↓≤ []              X       = z≤n
len-↓≤ (abst ∷ Δ₁)     zero    = n≤1+n _
len-↓≤ (rvld A ∷ Δ₁)   zero    = n≤1+n _
len-↓≤ (xrvld A ∷ Δ₁)  zero    = n≤1+n _
len-↓≤ (abst ∷ Δ₁)     (suc X) = ≤-trans (len-↓≤ Δ₁ X) (n≤1+n _)
len-↓≤ (rvld A ∷ Δ₁)   (suc X) = ≤-trans (len-↓≤ Δ₁ X) (n≤1+n _)
len-↓≤ (xrvld A ∷ Δ₁)  (suc X) = ≤-trans (len-↓≤ Δ₁ X) (n≤1+n _)

-- a context that HAS a knowledge slot is non-empty, so every prefix of it
-- is strictly shorter
len-↓< : ∀ (Δ₀ : TCtx) {Y B} → Δ₀ ∋ Y := B
       → ∀ X → suc (length (Δ₀ ↓ X)) ≤ length Δ₀
len-↓< (rvld A ∷ Δ₁)  here           zero    = s≤s ≤-refl
len-↓< (rvld A ∷ Δ₁)  here           (suc X) = s≤s (len-↓≤ Δ₁ X)
len-↓< (abst ∷ Δ₁)    (skip-abst q)  zero    = s≤s ≤-refl
len-↓< (abst ∷ Δ₁)    (skip-abst q)  (suc X) = s≤s (len-↓≤ Δ₁ X)
len-↓< (rvld A ∷ Δ₁)  (skip-rvld q)  zero    = s≤s ≤-refl
len-↓< (rvld A ∷ Δ₁)  (skip-rvld q)  (suc X) = s≤s (len-↓≤ Δ₁ X)
len-↓< (xrvld A ∷ Δ₁) (skip-xrvld q) zero    = s≤s ≤-refl
len-↓< (xrvld A ∷ Δ₁) (skip-xrvld q) (suc X) = s≤s (len-↓≤ Δ₁ X)

know-nonempty : ∀ {Δ₀ : TCtx} {Y B} → length Δ₀ ≤ 0 → Δ₀ ∋ Y := B → ⊥
know-nonempty {rvld A ∷ Δ₁}  ()  here
know-nonempty {abst ∷ Δ₁}    ()  (skip-abst q)
know-nonempty {rvld A ∷ Δ₁}  ()  (skip-rvld q)
know-nonempty {xrvld A ∷ Δ₁} ()  (skip-xrvld q)

-- the prefix lift commutes with renaming (this is Reversal-ren's second
-- half, factored out)
upRep-ren : ∀ {ρ} → Mono ρ → ∀ X A₀
  → renameᵗ ρ (upRep X A₀) ≡ upRep (ρ X) (renameᵗ (restrictRen X ρ) A₀)
upRep-ren {ρ} mono X A₀ =
  trans (rename-rename-commute (λ i → suc X + i) ρ A₀)
    (trans (rename-cong eq A₀)
           (sym (rename-rename-commute (restrictRen X ρ)
                                       (λ i → suc (ρ X) + i) A₀)))
  where
    eq : ∀ i → ρ (suc X + i) ≡ suc (ρ X) + restrictRen X ρ i
    eq i = sym (m+[n∸m]≡n (mono {X} {suc X + i} (m≤m+n (suc X) i)))

-- and the read-back commutes with renaming (Reversal-ren's first half)
outRead-ren : ∀ {ρ} → Mono ρ → ∀ Θ A
  → outRead (renᴮ ρ (intRen ρ Θ) Θ) (renameᵗ (intRen ρ Θ) A)
    ≡ renameᵗ ρ (outRead Θ A)
outRead-ren {ρ} mono Θ A =
  trans (rename-subst-commute (intRen ρ Θ)
                              (outSub (renᴮ ρ (intRen ρ Θ) Θ)) A)
    (trans (subst-cong (λ Y → outSub-ren mono Θ Y) A)
           (sym (rename-subst ρ (outSub Θ) A)))

-- the ∋:= transport, restricted to a slot's own prefix
hk-↓ : ∀ {ρ} {Δ Δ' : TCtx} → Mono ρ
  → (∀ {Y A₀} → Δ ∋ Y := A₀ → Δ' ∋ ρ Y := renameᵗ (restrictRen Y ρ) A₀)
  → ∀ X {Z C} → (Δ ↓ X) ∋ Z := C
  → (Δ' ↓ ρ X) ∋ restrictRen X ρ Z
      := renameᵗ (restrictRen Z (restrictRen X ρ)) C
hk-↓ {ρ} {Δ} {Δ'} mono hk X {Z} {C} q =
  subst₂ (λ Ψ T → Ψ ∋ restrictRen X ρ Z := T)
         (dropN-↓ Δ' (ρ X))
         (rename-cong (λ k → sym (restrict-deep mono (suc X) Z k)) C)
    (dropN-∋:=⁻ (suc (ρ X)) Δ'
      (subst (λ n → Δ' ∋ n := renameᵗ (restrictRen (suc X + Z) ρ) C)
             (sym key)
             (hk (dropN-∋:= (suc X) Δ
                   (subst (λ Ψ → Ψ ∋ Z := C) (sym (dropN-↓ Δ X)) q)))))
  where
    key : suc (ρ X) + restrictRen X ρ Z ≡ ρ (suc X + Z)
    key = m+[n∸m]≡n (mono {X} {suc X + Z} (m≤m+n (suc X) Z))

UnfRen≈-hk : ∀ n {ρ} {Δ Δ' : TCtx} → length Δ ≤ n → Mono ρ
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → UnfRen≈ ρ Δ Δ'
UnfRen≈-hk zero {ρ} {Δ} {Δ'} le mono hk X with unfSub-dich Δ X
UnfRen≈-hk zero {ρ} {Δ} {Δ'} le mono hk X | inj₁ e =
  UnfRen≈-fix ρ Δ Δ' X e
UnfRen≈-hk zero {ρ} {Δ} {Δ'} le mono hk X | inj₂ (B , p , e) =
  ⊥-elim (know-nonempty le p)
UnfRen≈-hk (suc n) {ρ} {Δ} {Δ'} le mono hk X with unfSub-dich Δ X
UnfRen≈-hk (suc n) {ρ} {Δ} {Δ'} le mono hk X | inj₁ e =
  UnfRen≈-fix ρ Δ Δ' X e
UnfRen≈-hk (suc n) {ρ} {Δ} {Δ'} le mono hk X | inj₂ (B , p , e) =
  trans (cong (λ T → unfoldᵉ Δ' (renameᵗ ρ T)) e)
    (trans (cong (unfoldᵉ Δ') (upRep-ren mono X (unfoldᵉ (Δ ↓ X) B)))
      (trans (unf-up Δ' (ρ X)
               (renameᵗ (restrictRen X ρ) (unfoldᵉ (Δ ↓ X) B)))
        (trans (cong (upᵉ (ρ X))
                 (unf-ren-step (Δ ↓ X) (Δ' ↓ ρ X) ih B))
               (sym (unfSub-know Δ' (hk p))))))
  where
    ih : UnfRen≈ (restrictRen X ρ) (Δ ↓ X) (Δ' ↓ ρ X)
    ih = UnfRen≈-hk n (≤-pred (≤-trans (len-↓< Δ p X) le))
                      (Mono-restrictRen X mono) (hk-↓ mono hk X)

-- THE REVERSAL PREMISE TRANSPORTS, UP TO ≈.  Both sides move by the
-- EXTERIOR ρ (outRead-ren / upRep-ren), and the congruence follows them
-- (≈-ren) with the absorbed hypothesis derived just above.
Reversal≈-ren : ∀ {ρ} {Δ Δ' : TCtx} → Mono ρ
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → ∀ Θ X A A₀ → Reversal≈ Δ Θ X A A₀
  → Reversal≈ Δ' (renᴮ ρ (intRen ρ Θ) Θ) (ρ X)
              (renameᵗ (intRen ρ Θ) A) (renameᵗ (restrictRen X ρ) A₀)
Reversal≈-ren {ρ} {Δ} {Δ'} mono hk Θ X A A₀ rev =
  subst₂ (λ S T → S ≈Δ̄⟨ Δ' ⟩ T)
         (sym (outRead-ren mono Θ A))
         (upRep-ren mono X A₀)
         (≈-ren Δ Δ' (UnfRen≈-hk (length Δ) ≤-refl mono hk) rev)

-- the starOnly premise transports for free: it mentions NO context, and
-- renᴮ keeps every rvl⋆ in place while intRen is the identity below revs Θ
-- (so it fixes exactly the variables starOnly accepts).
revStar-ren : ∀ ρ ir Θ i → revStar (renᴮ ρ ir Θ) i ≡ revStar Θ i
revStar-ren ρ ir []            i       = refl
revStar-ren ρ ir (rvl A ∷ Θ)   zero    = refl
revStar-ren ρ ir (rvl A ∷ Θ)   (suc i) = revStar-ren ρ ir Θ i
revStar-ren ρ ir (rvl⋆ ∷ Θ)    zero    = refl
revStar-ren ρ ir (rvl⋆ ∷ Θ)    (suc i) = revStar-ren ρ ir Θ i
revStar-ren ρ ir (cnc X A ∷ Θ) i       = revStar-ren ρ ir Θ i
revStar-ren ρ ir (cnc⋆ X ∷ Θ)  i       = revStar-ren ρ ir Θ i

revStar-hi : ∀ Θ i → revs Θ ≤ i → revStar Θ i ≡ false
revStar-hi []            i       le       = refl
revStar-hi (rvl A ∷ Θ)   zero    ()
revStar-hi (rvl A ∷ Θ)   (suc i) (s≤s le) = revStar-hi Θ i le
revStar-hi (rvl⋆ ∷ Θ)    zero    ()
revStar-hi (rvl⋆ ∷ Θ)    (suc i) (s≤s le) = revStar-hi Θ i le
revStar-hi (cnc X A ∷ Θ) i       le       = revStar-hi Θ i le
revStar-hi (cnc⋆ X ∷ Θ)  i       le       = revStar-hi Θ i le

starOnly-ren : ∀ {ρ} Θ d A → starOnly (renᴮ ρ (intRen ρ Θ) Θ) d
                                      (renameᵗ (liftⁿ d (intRen ρ Θ)) A)
                             ≡ starOnly Θ d A
starOnly-ren {ρ} Θ d (` X) with split d X
starOnly-ren {ρ} Θ d (` X) | inj₁ lt
  rewrite liftⁿ-lo d (intRen ρ Θ) X lt
        | ⌊⌋-of (X <? d) lt = refl
starOnly-ren {ρ} Θ d (` .(d + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi d (intRen ρ Θ) i
        | ⌊⌋-false ((d + intRen ρ Θ i) <? d) (m+n≮m d (intRen ρ Θ i))
        | ⌊⌋-false ((d + i) <? d) (m+n≮m d i)
        | m+n∸m≡n d (intRen ρ Θ i)
        | m+n∸m≡n d i
        | revStar-ren ρ (intRen ρ Θ) Θ (intRen ρ Θ i) = star-i
  where
    star-i : revStar Θ (intRen ρ Θ i) ≡ revStar Θ i
    star-i with split (revs Θ) i
    star-i | inj₁ lt
      rewrite liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) i lt = refl
    star-i | inj₂ (k , refl)
      rewrite liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) k =
      trans (revStar-hi Θ (revs Θ + deepRen (cmax Θ) ρ k)
                        (m≤m+n (revs Θ) (deepRen (cmax Θ) ρ k)))
            (sym (revStar-hi Θ (revs Θ + k) (m≤m+n (revs Θ) k)))
starOnly-ren Θ d `ℕ      = refl
starOnly-ren Θ d `𝔹      = refl
starOnly-ren Θ d (A ⇒ B) =
  cong₂ _∧_ (starOnly-ren Θ d A) (starOnly-ren Θ d B)
starOnly-ren {ρ} Θ d (`∀ A) = starOnly-ren Θ (suc d) A

------------------------------------------------------------------------
-- THE x-TRANSPORT HYPOTHESIS (notes/D1Probe.agda §7.1; notes/DECISIONS.md's
-- "D1 PROBE VERDICT").  The repaired (bwf-↓x) compares the conceal's rep
-- with the RECORDED one by skeleton, so the x-transport must promise more
-- than mere EXISTENCE of the target's rep: it must say the target's rep has
-- the source rep's SKELETON.  That is strictly weaker than
-- notes/DualLicenseDesign.md §5(i)'s rejected XRen — it does not say WHICH
-- renaming moved the rep, only that renaming is what moved it — and both
-- live instances already satisfy it (hx-suc / SkelX-suc for the weakening,
-- SkelX-mv for the (env) recursion's reveal block).
------------------------------------------------------------------------

SkelX : Renameᵗ → TCtx → TCtx → Set
SkelX ρ Δ Δ' = ∀ {X A′} → Δ ∋ X :=x A′
             → Σ Ty λ A″ → (Δ' ∋ ρ X :=x A″) × SkelEq A′ A″

-- instance 2: the (env) recursion's REVEAL block — the one branch where the
-- rep genuinely MOVES, by the EXTERIOR ρ (the slot moves by the interior
-- renaming, which is why the index is left free here)
SkelX-mv : ∀ (ρ : Renameᵗ) {Δ' : TCtx} {Y} A′
         → Δ' ∋ Y :=x renameᵗ ρ A′
         → Σ Ty λ A″ → (Δ' ∋ Y :=x A″) × SkelEq A′ A″
SkelX-mv ρ A′ q = renameᵗ ρ A′ , q , skel-renʳ ρ A′

------------------------------------------------------------------------
-- Boundary well-formedness transports.  The reveal premise lives over the
-- PLAIN exterior, so it renames by ρ itself; the ORDINARY conceal premise
-- needs both the exterior's knowledge transport (∋:=) and Reversal≈-ren;
-- the x-clause needs the x-LOOKUP in its SkelX form (starOnly is
-- context-free and rides starOnly-ren, and the skeleton premise rides
-- skel-renˡ against SkelX's own witness — hypothesis-free, which is the
-- whole point of comparing skeletons); and a cnc⋆ rides the ∋tv transport
-- alone.
------------------------------------------------------------------------

bwf-ren : ∀ {ρ Δ Δ' Ψ Ψ' Θ Ξ} → Mono ρ
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X)
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → SkelX ρ Δ Δ'
  → (∀ {Y} → Ψ ∋tv Y → Ψ' ∋tv intRen ρ Θ Y)
  → Bwf Δ Ψ Θ Ξ
  → Bwf Δ' Ψ' (renᴮ ρ (intRen ρ Θ) Θ) (renᴮ ρ (intRen ρ Θ) Ξ)
bwf-ren mono h hk hx hi bwf[] = bwf[]
bwf-ren {ρ} {Θ = Θ} mono h hk hx hi (bwf↑ {A} {Ξ} wfA b) =
  bwf↑ (wf-ren h wfA) (bwf-ren mono h hk hx hi b)
bwf-ren mono h hk hx hi (bwf⋆ b) = bwf⋆ (bwf-ren mono h hk hx hi b)
bwf-ren {ρ} {Θ = Θ} mono h hk hx hi (bwf↓ {X} {A} {A₀} p rev wfA b) =
  bwf↓ (hk p) (Reversal≈-ren mono hk Θ X A A₀ rev)
       (wf-ren hi wfA) (bwf-ren mono h hk hx hi b)
bwf-ren {ρ} {Θ = Θ} mono h hk hx hi (bwf↓x {X} {A} p so sk wfA b) =
  bwf↓x (proj₁ (proj₂ (hx p)))
        (trans (starOnly-ren Θ 0 A) so)
        (skel-renˡ (intRen ρ Θ) (skel-trans sk (proj₂ (proj₂ (hx p)))))
        (wf-ren hi wfA) (bwf-ren mono h hk hx hi b)
bwf-ren mono h hk hx hi (bwf⋆↓ p b) =
  bwf⋆↓ (h p) (bwf-ren mono h hk hx hi b)


------------------------------------------------------------------------
-- The EXTERIOR-READ lookup transports too, and — this is the one place the
-- two knowledge forms part company — its rep moves by the EXTERIOR ρ, not
-- by the interior renaming (notes/DualLicenseDesign.md §5; the shape of
-- DualLicenseProbe's XRen).  In the reveal block that is exactly what
-- renᴮ does to the reveal's stored rep; in the kept tail it is what the
-- exterior hypothesis supplies.  Both branches deliver the SkelEq witness
-- (bwf-↓x's skeleton premise): in the reveal block the rep moved by a
-- renaming (SkelX-mv), and in the tail the hypothesis hands its own.
------------------------------------------------------------------------

dropN-∋:=x : ∀ c (Δ : TCtx) {Z B} → dropN c Δ ∋ Z :=x B → Δ ∋ (c + Z) :=x B
dropN-∋:=x zero    Δ       p = p
dropN-∋:=x (suc c) []      ()
dropN-∋:=x (suc c) (E ∷ Δ) p = skipx (dropN-∋:=x c Δ p)

dropN-∋:=x⁻ : ∀ c (Δ : TCtx) {Z B} → Δ ∋ (c + Z) :=x B → dropN c Δ ∋ Z :=x B
dropN-∋:=x⁻ zero    Δ       p         = p
dropN-∋:=x⁻ (suc c) []      ()
dropN-∋:=x⁻ (suc c) (E ∷ Δ) (skipx p) = dropN-∋:=x⁻ c Δ p

revE-hi:=x : ∀ Θ j Ξ {Γ : TCtx} {Z B} → Γ ∋ Z :=x B
           → (revEnts Θ j Ξ ++ Γ) ∋ (revs Ξ + Z) :=x B
revE-hi:=x Θ j []            p = p
revE-hi:=x Θ j (rvl A ∷ Ξ)   p = skipx (revE-hi:=x Θ (suc j) Ξ p)
revE-hi:=x Θ j (rvl⋆ ∷ Ξ)    p = skipx (revE-hi:=x Θ (suc j) Ξ p)
revE-hi:=x Θ j (cnc X A ∷ Ξ) p = revE-hi:=x Θ j Ξ p
revE-hi:=x Θ j (cnc⋆ X ∷ Ξ)  p = revE-hi:=x Θ j Ξ p

revE-hi:=x⁻ : ∀ Θ j Ξ {Γ : TCtx} {Z B}
            → (revEnts Θ j Ξ ++ Γ) ∋ (revs Ξ + Z) :=x B → Γ ∋ Z :=x B
revE-hi:=x⁻ Θ j []            p         = p
revE-hi:=x⁻ Θ j (rvl A ∷ Ξ)   (skipx p) = revE-hi:=x⁻ Θ (suc j) Ξ p
revE-hi:=x⁻ Θ j (rvl⋆ ∷ Ξ)    (skipx p) = revE-hi:=x⁻ Θ (suc j) Ξ p
revE-hi:=x⁻ Θ j (cnc X A ∷ Ξ) p         = revE-hi:=x⁻ Θ j Ξ p
revE-hi:=x⁻ Θ j (cnc⋆ X ∷ Ξ)  p         = revE-hi:=x⁻ Θ j Ξ p

∋:=x-int : ∀ {ρ Δ Δ'} → Mono ρ → SkelX ρ Δ Δ'
  → ∀ Θ {Y A′}
  → intOf Δ Θ ∋ Y :=x A′
  → Σ Ty λ A″ → (intOf Δ' (renᴮ ρ (intRen ρ Θ) Θ) ∋ intRen ρ Θ Y :=x A″)
                × SkelEq A′ A″
∋:=x-int {ρ} {Δ} {Δ'} mono hx Θ {Y} {A′} p with split (revs Θ) Y
∋:=x-int {ρ} {Δ} {Δ'} mono hx Θ {Y} {A′} p | inj₁ lt =
  SkelX-mv ρ A′
  (subst (λ Ψ₀ → (Ψ₀ ++ dropN (cmax Θ') Δ')
                 ∋ intRen ρ Θ Y :=x renameᵗ ρ A′)
         (sym (revEnts-ren mono Θ 0 Θ refl))
         (subst (λ n → (mapEnts (λ m → entRen₂ ρ (restrictRen m (intRen ρ Θ)))
                                0 (revEnts Θ 0 Θ) ++ dropN (cmax Θ') Δ')
                       ∋ n :=x renameᵗ ρ A′)
                (sym (liftⁿ-lo (revs Θ) (deepRen (cmax Θ) ρ) Y lt))
                (mapEnts-∋:=x ρ (λ n → restrictRen n (intRen ρ Θ)) 0
                              (revEnts Θ 0 Θ)
                              (subst (Y <_) (sym (len-revEnts Θ 0 Θ)) lt) p)))
  where Θ' = renᴮ ρ (intRen ρ Θ) Θ
∋:=x-int {ρ} {Δ} {Δ'} mono hx Θ {.(revs Θ + Z)} {A′} p | inj₂ (Z , refl)
  with hx (dropN-∋:=x (cmax Θ) Δ (revE-hi:=x⁻ Θ 0 Θ p))
∋:=x-int {ρ} {Δ} {Δ'} mono hx Θ {.(revs Θ + Z)} {A′} p | inj₂ (Z , refl)
  | A″ , q , sq =
  A″ ,
  subst (λ n → intOf Δ' Θ' ∋ n :=x A″) idx
    (revE-hi:=x Θ' 0 Θ'
      (dropN-∋:=x⁻ (cmax Θ') Δ'
        (subst (λ n → Δ' ∋ n :=x A″) (sym key) q))) ,
  sq
  where
    Θ' = renᴮ ρ (intRen ρ Θ) Θ
    idx : revs Θ' + deepRen (cmax Θ) ρ Z ≡ intRen ρ Θ (revs Θ + Z)
    idx = trans (cong (_+ deepRen (cmax Θ) ρ Z)
                      (revs-ren ρ (intRen ρ Θ) Θ))
                (sym (liftⁿ-hi (revs Θ) (deepRen (cmax Θ) ρ) Z))
    key : cmax Θ' + deepRen (cmax Θ) ρ Z ≡ ρ (cmax Θ + Z)
    key with cmax-ren mono (intRen ρ Θ) Θ
    key | cm-0 e e′ rewrite e | e′ = refl
    key | cm-s W e e′ rewrite e | e′ =
      m+[n∸m]≡n (mono {W} {suc W + Z} (m≤m+n (suc W) Z))

------------------------------------------------------------------------
-- Type-variable renaming preserves typing.
--
-- ρ must be MONOTONE, not merely lookup-preserving: boundary renaming
-- depends on index order through cmax / restrictRen (a non-monotone ρ that
-- permutes indices could shrink a conceal's interior and strand a
-- variable).  And, since the reversal premise reads the exterior's
-- KNOWLEDGE, ρ must also transport ∋:= — the third hypothesis, which the
-- interior-form rework identified: it holds at `suc` because
-- restrictRen X suc is pointwise the identity, and it extends under a Λ
-- because restrictRen (suc X) (extᵗ ρ) is pointwise restrictRen X ρ.
------------------------------------------------------------------------

hk-ext : ∀ {ρ Δ Δ'}
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → ∀ {X A₀} → (abst ∷ Δ) ∋ X := A₀
  → (abst ∷ Δ') ∋ extᵗ ρ X := renameᵗ (restrictRen X (extᵗ ρ)) A₀
hk-ext hk (skip-abst p) = skip-abst (hk p)

hx-ext : ∀ {ρ} {Δ Δ' : TCtx} → SkelX ρ Δ Δ'
       → SkelX (extᵗ ρ) (abst ∷ Δ) (abst ∷ Δ')
hx-ext hx (skipx p) with hx p
hx-ext hx (skipx p) | A″ , q , sq = A″ , skipx q , sq

⊢renameᵀ : ∀ {ρ Δ Δ' Γₜ M A}
  → (∀ {X} → Δ ∋tv X → Δ' ∋tv ρ X) → Mono ρ
  → (∀ {X A₀} → Δ ∋ X := A₀ → Δ' ∋ ρ X := renameᵗ (restrictRen X ρ) A₀)
  → SkelX ρ Δ Δ'
  → Δ ∣ Γₜ ⊢ M ⦂ A
  → Δ' ∣ map (renameᵗ ρ) Γₜ ⊢ renameᵀ ρ M ⦂ renameᵗ ρ A
⊢renameᵀ h mono hk hx (⊢` p)      = ⊢` (∋-map p)
⊢renameᵀ h mono hk hx ⊢$          = ⊢$
⊢renameᵀ h mono hk hx (⊢ƛ wfA ⊢N) =
  ⊢ƛ (wf-ren h wfA) (⊢renameᵀ h mono hk hx ⊢N)
⊢renameᵀ h mono hk hx (⊢· ⊢L ⊢M)  =
  ⊢· (⊢renameᵀ h mono hk hx ⊢L) (⊢renameᵀ h mono hk hx ⊢M)
⊢renameᵀ h mono hk hx (⊢Λ {Γₜ = Γₜ} ⊢N) =
  ⊢Λ (subst (λ Γ' → _ ∣ Γ' ⊢ _ ⦂ _) (⤊-ren Γₜ)
            (⊢renameᵀ (ext-h h) (Mono-extᵗ mono) (hk-ext hk)
                      (hx-ext hx) ⊢N))
⊢renameᵀ {ρ} h mono hk hx (⊢·[] {L = L} {B = B} {A = A} ⊢L wfA) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ ρ L
                     ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ] ⦂ T)
        (sym (rename-[]ᵗ-commute ρ B A))
    (⊢·[] (⊢renameᵀ h mono hk hx ⊢L) (wf-ren h wfA))
⊢renameᵀ {ρ} h mono hk hx (env {Θ = Θ} {B₀ = B₀} {M = M} bwf sc ⊢M) =
  subst (λ T → _ ∣ _ ⊢ renameᵀ (intRen ρ Θ) M
                       ⟪ renᴮ ρ (intRen ρ Θ) Θ
                       , renameᵗ (liftⁿ (revs Θ) ρ) B₀ ⟫ ⦂ T)
        (C-ext ρ (intRen ρ Θ) Θ B₀)
    (env (bwf-ren mono h hk hx (h-int h mono Θ) bwf)
         (sc-ren h mono Θ sc)
         (subst (λ T → _ ∣ [] ⊢ renameᵀ (intRen ρ Θ) M ⦂ T)
                (sym (C-int mono Θ sc))
                (⊢renameᵀ (h-int h mono Θ) (Mono-intRen Θ mono)
                          (∋:=-int mono hk Θ)
                          (∋:=x-int mono hx Θ) ⊢M)))

-- the hypotheses really are met by the weakening ⇑ᵀ uses
Mono-suc : Mono suc
Mono-suc lt = s≤s lt

-- instance 1: the weakening ⇑ᵀ uses.  It carries the entry across VERBATIM,
-- so the skeleton premise is skel-refl — the strengthening is free.
hx-suc : ∀ {Δ : TCtx} {E X A′} → Δ ∋ X :=x A′
       → Σ Ty λ A″ → ((E ∷ Δ) ∋ suc X :=x A″) × SkelEq A′ A″
hx-suc {A′ = A′} p = A′ , skipx p , skel-refl A′

SkelX-suc : ∀ {Δ : TCtx} {E} → SkelX suc Δ (E ∷ Δ)
SkelX-suc = hx-suc

hk-suc : ∀ {Δ : TCtx} {E X A₀} → Δ ∋ X := A₀
       → (E ∷ Δ) ∋ suc X := renameᵗ (restrictRen X suc) A₀
hk-suc {E = E} {X} {A₀} p =
  ent-skip:= E (∋:=-cong (sym (trans (rename-cong (m+n∸m≡n X) A₀)
                                     (rename-id A₀))) p)
  where
    rename-id : ∀ (T : Ty) → renameᵗ (λ i → i) T ≡ T
    rename-id (` X') = refl
    rename-id `ℕ     = refl
    rename-id `𝔹     = refl
    rename-id (T ⇒ U) = cong₂ _⇒_ (rename-id T) (rename-id U)
    rename-id (`∀ T)  =
      cong `∀ (trans (rename-cong ext-id T) (rename-id T))
      where ext-id : ∀ i → extᵗ (λ n → n) i ≡ i
            ext-id zero    = refl
            ext-id (suc i) = refl

------------------------------------------------------------------------
-- THE ONE-SLOT WEAKENING ⊢⇑ᵀ, and the substitution identity TyPeel needs.
--
-- TyPeel's inner type application lives in the interior of the SHIFTED
-- boundary, which is the old interior with ONE entry pushed on top
-- (intOf-shift).  The entry's flavour is not known statically — it is
-- ⟦ rvl A ∷ shiftReps Θ ⟧ᴴ 0 A — so the two lookup facts are stated for an
-- ARBITRARY entry, exactly as ent-skip:= already is.
------------------------------------------------------------------------

ent-here-tv : ∀ (E : TyEntry) {Δ : TCtx} → (E ∷ Δ) ∋tv 0
ent-here-tv abst      = here-abst
ent-here-tv (rvld B₃) = here-rvld
ent-here-tv (xrvld B₃) = here-xrvld

ent-skip-tv : ∀ (E : TyEntry) {Δ : TCtx} {X} → Δ ∋tv X → (E ∷ Δ) ∋tv suc X
ent-skip-tv abst       p = skip-abst p
ent-skip-tv (rvld B₃)  p = skip-rvld p
ent-skip-tv (xrvld B₃) p = skip-xrvld p

-- ⇑ᵀ is a pure WEAKENING: the entry crosses verbatim, so the skeleton
-- premise is skel-refl and the knowledge premise is hk-suc.
⊢⇑ᵀ : ∀ {Δ : TCtx} {E M A} → Δ ∣ [] ⊢ M ⦂ A → (E ∷ Δ) ∣ [] ⊢ ⇑ᵀ M ⦂ ⇑ᵗ A
⊢⇑ᵀ {E = E} ⊢M = ⊢renameᵀ (ent-skip-tv E) Mono-suc hk-suc SkelX-suc ⊢M

-- a renaming undone by a substitution, pointwise ⇒ on the nose
ren-sub-id : ∀ (ρ : Renameᵗ) (σ : Substᵗ) → (∀ X → σ (ρ X) ≡ ` X)
           → ∀ T → substᵗ σ (renameᵗ ρ T) ≡ T
ren-sub-id ρ σ h (` X)   = h X
ren-sub-id ρ σ h `ℕ      = refl
ren-sub-id ρ σ h `𝔹      = refl
ren-sub-id ρ σ h (T ⇒ U) =
  cong₂ _⇒_ (ren-sub-id ρ σ h T) (ren-sub-id ρ σ h U)
ren-sub-id ρ σ h (`∀ T)  = cong `∀ (ren-sub-id (extᵗ ρ) (extsᵗ σ) h′ T)
  where
    h′ : ∀ X → extsᵗ σ (extᵗ ρ X) ≡ ` X
    h′ zero    = refl
    h′ (suc X) = cong ⇑ᵗ (h X)

-- INSTANTIATING AT THE FRESH VARIABLE UNDOES THE WEAKENING.  This is what
-- makes TyPeel's inner type application type-neutral: the ∀-body is the
-- weakened interior face, and applying it to ` 0 gives that face back.
peel-tyarg : ∀ T → (renameᵗ (extᵗ suc) T) [ ` 0 ]ᵗ ≡ T
peel-tyarg = ren-sub-id (extᵗ suc) (singleTyEnv (` 0)) h
  where
    h : ∀ X → singleTyEnv (` 0) (extᵗ suc X) ≡ ` X
    h zero    = refl
    h (suc X) = refl

------------------------------------------------------------------------
-- The interior of the SHIFTED boundary.  Every reveal of Θ keeps its rep
-- and moves one slot down, and its interior reading moves with it: the
-- conceal reps shift by suc (γcnc-shift) and the entry's own down-shift
-- absorbs it, so the entries are UNCHANGED.  No accessibility condition is
-- needed here — unlike renaming, the shift agrees at every slot.
------------------------------------------------------------------------

bfree-shift : ∀ A Θ d A₁
  → bfree (rvl A ∷ shiftReps Θ) d A₁ ≡ bfree Θ d A₁
bfree-shift A Θ d (` X)   =
  cong (λ s → ⌊ X <? d ⌋ ∨ isOk s) (slotAt-shift A Θ (X ∸ d))
bfree-shift A Θ d `ℕ      = refl
bfree-shift A Θ d `𝔹      = refl
bfree-shift A Θ d (B ⇒ C) =
  cong₂ _∧_ (bfree-shift A Θ d B) (bfree-shift A Θ d C)
bfree-shift A Θ d (`∀ B)  = bfree-shift A Θ (suc d) B

rdSub-shift : ∀ A Θ k
  → rdSub (rvl A ∷ shiftReps Θ) k ≡ renameᵗ suc (rdSub Θ k)
rdSub-shift A Θ k =
  trans (cong₂ (λ r c → γcnc r c (shiftReps Θ) k)
               (cong suc (revs-shiftReps Θ)) (cmax-shiftReps Θ))
        (γcnc-shift (revs Θ) (cmax Θ) Θ k)

rawRead-shift : ∀ A Θ A₁
  → rawRead (rvl A ∷ shiftReps Θ) A₁ ≡ renameᵗ suc (rawRead Θ A₁)
rawRead-shift A Θ A₁ =
  trans (subst-cong (rdSub-shift A Θ) A₁)
        (sym (rename-subst suc (rdSub Θ) A₁))

dfree-shift : ∀ j b T
  → dfree b (suc (suc j)) (renameᵗ (liftⁿ b suc) T) ≡ dfree b (suc j) T
dfree-shift j b (` X) with split b X
dfree-shift j b (` X) | inj₁ lt
  rewrite liftⁿ-lo b suc X lt | ⌊⌋-of (X <? b) lt = refl
dfree-shift j b (` .(b + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi b suc i =
  cong₂ _∨_
    (trans (⌊⌋-false ((b + suc i) <? b) (m+n≮m b (suc i)))
           (sym (⌊⌋-false ((b + i) <? b) (m+n≮m b i))))
    (⌊⌋-iff ((b + suc (suc j)) ≤? (b + suc i))
            ((b + suc j) ≤? (b + i)) fwd bwd)
  where
    fwd : b + suc (suc j) ≤ b + suc i → b + suc j ≤ b + i
    fwd le = +-monoʳ-≤ b (≤-pred (+-cancelˡ-≤ b _ _ le))
    bwd : b + suc j ≤ b + i → b + suc (suc j) ≤ b + suc i
    bwd le = +-monoʳ-≤ b (s≤s (+-cancelˡ-≤ b _ _ le))
dfree-shift j b `ℕ      = refl
dfree-shift j b `𝔹      = refl
dfree-shift j b (T ⇒ U) =
  cong₂ _∧_ (dfree-shift j b T) (dfree-shift j b U)
dfree-shift j b (`∀ T)  = dfree-shift j (suc b) T

dnT-shift : ∀ j b T
  → renameᵗ (liftⁿ b (_∸ suc (suc j))) (renameᵗ (liftⁿ b suc) T)
    ≡ renameᵗ (liftⁿ b (_∸ suc j)) T
dnT-shift j b (` X) with split b X
dnT-shift j b (` X) | inj₁ lt
  rewrite liftⁿ-lo b suc X lt
        | liftⁿ-lo b (_∸ suc (suc j)) X lt
        | liftⁿ-lo b (_∸ suc j) X lt = refl
dnT-shift j b (` .(b + i)) | inj₂ (i , refl)
  rewrite liftⁿ-hi b suc i
        | liftⁿ-hi b (_∸ suc (suc j)) (suc i)
        | liftⁿ-hi b (_∸ suc j) i = refl
dnT-shift j b `ℕ      = refl
dnT-shift j b `𝔹      = refl
dnT-shift j b (T ⇒ U) =
  cong₂ _⇒_ (dnT-shift j b T) (dnT-shift j b U)
dnT-shift j b (`∀ T)  = cong `∀ (dnT-shift j (suc b) T)

⟦⟧-shift : ∀ A Θ j A₁
  → ⟦ rvl A ∷ shiftReps Θ ⟧ᴴ (suc j) A₁ ≡ ⟦ Θ ⟧ᴴ j A₁
⟦⟧-shift A Θ j A₁
  rewrite bfree-shift A Θ 0 A₁ | rawRead-shift A Θ A₁
        | dfree-shift j 0 (rawRead Θ A₁)
        | dnT-shift j 0 (rawRead Θ A₁) = refl

revEnts-shift : ∀ A Θ j Ξ
  → revEnts (rvl A ∷ shiftReps Θ) (suc j) (shiftReps Ξ)
    ≡ revEnts Θ j Ξ
revEnts-shift A Θ j []            = refl
revEnts-shift A Θ j (rvl B ∷ Ξ)   =
  cong₂ _∷_ (⟦⟧-shift A Θ j B) (revEnts-shift A Θ (suc j) Ξ)
revEnts-shift A Θ j (rvl⋆ ∷ Ξ)    =
  cong (abst ∷_) (revEnts-shift A Θ (suc j) Ξ)
revEnts-shift A Θ j (cnc X B ∷ Ξ) = revEnts-shift A Θ j Ξ
revEnts-shift A Θ j (cnc⋆ X ∷ Ξ)  = revEnts-shift A Θ j Ξ

-- the interior of the shifted boundary is the old one, with the new
-- reveal's own knowledge entry on top
intOf-shift : ∀ (Γ : TCtx) A Θ
  → intOf Γ (rvl A ∷ shiftReps Θ)
    ≡ ⟦ rvl A ∷ shiftReps Θ ⟧ᴴ 0 A ∷ intOf Γ Θ
intOf-shift Γ A Θ =
  cong₂ (λ Ψ c → ⟦ rvl A ∷ shiftReps Θ ⟧ᴴ 0 A ∷ (Ψ ++ dropN c Γ))
        (revEnts-shift A Θ 0 Θ) (cmax-shiftReps Θ)

-- … so R1's boundary is well formed at the interior (env) uses.  TyWrap's own
-- premise is now the PLAIN Δ ⊢ A of the redex's ⊢·[]: no lift, because a
-- reveal's rep is read in the plain exterior.
bwf-shift : ∀ {Δ A} Θ → Δ ∣ intOf Δ Θ ⊢ᵇ Θ → Δ ⊢ A
  → Δ ∣ intOf Δ (rvl A ∷ shiftReps Θ) ⊢ᵇ (rvl A ∷ shiftReps Θ)
bwf-shift {Δ} {A} Θ bwf wfA =
  subst (λ Ψ → Bwf Δ Ψ (rvl A ∷ shiftReps Θ) (rvl A ∷ shiftReps Θ))
        (sym (intOf-shift Δ A Θ))
        (bwf↑ wfA
              (bwf-shiftReps (⟦ rvl A ∷ shiftReps Θ ⟧ᴴ 0 A)
                             Θ Θ bwf))


------------------------------------------------------------------------
-- MERGE, PART 2: THE SHAPE LAWS.
--
--   revs (Θ₁ ⊕ Θ₂) = revs Θ₁ + (revs Θ₂ ∸ cmax Θ₁)   -- R⊕
--   cmax (Θ₁ ⊕ Θ₂) = cmax Θ₂ + (cmax Θ₁ ∸ revs Θ₂)   -- C⊕
--
-- Both are pure entry-counting: the composite keeps Θ₁'s reveals and the
-- reveals of Θ₂ that Θ₁ did not drop, and it drops Θ₂'s conceals plus the
-- Θ₁-conceals that landed on inherited exterior slots.
------------------------------------------------------------------------

drop-lo : ∀ m j → j < m → m ∸ j ≡ suc (m ∸ suc j)
drop-lo (suc m) zero    (s≤s z≤n) = refl
drop-lo (suc m) (suc j) (s≤s lt)  = drop-lo m j lt

-- a ⊔ b, cut at a bound that already dominates a, is b cut at that bound
⊔∸-lo : ∀ a b c → a ≤ c → (a ⊔ b) ∸ c ≡ b ∸ c
⊔∸-lo a b c le with a ≤? b
⊔∸-lo a b c le | yes ab = cong (_∸ c) (m≤n⇒m⊔n≡n ab)
⊔∸-lo a b c le | no  ba =
  trans (cong (_∸ c) (m≥n⇒m⊔n≡m (<⇒≤ (≰⇒> ba))))
        (trans (m≤n⇒m∸n≡0 le)
               (sym (m≤n⇒m∸n≡0 (≤-trans (<⇒≤ (≰⇒> ba)) le))))

revs-mapL : ∀ Θ₂ Θ₁ → revs (mapL Θ₂ Θ₁) ≡ revs Θ₁
revs-mapL Θ₂ []            = refl
revs-mapL Θ₂ (rvl A ∷ Θ)   = cong suc (revs-mapL Θ₂ Θ)
revs-mapL Θ₂ (rvl⋆ ∷ Θ)    = cong suc (revs-mapL Θ₂ Θ)
revs-mapL Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
revs-mapL Θ₂ (cnc X A ∷ Θ) | yes _ = revs-mapL Θ₂ Θ
revs-mapL Θ₂ (cnc X A ∷ Θ) | no  _ = revs-mapL Θ₂ Θ
revs-mapL Θ₂ (cnc⋆ X ∷ Θ)  with X <? revs Θ₂
revs-mapL Θ₂ (cnc⋆ X ∷ Θ)  | yes _ = revs-mapL Θ₂ Θ
revs-mapL Θ₂ (cnc⋆ X ∷ Θ)  | no  _ = revs-mapL Θ₂ Θ

cmax-mapR : ∀ Θ₁ j Θ₂ → cmax (mapR Θ₁ j Θ₂) ≡ cmax Θ₂
cmax-mapR Θ₁ j []            = refl
cmax-mapR Θ₁ j (rvl A ∷ Θ)   with j <? cmax Θ₁
cmax-mapR Θ₁ j (rvl A ∷ Θ)   | yes _ = cmax-mapR Θ₁ (suc j) Θ
cmax-mapR Θ₁ j (rvl A ∷ Θ)   | no  _ = cmax-mapR Θ₁ (suc j) Θ
cmax-mapR Θ₁ j (rvl⋆ ∷ Θ)    with j <? cmax Θ₁
cmax-mapR Θ₁ j (rvl⋆ ∷ Θ)    | yes _ = cmax-mapR Θ₁ (suc j) Θ
cmax-mapR Θ₁ j (rvl⋆ ∷ Θ)    | no  _ = cmax-mapR Θ₁ (suc j) Θ
cmax-mapR Θ₁ j (cnc X A ∷ Θ) = cong (suc X ⊔_) (cmax-mapR Θ₁ j Θ)
cmax-mapR Θ₁ j (cnc⋆ X ∷ Θ)  = cong (suc X ⊔_) (cmax-mapR Θ₁ j Θ)

revs-mapR : ∀ Θ₁ j Θ₂ → revs (mapR Θ₁ j Θ₂) ≡ revs Θ₂ ∸ (cmax Θ₁ ∸ j)
revs-mapR Θ₁ j []          = sym (0∸n≡0 (cmax Θ₁ ∸ j))
revs-mapR Θ₁ j (rvl A ∷ Θ) with j <? cmax Θ₁
revs-mapR Θ₁ j (rvl A ∷ Θ) | yes lt =
  trans (revs-mapR Θ₁ (suc j) Θ)
        (sym (cong (suc (revs Θ) ∸_) (drop-lo (cmax Θ₁) j lt)))
revs-mapR Θ₁ j (rvl A ∷ Θ) | no ge =
  trans (cong suc (revs-mapR Θ₁ (suc j) Θ))
        (trans (cong (λ n → suc (revs Θ ∸ n))
                     (m≤n⇒m∸n≡0 (≤-trans (≮⇒≥ ge) (n≤1+n j))))
               (sym (cong (suc (revs Θ) ∸_) (m≤n⇒m∸n≡0 (≮⇒≥ ge)))))
revs-mapR Θ₁ j (rvl⋆ ∷ Θ) with j <? cmax Θ₁
revs-mapR Θ₁ j (rvl⋆ ∷ Θ) | yes lt =
  trans (revs-mapR Θ₁ (suc j) Θ)
        (sym (cong (suc (revs Θ) ∸_) (drop-lo (cmax Θ₁) j lt)))
revs-mapR Θ₁ j (rvl⋆ ∷ Θ) | no ge =
  trans (cong suc (revs-mapR Θ₁ (suc j) Θ))
        (trans (cong (λ n → suc (revs Θ ∸ n))
                     (m≤n⇒m∸n≡0 (≤-trans (≮⇒≥ ge) (n≤1+n j))))
               (sym (cong (suc (revs Θ) ∸_) (m≤n⇒m∸n≡0 (≮⇒≥ ge)))))
revs-mapR Θ₁ j (cnc X A ∷ Θ) = revs-mapR Θ₁ j Θ
revs-mapR Θ₁ j (cnc⋆ X ∷ Θ)  = revs-mapR Θ₁ j Θ

-- the kept-conceal case, shared by cnc and cnc⋆ (same index arithmetic)
cmax-mapL-kept : ∀ Θ₂ X Θ → revs Θ₂ ≤ X
  → cmax (mapL Θ₂ Θ) ⊔ cmax Θ₂ ≡ cmax Θ₂ + (cmax Θ ∸ revs Θ₂)
  → (suc (cmax Θ₂ + (X ∸ revs Θ₂)) ⊔ cmax (mapL Θ₂ Θ)) ⊔ cmax Θ₂
    ≡ cmax Θ₂ + ((suc X ⊔ cmax Θ) ∸ revs Θ₂)
cmax-mapL-kept Θ₂ X Θ ge ih =
  trans (⊔-assoc (suc (cmax Θ₂ + (X ∸ revs Θ₂))) (cmax (mapL Θ₂ Θ))
                 (cmax Θ₂))
        (trans (cong (suc (cmax Θ₂ + (X ∸ revs Θ₂)) ⊔_) ih)
               (trans (cong (_⊔ (cmax Θ₂ + (cmax Θ ∸ revs Θ₂))) sucstep)
                      (trans (sym (+-distribˡ-⊔ (cmax Θ₂) (suc X ∸ revs Θ₂)
                                                (cmax Θ ∸ revs Θ₂)))
                             (cong (cmax Θ₂ +_)
                                   (sym (∸-distribʳ-⊔ (revs Θ₂) (suc X)
                                                      (cmax Θ)))))))
  where
    sucstep : suc (cmax Θ₂ + (X ∸ revs Θ₂)) ≡ cmax Θ₂ + (suc X ∸ revs Θ₂)
    sucstep =
      trans (sym (+-suc (cmax Θ₂) (X ∸ revs Θ₂)))
            (cong (cmax Θ₂ +_) (sym (+-∸-assoc 1 ge)))

cmax-mapL⊔ : ∀ Θ₂ Θ₁
  → cmax (mapL Θ₂ Θ₁) ⊔ cmax Θ₂ ≡ cmax Θ₂ + (cmax Θ₁ ∸ revs Θ₂)
cmax-mapL⊔ Θ₂ []          =
  sym (trans (cong (cmax Θ₂ +_) (0∸n≡0 (revs Θ₂))) (+-identityʳ (cmax Θ₂)))
cmax-mapL⊔ Θ₂ (rvl A ∷ Θ) = cmax-mapL⊔ Θ₂ Θ
cmax-mapL⊔ Θ₂ (rvl⋆ ∷ Θ)  = cmax-mapL⊔ Θ₂ Θ
cmax-mapL⊔ Θ₂ (cnc X A ∷ Θ) with X <? revs Θ₂
cmax-mapL⊔ Θ₂ (cnc X A ∷ Θ) | yes lt =
  trans (cmax-mapL⊔ Θ₂ Θ)
        (cong (cmax Θ₂ +_) (sym (⊔∸-lo (suc X) (cmax Θ) (revs Θ₂) lt)))
cmax-mapL⊔ Θ₂ (cnc X A ∷ Θ) | no ge =
  cmax-mapL-kept Θ₂ X Θ (≮⇒≥ ge) (cmax-mapL⊔ Θ₂ Θ)
cmax-mapL⊔ Θ₂ (cnc⋆ X ∷ Θ)  with X <? revs Θ₂
cmax-mapL⊔ Θ₂ (cnc⋆ X ∷ Θ)  | yes lt =
  trans (cmax-mapL⊔ Θ₂ Θ)
        (cong (cmax Θ₂ +_) (sym (⊔∸-lo (suc X) (cmax Θ) (revs Θ₂) lt)))
cmax-mapL⊔ Θ₂ (cnc⋆ X ∷ Θ)  | no ge =
  cmax-mapL-kept Θ₂ X Θ (≮⇒≥ ge) (cmax-mapL⊔ Θ₂ Θ)

revs-⊕ : ∀ Θ₁ Θ₂ → revs (Θ₁ ⊕ Θ₂) ≡ R⊕ Θ₁ Θ₂
revs-⊕ Θ₁ Θ₂ =
  trans (revs-++ (mapL Θ₂ Θ₁) (mapR Θ₁ 0 Θ₂))
        (cong₂ _+_ (revs-mapL Θ₂ Θ₁) (revs-mapR Θ₁ 0 Θ₂))

cmax-⊕ : ∀ Θ₁ Θ₂ → cmax (Θ₁ ⊕ Θ₂) ≡ C⊕ Θ₁ Θ₂
cmax-⊕ Θ₁ Θ₂ =
  trans (cmax-++ (mapL Θ₂ Θ₁) (mapR Θ₁ 0 Θ₂))
        (trans (cong (cmax (mapL Θ₂ Θ₁) ⊔_) (cmax-mapR Θ₁ 0 Θ₂))
               (cmax-mapL⊔ Θ₂ Θ₁))

------------------------------------------------------------------------
-- MERGE, PART 3: THE INTERNAL FACE COMPOSES — ⊕-γ, A THEOREM.
--
--   ⊕-γ : cmax Θ₁ ≤ revs Θ₂ → Scoped (baseS Θ₁ Ψ₂) B₁
--       → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (γᵇ Θ₁) B₁
--
-- i.e. the merged wrapper types the SAME body at the SAME interior type —
-- which is why mrgB (B₁ pushed out) is the landed B₂′.  The side
-- condition says Θ₁ drops only slots Θ₂ reveals; it is MergeOK's first
-- component.  It is the EXTERNAL face that has no general law (part 4).
------------------------------------------------------------------------

γᵇ-lo : ∀ Θ X → X < revs Θ → γᵇ Θ X ≡ ` X
γᵇ-lo Θ X lt = prepId-lo (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) X lt

γᵇ-hi : ∀ Θ i → γᵇ Θ (revs Θ + i) ≡ γcnc (revs Θ) (cmax Θ) Θ i
γᵇ-hi Θ i = prepId-hi (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ) i

sub-ren : ∀ ρ σ A → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
sub-ren ρ σ A =
  trans (cong (substᵗ σ) (sym (substᵗ-renᵗ ρ A))) (sub-sub (renᵗ ρ) σ A)

-- Ψ₁ embeds into ⊕'s frame by up⊕, and γᵇ of the composite undoes it
γ-generic : ∀ Θ R C j → revs Θ ≡ R → cmax Θ ≡ C → R ≤ j
          → γᵇ Θ (R + (C + (j ∸ R))) ≡ ` j
γ-generic Θ R C j refl refl le =
  trans (γᵇ-hi Θ (cmax Θ + (j ∸ revs Θ)))
        (trans (γcnc-kept (revs Θ) (cmax Θ) Θ (cmax Θ + (j ∸ revs Θ))
                          (m≤m+n (cmax Θ) (j ∸ revs Θ)))
               (cong `_ (trans (cong (revs Θ +_)
                                     (m+n∸m≡n (cmax Θ) (j ∸ revs Θ)))
                               (m+[n∸m]≡n le))))

γ⊕-up : ∀ Θ₁ Θ₂ j → γᵇ (Θ₁ ⊕ Θ₂) (up⊕ Θ₁ Θ₂ j) ≡ ` j
γ⊕-up Θ₁ Θ₂ j with j <? R⊕ Θ₁ Θ₂
γ⊕-up Θ₁ Θ₂ j | yes lt =
  γᵇ-lo (Θ₁ ⊕ Θ₂) j (subst (j <_) (sym (revs-⊕ Θ₁ Θ₂)) lt)
γ⊕-up Θ₁ Θ₂ j | no ge =
  γ-generic (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂) (C⊕ Θ₁ Θ₂) j
            (revs-⊕ Θ₁ Θ₂) (cmax-⊕ Θ₁ Θ₂) (≮⇒≥ ge)

γ⊕-rep : ∀ Θ₁ Θ₂ A
       → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (renameᵗ (up⊕ Θ₁ Θ₂) A) ≡ A
γ⊕-rep Θ₁ Θ₂ A =
  trans (sub-ren (up⊕ Θ₁ Θ₂) (γᵇ (Θ₁ ⊕ Θ₂)) A)
        (trans (subst-cong (γ⊕-up Θ₁ Θ₂) A) (subst-id A))

∸-chain : ∀ {a b c} → a ≤ b → b ≤ c → (b ∸ a) + (c ∸ b) ≡ c ∸ a
∸-chain {zero}  z≤n      bc      = m+[n∸m]≡n bc
∸-chain (s≤s ab) (s≤s bc)        = ∸-chain ab bc

mrg₁-lo : ∀ Θ₁ Θ₂ j → j < revs Θ₁ → mrg₁ Θ₁ Θ₂ j ≡ ` j
mrg₁-lo Θ₁ Θ₂ j l with j <? revs Θ₁
mrg₁-lo Θ₁ Θ₂ j l | yes _  = refl
mrg₁-lo Θ₁ Θ₂ j l | no  ¬p = ⊥-elim (¬p l)

mrg₁-hi : ∀ Θ₁ Θ₂ X → mrg₁ Θ₁ Θ₂ (revs Θ₁ + X) ≡ mrgΨ Θ₁ Θ₂ X
mrg₁-hi Θ₁ Θ₂ X with (revs Θ₁ + X) <? revs Θ₁
mrg₁-hi Θ₁ Θ₂ X | yes lt = ⊥-elim (m+n≮m (revs Θ₁) X lt)
mrg₁-hi Θ₁ Θ₂ X | no  _  = cong (mrgΨ Θ₁ Θ₂) (m+n∸m≡n (revs Θ₁) X)

mrgΨ-c : ∀ Θ₁ Θ₂ X → X < revs Θ₂ → X < cmax Θ₁
       → mrgΨ Θ₁ Θ₂ X ≡ renameᵗ (up⊕ Θ₁ Θ₂) (repOf X Θ₁)
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ with X <? revs Θ₂
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | yes _ with X <? cmax Θ₁
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | yes _ | yes _ = refl
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | yes _ | no ¬p = ⊥-elim (¬p l₁)
mrgΨ-c Θ₁ Θ₂ X l₂ l₁ | no ¬p         = ⊥-elim (¬p l₂)

mrgΨ-r : ∀ Θ₁ Θ₂ X → X < revs Θ₂ → cmax Θ₁ ≤ X
       → mrgΨ Θ₁ Θ₂ X ≡ ` (revs Θ₁ + (X ∸ cmax Θ₁))
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ with X <? revs Θ₂
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | yes _ with X <? cmax Θ₁
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | yes _ | yes p = ⊥-elim (≤⇒≯ g₁ p)
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | yes _ | no  _ = refl
mrgΨ-r Θ₁ Θ₂ X l₂ g₁ | no ¬p         = ⊥-elim (¬p l₂)

mrgΨ-d : ∀ Θ₁ Θ₂ X → revs Θ₂ ≤ X
       → mrgΨ Θ₁ Θ₂ X ≡ ` (R⊕ Θ₁ Θ₂ + (cmax Θ₂ + (X ∸ revs Θ₂)))
mrgΨ-d Θ₁ Θ₂ X g₂ with X <? revs Θ₂
mrgΨ-d Θ₁ Θ₂ X g₂ | yes p = ⊥-elim (≤⇒≯ g₂ p)
mrgΨ-d Θ₁ Θ₂ X g₂ | no  _ = refl

-- the KEPT case of a Θ₂-revealed slot: Θ₁ does not drop it, so both sides
-- land on the composite's own reveal slot
⊕-γ-kept : ∀ Θ₁ Θ₂ X → X < revs Θ₂ → cmax Θ₁ ≤ X
     → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrg₁ Θ₁ Θ₂ (revs Θ₁ + X))
       ≡ γᵇ Θ₁ (revs Θ₁ + X)
⊕-γ-kept Θ₁ Θ₂ X l₂ g₁ =
  trans (cong (substᵗ (γᵇ (Θ₁ ⊕ Θ₂)))
              (trans (mrg₁-hi Θ₁ Θ₂ X) (mrgΨ-r Θ₁ Θ₂ X l₂ g₁)))
        (trans (γᵇ-lo (Θ₁ ⊕ Θ₂) (revs Θ₁ + (X ∸ cmax Θ₁)) lt⊕)
               (sym (trans (γᵇ-hi Θ₁ X)
                           (γcnc-kept (revs Θ₁) (cmax Θ₁) Θ₁ X g₁))))
  where
    lt⊕ : revs Θ₁ + (X ∸ cmax Θ₁) < revs (Θ₁ ⊕ Θ₂)
    lt⊕ = subst (revs Θ₁ + (X ∸ cmax Θ₁) <_) (sym (revs-⊕ Θ₁ Θ₂))
                (+-monoʳ-< (revs Θ₁) (∸-monoˡ-< l₂ g₁))

-- the pointwise internal-face law, at an ACCESSIBLE slot of Θ₁'s frame
⊕-γ-pt : ∀ Θ₁ Θ₂ → cmax Θ₁ ≤ revs Θ₂ → ∀ X
       → (cmax Θ₁ ≤ X) ⊎ (isConc X Θ₁ ≡ true)
       → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrg₁ Θ₁ Θ₂ (revs Θ₁ + X))
         ≡ γᵇ Θ₁ (revs Θ₁ + X)
⊕-γ-pt Θ₁ Θ₂ sc X acc with X <? revs Θ₂
⊕-γ-pt Θ₁ Θ₂ sc X (inj₁ g₁) | yes l₂ = ⊕-γ-kept Θ₁ Θ₂ X l₂ g₁
⊕-γ-pt Θ₁ Θ₂ sc X (inj₂ c)  | yes l₂ with cmax Θ₁ ≤? X
⊕-γ-pt Θ₁ Θ₂ sc X (inj₂ c)  | yes l₂ | yes g₁ = ⊕-γ-kept Θ₁ Θ₂ X l₂ g₁
⊕-γ-pt Θ₁ Θ₂ sc X (inj₂ c)  | yes l₂ | no  l₁ =
  trans (cong (substᵗ (γᵇ (Θ₁ ⊕ Θ₂)))
              (trans (mrg₁-hi Θ₁ Θ₂ X) (mrgΨ-c Θ₁ Θ₂ X l₂ (≰⇒> l₁))))
        (trans (γ⊕-rep Θ₁ Θ₂ (repOf X Θ₁))
               (sym (trans (γᵇ-hi Θ₁ X)
                           (γcnc-conc (revs Θ₁) (cmax Θ₁) Θ₁ X c))))
⊕-γ-pt Θ₁ Θ₂ sc X acc | no g₂ =
  trans (cong (substᵗ (γᵇ (Θ₁ ⊕ Θ₂)))
              (trans (mrg₁-hi Θ₁ Θ₂ X) (mrgΨ-d Θ₁ Θ₂ X (≮⇒≥ g₂))))
        (trans lhs (sym rhs))
  where
    g₂' : revs Θ₂ ≤ X
    g₂' = ≮⇒≥ g₂
    g₁ : cmax Θ₁ ≤ X
    g₁ = ≤-trans sc g₂'
    cC : C⊕ Θ₁ Θ₂ ≡ cmax Θ₂
    cC = trans (cong (cmax Θ₂ +_) (m≤n⇒m∸n≡0 sc)) (+-identityʳ (cmax Θ₂))
    shape : C⊕ Θ₁ Θ₂ + ((R⊕ Θ₁ Θ₂ + (X ∸ revs Θ₂)) ∸ R⊕ Θ₁ Θ₂)
          ≡ cmax Θ₂ + (X ∸ revs Θ₂)
    shape = cong₂ _+_ cC (m+n∸m≡n (R⊕ Θ₁ Θ₂) (X ∸ revs Θ₂))
    lhs : γᵇ (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂ + (cmax Θ₂ + (X ∸ revs Θ₂)))
        ≡ ` (revs Θ₁ + (X ∸ cmax Θ₁))
    lhs = trans (cong (λ u → γᵇ (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂ + u)) (sym shape))
                (trans (γ-generic (Θ₁ ⊕ Θ₂) (R⊕ Θ₁ Θ₂) (C⊕ Θ₁ Θ₂)
                                  (R⊕ Θ₁ Θ₂ + (X ∸ revs Θ₂))
                                  (revs-⊕ Θ₁ Θ₂) (cmax-⊕ Θ₁ Θ₂)
                                  (m≤m+n (R⊕ Θ₁ Θ₂) (X ∸ revs Θ₂)))
                       (cong `_ (trans (+-assoc (revs Θ₁)
                                                (revs Θ₂ ∸ cmax Θ₁)
                                                (X ∸ revs Θ₂))
                                       (cong (revs Θ₁ +_)
                                             (∸-chain sc g₂')))))
    rhs : γᵇ Θ₁ (revs Θ₁ + X) ≡ ` (revs Θ₁ + (X ∸ cmax Θ₁))
    rhs = trans (γᵇ-hi Θ₁ X) (γcnc-kept (revs Θ₁) (cmax Θ₁) Θ₁ X g₁)

⊕-γ : ∀ {Ψ₂ : TCtx} {B₁} Θ₁ Θ₂ → cmax Θ₁ ≤ revs Θ₂
    → Scoped (baseS Θ₁ Ψ₂) B₁
    → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁) ≡ substᵗ (γᵇ Θ₁) B₁
⊕-γ {Ψ₂} {B₁} Θ₁ Θ₂ sc scB =
  trans (sub-sub (mrg₁ Θ₁ Θ₂) (γᵇ (Θ₁ ⊕ Θ₂)) B₁) (subst-cong-sc scB pt)
  where
    pt : ∀ j → baseS Θ₁ Ψ₂ ∋ok j
       → substᵗ (γᵇ (Θ₁ ⊕ Θ₂)) (mrg₁ Θ₁ Θ₂ j) ≡ γᵇ Θ₁ j
    pt j p with split (revs Θ₁) j
    pt j p | inj₁ lt
      rewrite mrg₁-lo Θ₁ Θ₂ j lt =
        trans (γᵇ-lo (Θ₁ ⊕ Θ₂) j
                     (subst (j <_) (sym (revs-⊕ Θ₁ Θ₂))
                            (≤-trans lt
                                     (m≤m+n (revs Θ₁)
                                            (revs Θ₂ ∸ cmax Θ₁)))))
              (sym (γᵇ-lo Θ₁ j lt))
    pt j p | inj₂ (X , refl) =
      ⊕-γ-pt Θ₁ Θ₂ sc X (baseS-acc Θ₁ X p)

------------------------------------------------------------------------
-- MERGE, PART 4: THE EXTERNAL FACE, AND WHY IT IS A PREMISE.
--
-- ρᵇ of the composite reads off as expected at Θ₁'s reveals (their reps
-- PUSHED OUT), at Θ₂'s surviving reveals, and at the exterior — that is
-- ρ⊕-lo / ρ⊕-mid / ρᵇ-hi below, all theorems.  Composing them gives
--
--   substᵗ (ρᵇ (Θ₁ ⊕ Θ₂)) (mrgB Θ₁ Θ₂ B₁)
--     = substᵗ (outSub Θ₂) (substᵗ (ρᵇ Θ₁) B₁)     … away from cancels
--     = substᵗ (outSub Θ₂) (substᵗ (γᵇ Θ₂) B₂)     … the middle-type eq
--
-- and the redex's own type is substᵗ (ρᵇ Θ₂) B₂.  The two differ exactly
-- where B₂ names a CONCEAL of Θ₂: read IN, the slot becomes the conceal's
-- rep; read OUT, the reversal premise says that rep is Δ's KNOWLEDGE about
-- the slot — ≈Δ̄-equal to the concealed variable, never syntactically equal
-- to it.  So the equation is MergeOK's last component, not a lemma; the
-- counterexample is notes/InstallGauntlet §9d.
------------------------------------------------------------------------

ρᵇ-mapL-lo : ∀ Θ₂ Θ₁ Ξ j → j < revs Θ₁
  → ρᵇ (mapL Θ₂ Θ₁ ++ Ξ) j ≡ substᵗ (outSub Θ₂) (ρᵇ Θ₁ j)
ρᵇ-mapL-lo Θ₂ []            Ξ j       ()
ρᵇ-mapL-lo Θ₂ (rvl A ∷ Θ)   Ξ zero    lt       = refl
ρᵇ-mapL-lo Θ₂ (rvl A ∷ Θ)   Ξ (suc j) (s≤s lt) = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt
ρᵇ-mapL-lo Θ₂ (rvl⋆ ∷ Θ)    Ξ zero    lt       = refl
ρᵇ-mapL-lo Θ₂ (rvl⋆ ∷ Θ)    Ξ (suc j) (s≤s lt) = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt
ρᵇ-mapL-lo Θ₂ (cnc X A ∷ Θ) Ξ j lt with X <? revs Θ₂
ρᵇ-mapL-lo Θ₂ (cnc X A ∷ Θ) Ξ j lt | yes _ = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt
ρᵇ-mapL-lo Θ₂ (cnc X A ∷ Θ) Ξ j lt | no  _ = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt
ρᵇ-mapL-lo Θ₂ (cnc⋆ X ∷ Θ)  Ξ j lt with X <? revs Θ₂
ρᵇ-mapL-lo Θ₂ (cnc⋆ X ∷ Θ)  Ξ j lt | yes _ = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt
ρᵇ-mapL-lo Θ₂ (cnc⋆ X ∷ Θ)  Ξ j lt | no  _ = ρᵇ-mapL-lo Θ₂ Θ Ξ j lt

ρᵇ-mapL-hi : ∀ Θ₂ Θ₁ Ξ t → ρᵇ (mapL Θ₂ Θ₁ ++ Ξ) (revs Θ₁ + t) ≡ ρᵇ Ξ t
ρᵇ-mapL-hi Θ₂ []            Ξ t = refl
ρᵇ-mapL-hi Θ₂ (rvl A ∷ Θ)   Ξ t = ρᵇ-mapL-hi Θ₂ Θ Ξ t
ρᵇ-mapL-hi Θ₂ (rvl⋆ ∷ Θ)    Ξ t = ρᵇ-mapL-hi Θ₂ Θ Ξ t
ρᵇ-mapL-hi Θ₂ (cnc X A ∷ Θ) Ξ t with X <? revs Θ₂
ρᵇ-mapL-hi Θ₂ (cnc X A ∷ Θ) Ξ t | yes _ = ρᵇ-mapL-hi Θ₂ Θ Ξ t
ρᵇ-mapL-hi Θ₂ (cnc X A ∷ Θ) Ξ t | no  _ = ρᵇ-mapL-hi Θ₂ Θ Ξ t
ρᵇ-mapL-hi Θ₂ (cnc⋆ X ∷ Θ)  Ξ t with X <? revs Θ₂
ρᵇ-mapL-hi Θ₂ (cnc⋆ X ∷ Θ)  Ξ t | yes _ = ρᵇ-mapL-hi Θ₂ Θ Ξ t
ρᵇ-mapL-hi Θ₂ (cnc⋆ X ∷ Θ)  Ξ t | no  _ = ρᵇ-mapL-hi Θ₂ Θ Ξ t

-- the composite's face at Θ₁'s OWN reveal slots: the rep, pushed out
ρ⊕-lo : ∀ Θ₁ Θ₂ j → j < revs Θ₁
      → ρᵇ (Θ₁ ⊕ Θ₂) j ≡ substᵗ (outSub Θ₂) (ρᵇ Θ₁ j)
ρ⊕-lo Θ₁ Θ₂ j lt = ρᵇ-mapL-lo Θ₂ Θ₁ (mapR Θ₁ 0 Θ₂) j lt

ρᵇ-mapR : ∀ Θ₁ j Θ₂ t → (cmax Θ₁ ∸ j) ≤ revs Θ₂
  → ρᵇ (mapR Θ₁ j Θ₂) t ≡ ρᵇ Θ₂ ((cmax Θ₁ ∸ j) + t)
ρᵇ-mapR Θ₁ j []            t le = cong (λ n → ` (n + t)) (sym (n≤0⇒n≡0 le))
ρᵇ-mapR Θ₁ j (rvl A ∷ Θ)   t le with j <? cmax Θ₁
ρᵇ-mapR Θ₁ j (rvl A ∷ Θ)   t le | yes lt =
  trans (ρᵇ-mapR Θ₁ (suc j) Θ t le')
        (cong (λ n → ρᵇ (rvl A ∷ Θ) (n + t)) (sym dd))
  where
    dd : cmax Θ₁ ∸ j ≡ suc (cmax Θ₁ ∸ suc j)
    dd = drop-lo (cmax Θ₁) j lt
    le' : (cmax Θ₁ ∸ suc j) ≤ revs Θ
    le' = ≤-pred (subst (_≤ suc (revs Θ)) dd le)
ρᵇ-mapR Θ₁ j (rvl A ∷ Θ)   t le | no ge =
  trans (body t) (cong (λ n → ρᵇ (rvl A ∷ Θ) (n + t)) (sym z))
  where
    z : cmax Θ₁ ∸ j ≡ 0
    z = m≤n⇒m∸n≡0 (≮⇒≥ ge)
    z' : cmax Θ₁ ∸ suc j ≡ 0
    z' = m≤n⇒m∸n≡0 (≤-trans (≮⇒≥ ge) (n≤1+n j))
    body : ∀ u → ρᵇ (rvl A ∷ mapR Θ₁ (suc j) Θ) u ≡ ρᵇ (rvl A ∷ Θ) u
    body zero    = refl
    body (suc u) =
      trans (ρᵇ-mapR Θ₁ (suc j) Θ u (subst (_≤ revs Θ) (sym z') z≤n))
            (cong (λ n → ρᵇ Θ (n + u)) z')
ρᵇ-mapR Θ₁ j (rvl⋆ ∷ Θ)    t le with j <? cmax Θ₁
ρᵇ-mapR Θ₁ j (rvl⋆ ∷ Θ)    t le | yes lt =
  trans (ρᵇ-mapR Θ₁ (suc j) Θ t le')
        (cong (λ n → ρᵇ (rvl⋆ ∷ Θ) (n + t)) (sym dd))
  where
    dd : cmax Θ₁ ∸ j ≡ suc (cmax Θ₁ ∸ suc j)
    dd = drop-lo (cmax Θ₁) j lt
    le' : (cmax Θ₁ ∸ suc j) ≤ revs Θ
    le' = ≤-pred (subst (_≤ suc (revs Θ)) dd le)
ρᵇ-mapR Θ₁ j (rvl⋆ ∷ Θ)    t le | no ge =
  trans (body t) (cong (λ n → ρᵇ (rvl⋆ ∷ Θ) (n + t)) (sym z))
  where
    z : cmax Θ₁ ∸ j ≡ 0
    z = m≤n⇒m∸n≡0 (≮⇒≥ ge)
    z' : cmax Θ₁ ∸ suc j ≡ 0
    z' = m≤n⇒m∸n≡0 (≤-trans (≮⇒≥ ge) (n≤1+n j))
    body : ∀ u → ρᵇ (rvl⋆ ∷ mapR Θ₁ (suc j) Θ) u ≡ ρᵇ (rvl⋆ ∷ Θ) u
    body zero    = refl
    body (suc u) =
      trans (ρᵇ-mapR Θ₁ (suc j) Θ u (subst (_≤ revs Θ) (sym z') z≤n))
            (cong (λ n → ρᵇ Θ (n + u)) z')
ρᵇ-mapR Θ₁ j (cnc X A ∷ Θ) t le = ρᵇ-mapR Θ₁ j Θ t le
ρᵇ-mapR Θ₁ j (cnc⋆ X ∷ Θ)  t le = ρᵇ-mapR Θ₁ j Θ t le

-- the composite's face at Θ₂'s SURVIVING reveal slots
ρ⊕-mid : ∀ Θ₁ Θ₂ t → cmax Θ₁ ≤ revs Θ₂
  → ρᵇ (Θ₁ ⊕ Θ₂) (revs Θ₁ + t) ≡ ρᵇ Θ₂ (cmax Θ₁ + t)
ρ⊕-mid Θ₁ Θ₂ t sc =
  trans (ρᵇ-mapL-hi Θ₂ Θ₁ (mapR Θ₁ 0 Θ₂) t) (ρᵇ-mapR Θ₁ 0 Θ₂ t sc)

------------------------------------------------------------------------
-- MERGE, PART 5: WORKED EXAMPLE (a) — THE CANCEL PAIR.
--
--   (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=ℕ , X ⟫  --Merge--→  7 ⟪ ∅ , ℕ ⟫
--                                    --Drop$--→  7          (all : ℕ)
--
-- The inner boundary CONCEALS the very slot the outer one REVEALS, so
-- mapL deletes the conceal and mapR deletes the reveal: the composite is
-- EMPTY.  B₂′ is the cancelled slot rewritten through the agreed rep — ℕ.
--
-- THE PAIR IS THE DECISION-6 CLASSIFICATION IN MINIATURE.  The inner
-- face ` 0 is INERT (revs Θ1c = 0, so slot 0 is a conceal), the outer
-- face ` 0 is ACTIVE (0 < revs Θ2c = 1), so the redex is not a value and
-- Merge is its unique step; the contractum's face is the BASE type ℕ,
-- active again, so Drop$ removes the vacuous wrapper — which is what
-- Drop∅ used to do, and why Drop∅ is retired rather than replaced.
------------------------------------------------------------------------

Θ1c Θ2c : BCtx
Θ1c = cnc 0 `ℕ ∷ []                    -- ↓X:=ℕ, over the interior of Θ2c
Θ2c = rvl `ℕ ∷ []                      -- ↑X:=ℕ

_ : Θ1c ⊕ Θ2c ≡ []                     -- both entries cancel
_ = refl

_ : mrgB Θ1c Θ2c (` 0) ≡ `ℕ            -- B₂′ = the agreed rep
_ = refl

⊢redex-c : [] ∣ [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ ⦂ `ℕ
⊢redex-c = env (bwf↑ wf-ℕ bwf[]) (sc-var hereᵒ)
               (env (bwf↓ here (≡→≈ refl) wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

ok-c : MergeOK [] Θ1c Θ2c (` 0) (` 0)
ok-c = s≤s z≤n , bwf[] , sc-ℕ , ≼≈[] , refl

_ : [] ⊢ (($ 7) ⟪ Θ1c , ` 0 ⟫) ⟪ Θ2c , ` 0 ⟫ -→ ($ 7) ⟪ [] , `ℕ ⟫
_ = Merge V-$ (I-var z≤n) (A-var (s≤s z≤n)) ok-c

⊢contractum-c : [] ∣ [] ⊢ ($ 7) ⟪ [] , `ℕ ⟫ ⦂ `ℕ
⊢contractum-c = env bwf[] sc-ℕ ⊢$

_ : [] ⊢ ($ 7) ⟪ [] , `ℕ ⟫ -→ $ 7
_ = Drop$

⊢final-c : [] ∣ [] ⊢ $ 7 ⦂ `ℕ
⊢final-c = ⊢$

------------------------------------------------------------------------
-- MERGE, PART 6: WORKED EXAMPLE (c) — AN EXAMPLE-3-SHAPED TOWER, MERGED
-- TWICE.  Δtw = X:=𝔹 ;  Θtw3 = ↑Z₁:=X , ↓X:=𝔹 ;  Θtw2 = ↑Z₂:=Z₁ , ↑Y:=ℕ ;
-- Θtw1 = ↑Z₃:=Z₂ ;  V = λz:Z₃. z.
--
-- Every boundary type is Z→Z at its own level, and each composite keeps
-- both faces on the nose.  The INTERIORS, however, compose only up to
-- _≼≈_: nested, Z₃'s entry is the reveal variable Z₂; merged, it is Z₂'s
-- own rep — and the two agree after ONE unfolding, which is exactly the
-- knowledge ordering ⊢retag≈ consumes (MergeProbe's ¬⊕-intR, resolved
-- by ≼≈).
--
-- AFTER DECISION 6 THIS TOWER DOES NOT STEP, and that is the point: every
-- face here is ⇒-shaped, hence INERT, so the tower is a VALUE at rest
-- (val-tower / tower-¬-→) and its boundaries are consumed at their USE
-- site by Peel, one layer per application — never merged.  What survives
-- as evidence is the ⊕ ARITHMETIC and the MergeOK packages themselves
-- (ok-tw1 / ok-tw2, still fully discharged): the composite is well
-- formed and both faces agree, which is what a merge WOULD need.  The
-- steps are gone because the value restriction forbids them, not because
-- the composite got worse.
------------------------------------------------------------------------

Δtw : TCtx
Δtw = rvld `𝔹 ∷ []

Θtw3 Θtw2 Θtw1 : BCtx
Θtw3 = rvl (` 0) ∷ cnc 0 `𝔹 ∷ []
Θtw2 = rvl (` 0) ∷ rvl `ℕ ∷ []
Θtw1 = rvl (` 0) ∷ []

Ψtw3 : TCtx
Ψtw3 = intOf Δtw Θtw3

Vtw : Term
Vtw = ƛ ` 0 ∙ ` 0

-- the nested interiors, and the composite's — equal EXCEPT at the entries
-- the merge resolves one step further
_ : intOf (intOf Ψtw3 Θtw2) Θtw1
    ≡ rvld (` 0) ∷ rvld (` 1) ∷ rvld `ℕ ∷ rvld `𝔹 ∷ []
_ = refl

_ : intOf Ψtw3 (Θtw1 ⊕ Θtw2)
    ≡ rvld (` 2) ∷ rvld (` 1) ∷ rvld `ℕ ∷ rvld `𝔹 ∷ []
_ = refl

int-tw1 : intOf (intOf Ψtw3 Θtw2) Θtw1 ≼≈ intOf Ψtw3 (Θtw1 ⊕ Θtw2)
int-tw1 = ≼≈rvld (≼≈-refl _) (≈unf refl)

_ : Θtw1 ⊕ Θtw2 ≡ rvl (` 0) ∷ rvl (` 0) ∷ rvl `ℕ ∷ []
_ = refl

⊢tower : Δtw ∣ []
  ⊢ ((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
  ⦂ (` 0 ⇒ ` 0)
⊢tower =
  env (bwf↑ (wf-var here-rvld) (bwf↓ here (≡→≈ refl) wf-𝔹 bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (env (bwf↑ (wf-var here-rvld) (bwf↑ wf-ℕ bwf[]))
           (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
           (env (bwf↑ (wf-var here-rvld) bwf[])
                (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
                (⊢ƛ (wf-var here-rvld) (⊢` here))))

ok-tw1 : MergeOK Ψtw3 Θtw1 Θtw2 (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
ok-tw1 = z≤n
       , bwf↑ (wf-var here-rvld) (bwf↑ (wf-var here-rvld)
                                       (bwf↑ wf-ℕ bwf[]))
       , sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)
       , int-tw1
       , refl

-- THE TOWER IS A VALUE, and therefore takes no step at all: all three
-- faces are ⇒-shaped, so all three boundaries are inert.
val-tower : Value (((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫)
                     ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫)
val-tower = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ (V-G G-ƛ) I-⇒) I-⇒) I-⇒

tower-¬-→ : ∀ {M′}
  → Δtw ⊢ ((Vtw ⟪ Θtw1 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw2 , ` 0 ⇒ ` 0 ⟫)
            ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫ -→ M′ → ⊥
tower-¬-→ = V-¬-→ val-tower

⊢tower′ : Δtw ∣ []
  ⊢ (Vtw ⟪ Θtw1 ⊕ Θtw2 , ` 0 ⇒ ` 0 ⟫) ⟪ Θtw3 , ` 0 ⇒ ` 0 ⟫
  ⦂ (` 0 ⇒ ` 0)
⊢tower′ =
  env (bwf↑ (wf-var here-rvld) (bwf↓ here (≡→≈ refl) wf-𝔹 bwf[]))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (env (bwf↑ (wf-var here-rvld)
                 (bwf↑ (wf-var here-rvld) (bwf↑ wf-ℕ bwf[])))
           (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
           (⊢ƛ (wf-var here-rvld) (⊢` here)))

Θtw⊕ : BCtx
Θtw⊕ = (Θtw1 ⊕ Θtw2) ⊕ Θtw3

_ : Θtw⊕ ≡ rvl (` 0) ∷ rvl (` 0) ∷ rvl `ℕ ∷ rvl (` 0) ∷ cnc 0 `𝔹 ∷ []
_ = refl

int-tw2 : intOf Ψtw3 (Θtw1 ⊕ Θtw2) ≼≈ intOf Δtw Θtw⊕
int-tw2 = ≼≈rvld (≼≈rvld (≼≈-refl _) (≈unf refl)) (≈unf refl)

ok-tw2 : MergeOK Δtw (Θtw1 ⊕ Θtw2) Θtw3 (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
ok-tw2 = z≤n
       , bwf↑ (wf-var here-rvld)
              (bwf↑ (wf-var here-rvld)
                    (bwf↑ wf-ℕ
                          (bwf↑ (wf-var here-rvld)
                                (bwf↓ here (≡→≈ refl) wf-𝔹 bwf[]))))
       , sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ)
       , int-tw2
       , refl

-- the twice-merged boundary still types the value at the tower's own
-- type — the composite is right, it is just never reached by a step
⊢tower″ : Δtw ∣ [] ⊢ Vtw ⟪ Θtw⊕ , ` 0 ⇒ ` 0 ⟫ ⦂ (` 0 ⇒ ` 0)
⊢tower″ =
  env (bwf↑ (wf-var here-rvld)
            (bwf↑ (wf-var here-rvld)
                  (bwf↑ wf-ℕ
                        (bwf↑ (wf-var here-rvld)
                              (bwf↓ here (≡→≈ refl) wf-𝔹 bwf[])))))
      (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
      (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- (env) INVERSION, WITH A FREE RESULT INDEX.  (env) is the only rule whose
-- subject is a wrapper, so a wrapper's type is FORCED to be its external
-- face.  Stated with a free T so the unifier never has to match a
-- constructor type against the neutral substᵗ (ρᵇ Θ) B₀ — the same trick
-- strong.Progress uses, and what Merge's preservation case needs to invert
-- the NESTED (env) and read off the middle type.
------------------------------------------------------------------------

env-ty : ∀ {Δ Γₜ M Θ B₀ T} → Δ ∣ Γₜ ⊢ M ⟪ Θ , B₀ ⟫ ⦂ T
       → T ≡ substᵗ (ρᵇ Θ) B₀
env-ty (env bwf sc ⊢M) = refl

env-bwf : ∀ {Δ Γₜ M Θ B₀ T} → Δ ∣ Γₜ ⊢ M ⟪ Θ , B₀ ⟫ ⦂ T
        → Δ ∣ intOf Δ Θ ⊢ᵇ Θ
env-bwf (env bwf sc ⊢M) = bwf

env-sc : ∀ {Δ Γₜ M Θ B₀ T} → Δ ∣ Γₜ ⊢ M ⟪ Θ , B₀ ⟫ ⦂ T
       → Scoped (baseS Θ Δ) B₀
env-sc (env bwf sc ⊢M) = sc

env-body : ∀ {Δ Γₜ M Θ B₀ T} → Δ ∣ Γₜ ⊢ M ⟪ Θ , B₀ ⟫ ⦂ T
         → intOf Δ Θ ∣ [] ⊢ M ⦂ substᵗ (γᵇ Θ) B₀
env-body (env bwf sc ⊢M) = ⊢M

-- THE MIDDLE-TYPE EQUATION, read off the nested (env)s: the inner
-- wrapper's EXTERNAL face is the outer wrapper's INTERNAL face.  This is
-- what Merge's two obligations are stated relative to.
mid-eq : ∀ {Δ V Θ₁ Θ₂ B₁ B₂}
       → intOf Δ Θ₂ ∣ [] ⊢ V ⟪ Θ₁ , B₁ ⟫ ⦂ substᵗ (γᵇ Θ₂) B₂
       → substᵗ (γᵇ Θ₂) B₂ ≡ substᵗ (ρᵇ Θ₁) B₁
mid-eq ⊢in = env-ty ⊢in

------------------------------------------------------------------------
-- CANCEL-AGREE, ORDINARY — THE ≡-ANALOGUE OF DualDef's xrep-stored, ON THE
-- LIVE CORE.  An ORDINARY knowledge lookup inside a boundary's reveal block
-- returns the READING of that reveal's STORED rep, on the nose:
--
--   rep-stored :  (revEnts Θ j Ξ ++ Γ) ∋ k := A₀
--              →  A₀ ≡ dnT (suc (j + k)) (rawRead Θ (ρᵇ Ξ k))
--
-- This is what justifies MERGE'S DELETING CANCEL for an ordinary pair.  A
-- conceal of Θ₁ at a slot Θ₂ REVEALS is licensed by (bwf-↓) against the
-- interior's knowledge about that slot — and by this lemma that knowledge
-- IS the reading of the deleted reveal's rep.  So the rep the cancel keeps
-- and the rep the deleted reveal carried are the same type, read at the two
-- ends of the boundary: exactly the old `cancel-agree`, re-derived here on
-- the knowledge interiors.  (The x-pair's version is DualDef's xrep-stored
-- + dual-cnc-skel; between them the two disjuncts of every conceal licence
-- are covered.)
------------------------------------------------------------------------

rep-stored : ∀ Θ j Ξ {Γ : TCtx} {A₀} k → k < revs Ξ
           → (revEnts Θ j Ξ ++ Γ) ∋ k := A₀
           → A₀ ≡ dnT (suc (j + k)) (rawRead Θ (ρᵇ Ξ k))
rep-stored Θ j []            k       ()       p
rep-stored Θ j (rvl A ∷ Ξ)   zero    lt       p
  with expr Θ j A | p
rep-stored Θ j (rvl A ∷ Ξ)   zero    lt       p | true  | here =
  cong (λ n → dnT (suc n) (rawRead Θ A)) (sym (+-identityʳ j))
rep-stored Θ j (rvl A ∷ Ξ)   zero    lt       p | false | ()
rep-stored Θ j (rvl A ∷ Ξ)   (suc k) (s≤s lt) p
  with expr Θ j A | p
rep-stored Θ j (rvl A ∷ Ξ)   (suc k) (s≤s lt) p | true  | skip-rvld q =
  trans (rep-stored Θ (suc j) Ξ k lt q)
        (cong (λ n → dnT (suc n) (rawRead Θ (ρᵇ Ξ k))) (sym (+-suc j k)))
rep-stored Θ j (rvl A ∷ Ξ)   (suc k) (s≤s lt) p | false | skip-xrvld q =
  trans (rep-stored Θ (suc j) Ξ k lt q)
        (cong (λ n → dnT (suc n) (rawRead Θ (ρᵇ Ξ k))) (sym (+-suc j k)))
rep-stored Θ j (rvl⋆ ∷ Ξ)    zero    lt       ()
rep-stored Θ j (rvl⋆ ∷ Ξ)    (suc k) (s≤s lt) (skip-abst q) =
  trans (rep-stored Θ (suc j) Ξ k lt q)
        (cong (λ n → dnT (suc n) (rawRead Θ (ρᵇ Ξ k))) (sym (+-suc j k)))
rep-stored Θ j (cnc X A ∷ Ξ) k       lt       p = rep-stored Θ j Ξ k lt p
rep-stored Θ j (cnc⋆ X ∷ Ξ)  k       lt       p = rep-stored Θ j Ξ k lt p

-- … and at a boundary's own interior, which is the form the cancel consumes
cancel-agree : ∀ {Δ₀ : TCtx} Θ {A₀} k → k < revs Θ
             → intOf Δ₀ Θ ∋ k := A₀
             → A₀ ≡ dnT (suc k) (rawRead Θ (ρᵇ Θ k))
cancel-agree Θ k lt p = rep-stored Θ 0 Θ k lt p
