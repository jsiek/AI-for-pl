module strong.notes.GroundedProbe where

-- DESIGN FEASIBILITY PROBE (not part of the development) for DECISIONS.md
-- Decision 1, Option 1a — "grounded reps": a reveal puts a REVEALED entry
-- `rvld A` (not `abst`) into the interior, and a conceal `cnc X A` is well
-- formed only if the exterior already knows X at that rep, `Δ ∋ X := A`.
--
-- Nothing here edits Boundary.agda: the whole variant is a private copy —
--   intOf′ / _∣_⊢ᵇ′_ / _∣_⊢′_⦂_ — sharing γᵇ, ρᵇ, Scoped and baseS with the
-- real development (those read Δ only through its SHAPE, so they are reused
-- unchanged; baseS-len, imported from BReduction, is the proof).
--
-- Contents
--   §0  the variant definitions
--   §1  `bad` (BoundaryRulesProbe §5a) is NOT typable under ⊢′            ✓
--   §2  Example 8's trace T0 … T5 all type under ⊢′                       ✓
--   §3  the Wrap crux: ⊢retag fails, a ≼-retagging replaces it; the
--       runtime invariant it needs, and a COUNTEREXAMPLE when it fails
--   §4  Merge/Cancel: a conceal in Θ₁ agrees with the reveal in Θ₂        ✓
--   §5  THE HOLE IN 1a: `bad₂`, a closed stuck value that passes 1a's
--       check — 1a's `Δ ∋ X := A` compares an EXTERIOR reading of A with
--       an INTERIOR one, and they differ by the reveal prefix.  With the
--       repaired premise (§5c) `bad₂` is rejected.

open import Data.Nat
  using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ⊔-lub; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import strong.Types
open import strong.Context
  using (TCtx; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         _∋_:=_; here; ∋:=→∋tv;
         Ctx; _∋_⦂_; there; ⤊)
open import strong.Boundary
open import strong.BReduction
  using (Value; GVal; V-$; V-G; V-⟪⟫; G-ƛ; G-Λ; _-→_;
         TyBeta; Beta; TyWrap; Wrap; ξ-·-l; ξ-·-r; ξ-·[]; ξ-Λ; ξ-⟪⟫;
         ⇑ᵀ; _[_]ᵐ; polyid; ∀ZZ;
         dualᵇ; swapᵇ; repOf; rvlsOf; cncOfRevs; shiftReps;
         revs-dual; cmax-dual; baseS-len; ∋tv-len-bound)

private
  variable
    Δ Δ′ Ψ Ψ′ : TCtx
    Γₜ : Ctx
    A B C B₀ : Ty
    M N : Term
    Θ : BCtx
    x n X : ℕ

------------------------------------------------------------------------
-- §0.  The Option-1a variant
------------------------------------------------------------------------

-- The reveal entries, as KNOWLEDGE entries: the rep is stored exactly as it
-- was written, i.e. read in the boundary's EXTERIOR Δ, not over its own tail.
-- (This is the "first cost" of 1a recorded in DECISIONS.md; §5 shows it has
-- teeth.)
revEnts : BCtx → TCtx
revEnts []            = []
revEnts (rvl A   ∷ Θ) = rvld A ∷ revEnts Θ
revEnts (cnc X A ∷ Θ) = revEnts Θ

intOf′ : TCtx → BCtx → TCtx
intOf′ Δ Θ = revEnts Θ ++ dropN (cmax Θ) Δ

-- shape agreement with the real intOf: same length, so γᵇ/ρᵇ/baseS are reusable
len-revEnts : ∀ Θ → length (revEnts Θ) ≡ revs Θ
len-revEnts []            = refl
len-revEnts (rvl A   ∷ Θ) = cong suc (len-revEnts Θ)
len-revEnts (cnc X A ∷ Θ) = len-revEnts Θ

-- (bwf-↓) of Option 1a: the rep is licensed by the exterior's knowledge.
-- The `Ψ ⊢ A` premise of the real bwf↓ is KEPT (see §5 for why it cannot
-- simply be dropped: it is the only premise that reads A on the side where
-- γᵇ actually uses it).
infix 4 _∣_⊢ᵇ′_
data _∣_⊢ᵇ′_ : TCtx → TCtx → BCtx → Set where
  bwf[]′ : Δ ∣ Ψ ⊢ᵇ′ []
  bwf↑′  : Δ ⊢ A → Δ ∣ Ψ ⊢ᵇ′ Θ → Δ ∣ Ψ ⊢ᵇ′ (rvl A ∷ Θ)
  bwf↓′  : Δ ∋ X := A → Ψ ⊢ A → Δ ∣ Ψ ⊢ᵇ′ Θ → Δ ∣ Ψ ⊢ᵇ′ (cnc X A ∷ Θ)

infix 3 _∣_⊢′_⦂_
data _∣_⊢′_⦂_ : TCtx → Ctx → Term → Ty → Set where
  ⊢`′   : Γₜ ∋ x ⦂ A → Δ ∣ Γₜ ⊢′ ` x ⦂ A
  ⊢$′   : Δ ∣ Γₜ ⊢′ $ n ⦂ `ℕ
  ⊢ƛ′   : Δ ⊢ A → Δ ∣ A ∷ Γₜ ⊢′ N ⦂ B → Δ ∣ Γₜ ⊢′ ƛ A ∙ N ⦂ (A ⇒ B)
  ⊢·′   : Δ ∣ Γₜ ⊢′ M ⦂ (A ⇒ B) → Δ ∣ Γₜ ⊢′ N ⦂ A → Δ ∣ Γₜ ⊢′ M · N ⦂ B
  ⊢Λ′   : (abst ∷ Δ) ∣ ⤊ Γₜ ⊢′ N ⦂ C → Δ ∣ Γₜ ⊢′ Λ N ⦂ `∀ C
  ⊢·[]′ : Δ ∣ Γₜ ⊢′ M ⦂ `∀ B → Δ ⊢ A → Δ ∣ Γₜ ⊢′ M ·[ B , A ] ⦂ B [ A ]ᵗ
  env′  : Δ ∣ intOf′ Δ Θ ⊢ᵇ′ Θ
        → Scoped (baseS Θ Δ) B₀
        → intOf′ Δ Θ ∣ [] ⊢′ M ⦂ substᵗ (γᵇ Θ) B₀
          ---------------------------------------------------
        → Δ ∣ Γₜ ⊢′ M ⟪ Θ , B₀ ⟫ ⦂ substᵗ (ρᵇ Θ) B₀

------------------------------------------------------------------------
-- §1.  `bad` is refuted.
--
--   bad = ((7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=∀Z.Z→Z , X ⟫)  :  ∀Z.Z→Z
--
-- Under ⊢′ the outer boundary's interior is `rvld ∀ZZ ∷ []`, so the inner
-- conceal must produce  (rvld ∀ZZ ∷ []) ∋ 0 := ℕ  — refuted by `here`'s
-- unifier (ℕ ≢ ∀ZZ).  This is Option 1a doing its job.
------------------------------------------------------------------------

bad : Term
bad = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ rvl ∀ZZ ∷ [] , ` 0 ⟫

-- for the record: under the CURRENT (env) it is well typed (Boundary’s rule)
⊢bad-old : [] ∣ [] ⊢ bad ⦂ ∀ZZ
⊢bad-old = env (bwf↑ (wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst))) bwf[])
               (sc-var hereᵒ)
               (env (bwf↓ here-abst wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$)

_ : intOf′ [] (rvl ∀ZZ ∷ []) ≡ rvld ∀ZZ ∷ []
_ = refl

¬⊢bad : ¬ ([] ∣ [] ⊢′ bad ⦂ ∀ZZ)
¬⊢bad (env′ _ _ (env′ (bwf↓′ () _ _) _ _))

------------------------------------------------------------------------
-- §2.  Example 8's trace, T0 … T5, under ⊢′.
--
-- The contexts change: every reveal now contributes `rvld A` instead of
-- `abst`, so Example8Trace's Δ1 = [abst] becomes [rvld ℕ] and its
-- Δ8 = [abst , abst] becomes [abst , rvld ℕ].  Three derivations need care
-- (marked ★): a `wf-var here-abst` becomes `wf-var here-rvld` where the
-- variable in question is now a reveal entry.
------------------------------------------------------------------------

Bfun : Ty
Bfun = ∀ZZ ⇒ ∀ZZ

body8 : Term
body8 = Λ ((` 0) ·[ ` 0 ⇒ ` 0 , ` 0 ])

src : Term
src = Λ (ƛ ∀ZZ ∙ body8)

Θr : BCtx                       -- ↑X:=ℕ
Θr = rvl `ℕ ∷ []

Θc : BCtx                       -- ↓X:=ℕ  (= dualᵇ Θr)
Θc = cnc 0 `ℕ ∷ []

Θ8′ : BCtx                      -- ↓X:=ℕ after ⇑ᵀ
Θ8′ = cnc 1 `ℕ ∷ []

Θn : BCtx                       -- ↑Z:=Y , ↓X:=ℕ
Θn = rvl (` 0) ∷ shiftReps Θ8′

Θi : BCtx                       -- the boundary TyBeta mints inside T4
Θi = rvl (` 0) ∷ []

_ : dualᵇ Θr ≡ Θc
_ = refl

Δ1′ : TCtx                      -- interior of ↑X:=ℕ : X is REVEALED at ℕ
Δ1′ = rvld `ℕ ∷ []

Δ8′ : TCtx                      -- under the Λ inside it : [Y , X:=ℕ]
Δ8′ = abst ∷ rvld `ℕ ∷ []

_ : intOf′ [] Θr ≡ Δ1′
_ = refl

_ : intOf′ Δ1′ Θc ≡ []
_ = refl

_ : intOf′ Δ8′ Θ8′ ≡ []
_ = refl

_ : intOf′ Δ8′ Θn ≡ rvld (` 0) ∷ []
_ = refl

-- the scope stacks are unchanged (baseS reads Δ's shape only)
_ : baseS Θ8′ Δ8′ ≡ blk ∷ ok ∷ []
_ = refl

_ : baseS Θn Δ8′ ≡ ok ∷ blk ∷ ok ∷ []
_ = refl

-- … but the interior of T5's inner boundary is a context whose `rvld`
-- entries are NOT tail-relative: slot 0 stores ` 0 meaning "slot 0 of the
-- exterior [rvld (` 0)]", slot 1 stores ` 0 meaning "slot 0 of Δ8′" (= Y).
-- Reading either as a telescope entry gives the wrong type.  §5 exploits it.
_ : intOf′ (rvld (` 0) ∷ []) Θi ≡ rvld (` 0) ∷ rvld (` 0) ∷ []
_ = refl

⊢∀ZZ : ∀ {Δ} → Δ ⊢ ∀ZZ
⊢∀ZZ = wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst))

⊢polyid′ : ∀ {Δ Γₜ} → Δ ∣ Γₜ ⊢′ polyid ⦂ ∀ZZ
⊢polyid′ = ⊢Λ′ (⊢ƛ′ (wf-var here-abst) (⊢`′ here))

⊢lam8′ : ∀ {Δ} → Δ ∣ [] ⊢′ (ƛ ∀ZZ ∙ body8) ⦂ Bfun
⊢lam8′ = ⊢ƛ′ ⊢∀ZZ (⊢Λ′ (⊢·[]′ (⊢`′ here) (wf-var here-abst)))

sc∀ZZ : ∀ {Φ} → Scoped Φ ∀ZZ
sc∀ZZ = sc-∀ (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))

-- T0
T0 : Term
T0 = (src ·[ Bfun , `ℕ ]) · polyid

⊢T0 : [] ∣ [] ⊢′ T0 ⦂ ∀ZZ
⊢T0 = ⊢·′ (⊢·[]′ (⊢Λ′ ⊢lam8′) wf-ℕ) ⊢polyid′

-- T1 (TyBeta)
T1 : Term
T1 = ((ƛ ∀ZZ ∙ body8) ⟪ Θr , Bfun ⟫) · polyid

_ : T0 -→ T1
_ = ξ-·-l (TyBeta (V-G G-ƛ))

⊢T1 : [] ∣ [] ⊢′ T1 ⦂ ∀ZZ
⊢T1 = ⊢·′ (env′ (bwf↑′ wf-ℕ bwf[]′) (sc-⇒ sc∀ZZ sc∀ZZ) ⊢lam8′) ⊢polyid′

-- T2 (Wrap): the argument enters through the dual.  1a's check on the
-- dual's conceal is  Δ1′ ∋ 0 := ℕ  — the reveal it came from ✓.
W2 : Term
W2 = polyid ⟪ Θc , ∀ZZ ⟫

-- 2026-09-04 (Decision 2 revised): Wrap now CONSUMES the ƛ, so T1 steps
-- straight to T3 (T2's own Beta contractum) — see the step below T3.  T2 is
-- kept as a typing record: the claim here is that it types under ⊢′.
T2 : Term
T2 = ((ƛ ∀ZZ ∙ body8) · W2) ⟪ Θr , ∀ZZ ⟫

⊢W2 : Δ1′ ∣ [] ⊢′ W2 ⦂ ∀ZZ
⊢W2 = env′ (bwf↓′ here wf-ℕ bwf[]′) sc∀ZZ ⊢polyid′

⊢T2 : [] ∣ [] ⊢′ T2 ⦂ ∀ZZ
⊢T2 = env′ (bwf↑′ wf-ℕ bwf[]′) sc∀ZZ (⊢·′ ⊢lam8′ ⊢W2)

-- T3 (Beta under the boundary)
W3 : Term
W3 = polyid ⟪ Θ8′ , ∀ZZ ⟫

T3 : Term
T3 = (Λ (W3 ·[ ` 0 ⇒ ` 0 , ` 0 ])) ⟪ Θr , ∀ZZ ⟫

_ : ⇑ᵀ W2 ≡ W3
_ = refl

_ : T2 -→ T3
_ = ξ-⟪⟫ (Beta (V-⟪⟫ (V-G (G-Λ (V-G G-ƛ)))))

-- … and the ONE step the current Wrap makes of the two: the dual-wrapped
-- argument it substitutes IS W2, so the contractum is T3 on the nose.
_ : T1 -→ T3
_ = Wrap (V-G (G-Λ (V-G G-ƛ)))

-- the conceal of X is licensed by Δ8′'s knowledge X:=ℕ
⊢redex′ : Δ8′ ∣ [] ⊢′ (W3 ·[ ` 0 ⇒ ` 0 , ` 0 ]) ⦂ (` 0 ⇒ ` 0)
⊢redex′ = ⊢·[]′ (env′ (bwf↓′ (skip-abst here) wf-ℕ bwf[]′) sc∀ZZ ⊢polyid′)
                (wf-var here-abst)

⊢T3 : [] ∣ [] ⊢′ T3 ⦂ ∀ZZ
⊢T3 = env′ (bwf↑′ wf-ℕ bwf[]′) sc∀ZZ (⊢Λ′ ⊢redex′)

-- T4 (the OLD float-inside TyWrap's contractum).  ★ the floated type
-- application is applied to the fresh reveal variable, which is now a
-- REVEALED entry: wf-var here-rvld.
-- 2026-09-04 (Decision 2 revised): TyWrap now CONSUMES the Λ, so T3 steps to
-- T4′ below instead; T4 and T5 are kept as typing records (and T4 -→ T5 is
-- still a real step from T4).
R1body : Term
R1body = (polyid ·[ ` 0 ⇒ ` 0 , ` 0 ]) ⟪ Θn , ` 0 ⇒ ` 0 ⟫

T4 : Term
T4 = (Λ R1body) ⟪ Θr , ∀ZZ ⟫

-- the direct-combine contractum: the Λ's slot IS the new reveal's, so the
-- Λ-body stands where the floated application used to be
T4′body : Term
T4′body = (ƛ ` 0 ∙ ` 0) ⟪ Θn , ` 0 ⇒ ` 0 ⟫

T4′ : Term
T4′ = (Λ T4′body) ⟪ Θr , ∀ZZ ⟫

_ : T3 -→ T4′
_ = ξ-⟪⟫ (ξ-Λ (TyWrap (V-G G-ƛ)))

⊢R1body : Δ8′ ∣ [] ⊢′ R1body ⦂ (` 0 ⇒ ` 0)
⊢R1body =
  env′ (bwf↑′ (wf-var here-abst) (bwf↓′ (skip-abst here) wf-ℕ bwf[]′))
       (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
       (⊢·[]′ ⊢polyid′ (wf-var here-rvld))          -- ★ was here-abst

⊢T4 : [] ∣ [] ⊢′ T4 ⦂ ∀ZZ
⊢T4 = env′ (bwf↑′ wf-ℕ bwf[]′) sc∀ZZ (⊢Λ′ ⊢R1body)

⊢T4′body : Δ8′ ∣ [] ⊢′ T4′body ⦂ (` 0 ⇒ ` 0)
⊢T4′body =
  env′ (bwf↑′ (wf-var here-abst) (bwf↓′ (skip-abst here) wf-ℕ bwf[]′))
       (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
       (⊢ƛ′ (wf-var here-rvld) (⊢`′ here))          -- ★ was here-abst

⊢T4′ : [] ∣ [] ⊢′ T4′ ⦂ ∀ZZ
⊢T4′ = env′ (bwf↑′ wf-ℕ bwf[]′) sc∀ZZ (⊢Λ′ ⊢T4′body)

-- T5 (TyBeta inside T4): the nested wrapper.  ★ twice.
T5body : Term
T5body = ((ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫) ⟪ Θn , ` 0 ⇒ ` 0 ⟫

T5 : Term
T5 = (Λ T5body) ⟪ Θr , ∀ZZ ⟫

_ : T4 -→ T5
_ = ξ-⟪⟫ (ξ-Λ (ξ-⟪⟫ (TyBeta (V-G G-ƛ))))

⊢inner : (rvld (` 0) ∷ []) ∣ [] ⊢′ (ƛ ` 0 ∙ ` 0) ⟪ Θi , ` 0 ⇒ ` 0 ⟫
                              ⦂ (` 0 ⇒ ` 0)
⊢inner = env′ (bwf↑′ (wf-var here-rvld) bwf[]′)     -- ★ was here-abst
              (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
              (⊢ƛ′ (wf-var here-rvld) (⊢`′ here))   -- ★ was here-abst

⊢T5body : Δ8′ ∣ [] ⊢′ T5body ⦂ (` 0 ⇒ ` 0)
⊢T5body =
  env′ (bwf↑′ (wf-var here-abst) (bwf↓′ (skip-abst here) wf-ℕ bwf[]′))
       (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
       ⊢inner

⊢T5 : [] ∣ [] ⊢′ T5 ⦂ ∀ZZ
⊢T5 = env′ (bwf↑′ wf-ℕ bwf[]′) sc∀ZZ (⊢Λ′ ⊢T5body)

------------------------------------------------------------------------
-- §3.  The Wrap crux.
--
-- ⊢retag (typing transports along any context of the same LENGTH) FAILS for
-- ⊢′, because bwf↓′ reads ∋:=.  What survives is a MONOTONE retagging: a
-- derivation transports along a context that is at least as informative
-- entrywise.  `abst` may become anything (nothing reads it); `rvld A` must
-- stay `rvld A`.
------------------------------------------------------------------------

infix 4 _≼_
data _≼_ : TCtx → TCtx → Set where
  ≼[]   : [] ≼ []
  ≼abst : ∀ {Δ Δ′ E} → Δ ≼ Δ′ → (abst ∷ Δ) ≼ (E ∷ Δ′)
  ≼rvld : ∀ {Δ Δ′ A} → Δ ≼ Δ′ → (rvld A ∷ Δ) ≼ (rvld A ∷ Δ′)

≼-refl : ∀ (Δ : TCtx) → Δ ≼ Δ
≼-refl []             = ≼[]
≼-refl (abst   ∷ Δ)   = ≼abst (≼-refl Δ)
≼-refl (rvld A ∷ Δ)   = ≼rvld (≼-refl Δ)

≼-len : Δ ≼ Δ′ → length Δ ≡ length Δ′
≼-len ≼[]        = refl
≼-len (≼abst p)  = cong suc (≼-len p)
≼-len (≼rvld p)  = cong suc (≼-len p)

≼-∋tv : Δ ≼ Δ′ → Δ ∋tv X → Δ′ ∋tv X
≼-∋tv (≼abst {E = abst}   p) here-abst     = here-abst
≼-∋tv (≼abst {E = rvld _} p) here-abst     = here-rvld
≼-∋tv (≼rvld p)              here-rvld     = here-rvld
≼-∋tv (≼abst {E = abst}   p) (skip-abst q) = skip-abst (≼-∋tv p q)
≼-∋tv (≼abst {E = rvld _} p) (skip-abst q) = skip-rvld (≼-∋tv p q)
≼-∋tv (≼rvld p)              (skip-rvld q) = skip-rvld (≼-∋tv p q)

≼-∋:= : Δ ≼ Δ′ → Δ ∋ X := A → Δ′ ∋ X := A
≼-∋:= (≼rvld p)              here          = here
≼-∋:= (≼abst {E = abst}   p) (skip-abst q) = skip-abst (≼-∋:= p q)
≼-∋:= (≼abst {E = rvld _} p) (skip-abst q) = skip-rvld (≼-∋:= p q)
≼-∋:= (≼rvld p)              (skip-rvld q) = skip-rvld (≼-∋:= p q)

≼-⊢ : Δ ≼ Δ′ → Δ ⊢ A → Δ′ ⊢ A
≼-⊢ p (wf-var q) = wf-var (≼-∋tv p q)
≼-⊢ p wf-ℕ       = wf-ℕ
≼-⊢ p wf-𝔹       = wf-𝔹
≼-⊢ p (wf-⇒ a b) = wf-⇒ (≼-⊢ p a) (≼-⊢ p b)
≼-⊢ p (wf-∀ a)   = wf-∀ (≼-⊢ (≼abst p) a)

≼-dropN : ∀ n → Δ ≼ Δ′ → dropN n Δ ≼ dropN n Δ′
≼-dropN zero    p           = p
≼-dropN (suc n) ≼[]         = ≼[]
≼-dropN (suc n) (≼abst p)   = ≼-dropN n p
≼-dropN (suc n) (≼rvld p)   = ≼-dropN n p

≼-++ : ∀ (Φ : TCtx) → Δ ≼ Δ′ → (Φ ++ Δ) ≼ (Φ ++ Δ′)
≼-++ []            p = p
≼-++ (abst   ∷ Φ)  p = ≼abst (≼-++ Φ p)
≼-++ (rvld A ∷ Φ)  p = ≼rvld (≼-++ Φ p)

≼-intOf′ : ∀ Θ → Δ ≼ Δ′ → intOf′ Δ Θ ≼ intOf′ Δ′ Θ
≼-intOf′ Θ p = ≼-++ (revEnts Θ) (≼-dropN (cmax Θ) p)

≼-bwf′ : Δ ≼ Δ′ → Ψ ≼ Ψ′ → Δ ∣ Ψ ⊢ᵇ′ Θ → Δ′ ∣ Ψ′ ⊢ᵇ′ Θ
≼-bwf′ pΔ pΨ bwf[]′          = bwf[]′
≼-bwf′ pΔ pΨ (bwf↑′ w b)     = bwf↑′ (≼-⊢ pΔ w) (≼-bwf′ pΔ pΨ b)
≼-bwf′ pΔ pΨ (bwf↓′ k w b)   =
  bwf↓′ (≼-∋:= pΔ k) (≼-⊢ pΨ w) (≼-bwf′ pΔ pΨ b)

-- the replacement for ⊢retag
⊢retag′ : Δ ≼ Δ′ → Δ ∣ Γₜ ⊢′ M ⦂ A → Δ′ ∣ Γₜ ⊢′ M ⦂ A
⊢retag′ p (⊢`′ q)        = ⊢`′ q
⊢retag′ p ⊢$′            = ⊢$′
⊢retag′ p (⊢ƛ′ w ⊢N)     = ⊢ƛ′ (≼-⊢ p w) (⊢retag′ p ⊢N)
⊢retag′ p (⊢·′ ⊢L ⊢M)    = ⊢·′ (⊢retag′ p ⊢L) (⊢retag′ p ⊢M)
⊢retag′ p (⊢Λ′ ⊢N)       = ⊢Λ′ (⊢retag′ (≼abst p) ⊢N)
⊢retag′ p (⊢·[]′ ⊢L w)   = ⊢·[]′ (⊢retag′ p ⊢L) (≼-⊢ p w)
⊢retag′ {Δ} {Δ′} p (env′ {Θ = Θ} {B₀ = B₀} b sc ⊢M) =
  env′ (≼-bwf′ p (≼-intOf′ Θ p) b)
       (subst (λ Φ → Scoped Φ B₀) (baseS-len Θ Δ Δ′ (≼-len p)) sc)
       (⊢retag′ (≼-intOf′ Θ p) ⊢M)

------------------------------------------------------------------------
-- §3a.  The dual's interior, under intOf′.
--
--   intOf′ (intOf′ Δ Θ) (dualᵇ Θ)  =  [rvld (repOf 0 Θ) … rvld (repOf (c−1) Θ)]
--                                     ++ dropN c Δ          (c = cmax Θ)
--
-- so it REBUILDS Δ's dropped prefix from Θ's conceal reps: at a CONCEALED
-- slot that is exactly Δ's own entry (bwf↓′ says Δ ∋ X := repOf X Θ), and at
-- a BLOCKED slot it is the dummy `rvld ℕ`, which agrees with Δ only when
-- Δ's entry there is `abst`.
------------------------------------------------------------------------

revEnts-++ : ∀ Θ₁ Θ₂ → revEnts (Θ₁ ++ Θ₂) ≡ revEnts Θ₁ ++ revEnts Θ₂
revEnts-++ []            Θ₂ = refl
revEnts-++ (rvl A   ∷ Θ) Θ₂ = cong (rvld A ∷_) (revEnts-++ Θ Θ₂)
revEnts-++ (cnc X A ∷ Θ) Θ₂ = revEnts-++ Θ Θ₂

revEnts-cncOfRevs : ∀ j Θ → revEnts (cncOfRevs j Θ) ≡ []
revEnts-cncOfRevs j []            = refl
revEnts-cncOfRevs j (rvl A   ∷ Θ) = revEnts-cncOfRevs (suc j) Θ
revEnts-cncOfRevs j (cnc X A ∷ Θ) = revEnts-cncOfRevs j Θ

dropN-++ : ∀ (Φ Δ : TCtx) → dropN (length Φ) (Φ ++ Δ) ≡ Δ
dropN-++ []      Δ = refl
dropN-++ (E ∷ Φ) Δ = dropN-++ Φ Δ

dropN-len : ∀ {n} (Φ Δ : TCtx) → length Φ ≡ n → dropN n (Φ ++ Δ) ≡ Δ
dropN-len Φ Δ refl = dropN-++ Φ Δ

intOf′-dual : ∀ (Δ : TCtx) Θ
  → intOf′ (intOf′ Δ Θ) (dualᵇ Θ)
    ≡ revEnts (rvlsOf (cmax Θ) 0 Θ) ++ dropN (cmax Θ) Δ
intOf′-dual Δ Θ
  rewrite revEnts-++ (rvlsOf (cmax Θ) 0 Θ) (cncOfRevs 0 Θ)
        | revEnts-cncOfRevs 0 Θ
        | ++-identityʳ (revEnts (rvlsOf (cmax Θ) 0 Θ))
        | dropN-len {cmax (dualᵇ Θ)} (revEnts Θ) (dropN (cmax Θ) Δ)
                    (trans (len-revEnts Θ) (sym (cmax-dual Θ)))
  = refl

------------------------------------------------------------------------
-- §3b.  The runtime invariant, and the transport it buys.
--
-- Fits Θ k s Δ : the first k entries of Δ, whose Θ-slot numbers start at s,
-- are each either `abst` (a blocked slot carries no knowledge) or exactly
-- `rvld (repOf …)` (a concealed slot carries Θ's own rep).
------------------------------------------------------------------------

data Fits (Θ : BCtx) : ℕ → ℕ → TCtx → Set where
  fits0 : ∀ {s Δ} → Fits Θ 0 s Δ
  fitsA : ∀ {k s Δ} → Fits Θ k (suc s) Δ → Fits Θ (suc k) s (abst ∷ Δ)
  fitsR : ∀ {k s Δ A} → A ≡ repOf s Θ → Fits Θ k (suc s) Δ
        → Fits Θ (suc k) s (rvld A ∷ Δ)

fits-≼ : ∀ Θ k s (Δ : TCtx) → Fits Θ k s Δ
       → Δ ≼ (revEnts (rvlsOf k s Θ) ++ dropN k Δ)
fits-≼ Θ zero    s Δ            fits0        = ≼-refl Δ
fits-≼ Θ (suc k) s (abst ∷ Δ)   (fitsA f)    = ≼abst (fits-≼ Θ k (suc s) Δ f)
fits-≼ Θ (suc k) s (rvld A ∷ Δ) (fitsR refl f) =
  ≼rvld (fits-≼ Θ k (suc s) Δ f)

-- the Wrap crux, discharged under the invariant
dual-≼ : ∀ (Δ : TCtx) Θ → Fits Θ (cmax Θ) 0 Δ
       → Δ ≼ intOf′ (intOf′ Δ Θ) (dualᵇ Θ)
dual-≼ Δ Θ f =
  subst (Δ ≼_) (sym (intOf′-dual Δ Θ)) (fits-≼ Θ (cmax Θ) 0 Δ f)

-- Wrap's preservation obligation: the argument retypes in the dual's interior
Wrap-arg : ∀ {Δ Γₜ M A} Θ → Fits Θ (cmax Θ) 0 Δ
         → Δ ∣ Γₜ ⊢′ M ⦂ A
         → intOf′ (intOf′ Δ Θ) (dualᵇ Θ) ∣ Γₜ ⊢′ M ⦂ A
Wrap-arg {Δ} Θ f ⊢M = ⊢retag′ (dual-≼ Δ Θ f) ⊢M

------------------------------------------------------------------------
-- §3c.  Where the invariant comes from: the CONCEALED half is free
-- (bwf↓′ gives it), the BLOCKED half is the real proof obligation.
------------------------------------------------------------------------

data AbstAt : TCtx → ℕ → Set where
  ab-here  : ∀ {Δ}     → AbstAt (abst ∷ Δ) 0
  ab-there : ∀ {Δ E X} → AbstAt Δ X → AbstAt (E ∷ Δ) (suc X)

-- a concealed slot's Δ-entry is exactly `rvld (repOf X Θ)`
bwf-repOf : ∀ {Δ Ψ} Θ → Δ ∣ Ψ ⊢ᵇ′ Θ
          → ∀ i → isConc i Θ ≡ true → Δ ∋ i := repOf i Θ
bwf-repOf [] bwf[]′ i ()
bwf-repOf (rvl A ∷ Θ) (bwf↑′ _ b) i q = bwf-repOf Θ b i q
bwf-repOf (cnc X A ∷ Θ) (bwf↓′ k _ b) i q with i ≟ X
... | yes refl = k
... | no  _    = bwf-repOf Θ b i q

∋:=-tail : ∀ {Δ E X A} → (E ∷ Δ) ∋ suc X := A → Δ ∋ X := A
∋:=-tail (skip-abst p) = p
∋:=-tail (skip-rvld p) = p

∋:=-head : ∀ {Δ E A} → (E ∷ Δ) ∋ 0 := A → E ≡ rvld A
∋:=-head here = refl

mkFits : ∀ Θ k s (Δ : TCtx) → k ≤ length Δ
  → (∀ i → i < k → isConc (i + s) Θ ≡ true  → Δ ∋ i := repOf (i + s) Θ)
  → (∀ i → i < k → isConc (i + s) Θ ≡ false → AbstAt Δ i)
  → Fits Θ k s Δ
mkFits Θ zero    s Δ       le hc hb = fits0
mkFits Θ (suc k) s (E ∷ Δ) (s≤s le) hc hb with isConc s Θ in eqc
... | true  = subst (λ E′ → Fits Θ (suc k) s (E′ ∷ Δ))
                    (sym (∋:=-head (hc 0 (s≤s z≤n) eqc)))
                    (fitsR refl (mkFits Θ k (suc s) Δ le hc′ hb′))
  where
    hc′ : ∀ i → i < k → isConc (i + suc s) Θ ≡ true
        → Δ ∋ i := repOf (i + suc s) Θ
    hc′ i lt q =
      subst (λ m → Δ ∋ i := repOf m Θ) (sym (+-suc i s))
        (∋:=-tail (hc (suc i) (s≤s lt)
          (subst (λ m → isConc m Θ ≡ true) (+-suc i s) q)))
    hb′ : ∀ i → i < k → isConc (i + suc s) Θ ≡ false → AbstAt Δ i
    hb′ i lt q with hb (suc i) (s≤s lt)
                        (subst (λ m → isConc m Θ ≡ false) (+-suc i s) q)
    ... | ab-there a = a
... | false with hb 0 (s≤s z≤n) eqc
...   | ab-here = fitsA (mkFits Θ k (suc s) Δ le hc′ hb′)
  where
    hc′ : ∀ i → i < k → isConc (i + suc s) Θ ≡ true
        → Δ ∋ i := repOf (i + suc s) Θ
    hc′ i lt q =
      subst (λ m → Δ ∋ i := repOf m Θ) (sym (+-suc i s))
        (∋:=-tail (hc (suc i) (s≤s lt)
          (subst (λ m → isConc m Θ ≡ true) (+-suc i s) q)))
    hb′ : ∀ i → i < k → isConc (i + suc s) Θ ≡ false → AbstAt Δ i
    hb′ i lt q with hb (suc i) (s≤s lt)
                        (subst (λ m → isConc m Θ ≡ false) (+-suc i s) q)
    ... | ab-there a = a

bwf′-cmax : ∀ {Δ Ψ} Θ → Δ ∣ Ψ ⊢ᵇ′ Θ → cmax Θ ≤ length Δ
bwf′-cmax []            bwf[]′         = z≤n
bwf′-cmax (rvl A ∷ Θ)   (bwf↑′ _ b)    = bwf′-cmax Θ b
bwf′-cmax (cnc X A ∷ Θ) (bwf↓′ k _ b)  =
  ⊔-lub (∋tv-len-bound (∋:=→∋tv k)) (bwf′-cmax Θ b)

-- BlkAbst Θ Δ : every BLOCKED slot of Θ carries no knowledge in Δ.
-- This is the one new invariant Option 1a's Wrap needs.
BlkAbst : BCtx → TCtx → Set
BlkAbst Θ Δ = ∀ i → i < cmax Θ → isConc i Θ ≡ false → AbstAt Δ i

Fits-of : ∀ {Δ Ψ} Θ → Δ ∣ Ψ ⊢ᵇ′ Θ → BlkAbst Θ Δ → Fits Θ (cmax Θ) 0 Δ
Fits-of {Δ} Θ b bA =
  mkFits Θ (cmax Θ) 0 Δ (bwf′-cmax Θ b)
    (λ i lt q → subst (λ m → Δ ∋ i := repOf m Θ) (sym (+-identityʳ i))
                  (bwf-repOf Θ b i (subst (λ m → isConc m Θ ≡ true)
                                          (+-identityʳ i) q)))
    (λ i lt q → bA i lt (subst (λ m → isConc m Θ ≡ false) (+-identityʳ i) q))

-- Putting §3b and §3c together: Wrap's preservation case goes through under
-- ⊢′ provided BlkAbst holds of the redex's boundary.
Wrap-arg′ : ∀ {Δ Ψ Γₜ M A} Θ → Δ ∣ Ψ ⊢ᵇ′ Θ → BlkAbst Θ Δ
          → Δ ∣ Γₜ ⊢′ M ⦂ A
          → intOf′ (intOf′ Δ Θ) (dualᵇ Θ) ∣ Γₜ ⊢′ M ⦂ A
Wrap-arg′ Θ b bA ⊢M = Wrap-arg Θ (Fits-of Θ b bA) ⊢M

------------------------------------------------------------------------
-- §3d.  BlkAbst is NECESSARY: a machine-checked Wrap counterexample.
--
--   Δ✗ = [Y:=𝔹 , X:=ℕ]     Θ✗ = ↓X:=ℕ        (Y is blocked, and REVEALED)
--   W✗ = (7 ⟪ ↓Y:=𝔹 , ℕ ⟫) : ℕ               (its conceal names the blocked Y)
--
-- The redex types under ⊢′; the Wrap contractum does NOT, because the dual
-- reveals the blocked slot Y at the DUMMY rep ℕ, so `∋ 0 := 𝔹` is lost.
------------------------------------------------------------------------

Δ✗ : TCtx
Δ✗ = rvld `𝔹 ∷ rvld `ℕ ∷ []

Θ✗ : BCtx
Θ✗ = cnc 1 `ℕ ∷ []

W✗ : Term
W✗ = ($ 7) ⟪ cnc 0 `𝔹 ∷ [] , `ℕ ⟫

V✗ : Term
V✗ = ƛ `ℕ ∙ ` 0

_ : baseS Θ✗ Δ✗ ≡ blk ∷ ok ∷ []        -- slot 0 (Y) is blocked
_ = refl

_ : dualᵇ Θ✗ ≡ rvl `ℕ ∷ rvl `ℕ ∷ []    -- the blocked slot gets the DUMMY ℕ
_ = refl

_ : intOf′ (intOf′ Δ✗ Θ✗) (dualᵇ Θ✗) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl                               -- … whereas Δ✗ has  rvld 𝔹  at slot 0

⊢W✗ : Δ✗ ∣ [] ⊢′ W✗ ⦂ `ℕ
⊢W✗ = env′ (bwf↓′ here wf-𝔹 bwf[]′) sc-ℕ ⊢$′

⊢redex✗ : Δ✗ ∣ [] ⊢′ (V✗ ⟪ Θ✗ , `ℕ ⇒ `ℕ ⟫) · W✗ ⦂ `ℕ
⊢redex✗ = ⊢·′ (env′ (bwf↓′ (skip-rvld here) wf-ℕ bwf[]′)
                    (sc-⇒ sc-ℕ sc-ℕ)
                    (⊢ƛ′ wf-ℕ (⊢`′ here)))
              ⊢W✗

-- 2026-09-04 (Decision 2 revised): Wrap consumes the ƛ, so the contractum is
-- the substituted body — here V✗'s body is ` 0, i.e. the dual-wrapped
-- argument itself.  The refutation is unchanged in substance (one ⊢·′ layer
-- fewer): W✗'s conceal ↓Y:=𝔹 has no knowledge to match in the dual's
-- interior, which reveals the blocked Y at the DUMMY rep ℕ.
contractum✗ : Term
contractum✗ = (W✗ ⟪ dualᵇ Θ✗ , renameᵗ (swapᵇ Θ✗) `ℕ ⟫) ⟪ Θ✗ , `ℕ ⟫

_ : (V✗ ⟪ Θ✗ , `ℕ ⇒ `ℕ ⟫) · W✗ -→ contractum✗
_ = Wrap (V-⟪⟫ V-$)

¬⊢contractum✗ : ¬ (Δ✗ ∣ [] ⊢′ contractum✗ ⦂ `ℕ)
¬⊢contractum✗ (env′ _ _ (env′ _ _ (env′ (bwf↓′ () _ _) _ _)))

-- and indeed the invariant fails on Δ✗ (slot 0 is rvld 𝔹, not abst)
¬fits✗ : ¬ (Fits Θ✗ (cmax Θ✗) 0 Δ✗)
¬fits✗ (fitsR () _)

-- the same pair REFUTES ⊢retag for ⊢′: equal lengths, typable on the left,
-- not on the right.  Length-retagging must be replaced by ≼-retagging.
_ : length Δ✗ ≡ length (rvld `ℕ ∷ rvld `ℕ ∷ [])
_ = refl

¬⊢retag-len : ¬ ((rvld `ℕ ∷ rvld `ℕ ∷ []) ∣ [] ⊢′ W✗ ⦂ `ℕ)
¬⊢retag-len (env′ (bwf↓′ () _ _) _ _)

------------------------------------------------------------------------
-- §3e.  The positive case: BReduction's mixed Wrap example (one reveal, one
-- conceal), 1a-ified — X is now REVEALED at ℕ in the exterior.
------------------------------------------------------------------------

Δm′ : TCtx                       -- Y (Λ-bound, blocked) , X:=ℕ
Δm′ = abst ∷ rvld `ℕ ∷ []

Θm : BCtx                        -- ↑Z:=ℕ , ↓X:=ℕ
Θm = rvl `ℕ ∷ cnc 1 `ℕ ∷ []

_ : intOf′ Δm′ Θm ≡ rvld `ℕ ∷ []
_ = refl

_ : intOf′ (intOf′ Δm′ Θm) (dualᵇ Θm) ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

fitsm : Fits Θm (cmax Θm) 0 Δm′
fitsm = fitsA (fitsR refl fits0)

≼m : Δm′ ≼ intOf′ (intOf′ Δm′ Θm) (dualᵇ Θm)
≼m = dual-≼ Δm′ Θm fitsm

⊢redex-m : Δm′ ∣ [] ⊢′ ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3) ⦂ `ℕ
⊢redex-m =
  ⊢·′ (env′ (bwf↑′ wf-ℕ (bwf↓′ (skip-abst here) wf-ℕ bwf[]′))
            (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
            (⊢ƛ′ (wf-var here-rvld) (⊢`′ here)))
      ⊢$′

-- 2026-09-04 (Decision 2 revised): Wrap consumes the ƛ; its body is ` 0, so
-- the contractum is the dual-wrapped argument under the original boundary.
_ : ((ƛ ` 0 ∙ ` 0) ⟪ Θm , ` 0 ⇒ ` 0 ⟫) · ($ 3)
    -→ (($ 3) ⟪ dualᵇ Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫
_ = Wrap V-$

⊢contractum-m :
  Δm′ ∣ [] ⊢′ (($ 3) ⟪ dualᵇ Θm , ` 2 ⟫) ⟪ Θm , ` 0 ⟫ ⦂ `ℕ
⊢contractum-m =
  env′ (bwf↑′ wf-ℕ (bwf↓′ (skip-abst here) wf-ℕ bwf[]′))
       (sc-var hereᵒ)
       (env′ (bwf↑′ wf-ℕ (bwf↑′ wf-ℕ (bwf↓′ here wf-ℕ bwf[]′)))
             (sc-var (thereᵒ (thereᵒ hereᵒ)))
             ⊢$′)

-- BUT: the blocked slot Y, `abst` in Δm′, becomes `rvld ℕ` in the dual's
-- interior — so BlkAbst is NOT preserved by Wrap.  Any later boundary
-- inside the argument that blocks slot 0 lands in §3d's situation.
_ : AbstAt Δm′ 0
_ = ab-here

¬abst-after : ¬ (AbstAt (intOf′ (intOf′ Δm′ Θm) (dualᵇ Θm)) 0)
¬abst-after ()

------------------------------------------------------------------------
-- §3f.  The other half of Wrap's obligation is FREE under 1a: the dual's
-- conceals are Θ's reveals at Θ's own reps, and intOf′ PUT those reps into
-- the dual's exterior.  So bwf↓′'s new premise is discharged by construction.
------------------------------------------------------------------------

revEnts-∋ʳ : ∀ Θ (Φ : TCtx) j → j < revs Θ → (revEnts Θ ++ Φ) ∋ j := ρᵇ Θ j
revEnts-∋ʳ []            Φ j       ()
revEnts-∋ʳ (rvl A ∷ Θ)   Φ zero    lt       = here
revEnts-∋ʳ (rvl A ∷ Θ)   Φ (suc j) (s≤s lt) = skip-rvld (revEnts-∋ʳ Θ Φ j lt)
revEnts-∋ʳ (cnc X A ∷ Θ) Φ j       lt       = revEnts-∋ʳ Θ Φ j lt

dual-cnc-ok : ∀ Θ (Δ : TCtx) j → j < revs Θ → intOf′ Δ Θ ∋ j := ρᵇ Θ j
dual-cnc-ok Θ Δ j lt = revEnts-∋ʳ Θ (dropN (cmax Θ) Δ) j lt

-- instance: the ↓Z:=ℕ of dualᵇ Θm, licensed in intOf′ Δm′ Θm
_ : intOf′ Δm′ Θm ∋ 0 := `ℕ
_ = dual-cnc-ok Θm Δm′ 0 (s≤s z≤n)

------------------------------------------------------------------------
-- §4.  Merge (Decision 3): Cancel's agreement is FREE under 1a.
--
-- In (V ⟪ Θ₁ , B₁ ⟫) ⟪ Θ₂ , B₂ ⟫ the inner boundary is typed at the exterior
-- intOf′ Δ Θ₂, whose slot X (< revs Θ₂) is `rvld (Θ₂'s X-th reveal rep)` —
-- and that rep is exactly ρᵇ Θ₂ X.  So a conceal ↓X:=A of Θ₁ against the
-- reveal ↑X:=A′ of Θ₂ has A ≡ A′ by bwf↓′ inversion alone.
------------------------------------------------------------------------

revEnts-∋ : ∀ Θ (Φ : TCtx) X A → X < revs Θ
          → (revEnts Θ ++ Φ) ∋ X := A → ρᵇ Θ X ≡ A
revEnts-∋ []            Φ X       A ()  p
revEnts-∋ (rvl B ∷ Θ)   Φ zero    A lt  here          = refl
revEnts-∋ (rvl B ∷ Θ)   Φ (suc X) A (s≤s lt) (skip-rvld p) =
  revEnts-∋ Θ Φ X A lt p
revEnts-∋ (cnc Y B ∷ Θ) Φ X       A lt  p = revEnts-∋ Θ Φ X A lt p

cancel-agree : ∀ Θ₂ (Δ : TCtx) X A → X < revs Θ₂
             → intOf′ Δ Θ₂ ∋ X := A → ρᵇ Θ₂ X ≡ A
cancel-agree Θ₂ Δ X A lt p = revEnts-∋ Θ₂ (dropN (cmax Θ₂) Δ) X A lt p

-- The Merge/Cancel obligation, as it would be discharged: from the inner
-- boundary's derivation alone.
cancel-of-bwf : ∀ {Δ Ψ} Θ₁ Θ₂ X → X < revs Θ₂
              → (intOf′ Δ Θ₂) ∣ Ψ ⊢ᵇ′ Θ₁ → isConc X Θ₁ ≡ true
              → ρᵇ Θ₂ X ≡ repOf X Θ₁
cancel-of-bwf {Δ} Θ₁ Θ₂ X lt b q =
  cancel-agree Θ₂ Δ X (repOf X Θ₁) lt (bwf-repOf Θ₁ b X q)

-- instance: Example 8's T2 — the dual's ↓X:=ℕ against Θr's ↑X:=ℕ
_ : ρᵇ Θr 0 ≡ `ℕ
_ = cancel-of-bwf {Δ = []} {Ψ = []} Θc Θr 0 (s≤s z≤n)
                  (bwf↓′ here wf-ℕ bwf[]′) refl

-- instance: Example 3's tower shape — an inner conceal of the outer reveal
-- variable, at a NON-ℕ rep (𝔹), still forced to agree
_ : ρᵇ (rvl `𝔹 ∷ []) 0 ≡ `𝔹
_ = cancel-of-bwf {Δ = []} {Ψ = []} (cnc 0 `𝔹 ∷ []) (rvl `𝔹 ∷ []) 0 (s≤s z≤n)
                  (bwf↓′ here wf-𝔹 bwf[]′) refl

-- and `bad` is exactly the failure of this agreement (§1): ℕ ≢ ∀ZZ
¬cancel-bad : ¬ (ρᵇ (rvl ∀ZZ ∷ []) 0 ≡ `ℕ)
¬cancel-bad ()

------------------------------------------------------------------------
-- §5.  THE HOLE IN OPTION 1a AS STATED.
--
-- bwf↓′'s premise `Δ ∋ X := A` compares two different readings of A:
--   * the stored entry is read in the boundary's EXTERIOR (that is what
--     intOf′ puts there — a knowledge entry, DECISIONS.md's "first cost");
--   * the conceal's rep A is read in the INTERIOR intOf′ Δ Θ, which is the
--     exterior with `revs Θ` reveal entries PREPENDED and `cmax Θ` dropped.
-- The two index spaces differ by the reveal prefix, so the syntactic
-- comparison is off by `revs Θ` — and the gap is exploitable.
--
--   Δb  = [X:=P , P:=∀Z.Z→Z]        (X's rep is the DEEPER variable P)
--   Θb  = ↑Z:=ℕ , ↓X:=` 0
--
-- `↓X:=` 0` passes 1a's check (Δb ∋ 0 := ` 0) because ` 0 also SPELLS P in
-- the exterior — but inside, ` 0 is the fresh reveal Z (rep ℕ).  So the
-- boundary converts an "ℕ" into an "∀Z.Z→Z", exactly what §1 forbade.
------------------------------------------------------------------------

Δb₁ : TCtx                       -- P := ∀Z.Z→Z
Δb₁ = rvld ∀ZZ ∷ []

Δb : TCtx                        -- X := P , P := ∀Z.Z→Z
Δb = rvld (` 0) ∷ rvld ∀ZZ ∷ []

Θb : BCtx                        -- ↑Z:=ℕ , ↓X:=` 0
Θb = rvl `ℕ ∷ cnc 0 (` 0) ∷ []

Ψb : TCtx
Ψb = rvld `ℕ ∷ rvld ∀ZZ ∷ []

_ : intOf′ Δb Θb ≡ Ψb
_ = refl

-- the exterior knowledge: X's rep is ` 0 read in Δb ↓ 0 = [P:=∀Z.Z→Z] = P
_ : Δb ∋ 0 := ` 0
_ = here

_ : Δb ↓ 0 ≡ Δb₁
_ = refl

-- the INTERIOR reading of that same ` 0 is the reveal variable Z (rep ℕ) …
_ : Ψb ∋ 0 := `ℕ
_ = here

-- … and that is what γᵇ uses: the concealed slot's interior image is ` 0 = Z
_ : substᵗ (γᵇ Θb) (` 1) ≡ ` 0
_ = refl

_ : substᵗ (ρᵇ Θb) (` 1) ≡ ` 0     -- exterior image: X
_ = refl

inner₂ : Term
inner₂ = ($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫

mid₂ : Term
mid₂ = inner₂ ⟪ Θb , ` 1 ⟫

bad₂ : Term
bad₂ = (mid₂ ⟪ rvl (` 0) ∷ [] , ` 0 ⟫) ⟪ rvl ∀ZZ ∷ [] , ` 0 ⟫

⊢inner₂ : Ψb ∣ [] ⊢′ inner₂ ⦂ ` 0
⊢inner₂ = env′ (bwf↓′ here wf-ℕ bwf[]′) (sc-var hereᵒ) ⊢$′

⊢mid₂ : Δb ∣ [] ⊢′ mid₂ ⦂ ` 0
⊢mid₂ = env′ (bwf↑′ wf-ℕ (bwf↓′ here (wf-var here-rvld) bwf[]′))
             (sc-var (thereᵒ hereᵒ))
             ⊢inner₂

-- closed, well typed under ⊢′, a VALUE, and its boundary type is a reveal
-- VARIABLE — the §5a stuck configuration, which 1a was supposed to kill.
⊢bad₂ : [] ∣ [] ⊢′ bad₂ ⦂ ∀ZZ
⊢bad₂ = env′ (bwf↑′ ⊢∀ZZ bwf[]′) (sc-var hereᵒ)
             (env′ (bwf↑′ (wf-var here-rvld) bwf[]′) (sc-var hereᵒ) ⊢mid₂)

bad₂-value : Value bad₂
bad₂-value = V-⟪⟫ (V-⟪⟫ (V-⟪⟫ (V-⟪⟫ V-$)))

bad₂-B₀-not-∀ : ¬ (Σ Ty λ T → (` 0) ≡ `∀ T)
bad₂-B₀-not-∀ (T , ())

⊢bad₂-redex : [] ∣ [] ⊢′ bad₂ ·[ ` 0 ⇒ ` 0 , `ℕ ] ⦂ (`ℕ ⇒ `ℕ)
⊢bad₂-redex = ⊢·[]′ ⊢bad₂ wf-ℕ

-- … and it is STUCK: no rule applies (TyWrap wants `∀ at the boundary type,
-- and every interior is already a value).
¬-→-$7 : ∀ {N} → ¬ (($ 7) -→ N)
¬-→-$7 ()

¬-→-inner₂ : ∀ {N} → ¬ (inner₂ -→ N)
¬-→-inner₂ (ξ-⟪⟫ st) = ¬-→-$7 st

¬-→-mid₂ : ∀ {N} → ¬ (mid₂ -→ N)
¬-→-mid₂ (ξ-⟪⟫ st) = ¬-→-inner₂ st

¬-→-bad₂ : ∀ {N} → ¬ (bad₂ -→ N)
¬-→-bad₂ (ξ-⟪⟫ (ξ-⟪⟫ st)) = ¬-→-mid₂ st

bad₂-stuck : ∀ {N} → ¬ (bad₂ ·[ ` 0 ⇒ ` 0 , `ℕ ] -→ N)
bad₂-stuck (ξ-·[] st) = ¬-→-bad₂ st

------------------------------------------------------------------------
-- §5c.  The repair.  License the conceal rep by the exterior knowledge
-- TRANSPORTED into the interior: A₀ (read in Δ ↓ X) sits at boundary-frame
-- index  revs Θ + suc X + i,  and γᵇ Θ carries the frame into the interior.
--
--   (bwf-↓)  Γ ∋ Y:=A₀    Ψ ⊢ A    A = (↑A₀)[γΘ]    Γ ∣ Ψ ⊢ Θ
--            ⟹  Γ ∣ Ψ ⊢ ↓Y:=A , Θ
--
-- Note this must be read with the WHOLE Θ (γᵇ Θ, not the tail's), so bwf
-- becomes a whole-boundary judgement (or carries Θ as a parameter).
------------------------------------------------------------------------

liftRep : BCtx → ℕ → Ty → Ty
liftRep Θ X A₀ = renameᵗ (λ i → revs Θ + suc X + i) A₀

grounded : BCtx → ℕ → Ty → Ty → Set
grounded Θ X A A₀ = A ≡ substᵗ (γᵇ Θ) (liftRep Θ X A₀)

-- it REJECTS bad₂ (the required rep is ` 1 = P's interior image, not ` 0 = Z)
_ : substᵗ (γᵇ Θb) (liftRep Θb 0 (` 0)) ≡ ` 1
_ = refl

¬grounded-bad₂ : ¬ (grounded Θb 0 (` 0) (` 0))
¬grounded-bad₂ ()

-- it ACCEPTS every conceal of §2 and §3e (closed reps) …
_ : grounded Θ8′ 1 `ℕ `ℕ
_ = refl

_ : grounded Θn 1 `ℕ `ℕ
_ = refl

_ : grounded Θm 1 `ℕ `ℕ
_ = refl

_ : grounded Θc 0 `ℕ `ℕ
_ = refl

-- … and it accepts a NON-closed rep that is genuinely aligned: Δ = [Y:=X→X ,
-- X:=ℕ], Θ = ↓Y:=(X→X) — no reveals, so the frame shift is exactly the drop.
_ : grounded (cnc 0 (` 0 ⇒ ` 0) ∷ []) 0 (` 0 ⇒ ` 0) (` 0 ⇒ ` 0)
_ = refl

------------------------------------------------------------------------
-- §5d.  For contrast: under the repaired premise the `Ψ ⊢ A` premise is
-- derivable in spirit (A is the γᵇ-image of a well-formed A₀), so the
-- redundancy of §0's two premises disappears.  Dropping `Ψ ⊢ A` from the
-- UNREPAIRED bwf↓′ would be unsound in the other direction as well: with
-- reveals present, `Δ ∋ X := A` alone does not make A an interior type.
------------------------------------------------------------------------

-- Δ ∋ 1 := ` 0 holds, and ` 0 IS an interior type, but they name different
-- variables: in the exterior ` 0 (below slot 1) is slot 2; in the interior
-- it is the reveal variable.
Δs : TCtx
Δs = abst ∷ rvld (` 0) ∷ abst ∷ []

Θs : BCtx
Θs = rvl `ℕ ∷ cnc 1 (` 0) ∷ []

_ : Δs ∋ 1 := ` 0
_ = skip-abst here

_ : intOf′ Δs Θs ≡ rvld `ℕ ∷ abst ∷ []
_ = refl

_ : intOf′ Δs Θs ⊢ ` 0
_ = wf-var here-rvld

-- the repaired premise sees through it: the required rep is ` 1, not ` 0
_ : substᵗ (γᵇ Θs) (liftRep Θs 1 (` 0)) ≡ ` 1
_ = refl

¬grounded-Δs : ¬ (grounded Θs 1 (` 0) (` 0))
¬grounded-Δs ()
