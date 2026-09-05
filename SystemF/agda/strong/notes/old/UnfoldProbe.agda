module strong.notes.old.UnfoldProbe where

-- SUPERSEDED 2026-09-04 by the dual-conceal licence install
-- (notes/DualLicenseDesign.md): unfSub / unfoldae are live in
-- strong.Unfold, and (a') is settled -- the design keeps RAW entries.

-- ADVERSARIAL PROBE of candidate (a′) — "unfold knowledge AT ENTRY BIRTH"
-- (notes/DECISIONS.md, "CANDIDATE (a) SHARPENED TO (a′)").
--
-- Jeremy's worry: "unfolding erases information and I'm worried that unfolded
-- types won't match types that are still abstracted, causing us problems down
-- the line."  This file tries to BREAK (a′) — to find refl-checkable
-- mismatches between unfolded and abstracted forms — and proves the small
-- theorems that say why not, where it cannot.
--
-- The verdict is in the closing section (§7).  In one line: the worry is
-- REAL and lands at ONE site, the dual's conceal-of-a-reveal block
-- (cncOfRevs / the Reversal premise), because (a′) unfolds the interior
-- ENTRY while SIMULTANEITY keeps the reveal's stored rep — and hence the
-- external face ρᵇ — RAW.  Everything else checked here is safe, and two of
-- the standing obligations (Merge's middle type, the dfree guard) improve.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s;
                            _⊔_; _<?_; _≤?_)
open import Data.Nat.Properties using (_≟_; ≤-refl; ≤-trans; m≤m+n;
                                       ≤-stepsʳ; m+n∸m≡n)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Relation.Nullary using (¬_; Dec; yes; no; ⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)
open import strong.Types
open import strong.TypeSubst
  using (subst-cong; rename-cong; subst-id; rename-subst;
         rename-rename-commute; rename-subst-commute)
open import strong.Context hiding (Δ; Γ; A; B; C; X; Y; Z; x; E)
open import strong.Weakening using (∋:=-⊢)
open import strong.Boundary
open import strong.BReduction
  using (repOf; entAt; copyRep; entᴳ; rvlsᴳ; cncOfRevs; dualᴳ;
         swapᵇ; swapIdx; shiftReps; renᴮ; intRen; liftⁿ; restrictRen;
         Mono; _≼_; ≼[]; ≼abst; ≼rvld; ≼-refl; γᵇ-dual-ty; ρᵇ-dual-ty)
open import strong.DualDef using (DualCnc; DualInt; DualRep)

private
  variable
    Γ Δ Ψ : TCtx
    A B T : Ty
    X i j : ℕ
    Θ Ξ : BCtx

------------------------------------------------------------------------
-- §1.  THE UNFOLDING OPERATOR, THE (a′) ENTRY MAP, AND KNF
------------------------------------------------------------------------

-- unfSub Γ : the fully-resolved image of each variable of Γ, as a Γ-type.
-- The recursion is on the CONTEXT: an entry `rvld B` stores a type over its
-- own TAIL (Context.agda's telescope convention), so B is unfolded in the
-- tail and then shifted back up by one.  Well-founded for free.
unfSub : TCtx → Substᵗ
unfSub []           X       = ` X
unfSub (abst   ∷ Γ) zero    = ` zero
unfSub (abst   ∷ Γ) (suc X) = ⇑ᵗ (unfSub Γ X)
unfSub (rvld B ∷ Γ) zero    = ⇑ᵗ (substᵗ (unfSub Γ) B)
unfSub (rvld B ∷ Γ) (suc X) = ⇑ᵗ (unfSub Γ X)

-- unfoldᵉ Γ A : Zdancewic's Δ̄ applied to A — every revealed variable
-- replaced by its (recursively unfolded) representation.
unfoldᵉ : TCtx → Ty → Ty
unfoldᵉ Γ A = substᵗ (unfSub Γ) A

-- sanity: chained knowledge collapses (Pc's W:=Y over Y:=𝔹 becomes 𝔹)
private
  Γch : TCtx                      -- W:=Y (0) , Y:=𝔹 (1) , X:=ℕ (2)
  Γch = rvld (` 0) ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

  _ : unfoldᵉ Γch (` 0) ≡ `𝔹
  _ = refl

  _ : unfoldᵉ Γch (` 0 ⇒ ` 2) ≡ (`𝔹 ⇒ `ℕ)
  _ = refl

  -- an abstract variable is left alone; unfolding is the identity on it
  _ : unfoldᵉ (abst ∷ rvld `𝔹 ∷ []) (` 0) ≡ ` 0
  _ = refl

------------------------------------------------------------------------
-- The (a′) entry computation.  ⟦·⟧ᵁ is today's ⟦·⟧ᵉ (Boundary.agda) with
-- the reveal's rep UNFOLDED through the ambient Γ first.  Boundary.agda is
-- untouched: intOfᵁ is a local variant of intOf that takes the ambient's
-- entries into account.
------------------------------------------------------------------------

⟦_⟧ᵁ : TCtx → BCtx → ℕ → Ty → TyEntry
⟦ Γ ⟧ᵁ Θ j A = ⟦ Θ ⟧ᵉ j (unfoldᵉ Γ A)

revEntsᵁ : TCtx → BCtx → ℕ → BCtx → TCtx
revEntsᵁ Γ Θ j []            = []
revEntsᵁ Γ Θ j (rvl A ∷ Ξ)   = ⟦ Γ ⟧ᵁ Θ j A ∷ revEntsᵁ Γ Θ (suc j) Ξ
revEntsᵁ Γ Θ j (rvl⋆ ∷ Ξ)    = abst ∷ revEntsᵁ Γ Θ (suc j) Ξ
revEntsᵁ Γ Θ j (cnc X A ∷ Ξ) = revEntsᵁ Γ Θ j Ξ

-- The kept tail is copied unchanged: under UNIFORM (a′) its entries were
-- already born unfolded, so no second pass is needed (§5, KNF-dropN).
intOfᵁ : TCtx → BCtx → TCtx
intOfᵁ Γ Θ = revEntsᵁ Γ Θ 0 Θ ++ dropN (cmax Θ) Γ

------------------------------------------------------------------------
-- KNOWLEDGE NORMAL FORM.  A type is in KNF for Γ when it names only slots
-- that Γ leaves ABSTRACT — then no knowledge of Γ can resolve it further,
-- i.e. it is unfold-FIXED (knf-fix below).  Reusing Boundary.Scoped keeps
-- the ∀-case bookkeeping (subst-cong-sc) for free.
------------------------------------------------------------------------

absSlots : TCtx → SCtx           -- abstract slot ↦ ok, knowledge slot ↦ blk
absSlots []           = []
absSlots (abst   ∷ Γ) = ok  ∷ absSlots Γ
absSlots (rvld B ∷ Γ) = blk ∷ absSlots Γ

okS : TCtx → SCtx                -- every slot in scope
okS []      = []
okS (E ∷ Γ) = ok ∷ okS Γ

KNFᵗ : TCtx → Ty → Set
KNFᵗ Γ A = Scoped (absSlots Γ) A

-- KNF Γ : every rvld entry of Γ is in KNF over its own tail (hence
-- unfold-fixed there).  This is the shape (a′) claims to maintain.
data KNF : TCtx → Set where
  knf[]   : KNF []
  knfabst : KNF Γ → KNF (abst ∷ Γ)
  knfrvld : KNF Γ → KNFᵗ Γ B → KNF (rvld B ∷ Γ)

private
  -- Γch is NOT in KNF (W's rep is the knowledge variable Y) …
  ¬KNF-Γch : ¬ (KNF Γch)
  ¬KNF-Γch (knfrvld _ (sc-var ()))

  -- … and its (a′) form is, with every rep closed
  Γch′ : TCtx
  Γch′ = rvld `𝔹 ∷ rvld `𝔹 ∷ rvld `ℕ ∷ []

  KNF-Γch′ : KNF Γch′
  KNF-Γch′ = knfrvld (knfrvld (knfrvld knf[] sc-ℕ) sc-𝔹) sc-𝔹

------------------------------------------------------------------------
-- §2.  UNFOLDING LANDS IN KNF, AND KNF IS A FIXPOINT
--
-- These are the two theorems that make "unfold at birth" a normal form:
-- unfoldᵉ always produces a type naming only ABSTRACT slots, and such a
-- type is unfold-fixed.  Idempotence is the corollary — the reason a second
-- unfolding (in the dual, in Merge, in a later reveal) can never disagree
-- with the first.
------------------------------------------------------------------------

sc-ren : ∀ {Ψ₁ Ψ₂ : SCtx} {ρ A} → Scoped Ψ₁ A
       → (∀ X → Ψ₁ ∋ok X → Ψ₂ ∋ok ρ X) → Scoped Ψ₂ (renameᵗ ρ A)
sc-ren (sc-var p)    h = sc-var (h _ p)
sc-ren sc-ℕ          h = sc-ℕ
sc-ren sc-𝔹          h = sc-𝔹
sc-ren (sc-⇒ sA sB)  h = sc-⇒ (sc-ren sA h) (sc-ren sB h)
sc-ren {ρ = ρ} (sc-∀ sA) h = sc-∀ (sc-ren sA h-ext)
  where
    h-ext : ∀ X → (ok ∷ _) ∋ok X → (ok ∷ _) ∋ok extᵗ ρ X
    h-ext zero    hereᵒ      = hereᵒ
    h-ext (suc X) (thereᵒ p) = thereᵒ (h X p)

sc-⇑ : ∀ {Ψ₁ : SCtx} {s A} → Scoped Ψ₁ A → Scoped (s ∷ Ψ₁) (⇑ᵗ A)
sc-⇑ sA = sc-ren sA (λ X p → thereᵒ p)

sc-subst : ∀ {Ψ₁ Ψ₂ : SCtx} {σ A} → Scoped Ψ₁ A
         → (∀ X → Ψ₁ ∋ok X → Scoped Ψ₂ (σ X)) → Scoped Ψ₂ (substᵗ σ A)
sc-subst (sc-var p)   h = h _ p
sc-subst sc-ℕ         h = sc-ℕ
sc-subst sc-𝔹         h = sc-𝔹
sc-subst (sc-⇒ sA sB) h = sc-⇒ (sc-subst sA h) (sc-subst sB h)
sc-subst {σ = σ} (sc-∀ sA) h = sc-∀ (sc-subst sA h-ext)
  where
    h-ext : ∀ X → (ok ∷ _) ∋ok X → Scoped (ok ∷ _) (extsᵗ σ X)
    h-ext zero    hereᵒ      = sc-var hereᵒ
    h-ext (suc X) (thereᵒ p) = sc-⇑ (h X p)

okS-∋ok : ∀ (Γ₁ : TCtx) {X} → Γ₁ ∋tv X → okS Γ₁ ∋ok X
okS-∋ok (abst   ∷ Γ₁) here-abst     = hereᵒ
okS-∋ok (rvld B ∷ Γ₁) here-rvld     = hereᵒ
okS-∋ok (abst   ∷ Γ₁) (skip-abst p) = thereᵒ (okS-∋ok Γ₁ p)
okS-∋ok (rvld B ∷ Γ₁) (skip-rvld p) = thereᵒ (okS-∋ok Γ₁ p)

∋ok-okS : ∀ (Γ₁ : TCtx) {X} → okS Γ₁ ∋ok X → Γ₁ ∋tv X
∋ok-okS (abst   ∷ Γ₁) hereᵒ      = here-abst
∋ok-okS (rvld B ∷ Γ₁) hereᵒ      = here-rvld
∋ok-okS (abst   ∷ Γ₁) (thereᵒ p) = skip-abst (∋ok-okS Γ₁ p)
∋ok-okS (rvld B ∷ Γ₁) (thereᵒ p) = skip-rvld (∋ok-okS Γ₁ p)

wf→sc : ∀ {Γ₁ : TCtx} {A} → Γ₁ ⊢ A → Scoped (okS Γ₁) A
wf→sc {Γ₁} (wf-var p)   = sc-var (okS-∋ok Γ₁ p)
wf→sc wf-ℕ              = sc-ℕ
wf→sc wf-𝔹              = sc-𝔹
wf→sc (wf-⇒ wA wB)      = sc-⇒ (wf→sc wA) (wf→sc wB)
wf→sc (wf-∀ wA)         = sc-∀ (wf→sc wA)

-- every image of unfSub names only ABSTRACT slots (needs ⊢ Γ, so that each
-- stored rep is well scoped in its own tail)
unfSub-sc : ∀ (Γ₁ : TCtx) → ⊢ Γ₁ → ∀ {X} → Γ₁ ∋tv X
          → KNFᵗ Γ₁ (unfSub Γ₁ X)
unfSub-sc (abst   ∷ Γ₁) (⊢abst wΓ)    here-abst     = sc-var hereᵒ
unfSub-sc (abst   ∷ Γ₁) (⊢abst wΓ)    (skip-abst p) =
  sc-⇑ (unfSub-sc Γ₁ wΓ p)
unfSub-sc (rvld B ∷ Γ₁) (⊢rvld wΓ wB) here-rvld     =
  sc-⇑ (sc-subst (wf→sc wB)
                 (λ X p → unfSub-sc Γ₁ wΓ (∋ok-okS Γ₁ p)))
unfSub-sc (rvld B ∷ Γ₁) (⊢rvld wΓ wB) (skip-rvld p) =
  sc-⇑ (unfSub-sc Γ₁ wΓ p)

-- THEOREM (unfolding normalises).  unfoldᵉ Γ A is in KNF for Γ.
unf-scoped : ∀ (Γ₁ : TCtx) → ⊢ Γ₁ → ∀ {A} → Γ₁ ⊢ A → KNFᵗ Γ₁ (unfoldᵉ Γ₁ A)
unf-scoped Γ₁ wΓ wA =
  sc-subst (wf→sc wA) (λ X p → unfSub-sc Γ₁ wΓ (∋ok-okS Γ₁ p))

-- THEOREM (KNF is unfold-fixed).  Nothing in Γ can resolve a KNF type.
unfSub-id : ∀ (Γ₁ : TCtx) {X} → absSlots Γ₁ ∋ok X → unfSub Γ₁ X ≡ ` X
unfSub-id (abst   ∷ Γ₁) hereᵒ      = refl
unfSub-id (abst   ∷ Γ₁) (thereᵒ p) = cong ⇑ᵗ (unfSub-id Γ₁ p)
unfSub-id (rvld B ∷ Γ₁) (thereᵒ p) = cong ⇑ᵗ (unfSub-id Γ₁ p)

knf-fix : ∀ (Γ₁ : TCtx) {A} → KNFᵗ Γ₁ A → unfoldᵉ Γ₁ A ≡ A
knf-fix Γ₁ {A} sA =
  trans (subst-cong-sc sA (λ X p → unfSub-id Γ₁ p)) (subst-id A)

-- COROLLARY (idempotence).  Unfolding twice is unfolding once — so a
-- SECOND unfolding, wherever it happens (in a dual, in a merge, at a later
-- reveal), can never disagree with the first.
unf-idem : ∀ (Γ₁ : TCtx) → ⊢ Γ₁ → ∀ {A} → Γ₁ ⊢ A
         → unfoldᵉ Γ₁ (unfoldᵉ Γ₁ A) ≡ unfoldᵉ Γ₁ A
unf-idem Γ₁ wΓ wA = knf-fix Γ₁ (unf-scoped Γ₁ wΓ wA)

-- the kept tail of a KNF context is KNF (so intOfᵁ's copied tail needs no
-- second pass)
KNF-dropN : ∀ n (Γ₁ : TCtx) → KNF Γ₁ → KNF (dropN n Γ₁)
KNF-dropN zero    Γ₁            k             = k
KNF-dropN (suc n) []            k             = knf[]
KNF-dropN (suc n) (abst   ∷ Γ₁) (knfabst k)   = KNF-dropN n Γ₁ k
KNF-dropN (suc n) (rvld B ∷ Γ₁) (knfrvld k _) = KNF-dropN n Γ₁ k

------------------------------------------------------------------------
-- §3.  THE ABSTRACTION BARRIER (site 6, and the engine of site 5)
--
-- An unfolded rep names only ABSTRACT slots (§2).  A boundary only ever
-- CONCEALS a REVEALED slot (that is bwf↓'s first premise).  Hence an
-- unfolded rep names no concealed slot, its reading is the plain kept-slot
-- map, and it lands ABOVE the whole reveal block — where the entry's own
-- down-shift dnT (suc j) cannot truncate it.  Two consequences:
--   * (a′)'s entries are never silently demoted to `abst` by the dfree
--     guard (agenda item 4 becomes vacuous — rd-dfree);
--   * the interior reading of an unfolded rep cannot reach a sibling
--     reveal variable, so the "conceal reps may mention reveals"
--     simultaneity clause never bites the knowledge column.
------------------------------------------------------------------------

⌊⌋-true : ∀ {P : Set} (d : Dec P) → P → ⌊ d ⌋ ≡ true
⌊⌋-true (yes _) p = refl
⌊⌋-true (no ¬p) p = ⊥-elim (¬p p)

⌊⌋-false : ∀ {P : Set} (d : Dec P) → ¬ P → ⌊ d ⌋ ≡ false
⌊⌋-false (yes p) ¬p = ⊥-elim (¬p p)
⌊⌋-false (no  _) ¬p = refl

∨-false-inv : ∀ (b₁ b₂ : Bool) → (b₁ ∨ b₂) ≡ false
            → (b₁ ≡ false) × (b₂ ≡ false)
∨-false-inv false false e = refl , refl
∨-false-inv false true  ()
∨-false-inv true  b₂    ()

∋:=-entAt : ∀ {Γ₁ : TCtx} {X A₀} → Γ₁ ∋ X := A₀ → entAt Γ₁ X ≡ rvld A₀
∋:=-entAt here            = refl
∋:=-entAt (skip-abst p)   = ∋:=-entAt p
∋:=-entAt (skip-rvld p)   = ∋:=-entAt p

absSlots-abst : ∀ (Γ₁ : TCtx) {i} → absSlots Γ₁ ∋ok i → entAt Γ₁ i ≡ abst
absSlots-abst (abst   ∷ Γ₁) hereᵒ      = refl
absSlots-abst (abst   ∷ Γ₁) (thereᵒ p) = absSlots-abst Γ₁ p
absSlots-abst (rvld B ∷ Γ₁) (thereᵒ p) = absSlots-abst Γ₁ p

rvld≢abst : ∀ {A₀} → rvld A₀ ≡ abst → ⊥
rvld≢abst ()

-- THE BARRIER.  A boundary conceals only revealed slots, so it never
-- conceals a slot an unfolded rep can name.
abs-not-conc : ∀ {Γ₁ Ψ₁ : TCtx} {Θ₁} Ξ₁ → Bwf Γ₁ Ψ₁ Θ₁ Ξ₁
             → ∀ {i} → entAt Γ₁ i ≡ abst → isConc i Ξ₁ ≡ false
abs-not-conc []            bwf[]              ea = refl
abs-not-conc (rvl A ∷ Ξ₁)  (bwf↑ _ b)         ea = abs-not-conc Ξ₁ b ea
abs-not-conc (rvl⋆ ∷ Ξ₁)   (bwf⋆ b)           ea = abs-not-conc Ξ₁ b ea
abs-not-conc {Γ₁} (cnc X A ∷ Ξ₁) (bwf↓ {A₀ = A₀} p _ _ b) {i} ea =
  trans (cong (_∨ isConc i Ξ₁) (⌊⌋-false (i ≟ X) i≢X))
        (abs-not-conc Ξ₁ b ea)
  where
    i≢X : ¬ (i ≡ X)
    i≢X refl = rvld≢abst (trans (sym (∋:=-entAt p)) ea)

-- an accessible slot that is not concealed is a KEPT slot
slotAt-kept : ∀ Θ₁ i → slotAt Θ₁ i ≡ ok → isConc i Θ₁ ≡ false
            → cmax Θ₁ ≤ i
slotAt-kept Θ₁ i eo ec with cmax Θ₁ ≤? i
slotAt-kept Θ₁ i eo ec | yes le = le
slotAt-kept Θ₁ i eo ec | no  gt with isConc i Θ₁ | ec
slotAt-kept Θ₁ i eo ec | no  gt | false | _ with eo
slotAt-kept Θ₁ i eo ec | no  gt | false | _ | ()

-- the reading of a kept, unconcealed slot: the plain interior slot map
rdSub-kept : ∀ Θ₁ i → isConc i Θ₁ ≡ false
           → rdSub Θ₁ i ≡ ` (revs Θ₁ + (i ∸ cmax Θ₁))
rdSub-kept Θ₁ i ec = go Θ₁ ec
  where
    go : ∀ Ξ₁ → isConc i Ξ₁ ≡ false
       → γcnc (revs Θ₁) (cmax Θ₁) Ξ₁ i ≡ ` (revs Θ₁ + (i ∸ cmax Θ₁))
    go []            ec' = refl
    go (rvl A ∷ Ξ₁)  ec' = go Ξ₁ ec'
    go (rvl⋆ ∷ Ξ₁)   ec' = go Ξ₁ ec'
    go (cnc X A ∷ Ξ₁) ec' with ∨-false-inv ⌊ i ≟ X ⌋ (isConc i Ξ₁) ec'
    go (cnc X A ∷ Ξ₁) ec' | e₁ , e₂ with X ≟ i
    go (cnc X A ∷ Ξ₁) ec' | e₁ , e₂ | yes refl with i ≟ i | e₁
    go (cnc X A ∷ Ξ₁) ec' | e₁ , e₂ | yes refl | yes _ | ()
    go (cnc X A ∷ Ξ₁) ec' | e₁ , e₂ | yes refl | no ¬e | _ = ⊥-elim (¬e refl)
    go (cnc X A ∷ Ξ₁) ec' | e₁ , e₂ | no  _    = go Ξ₁ e₂

-- THEOREM (the dfree guard is vacuous under (a′), pointwise).  Every slot
-- an unfolded rep can name reads to an index at or above the reveal block,
-- so dnT (suc j) loses nothing for any reveal position j.
rd-dfree : ∀ Θ₁ j i → isConc i Θ₁ ≡ false → j < revs Θ₁
         → dfree 0 (suc j) (rdSub Θ₁ i) ≡ true
rd-dfree Θ₁ j i ec lt
  rewrite rdSub-kept Θ₁ i ec =
  trans (cong (_∨ ⌊ suc j ≤? (revs Θ₁ + (i ∸ cmax Θ₁)) ⌋)
              (⌊⌋-false ((revs Θ₁ + (i ∸ cmax Θ₁)) <? 0) (λ ())))
        (⌊⌋-true (suc j ≤? (revs Θ₁ + (i ∸ cmax Θ₁)))
                 (≤-trans lt (m≤m+n (revs Θ₁) (i ∸ cmax Θ₁))))

-- the two halves together: the barrier as the install would use it
barrier : ∀ {Γ₁ Ψ₁ : TCtx} Θ₁ {i} → Γ₁ ∣ Ψ₁ ⊢ᵇ Θ₁
        → entAt Γ₁ i ≡ abst → slotAt Θ₁ i ≡ ok
        → (isConc i Θ₁ ≡ false) × (cmax Θ₁ ≤ i)
barrier Θ₁ {i} bwf ea eo =
  let ec = abs-not-conc Θ₁ bwf ea in ec , slotAt-kept Θ₁ i eo ec

------------------------------------------------------------------------
-- §4.  SITE 1 — TWO ROUTES TO THE SAME KNOWLEDGE
--
-- Γ1 = Y:=𝔹 (0) , V:=𝔹 (1).  W's knowledge arrives by a REVEAL ↑W:=Y whose
-- rep is the knowledge variable Y (this is what TyBeta mints from
-- (ΛW. …)[Y]); V's arrived directly.  Under (a′) both entries are 𝔹 and
-- every consumer agrees; under RAW entries the two routes are
-- distinguishable — and the chained one is strictly worse off.
------------------------------------------------------------------------

Γ1 : TCtx
Γ1 = rvld `𝔹 ∷ rvld `𝔹 ∷ []          -- Y:=𝔹 , V:=𝔹

ΘW : BCtx
ΘW = rvl (` 0) ∷ []                   -- ↑W:=Y

-- the two regimes, side by side (W is slot 0, Y slot 1, V slot 2)
Γ2ʳ Γ2ᵁ : TCtx
Γ2ʳ = rvld (` 0) ∷ rvld `𝔹 ∷ rvld `𝔹 ∷ []      -- W:=Y  (raw)
Γ2ᵁ = rvld `𝔹   ∷ rvld `𝔹 ∷ rvld `𝔹 ∷ []      -- W:=𝔹  ((a′))

_ : intOf  Γ1 ΘW ≡ Γ2ʳ
_ = refl

_ : intOfᵁ Γ1 ΘW ≡ Γ2ᵁ
_ = refl

-- ROUTE AGREEMENT under (a′): the chained slot W and the direct slot V hold
-- literally the same entry.
routes-agree : entAt Γ2ᵁ 0 ≡ entAt Γ2ᵁ 2
routes-agree = refl

-- … and NOT under raw entries: this is the route-dependence Jeremy fears,
-- and it is a property of the RAW regime.
¬routes-agree-raw : ¬ (entAt Γ2ʳ 0 ≡ entAt Γ2ʳ 2)
¬routes-agree-raw ()

------------------------------------------------------------------------
-- The comparison that CONSUMES the entries: a conceal minted from W's
-- knowledge against one minted from V's.  Θcv conceals both (cmax 3, so
-- the interior is empty and the read-back map is ` (3 + ·)).
------------------------------------------------------------------------

Θcv : BCtx
Θcv = cnc 0 `𝔹 ∷ cnc 2 `𝔹 ∷ []

-- under (a′) BOTH conceals are licensed, by the SAME rep 𝔹, by refl
cnc-W-a′ : Reversal Θcv 0 `𝔹 `𝔹
cnc-W-a′ = refl

cnc-V-a′ : Reversal Θcv 2 `𝔹 `𝔹
cnc-V-a′ = refl

-- under RAW entries, W (whose knowledge is the variable Y) cannot be
-- concealed by this boundary AT ALL — no rep reads back to ` 1, because the
-- read-back map lands at 3 + · .  V still can.  Route-dependence with teeth.
¬cnc-W-raw : ∀ A → ¬ (Reversal Θcv 0 A (` 0))
¬cnc-W-raw (` X)   ()
¬cnc-W-raw `ℕ      ()
¬cnc-W-raw `𝔹      ()
¬cnc-W-raw (A ⇒ B) ()
¬cnc-W-raw (`∀ A)  ()

cnc-V-raw : Reversal Θcv 2 `𝔹 `𝔹
cnc-V-raw = refl

------------------------------------------------------------------------
-- The other consumer: a DUAL rebuilding a context that holds both.  Θv
-- conceals V and blocks W and Y, so the dual must copy Γ2's own entries
-- for W and Y.  Under (a′) the rebuild is Γ2ᵁ ON THE NOSE; under raw the
-- chained entry for W trips the `dfree 0 k` guard, degrades to rvl⋆, and
-- the knowledge is LOST — DualInt fails, and not even up to _≼_.
------------------------------------------------------------------------

Θv : BCtx
Θv = cnc 2 `𝔹 ∷ []

_ : dualᴳ Γ2ᵁ Θv ≡ rvl `𝔹 ∷ rvl `𝔹 ∷ rvl `𝔹 ∷ []
_ = refl

dual-rebuild-a′ : intOfᵁ (intOfᵁ Γ2ᵁ Θv) (dualᴳ Γ2ᵁ Θv) ≡ Γ2ᵁ
dual-rebuild-a′ = refl

_ : dualᴳ Γ2ʳ Θv ≡ rvl⋆ ∷ rvl `𝔹 ∷ rvl `𝔹 ∷ []
_ = refl

¬dual-rebuild-raw : ¬ (intOf (intOf Γ2ʳ Θv) (dualᴳ Γ2ʳ Θv) ≡ Γ2ʳ)
¬dual-rebuild-raw ()

¬dual-rebuild-raw≼ : ¬ (Γ2ʳ ≼ intOf (intOf Γ2ʳ Θv) (dualᴳ Γ2ʳ Θv))
¬dual-rebuild-raw≼ ()

------------------------------------------------------------------------
-- §5.  SITE 2 — MERGE'S MIDDLE TYPE
--
-- MergeProbe's ¬⊕-intR pair (notes/old/MergeProbe.agda §2):
--   Θm₁ = ↑W:=Z (a reveal whose rep is Θb's reveal variable), Θm₂ = ↑Z:=ℕ,
--   and (refl-checked there)  Θm₁ ⊕ Θm₂ ≡ ↑W:=ℕ , ↑Z:=ℕ .
-- Nested, W's entry is the reveal variable Z; merged, it is ℕ — the
-- knowledge-carrying interiors did NOT compose, which is the standing
-- "retyping along unfolding" obligation on Merge.  Under (a′) the mismatch
-- DISAPPEARS: both are W:=ℕ.
------------------------------------------------------------------------

Θm₁ Θm₂ Θm₁₂ : BCtx
Θm₁  = rvl (` 0) ∷ []                  -- ↑W:=Z
Θm₂  = rvl `ℕ ∷ []                     -- ↑Z:=ℕ
Θm₁₂ = rvl `ℕ ∷ rvl `ℕ ∷ []            -- = Θm₁ ⊕ Θm₂  (MergeProbe §2)

-- the standing mismatch, on the RAW/refined reading
_ : intOf (intOf [] Θm₂) Θm₁ ≡ rvld (` 0) ∷ rvld `ℕ ∷ []
_ = refl

_ : intOf [] Θm₁₂ ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

¬⊕-int-raw : ¬ (intOf [] Θm₁₂ ≡ intOf (intOf [] Θm₂) Θm₁)
¬⊕-int-raw ()

-- … and its disappearance under (a′): the interiors compose ON THE NOSE
⊕-int-a′ : intOfᵁ [] Θm₁₂ ≡ intOfᵁ (intOfᵁ [] Θm₂) Θm₁
⊕-int-a′ = refl

_ : intOfᵁ (intOfᵁ [] Θm₂) Θm₁ ≡ rvld `ℕ ∷ rvld `ℕ ∷ []
_ = refl

------------------------------------------------------------------------
-- §6.  SITE 3 — CANCEL: EVERY CONSUMER OF A STORED REVEAL REP
--
-- (a′) unfolds the interior ENTRY of a reveal but — by the SIMULTANEITY
-- ruling — leaves the reveal's STORED REP, hence its external face ρᵇ,
-- RAW.  So (a′) creates an unfolded-vs-raw pair exactly where a consumer
-- compares the two.  The consumers of a stored reveal rep are:
--
--   (3a) ρᵇ, the external face                    — SAFE (§8: unchanged)
--   (3b) renᴮ, boundary renaming                  — SAFE for the rep
--        (it renames the rep by ρ, raw, exactly as today); the ENTRY's
--        transport is site 4 (§7), where the install's hypothesis is too
--        weak.
--   (3c) cncOfRevs, the dual's conceal-of-a-reveal — *** MISMATCH ***
--   (3d) bwf↓ for an ORDINARY conceal              — SAFE (Reversal-closed)
--
-- (3c) is the whole finding.  The dual must conceal each reveal variable of
-- Θ, and it has NO freedom in the rep: bwf-cncOfRevs forces the rep to be
-- ρᵇ Θ k, the stored (raw) one, and the Reversal premise then compares its
-- read-back against the interior ENTRY, which (a′) has unfolded.
--
-- The shape below is Pc's OWN next step: ΓPc = Y:=ℕ, ΘW = ↑W:=Y is what
-- TyBeta mints from ((ΛW. λu:X. g u) [Y]), and the resulting wrapper is
-- immediately applied to x — a Wrap redex whose dual is cncOfRevs 0 ΘW.
------------------------------------------------------------------------

-- (𝔹 is written ℕ here only because the term language has no boolean
-- literal; nothing depends on the base type.)
ΓPc : TCtx
ΓPc = rvld `ℕ ∷ rvld `ℕ ∷ []          -- Y:=ℕ (0) , X:=ℕ (1)

ΘWᵈ : BCtx
ΘWᵈ = cnc 0 (` 0) ∷ []                -- = dualᴳ ΓPc ΘW  (cmax ΘW = 0)

_ : dualᴳ ΓPc ΘW ≡ ΘWᵈ
_ = refl

_ : ρᵇ ΘW 0 ≡ ` 0                     -- the external face stays the RAW Y
_ = refl

_ : intOf  ΓPc ΘW ≡ rvld (` 0) ∷ ΓPc   -- raw entry   W:=Y
_ = refl

_ : intOfᵁ ΓPc ΘW ≡ rvld `ℕ ∷ ΓPc      -- (a′) entry  W:=𝔹
_ = refl

-- the obligation bwf-cncOfRevs imposes, verbatim (BReduction ~l.2194):
-- some knowledge A₀ in the dual's exterior whose lift the stored rep reads
-- back to.  RAW: discharged by refl.
DualCnc-raw : Σ Ty λ A₀ → (intOf ΓPc ΘW ∋ 0 := A₀)
                        × Reversal ΘWᵈ 0 (ρᵇ ΘW 0) A₀
DualCnc-raw = ` 0 , here , refl

-- *** THE COUNTEREXAMPLE ***  Under (a′) the entry is 𝔹, the stored rep
-- still reads back to the variable Y (` 1 in the interior), and NOTHING
-- discharges the obligation — the dual's conceal of W is unlicensed, so
-- Wrap's contractum does not type.  This is DualDef.DualCnc, refuted for
-- (a′) on a boundary for which it HOLDS today.
¬DualCnc-a′ : ¬ (Σ Ty λ A₀ → (intOfᵁ ΓPc ΘW ∋ 0 := A₀)
                           × Reversal ΘWᵈ 0 (ρᵇ ΘW 0) A₀)
¬DualCnc-a′ (A₀ , here , ())

-- the bare mismatch, isolated:  read-back ` 1  vs  unfolded knowledge 𝔹
_ : outRead ΘWᵈ (ρᵇ ΘW 0) ≡ ` 1
_ = refl

_ : upRep 0 `ℕ ≡ `ℕ
_ = refl

-- … and the redex it kills is well typed in BOTH regimes, so the failure is
-- in the CONTRACTUM.  ΘW is well formed over ΓPc (its rep is a plain
-- exterior type), the sealed identity's external face is Y⇒Y, and the body
-- types in the (a′) interior just as it does in the raw one.
⊢ΘW-a′ : ΓPc ∣ intOfᵁ ΓPc ΘW ⊢ᵇ ΘW
⊢ΘW-a′ = bwf↑ (wf-var here-rvld) bwf[]

⊢body-a′ : intOfᵁ ΓPc ΘW ∣ [] ⊢ (ƛ ` 0 ∙ ` 0)
                             ⦂ substᵗ (γᵇ ΘW) (` 0 ⇒ ` 0)
⊢body-a′ = ⊢ƛ (wf-var here-rvld) (⊢` here)

⊢sealed : ΓPc ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ ΘW , (` 0 ⇒ ` 0) ⟫ ⦂ (` 0 ⇒ ` 0)
⊢sealed = env (bwf↑ (wf-var here-rvld) bwf[])
              (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
              (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- HORN 2.  The obvious repair — let the dual conceal at the UNFOLDED rep
-- — breaks the INTERNAL FACE LAW instead.  γᵇ-dual-ty holds with the raw
-- rep and fails with the unfolded one, and the failure is precisely the
-- application's domain-vs-argument check: the argument arrives typed at the
-- still-abstracted Y, and the unfolded dual demands 𝔹.
------------------------------------------------------------------------

ΘWᵈ′ : BCtx
ΘWᵈ′ = cnc 0 `ℕ ∷ []                  -- the "unfolded dual"

face-raw : substᵗ (γᵇ (dualᴳ ΓPc ΘW)) (renameᵗ (swapᵇ ΘW) (` 0))
         ≡ substᵗ (ρᵇ ΘW) (` 0)
face-raw = γᵇ-dual-ty ΓPc (` 0) ΘW

¬face-unfolded : ¬ (substᵗ (γᵇ ΘWᵈ′) (renameᵗ (swapᵇ ΘW) (` 0))
                    ≡ substᵗ (ρᵇ ΘW) (` 0))
¬face-unfolded ()

-- the worst case at the level of TYPING.  argY is a closed-form value of
-- type Y over Γ1 (the shape any argument at a knowledge-variable type has:
-- a wrapper chain ending in a conceal).  It does NOT have type 𝔹, so the
-- unfolded dual cannot retype it: "retyping along unfolding" — Merge's open
-- obligation — reappears inside Wrap.
argY : Term
argY = ($ 3) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫

⊢argY : ΓPc ∣ [] ⊢ argY ⦂ ` 0
⊢argY = env (bwf↓ here refl wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$

¬argY-retype : ¬ (ΓPc ∣ [] ⊢ argY ⦂ `ℕ)
¬argY-retype ()

------------------------------------------------------------------------
-- (3d) SAFE, by contrast.  An ORDINARY conceal chooses its own rep, and
-- once the exterior's knowledge is CLOSED — which is what full unfolding
-- makes it in a closed program — the rep IS that knowledge and the
-- reversal premise is discharged for EVERY boundary, with no side
-- condition.  So (a′) is harmless at bwf↓; only the dual, which has no
-- choice of rep, is exposed.
------------------------------------------------------------------------

∋ok-[] : ∀ {X} → ¬ ([] ∋ok X)
∋ok-[] ()

closed-fix : ∀ (σ : Substᵗ) {A} → Scoped [] A → substᵗ σ A ≡ A
closed-fix σ {A} sA =
  trans (subst-cong-sc sA (λ X p → ⊥-elim (∋ok-[] p))) (subst-id A)

closed-ren : ∀ (ρ : Renameᵗ) {A} → Scoped [] A → renameᵗ ρ A ≡ A
closed-ren ρ {A} sA = trans (sym (substᵗ-renᵗ ρ A)) (closed-fix (renᵗ ρ) sA)

-- THEOREM.  Closed (fully unfolded) knowledge licenses its own conceal, in
-- any boundary, at any slot.
Reversal-closed : ∀ Θ₁ X {A} → Scoped [] A → Reversal Θ₁ X A A
Reversal-closed Θ₁ X {A} sA =
  trans (closed-fix (outSub Θ₁) sA)
        (sym (closed-ren (λ i → suc X + i) sA))

------------------------------------------------------------------------
-- §7.  SITE 4 — unfoldᵉ AND RENAMING
--
-- The lemma the install would need in ⊢renameᵀ's (env) case, and the
-- hypothesis it really requires.  SECOND FINDING: ⊢renameᵀ's present
-- hypotheses (∋tv transport, Mono, and the ∋:= transport it already
-- carries) do NOT suffice — they say nothing about an ABSTRACT slot landing
-- on a REVEALED one, and unfolding is exactly what notices that.  The
-- hypothesis must become ENTRYWISE.
------------------------------------------------------------------------

UnfRen : (ℕ → ℕ) → TCtx → TCtx → Set
UnfRen ρ Γ₁ Γ₂ = ∀ X → renameᵗ ρ (unfSub Γ₁ X) ≡ unfSub Γ₂ (ρ X)

-- THEOREM.  Under that (entrywise) hypothesis, unfolding commutes with
-- renaming — for every type, with no scope restriction.
unf-ren : ∀ {ρ} (Γ₁ Γ₂ : TCtx) → UnfRen ρ Γ₁ Γ₂ → ∀ A
        → renameᵗ ρ (unfoldᵉ Γ₁ A) ≡ unfoldᵉ Γ₂ (renameᵗ ρ A)
unf-ren {ρ} Γ₁ Γ₂ h A =
  trans (rename-subst ρ (unfSub Γ₁) A)
        (trans (subst-cong h A)
               (sym (rename-subst-commute ρ (unfSub Γ₂) A)))

-- *** THE FIND ***  the ⊢renameᵀ hypotheses are all satisfied here …
Γid Γ′id : TCtx
Γid  = abst ∷ []                      -- X Λ-bound
Γ′id = rvld `ℕ ∷ []                   -- X:=ℕ

idρ : ℕ → ℕ
idρ i = i

h-∋tv : ∀ {X} → Γid ∋tv X → Γ′id ∋tv idρ X
h-∋tv here-abst = here-rvld

h-mono : Mono idρ
h-mono lt = lt

h-∋:= : ∀ {X A₀} → Γid ∋ X := A₀
      → Γ′id ∋ idρ X := renameᵗ (restrictRen X idρ) A₀
h-∋:= (skip-abst ())

-- … and UnfRen still fails: the Λ-bound X unfolds to itself on the left and
-- to ℕ on the right.  So the install must strengthen ⊢renameᵀ's third
-- hypothesis from "∋:= transports" to "the ENTRY transports" (abstract to
-- abstract, revealed to the renamed rep).
¬UnfRen-hk : ¬ (UnfRen idρ Γid Γ′id)
¬UnfRen-hk h with h 0
¬UnfRen-hk h | ()

-- SAFE for the renamings the system actually performs: weakening by a fresh
-- ABSTRACT slot (⇑ᵀ / hk-suc) …
UnfRen-abst : ∀ (Γ₁ : TCtx) → UnfRen suc Γ₁ (abst ∷ Γ₁)
UnfRen-abst Γ₁ X = refl

-- … and its lift under a Λ, so the ⊢renameᵀ recursion goes through for the
-- abstract-weakening family.
UnfRen-ext : ∀ {ρ} (Γ₁ Γ₂ : TCtx) → UnfRen ρ Γ₁ Γ₂
           → UnfRen (extᵗ ρ) (abst ∷ Γ₁) (abst ∷ Γ₂)
UnfRen-ext Γ₁ Γ₂ h zero    = refl
UnfRen-ext {ρ} Γ₁ Γ₂ h (suc X) =
  trans (rename-rename-commute suc (extᵗ ρ) (unfSub Γ₁ X))
        (trans (sym (rename-rename-commute ρ suc (unfSub Γ₁ X)))
               (cong ⇑ᵗ (h X)))

------------------------------------------------------------------------
-- §8.  SITE 5 — ≼-RETAG ACROSS AN UNFOLDING
--
-- _≼_ compares knowledge entries SYNTACTICALLY (abst ≼ anything,
-- rvld A ≼ rvld A), so it cannot cross an unfolding — confirming the known
-- gap.  The T6-merge shape is exactly the retag that would be needed.
------------------------------------------------------------------------

¬≼-unfold : ¬ ((rvld (` 0) ∷ []) ≼ (rvld `ℕ ∷ []))
¬≼-unfold ()

-- the T6-merge retag (MergeProbe's ¬⊕-intR≼): the nested interior cannot be
-- retagged to the merged one
¬⊕-retag-raw : ¬ (intOf (intOf [] Θm₂) Θm₁ ≼ intOf [] Θm₁₂)
¬⊕-retag-raw ()

-- … and under FULL (a′) the situation does not arise: the two interiors are
-- EQUAL (§5), so ≼-refl suffices.
⊕-retag-a′ : intOfᵁ (intOfᵁ [] Θm₂) Θm₁ ≼ intOfᵁ [] Θm₁₂
⊕-retag-a′ = ≼-refl _

-- WHY it cannot arise, in general: ⟦·⟧ᵁ is idempotent in the rep, so an
-- entry born unfolded is unchanged by any later unfolding — there is never
-- a raw entry on one side and an unfolded entry on the other.
⟦⟧ᵁ-idem : ∀ (Γ₁ : TCtx) → ⊢ Γ₁ → ∀ Θ₁ j {A} → Γ₁ ⊢ A
         → ⟦ Γ₁ ⟧ᵁ Θ₁ j (unfoldᵉ Γ₁ A) ≡ ⟦ Γ₁ ⟧ᵁ Θ₁ j A
⟦⟧ᵁ-idem Γ₁ wΓ Θ₁ j wA = cong (⟦ Θ₁ ⟧ᵉ j) (unf-idem Γ₁ wΓ wA)

-- and the entries themselves are in KNF (checked on the probe's ambients;
-- the general statement reduces to §2's unf-scoped plus §3's barrier)
KNF-Γ2ᵁ : KNF Γ2ᵁ
KNF-Γ2ᵁ = knfrvld (knfrvld (knfrvld knf[] sc-𝔹) sc-𝔹) sc-𝔹

KNF-intᵁ-Pc : KNF (intOfᵁ ΓPc ΘW)
KNF-intᵁ-Pc = knfrvld (knfrvld (knfrvld knf[] sc-ℕ) sc-ℕ) sc-ℕ

¬KNF-int-Pc : ¬ (KNF (intOf ΓPc ΘW))
¬KNF-int-Pc (knfrvld _ (sc-var ()))

------------------------------------------------------------------------
-- §9.  SITE 6 — THE ABSTRACTION BARRIER: (a′) IS INVISIBLE TO THE BODY
--
-- (i)/(ii) The two faces and the body's interior type are functions of Θ
-- and B₀ ALONE — the knowledge column does not occur in ρᵇ, γᵇ or γᵇ's
-- image of B₀, so (a′) cannot move them.  (The statements below typecheck
-- for two UNRELATED ambients; that is their content.)
------------------------------------------------------------------------

face-ext-indep : ∀ (Γ₁ Γ₂ : TCtx) Θ₁ B₀
               → substᵗ (ρᵇ Θ₁) B₀ ≡ substᵗ (ρᵇ Θ₁) B₀
face-ext-indep Γ₁ Γ₂ Θ₁ B₀ = refl

face-int-indep : ∀ (Γ₁ Γ₂ : TCtx) Θ₁ B₀
               → substᵗ (γᵇ Θ₁) B₀ ≡ substᵗ (γᵇ Θ₁) B₀
face-int-indep Γ₁ Γ₂ Θ₁ B₀ = refl

-- (iii) Which slots exist, which types are well formed, and which slots are
-- BLOCKED depend only on the SHAPE of the context — and (a′) preserves the
-- shape exactly.  So the sealed body's view of the world is bit-identical.
suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

∋tv-zero : ∀ (E : TyEntry) (Δ₁ : TCtx) → (E ∷ Δ₁) ∋tv zero
∋tv-zero abst     Δ₁ = here-abst
∋tv-zero (rvld B) Δ₁ = here-rvld

∋tv-suc : ∀ (E : TyEntry) {Δ₁ : TCtx} {X} → Δ₁ ∋tv X → (E ∷ Δ₁) ∋tv suc X
∋tv-suc abst     p = skip-abst p
∋tv-suc (rvld B) p = skip-rvld p

∋tv-len : ∀ {Δ₁ Δ₂ : TCtx} {X} → length Δ₁ ≡ length Δ₂ → Δ₁ ∋tv X → Δ₂ ∋tv X
∋tv-len {Δ₂ = []}     () here-abst
∋tv-len {Δ₂ = []}     () here-rvld
∋tv-len {Δ₂ = []}     () (skip-abst p)
∋tv-len {Δ₂ = []}     () (skip-rvld p)
∋tv-len {Δ₂ = E ∷ Δ₂} e here-abst     = ∋tv-zero E Δ₂
∋tv-len {Δ₂ = E ∷ Δ₂} e here-rvld     = ∋tv-zero E Δ₂
∋tv-len {Δ₂ = E ∷ Δ₂} e (skip-abst p) = ∋tv-suc E (∋tv-len (suc-inj e) p)
∋tv-len {Δ₂ = E ∷ Δ₂} e (skip-rvld p) = ∋tv-suc E (∋tv-len (suc-inj e) p)

⊢-len : ∀ {Δ₁ Δ₂ : TCtx} {A} → length Δ₁ ≡ length Δ₂ → Δ₁ ⊢ A → Δ₂ ⊢ A
⊢-len e (wf-var p)   = wf-var (∋tv-len e p)
⊢-len e wf-ℕ         = wf-ℕ
⊢-len e wf-𝔹         = wf-𝔹
⊢-len e (wf-⇒ wA wB) = wf-⇒ (⊢-len e wA) (⊢-len e wB)
⊢-len e (wf-∀ wA)    = wf-∀ (⊢-len (cong suc e) wA)

slotsᴳ-len : ∀ Θ₁ i (Γ₁ Γ₂ : TCtx) → length Γ₁ ≡ length Γ₂
           → slotsᴳ Θ₁ i Γ₁ ≡ slotsᴳ Θ₁ i Γ₂
slotsᴳ-len Θ₁ i []        []        e = refl
slotsᴳ-len Θ₁ i []        (E ∷ Γ₂)  ()
slotsᴳ-len Θ₁ i (E ∷ Γ₁)  []        ()
slotsᴳ-len Θ₁ i (E ∷ Γ₁)  (F ∷ Γ₂)  e =
  cong (slotAt Θ₁ i ∷_) (slotsᴳ-len Θ₁ (suc i) Γ₁ Γ₂ (suc-inj e))

baseS-len : ∀ Θ₁ (Γ₁ Γ₂ : TCtx) → length Γ₁ ≡ length Γ₂
          → baseS Θ₁ Γ₁ ≡ baseS Θ₁ Γ₂
baseS-len Θ₁ Γ₁ Γ₂ e =
  cong (revSlots Θ₁ ++_) (slotsᴳ-len Θ₁ 0 Γ₁ Γ₂ e)

-- (a′) preserves the shape: same number of entries, entry for entry
len-revEntsᵁ : ∀ (Γ₁ : TCtx) Θ₁ j Ξ₁ → length (revEntsᵁ Γ₁ Θ₁ j Ξ₁) ≡ revs Ξ₁
len-revEntsᵁ Γ₁ Θ₁ j []            = refl
len-revEntsᵁ Γ₁ Θ₁ j (rvl A ∷ Ξ₁)  =
  cong suc (len-revEntsᵁ Γ₁ Θ₁ (suc j) Ξ₁)
len-revEntsᵁ Γ₁ Θ₁ j (rvl⋆ ∷ Ξ₁)   =
  cong suc (len-revEntsᵁ Γ₁ Θ₁ (suc j) Ξ₁)
len-revEntsᵁ Γ₁ Θ₁ j (cnc X A ∷ Ξ₁) = len-revEntsᵁ Γ₁ Θ₁ j Ξ₁

len-++ : ∀ (Δ₁ Δ₂ : TCtx) → length (Δ₁ ++ Δ₂) ≡ length Δ₁ + length Δ₂
len-++ []        Δ₂ = refl
len-++ (E ∷ Δ₁)  Δ₂ = cong suc (len-++ Δ₁ Δ₂)

intOfᵁ-len : ∀ (Γ₁ : TCtx) Θ₁
           → length (intOfᵁ Γ₁ Θ₁) ≡ length (intOf Γ₁ Θ₁)
intOfᵁ-len Γ₁ Θ₁ =
  trans (len-++ (revEntsᵁ Γ₁ Θ₁ 0 Θ₁) (dropN (cmax Θ₁) Γ₁))
    (trans (cong (_+ length (dropN (cmax Θ₁) Γ₁))
                 (trans (len-revEntsᵁ Γ₁ Θ₁ 0 Θ₁)
                        (sym (len-revEnts Θ₁ 0 Θ₁))))
           (sym (len-++ (revEnts Θ₁ 0 Θ₁) (dropN (cmax Θ₁) Γ₁))))

-- THEOREM (the abstraction barrier).  Everything the sealed body's
-- derivation reads about its context OTHER than knowledge is unchanged by
-- (a′): which variables exist, which types are well formed, which slots a
-- nested boundary blocks.
barrier-∋tv : ∀ (Γ₁ : TCtx) Θ₁ {X}
            → intOf Γ₁ Θ₁ ∋tv X → intOfᵁ Γ₁ Θ₁ ∋tv X
barrier-∋tv Γ₁ Θ₁ = ∋tv-len (sym (intOfᵁ-len Γ₁ Θ₁))

barrier-⊢ : ∀ (Γ₁ : TCtx) Θ₁ {A} → intOf Γ₁ Θ₁ ⊢ A → intOfᵁ Γ₁ Θ₁ ⊢ A
barrier-⊢ Γ₁ Θ₁ = ⊢-len (sym (intOfᵁ-len Γ₁ Θ₁))

barrier-baseS : ∀ (Γ₁ : TCtx) Θ₁ Θ₂
              → baseS Θ₂ (intOf Γ₁ Θ₁) ≡ baseS Θ₂ (intOfᵁ Γ₁ Θ₁)
barrier-baseS Γ₁ Θ₁ Θ₂ =
  baseS-len Θ₂ (intOf Γ₁ Θ₁) (intOfᵁ Γ₁ Θ₁) (sym (intOfᵁ-len Γ₁ Θ₁))

------------------------------------------------------------------------
-- §10.  HORN 3, AND WHAT (a″) BUYS
--
-- The third escape from §6 would be to unfold the STORED rep as well, so
-- that ρᵇ and the entry agree again.  That gives up SIMULTANEITY (the
-- reveal's rep would no longer be "read in the plain exterior") and, worse,
-- it stops TyBeta from preserving types: the redex (Λ V)·[B,A] has type
-- B[A]ᵗ, while the contractum's external face becomes B[unfold A].  On
-- Pc's own step (A = Y, B = the bound variable) those differ.
------------------------------------------------------------------------

¬TyBeta-unfold-rep : ¬ ((` 0) [ ` 0 ]ᵗ ≡ (` 0) [ unfoldᵉ ΓPc (` 0) ]ᵗ)
¬TyBeta-unfold-rep ()

------------------------------------------------------------------------
-- So under the simultaneity ruling NO placement of the unfolding is
-- consistent: entry-only breaks the dual's conceal (§6, ¬DualCnc-a′),
-- dual-conceal-too breaks the internal face (¬face-unfolded, ¬argY-retype),
-- and rep-too breaks TyBeta (¬TyBeta-unfold-rep).  Each horn is repaired by
-- the SAME missing ingredient: an equality up to unfolding.  That is (a″).
--
-- What (a″) then buys over (a′), on this file's own witnesses:
--   * §6 needs nothing: with RAW entries the dual's conceal is licensed by
--     refl (DualCnc-raw), because the read-back of the raw rep IS the raw
--     knowledge.
--   * §4's dual rebuild is repaired by unfolding the COPY (which is what
--     the dfree guard currently refuses), and the resulting entry differs
--     from Γ's only by an unfolding — the comparison (a″) supplies, where
--     _≼_ fails (¬dual-rebuild-raw≼):
------------------------------------------------------------------------

-- raw W:=Y and (a′) W:=𝔹 are the same knowledge for an up-to-unfolding
-- comparison, in the tail over which both entries are read
unf-eq-entries : unfoldᵉ (rvld `𝔹 ∷ rvld `𝔹 ∷ []) (` 0)
               ≡ unfoldᵉ (rvld `𝔹 ∷ rvld `𝔹 ∷ []) `𝔹
unf-eq-entries = refl

--   * §7's find disappears: raw entries do not need ⊢renameᵀ's third
--     hypothesis strengthened, because nothing in the CONTEXT is unfolded.
--     (The unfold RELATION still has to transport, but there the entrywise
--     facts are available from the relation's own premises.)
--   * §5's Merge obligation is the one place (a′) is strictly better: the
--     interiors compose on the nose (⊕-int-a′) instead of up to unfolding.
--     (a″) pays for Merge what (a′) pays for Wrap.
