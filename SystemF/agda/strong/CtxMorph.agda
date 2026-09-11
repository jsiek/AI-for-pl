module strong.CtxMorph where

-- Strong System F — THE v3 SCOPE BOUNDARY.
--
-- v3 (notes/notes-v3.md) SPLITS what v2 combined.  A v2 boundary
-- `M ⟪ Θ , c ⟫` carried a context morphism Θ AND a conversion c together.
-- v3 has TWO separate runtime forms (strong.Terms):
--
--   ᵇ[M]    a SCOPE BOUNDARY — M under a boundary tag b, with NO conversion;
--   M⟨c⟩    a CONVERSION applied to M, with NO scope change.
--
-- This module defines the boundary tag `b` and the operations the typing
-- and reduction rules read off it.  A tag is one of THREE things
-- (notes §"Runtime Terms"/§"Binding applied to Context"):
--
--   intro A   ( +X=A )  introduce a FRESH binder at interior slot 0, whose
--                      representation is A (a type over the exterior).
--                      names(b) = {0}; it adds ONE de Bruijn binder.
--   reveal χ  ( +χ  )   UNLOCK every exterior slot in the set χ.
--   conceal χ ( -χ  )   LOCK   every exterior slot in the set χ.
--
-- A variable-set χ is a list of de Bruijn indices (`VarSet`).  Locking and
-- unlocking a set are the one-slot `mask`/`unmask` of strong.Ctx folded
-- over the list; because distinct slots' masks commute, the fold order is
-- immaterial.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length; filter)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.Ctx

private
  variable
    Δ Δ′ : Ctxᵗ
    A B : Ty
    X Y : ℕ

------------------------------------------------------------------------
-- 1.  Variable sets and their (un)locking
------------------------------------------------------------------------

VarSet : Set
VarSet = List ℕ

-- χ ≠ ∅ — the side condition the value grammar and several reduction
-- rules carry (notes §"Values", rules ⁻χ¹⁻χ², ⁺χ, …).
data NonEmpty : VarSet → Set where
  ne : ∀ {X χ} → NonEmpty (X ∷ χ)

-- X ∈χ χ — membership, with its decision procedure.  The round-trip laws
-- of §2c split on it: a repeated index in χ is absorbed rather than
-- undone, so the laws hold for any χ, duplicates included.
infix 4 _∈χ_
data _∈χ_ : ℕ → VarSet → Set where
  ∈-here  : ∀ {X χ} → X ∈χ (X ∷ χ)
  ∈-there : ∀ {X Y χ} → X ∈χ χ → X ∈χ (Y ∷ χ)

_∈χ?_ : (X : ℕ) (χ : VarSet) → Dec (X ∈χ χ)
X ∈χ? []      = no (λ ())
X ∈χ? (Y ∷ χ) = ∈χ?-head X Y χ (X ≟ℕ Y)
  where
  ∈χ?-tail : (X Y : ℕ) (χ : VarSet) → ¬ (X ≡ Y) → Dec (X ∈χ χ) → Dec (X ∈χ (Y ∷ χ))
  ∈χ?-tail X Y χ X≢Y (yes m) = yes (∈-there m)
  ∈χ?-tail X Y χ X≢Y (no ¬m) =
    no λ { ∈-here → X≢Y refl ; (∈-there m) → ¬m m }
  ∈χ?-head : (X Y : ℕ) (χ : VarSet) → Dec (X ≡ Y) → Dec (X ∈χ (Y ∷ χ))
  ∈χ?-head X Y χ (yes refl) = yes ∈-here
  ∈χ?-head X Y χ (no X≢Y)   = ∈χ?-tail X Y χ X≢Y (X ∈χ? χ)

-- Membership transports along `map suc`, in both directions — the only
-- fact `scopeᵗ`'s adequacy needs about the shift.
∈χ-map-suc : ∀ {X χ} → X ∈χ χ → suc X ∈χ map suc χ
∈χ-map-suc ∈-here      = ∈-here
∈χ-map-suc (∈-there m) = ∈-there (∈χ-map-suc m)

∈χ-map-suc⁻ : ∀ {X χ} → X ∈χ map suc χ → ∃[ Y ] ((X ≡ suc Y) × (Y ∈χ χ))
∈χ-map-suc⁻ {χ = Y ∷ χ} ∈-here      = Y , refl , ∈-here
∈χ-map-suc⁻ {χ = Y ∷ χ} (∈-there m) with ∈χ-map-suc⁻ m
∈χ-map-suc⁻ {χ = Y ∷ χ} (∈-there m) | (Z , eq , m′) = Z , eq , ∈-there m′

-- lock / unlock a whole set, in place.  `mask`/`unmask` are strong.Ctx's
-- one-slot updates; folding them over χ realises notes' `lock(χ,Γ)` /
-- `unlock(χ,Γ)`.
lockχ : VarSet → Ctxᵗ → Ctxᵗ
lockχ []      Δ = Δ
lockχ (X ∷ χ) Δ = mask X (lockχ χ Δ)

unlockχ : VarSet → Ctxᵗ → Ctxᵗ
unlockχ []      Δ = Δ
unlockχ (X ∷ χ) Δ = unmask X (unlockχ χ Δ)

------------------------------------------------------------------------
-- 1b.  scopeᵗ — THE TYPE VARIABLES IN SCOPE  (colour preservation)
------------------------------------------------------------------------

-- scopeᵗ Δ — the de Bruijn indices of Δ whose entry is UNMASKED, listed in
-- ASCENDING order (slot 0 first, i.e. innermost first).  `masked` slots are
-- skipped: `masked` is exactly "not nameable" (Ctx.Nameable).
--
-- THIS IS THE COLOUR SET.  Every SOURCE term node carries one as an
-- annotation (strong.Terms), and its typing rule demands the annotation be
-- EQUAL to scopeᵗ of the node's type context — "a type variable is in scope
-- iff it is in the annotation" (notes-v3 §Criteria, Jeremy 2026-09-11).
-- Reduction TRANSPORTS annotations and never recomputes them, so
-- Preservation then says the colour set at every source node is what it
-- always was: colour preservation is a corollary.
scopeᵗ : Ctxᵗ → VarSet
scopeᵗ []               = []
scopeᵗ (unmasked b ∷ Δ) = 0 ∷ map suc (scopeᵗ Δ)
scopeᵗ (masked   b ∷ Δ) =     map suc (scopeᵗ Δ)

-- ADEQUACY: scopeᵗ is exactly `_∋tv_` collected into a list.
scopeᵗ-complete : ∀ {Δ X} → Δ ∋tv X → X ∈χ scopeᵗ Δ
scopeᵗ-complete {Δ = unmasked b ∷ Δ} (_ , ez , nameable) = ∈-here
scopeᵗ-complete {Δ = masked b ∷ Δ}   (_ , ez , ())
scopeᵗ-complete {Δ = unmasked b ∷ Δ} (_ , es d , v) =
  ∈-there (∈χ-map-suc (scopeᵗ-complete (_ , d , renᵉ-Nameable⁻ v)))
scopeᵗ-complete {Δ = masked b ∷ Δ}   (_ , es d , v) =
  ∈χ-map-suc (scopeᵗ-complete (_ , d , renᵉ-Nameable⁻ v))

∋tv-suc : ∀ {Δ E Y} → Δ ∋tv Y → (E ∷ Δ) ∋tv suc Y
∋tv-suc (E₀ , d , v) = ⇑ᵉ E₀ , es d , renᵉ-Nameable v

scopeᵗ-sound : ∀ {Δ X} → X ∈χ scopeᵗ Δ → Δ ∋tv X
scopeᵗ-sound {Δ = unmasked b ∷ Δ} ∈-here     = _ , ez , nameable
scopeᵗ-sound {Δ = unmasked b ∷ Δ} (∈-there m) with ∈χ-map-suc⁻ m
scopeᵗ-sound {Δ = unmasked b ∷ Δ} (∈-there m) | (Y , refl , m′) =
  ∋tv-suc (scopeᵗ-sound m′)
scopeᵗ-sound {Δ = masked b ∷ Δ}   m with ∈χ-map-suc⁻ m
scopeᵗ-sound {Δ = masked b ∷ Δ}   m | (Y , refl , m′) =
  ∋tv-suc (scopeᵗ-sound m′)

------------------------------------------------------------------------
-- 2.  "Not free in a type" — the freshness the boundary rules demand
------------------------------------------------------------------------

-- X ∉FV B :  the de Bruijn index X does not occur free in B.  This is the
-- per-variable half of notes' `names(b) ∩ FV(B) = ∅`.  Under a `∀` the
-- index shifts, matching `renameᵗ`.
infix 4 _∉FV_
data _∉FV_ : ℕ → Ty → Set where
  ∉-var : ∀ {X Y} → X ≢ Y → X ∉FV (` Y)
  ∉-ℕ   : ∀ {X}   → X ∉FV `ℕ
  ∉-𝔹   : ∀ {X}   → X ∉FV `𝔹
  ∉-⇒   : ∀ {X A B} → X ∉FV A → X ∉FV B → X ∉FV (A ⇒ B)
  ∉-∀   : ∀ {X A} → suc X ∉FV A → X ∉FV (`∀ A)

-- χ ∩ FV(B) = ∅ :  no member of the set χ occurs free in B.
infix 4 _∉FVs_
data _∉FVs_ : VarSet → Ty → Set where
  ∉[] : ∀ {B} → [] ∉FVs B
  ∉∷  : ∀ {X χ B} → X ∉FV B → χ ∉FVs B → (X ∷ χ) ∉FVs B

------------------------------------------------------------------------
-- 2b.  LOCKEDNESS OF A TAG'S SLOTS — the premise the boundary rules need
------------------------------------------------------------------------

-- A `reveal χ` UNLOCKS χ and a `conceal χ` LOCKS it; the application rule
-- `ᵇ[V]·W -→ ᵇ[V · ⁻ᵇ[W]]` then sends the argument across the DUAL tag, so
-- W lands at `lockχ χ (unlockχ χ Δ)` (resp. `unlockχ χ (lockχ χ Δ)`).
-- That is Δ again ONLY IF the tag's slots were in the state the tag claims
-- to change: every X ∈ χ LOCKED for a reveal, NAMEABLE for a conceal.
-- Without these premises Preservation is false — a `reveal χ` at an
-- already-unlocked χ re-locks the argument's own variables (see
-- notes/ScopeProbe.agda and the 2026-09-11 entry in notes/DECISIONS.md).

-- every member of χ is LOCKED in Δ   (the premise of ⊢reveal)
infix 4 _∋lks_
data _∋lks_ : Ctxᵗ → VarSet → Set where
  lks[] : ∀ {Δ} → Δ ∋lks []
  lks∷  : ∀ {Δ X χ} → Δ ∋lk X → Δ ∋lks χ → Δ ∋lks (X ∷ χ)

-- every member of χ is NAMEABLE in Δ  (the premise of ⊢conceal)
infix 4 _∋tvs_
data _∋tvs_ : Ctxᵗ → VarSet → Set where
  tvs[] : ∀ {Δ} → Δ ∋tvs []
  tvs∷  : ∀ {Δ X χ} → Δ ∋tv X → Δ ∋tvs χ → Δ ∋tvs (X ∷ χ)

------------------------------------------------------------------------
-- 2c.  THE ROUND TRIP — why those premises are the right ones
------------------------------------------------------------------------

-- These are what AppBnd's crossing needs: the argument leaves Δ, enters
-- the boundary's interior, and is wrapped in the DUAL tag, so it must land
-- back on Δ EXACTLY.  `lock-unlock` / `unlock-lock` say it does, given the
-- premises of ⊢reveal / ⊢conceal and nothing else.

-- Away from χ, a one-slot update passes through the fold.
lockχ-∉ : ∀ {X} (χ : VarSet) (Δ : Ctxᵗ) → ¬ (X ∈χ χ)
  → lockχ χ (unmask X Δ) ≡ unmask X (lockχ χ Δ)
lockχ-∉ []      Δ ¬m = refl
lockχ-∉ {X} (Y ∷ χ) Δ ¬m =
  trans (cong (mask Y) (lockχ-∉ χ Δ (λ m → ¬m (∈-there m))))
        (updateAt-comm maskEnt unmaskEnt (lockχ χ Δ)
          (λ eq → ¬m (subst (λ z → z ∈χ (Y ∷ χ)) eq ∈-here)))

-- At a member of χ the fold's own lock ABSORBS the unlock.
lockχ-∈ : ∀ {X} (χ : VarSet) (Δ : Ctxᵗ) → X ∈χ χ
  → lockχ χ (unmask X Δ) ≡ lockχ χ Δ
lockχ-∈ {X} (.X ∷ χ) Δ ∈-here      = lockχ-∈-here X χ Δ (X ∈χ? χ)
  where
  lockχ-∈-here : (X : ℕ) (χ : VarSet) (Δ : Ctxᵗ) → Dec (X ∈χ χ)
    → lockχ (X ∷ χ) (unmask X Δ) ≡ lockχ (X ∷ χ) Δ
  lockχ-∈-here X χ Δ (yes m) = cong (mask X) (lockχ-∈ χ Δ m)
  lockχ-∈-here X χ Δ (no ¬m) =
    trans (cong (mask X) (lockχ-∉ χ Δ ¬m)) (mask-absorb X (lockχ χ Δ))
lockχ-∈     (Y ∷ χ) Δ (∈-there m) = cong (mask Y) (lockχ-∈ χ Δ m)

-- ⊢reveal's crossing:  lock ∘ unlock = id  when every slot WAS locked.
lock-unlock : ∀ {Δ χ} → Δ ∋lks χ → lockχ χ (unlockχ χ Δ) ≡ Δ
lock-unlock lks[] = refl
lock-unlock {Δ} {X ∷ χ} (lks∷ lk lks) = go (X ∈χ? χ)
  where
  go : Dec (X ∈χ χ) → lockχ (X ∷ χ) (unlockχ (X ∷ χ) Δ) ≡ Δ
  go (yes m) =
    trans (cong (mask X) (lockχ-∈ χ (unlockχ χ Δ) m))
          (trans (cong (mask X) (lock-unlock lks)) (mask-locked lk))
  go (no ¬m) =
    trans (cong (mask X) (lockχ-∉ χ (unlockχ χ Δ) ¬m))
          (trans (cong (λ Δ′ → mask X (unmask X Δ′)) (lock-unlock lks))
                 (mask-unmask lk))

unlockχ-∉ : ∀ {X} (χ : VarSet) (Δ : Ctxᵗ) → ¬ (X ∈χ χ)
  → unlockχ χ (mask X Δ) ≡ mask X (unlockχ χ Δ)
unlockχ-∉ []      Δ ¬m = refl
unlockχ-∉ {X} (Y ∷ χ) Δ ¬m =
  trans (cong (unmask Y) (unlockχ-∉ χ Δ (λ m → ¬m (∈-there m))))
        (updateAt-comm unmaskEnt maskEnt (unlockχ χ Δ)
          (λ eq → ¬m (subst (λ z → z ∈χ (Y ∷ χ)) eq ∈-here)))

unlockχ-∈ : ∀ {X} (χ : VarSet) (Δ : Ctxᵗ) → X ∈χ χ
  → unlockχ χ (mask X Δ) ≡ unlockχ χ Δ
unlockχ-∈ {X} (.X ∷ χ) Δ ∈-here      = unlockχ-∈-here X χ Δ (X ∈χ? χ)
  where
  unlockχ-∈-here : (X : ℕ) (χ : VarSet) (Δ : Ctxᵗ) → Dec (X ∈χ χ)
    → unlockχ (X ∷ χ) (mask X Δ) ≡ unlockχ (X ∷ χ) Δ
  unlockχ-∈-here X χ Δ (yes m) = cong (unmask X) (unlockχ-∈ χ Δ m)
  unlockχ-∈-here X χ Δ (no ¬m) =
    trans (cong (unmask X) (unlockχ-∉ χ Δ ¬m)) (unmask-absorb X (unlockχ χ Δ))
unlockχ-∈     (Y ∷ χ) Δ (∈-there m) = cong (unmask Y) (unlockχ-∈ χ Δ m)

-- ⊢conceal's crossing:  unlock ∘ lock = id  when every slot WAS nameable.
unlock-lock : ∀ {Δ χ} → Δ ∋tvs χ → unlockχ χ (lockχ χ Δ) ≡ Δ
unlock-lock tvs[] = refl
unlock-lock {Δ} {X ∷ χ} (tvs∷ tv tvs) = go (X ∈χ? χ)
  where
  go : Dec (X ∈χ χ) → unlockχ (X ∷ χ) (lockχ (X ∷ χ) Δ) ≡ Δ
  go (yes m) =
    trans (cong (unmask X) (unlockχ-∈ χ (lockχ χ Δ) m))
          (trans (cong (unmask X) (unlock-lock tvs)) (unmask-nameable tv))
  go (no ¬m) =
    trans (cong (unmask X) (unlockχ-∉ χ (lockχ χ Δ) ¬m))
          (trans (cong (λ Δ′ → unmask X (mask X Δ′)) (unlock-lock tvs))
                 (unmask-mask tv))

------------------------------------------------------------------------
-- 3.  The boundary tag
------------------------------------------------------------------------

data Bnd : Set where
  intro   : Ty → Bnd        -- +X=A   (fresh binder, rep A)
  reveal  : VarSet → Bnd    -- +χ     (unlock χ)
  conceal : VarSet → Bnd    -- -χ     (lock   χ)

-- The number of de Bruijn binders a tag adds to the interior.  Only
-- `intro` binds; the (un)lock tags rename nothing.
numBindsᵇ : Bnd → ℕ
numBindsᵇ (intro A)   = 1
numBindsᵇ (reveal χ)  = 0
numBindsᵇ (conceal χ) = 0

-- b(Γ) — the interior type context the boundary body is typed in
-- (notes §"Binding applied to Context").
applyᵇ : Bnd → Ctxᵗ → Ctxᵗ
applyᵇ (intro A)   Δ = unmasked (bind A) ∷ Δ
applyᵇ (reveal χ)  Δ = unlockχ χ Δ
applyᵇ (conceal χ) Δ = lockχ χ Δ

-- The DUAL tag  -b  (notes' `-b`).  Used by the application rule
-- `ᵇ[Vˢ]·W → ᵇ[Vˢ · ⁻ᵇ[W]]`: the crossing argument is wrapped in the dual
-- so it may enter the interior.
--
--   -(intro A) = conceal {0}   (the fresh binder is masked for the arg,
--                              which is also weakened past it — the shift
--                              is applied at the use site, strong.Reduction)
--   -(reveal χ)  = conceal χ
--   -(conceal χ) = reveal  χ
dualᵇ : Bnd → Bnd
dualᵇ (intro A)   = conceal (0 ∷ [])
dualᵇ (reveal χ)  = conceal χ
dualᵇ (conceal χ) = reveal χ

------------------------------------------------------------------------
-- 4.  Set difference on variable sets  (rule ⁻χ¹[⁺χ²[V]] -→ ⁺χ³[⁻χ⁴[V]])
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (_<_; _<?_)

-- Boolean membership, via strong.Ctx's decidable `_≟ℕ_`.
memberᵇ : ℕ → VarSet → Bool
memberᵇ X []      = false
memberᵇ X (Y ∷ χ) with X ≟ℕ Y
... | yes _ = true
... | no  _ = memberᵇ X χ

-- χ ∖ ψ : the members of χ not in ψ.  Used to compute χ3 = χ2 ∖ χ1 and
-- χ4 = χ1 ∖ χ2 in the conceal/reveal commuting rule.
infixl 6 _∖_
_∖_ : VarSet → VarSet → VarSet
[]      ∖ ψ = []
(X ∷ χ) ∖ ψ = if memberᵇ X ψ then (χ ∖ ψ) else (X ∷ (χ ∖ ψ))

-- Union of two sets (the merged conceal `⁻χ¹χ²`, rule ⁻χ¹[⁻χ²[Vˢ]]).
-- A plain append; duplicates are harmless because locking is idempotent.
infixl 5 _∪_
_∪_ : VarSet → VarSet → VarSet
χ ∪ ψ = χ ++ ψ

------------------------------------------------------------------------
-- 5.  scopeᵇ — THE COLOUR SET ACROSS A BOUNDARY
------------------------------------------------------------------------

-- `scopeᵗ` is a CANONICAL list — ascending and duplicate-free — so the
-- unlocking side needs an ordered insert rather than `_∪_` (which is
-- `_++_`, right for boundary tags and wrong for a colour set).
insertᵒ : ℕ → VarSet → VarSet
insertᵒ X []      = X ∷ []
insertᵒ X (Y ∷ χ) = insertᵒ-eq X Y χ (X ≟ℕ Y)
  where
  insertᵒ-lt : (X Y : ℕ) (χ : VarSet) → Dec (X < Y) → VarSet
  insertᵒ-lt X Y χ (yes _) = X ∷ Y ∷ χ
  insertᵒ-lt X Y χ (no  _) = Y ∷ insertᵒ X χ
  insertᵒ-eq : (X Y : ℕ) (χ : VarSet) → Dec (X ≡ Y) → VarSet
  insertᵒ-eq X Y χ (yes _) = Y ∷ χ
  insertᵒ-eq X Y χ (no  _) = insertᵒ-lt X Y χ (X <? Y)

mergeᵒ : VarSet → VarSet → VarSet
mergeᵒ []      χ = χ
mergeᵒ (X ∷ ψ) χ = insertᵒ X (mergeᵒ ψ χ)

-- scopeᵇ b χ — the colour set INSIDE the boundary, computed from the set
-- OUTSIDE it and the tag alone.  Its law is
--
--   scopeᵇ b (scopeᵗ Δ) ≡ scopeᵗ (applyᵇ b Δ)
--
-- (given the ⊢reveal / ⊢conceal premises, which put every slot of the tag
-- in range).  Only the TWO reduction rules that move a node ACROSS a
-- boundary — AppBnd and TyPos — use it; every other rule transports its
-- annotations unchanged.
scopeᵇ : Bnd → VarSet → VarSet
scopeᵇ (intro A)   χ = 0 ∷ map suc χ
scopeᵇ (reveal ψ)  χ = mergeᵒ ψ χ
scopeᵇ (conceal ψ) χ = χ ∖ ψ
