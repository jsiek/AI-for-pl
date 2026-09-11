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
open import Relation.Nullary using (¬_; yes; no)
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
