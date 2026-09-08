module strong.TermSubst where

-- Strong System F — SUBSTITUTION AND THE TWO TRANSPORTS.
--
-- Term substitution is ordinary: boundaries are term-closed, so a wrapper is
-- never descended into.  The interesting content is the pair of TYPE-LEVEL
-- transports the binder design has to pay for, and both come out cheap:
--
--   ⊢rename : a type context renaming moves a whole typing derivation, with the ONE
--             structural hypothesis `Inj ρ` (positional masking; no
--             hypothesis mentions a representation).
--   ⊢retag  : knowledge refinement moves a whole typing derivation with the
--             TERM AND THE TYPE UNCHANGED — no ≈, no unfolding, no residue,
--             because nothing on the type context is ever destroyed.
--
-- §5 defines term-variable renaming (`renⁿ`) and substitution (`substᵐ`,
-- `_[_∶_]ᵐ`); §6 proves them sound (`⊢renⁿ`, `⊢substᵐ`, `⊢subst`), which is
-- what Beta's preservation case consumes (`preserve-Beta`).  TWO CASES carry
-- the whole story:
--
--   (env)  is TRIVIAL — a wrapper is TERM-CLOSED (the rule types its body at
--          Γ = []) and the rule's conclusion holds at an ARBITRARY term
--          context, so both `renⁿ` and `substᵐ` are the identity on wrappers
--          and the case is literally the premises handed back.
--
--   ⊢Λ     is the only real work — it types its body at the SHIFTED term
--          context ⤊ Γ, so every image of σ must cross the new Λ-bound
--          slot.  SHIFTING BY ⇑ᴹ = renᴹ suc IS NOT ENOUGH: it is sound but
--          not FRAME-EXACT (the image's frame gains the Λ's slot).  §5b
--          repairs it — a value image is WRAPPED IN THE BINDER'S DUAL
--          `⟪ morph [] (lock 0 ∷ []) , mkId (⇑ᵗ A) ⟫`, whose frame
--          identity `interior … (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ` is
--          DEFINITIONAL — and the case is then `⊢rename` at suc with
--          `Ren-wk`/`Inj-suc` plus `mkId-⊢` (`⊢crossΛ`, §6).  No knowledge
--          premise appears, because a boundary carries NAMES, never
--          spellings.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.TypeSubst using (rename-[]ᵗ-commute)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph

private
  variable
    Δ Δ′ : Ctxᵗ
    ρ : Renameᵗ

------------------------------------------------------------------------
-- 1.  Renaming boundaries and terms
------------------------------------------------------------------------

-- Renaming a CHANGE moves the exterior name it carries and nothing else.
renᶠ : Renameᵗ → Change → Change
renᶠ ρ (unlock X) = unlock (ρ X)
renᶠ ρ (lock X)   = lock (ρ X)

-- THE PAIR RENAMES COMPONENTWISE.  `binds (renᴮ ρ Θ) ≡ map (renameᵗ ρ)
-- (binds Θ)` is now DEFINITIONAL — the old `repsOf-ren` was the filtering
-- lemma that said it, and it is gone.
renᴮ : Renameᵗ → CtxMorph → CtxMorph
renᴮ ρ Θ = morph (map (renameᵗ ρ) (binds Θ)) (map (renᶠ ρ) (changes Θ))

numBinds-ren : (ρ : Renameᵗ) (Θ : CtxMorph) → numBinds (renᴮ ρ Θ) ≡ numBinds Θ
numBinds-ren ρ Θ = map-length (renameᵗ ρ) (binds Θ)

renᴹ : Renameᵗ → Term → Term
renᴹ ρ (` x)          = ` x
renᴹ ρ ($ n)          = $ n
renᴹ ρ (ƛ A ∙ N)      = ƛ renameᵗ ρ A ∙ renᴹ ρ N
renᴹ ρ (L · M)        = renᴹ ρ L · renᴹ ρ M
renᴹ ρ (Λ N)          = Λ (renᴹ (extᵗ ρ) N)
renᴹ ρ (L ·[ B , A ]) = renᴹ ρ L ·[ renameᵗ (extᵗ ρ) B , renameᵗ ρ A ]
renᴹ ρ (M ⟪ Θ , c ⟫)  =
  renᴹ (extN (numBinds Θ) ρ) M ⟪ renᴮ ρ Θ , renᶜ (extN (numBinds Θ) ρ) c ⟫

-- The weakening a crossing argument undergoes: the boundary's frame grew by
-- `numBinds Θ` binders, so the argument's ANNOTATIONS shift.  Ordinary de
-- Bruijn weakening, not a re-spelling.
wkN : ℕ → Renameᵗ
wkN n X = n + X

wkᴹ : ℕ → Term → Term
wkᴹ n = renᴹ (wkN n)

Inj-wkN : (n : ℕ) → Inj (wkN n)
Inj-wkN zero    eq = eq
Inj-wkN (suc n) eq = Inj-wkN n (Inj-suc eq)

------------------------------------------------------------------------
-- 2.  The type context operations transport (the structural half)
------------------------------------------------------------------------

ren-applyChanges : (S : List Change) → Ren ρ Δ Δ′ → Inj ρ
        → Ren ρ (applyChanges S Δ) (applyChanges (map (renᶠ ρ) S) Δ′)
ren-applyChanges []             r i = r
ren-applyChanges (unlock X ∷ S) r i = ren-unmask (ren-applyChanges S r i) i
ren-applyChanges (lock X ∷ S)   r i = ren-mask (ren-applyChanges S r i) i

ren-applyUnlocks : (S : List Change) → Ren ρ Δ Δ′ → Inj ρ
         → Ren ρ (applyUnlocks S Δ) (applyUnlocks (map (renᶠ ρ) S) Δ′)
ren-applyUnlocks []             r i = r
ren-applyUnlocks (unlock X ∷ S) r i = ren-unmask (ren-applyUnlocks S r i) i
ren-applyUnlocks (lock X ∷ S)   r i = ren-applyUnlocks S r i

ren-scope : (Θ : CtxMorph) → Ren ρ Δ Δ′ → Inj ρ
        → Ren ρ (scope Θ Δ) (scope (renᴮ ρ Θ) Δ′)
ren-scope Θ r i = ren-applyChanges (changes Θ) r i

ren-unlockedScope : (Θ : CtxMorph) → Ren ρ Δ Δ′ → Inj ρ
         → Ren ρ (unlockedScope Θ Δ) (unlockedScope (renᴮ ρ Θ) Δ′)
ren-unlockedScope Θ r i = ren-applyUnlocks (changes Θ) r i

ren-interior : (Θ : CtxMorph) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (numBinds Θ) ρ) (interior Θ Δ) (interior (renᴮ ρ Θ) Δ′)
ren-interior Θ ρ r i = ren-pushBinds (binds Θ) ρ (ren-scope Θ r i)

ren-convCtx : (Θ : CtxMorph) (ρ : Renameᵗ) → Ren ρ Δ Δ′ → Inj ρ
  → Ren (extN (numBinds Θ) ρ) (convCtx Θ Δ) (convCtx (renᴮ ρ Θ) Δ′)
ren-convCtx Θ ρ r i = ren-pushBinds (binds Θ) ρ (ren-unlockedScope Θ r i)

-- THE PAIR TRANSPORTS BY HALVES: the parallel reps all move by
-- `ren-unlockedScope`, and each sequential change by `ren-applyChanges`
-- at its own tail.
⊢ʳ-ren : ∀ {Bs} → Ren ρ Δ Δ′ → Δ ⊢ʳ Bs → Δ′ ⊢ʳ map (renameᵗ ρ) Bs
⊢ʳ-ren r rw[]        = rw[]
⊢ʳ-ren r (rw-b w ws) = rw-b (wf-ren r w) (⊢ʳ-ren r ws)

⊢ˢ-ren : ∀ {S} → Ren ρ Δ Δ′ → Inj ρ → Δ ⊢ˢ S → Δ′ ⊢ˢ map (renᶠ ρ) S
⊢ˢ-ren r i sw[] = sw[]
⊢ˢ-ren {S = lock X ∷ S}   r i (sw-l tv b) =
  sw-l (ren-tv (ren-applyChanges S r i) tv) (⊢ˢ-ren r i b)
⊢ˢ-ren {S = unlock X ∷ S} r i (sw-u lk b) =
  sw-u (ren-∋lk (ren-applyChanges S r i) lk) (⊢ˢ-ren r i b)

⊢ᵐ-ren : ∀ {Θ} → Ren ρ Δ Δ′ → Inj ρ → Δ ⊢ᵐ Θ → Δ′ ⊢ᵐ renᴮ ρ Θ
⊢ᵐ-ren {Θ = Θ} r i (mw ws bs) =
  mw (⊢ʳ-ren (ren-unlockedScope Θ r i) ws) (⊢ˢ-ren r i bs)

------------------------------------------------------------------------
-- 3.  THE RENAMING TRANSPORT
------------------------------------------------------------------------

renΓ : Renameᵗ → Ctx → Ctx
renΓ ρ Γ = map (renameᵗ ρ) Γ

∋⦂-ren : ∀ {Γ x A} (ρ : Renameᵗ) → Γ ∋ x ⦂ A → renΓ ρ Γ ∋ x ⦂ renameᵗ ρ A
∋⦂-ren ρ here      = here
∋⦂-ren ρ (there d) = there (∋⦂-ren ρ d)

⤊-ren : (ρ : Renameᵗ) (Γ : Ctx) → ⤊ (renΓ ρ Γ) ≡ renΓ (extᵗ ρ) (⤊ Γ)
⤊-ren ρ []      = refl
⤊-ren ρ (A ∷ Γ) = cong₂ _∷_ (sym (ren-⇑-comm ρ A)) (⤊-ren ρ Γ)

⊢rename : ∀ {Δ Δ′ Γ M A ρ}
  → Ren ρ Δ Δ′ → Inj ρ
  → Δ  ∣ Γ ⊢ M ⦂ A
    ------------------------------------------------
  → Δ′ ∣ renΓ ρ Γ ⊢ renᴹ ρ M ⦂ renameᵗ ρ A
⊢rename {ρ = ρ} r i (⊢` d)   = ⊢` (∋⦂-ren ρ d)
⊢rename r i ⊢$               = ⊢$
⊢rename r i (⊢ƛ w ⊢N)        = ⊢ƛ (wf-ren r w) (⊢rename r i ⊢N)
⊢rename r i (⊢· ⊢L ⊢M)       = ⊢· (⊢rename r i ⊢L) (⊢rename r i ⊢M)
⊢rename {Γ = Γ} {ρ = ρ} r i (⊢Λ ⊢N) =
  ⊢Λ (subst (λ Γ′ → _ ∣ Γ′ ⊢ _ ⦂ _) (sym (⤊-ren ρ Γ))
            (⊢rename (ren-ext r) (Inj-ext i) ⊢N))
⊢rename {ρ = ρ} r i (⊢·[] {A = A} {B = B} ⊢L w)
  rewrite rename-[]ᵗ-commute ρ B A =
  ⊢·[] (⊢rename r i ⊢L) (wf-ren r w)
⊢rename {Δ′ = Δ′} {ρ = ρ} r i
        (env {Θ = Θ} {c = c} {Bᵢ = Bᵢ} {Bₑ = Bₑ} mwᵥ ⊢M ⊢c wE) =
  env (⊢ᵐ-ren r i mwᵥ)
      (⊢rename (ren-interior Θ ρ r i) (Inj-extN (numBinds Θ) i) ⊢M)
      cprem
      (wf-ren r wE)
  where
  cprem : convCtx (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (numBinds Θ) ρ) c
            ∶ renameᵗ (extN (numBinds Θ) ρ) Bᵢ
            ⇝ shiftBy (numBinds (renᴮ ρ Θ)) (renameᵗ ρ Bₑ)
  cprem = subst (λ n → convCtx (renᴮ ρ Θ) Δ′ ⊢ renᶜ (extN (numBinds Θ) ρ) c
                         ∶ renameᵗ (extN (numBinds Θ) ρ) Bᵢ
                         ⇝ shiftBy n (renameᵗ ρ Bₑ))
                (sym (numBinds-ren ρ Θ))
                (subst (λ t → convCtx (renᴮ ρ Θ) Δ′
                                ⊢ renᶜ (extN (numBinds Θ) ρ) c
                                ∶ renameᵗ (extN (numBinds Θ) ρ) Bᵢ ⇝ t)
                       (shiftBy-ren (numBinds Θ) ρ Bₑ)
                       (conv-ren (ren-convCtx Θ ρ r i) ⊢c))

------------------------------------------------------------------------
-- 4.  THE RETAGGING TRANSPORT
------------------------------------------------------------------------

-- THE REFINEMENT A TERM TRAVELS ALONG IS `_⊑ᵃ_` (strong.Ctx §4b), NOT
-- `_⊑_`: a boundary's `unlock X` claims that X is LOCKED, and `le-mu` —
-- the clause that re-exposes a concealed slot — destroys the claim
-- (`⊢ᵐ-⊑ᵃ`, strong.Terms).  TYPES and CONVERSIONS still travel along the
-- full `_⊑_`: `⊑-wf` and `conv-⊑` are applied at `⊑ᵃ→⊑ ls`.
⊢retag : ∀ {Δ Δ′ Γ M A}
  → Δ ⊑ᵃ Δ′
  → Δ  ∣ Γ ⊢ M ⦂ A
    ---------------
  → Δ′ ∣ Γ ⊢ M ⦂ A
⊢retag ls (⊢` d)       = ⊢` d
⊢retag ls ⊢$           = ⊢$
⊢retag ls (⊢ƛ w ⊢N)    = ⊢ƛ (⊑-wf (⊑ᵃ→⊑ ls) w) (⊢retag ls ⊢N)
⊢retag ls (⊢· ⊢L ⊢M)   = ⊢· (⊢retag ls ⊢L) (⊢retag ls ⊢M)
⊢retag ls (⊢Λ ⊢N)      = ⊢Λ (⊢retag (la∷ (la-uu le-aa) ls) ⊢N)
⊢retag ls (⊢·[] ⊢L w)  = ⊢·[] (⊢retag ls ⊢L) (⊑-wf (⊑ᵃ→⊑ ls) w)
⊢retag ls (env {Θ = Θ} mwᵥ ⊢M ⊢c wE) =
  env (⊢ᵐ-⊑ᵃ ls mwᵥ)
      (⊢retag (⊑ᵃ-interior Θ ls) ⊢M)
      (conv-⊑ (⊑-convCtx Θ (⊑ᵃ→⊑ ls)) ⊢c)
      (⊑-wf (⊑ᵃ→⊑ ls) wE)

------------------------------------------------------------------------
-- 5.  Term substitution
------------------------------------------------------------------------

-- TERM-VARIABLE renaming.  A boundary is TERM-CLOSED — (env) types its body
-- at Γ = [] — so this is the IDENTITY on wrappers, and so is `substᵐ` below.
-- (Shape cherry-picked from v1's `renameᵀᵐ`/`extⁿ`, which live in
-- `git show origin/main:SystemF/agda/strong/BReduction.agda`.)
extⁿ : (ℕ → ℕ) → (ℕ → ℕ)
extⁿ ρ zero    = zero
extⁿ ρ (suc x) = suc (ρ x)

renⁿ : (ℕ → ℕ) → Term → Term
renⁿ ρ (` x)          = ` (ρ x)
renⁿ ρ ($ n)          = $ n
renⁿ ρ (ƛ A ∙ N)      = ƛ A ∙ renⁿ (extⁿ ρ) N
renⁿ ρ (L · M)        = renⁿ ρ L · renⁿ ρ M
renⁿ ρ (Λ N)          = Λ (renⁿ ρ N)
renⁿ ρ (L ·[ B , A ]) = renⁿ ρ L ·[ B , A ]
renⁿ ρ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

-- The TYPE-variable weakening OF A TERM: what a Λ imposes on everything
-- that crosses under it.  Note it is NOT the identity on a wrapper — a
-- wrapper is term-closed, not type-closed, and its `seal`/`unseal` NAMES
-- shift with the frame.
⇑ᴹ : Term → Term
⇑ᴹ = renᴹ suc

-- Weakening by one term variable.  It must protect the ƛ-bound slot, hence
-- `extⁿ`: `shiftᵐ (ƛ A ∙ ` 0)` is `ƛ A ∙ ` 0`, not `ƛ A ∙ ` 1`.
shiftᵐ : Term → Term
shiftᵐ = renⁿ suc

------------------------------------------------------------------------
-- 5b.  THE IMAGES OF A SUBSTITUTION — FRAME-EXACT AT EVERY BINDER
------------------------------------------------------------------------

-- FRAME-EXACT SUBSTITUTION (Jeremy, 2026-09-08).  THE GAP THIS CLOSES.
--
-- The old Λ clause was `substᵐ (λ x → ⇑ᴹ (σ x))`: an image was SHIFTED
-- past the new Λ-bound slot and nothing else.  Shifting is enough for
-- SOUNDNESS — the image's shifted indices cannot reach slot 0 — but it is
-- not FRAME-EXACT: the image's frame silently GAINS the Λ's slot, so at
-- Examples §14's E₃ the crossing wrapper `(ΛZ. λz:Z. z) ⟪ ↓X , … ⟫`,
-- planted under `ΛY`, was read at `Y Λ-bound , ⌷[X := ℕ]` — one entry
-- MORE than its birth frame.  Every other rule is exact (`interior-dual`
-- for Peel, `interior-⋉-rewind` for CancelR/IdPush, TyBeta/TyPeelR by
-- construction); Beta was the one inexact rule.
--
-- THE REPAIR: what crosses a binder is WRAPPED IN THE BINDER'S DUAL.
-- Crossing a `Λ` is crossing an abst binder that occupies slot 0 inside,
-- so the dual of the crossing is `morph [] (lock 0 ∷ [])` — no binds, one
-- lock, exactly what `dual (morph (A ∷ []) [])` is (Examples §11) — and
-- the conversion is the IDENTITY at the value's own type, shifted past the
-- binder.  The frame identity is then DEFINITIONAL:
--
--   interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ
--
-- i.e. the image's frame IS ITS BIRTH FRAME Δ, with the crossed binder
-- masked: nothing gained, nothing lost.  It is the same shape `Peel`
-- mints for its crossing argument, so it is proved by the same two
-- moves — `⊢rename` at `suc` for the interior, `mkId-⊢` for the
-- conversion.
--
-- SUBSTITUTION MUST THEREFORE CARRY THE VALUE'S TYPE (`mkId` needs it),
-- and it may only wrap a TERM-CLOSED image ((env) types its interior at
-- Γ = []).  Both facts live in the IMAGE:
--
--   ivar x    a term VARIABLE — the identity part of the substitution.
--             It crosses a Λ untouched (a type binder does not move a
--             term index) and is never wrapped: a variable is not
--             term-closed, so `env` would refuse it.
--   ival W A  the substituted VALUE, at its type.  It is term-CLOSED
--             (`⊢ival`), which is what makes both the wrapper and the
--             weakening below legal.
data Img : Set where
  ivar : ℕ → Img
  ival : Term → Ty → Img

imgTm : Img → Term
imgTm (ivar x)   = ` x
imgTm (ival W A) = W

-- Weakening an image by one TERM variable.  A value image is CLOSED, so
-- `shiftᵐ` would be the identity on it and is not applied — which is
-- exactly why `shiftᴵ-⊢` (§6) has no premise to discharge.
shiftᴵ : Img → Img
shiftᴵ (ivar x)   = ivar (suc x)
shiftᴵ (ival W A) = ival W A

-- THE Λ CROSSING, AS A TERM: the shifted value under the DUAL of the
-- binder it crossed, with an identity conversion at its own type.
crossΛ : Term → Ty → Term
crossΛ W A = ⇑ᴹ W ⟪ morph [] (lock 0 ∷ []) , mkId (⇑ᵗ A) ⟫

-- THE Λ CLAUSE, frame-exact.  A variable image is untouched; a value
-- image is shifted AND WRAPPED, and its annotation shifts with it.
⇑ᴵ : Img → Img
⇑ᴵ (ivar x)   = ivar x
⇑ᴵ (ival W A) = ival (crossΛ W A) (⇑ᵗ A)

extᴵ : (ℕ → Img) → (ℕ → Img)
extᴵ σ zero    = ivar zero
extᴵ σ (suc x) = shiftᴵ (σ x)

substᵐ : (ℕ → Img) → Term → Term
substᵐ σ (` x)          = imgTm (σ x)
substᵐ σ ($ n)          = $ n
substᵐ σ (ƛ A ∙ N)      = ƛ A ∙ substᵐ (extᴵ σ) N
substᵐ σ (L · M)        = substᵐ σ L · substᵐ σ M
substᵐ σ (Λ N)          = Λ (substᵐ (λ x → ⇑ᴵ (σ x)) N)
substᵐ σ (L ·[ B , A ]) = substᵐ σ L ·[ B , A ]
substᵐ σ (M ⟪ Θ , c ⟫)  = M ⟪ Θ , c ⟫

-- BETA'S SUBSTITUTION.  The type is the ƛ's own annotation, so the rule
-- reads it off the redex (strong.Reduction, `Beta`).
infix 8 _[_∶_]ᵐ
_[_∶_]ᵐ : Term → Term → Ty → Term
N [ W ∶ A ]ᵐ = substᵐ (λ { zero → ival W A ; (suc x) → ivar x }) N

------------------------------------------------------------------------
-- 6.  THE SUBSTITUTION TYPING LEMMA
------------------------------------------------------------------------

-- Pulling a TERM-context lookup back through `map`.  Needed at every ⊢Λ,
-- where the body's term context is ⤊ Γ = map ⇑ᵗ Γ.  (v1's `∋-map⁻`.)
∋⦂-map⁻ : ∀ {f : Ty → Ty} {Γ x A′}
  → map f Γ ∋ x ⦂ A′
    -----------------------------------------
  → ∃[ A ] ((A′ ≡ f A) × (Γ ∋ x ⦂ A))
∋⦂-map⁻ {Γ = []}      ()
∋⦂-map⁻ {Γ = A₀ ∷ Γ₀} here      = A₀ , refl , here
∋⦂-map⁻ {Γ = A₀ ∷ Γ₀} (there d) with ∋⦂-map⁻ d
... | A , eq , q = A , eq , there q

∋⦂-⤊ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ⤊ Γ ∋ x ⦂ ⇑ᵗ A
∋⦂-⤊ here      = here
∋⦂-⤊ (there d) = there (∋⦂-⤊ d)

-- A TERM renaming survives the type-context shift a Λ imposes: the term
-- variables are untouched, only their types are shifted.
⤊-∋ⁿ : ∀ {ρ : ℕ → ℕ} {Γ Γ′}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
    -------------------------------------------
  → (∀ {x B} → ⤊ Γ ∋ x ⦂ B → ⤊ Γ′ ∋ ρ x ⦂ B)
⤊-∋ⁿ h d with ∋⦂-map⁻ d
... | A , refl , q = ∋⦂-⤊ (h q)

extⁿ-∋ : ∀ {ρ : ℕ → ℕ} {Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
    ---------------------------------------------------------------
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B → (A ∷ Γ′) ∋ extⁿ ρ x ⦂ B)
extⁿ-∋ h here      = here
extⁿ-∋ h (there d) = there (h d)

-- Term-variable renaming preserves typing.  The (env) case is LITERALLY the
-- premises back: `renⁿ` is the identity on a wrapper, and (env)'s conclusion
-- holds at an ARBITRARY term context.
⊢renⁿ : ∀ {Δ Γ Γ′ M A} {ρ : ℕ → ℕ}
  → (∀ {x B} → Γ ∋ x ⦂ B → Γ′ ∋ ρ x ⦂ B)
  → Δ ∣ Γ  ⊢ M ⦂ A
    ---------------------------
  → Δ ∣ Γ′ ⊢ renⁿ ρ M ⦂ A
⊢renⁿ h (⊢` d)            = ⊢` (h d)
⊢renⁿ h ⊢$                = ⊢$
⊢renⁿ h (⊢ƛ w ⊢N)         = ⊢ƛ w (⊢renⁿ (extⁿ-∋ h) ⊢N)
⊢renⁿ h (⊢· ⊢L ⊢M)        = ⊢· (⊢renⁿ h ⊢L) (⊢renⁿ h ⊢M)
⊢renⁿ h (⊢Λ ⊢N)           = ⊢Λ (⊢renⁿ (⤊-∋ⁿ h) ⊢N)
⊢renⁿ h (⊢·[] ⊢L w)       = ⊢·[] (⊢renⁿ h ⊢L) w
⊢renⁿ h (env mwᵥ ⊢M ⊢c wE) = env mwᵥ ⊢M ⊢c wE

-- The one type-context renaming the substitution lemma needs: pushing a
-- fresh Λ-bound slot on the front.
Ren-wk : ∀ {Δ E} → Ren suc Δ (E ∷ Δ)
Ren-wk = mkRen es

-- Term-variable renaming AT THE IDENTITY renaming is the identity.  This
-- is what makes the CLOSED-TERM weakening below a corollary of `⊢renⁿ`
-- rather than a second induction.
renⁿ-id : (ρ : ℕ → ℕ) → (∀ x → ρ x ≡ x) → (M : Term) → renⁿ ρ M ≡ M
renⁿ-id ρ h (` x)          = cong `_ (h x)
renⁿ-id ρ h ($ n)          = refl
renⁿ-id ρ h (ƛ A ∙ N)      = cong (ƛ A ∙_) (renⁿ-id (extⁿ ρ) hext N)
  where
  hext : (x : ℕ) → extⁿ ρ x ≡ x
  hext zero    = refl
  hext (suc x) = cong suc (h x)
renⁿ-id ρ h (L · M)        = cong₂ _·_ (renⁿ-id ρ h L) (renⁿ-id ρ h M)
renⁿ-id ρ h (Λ N)          = cong Λ_ (renⁿ-id ρ h N)
renⁿ-id ρ h (L ·[ B , A ]) = cong (λ L′ → L′ ·[ B , A ]) (renⁿ-id ρ h L)
renⁿ-id ρ h (M ⟪ Θ , c ⟫)  = refl

-- A TERM-CLOSED term types at ANY term context.  The hypothesis of
-- `⊢renⁿ` is vacuous at Γ = [] — there is no lookup to move — so the
-- lemma is `⊢renⁿ` at the identity renaming.
⊢weakenⁿ : ∀ {Δ Γ M A} → Δ ∣ [] ⊢ M ⦂ A → Δ ∣ Γ ⊢ M ⦂ A
⊢weakenⁿ {Γ = Γ} {M = M} {A = A} ⊢M =
  subst (λ N → _ ∣ Γ ⊢ N ⦂ A) (renⁿ-id (λ x → x) (λ x → refl) M)
        (⊢renⁿ (λ ()) ⊢M)

-- THE IMAGE TYPING JUDGEMENT.  `⊢ival` is where the two things frame-exact
-- substitution needs are recorded: the value's TYPE (which `mkId` reads)
-- and its TERM-CLOSEDNESS (which `env` demands of an interior).  Its
-- conclusion holds at an ARBITRARY term context, exactly as (env)'s does.
infix 3 _∣_⊢ⁱ_⦂_
data _∣_⊢ⁱ_⦂_ : Ctxᵗ → Ctx → Img → Ty → Set where

  ⊢ivar : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ⁱ ivar x ⦂ A

  ⊢ival : ∀ {Δ Γ W A} → Δ ⊢ᵗ A → Δ ∣ [] ⊢ W ⦂ A → Δ ∣ Γ ⊢ⁱ ival W A ⦂ A

⊢imgTm : ∀ {Δ Γ i A} → Δ ∣ Γ ⊢ⁱ i ⦂ A → Δ ∣ Γ ⊢ imgTm i ⦂ A
⊢imgTm (⊢ivar d)    = ⊢` d
⊢imgTm (⊢ival w ⊢W) = ⊢weakenⁿ ⊢W

-- (‡) THE Λ CROSSING, TYPED — the Beta analogue of PeelDual's `crossing`.
-- EVERY PREMISE IS DEFINITIONAL AT THE DUAL:
--
--   interior (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ≡ masked abst ∷ Δ
--   convCtx  (morph [] (lock 0 ∷ [])) (unmasked abst ∷ Δ) ≡ unmasked abst ∷ Δ
--   numBinds (morph [] (lock 0 ∷ [])) ≡ 0
--
-- so the interior is `⊢rename` at `suc` ALONE (`Ren-wk`, `Inj-suc`) —
-- W is typed inside at its birth frame, one masked binder in — the
-- conversion is `mkId-⊢` on the shifted type, and the `lock 0` is well
-- formed because the Λ's own slot is nameable (`sw-l`).
⊢crossΛ : ∀ {Δ W A}
  → Δ ⊢ᵗ A
  → Δ ∣ [] ⊢ W ⦂ A
    -----------------------------------------------
  → (unmasked abst ∷ Δ) ∣ [] ⊢ crossΛ W A ⦂ ⇑ᵗ A
⊢crossΛ w ⊢W =
  env (mw rw[] (sw-l (unmasked abst , ez , nameable) sw[]))
      (⊢rename Ren-wk Inj-suc ⊢W)
      (mkId-⊢ (wf-ren Ren-wk w))
      (wf-ren Ren-wk w)

-- Weakening an image: a variable image moves by `there`, a value image is
-- CLOSED and moves by nothing at all.
shiftᴵ-⊢ : ∀ {Δ Γ i A B} → Δ ∣ Γ ⊢ⁱ i ⦂ B → Δ ∣ (A ∷ Γ) ⊢ⁱ shiftᴵ i ⦂ B
shiftᴵ-⊢ (⊢ivar d)    = ⊢ivar (there d)
shiftᴵ-⊢ (⊢ival w ⊢W) = ⊢ival w ⊢W

extᴵ-⊢ : ∀ {σ : ℕ → Img} {Δ Γ Γ′ A}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ B)
    ------------------------------------------------------------------
  → (∀ {x B} → (A ∷ Γ) ∋ x ⦂ B → Δ ∣ (A ∷ Γ′) ⊢ⁱ extᴵ σ x ⦂ B)
extᴵ-⊢ h here      = ⊢ivar here
extᴵ-⊢ h (there d) = shiftᴵ-⊢ (h d)

-- ONE image across one Λ.  A variable's type shifts with the context
-- (`∋⦂-⤊`); a value acquires the DUAL WRAPPER (‡) and its annotation
-- shifts.  No knowledge premise appears: a boundary carries NAMES.
⇑ᴵ-⊢1 : ∀ {Δ Γ i A}
  → Δ ∣ Γ ⊢ⁱ i ⦂ A
    ----------------------------------------------------
  → (unmasked abst ∷ Δ) ∣ ⤊ Γ ⊢ⁱ ⇑ᴵ i ⦂ ⇑ᵗ A
⇑ᴵ-⊢1 (⊢ivar d)    = ⊢ivar (∋⦂-⤊ d)
⇑ᴵ-⊢1 (⊢ival w ⊢W) = ⊢ival (wf-ren Ren-wk w) (⊢crossΛ w ⊢W)

-- Pushing a term substitution under a Λ.
⇑ᴵ-⊢ : ∀ {σ : ℕ → Img} {Δ Γ Γ′}
  → (∀ {x B} → Γ ∋ x ⦂ B → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ B)
    ---------------------------------------------------------------------
  → (∀ {x B} → ⤊ Γ ∋ x ⦂ B → (unmasked abst ∷ Δ) ∣ ⤊ Γ′ ⊢ⁱ ⇑ᴵ (σ x) ⦂ B)
⇑ᴵ-⊢ h d with ∋⦂-map⁻ d
... | A , refl , q = ⇑ᴵ-⊢1 (h q)

-- THE SIMULTANEOUS SUBSTITUTION LEMMA.  Two cases carry the whole story:
-- (env) is trivial because a wrapper is term-closed, and ⊢Λ is `⇑ᴵ-⊢`,
-- i.e. `⊢rename` at suc PLUS THE DUAL WRAPPER (‡).
⊢substᵐ : ∀ {σ : ℕ → Img} {Δ Γ Γ′ N B}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∣ Γ′ ⊢ⁱ σ x ⦂ A)
  → Δ ∣ Γ  ⊢ N ⦂ B
    ----------------------------
  → Δ ∣ Γ′ ⊢ substᵐ σ N ⦂ B
⊢substᵐ h (⊢` d)            = ⊢imgTm (h d)
⊢substᵐ h ⊢$                = ⊢$
⊢substᵐ h (⊢ƛ w ⊢N)         = ⊢ƛ w (⊢substᵐ (extᴵ-⊢ h) ⊢N)
⊢substᵐ h (⊢· ⊢L ⊢M)        = ⊢· (⊢substᵐ h ⊢L) (⊢substᵐ h ⊢M)
⊢substᵐ h (⊢Λ ⊢N)           = ⊢Λ (⊢substᵐ (⇑ᴵ-⊢ h) ⊢N)
⊢substᵐ h (⊢·[] ⊢L w)       = ⊢·[] (⊢substᵐ h ⊢L) w
⊢substᵐ h (env mwᵥ ⊢M ⊢c wE) = env mwᵥ ⊢M ⊢c wE

-- THE SUBSTITUTION TYPING LEMMA — what Beta's preservation case consumes.
-- THE VALUE IS TERM-CLOSED AND ITS TYPE IS CARRIED: both are what the
-- wrapper minted at a crossed Λ needs, and both are on Beta's redex (the
-- rule reduces closed terms, and the type is the ƛ's annotation).
⊢subst : ∀ {Δ Γ A B N W}
  → Δ ⊢ᵗ A
  → Δ ∣ (A ∷ Γ) ⊢ N ⦂ B
  → Δ ∣ [] ⊢ W ⦂ A
    -----------------------------
  → Δ ∣ Γ ⊢ N [ W ∶ A ]ᵐ ⦂ B
⊢subst w ⊢N ⊢W =
  ⊢substᵐ (λ { here → ⊢ival w ⊢W ; (there d) → ⊢ivar d }) ⊢N

-- Beta preservation, ready to be wired into the preservation theorem.
-- (⊢·) is the only rule that can conclude an application — (env) concludes a
-- wrapper — so the inversion is a single clause, and it hands over BOTH
-- things `⊢subst` now asks for: the ƛ's `Δ ⊢ᵗ A` and the argument's typing
-- at Γ = [].
preserve-Beta : ∀ {Δ A B N W}
  → Δ ∣ [] ⊢ (ƛ A ∙ N) · W ⦂ B
    ------------------------------
  → Δ ∣ [] ⊢ N [ W ∶ A ]ᵐ ⦂ B
preserve-Beta (⊢· (⊢ƛ w ⊢N) ⊢W) = ⊢subst w ⊢N ⊢W
