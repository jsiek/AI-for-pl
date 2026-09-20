module strong.notes.AddLock0Wall where

-- `TyPeelR-⟪⟫` RE-SPELLS ITS MOVED CONVERSION IN THE WRONG NAME MAP
-- (2026-09-20).  `AddLock0Typing` — preservation's last parameter — is
-- FALSE, and not for want of a premise: the REDUCTION RULE is unsound.
-- A closed, plain System F program, with no boundary written by hand,
-- loses its type three steps in.
--
-- THE CONTRACTUM.  `TyPeelR-⟪⟫` moves the inner boundary out by one new
-- representation binder and one new ordinary name, and re-spells its
-- three parts SEPARATELY:
--
--     renᴹ² (ren² idᵗ (extN (numBinds Θ′) suc)) W   -- the interior term
--       ⟪ addLock0 (renᴮ² (ren² idᵗ suc) Θ′)        -- the frame
--       , `∀ (renᶜ (extᵗ suc) s′) ⟫                 -- the conversion
--
-- The first two are right.  `addLock0` APPENDS `lock 0 (numBinds Θ′)` to
-- the change list, and a change list acts head-LAST, so that lock runs
-- FIRST: in the INTERIOR reading it deletes the new ordinary name before
-- any of Θ′'s own changes run, which is exactly what leaves every
-- ordinary position of the moved term where it was.
--
-- THE CONVERSION IS READ SOMEWHERE ELSE.  `env` checks it at the
-- boundary's CONVERSION context, and the conversion reading SKIPS locks
-- (`conv-lock`, strong.CtxMorph §3) — that is the whole point of a
-- conversion context: it is the union of the names live anywhere along
-- the morphism.  So the new name is NOT deleted there, and every
-- `unlock X α` of Θ′ then inserts at position X of a map that already
-- carries it.  The new name is therefore DISPLACED by Θ′'s unlocks,
-- while `renᶜ (extᵗ suc) s′` — which is `renᶜ suc` on the whole `` `∀ ``
-- conversion — assumes it landed at position ZERO.
--
-- ONE UNLOCK IS ENOUGH, and `TyBeta` mints one: `instantiate R Θ`
-- appends `unlock 0 0`.  In the run below the moved boundary's
-- conversion context goes
--
--     (bindR `ℕ ∷ abstR ∷ [])             ∣ (0 ∷ [])       -- before
--     (bindR `ℕ ∷ bindR `𝔹 ∷ abstR ∷ [])  ∣ (0 ∷ 1 ∷ [])   -- after
--
-- (`conv-before` and `conv-after` below).  The new ordinary name lands at
-- position ONE, not zero: position 0 still names the `TyBeta` binder
-- `bindR `ℕ`.  `renᶜ suc` moves the conversion's occurrences of position
-- 0 onto position 1 — onto the NEW binder, whose payload is the type
-- argument `` `𝔹 ``.  `seal 1 ↦ unseal 1`, which converted
-- `` ` 1 ⇒ ` 1 `` to `` `ℕ ⇒ `ℕ ``, becomes `seal 2 ↦ unseal 2`, which
-- converts `` ` 2 ⇒ ` 2 `` to `` `𝔹 ⇒ `𝔹 ``; and `env`'s exterior
-- alignment `SameTyExt` then has to relate `` `∀ (`ℕ ⇒ `ℕ) `` to
-- `` `∀ (`𝔹 ⇒ `𝔹) ``, which it cannot.
--
-- WHY NO PREMISE REPAIRS IT.  The offending spelling is in the
-- CONTRACTUM, so no hypothesis on the redex can change it; and the
-- correct re-spelling is not a renaming at all — where the new name ends
-- up depends on Θ′'s own unlocks.  This is precisely the defect the
-- crossing audit found for `Peel` on 2026-09-18 ("not merely a
-- renumbering of the same one", strong.Reduction): the repair there was
-- to NAME the re-spelled conversion in the rule and carry a `SameConv`
-- relating it to the original, with `respell`/`Q` (strong.Conversion §2b,
-- strong.CtxMorph §3b) supplying the witness.  `TyPeelR-⟪⟫` needs the
-- same repair, and that is Jeremy's call; this module only records the
-- wall.
--
-- WHAT SURVIVES OF THE DECOMPOSITION.  The representation half is fine
-- and is proved elsewhere: the mover is `renᴹᴿ (extN (numBinds Θ′) suc)`
-- by `renᴹ²-ord-id`/`renᴮ²-ord-id`, and the head insertion is
-- `repwk-cons₀` (strong.CtxMorph §3d, added with this note) pushed
-- through `repwk-push`.  The interior reading of `addLock0 Θ′` is the
-- interior reading of Θ′, because the appended lock deletes the new name
-- first.  It is the CONVERSION reading, and only it, that the rule gets
-- wrong.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction
open import strong.TypeCheck using (tc)
open import strong.Eval using (eval; report; repKept; traceEnd;
                              eval-sound)
open import strong.Preservation using (Preservation; Preservation*)
open import strong.proof.Preserve using (AddLock0Typing)

------------------------------------------------------------------------
-- §1  A closed, plain source program, and its run
------------------------------------------------------------------------

--   Src = (λf : ∀X. ℕ⇒ℕ. ΛX. f [𝔹])
--           · ((ΛY. ΛZ. λx:Y. x) [ℕ])
--
-- The argument packages a polymorphic identity whose type MENTIONS the
-- outer binder, so `TyBeta` mints a `` `∀ `` conversion with a real
-- `seal`/`unseal` pair in it.  The function then carries that value
-- under a `Λ`, which wraps it in the binder's dual (`crossΛᴹ`) — a
-- SECOND `` `∀ `` boundary — and applies it to a type.  That application
-- is the `TyPeelR-⟪⟫` redex.

Vfun Pkg Use Src : Term
Vfun = Λ (ƛ (` 1) ∙ ` 0)
Pkg  = (Λ Vfun) ·[ `∀ (` 1 ⇒ ` 1) , `ℕ ]
Use  = ƛ (`∀ (`ℕ ⇒ `ℕ)) ∙ Λ ((` 0) ·[ `ℕ ⇒ `ℕ , `𝔹 ])
Src  = Use · Pkg

Src-⊢ : empty ∣ [] ⊢ Src ⦂ `∀ (`ℕ ⇒ `ℕ)
Src-⊢ = tc

-- The run is `TyBeta`, then `Beta`, then `TyPeelR-⟪⟫` — and the
-- evaluator's own per-state check REJECTS the third contractum.  That
-- check is only a checker's verdict; §3 proves the state untypeable.
run-loses-the-type : repKept (report (eval 10 Src Src-⊢)) ≡ false
run-loses-the-type = refl

------------------------------------------------------------------------
-- §2  The state the run reaches, and the two conversion contexts
------------------------------------------------------------------------

-- the inner boundary `TyBeta` minted, carried under the `Λ` by `Beta`
Θ′ : CtxMorph
Θ′ = renᴮ² (ren² (λ X → X) suc) TyBetaMorph

inner : Term
inner = Vfun ⟪ Θ′ , `∀ (seal 1 ↦ unseal 1) ⟫

-- its exterior, and the context it is moved to: one `bindR `𝔹` (the
-- type argument's representation) and one new ordinary name for it
Δᵢ Δ⁺ : Ctxᵗ
Δᵢ = (abstR ∷ []) ∣ []
Δ⁺ = (bindR `𝔹 ∷ abstR ∷ []) ∣ (0 ∷ [])

⊢inner : Δᵢ ∣ [] ⊢ inner ⦂ `∀ (`ℕ ⇒ `ℕ)
⊢inner = tc

wf⁺ : WfCtx Δ⁺
wf⁺ = wf-ctx (wf-bindR wfᴿ-𝔹 (wf-abstR wf-reps[])) vn
             (unique∷ fresh[] unique[])
  where
  vn : ValidNames (bindR `𝔹 ∷ abstR ∷ []) (0 ∷ [])
  vn here = bindR `𝔹 , here

-- THE TWO CONVERSION CONTEXTS.  Before the move the boundary's own
-- conversion context names one representation variable; after it, two —
-- and the NEW one is at position 1, because the skipped `lock 0 1` left
-- it in place and Θ′'s `unlock 0 0` inserted in front of it.
Δᶜ′ Δᶜ⁺ : Ctxᵗ
Δᶜ′ = (bindR `ℕ ∷ abstR ∷ []) ∣ (0 ∷ [])
Δᶜ⁺ = (bindR `ℕ ∷ bindR `𝔹 ∷ abstR ∷ []) ∣ (0 ∷ 1 ∷ [])

conv-before : Δᵢ ⊢ᶜ Θ′ ⇒ Δᶜ′
conv-before =
  conversion (conv-unlock (bindR `ℕ , here) conv[] fresh[] ins-here)

AL : CtxMorph
AL = addLock0 Θ′

conv-after : Δ⁺ ⊢ᶜ AL ⇒ Δᶜ⁺
conv-after =
  conversion
    (conv-unlock (bindR `ℕ , here)
      (conv-lock (bindR `𝔹 , there here) conv[])
      (fresh∷ (λ ()) fresh[])
      ins-here)

-- the moved boundary, and the whole state the run stops at
moved bad : Term
moved = Vfun ⟪ AL , `∀ (seal 2 ↦ unseal 2) ⟫
bad = (moved ·[ `ℕ ⇒ `ℕ , ` 0 ])
        ⟪ morph (`𝔹 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
        , id `ℕ ↦ id `ℕ ⟫

the-run : empty ⊢ Src -→* Λ bad
the-run = eval-sound 10 Src-⊢

------------------------------------------------------------------------
-- §3  That state has no typing derivation
------------------------------------------------------------------------

-- The moved conversion reads the NEW binder, whose payload is `` `𝔹 ``.
sq2 : underΛ Δᶜ⁺ ∋ 2 := `𝔹
sq2 = 2 , `𝔹 , there (there here) , r-there-abst (r-there r-here)
    , same-𝔹

⊢c⁺ : Δᶜ⁺ ⊢ `∀ (seal 2 ↦ unseal 2) ∶ `∀ (` 2 ⇒ ` 2) ⇝ `∀ (`𝔹 ⇒ `𝔹)
⊢c⁺ = conv-all (conv-fun (conv-seal sq2) (conv-unseal sq2))

uq⁺ : Unique (names Δᶜ⁺)
uq⁺ = unique∷ (fresh∷ (λ ()) fresh[]) (unique∷ fresh[] unique[])

-- The conversion context is a FUNCTION of the morphism and its exterior,
-- so `conv-after` IS the one `env` stored; the conversion's types are
-- then unique on it; and the exterior alignment asks for `` `ℕ ⇒ `ℕ ``
-- to read as the representation `` `𝔹 ⇒ `𝔹 ``.
no-moved : ¬ (Δ⁺ ∣ [] ⊢ moved ⦂ `∀ (`ℕ ⇒ `ℕ))
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
  with conversion-functional (mw-conversion mwΘ) conv-after
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl
  with conv-types-unique uq⁺ ⊢c ⊢c⁺
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl | refl , refl
  with sameₑ
no-moved (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | refl | refl , refl
  | S , same-∀ (same-⇒ same-ℕ same-ℕ) , same-∀ (same-⇒ () q)

-- The pushed-in type application demands exactly the type the moved
-- boundary cannot have: its annotation is `renameᵗ (extᵗ suc) Bᵢ′`,
-- which here is `` `ℕ ⇒ `ℕ ``.
int⁺ : underΛ empty ⊢ⁱ morph (`𝔹 ∷ []) (lock 1 1 ∷ unlock 0 0 ∷ [])
         ⇒ Δ⁺
int⁺ =
  interior
    (changes∷ (changes∷ changes[]
                (step-unlock (bindR `𝔹 , here) (fresh∷ (λ ()) fresh[])
                             ins-here))
              (step-lock (abstR , there here) (del-there del-here)
                         (fresh∷ (λ ()) fresh[])))

no-bad : ¬ (underΛ empty ∣ [] ⊢ bad ⦂ `ℕ ⇒ `ℕ)
no-bad (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE)
  with interior-functional (mw-interior mwΘ) int⁺
no-bad (env mwΘ (⊢·[] ⊢L wA) ⊢c sameᵢ sameₑ wE) | refl = no-moved ⊢L

no-state : ¬ (empty ∣ [] ⊢ Λ bad ⦂ `∀ (`ℕ ⇒ `ℕ))
no-state (⊢Λ ⊢N) = no-bad ⊢N

------------------------------------------------------------------------
-- §4  The two refutations
------------------------------------------------------------------------

-- (i) the transport statement itself, at exactly the instance the run
-- produces: Δ is the outer boundary's interior, W is `Vfun`, Θ is the
-- `TyBeta` frame, and P is the type argument's representation `` `𝔹 ``.
no-addLock0 : ¬ AddLock0Typing
no-addLock0 al =
  no-moved (al {Δ = Δᵢ} {W = Vfun} {Θ = Θ′}
               {s = seal 1 ↦ unseal 1} {A = `ℕ ⇒ `ℕ} {P = `𝔹}
               wf⁺ ⊢inner)

-- (ii) and therefore preservation, which no choice of parameter can
-- rescue: the program above is closed, plain source, and its run is the
-- one `det` allows.
pres→pres* : Preservation → Preservation*
pres→pres* pres wfΔ ⊢M done = ⊢M
pres→pres* pres wfΔ ⊢M (st then sts) =
  pres→pres* pres wfΔ (pres wfΔ ⊢M st) sts

no-preservation* : ¬ Preservation*
no-preservation* pres* = no-state (pres* wf-empty Src-⊢ the-run)

no-preservation : ¬ Preservation
no-preservation pres = no-preservation* (pres→pres* pres)
