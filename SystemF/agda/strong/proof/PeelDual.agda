module strong.proof.PeelDual where

-- THE PEEL REPAIR — with the fixed `dual` (strong.Reduction), `intC-dual`
-- and `fceC-dual` are TRUE in general and `PeelCase` is PROVEN.
--
--   intC (dual Θ) (intC Θ Δ) ≡ map blk (prep (reps Θ) []) ++ fscp Θ Δ
--   fceC (dual Θ) (intC Θ Δ) ≡ fceC Θ Δ
--
-- The crossing argument (typed in Δ) retypes one owner-frame deeper by
-- `⊢rename (wkN (nbind Θ))` + `⊢retag` (the tail relaxes Δ ⊑ fscp Θ Δ),
-- and the face `s` transplants verbatim through `fceC-dual`.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-step)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
open import strong.TypeSubst using (rename-cong; rename-rename-commute)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction using (lockBinds; reps→bind; dualS; dual)
open import strong.proof.Preserve using (PeelCase; ⊢ᵗ-of; CtxWf-[])
open import strong.proof.Canonical using (liftN-⇒; conv-tgt≡)

------------------------------------------------------------------------
-- Structural helpers
------------------------------------------------------------------------

scp-++ : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → scp (Θ₁ ++ Θ₂) Δ ≡ scp Θ₁ (scp Θ₂ Δ)
scp-++ []              Θ₂ Δ = refl
scp-++ (bind A ∷ Θ₁)   Θ₂ Δ = scp-++ Θ₁ Θ₂ Δ
scp-++ (unlock X ∷ Θ₁) Θ₂ Δ = cong (unmask X) (scp-++ Θ₁ Θ₂ Δ)
scp-++ (lock X ∷ Θ₁)   Θ₂ Δ = cong (mask X) (scp-++ Θ₁ Θ₂ Δ)

fscp-++ : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → fscp (Θ₁ ++ Θ₂) Δ ≡ fscp Θ₁ (fscp Θ₂ Δ)
fscp-++ []              Θ₂ Δ = refl
fscp-++ (bind A ∷ Θ₁)   Θ₂ Δ = fscp-++ Θ₁ Θ₂ Δ
fscp-++ (unlock X ∷ Θ₁) Θ₂ Δ = cong (unmask X) (fscp-++ Θ₁ Θ₂ Δ)
fscp-++ (lock X ∷ Θ₁)   Θ₂ Δ = fscp-++ Θ₁ Θ₂ Δ

prep-++ : (As : List Ty) (Δ : Ctxᵗ) → prep As Δ ≡ prep As [] ++ Δ
prep-++ []       Δ = refl
prep-++ (A ∷ As) Δ rewrite prep-++ As Δ | prep-++ As [] = refl

length-prep : (As : List Ty) → length (prep As []) ≡ length As
length-prep []       = refl
length-prep (A ∷ As) = cong suc (length-prep As)

-- Two in-place updates commute.
upd-upd-comm : (f : Ent → Ent) (a b : ℕ) (Δ : Ctxᵗ)
  → upd f a (upd f b Δ) ≡ upd f b (upd f a Δ)
upd-upd-comm f a       b       []      = refl
upd-upd-comm f zero    zero    (E ∷ Δ) = refl
upd-upd-comm f zero    (suc b) (E ∷ Δ) = refl
upd-upd-comm f (suc a) zero    (E ∷ Δ) = refl
upd-upd-comm f (suc a) (suc b) (E ∷ Δ) =
  cong (E ∷_) (upd-upd-comm f a b Δ)

-- mask/unmask at a position ≥ |Ow| only touches the tail.
upd-app-tail : (f : Ent → Ent) (Ow : Ctxᵗ) (X : ℕ) (Δ : Ctxᵗ)
  → upd f (length Ow + X) (Ow ++ Δ) ≡ Ow ++ upd f X Δ
upd-app-tail f []       X Δ = refl
upd-app-tail f (E ∷ Ow) X Δ = cong (E ∷_) (upd-app-tail f Ow X Δ)

-- Unmasking a slot undoes masking it, on the nose.
unmask-mask : (a : ℕ) (Ξ : Ctxᵗ) → unmask a (mask a Ξ) ≡ Ξ
unmask-mask zero    []      = refl
unmask-mask (suc a) []      = refl
unmask-mask zero    (E ∷ Ξ) = cong (_∷ Ξ) (unblk-blk E)
  where
  unblk-blk : (E : Ent) → unblk (blk E) ≡ E
  unblk-blk E = refl
unmask-mask (suc a) (E ∷ Ξ) = cong (E ∷_) (unmask-mask a Ξ)

-- dualS is all-unlock, so its `scp` commutes with any extra unmask.
dualS-unmask-comm : (n : ℕ) (Θ : CtxMorph) (Y : ℕ) (Δ : Ctxᵗ)
  → scp (dualS n Θ) (unmask Y Δ) ≡ unmask Y (scp (dualS n Θ) Δ)
dualS-unmask-comm n []             Y Δ = refl
dualS-unmask-comm n (bind A ∷ Θ)   Y Δ = dualS-unmask-comm n Θ Y Δ
dualS-unmask-comm n (unlock X ∷ Θ) Y Δ = dualS-unmask-comm n Θ Y Δ
dualS-unmask-comm n (lock X ∷ Θ)   Y Δ
  rewrite dualS-unmask-comm n Θ Y Δ =
  upd-upd-comm unblk (n + X) Y (scp (dualS n Θ) Δ)

------------------------------------------------------------------------
-- STEP A: dualS unmasks exactly Θ's lock positions, turning scp into fscp.
------------------------------------------------------------------------

stepA : (Ow : Ctxᵗ) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scp (dualS (length Ow) Θ) (Ow ++ scp Θ Δ) ≡ Ow ++ fscp Θ Δ
stepA Ow []             Δ = refl
stepA Ow (bind A ∷ Θ)   Δ = stepA Ow Θ Δ
stepA Ow (unlock X ∷ Θ) Δ
  rewrite sym (upd-app-tail unblk Ow X (scp Θ Δ))
        | dualS-unmask-comm (length Ow) Θ (length Ow + X) (Ow ++ scp Θ Δ)
        | stepA Ow Θ Δ =
  upd-app-tail unblk Ow X (fscp Θ Δ)
stepA Ow (lock X ∷ Θ)   Δ
  rewrite sym (dualS-unmask-comm (length Ow) Θ (length Ow + X)
                 (Ow ++ mask X (scp Θ Δ)))
        | upd-app-tail unblk Ow X (mask X (scp Θ Δ))
        | unmask-mask X (scp Θ Δ)
        | stepA Ow Θ Δ = refl

------------------------------------------------------------------------
-- STEP B: lockBinds masks the whole owner prefix.
------------------------------------------------------------------------

lockBinds-cons : (k : ℕ) (E : Ent) (Ξ : Ctxᵗ)
  → scp (lockBinds (suc k)) (E ∷ Ξ) ≡ blk E ∷ scp (lockBinds k) Ξ
lockBinds-cons zero    E Ξ = refl
lockBinds-cons (suc k) E Ξ
  rewrite lockBinds-cons k E Ξ = refl

stepB : (Ow Δ : Ctxᵗ)
  → scp (lockBinds (length Ow)) (Ow ++ Δ) ≡ map blk Ow ++ Δ
stepB []       Δ = refl
stepB (E ∷ Ow) Δ
  rewrite lockBinds-cons (length Ow) E (Ow ++ Δ)
        | stepB Ow Δ = refl

-- dual produces no binders, so its `prep` is the identity.
reps-lockBinds : (k : ℕ) → reps (lockBinds k) ≡ []
reps-lockBinds zero    = refl
reps-lockBinds (suc k) = reps-lockBinds k

reps-dualS : (n : ℕ) (Θ : CtxMorph) → reps (dualS n Θ) ≡ []
reps-dualS n []             = refl
reps-dualS n (bind A ∷ Θ)   = reps-dualS n Θ
reps-dualS n (unlock X ∷ Θ) = reps-dualS n Θ
reps-dualS n (lock X ∷ Θ)   = reps-dualS n Θ

reps-++ : (Θ₁ Θ₂ : CtxMorph) → reps (Θ₁ ++ Θ₂) ≡ reps Θ₁ ++ reps Θ₂
reps-++ []              Θ₂ = refl
reps-++ (bind A ∷ Θ₁)   Θ₂ = cong (_ ∷_) (reps-++ Θ₁ Θ₂)
reps-++ (unlock X ∷ Θ₁) Θ₂ = reps-++ Θ₁ Θ₂
reps-++ (lock X ∷ Θ₁)   Θ₂ = reps-++ Θ₁ Θ₂

reps-dual : (Θ : CtxMorph) → reps (dual Θ) ≡ []
reps-dual Θ rewrite reps-++ (lockBinds (nbind Θ)) (dualS (nbind Θ) Θ)
                   | reps-lockBinds (nbind Θ)
                   | reps-dualS (nbind Θ) Θ = refl

------------------------------------------------------------------------
-- intC-dual : the honest RHS, PROVEN
------------------------------------------------------------------------

intC-dual : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → intC (dual Θ) (intC Θ Δ)
      ≡ map blk (prep (reps Θ) []) ++ fscp Θ Δ
intC-dual Θ Δ
  rewrite reps-dual Θ
        | prep-++ (reps Θ) (scp Θ Δ)
  = go
  where
  Ow : Ctxᵗ
  Ow = prep (reps Θ) []
  lenOw : length Ow ≡ nbind Θ
  lenOw = length-prep (reps Θ)
  -- intC (dual Θ) Ξ = scp (dual Θ) Ξ  (dual has no binds)
  go : scp (dual Θ) (Ow ++ scp Θ Δ) ≡ map blk Ow ++ fscp Θ Δ
  go rewrite scp-++ (lockBinds (nbind Θ)) (dualS (nbind Θ) Θ) (Ow ++ scp Θ Δ)
           | sym lenOw
           | stepA Ow Θ Δ
           | stepB Ow (fscp Θ Δ) = refl

------------------------------------------------------------------------
-- fceC-dual : the face context is UNCHANGED by the dual
------------------------------------------------------------------------

-- On an all-unlock morphism (like dualS), fscp = scp.
fscp-dualS : (n : ℕ) (Θ : CtxMorph) (Ξ : Ctxᵗ)
  → fscp (dualS n Θ) Ξ ≡ scp (dualS n Θ) Ξ
fscp-dualS n []             Ξ = refl
fscp-dualS n (bind A ∷ Θ)   Ξ = fscp-dualS n Θ Ξ
fscp-dualS n (unlock X ∷ Θ) Ξ = fscp-dualS n Θ Ξ
fscp-dualS n (lock X ∷ Θ)   Ξ =
  cong (unmask (n + X)) (fscp-dualS n Θ Ξ)

-- fscp skips locks, so lockBinds is invisible to the face context.
fscp-lockBinds : (k : ℕ) (Ξ : Ctxᵗ) → fscp (lockBinds k) Ξ ≡ Ξ
fscp-lockBinds zero    Ξ = refl
fscp-lockBinds (suc k) Ξ = fscp-lockBinds k Ξ

fceC-dual : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → fceC (dual Θ) (intC Θ Δ) ≡ fceC Θ Δ
fceC-dual Θ Δ
  rewrite reps-dual Θ
        | prep-++ (reps Θ) (scp Θ Δ)
        | prep-++ (reps Θ) (fscp Θ Δ)
  = go
  where
  Ow : Ctxᵗ
  Ow = prep (reps Θ) []
  lenOw : length Ow ≡ nbind Θ
  lenOw = length-prep (reps Θ)
  go : fscp (dual Θ) (Ow ++ scp Θ Δ) ≡ Ow ++ fscp Θ Δ
  go rewrite fscp-++ (lockBinds (nbind Θ)) (dualS (nbind Θ) Θ)
                     (Ow ++ scp Θ Δ)
           | fscp-lockBinds (nbind Θ) (fscp (dualS (nbind Θ) Θ) (Ow ++ scp Θ Δ))
           | fscp-dualS (nbind Θ) Θ (Ow ++ scp Θ Δ)
           | sym lenOw
           | stepA Ow Θ Δ = refl


------------------------------------------------------------------------
-- Renaming identity/composition and wkN = liftN
------------------------------------------------------------------------

renameᵗ-id : (a : Ty) → renameᵗ (λ X → X) a ≡ a
renameᵗ-id (` X)   = refl
renameᵗ-id `ℕ      = refl
renameᵗ-id `𝔹      = refl
renameᵗ-id (a ⇒ b) = cong₂ _⇒_ (renameᵗ-id a) (renameᵗ-id b)
renameᵗ-id (`∀ a)  =
  cong `∀ (trans (rename-cong ext-id a) (renameᵗ-id a))
  where
  ext-id : (X : ℕ) → extᵗ (λ Y → Y) X ≡ X
  ext-id zero    = refl
  ext-id (suc X) = refl

renᵉ-id : (E : Ent) → renᵉ (λ X → X) E ≡ E
renᵉ-id abst     = refl
renᵉ-id (bind A) = cong bind (renameᵗ-id A)
renᵉ-id (blk E)  = cong blk (renᵉ-id E)

renᵉ-comp : (ρ₁ ρ₂ : Renameᵗ) (E : Ent)
  → renᵉ ρ₂ (renᵉ ρ₁ E) ≡ renᵉ (λ X → ρ₂ (ρ₁ X)) E
renᵉ-comp ρ₁ ρ₂ abst     = refl
renᵉ-comp ρ₁ ρ₂ (bind A) = cong bind (rename-rename-commute ρ₁ ρ₂ A)
renᵉ-comp ρ₁ ρ₂ (blk E)  = cong blk (renᵉ-comp ρ₁ ρ₂ E)

renᵗ-wkN : (n : ℕ) (A : Ty) → renameᵗ (wkN n) A ≡ liftN n A
renᵗ-wkN zero    A = renameᵗ-id A
renᵗ-wkN (suc m) A =
  trans (sym (rename-rename-commute (wkN m) suc A))
        (cong ⇑ᵗ (renᵗ-wkN m A))

------------------------------------------------------------------------
-- ⊑ facts: Δ ⊑ fscp Θ Δ, and ⊑ under a common prefix
------------------------------------------------------------------------

ent⊑unblk : (E : Ent) → E ⊑ᵉ unblk E
ent⊑unblk abst     = le-aa
ent⊑unblk (bind A) = le-oo
ent⊑unblk (blk E)  = blk-le (⊑ᵉ-refl E)

⊑-unmask : (X : ℕ) (Ξ : Ctxᵗ) → Ξ ⊑ unmask X Ξ
⊑-unmask X       []      = le[]
⊑-unmask zero    (E ∷ Ξ) = le∷ (ent⊑unblk E) (⊑-refl Ξ)
⊑-unmask (suc X) (E ∷ Ξ) = le∷ (⊑ᵉ-refl E) (⊑-unmask X Ξ)

Δ⊑fscp : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊑ fscp Θ Δ
Δ⊑fscp []             Δ = ⊑-refl Δ
Δ⊑fscp (bind A ∷ Θ)   Δ = Δ⊑fscp Θ Δ
Δ⊑fscp (unlock X ∷ Θ) Δ = ⊑-trans (Δ⊑fscp Θ Δ) (⊑-unmask X (fscp Θ Δ))
  where
  ⊑-trans : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⊑ Δ₂ → Δ₂ ⊑ Δ₃ → Δ₁ ⊑ Δ₃
  ⊑-trans le[]        le[]        = le[]
  ⊑-trans (le∷ l ls)  (le∷ m ms)  = le∷ (⊑ᵉ-trans l m) (⊑-trans ls ms)
    where
    ⊑ᵉ-trans : ∀ {E₁ E₂ E₃} → E₁ ⊑ᵉ E₂ → E₂ ⊑ᵉ E₃ → E₁ ⊑ᵉ E₃
    ⊑ᵉ-trans le-aa        m           = m
    ⊑ᵉ-trans le-ao        le-oo       = le-ao
    ⊑ᵉ-trans le-oo        le-oo       = le-oo
    ⊑ᵉ-trans (le-bb l)    (le-bb m)   = le-bb (⊑ᵉ-trans l m)
    ⊑ᵉ-trans (le-bb l)    (le-bu m v) = le-bu (⊑ᵉ-trans l m) v
    ⊑ᵉ-trans (le-bu l vE) m           = le-bu (⊑ᵉ-trans l m) (vis-mono m vE)
Δ⊑fscp (lock X ∷ Θ)   Δ = Δ⊑fscp Θ Δ

⊑-app : (Ξ : Ctxᵗ) {Δ Δ′ : Ctxᵗ} → Δ ⊑ Δ′ → (Ξ ++ Δ) ⊑ (Ξ ++ Δ′)
⊑-app []       ls = ls
⊑-app (E ∷ Ξ) ls = le∷ (⊑ᵉ-refl E) (⊑-app Ξ ls)

------------------------------------------------------------------------
-- Ren (wkN (length Ξ)) Δ (Ξ ++ Δ)
------------------------------------------------------------------------

ren∋-wkN : (Ξ : Ctxᵗ) {Δ : Ctxᵗ} {X : ℕ} {E : Ent}
  → Δ ∋e X , E → (Ξ ++ Δ) ∋e (length Ξ + X) , renᵉ (wkN (length Ξ)) E
ren∋-wkN []      {E = E} d =
  subst (λ e → _ ∋e _ , e) (sym (renᵉ-id E)) d
ren∋-wkN (F ∷ Ξ) {E = E} d =
  subst (λ e → _ ∋e _ , e)
        (trans (renᵉ-comp (wkN (length Ξ)) suc E) refl)
        (es (ren∋-wkN Ξ d))

Ren-wkN : (Ξ : Ctxᵗ) {Δ : Ctxᵗ} → Ren (wkN (length Ξ)) Δ (Ξ ++ Δ)
Ren-wkN Ξ = mkRen (ren∋-wkN Ξ)

------------------------------------------------------------------------
-- Bwf (intC Θ Δ) (dual Θ)
------------------------------------------------------------------------

Bwf-++ : ∀ {Δ Θ₁ Θ₂} → Bwf Δ Θ₁ → Bwf Δ Θ₂ → Bwf Δ (Θ₁ ++ Θ₂)
Bwf-++ bw[]        b₂ = b₂
Bwf-++ (bw-b w b)  b₂ = bw-b w (Bwf-++ b b₂)
Bwf-++ (bw-l tv b) b₂ = bw-l tv (Bwf-++ b b₂)
Bwf-++ (bw-u d b)  b₂ = bw-u d (Bwf-++ b b₂)

-- owner slots of a prep are visible
prep-∋tv : (As : List Ty) (Ξ : Ctxᵗ) (j : ℕ)
  → j < length As → prep As Ξ ∋tv j
prep-∋tv (A ∷ As) Ξ zero    (s≤s _)  = bind _ , ez , vis-b
prep-∋tv (A ∷ As) Ξ (suc j) (s≤s lt) with prep-∋tv As Ξ j lt
... | E , d , v = _ , es d , renᵉ-Vis v

Bwf-lockBinds : (k : ℕ) (Ξ : Ctxᵗ)
  → ((j : ℕ) → j < k → Ξ ∋tv j) → Bwf Ξ (lockBinds k)
Bwf-lockBinds zero    Ξ h = bw[]
Bwf-lockBinds (suc k) Ξ h =
  bw-l (h k ≤-refl) (Bwf-lockBinds k Ξ (λ j lt → h j (≤-step lt)))

-- existence of a slot survives an in-place update
upd-∋e-ex : (f : Ent → Ent) (Y : ℕ) {Δ : Ctxᵗ} {X : ℕ} {E : Ent}
  → Δ ∋e X , E → ∃[ E′ ] (upd f Y Δ ∋e X , E′)
upd-∋e-ex f zero    ez        = _ , ez
upd-∋e-ex f (suc Y) ez        = _ , ez
upd-∋e-ex f zero    (es d)    = _ , es d
upd-∋e-ex f (suc Y) (es d) with upd-∋e-ex f Y d
... | E′ , d′ = _ , es d′

scp-∋e-ex : (Θ : CtxMorph) {Δ : Ctxᵗ} {X : ℕ} {E : Ent}
  → Δ ∋e X , E → ∃[ E′ ] (scp Θ Δ ∋e X , E′)
scp-∋e-ex []             d = _ , d
scp-∋e-ex (bind A ∷ Θ)   d = scp-∋e-ex Θ d
scp-∋e-ex (unlock Y ∷ Θ) d with scp-∋e-ex Θ d
... | E′ , d′ = upd-∋e-ex unblk Y d′
scp-∋e-ex (lock Y ∷ Θ)   d with scp-∋e-ex Θ d
... | E′ , d′ = upd-∋e-ex blk Y d′

-- a slot of prep(As)Ξ past the owners
prep-∋e-tail : (As : List Ty) {Ξ : Ctxᵗ} {X : ℕ} {E : Ent}
  → Ξ ∋e X , E → ∃[ E′ ] (prep As Ξ ∋e (length As + X) , E′)
prep-∋e-tail As {Ξ} {X} d
  rewrite prep-++ As Ξ
        | sym (length-prep As) =
  _ , ren∋-wkN (prep As []) d

Bwf-dualS-self : (Θ : CtxMorph) (Δ : Ctxᵗ) → Bwf Δ Θ
  → Bwf (intC Θ Δ) (dualS (nbind Θ) Θ)
Bwf-dualS-self Θ Δ bwΘ = go Θ bwΘ
  where
  go : (Ξ : CtxMorph) → Bwf Δ Ξ → Bwf (intC Θ Δ) (dualS (nbind Θ) Ξ)
  go []             _            = bw[]
  go (bind A ∷ Ξ)   (bw-b _ b)   = go Ξ b
  go (unlock X ∷ Ξ) (bw-u _ b)   = go Ξ b
  go (lock X ∷ Ξ)   (bw-l (E , d , v) b)
    with scp-∋e-ex Θ d
  ... | E′ , d′ with prep-∋e-tail (reps Θ) d′
  ...   | E″ , d″ = bw-u d″ (go Ξ b)

Bwf-dual : (Θ : CtxMorph) (Δ : Ctxᵗ) → Bwf Δ Θ
  → Bwf (intC Θ Δ) (dual Θ)
Bwf-dual Θ Δ bwΘ =
  Bwf-++ (Bwf-lockBinds (nbind Θ) (intC Θ Δ)
            (λ j lt → prep-∋tv (reps Θ) (scp Θ Δ) j lt))
         (Bwf-dualS-self Θ Δ bwΘ)

------------------------------------------------------------------------
-- The crossing argument retypes inside the dual
------------------------------------------------------------------------

crossing : (Θ : CtxMorph) {Δ : Ctxᵗ} {W : Term} {A : Ty}
  → Δ ∣ [] ⊢ W ⦂ A
  → intC (dual Θ) (intC Θ Δ) ∣ [] ⊢ wkᴹ (nbind Θ) W ⦂ liftN (nbind Θ) A
crossing Θ {Δ} {W} {A} ⊢W =
  subst (λ C → C ∣ [] ⊢ wkᴹ (nbind Θ) W ⦂ liftN (nbind Θ) A)
        (sym (intC-dual Θ Δ))
        step3
  where
  Ow : Ctxᵗ
  Ow = prep (reps Θ) []
  Ξ : Ctxᵗ
  Ξ = map blk Ow
  len-eq : length Ξ ≡ nbind Θ
  len-eq = trans (map-length blk Ow) (length-prep (reps Θ))
  step0 : (Ξ ++ Δ) ∣ [] ⊢ renᴹ (wkN (length Ξ)) W ⦂ renameᵗ (wkN (length Ξ)) A
  step0 = ⊢rename (Ren-wkN Ξ) (Inj-wkN (length Ξ)) ⊢W
  step1 : (Ξ ++ Δ) ∣ [] ⊢ renᴹ (wkN (length Ξ)) W ⦂ liftN (length Ξ) A
  step1 = subst (λ B → (Ξ ++ Δ) ∣ [] ⊢ renᴹ (wkN (length Ξ)) W ⦂ B)
                (renᵗ-wkN (length Ξ) A) step0
  step2 : (Ξ ++ Δ) ∣ [] ⊢ wkᴹ (nbind Θ) W ⦂ liftN (nbind Θ) A
  step2 rewrite sym len-eq = step1
  step3 : (Ξ ++ fscp Θ Δ) ∣ [] ⊢ wkᴹ (nbind Θ) W ⦂ liftN (nbind Θ) A
  step3 = ⊢retag (⊑-app Ξ (Δ⊑fscp Θ Δ)) step2

------------------------------------------------------------------------
-- PeelCase, PROVEN for dual
------------------------------------------------------------------------

nbind-dual : (Θ : CtxMorph) → nbind (dual Θ) ≡ 0
nbind-dual Θ = cong length (reps-dual Θ)

preserve-Peel : PeelCase
preserve-Peel {Δ} {V} {W} {Θ} {s} {t} {C} vV vW
         (⊢· (env {Bᵢ = Bᵢ} {Bₑ = Aarg⇒C} {p = p} bw ⊢V ⊢c wE) ⊢W)
  with wE
... | wf-⇒ wAarg wC
  with conv-tgt≡ (liftN-⇒ (nbind Θ) _ _) ⊢c
...  | conv-fun ⊢s ⊢t
  with ⊢ᵗ-of CtxWf-[] ⊢V
...   | wf-⇒ wAᵈ wBᶜ =
  env {p = p} bw (⊢· ⊢V ⊢argcross) ⊢t wC
  where
  ⊢s-tr : fceC (dual Θ) (intC Θ Δ) ⊢ s
            ∶ liftN (nbind Θ) _ ⇝ liftN (nbind (dual Θ)) _ ∙ flip p
  ⊢s-tr rewrite nbind-dual Θ =
    subst (λ Ct → Ct ⊢ s ∶ liftN (nbind Θ) _ ⇝ _ ∙ flip p)
          (sym (fceC-dual Θ Δ)) ⊢s
  ⊢argcross : intC Θ Δ ∣ [] ⊢ wkᴹ (nbind Θ) W ⟪ dual Θ , s ⟫ ⦂ _
  ⊢argcross = env {p = flip p} (Bwf-dual Θ Δ bw)
                  (crossing Θ ⊢W) ⊢s-tr wAᵈ
