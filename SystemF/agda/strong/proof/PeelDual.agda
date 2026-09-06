module strong.proof.PeelDual where

-- THE PEEL CROSSING — the dual is an INVERSE, and the frame identity is
-- EXACT.
--
--   interior (dual Θ) (interior Θ Δ)
--     ≡ map masked (pushBinds (repsOf Θ) []) ++ Δ        (given Δ ⊢ᵐ Θ)
--   convCtx (dual Θ) (interior Θ Δ) ≡ convCtx Θ Δ
--
-- The first is (†): the crossing argument's frame IS THE EXTERIOR, one
-- bind prefix in, with the prefix masked.  So the argument (typed at Δ)
-- crosses by `⊢rename (wkN (numBinds Θ))` ALONE — no `⊢retag`, no
-- `le-mu`, and no scope is gained.  Under the old dual the right-hand
-- side was `… ++ unlockedScope Θ Δ`, strictly more nameable than Δ
-- whenever Θ unlocked a slot Δ masked, and `Peel` related a term the
-- exterior REFUSES to one it accepts (proof/DualTightness).
--
-- The two repairs (strong.CtxMorph §3) that buy it:
--   `unlock X ↦ lock (n + X)`  the dual RESTORES what Θ unlocked, sound
--                              because `mw-u` refuses a vacuous unlock
--                              (`mask-unmask`, strong.Ctx §6b);
--   the list is REVERSED        because `scope` applies HEAD-LAST.
--
--   §1  `⊢ᵐ-++` — the SEQUENTIAL judgement of an append (also used by
--       proof/MoveScope)
--   §2  the dual's scope: the frame identity, its `⊢ᵐ`, and the
--       conversion-context identity
--   §3  (†) and `convCtx-dual`
--   §4  the crossing, and `preserve-Peel`

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m≤n⇒m≤1+n; <⇒≢)
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
open import strong.CtxMorph using (hideBinds; dualScope; dual)
open import strong.proof.Preserve using (PeelCase; ⊢ᵗ-of; CtxWf-[])
open import strong.proof.Canonical using (shiftBy-⇒; conv-tgt≡)

------------------------------------------------------------------------
-- Structural helpers
------------------------------------------------------------------------

scope-++ : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → scope (Θ₁ ++ Θ₂) Δ ≡ scope Θ₁ (scope Θ₂ Δ)
scope-++ []              Θ₂ Δ = refl
scope-++ (bind A ∷ Θ₁)   Θ₂ Δ = scope-++ Θ₁ Θ₂ Δ
scope-++ (unlock X ∷ Θ₁) Θ₂ Δ = cong (unmask X) (scope-++ Θ₁ Θ₂ Δ)
scope-++ (lock X ∷ Θ₁)   Θ₂ Δ = cong (mask X) (scope-++ Θ₁ Θ₂ Δ)

unlockedScope-++ : (Θ₁ Θ₂ : CtxMorph) (Δ : Ctxᵗ)
  → unlockedScope (Θ₁ ++ Θ₂) Δ ≡ unlockedScope Θ₁ (unlockedScope Θ₂ Δ)
unlockedScope-++ []              Θ₂ Δ = refl
unlockedScope-++ (bind A ∷ Θ₁)   Θ₂ Δ = unlockedScope-++ Θ₁ Θ₂ Δ
unlockedScope-++ (unlock X ∷ Θ₁) Θ₂ Δ =
  cong (unmask X) (unlockedScope-++ Θ₁ Θ₂ Δ)
unlockedScope-++ (lock X ∷ Θ₁)   Θ₂ Δ = unlockedScope-++ Θ₁ Θ₂ Δ

pushBinds-++ : (As : List Ty) (Δ : Ctxᵗ) → pushBinds As Δ ≡ pushBinds As [] ++ Δ
pushBinds-++ []       Δ = refl
pushBinds-++ (A ∷ As) Δ rewrite pushBinds-++ As Δ | pushBinds-++ As [] = refl

length-pushBinds : (As : List Ty) → length (pushBinds As []) ≡ length As
length-pushBinds []       = refl
length-pushBinds (A ∷ As) = cong suc (length-pushBinds As)

-- Two in-place updates commute.
updateAt-updateAt-comm : (f : Ent → Ent) (a b : ℕ) (Δ : Ctxᵗ)
  → updateAt f a (updateAt f b Δ) ≡ updateAt f b (updateAt f a Δ)
updateAt-updateAt-comm f a       b       []      = refl
updateAt-updateAt-comm f zero    zero    (E ∷ Δ) = refl
updateAt-updateAt-comm f zero    (suc b) (E ∷ Δ) = refl
updateAt-updateAt-comm f (suc a) zero    (E ∷ Δ) = refl
updateAt-updateAt-comm f (suc a) (suc b) (E ∷ Δ) =
  cong (E ∷_) (updateAt-updateAt-comm f a b Δ)

-- mask/unmask at a position ≥ |Ow| only touches the tail.
updateAt-app-tail : (f : Ent → Ent) (Ow : Ctxᵗ) (X : ℕ) (Δ : Ctxᵗ)
  → updateAt f (length Ow + X) (Ow ++ Δ) ≡ Ow ++ updateAt f X Δ
updateAt-app-tail f []       X Δ = refl
updateAt-app-tail f (E ∷ Ow) X Δ = cong (E ∷_) (updateAt-app-tail f Ow X Δ)

------------------------------------------------------------------------
-- §1  `⊢ᵐ-++` — the sequential judgement of an APPEND
------------------------------------------------------------------------

-- `scope` applies its list HEAD-LAST, so in `Θ ++ Ψ` it is Ψ that runs
-- FIRST: Θ is judged over `scope Ψ Δ`, Ψ over Δ.  Each of the three
-- premises then lands on the nose except the rep, which moves from
-- `scope Ψ Δ` to `unlockedScope Ψ Δ` — MORE nameable
-- (`scope⊑unlockedScope`), so `⊑-wf` carries it.
⊢ᵐ-++ : (Θ Ψ : CtxMorph) {Δ : Ctxᵗ}
  → scope Ψ Δ ⊢ᵐ Θ → Δ ⊢ᵐ Ψ → Δ ⊢ᵐ (Θ ++ Ψ)
⊢ᵐ-++ []             Ψ mw[]        bΨ = bΨ
⊢ᵐ-++ (bind A ∷ Θ)   Ψ {Δ = Δ} (mw-b w b)  bΨ =
  mw-b (subst (λ Ξ → Ξ ⊢ᵗ A) (sym (unlockedScope-++ Θ Ψ Δ))
              (⊑-wf (⊑-unlockedScope Θ (scope⊑unlockedScope Ψ Δ)) w))
       (⊢ᵐ-++ Θ Ψ b bΨ)
⊢ᵐ-++ (lock X ∷ Θ)   Ψ {Δ = Δ} (mw-l tv b) bΨ =
  mw-l (subst (λ Ξ → Ξ ∋tv X) (sym (scope-++ Θ Ψ Δ)) tv) (⊢ᵐ-++ Θ Ψ b bΨ)
⊢ᵐ-++ (unlock X ∷ Θ) Ψ {Δ = Δ} (mw-u lk b) bΨ =
  mw-u (subst (λ Ξ → Ξ ∋lk X) (sym (scope-++ Θ Ψ Δ)) lk) (⊢ᵐ-++ Θ Ψ b bΨ)

------------------------------------------------------------------------
-- §2  The dual's scope half
------------------------------------------------------------------------

-- THE FRAME IDENTITY.  `dualScope` undoes `scope` on the nose — and this
-- is where the two repairs are paid for: the `unlock` case needs
-- `mask ∘ unmask = id`, which holds AT A LOCKED SLOT AND NOWHERE ELSE
-- (`mask-unmask`), and the reversal is what puts each inverse entry where
-- `scope` will apply it.
scope-dualScope : (As : List Ty) (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ
  → scope (dualScope (length As) Θ) (pushBinds As (scope Θ Δ)) ≡ pushBinds As Δ
scope-dualScope As []             mw[]         = refl
scope-dualScope As (bind A ∷ Θ)   (mw-b _ b)   = scope-dualScope As Θ b
scope-dualScope As (lock X ∷ Θ)   {Δ = Δ} (mw-l tv b)
  rewrite scope-++ (dualScope (length As) Θ) (unlock (length As + X) ∷ [])
                   (pushBinds As (mask X (scope Θ Δ)))
        | updateAt-pushBinds unmaskEnt As X (mask X (scope Θ Δ))
        | unmask-mask X (scope Θ Δ) = scope-dualScope As Θ b
scope-dualScope As (unlock X ∷ Θ) {Δ = Δ} (mw-u lk b)
  rewrite scope-++ (dualScope (length As) Θ) (lock (length As + X) ∷ [])
                   (pushBinds As (unmask X (scope Θ Δ)))
        | updateAt-pushBinds masked As X (unmask X (scope Θ Δ))
        | mask-unmask lk = scope-dualScope As Θ b

-- … AND IT IS WELL FORMED WHERE IT LANDS.  Θ's `lock X` becomes an
-- `unlock` at a slot the lock itself just masked (`mask-∋lk`); Θ's
-- `unlock X` becomes a `lock` at a slot the unlock itself just exposed
-- (`unmask-∋tv`).  Both premises come straight out of Θ's own.
⊢ᵐ-dualScope : (As : List Ty) (Θ : CtxMorph) {Δ : Ctxᵗ} → Δ ⊢ᵐ Θ
  → pushBinds As (scope Θ Δ) ⊢ᵐ dualScope (length As) Θ
⊢ᵐ-dualScope As []             mw[]       = mw[]
⊢ᵐ-dualScope As (bind A ∷ Θ)   (mw-b _ b) = ⊢ᵐ-dualScope As Θ b
⊢ᵐ-dualScope As (lock X ∷ Θ)   {Δ = Δ} (mw-l tv b) =
  ⊢ᵐ-++ (dualScope (length As) Θ) (unlock (length As + X) ∷ [])
        (subst (λ Ξ → Ξ ⊢ᵐ dualScope (length As) Θ) (sym eq)
               (⊢ᵐ-dualScope As Θ b))
        (mw-u (pushBinds-∋lk As (mask-∋lk tv)) mw[])
  where
  eq : unmask (length As + X) (pushBinds As (mask X (scope Θ Δ)))
         ≡ pushBinds As (scope Θ Δ)
  eq = trans (updateAt-pushBinds unmaskEnt As X (mask X (scope Θ Δ)))
             (cong (pushBinds As) (unmask-mask X (scope Θ Δ)))
⊢ᵐ-dualScope As (unlock X ∷ Θ) {Δ = Δ} (mw-u lk b) =
  ⊢ᵐ-++ (dualScope (length As) Θ) (lock (length As + X) ∷ [])
        (subst (λ Ξ → Ξ ⊢ᵐ dualScope (length As) Θ) (sym eq)
               (⊢ᵐ-dualScope As Θ b))
        (mw-l (pushBinds-∋tv As (unmask-∋tv lk)) mw[])
  where
  eq : mask (length As + X) (pushBinds As (unmask X (scope Θ Δ)))
         ≡ pushBinds As (scope Θ Δ)
  eq = trans (updateAt-pushBinds masked As X (unmask X (scope Θ Δ)))
             (cong (pushBinds As) (mask-unmask lk))

-- THE CONVERSION CONTEXT sees only the dual's UNLOCKS, i.e. only Θ's
-- LOCKS undone — so it is Θ's own conversion context, with no premise at
-- all.  (A composition of unmasks commutes, which is why the reversal is
-- invisible here.)
dualScope-unmask-comm : (m : ℕ) (Ψ : CtxMorph) (Y : ℕ) (Ξ : Ctxᵗ)
  → unlockedScope (dualScope m Ψ) (unmask Y Ξ)
      ≡ unmask Y (unlockedScope (dualScope m Ψ) Ξ)
dualScope-unmask-comm m []             Y Ξ = refl
dualScope-unmask-comm m (bind A ∷ Ψ)   Y Ξ = dualScope-unmask-comm m Ψ Y Ξ
dualScope-unmask-comm m (unlock X ∷ Ψ) Y Ξ
  rewrite unlockedScope-++ (dualScope m Ψ) (lock (m + X) ∷ []) (unmask Y Ξ)
        | unlockedScope-++ (dualScope m Ψ) (lock (m + X) ∷ []) Ξ =
  dualScope-unmask-comm m Ψ Y Ξ
dualScope-unmask-comm m (lock X ∷ Ψ)   Y Ξ
  rewrite unlockedScope-++ (dualScope m Ψ) (unlock (m + X) ∷ []) (unmask Y Ξ)
        | unlockedScope-++ (dualScope m Ψ) (unlock (m + X) ∷ []) Ξ
        | updateAt-updateAt-comm unmaskEnt (m + X) Y Ξ =
  dualScope-unmask-comm m Ψ Y (unmask (m + X) Ξ)

unlockedScope-dualScope : (As : List Ty) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → unlockedScope (dualScope (length As) Θ) (pushBinds As (scope Θ Δ))
      ≡ pushBinds As (unlockedScope Θ Δ)
unlockedScope-dualScope As []             Δ = refl
unlockedScope-dualScope As (bind A ∷ Θ)   Δ = unlockedScope-dualScope As Θ Δ
unlockedScope-dualScope As (lock X ∷ Θ)   Δ
  rewrite unlockedScope-++ (dualScope (length As) Θ)
                           (unlock (length As + X) ∷ [])
                           (pushBinds As (mask X (scope Θ Δ)))
        | updateAt-pushBinds unmaskEnt As X (mask X (scope Θ Δ))
        | unmask-mask X (scope Θ Δ) = unlockedScope-dualScope As Θ Δ
unlockedScope-dualScope As (unlock X ∷ Θ) Δ
  rewrite unlockedScope-++ (dualScope (length As) Θ)
                           (lock (length As + X) ∷ [])
                           (pushBinds As (unmask X (scope Θ Δ)))
        | sym (updateAt-pushBinds unmaskEnt As X (scope Θ Δ))
        | dualScope-unmask-comm (length As) Θ (length As + X)
                                (pushBinds As (scope Θ Δ))
        | unlockedScope-dualScope As Θ Δ =
  updateAt-pushBinds unmaskEnt As X (unlockedScope Θ Δ)

------------------------------------------------------------------------
-- §3  (†) and `convCtx-dual`
------------------------------------------------------------------------

-- `hideBinds` masks the whole bind prefix.
hideBinds-cons : (k : ℕ) (E : Ent) (Ξ : Ctxᵗ)
  → scope (hideBinds (suc k)) (E ∷ Ξ) ≡ masked E ∷ scope (hideBinds k) Ξ
hideBinds-cons zero    E Ξ = refl
hideBinds-cons (suc k) E Ξ
  rewrite hideBinds-cons k E Ξ = refl

stepB : (Ow Δ : Ctxᵗ)
  → scope (hideBinds (length Ow)) (Ow ++ Δ) ≡ map masked Ow ++ Δ
stepB []       Δ = refl
stepB (E ∷ Ow) Δ
  rewrite hideBinds-cons (length Ow) E (Ow ++ Δ)
        | stepB Ow Δ = refl

-- dual produces no binders, so its `pushBinds` is the identity.
repsOf-hideBinds : (k : ℕ) → repsOf (hideBinds k) ≡ []
repsOf-hideBinds zero    = refl
repsOf-hideBinds (suc k) = repsOf-hideBinds k

repsOf-++ : (Θ₁ Θ₂ : CtxMorph) → repsOf (Θ₁ ++ Θ₂) ≡ repsOf Θ₁ ++ repsOf Θ₂
repsOf-++ []              Θ₂ = refl
repsOf-++ (bind A ∷ Θ₁)   Θ₂ = cong (_ ∷_) (repsOf-++ Θ₁ Θ₂)
repsOf-++ (unlock X ∷ Θ₁) Θ₂ = repsOf-++ Θ₁ Θ₂
repsOf-++ (lock X ∷ Θ₁)   Θ₂ = repsOf-++ Θ₁ Θ₂

repsOf-dualScope : (n : ℕ) (Θ : CtxMorph) → repsOf (dualScope n Θ) ≡ []
repsOf-dualScope n []             = refl
repsOf-dualScope n (bind A ∷ Θ)   = repsOf-dualScope n Θ
repsOf-dualScope n (unlock X ∷ Θ)
  rewrite repsOf-++ (dualScope n Θ) (lock (n + X) ∷ [])
        | repsOf-dualScope n Θ = refl
repsOf-dualScope n (lock X ∷ Θ)
  rewrite repsOf-++ (dualScope n Θ) (unlock (n + X) ∷ [])
        | repsOf-dualScope n Θ = refl

repsOf-dual : (Θ : CtxMorph) → repsOf (dual Θ) ≡ []
repsOf-dual Θ rewrite repsOf-++ (hideBinds (numBinds Θ))
                                (dualScope (numBinds Θ) Θ)
                   | repsOf-hideBinds (numBinds Θ)
                   | repsOf-dualScope (numBinds Θ) Θ = refl

numBinds-dual : (Θ : CtxMorph) → numBinds (dual Θ) ≡ 0
numBinds-dual Θ = cong length (repsOf-dual Θ)

-- (†) THE CROSSING FRAME IS THE EXTERIOR, ONE BIND PREFIX IN.
interior-dual : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ᵐ Θ
  → interior (dual Θ) (interior Θ Δ)
      ≡ map masked (pushBinds (repsOf Θ) []) ++ Δ
interior-dual Θ Δ mwΘ
  rewrite repsOf-dual Θ
  = go
  where
  Ow : Ctxᵗ
  Ow = pushBinds (repsOf Θ) []
  lenOw : length Ow ≡ numBinds Θ
  lenOw = length-pushBinds (repsOf Θ)
  go : scope (dual Θ) (pushBinds (repsOf Θ) (scope Θ Δ)) ≡ map masked Ow ++ Δ
  go rewrite scope-++ (hideBinds (numBinds Θ)) (dualScope (numBinds Θ) Θ)
                      (pushBinds (repsOf Θ) (scope Θ Δ))
           | scope-dualScope (repsOf Θ) Θ mwΘ
           | pushBinds-++ (repsOf Θ) Δ
           | sym lenOw = stepB Ow Δ

-- unlockedScope skips locks, so hideBinds is invisible to the
-- conversion context.
unlockedScope-hideBinds : (k : ℕ) (Ξ : Ctxᵗ) → unlockedScope (hideBinds k) Ξ ≡ Ξ
unlockedScope-hideBinds zero    Ξ = refl
unlockedScope-hideBinds (suc k) Ξ = unlockedScope-hideBinds k Ξ

convCtx-dual : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → convCtx (dual Θ) (interior Θ Δ) ≡ convCtx Θ Δ
convCtx-dual Θ Δ
  rewrite repsOf-dual Θ
        | unlockedScope-++ (hideBinds (numBinds Θ)) (dualScope (numBinds Θ) Θ)
                           (pushBinds (repsOf Θ) (scope Θ Δ))
        | unlockedScope-hideBinds (numBinds Θ)
            (unlockedScope (dualScope (numBinds Θ) Θ)
                           (pushBinds (repsOf Θ) (scope Θ Δ))) =
  unlockedScope-dualScope (repsOf Θ) Θ Δ

------------------------------------------------------------------------
-- §4  The crossing, and `preserve-Peel`
------------------------------------------------------------------------

-- binder slots of a pushBinds are visible
pushBinds-∋tv-lt : (As : List Ty) (Ξ : Ctxᵗ) (j : ℕ)
  → j < length As → pushBinds As Ξ ∋tv j
pushBinds-∋tv-lt (A ∷ As) Ξ zero    (s≤s _)  = bind _ , ez , nameable-b
pushBinds-∋tv-lt (A ∷ As) Ξ (suc j) (s≤s lt) with pushBinds-∋tv-lt As Ξ j lt
... | E , d , v = _ , es d , renᵉ-Nameable v

-- `hideBinds k` masks slots 0 … k-1, so it misses every slot ≥ k.
hideBinds-∋tv : (k : ℕ) {Ξ : Ctxᵗ} {Y : ℕ} → k ≤ Y → Ξ ∋tv Y
  → scope (hideBinds k) Ξ ∋tv Y
hideBinds-∋tv zero    le tv = tv
hideBinds-∋tv (suc k) le tv with hideBinds-∋tv k (≤-trans (n≤1+n k) le) tv
... | E , d , v = E , updateAt-miss masked masked-comm (<⇒≢ le) d , v

⊢ᵐ-hideBinds : (k : ℕ) (Ξ : Ctxᵗ)
  → ((j : ℕ) → j < k → Ξ ∋tv j) → Ξ ⊢ᵐ hideBinds k
⊢ᵐ-hideBinds zero    Ξ h = mw[]
⊢ᵐ-hideBinds (suc k) Ξ h =
  mw-l (hideBinds-∋tv k ≤-refl (h k ≤-refl))
       (⊢ᵐ-hideBinds k Ξ (λ j lt → h j (m≤n⇒m≤1+n lt)))

⊢ᵐ-dual : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ᵐ Θ → interior Θ Δ ⊢ᵐ dual Θ
⊢ᵐ-dual Θ Δ mwΘ =
  ⊢ᵐ-++ (hideBinds (numBinds Θ)) (dualScope (numBinds Θ) Θ)
        (subst (λ Ξ → Ξ ⊢ᵐ hideBinds (numBinds Θ))
               (sym (scope-dualScope (repsOf Θ) Θ mwΘ))
               (⊢ᵐ-hideBinds (numBinds Θ) (pushBinds (repsOf Θ) Δ)
                  (λ j lt → pushBinds-∋tv-lt (repsOf Θ) Δ j lt)))
        (⊢ᵐ-dualScope (repsOf Θ) Θ mwΘ)

------------------------------------------------------------------------
-- Renaming identity/composition and wkN = shiftBy
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
renᵉ-id abst        = refl
renᵉ-id (bind A)    = cong bind (renameᵗ-id A)
renᵉ-id (masked E)  = cong masked (renᵉ-id E)

renᵉ-comp : (ρ₁ ρ₂ : Renameᵗ) (E : Ent)
  → renᵉ ρ₂ (renᵉ ρ₁ E) ≡ renᵉ (λ X → ρ₂ (ρ₁ X)) E
renᵉ-comp ρ₁ ρ₂ abst        = refl
renᵉ-comp ρ₁ ρ₂ (bind A)    = cong bind (rename-rename-commute ρ₁ ρ₂ A)
renᵉ-comp ρ₁ ρ₂ (masked E)  = cong masked (renᵉ-comp ρ₁ ρ₂ E)

renᵗ-wkN : (n : ℕ) (A : Ty) → renameᵗ (wkN n) A ≡ shiftBy n A
renᵗ-wkN zero    A = renameᵗ-id A
renᵗ-wkN (suc m) A =
  trans (sym (rename-rename-commute (wkN m) suc A))
        (cong ⇑ᵗ (renᵗ-wkN m A))

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
-- The crossing argument retypes inside the dual — BY RENAMING ALONE
------------------------------------------------------------------------

-- THIS IS TIGHTNESS.  The argument was typed at Δ and is typed inside at
-- Δ, shifted past the crossed boundary's (masked) binders.  Nothing is
-- relaxed; no slot the exterior refuses becomes nameable.
crossing : (Θ : CtxMorph) {Δ : Ctxᵗ} {W : Term} {A : Ty} → Δ ⊢ᵐ Θ
  → Δ ∣ [] ⊢ W ⦂ A
  → interior (dual Θ) (interior Θ Δ) ∣ []
      ⊢ wkᴹ (numBinds Θ) W ⦂ shiftBy (numBinds Θ) A
crossing Θ {Δ} {W} {A} mwΘ ⊢W =
  subst (λ C → C ∣ [] ⊢ wkᴹ (numBinds Θ) W ⦂ shiftBy (numBinds Θ) A)
        (sym (interior-dual Θ Δ mwΘ))
        step2
  where
  Ow : Ctxᵗ
  Ow = pushBinds (repsOf Θ) []
  Ξ : Ctxᵗ
  Ξ = map masked Ow
  len-eq : length Ξ ≡ numBinds Θ
  len-eq = trans (map-length masked Ow) (length-pushBinds (repsOf Θ))
  step0 : (Ξ ++ Δ) ∣ [] ⊢ renᴹ (wkN (length Ξ)) W ⦂ renameᵗ (wkN (length Ξ)) A
  step0 = ⊢rename (Ren-wkN Ξ) (Inj-wkN (length Ξ)) ⊢W
  step1 : (Ξ ++ Δ) ∣ [] ⊢ renᴹ (wkN (length Ξ)) W ⦂ shiftBy (length Ξ) A
  step1 = subst (λ B → (Ξ ++ Δ) ∣ [] ⊢ renᴹ (wkN (length Ξ)) W ⦂ B)
                (renᵗ-wkN (length Ξ) A) step0
  step2 : (Ξ ++ Δ) ∣ [] ⊢ wkᴹ (numBinds Θ) W ⦂ shiftBy (numBinds Θ) A
  step2 rewrite sym len-eq = step1

------------------------------------------------------------------------
-- PeelCase, PROVEN for dual
------------------------------------------------------------------------

preserve-Peel : PeelCase
preserve-Peel {Δ} {V} {W} {Θ} {s} {t} {C} vV vW
         (⊢· (env {Bᵢ = Bᵢ} {Bₑ = Aarg⇒C} mw ⊢V ⊢c wE) ⊢W)
  with wE
... | wf-⇒ wAarg wC
  with conv-tgt≡ (shiftBy-⇒ (numBinds Θ) _ _) ⊢c
...  | conv-fun ⊢s ⊢t
  with ⊢ᵗ-of CtxWf-[] ⊢V
...   | wf-⇒ wAᵈ wBᶜ =
  env mw (⊢· ⊢V ⊢argcross) ⊢t wC
  where
  ⊢s-tr : convCtx (dual Θ) (interior Θ Δ) ⊢ s
            ∶ shiftBy (numBinds Θ) _ ⇝ shiftBy (numBinds (dual Θ)) _
  ⊢s-tr rewrite numBinds-dual Θ =
    subst (λ Ct → Ct ⊢ s ∶ shiftBy (numBinds Θ) _ ⇝ _)
          (sym (convCtx-dual Θ Δ)) ⊢s
  ⊢argcross : interior Θ Δ ∣ [] ⊢ wkᴹ (numBinds Θ) W ⟪ dual Θ , s ⟫ ⦂ _
  ⊢argcross = env (⊢ᵐ-dual Θ Δ mw)
                  (crossing Θ mw ⊢W) ⊢s-tr wAᵈ
