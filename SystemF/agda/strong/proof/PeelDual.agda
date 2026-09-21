module strong.proof.PeelDual where

-- THE PEEL CROSSING — the dual is an INVERSE, and the frame identity is
-- EXACT.
--
--   interior (dual Θ) (interior Θ Δ)
--     ≡ map masked (pushBinds (binds Θ) []) ++ Δ         (given Δ ⊢ᵐ Θ)
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
--                              because `sw-u` refuses a vacuous unlock
--                              (`mask-unmask`, strong.Ctx §6b);
--   the list is REVERSED        because `applyChanges` applies HEAD-LAST.
--
-- WITH THE PAIR the dual is entirely a CHANGE-LIST construction: it binds
-- nothing, so `binds (dual Θ) ≡ []` and `numBinds (dual Θ) ≡ 0` hold by
-- REFLEXIVITY and the four `repsOf-…` filtering lemmas this module used
-- to need are gone.
--
--   §2  the dual's change list: the frame identity, its `⊢ˢ`, and the
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
open import strong.CtxMorph
open import strong.proof.Preserve using (PeelCase; ⊢ᵗ-of; CtxWf-[])
open import strong.proof.Canonical using (shiftBy-⇒; conv-tgt≡)

------------------------------------------------------------------------
-- Structural helpers
------------------------------------------------------------------------

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
-- §2  The dual's change list
------------------------------------------------------------------------

-- THE FRAME IDENTITY.  `dualScope` undoes `applyChanges` on the nose —
-- and this is where the two repairs are paid for: the `unlock` case needs
-- `mask ∘ unmask = id`, which holds AT A LOCKED SLOT AND NOWHERE ELSE
-- (`mask-unmask`), and the reversal is what puts each inverse entry where
-- `applyChanges` will apply it.
applyChanges-dualScope : (As : List Ty) (S : List Change) {Δ : Ctxᵗ} → Δ ⊢ˢ S
  → applyChanges (dualScope (length As) S) (pushBinds As (applyChanges S Δ))
      ≡ pushBinds As Δ
applyChanges-dualScope As []             sw[]         = refl
applyChanges-dualScope As (lock X ∷ S)   {Δ = Δ} (sw-l tv b)
  rewrite applyChanges-++ (dualScope (length As) S)
                          (unlock (length As + X) ∷ [])
                          (pushBinds As (mask X (applyChanges S Δ)))
        | updateAt-pushBinds unmaskEnt As X (mask X (applyChanges S Δ))
        | unmask-mask tv = applyChanges-dualScope As S b
applyChanges-dualScope As (unlock X ∷ S) {Δ = Δ} (sw-u lk b)
  rewrite applyChanges-++ (dualScope (length As) S)
                          (lock (length As + X) ∷ [])
                          (pushBinds As (unmask X (applyChanges S Δ)))
        | updateAt-pushBinds maskEnt As X (unmask X (applyChanges S Δ))
        | mask-unmask lk = applyChanges-dualScope As S b

-- … AND IT IS WELL FORMED WHERE IT LANDS.  S's `lock X` becomes an
-- `unlock` at a slot the lock itself just masked (`mask-∋lk`); S's
-- `unlock X` becomes a `lock` at a slot the unlock itself just exposed
-- (`unmask-∋tv`).  Both premises come straight out of S's own.
⊢ˢ-dualScope : (As : List Ty) (S : List Change) {Δ : Ctxᵗ} → Δ ⊢ˢ S
  → pushBinds As (applyChanges S Δ) ⊢ˢ dualScope (length As) S
⊢ˢ-dualScope As []             sw[]       = sw[]
⊢ˢ-dualScope As (lock X ∷ S)   {Δ = Δ} (sw-l tv b) =
  ⊢ˢ-++ (dualScope (length As) S) (unlock (length As + X) ∷ [])
        (subst (λ Ξ → Ξ ⊢ˢ dualScope (length As) S) (sym eq)
               (⊢ˢ-dualScope As S b))
        (sw-u (pushBinds-∋lk As (mask-∋lk tv)) sw[])
  where
  eq : unmask (length As + X) (pushBinds As (mask X (applyChanges S Δ)))
         ≡ pushBinds As (applyChanges S Δ)
  eq = trans (updateAt-pushBinds unmaskEnt As X (mask X (applyChanges S Δ)))
             (cong (pushBinds As) (unmask-mask tv))
⊢ˢ-dualScope As (unlock X ∷ S) {Δ = Δ} (sw-u lk b) =
  ⊢ˢ-++ (dualScope (length As) S) (lock (length As + X) ∷ [])
        (subst (λ Ξ → Ξ ⊢ˢ dualScope (length As) S) (sym eq)
               (⊢ˢ-dualScope As S b))
        (sw-l (pushBinds-∋tv As (unmask-∋tv lk)) sw[])
  where
  eq : mask (length As + X) (pushBinds As (unmask X (applyChanges S Δ)))
         ≡ pushBinds As (applyChanges S Δ)
  eq = trans (updateAt-pushBinds maskEnt As X (unmask X (applyChanges S Δ)))
             (cong (pushBinds As) (mask-unmask lk))

-- THE CONVERSION CONTEXT sees only the dual's UNLOCKS, i.e. only S's
-- LOCKS undone — so it is the original conversion context, with no
-- premise at all.  (A composition of unmasks commutes, which is why the
-- reversal is invisible here.)
dualScope-unmask-comm : (m : ℕ) (S : List Change) (Y : ℕ) (Ξ : Ctxᵗ)
  → applyUnlocks (dualScope m S) (unmask Y Ξ)
      ≡ unmask Y (applyUnlocks (dualScope m S) Ξ)
dualScope-unmask-comm m []             Y Ξ = refl
dualScope-unmask-comm m (unlock X ∷ S) Y Ξ
  rewrite applyUnlocks-++ (dualScope m S) (lock (m + X) ∷ []) (unmask Y Ξ)
        | applyUnlocks-++ (dualScope m S) (lock (m + X) ∷ []) Ξ =
  dualScope-unmask-comm m S Y Ξ
dualScope-unmask-comm m (lock X ∷ S)   Y Ξ
  rewrite applyUnlocks-++ (dualScope m S) (unlock (m + X) ∷ []) (unmask Y Ξ)
        | applyUnlocks-++ (dualScope m S) (unlock (m + X) ∷ []) Ξ
        | updateAt-updateAt-comm unmaskEnt (m + X) Y Ξ =
  dualScope-unmask-comm m S Y (unmask (m + X) Ξ)

-- THE ONE PLACE THE ONE-LOCK ENTRY COSTS A PREMISE.  `unmask ∘ mask` is
-- the identity only AT A NAMEABLE SLOT (`unmask-mask`, strong.Ctx §6b) —
-- with a stack of masks it held everywhere — so the `lock X` case needs
-- S's own `sw-l` premise, which is exactly where the nameability of X in
-- `applyChanges S Δ` is recorded.  Nothing else changes: the premise was
-- already threaded through `applyChanges-dualScope` next door.
applyUnlocks-dualScope : (As : List Ty) (S : List Change) (Δ : Ctxᵗ) → Δ ⊢ˢ S
  → applyUnlocks (dualScope (length As) S) (pushBinds As (applyChanges S Δ))
      ≡ pushBinds As (applyUnlocks S Δ)
applyUnlocks-dualScope As []             Δ sw[]        = refl
applyUnlocks-dualScope As (lock X ∷ S)   Δ (sw-l tv b)
  rewrite applyUnlocks-++ (dualScope (length As) S)
                          (unlock (length As + X) ∷ [])
                          (pushBinds As (mask X (applyChanges S Δ)))
        | updateAt-pushBinds unmaskEnt As X (mask X (applyChanges S Δ))
        | unmask-mask tv = applyUnlocks-dualScope As S Δ b
applyUnlocks-dualScope As (unlock X ∷ S) Δ (sw-u lk b)
  rewrite applyUnlocks-++ (dualScope (length As) S)
                          (lock (length As + X) ∷ [])
                          (pushBinds As (unmask X (applyChanges S Δ)))
        | sym (updateAt-pushBinds unmaskEnt As X (applyChanges S Δ))
        | dualScope-unmask-comm (length As) S (length As + X)
                                (pushBinds As (applyChanges S Δ))
        | applyUnlocks-dualScope As S Δ b =
  updateAt-pushBinds unmaskEnt As X (applyUnlocks S Δ)

------------------------------------------------------------------------
-- §3  (†) and `convCtx-dual`
------------------------------------------------------------------------

-- `hideBinds` masks the whole bind prefix.
hideBinds-cons : (k : ℕ) (E : Ent) (Ξ : Ctxᵗ)
  → applyChanges (hideBinds (suc k)) (E ∷ Ξ)
      ≡ maskEnt E ∷ applyChanges (hideBinds k) Ξ
hideBinds-cons zero    E Ξ = refl
hideBinds-cons (suc k) E Ξ
  rewrite hideBinds-cons k E Ξ = refl

stepB : (Ow Δ : Ctxᵗ)
  → applyChanges (hideBinds (length Ow)) (Ow ++ Δ) ≡ map maskEnt Ow ++ Δ
stepB []       Δ = refl
stepB (E ∷ Ow) Δ
  rewrite hideBinds-cons (length Ow) E (Ow ++ Δ)
        | stepB Ow Δ = refl

-- THE DUAL CARRIES NO BINDS, and with the pair that is a fact about the
-- constructor: it holds BY REFLEXIVITY.  The interleaved list needed four
-- filtering lemmas to say it (`repsOf-hideBinds`, `repsOf-++`,
-- `repsOf-dualScope`, `repsOf-dual`) and they are all gone.
numBinds-dual : (Θ : CtxMorph) → numBinds (dual Θ) ≡ 0
numBinds-dual Θ = refl

-- (†) THE CROSSING FRAME IS THE EXTERIOR, ONE BIND PREFIX IN.
interior-dual : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ᵐ Θ
  → interior (dual Θ) (interior Θ Δ)
      ≡ map maskEnt (pushBinds (binds Θ) []) ++ Δ
interior-dual Θ Δ mwΘ = go
  where
  Ow : Ctxᵗ
  Ow = pushBinds (binds Θ) []
  lenOw : length Ow ≡ numBinds Θ
  lenOw = length-pushBinds (binds Θ)
  go : applyChanges (changes (dual Θ)) (pushBinds (binds Θ) (scope Θ Δ))
         ≡ map maskEnt Ow ++ Δ
  go rewrite applyChanges-++ (hideBinds (numBinds Θ))
                             (dualScope (numBinds Θ) (changes Θ))
                             (pushBinds (binds Θ) (scope Θ Δ))
           | applyChanges-dualScope (binds Θ) (changes Θ) (mw-changes mwΘ)
           | pushBinds-++ (binds Θ) Δ
           | sym lenOw = stepB Ow Δ

-- `applyUnlocks` skips locks, so `hideBinds` is invisible to the
-- conversion context.
applyUnlocks-hideBinds : (k : ℕ) (Ξ : Ctxᵗ) → applyUnlocks (hideBinds k) Ξ ≡ Ξ
applyUnlocks-hideBinds zero    Ξ = refl
applyUnlocks-hideBinds (suc k) Ξ = applyUnlocks-hideBinds k Ξ

convCtx-dual : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ˢ changes Θ
  → convCtx (dual Θ) (interior Θ Δ) ≡ convCtx Θ Δ
convCtx-dual Θ Δ b
  rewrite applyUnlocks-++ (hideBinds (numBinds Θ))
                          (dualScope (numBinds Θ) (changes Θ))
                          (pushBinds (binds Θ) (scope Θ Δ))
        | applyUnlocks-hideBinds (numBinds Θ)
            (applyUnlocks (dualScope (numBinds Θ) (changes Θ))
                          (pushBinds (binds Θ) (scope Θ Δ))) =
  applyUnlocks-dualScope (binds Θ) (changes Θ) Δ b

------------------------------------------------------------------------
-- §4  The crossing, and `preserve-Peel`
------------------------------------------------------------------------

-- binder slots of a pushBinds are visible
pushBinds-∋tv-lt : (As : List Ty) (Ξ : Ctxᵗ) (j : ℕ)
  → j < length As → pushBinds As Ξ ∋tv j
pushBinds-∋tv-lt (A ∷ As) Ξ zero    (s≤s _)  = unmasked (bind _) , ez , nameable
pushBinds-∋tv-lt (A ∷ As) Ξ (suc j) (s≤s lt) with pushBinds-∋tv-lt As Ξ j lt
... | E , d , v = _ , es d , renᵉ-Nameable v

-- `hideBinds k` masks slots 0 … k-1, so it misses every slot ≥ k.
hideBinds-∋tv : (k : ℕ) {Ξ : Ctxᵗ} {Y : ℕ} → k ≤ Y → Ξ ∋tv Y
  → applyChanges (hideBinds k) Ξ ∋tv Y
hideBinds-∋tv zero    le tv = tv
hideBinds-∋tv (suc k) le tv with hideBinds-∋tv k (≤-trans (n≤1+n k) le) tv
... | E , d , v = E , updateAt-miss maskEnt maskEnt-comm (<⇒≢ le) d , v

⊢ˢ-hideBinds : (k : ℕ) (Ξ : Ctxᵗ)
  → ((j : ℕ) → j < k → Ξ ∋tv j) → Ξ ⊢ˢ hideBinds k
⊢ˢ-hideBinds zero    Ξ h = sw[]
⊢ˢ-hideBinds (suc k) Ξ h =
  sw-l (hideBinds-∋tv k ≤-refl (h k ≤-refl))
       (⊢ˢ-hideBinds k Ξ (λ j lt → h j (m≤n⇒m≤1+n lt)))

-- THE DUAL'S OWN `⊢ᵐ`.  Its REP half is EMPTY (`rw[]`) — the dual binds
-- nothing — so the whole content is the change half.
⊢ᵐ-dual : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ᵐ Θ → interior Θ Δ ⊢ᵐ dual Θ
⊢ᵐ-dual Θ Δ mwΘ =
  mw rw[]
     (⊢ˢ-++ (hideBinds (numBinds Θ)) (dualScope (numBinds Θ) (changes Θ))
        (subst (λ Ξ → Ξ ⊢ˢ hideBinds (numBinds Θ))
               (sym (applyChanges-dualScope (binds Θ) (changes Θ)
                       (mw-changes mwΘ)))
               (⊢ˢ-hideBinds (numBinds Θ) (pushBinds (binds Θ) Δ)
                  (λ j lt → pushBinds-∋tv-lt (binds Θ) Δ j lt)))
        (⊢ˢ-dualScope (binds Θ) (changes Θ) (mw-changes mwΘ)))

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

-- Both facts are BINDING facts, lifted through the lock layer: the two
-- `Ent` clauses just re-apply the constructor they matched.
renᵇ-id : (b : Binding) → renᵇ (λ X → X) b ≡ b
renᵇ-id abst     = refl
renᵇ-id (bind A) = cong bind (renameᵗ-id A)

renᵉ-id : (E : Ent) → renᵉ (λ X → X) E ≡ E
renᵉ-id (unmasked b) = cong unmasked (renᵇ-id b)
renᵉ-id (masked b)   = cong masked (renᵇ-id b)

renᵇ-comp : (ρ₁ ρ₂ : Renameᵗ) (b : Binding)
  → renᵇ ρ₂ (renᵇ ρ₁ b) ≡ renᵇ (λ X → ρ₂ (ρ₁ X)) b
renᵇ-comp ρ₁ ρ₂ abst     = refl
renᵇ-comp ρ₁ ρ₂ (bind A) = cong bind (rename-rename-commute ρ₁ ρ₂ A)

renᵉ-comp : (ρ₁ ρ₂ : Renameᵗ) (E : Ent)
  → renᵉ ρ₂ (renᵉ ρ₁ E) ≡ renᵉ (λ X → ρ₂ (ρ₁ X)) E
renᵉ-comp ρ₁ ρ₂ (unmasked b) = cong unmasked (renᵇ-comp ρ₁ ρ₂ b)
renᵉ-comp ρ₁ ρ₂ (masked b)   = cong masked (renᵇ-comp ρ₁ ρ₂ b)

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
  Ow = pushBinds (binds Θ) []
  Ξ : Ctxᵗ
  Ξ = map maskEnt Ow
  len-eq : length Ξ ≡ numBinds Θ
  len-eq = trans (map-length maskEnt Ow) (length-pushBinds (binds Θ))
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
         (⊢· (env {Bᵢ = Bᵢ} {Bₑ = Aarg⇒C} mwᵥ ⊢V ⊢c wE) ⊢W)
  with wE
... | wf-⇒ wAarg wC
  with conv-tgt≡ (shiftBy-⇒ (numBinds Θ) _ _) ⊢c
...  | conv-fun ⊢s ⊢t
  with ⊢ᵗ-of CtxWf-[] ⊢V
...   | wf-⇒ wAᵈ wBᶜ =
  env mwᵥ (⊢· ⊢V ⊢argcross) ⊢t wC
  where
  -- `numBinds (dual Θ)` REDUCES to 0, so no rewrite is needed here any
  -- more (the interleaved list had to `rewrite numBinds-dual Θ`).
  ⊢s-tr : convCtx (dual Θ) (interior Θ Δ) ⊢ s
            ∶ shiftBy (numBinds Θ) _ ⇝ shiftBy (numBinds (dual Θ)) _
  ⊢s-tr = subst (λ Ct → Ct ⊢ s ∶ shiftBy (numBinds Θ) _ ⇝ _)
                (sym (convCtx-dual Θ Δ (mw-changes mwᵥ))) ⊢s
  ⊢argcross : interior Θ Δ ∣ [] ⊢ wkᴹ (numBinds Θ) W ⟪ dual Θ , s ⟫ ⦂ _
  ⊢argcross = env (⊢ᵐ-dual Θ Δ mwᵥ)
                  (crossing Θ mwᵥ ⊢W) ⊢s-tr wAᵈ
