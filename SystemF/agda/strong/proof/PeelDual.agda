module strong.proof.PeelDual where

-- THE PEEL REPAIR — with the fixed `dual` (strong.Reduction), `interior-dual`
-- and `convCtx-dual` are TRUE in general and `PeelCase` is PROVEN.
--
--   interior (dual Θ) (interior Θ Δ)
--     ≡ map masked (pushBinds (repsOf Θ) []) ++ unlockedScope Θ Δ
--   convCtx (dual Θ) (interior Θ Δ) ≡ convCtx Θ Δ
--
-- The crossing argument (typed in Δ) retypes one bind frame deeper by
-- `⊢rename (wkN (numBinds Θ))` + `⊢retag` (the tail relaxes
-- Δ ⊑ unlockedScope Θ Δ), and the conversion `s` transplants verbatim
-- through `convCtx-dual`.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
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
open import strong.Reduction using (hideBinds; dualScope; dual)
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

-- Unmasking a slot undoes masking it, on the nose.
unmask-mask : (a : ℕ) (Ξ : Ctxᵗ) → unmask a (mask a Ξ) ≡ Ξ
unmask-mask zero    []      = refl
unmask-mask (suc a) []      = refl
unmask-mask zero    (E ∷ Ξ) = cong (_∷ Ξ) (unmaskEnt-masked E)
  where
  unmaskEnt-masked : (E : Ent) → unmaskEnt (masked E) ≡ E
  unmaskEnt-masked E = refl
unmask-mask (suc a) (E ∷ Ξ) = cong (E ∷_) (unmask-mask a Ξ)

-- dualScope is all-unlock, so its `scope` commutes with any extra unmask.
dualScope-unmask-comm : (n : ℕ) (Θ : CtxMorph) (Y : ℕ) (Δ : Ctxᵗ)
  → scope (dualScope n Θ) (unmask Y Δ) ≡ unmask Y (scope (dualScope n Θ) Δ)
dualScope-unmask-comm n []             Y Δ = refl
dualScope-unmask-comm n (bind A ∷ Θ)   Y Δ = dualScope-unmask-comm n Θ Y Δ
dualScope-unmask-comm n (unlock X ∷ Θ) Y Δ = dualScope-unmask-comm n Θ Y Δ
dualScope-unmask-comm n (lock X ∷ Θ)   Y Δ
  rewrite dualScope-unmask-comm n Θ Y Δ =
  updateAt-updateAt-comm unmaskEnt (n + X) Y (scope (dualScope n Θ) Δ)

------------------------------------------------------------------------
-- STEP A: dualScope unmasks exactly Θ's lock positions, turning `scope`
-- into `unlockedScope`.
------------------------------------------------------------------------

stepA : (Ow : Ctxᵗ) (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scope (dualScope (length Ow) Θ) (Ow ++ scope Θ Δ) ≡ Ow ++ unlockedScope Θ Δ
stepA Ow []             Δ = refl
stepA Ow (bind A ∷ Θ)   Δ = stepA Ow Θ Δ
stepA Ow (unlock X ∷ Θ) Δ
  rewrite sym (updateAt-app-tail unmaskEnt Ow X (scope Θ Δ))
        | dualScope-unmask-comm (length Ow) Θ (length Ow + X) (Ow ++ scope Θ Δ)
        | stepA Ow Θ Δ =
  updateAt-app-tail unmaskEnt Ow X (unlockedScope Θ Δ)
stepA Ow (lock X ∷ Θ)   Δ
  rewrite sym (dualScope-unmask-comm (length Ow) Θ (length Ow + X)
                 (Ow ++ mask X (scope Θ Δ)))
        | updateAt-app-tail unmaskEnt Ow X (mask X (scope Θ Δ))
        | unmask-mask X (scope Θ Δ)
        | stepA Ow Θ Δ = refl

------------------------------------------------------------------------
-- STEP B: hideBinds masks the whole bind prefix.
------------------------------------------------------------------------

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

repsOf-dualScope : (n : ℕ) (Θ : CtxMorph) → repsOf (dualScope n Θ) ≡ []
repsOf-dualScope n []             = refl
repsOf-dualScope n (bind A ∷ Θ)   = repsOf-dualScope n Θ
repsOf-dualScope n (unlock X ∷ Θ) = repsOf-dualScope n Θ
repsOf-dualScope n (lock X ∷ Θ)   = repsOf-dualScope n Θ

repsOf-++ : (Θ₁ Θ₂ : CtxMorph) → repsOf (Θ₁ ++ Θ₂) ≡ repsOf Θ₁ ++ repsOf Θ₂
repsOf-++ []              Θ₂ = refl
repsOf-++ (bind A ∷ Θ₁)   Θ₂ = cong (_ ∷_) (repsOf-++ Θ₁ Θ₂)
repsOf-++ (unlock X ∷ Θ₁) Θ₂ = repsOf-++ Θ₁ Θ₂
repsOf-++ (lock X ∷ Θ₁)   Θ₂ = repsOf-++ Θ₁ Θ₂

repsOf-dual : (Θ : CtxMorph) → repsOf (dual Θ) ≡ []
repsOf-dual Θ rewrite repsOf-++ (hideBinds (numBinds Θ))
                                (dualScope (numBinds Θ) Θ)
                   | repsOf-hideBinds (numBinds Θ)
                   | repsOf-dualScope (numBinds Θ) Θ = refl

------------------------------------------------------------------------
-- interior-dual : the honest RHS, PROVEN
------------------------------------------------------------------------

interior-dual : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → interior (dual Θ) (interior Θ Δ)
      ≡ map masked (pushBinds (repsOf Θ) []) ++ unlockedScope Θ Δ
interior-dual Θ Δ
  rewrite repsOf-dual Θ
        | pushBinds-++ (repsOf Θ) (scope Θ Δ)
  = go
  where
  Ow : Ctxᵗ
  Ow = pushBinds (repsOf Θ) []
  lenOw : length Ow ≡ numBinds Θ
  lenOw = length-pushBinds (repsOf Θ)
  -- interior (dual Θ) Ξ = scope (dual Θ) Ξ  (dual has no binds)
  go : scope (dual Θ) (Ow ++ scope Θ Δ) ≡ map masked Ow ++ unlockedScope Θ Δ
  go rewrite scope-++ (hideBinds (numBinds Θ)) (dualScope (numBinds Θ) Θ)
                      (Ow ++ scope Θ Δ)
           | sym lenOw
           | stepA Ow Θ Δ
           | stepB Ow (unlockedScope Θ Δ) = refl

------------------------------------------------------------------------
-- convCtx-dual : the conversion context is UNCHANGED by the dual
------------------------------------------------------------------------

-- On an all-unlock morphism (like dualScope), unlockedScope = scope.
unlockedScope-dualScope : (n : ℕ) (Θ : CtxMorph) (Ξ : Ctxᵗ)
  → unlockedScope (dualScope n Θ) Ξ ≡ scope (dualScope n Θ) Ξ
unlockedScope-dualScope n []             Ξ = refl
unlockedScope-dualScope n (bind A ∷ Θ)   Ξ = unlockedScope-dualScope n Θ Ξ
unlockedScope-dualScope n (unlock X ∷ Θ) Ξ = unlockedScope-dualScope n Θ Ξ
unlockedScope-dualScope n (lock X ∷ Θ)   Ξ =
  cong (unmask (n + X)) (unlockedScope-dualScope n Θ Ξ)

-- unlockedScope skips locks, so hideBinds is invisible to the
-- conversion context.
unlockedScope-hideBinds : (k : ℕ) (Ξ : Ctxᵗ) → unlockedScope (hideBinds k) Ξ ≡ Ξ
unlockedScope-hideBinds zero    Ξ = refl
unlockedScope-hideBinds (suc k) Ξ = unlockedScope-hideBinds k Ξ

convCtx-dual : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → convCtx (dual Θ) (interior Θ Δ) ≡ convCtx Θ Δ
convCtx-dual Θ Δ
  rewrite repsOf-dual Θ
        | pushBinds-++ (repsOf Θ) (scope Θ Δ)
        | pushBinds-++ (repsOf Θ) (unlockedScope Θ Δ)
  = go
  where
  Ow : Ctxᵗ
  Ow = pushBinds (repsOf Θ) []
  lenOw : length Ow ≡ numBinds Θ
  lenOw = length-pushBinds (repsOf Θ)
  go : unlockedScope (dual Θ) (Ow ++ scope Θ Δ) ≡ Ow ++ unlockedScope Θ Δ
  go rewrite unlockedScope-++ (hideBinds (numBinds Θ))
                              (dualScope (numBinds Θ) Θ)
                              (Ow ++ scope Θ Δ)
           | unlockedScope-hideBinds (numBinds Θ)
               (unlockedScope (dualScope (numBinds Θ) Θ)
                              (Ow ++ scope Θ Δ))
           | unlockedScope-dualScope (numBinds Θ) Θ (Ow ++ scope Θ Δ)
           | sym lenOw
           | stepA Ow Θ Δ = refl


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
-- ⊑ under a common prefix  (`Δ⊑unlockedScope` itself lives in strong.Terms)
------------------------------------------------------------------------

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
-- interior Θ Δ ⊢ᵐ dual Θ
------------------------------------------------------------------------

⊢ᵐ-++ : ∀ {Δ Θ₁ Θ₂} → Δ ⊢ᵐ Θ₁ → Δ ⊢ᵐ Θ₂ → Δ ⊢ᵐ (Θ₁ ++ Θ₂)
⊢ᵐ-++ mw[]        b₂ = b₂
⊢ᵐ-++ (mw-b w b)  b₂ = mw-b w (⊢ᵐ-++ b b₂)
⊢ᵐ-++ (mw-l tv b) b₂ = mw-l tv (⊢ᵐ-++ b b₂)
⊢ᵐ-++ (mw-u d b)  b₂ = mw-u d (⊢ᵐ-++ b b₂)

-- binder slots of a pushBinds are visible
pushBinds-∋tv : (As : List Ty) (Ξ : Ctxᵗ) (j : ℕ)
  → j < length As → pushBinds As Ξ ∋tv j
pushBinds-∋tv (A ∷ As) Ξ zero    (s≤s _)  = bind _ , ez , nameable-b
pushBinds-∋tv (A ∷ As) Ξ (suc j) (s≤s lt) with pushBinds-∋tv As Ξ j lt
... | E , d , v = _ , es d , renᵉ-Nameable v

⊢ᵐ-hideBinds : (k : ℕ) (Ξ : Ctxᵗ)
  → ((j : ℕ) → j < k → Ξ ∋tv j) → Ξ ⊢ᵐ hideBinds k
⊢ᵐ-hideBinds zero    Ξ h = mw[]
⊢ᵐ-hideBinds (suc k) Ξ h =
  mw-l (h k ≤-refl) (⊢ᵐ-hideBinds k Ξ (λ j lt → h j (m≤n⇒m≤1+n lt)))

-- existence of a slot survives an in-place update
updateAt-∋e-ex : (f : Ent → Ent) (Y : ℕ) {Δ : Ctxᵗ} {X : ℕ} {E : Ent}
  → Δ ∋e X , E → ∃[ E′ ] (updateAt f Y Δ ∋e X , E′)
updateAt-∋e-ex f zero    ez        = _ , ez
updateAt-∋e-ex f (suc Y) ez        = _ , ez
updateAt-∋e-ex f zero    (es d)    = _ , es d
updateAt-∋e-ex f (suc Y) (es d) with updateAt-∋e-ex f Y d
... | E′ , d′ = _ , es d′

scope-∋e-ex : (Θ : CtxMorph) {Δ : Ctxᵗ} {X : ℕ} {E : Ent}
  → Δ ∋e X , E → ∃[ E′ ] (scope Θ Δ ∋e X , E′)
scope-∋e-ex []             d = _ , d
scope-∋e-ex (bind A ∷ Θ)   d = scope-∋e-ex Θ d
scope-∋e-ex (unlock Y ∷ Θ) d with scope-∋e-ex Θ d
... | E′ , d′ = updateAt-∋e-ex unmaskEnt Y d′
scope-∋e-ex (lock Y ∷ Θ)   d with scope-∋e-ex Θ d
... | E′ , d′ = updateAt-∋e-ex masked Y d′

-- a slot of pushBinds(As)Ξ past the binders
pushBinds-∋e-tail : (As : List Ty) {Ξ : Ctxᵗ} {X : ℕ} {E : Ent}
  → Ξ ∋e X , E → ∃[ E′ ] (pushBinds As Ξ ∋e (length As + X) , E′)
pushBinds-∋e-tail As {Ξ} {X} d
  rewrite pushBinds-++ As Ξ
        | sym (length-pushBinds As) =
  _ , ren∋-wkN (pushBinds As []) d

⊢ᵐ-dualScope-self : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ᵐ Θ
  → interior Θ Δ ⊢ᵐ dualScope (numBinds Θ) Θ
⊢ᵐ-dualScope-self Θ Δ mwΘ = go Θ mwΘ
  where
  go : (Ξ : CtxMorph) → Δ ⊢ᵐ Ξ
     → interior Θ Δ ⊢ᵐ dualScope (numBinds Θ) Ξ
  go []             _            = mw[]
  go (bind A ∷ Ξ)   (mw-b _ b)   = go Ξ b
  go (unlock X ∷ Ξ) (mw-u _ b)   = go Ξ b
  go (lock X ∷ Ξ)   (mw-l (E , d , v) b)
    with scope-∋e-ex Θ d
  ... | E′ , d′ with pushBinds-∋e-tail (repsOf Θ) d′
  ...   | E″ , d″ = mw-u d″ (go Ξ b)

⊢ᵐ-dual : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊢ᵐ Θ
  → interior Θ Δ ⊢ᵐ dual Θ
⊢ᵐ-dual Θ Δ mwΘ =
  ⊢ᵐ-++ (⊢ᵐ-hideBinds (numBinds Θ) (interior Θ Δ)
            (λ j lt → pushBinds-∋tv (repsOf Θ) (scope Θ Δ) j lt))
         (⊢ᵐ-dualScope-self Θ Δ mwΘ)

------------------------------------------------------------------------
-- The crossing argument retypes inside the dual
------------------------------------------------------------------------

crossing : (Θ : CtxMorph) {Δ : Ctxᵗ} {W : Term} {A : Ty}
  → Δ ∣ [] ⊢ W ⦂ A
  → interior (dual Θ) (interior Θ Δ) ∣ []
      ⊢ wkᴹ (numBinds Θ) W ⦂ shiftBy (numBinds Θ) A
crossing Θ {Δ} {W} {A} ⊢W =
  subst (λ C → C ∣ [] ⊢ wkᴹ (numBinds Θ) W ⦂ shiftBy (numBinds Θ) A)
        (sym (interior-dual Θ Δ))
        step3
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
  step3 : (Ξ ++ unlockedScope Θ Δ) ∣ []
            ⊢ wkᴹ (numBinds Θ) W ⦂ shiftBy (numBinds Θ) A
  step3 = ⊢retag (⊑-app Ξ (Δ⊑unlockedScope Θ Δ)) step2

------------------------------------------------------------------------
-- PeelCase, PROVEN for dual
------------------------------------------------------------------------

numBinds-dual : (Θ : CtxMorph) → numBinds (dual Θ) ≡ 0
numBinds-dual Θ = cong length (repsOf-dual Θ)

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
                  (crossing Θ ⊢W) ⊢s-tr wAᵈ
