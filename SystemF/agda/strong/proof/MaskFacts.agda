module strong.proof.MaskFacts where

-- NO BOUNDARY OPERATION CAN TAKE A BINDER AWAY.
--
-- Masking RETAINS the binder's entry, and an alias RECOVERS it.  In the
-- previous design this is exactly what failed: `entᴳ` wrote `rvl⋆` at the
-- slot (demote-x-always, demote-count-break/n1b/n4), the rebuild carried
-- `abst`, and the crossing value's licence died (¬⊢W-rebuild).
--
-- Also here: the witness for Cancel's residue defect (repair 3a).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; Renameᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms

mask-retains : ∀ {Δ X Y A} → Δ ∋ X := A
  → (mask Y Δ ∋ X := A) ⊎ (mask Y Δ ∋e X , masked (bind A))
mask-retains {X = X} {Y = Y} d with Y ≟ℕ X
... | yes refl = inj₂ (updateAt-hit masked masked-comm d)
... | no ne    = inj₁ (updateAt-miss masked masked-comm ne d)

unlock-recovers : ∀ {Δ X A} → Δ ∋e X , masked (bind A) → unmask X Δ ∋ X := A
unlock-recovers d = updateAt-hit unmaskEnt unmaskEnt-comm d

-- The round trip is the identity on the type context: a program that hides from
-- itself and then looks again is harmless and typeable.
lock-then-unlock :
  interior (unlock 0 ∷ []) (interior (lock 0 ∷ []) (bind `ℕ ∷ []))
    ≡ bind `ℕ ∷ []
lock-then-unlock = refl

------------------------------------------------------------------------
-- Cancel's residue defect (repair 3a), as a refutation
------------------------------------------------------------------------

-- The mini-core's Cancel appended `hideBinds (numBinds Θ₂)` to the residue.
-- `scope` applies those masks to Δ, not to the boundary's `bind` entries,
-- so on
-- the mini-core's OWN cancel example the residue is not well formed.  This
-- is why strong.Reduction's CancelR drops it.
¬⊢ᵐ-cancel-residue : ¬ ([] ⊢ᵐ (bind `ℕ ∷ lock 0 ∷ []))
¬⊢ᵐ-cancel-residue (mw-b _ (mw-l (_ , () , _) _))

------------------------------------------------------------------------
-- THE MASK-ONLY FACT, PROVEN
------------------------------------------------------------------------

-- `interior Θ Δ` and `convCtx Θ Δ` differ ONLY by masking: `scope` applies the
-- `lock` masks, `unlockedScope` skips them, and both do the same binds and the
-- same unmasks.  Masking never turns an `abst` into a `bind` — it only
-- wraps and unwraps `masked` — so a slot that is VISIBLE inside and a BINDER
-- outside is that same binder inside.  This is the one structural step
-- `idPush⁺` (proof/IdPushReach, `MaskOnly`) and CancelR's preservation
-- case consume; here it is a theorem, not an interface.
--
-- The invariant that carries it: the CORE of an entry — what it is once
-- every conceal is peeled — is untouched by `masked` and by `unmaskEnt` alike.

core : Ent → Ent
core abst        = abst
core (bind A)    = bind A
core (masked E)  = core E

core-ren : (ρ : Renameᵗ) (E : Ent) → core (renᵉ ρ E) ≡ renᵉ ρ (core E)
core-ren ρ abst        = refl
core-ren ρ (bind A)    = refl
core-ren ρ (masked E)  = core-ren ρ E

core-nameable : ∀ {E} → Nameable E → core E ≡ E
core-nameable nameable-a = refl
core-nameable nameable-b = refl

core-masked : (E : Ent) → core (masked E) ≡ core E
core-masked E = refl

core-unmaskEnt : (E : Ent) → core (unmaskEnt E) ≡ core E
core-unmaskEnt abst        = refl
core-unmaskEnt (bind A)    = refl
core-unmaskEnt (masked E)  = refl

-- Two type contexts agree UP TO CONCEALMENT at every slot.
CoreEq : Ctxᵗ → Ctxᵗ → Set
CoreEq Δ Δ′ = ∀ {Y E E′} → Δ ∋e Y , E → Δ′ ∋e Y , E′ → core E ≡ core E′

CoreEq-refl : (Δ : Ctxᵗ) → CoreEq Δ Δ
CoreEq-refl Δ d d′ = cong core (∋e-det d d′)

module _ (f : Ent → Ent)
         (fc : ∀ ρ E → renᵉ ρ (f E) ≡ f (renᵉ ρ E))
         (fcore : ∀ E → core (f E) ≡ core E) where

  -- one update on the LEFT only (the `lock` case: `scope` masks,
  -- `unlockedScope` skips)
  CoreEq-updateAtˡ : ∀ {Δ Δ′ X} → CoreEq Δ Δ′ → CoreEq (updateAt f X Δ) Δ′
  CoreEq-updateAtˡ {X = X} ce {Y = Y} d d′ with X ≟ℕ Y
  CoreEq-updateAtˡ {X = X} ce d d′ | yes refl with updateAt-hit⁻ f fc d
  CoreEq-updateAtˡ {X = X} ce d d′ | yes refl | E₀ , d₀ , refl =
    trans (fcore E₀) (ce d₀ d′)
  CoreEq-updateAtˡ {X = X} ce d d′ | no ne = ce (updateAt-miss⁻ f fc ne d) d′

  -- one update on BOTH sides (the `unlock` case)
  CoreEq-updateAt : ∀ {Δ Δ′ X} → CoreEq Δ Δ′
    → CoreEq (updateAt f X Δ) (updateAt f X Δ′)
  CoreEq-updateAt {X = X} ce {Y = Y} d d′ with X ≟ℕ Y
  CoreEq-updateAt {X = X} ce d d′ | yes refl
    with updateAt-hit⁻ f fc d | updateAt-hit⁻ f fc d′
  CoreEq-updateAt {X = X} ce d d′ | yes refl | E₀ , d₀ , refl | E₁ , d₁ , refl =
    trans (fcore E₀) (trans (ce d₀ d₁) (sym (fcore E₁)))
  CoreEq-updateAt {X = X} ce d d′ | no ne =
    ce (updateAt-miss⁻ f fc ne d) (updateAt-miss⁻ f fc ne d′)

CoreEq-scope : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → CoreEq (scope Θ Δ) (unlockedScope Θ Δ)
CoreEq-scope []             Δ = CoreEq-refl Δ
CoreEq-scope (bind A ∷ Θ)   Δ = CoreEq-scope Θ Δ
CoreEq-scope (lock X ∷ Θ)   Δ =
  CoreEq-updateAtˡ masked masked-comm core-masked (CoreEq-scope Θ Δ)
CoreEq-scope (unlock X ∷ Θ) Δ =
  CoreEq-updateAt unmaskEnt unmaskEnt-comm core-unmaskEnt (CoreEq-scope Θ Δ)

CoreEq-pushBinds : ∀ {Δ Δ′} (As : List Ty)
  → CoreEq Δ Δ′ → CoreEq (pushBinds As Δ) (pushBinds As Δ′)
CoreEq-pushBinds []       ce d      d′       = ce d d′
CoreEq-pushBinds (A ∷ As) ce ez     ez       = refl
CoreEq-pushBinds (A ∷ As) ce (es {E = E} d) (es {E = E′} d′) =
  trans (core-ren suc E)
        (trans (cong ⇑ᵉ (CoreEq-pushBinds As ce d d′))
               (sym (core-ren suc E′)))

-- THE FACT.  (Stated exactly as `strong.proof.IdPushReach.MaskOnly`.)
mask-only : ∀ (Θ : CtxMorph) (Δ : Ctxᵗ) {Y A}
  → interior Θ Δ ∋tv Y → convCtx Θ Δ ∋ Y := A → interior Θ Δ ∋ Y := A
mask-only Θ Δ (E , d , v) df =
  subst (λ F → interior Θ Δ ∋e _ , F)
        (trans (sym (core-nameable v))
               (CoreEq-pushBinds (repsOf Θ) (CoreEq-scope Θ Δ) d df))
        d
