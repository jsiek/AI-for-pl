module strong.proof.MaskFacts where

-- NO BOUNDARY OPERATION CAN TAKE AN OWNER AWAY.
--
-- Masking RETAINS the owner's entry, and an alias RECOVERS it.  In the
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
  → (mask Y Δ ∋ X := A) ⊎ (mask Y Δ ∋e X , blk (bind A))
mask-retains {X = X} {Y = Y} d with Y ≟ℕ X
... | yes refl = inj₂ (upd-hit blk blk-comm d)
... | no ne    = inj₁ (upd-miss blk blk-comm ne d)

unlock-recovers : ∀ {Δ X A} → Δ ∋e X , blk (bind A) → unmask X Δ ∋ X := A
unlock-recovers d = upd-hit unblk unblk-comm d

-- The round trip is the identity on the type context: a program that hides from
-- itself and then looks again is harmless and typeable.
lock-then-unlock : intC (unlock 0 ∷ []) (intC (lock 0 ∷ []) (bind `ℕ ∷ []))
             ≡ bind `ℕ ∷ []
lock-then-unlock = refl

------------------------------------------------------------------------
-- Cancel's residue defect (repair 3a), as a refutation
------------------------------------------------------------------------

-- The mini-core's Cancel appended `lockBinds (nbind Θ₂)` to the residue.
-- `scp` applies those masks to Δ, not to the boundary's bind owners, so on
-- the mini-core's OWN cancel example the residue is not well formed.  This
-- is why strong.Reduction's CancelR drops it.
¬Bwf-cancel-residue : ¬ Bwf [] (bind `ℕ ∷ lock 0 ∷ [])
¬Bwf-cancel-residue (bw-b _ (bw-l (_ , () , _) _))

------------------------------------------------------------------------
-- THE MASK-ONLY FACT, PROVEN
------------------------------------------------------------------------

-- `intC Θ Δ` and `fceC Θ Δ` differ ONLY by masking: `scp` applies the
-- `lock` masks, `fscp` skips them, and both do the same binds and the
-- same unmasks.  Masking never turns an `abst` into a `bind` — it only
-- wraps and unwraps `blk` — so a slot that is VISIBLE inside and an OWNER
-- outside is that same owner inside.  This is the one structural step
-- `idPush⁺` (proof/IdPushReach, `MaskOnly`) and CancelR's preservation
-- case consume; here it is a theorem, not an interface.
--
-- The invariant that carries it: the CORE of an entry — what it is once
-- every conceal is peeled — is untouched by `blk` and by `unblk` alike.

core : Ent → Ent
core abst     = abst
core (bind A) = bind A
core (blk E)  = core E

core-ren : (ρ : Renameᵗ) (E : Ent) → core (renᵉ ρ E) ≡ renᵉ ρ (core E)
core-ren ρ abst     = refl
core-ren ρ (bind A) = refl
core-ren ρ (blk E)  = core-ren ρ E

core-vis : ∀ {E} → Vis E → core E ≡ E
core-vis vis-a = refl
core-vis vis-b = refl

core-blk : (E : Ent) → core (blk E) ≡ core E
core-blk E = refl

core-unblk : (E : Ent) → core (unblk E) ≡ core E
core-unblk abst     = refl
core-unblk (bind A) = refl
core-unblk (blk E)  = refl

-- Two type contexts agree UP TO CONCEALMENT at every slot.
CoreEq : Ctxᵗ → Ctxᵗ → Set
CoreEq Δ Δ′ = ∀ {Y E E′} → Δ ∋e Y , E → Δ′ ∋e Y , E′ → core E ≡ core E′

CoreEq-refl : (Δ : Ctxᵗ) → CoreEq Δ Δ
CoreEq-refl Δ d d′ = cong core (∋e-det d d′)

module _ (f : Ent → Ent)
         (fc : ∀ ρ E → renᵉ ρ (f E) ≡ f (renᵉ ρ E))
         (fcore : ∀ E → core (f E) ≡ core E) where

  -- one update on the LEFT only (the `lock` case: `scp` masks, `fscp`
  -- skips)
  CoreEq-updˡ : ∀ {Δ Δ′ X} → CoreEq Δ Δ′ → CoreEq (upd f X Δ) Δ′
  CoreEq-updˡ {X = X} ce {Y = Y} d d′ with X ≟ℕ Y
  CoreEq-updˡ {X = X} ce d d′ | yes refl with upd-hit⁻ f fc d
  CoreEq-updˡ {X = X} ce d d′ | yes refl | E₀ , d₀ , refl =
    trans (fcore E₀) (ce d₀ d′)
  CoreEq-updˡ {X = X} ce d d′ | no ne = ce (upd-miss⁻ f fc ne d) d′

  -- one update on BOTH sides (the `unlock` case)
  CoreEq-upd : ∀ {Δ Δ′ X} → CoreEq Δ Δ′ → CoreEq (upd f X Δ) (upd f X Δ′)
  CoreEq-upd {X = X} ce {Y = Y} d d′ with X ≟ℕ Y
  CoreEq-upd {X = X} ce d d′ | yes refl
    with upd-hit⁻ f fc d | upd-hit⁻ f fc d′
  CoreEq-upd {X = X} ce d d′ | yes refl | E₀ , d₀ , refl | E₁ , d₁ , refl =
    trans (fcore E₀) (trans (ce d₀ d₁) (sym (fcore E₁)))
  CoreEq-upd {X = X} ce d d′ | no ne =
    ce (upd-miss⁻ f fc ne d) (upd-miss⁻ f fc ne d′)

CoreEq-scp : (Θ : CtxMorph) (Δ : Ctxᵗ) → CoreEq (scp Θ Δ) (fscp Θ Δ)
CoreEq-scp []             Δ = CoreEq-refl Δ
CoreEq-scp (bind A ∷ Θ)   Δ = CoreEq-scp Θ Δ
CoreEq-scp (lock X ∷ Θ)   Δ =
  CoreEq-updˡ blk blk-comm core-blk (CoreEq-scp Θ Δ)
CoreEq-scp (unlock X ∷ Θ) Δ =
  CoreEq-upd unblk unblk-comm core-unblk (CoreEq-scp Θ Δ)

CoreEq-prep : ∀ {Δ Δ′} (As : List Ty)
  → CoreEq Δ Δ′ → CoreEq (prep As Δ) (prep As Δ′)
CoreEq-prep []       ce d      d′       = ce d d′
CoreEq-prep (A ∷ As) ce ez     ez       = refl
CoreEq-prep (A ∷ As) ce (es {E = E} d) (es {E = E′} d′) =
  trans (core-ren suc E)
        (trans (cong ⇑ᵉ (CoreEq-prep As ce d d′))
               (sym (core-ren suc E′)))

-- THE FACT.  (Stated exactly as `strong.proof.IdPushReach.MaskOnly`.)
mask-only : ∀ (Θ : CtxMorph) (Δ : Ctxᵗ) {Y A}
  → intC Θ Δ ∋tv Y → fceC Θ Δ ∋ Y := A → intC Θ Δ ∋ Y := A
mask-only Θ Δ (E , d , v) df =
  subst (λ F → intC Θ Δ ∋e _ , F)
        (trans (sym (core-vis v))
               (CoreEq-prep (reps Θ) (CoreEq-scp Θ Δ) d df))
        d
