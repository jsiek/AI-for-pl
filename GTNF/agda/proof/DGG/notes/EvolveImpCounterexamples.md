# EvolveImp counterexamples (2026-10-03)

These proved `¬ EvolveImp` against the first definition of `W ⟿[ ξs ∣ ξs′ ] W′`. They led to the premises the constructors now carry (proof/DGG/Evolve.agda charter). The Agda source is kept below for the record; it no longer type-checks, by design.

```agda
module proof.DGG.notes.EvolveImpCounterexamples where

-- File Charter:
--   * CHECKED COUNTEREXAMPLES to `EvolveImp` (EvolveImpDef) as stated
--     (2026-10-03).  Each refutes the statement at the closed world ∅ʷ
--     with a one-step evolution:
--     1. `ev-2` with payloads ℕ / 𝔹: `WfWorld (alloc² ℕ 𝔹 ∅ʷ)` fails,
--        the new global pair (0, 0) has no `Agree` (ℕ ⋢ 𝔹).
--     2. `ev-L⇔` at β = 0 with an empty right context: `WfWorld` fails,
--        the new pair (0, 0) names a right rep. var that is not in scope.
--     3. `ev-L` with the ill-formed payload ` 0: the ⊑ conclusion fails.
--        A left boundary `$ 7 ⟪ [] , id ℕ ⟫` would have to be typed at
--        `bindR (` 0) ∷ [] ∣ []`, whose `WfCtx` (inside BoundaryWf)
--        does not hold.
--   * A PROBE, not part of the development; All.agda does not import it.

open import Data.Nat using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Conversion
open import Boundary
open import Terms
open import Imprecision
open import ImprecisionWorld
open import ConversionImprecision
open import TermImprecision
open import proof.DGG.Evolve
open import proof.DGG.EvolveImpDef using (EvolveImp)
open import proof.DGG.ImprecisionTypingProof using (imprecision-typing)

wf-∅ʷ : WfWorld ∅ʷ
wf-∅ʷ = wf-world joint[] (λ { (inj₁ ()) ; (inj₂ ()) })
                 (λ { (inj₁ ()) _ ; (inj₂ ()) _ })

zero⊑zero : ∅ʷ ∣ [] ⊢ $ 0 ⊑ $ 0 ∶ ι⊑ι base-ℕ
zero⊑zero = κ⊑κ lit-$ (ι⊑ι base-ℕ)

-- 1. ev-2 with unrelated payloads
not-ev-2 : ¬ EvolveImp
not-ev-2 evolve-imp
  with wf-agree (proj₁ (evolve-imp (ev-2 {R = `ℕ} {R′ = `𝔹} ev-done)
                                    wf-∅ʷ zero⊑zero))
                (inj₁ here⇔)
... | rep-rep r-here r-here same-ℕ same-𝔹 ()

-- 2. ev-L⇔ at a right rep. var that is not in scope
no-partner : NoLeftPartner ∅ʷ 0
no-partner α (inj₁ ())
no-partner α (inj₂ ())

ev₂ : ∅ʷ ⟿[ new `ℕ ∷ [] ∣ [] ] allocᴸ⇔ `ℕ 0 ∅ʷ
ev₂ = ev-L⇔ no-partner ev-done

not-ev-L⇔ : ¬ EvolveImp
not-ev-L⇔ evolve-imp
  with wf-agree (proj₁ (evolve-imp
                  ev₂
                  wf-∅ʷ zero⊑zero))
                (inj₁ here⇔)
... | rep-rep l () s s′ p

-- 3. ev-L with an ill-formed payload
c₀ : Conv
c₀ = ⌞ id `ℕ ⌟

bw₀ : BoundaryWf empty [] empty empty
bw₀ = bw (wf-ctx wf-reps[] (λ ()) unique[]) (interior changes[])
         (conversion conv[])

b₀ : BdyTy empty [] empty `ℕ c₀ `ℕ
b₀ = bdy-ty bw₀ (conv-tail (conv-mid (conv-id base-ℕ)))
            (`ℕ , same-ℕ , same-ℕ) (`ℕ , same-ℕ , same-ℕ) wf-ℕ

int₀ : Interior ∅ʷ [] [] ∅ʷ
int₀ = interior-world (interior changes[]) (interior changes[]) _≡_.refl
  _≡_.refl (λ { (_ , ()) _ _ _ }) (λ { () _ _ })
  (λ { (_ , ()) _ _ }) (λ { (_ , ()) _ _ })
  where open import Relation.Binary.PropositionalEquality using (_≡_)

cint₀ : ConversionInterior ∅ʷ [] [] ∅ʷ
cint₀ = conversion-interior-world (conversion conv[]) (conversion conv[])
  _≡_.refl _≡_.refl (λ { () _ _ _ }) (λ { () _ _ })
  (λ { () _ _ }) (λ { () _ _ })
  where open import Relation.Binary.PropositionalEquality using (_≡_)

seven⊑seven : ∅ʷ ∣ [] ⊢ ($ 7) ⟪ [] , c₀ ⟫ ⊑ ($ 7) ⟪ [] , c₀ ⟫ ∶ ι⊑ι base-ℕ
seven⊑seven =
  ⟪⟫⊑⟪⟫ int₀ (κ⊑κ lit-$ (ι⊑ι base-ℕ)) b₀ b₀
    (∅ʷ , cint₀ ,
     conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))
    (ι⊑ι base-ℕ)

not-ev-L : ¬ EvolveImp
not-ev-L evolve-imp
  with proj₁ (imprecision-typing (proj₂ (proj₂ (evolve-imp
         (ev-L {R = ` 0} ev-done) wf-∅ʷ seven⊑seven))))
... | boundary (bw (wf-ctx (wf-bindR (wfᴿ-var (local-ref ())) _) _ _) _ _)
               _ _ _ _ _
... | boundary (bw (wf-ctx (wf-bindR (wfᴿ-var (free-ref ())) _) _ _) _ _)
               _ _ _ _ _
```
