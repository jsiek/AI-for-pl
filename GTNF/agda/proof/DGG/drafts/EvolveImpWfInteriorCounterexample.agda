module proof.DGG.drafts.EvolveImpWfInteriorCounterexample where

-- File Charter:
--   * REGRESSION TEST for a counterexample to `EvolveImp` found on
--     2026-10-03.  The world W₀ has one name X for rep. var 0 := ℕ,
--     paired with itself globally; the term is `$ 1 ⟪ unbind X , id ℕ ⟫`
--     on both sides (the boundary hides X).  One matched TyBeta (`ev-2`)
--     with payload ` 0 (X's rep. var) adds the global pair (0, 0) with
--     payloads ` 1 / ` 1.  When `Agree` read payloads through each
--     side's names, ` 1 had no reading inside the boundary, so no
--     interior world was well formed and the shifted terms were
--     unrelated (`¬ EvolveImp`, `¬ AllocImp2`).
--   * THE FIX (Jeremy, 2026-10-03; design.md D23): payloads are compared
--     in the representation universe (`RepImp`, ImprecisionWorld §8);
--     ` 1 ⊑ ` 1 holds because (1, 1) is paired.  Below: the evolved
--     world W₁ and the shifted boundary's interior world Wᵢ₁ are well
--     formed, and the shifted terms are related (`evolved`, EvolveImp's
--     conclusion at this instance).
--   * See proof/DGG/notes/RepImp.md.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

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

-- X names rep. var 0 := ℕ (TyBetaCtx), paired with itself globally
W₀ : World TyBetaCtx TyBetaCtx
W₀ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

right-unique₀ : ∀ {α α′ β} → Paired W₀ α β → Paired W₀ α′ β → α ≡ α′
right-unique₀ (inj₁ here⇔) (inj₁ here⇔) = refl
right-unique₀ (inj₁ here⇔) (inj₁ (there⇔ ()))
right-unique₀ (inj₁ (there⇔ ())) _
right-unique₀ (inj₁ here⇔) (inj₂ ())
right-unique₀ (inj₂ ()) _

agree-ℕ : ∀ {Δ Δ′} {W : World Δ Δ′} {α β}
  → Δ ∋rep α := `ℕ → Δ′ ∋rep β := `ℕ → Agree W α β
agree-ℕ l r = rep-rep l r (ι⊑ι base-ℕ)

wf₀ : WfWorld W₀
wf₀ = wf-world (both (inj₁ here⇔) joint[])
  (λ { (inj₁ here⇔) → agree-ℕ r-here r-here
     ; (inj₁ (there⇔ ())) ; (inj₂ ()) })
  right-unique₀

-- the boundary hides X
Θ₀ : Boundary
Θ₀ = unbind 0 0 ∷ []

Δᵢ : Ctxᵗ
Δᵢ = (bindR `ℕ ∷ []) ∣ []

int₀ : TyBetaCtx ⊢ⁱ Θ₀ ⇒ Δᵢ
int₀ = interior (changes∷ changes[] (step-unbind (_ , here) del-here fresh[]))

conv₀ : TyBetaCtx ⊢ᶜ Θ₀ ⇒ TyBetaCtx
conv₀ = conversion (conv-unbind (_ , here) conv[])

c₀ : Conv
c₀ = ⌞ id `ℕ ⌟

b₀ : BdyTy TyBetaCtx Θ₀ Δᵢ `ℕ c₀ `ℕ
b₀ = bdy-ty (bw TyBetaCtx-wf int₀ conv₀)
  (conv-tail (conv-mid (conv-id base-ℕ)))
  (`ℕ , same-ℕ , same-ℕ) (`ℕ , same-ℕ , same-ℕ) wf-ℕ

Wᵢ₀ : World Δᵢ Δᵢ
Wᵢ₀ = world [] []↪ []↪ ((0 , 0) ∷ []) []

interior₀ : Interior W₀ Θ₀ Θ₀ Wᵢ₀
interior₀ = interior-world int₀ int₀ refl refl
  (λ { (_ , ()) _ _ _ }) (λ { () _ _ })
  (λ { (_ , ()) _ _ }) (λ { (_ , ()) _ _ })

wfᵢ₀ : WfWorld Wᵢ₀
wfᵢ₀ = wf-world joint[]
  (λ { (inj₁ here⇔) → agree-ℕ r-here r-here
     ; (inj₁ (there⇔ ())) ; (inj₂ ()) })
  (λ { (inj₁ here⇔) (inj₁ here⇔) → refl
     ; (inj₁ here⇔) (inj₁ (there⇔ ())) ; (inj₁ (there⇔ ())) _
     ; (inj₁ here⇔) (inj₂ ()) ; (inj₂ ()) _ })

cint₀ : ConversionInterior W₀ Θ₀ Θ₀ W₀
cint₀ = conversion-interior-world conv₀ conv₀ refl refl
  (λ { here here here here → (λ j → j) , (λ j → j) })
  (λ { here here (inj₁ (fresh∷ ne _)) → ⊥-elim (ne refl)
     ; here here (inj₂ (fresh∷ ne _)) → ⊥-elim (ne refl) })
  (λ { here here mk → mk }) (λ { here here mk → mk })
  where open import Data.Empty using (⊥-elim)

M₀ : Term
M₀ = ($ 1) ⟪ Θ₀ , c₀ ⟫

M₀⊑M₀ : W₀ ∣ [] ⊢ M₀ ⊑ M₀ ∶ ι⊑ι base-ℕ
M₀⊑M₀ = ⟪⟫⊑⟪⟫ interior₀ wfᵢ₀ (κ⊑κ lit-$ (ι⊑ι base-ℕ)) b₀ b₀
  (W₀ , cint₀ , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))
  (ι⊑ι base-ℕ)

-- one matched TyBeta, payload X's rep. var on both sides
R₀ : Ty
R₀ = ` 0

wR₀ : reps TyBetaCtx ⊢ᴿ R₀
wR₀ = wfᴿ-var (free-ref here)

agree-new : Agree (alloc² R₀ R₀ W₀) 0 0
agree-new = rep-rep r-here r-here (α⊑β (inj₁ (there⇔ here⇔)))

ev₀ : W₀ ⟿[ new R₀ ∷ [] ∣ new R₀ ∷ [] ] alloc² R₀ R₀ W₀
ev₀ = ev-2 wR₀ wR₀ agree-new ev-done

------------------------------------------------------------------------
-- The evolved world and the shifted boundary are well formed
------------------------------------------------------------------------

W₁ : World (allocate R₀ TyBetaCtx) (allocate R₀ TyBetaCtx)
W₁ = alloc² R₀ R₀ W₀

-- rep. var 0 := ` 1 (X's rep. var, renumbered), rep. var 1 := ℕ
agree₁ : ∀ {α β} → Paired W₁ α β → Agree W₁ α β
agree₁ (inj₁ here⇔) = agree-new
agree₁ (inj₁ (there⇔ here⇔)) = agree-ℕ (r-there r-here) (r-there r-here)
agree₁ (inj₁ (there⇔ (there⇔ ())))
agree₁ (inj₂ ())

unique₁ : ∀ {α α′ β} → Paired W₁ α β → Paired W₁ α′ β → α ≡ α′
unique₁ (inj₁ here⇔) (inj₁ here⇔) = refl
unique₁ (inj₁ here⇔) (inj₁ (there⇔ (there⇔ ())))
unique₁ (inj₁ (there⇔ here⇔)) (inj₁ (there⇔ here⇔)) = refl
unique₁ (inj₁ (there⇔ here⇔)) (inj₁ (there⇔ (there⇔ ())))
unique₁ (inj₁ (there⇔ (there⇔ ()))) _
unique₁ (inj₁ _) (inj₂ ())
unique₁ (inj₂ ()) _

wf₁ : WfWorld W₁
wf₁ = wf-world (both (inj₁ (there⇔ here⇔)) joint[]) agree₁ unique₁

-- the boundary, shifted past the new rep. var, still hides X
Θ₁ : Boundary
Θ₁ = unbind 0 1 ∷ []

Δ₁ : Ctxᵗ
Δ₁ = allocate R₀ TyBetaCtx

Δ₁-wf : WfCtx Δ₁
Δ₁-wf = wf-ctx (wf-bindR wR₀ (wf-bindR wfᴿ-ℕ wf-reps[]))
  (λ { here → _ , there here })
  (unique∷ fresh[] unique[])

Δᵢ₁ : Ctxᵗ
Δᵢ₁ = (bindR R₀ ∷ bindR `ℕ ∷ []) ∣ []

int₁ : Δ₁ ⊢ⁱ Θ₁ ⇒ Δᵢ₁
int₁ = interior
  (changes∷ changes[] (step-unbind (_ , there here) del-here fresh[]))

conv₁ : Δ₁ ⊢ᶜ Θ₁ ⇒ Δ₁
conv₁ = conversion (conv-unbind (_ , there here) conv[])

b₁ : BdyTy Δ₁ Θ₁ Δᵢ₁ `ℕ c₀ `ℕ
b₁ = bdy-ty (bw Δ₁-wf int₁ conv₁)
  (conv-tail (conv-mid (conv-id base-ℕ)))
  (`ℕ , same-ℕ , same-ℕ) (`ℕ , same-ℕ , same-ℕ) wf-ℕ

-- no names inside; both global pairs kept
Wᵢ₁ : World Δᵢ₁ Δᵢ₁
Wᵢ₁ = world [] []↪ []↪ ((0 , 0) ∷ (1 , 1) ∷ []) []

interior₁ : Interior W₁ Θ₁ Θ₁ Wᵢ₁
interior₁ = interior-world int₁ int₁ refl refl
  (λ { (_ , ()) _ _ _ }) (λ { () _ _ })
  (λ { (_ , ()) _ _ }) (λ { (_ , ()) _ _ })

-- THE REGRESSION: ` 1 ⊑ ` 1 by the pair (1, 1), with no name for 1
agreeᵢ₁ : ∀ {α β} → Paired Wᵢ₁ α β → Agree Wᵢ₁ α β
agreeᵢ₁ (inj₁ here⇔) = rep-rep r-here r-here (α⊑β (inj₁ (there⇔ here⇔)))
agreeᵢ₁ (inj₁ (there⇔ here⇔)) = agree-ℕ (r-there r-here) (r-there r-here)
agreeᵢ₁ (inj₁ (there⇔ (there⇔ ())))
agreeᵢ₁ (inj₂ ())

uniqueᵢ₁ : ∀ {α α′ β} → Paired Wᵢ₁ α β → Paired Wᵢ₁ α′ β → α ≡ α′
uniqueᵢ₁ (inj₁ here⇔) (inj₁ here⇔) = refl
uniqueᵢ₁ (inj₁ here⇔) (inj₁ (there⇔ (there⇔ ())))
uniqueᵢ₁ (inj₁ (there⇔ here⇔)) (inj₁ (there⇔ here⇔)) = refl
uniqueᵢ₁ (inj₁ (there⇔ here⇔)) (inj₁ (there⇔ (there⇔ ())))
uniqueᵢ₁ (inj₁ (there⇔ (there⇔ ()))) _
uniqueᵢ₁ (inj₁ _) (inj₂ ())
uniqueᵢ₁ (inj₂ ()) _

wfᵢ₁ : WfWorld Wᵢ₁
wfᵢ₁ = wf-world joint[] agreeᵢ₁ uniqueᵢ₁

cint₁ : ConversionInterior W₁ Θ₁ Θ₁ W₁
cint₁ = conversion-interior-world conv₁ conv₁ refl refl
  (λ { here here here here → (λ j → j) , (λ j → j) })
  (λ { here here (inj₁ (fresh∷ ne _)) → ⊥-elim (ne refl)
     ; here here (inj₂ (fresh∷ ne _)) → ⊥-elim (ne refl) })
  (λ { here here mk → mk }) (λ { here here mk → mk })
  where open import Data.Empty using (⊥-elim)

M₁ : Term
M₁ = ($ 1) ⟪ Θ₁ , c₀ ⟫

M₁⊑M₁ : W₁ ∣ [] ⊢ M₁ ⊑ M₁ ∶ ι⊑ι base-ℕ
M₁⊑M₁ = ⟪⟫⊑⟪⟫ interior₁ wfᵢ₁ (κ⊑κ lit-$ (ι⊑ι base-ℕ)) b₁ b₁
  (W₁ , cint₁ , conv-tail⊑tail (conv-mid⊑mid (conv-id⊑id (ι⊑ι base-ℕ))))
  (ι⊑ι base-ℕ)

-- EvolveImp's conclusion at the former counterexample
evolved : WfWorld W₁
  × Σ[ q ∈ `ℕ ⊑ᵂ⟨ W₁ ⟩ `ℕ ]
      (W₁ ∣ [] ⊢ ↑ᴹ*[ new R₀ ∷ [] ] M₀ ⊑ ↑ᴹ*[ new R₀ ∷ [] ] M₀ ∶ q)
evolved = wf₁ , ι⊑ι base-ℕ , M₁⊑M₁
