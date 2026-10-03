module proof.DGG.drafts.EvolveImpWfInteriorCounterexample where

-- File Charter:
--   * A CHECKED COUNTEREXAMPLE (2026-10-03) to `EvolveImp` (EvolveImpDef)
--     with the premise `WfWorld Wᵢ` that the boundary rules gained the
--     same day.  A PROBE, not part of the development.
--   * The world W₀ has one name X for rep. var 0 := ℕ, paired with
--     itself globally.  The term is `$ 1 ⟪ unbind X , id ℕ ⟫` on both
--     sides: the boundary hides X.  One matched TyBeta (`ev-2`) with
--     payload ` 0 (that is, X's rep. var; all of ev-2's premises hold)
--     adds the global pair (0, 0) with payloads ` 1 / ` 1.  Inside the
--     boundary no name denotes rep. var 1, so the payload has no
--     reading there: no interior world of the shifted boundary has
--     `Agree` for (0, 0), hence none is well formed, and no rule relates
--     the shifted terms.
--   * `not-evolve-imp : ¬ EvolveImp`, and `not-alloc-imp2 : ¬ AllocImp2`
--     (drafts/AllocImpDef) from the same data.  The same happens for
--     `ev-L⇔` (its new pair's left payload).  `ev-L`/`ev-R` add no pair.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
open import proof.DGG.EvolveImpDef using (EvolveImp)

-- X names rep. var 0 := ℕ (TyBetaCtx), paired with itself globally
W₀ : World TyBetaCtx TyBetaCtx
W₀ = world (X⊑X ∷ []) (keep []↪) (keep []↪) ((0 , 0) ∷ []) []

right-unique₀ : ∀ {α α′ β} → Paired W₀ α β → Paired W₀ α′ β → α ≡ α′
right-unique₀ (inj₁ here⇔) (inj₁ here⇔) = refl
right-unique₀ (inj₁ here⇔) (inj₁ (there⇔ ()))
right-unique₀ (inj₁ (there⇔ ())) _
right-unique₀ (inj₁ here⇔) (inj₂ ())
right-unique₀ (inj₂ ()) _

agree-ℕ : ∀ {Δ Δ′} {W : World Δ Δ′} → Δ ∋rep 0 := `ℕ → Δ′ ∋rep 0 := `ℕ
  → Agree W 0 0
agree-ℕ l r = rep-rep l r same-ℕ same-ℕ (ι⊑ι base-ℕ)

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
agree-new = rep-rep r-here r-here (same-var here) (same-var here) X⊑X

ev₀ : W₀ ⟿[ new R₀ ∷ [] ∣ new R₀ ∷ [] ] alloc² R₀ R₀ W₀
ev₀ = ev-2 wR₀ wR₀ agree-new ev-done

------------------------------------------------------------------------
-- No well-formed interior world for the shifted boundary
------------------------------------------------------------------------

W₁ : World (allocate R₀ TyBetaCtx) (allocate R₀ TyBetaCtx)
W₁ = alloc² R₀ R₀ W₀

-- the interior of the shifted boundary has no names
Θ₁ : Boundary
Θ₁ = unbind 0 1 ∷ []

-- Agree for (0, 0) needs a reading of ` 1 through each side's names
no-agree-left : ∀ {Δ′} {W : World ((bindR R₀ ∷ bindR `ℕ ∷ []) ∣ []) Δ′}
  → ¬ Agree W 0 0
no-agree-left (abst-abst () r)
no-agree-left (abst-★ () r)
no-agree-left (rep-rep r-here r (same-var ()) s′ p)

no-agree-right : ∀ {Δ} {W : World Δ ((bindR R₀ ∷ bindR `ℕ ∷ []) ∣ [])}
  → ¬ Agree W 0 0
no-agree-right (abst-abst l ())
no-agree-right (abst-★ l ())
no-agree-right (rep-rep l r-here s (same-var ()) p)

paired₀ : ∀ {Δ Δ′} {W : World Δ Δ′} → ϱᵍʷ W ≡ ϱᵍʷ W₁ → Paired W 0 0
paired₀ eq = inj₁ (subst (λ ϱ → ϱ ∋ᵨ 0 ⇔ 0) (sym′ eq) here⇔)
  where
  sym′ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym′ refl = refl

shifted-unrelated : ∀ {q : `ℕ ⊑ᵂ⟨ W₁ ⟩ `ℕ}
  → ¬ (W₁ ∣ [] ⊢ ($ 1) ⟪ Θ₁ , c₀ ⟫ ⊑ ($ 1) ⟪ Θ₁ , c₀ ⟫ ∶ q)
shifted-unrelated
  (⟪⟫⊑⟪⟫ {Wᵢ = Wᵢ} (interior-world
           (interior (changes∷ changes[] (step-unbind v del-here fr)))
           ir eqᵍ eqˡ jc jf ml mr) wi M⊑ b b′ bc q) =
  no-agree-left (wf-agree wi (paired₀ {W = Wᵢ} eqᵍ))
shifted-unrelated
  (⟪⟫⊑ {Wᵢ = Wᵢ} (interior-world
         (interior (changes∷ changes[] (step-unbind v del-here fr)))
         ir eqᵍ eqˡ jc jf ml mr) wi M⊑ b q) =
  no-agree-left (wf-agree wi (paired₀ {W = Wᵢ} eqᵍ))
shifted-unrelated
  (⊑⟪⟫ {Wᵢ = Wᵢ} (interior-world il
         (interior (changes∷ changes[] (step-unbind v del-here fr)))
         eqᵍ eqˡ jc jf ml mr) wi M⊑ b′ q) =
  no-agree-right (wf-agree wi (paired₀ {W = Wᵢ} eqᵍ))

not-evolve-imp : ¬ EvolveImp
not-evolve-imp evolve-imp =
  shifted-unrelated
    (proj₂ (proj₂ (evolve-imp TyBetaCtx-wf TyBetaCtx-wf ev₀ wf₀ M₀⊑M₀)))

-- the same data refutes the draft corollary AllocImp2 directly
open import proof.DGG.drafts.AllocImpDef using (AllocImp2)

not-alloc-imp2 : ¬ AllocImp2
not-alloc-imp2 alloc-imp-2 =
  shifted-unrelated (proj₂ (proj₂ (alloc-imp-2 wR₀ wR₀ agree-new wf₀ M₀⊑M₀)))
