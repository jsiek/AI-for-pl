module strong-rep-nu.proof.MoveScope where

-- File Charter:
--   * THE SCOPE MOVE — the ONE-LAYER contractum `Merge` builds, and the
--     preservation case it owes (`preserve-Merge : MergeCase`).  §1 the
--     merged frame's conversion context retains BOTH old ones
--     (`merged-keeps₁`, `merged-keeps₂`); §2 gluing two readings of one
--     representation; §3 MERGE, PROVED.
--   * THE MOVE.  The merged boundary presents the outer boundary's
--     exterior and the inner boundary's interior, so the frames merge
--     too: `Θ₁ ++ Θ₂`.  Both conversions are weakened onto the merged
--     conversion context (`weaken-⊢`, the Wrap lemma) and composed
--     there (`⊢⨟`, strong-rep-nu.proof.Compose).
--   * THE MIDDLE TYPE AGREES: the target of `t₁′` and the source of
--     `c₂′` weaken ONE representation (the redex's middle type) at
--     ONE context with unique names (`same-target-unique`).
-- Commentary: Commentary.md § proof/MoveScope.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.proof.Preserve using (MergeCase)
open import strong-rep-nu.proof.WrapDual using (weaken-⊢)
open import strong-rep-nu.proof.Compose using (⊢⨟)

------------------------------------------------------------------------
-- §1  The merged conversion context keeps both old ones
------------------------------------------------------------------------

-- A conversion reading of `χ₁ ++ χ₂` reads `χ₂` first.
conv-split : ∀ {Ξ Δ Δ″} (χ₁ : List Change) {χ₂ : List Change}
  → Ξ ∣ Δ ⊢χᶜ χ₁ ++ χ₂ ⇒ Δ″
  → ∃[ Δ′ ] ((Ξ ∣ Δ ⊢χᶜ χ₂ ⇒ Δ′) × (Ξ ∣ Δ′ ⊢χᶜ χ₁ ⇒ Δ″))
conv-split [] cs = _ , cs , conv[]
conv-split (unbind X α ∷ χ₁) (conv-unbind v cs) with conv-split χ₁ cs
conv-split (unbind X α ∷ χ₁) (conv-unbind v cs) | Δ′ , cs₂ , cs₁ =
  Δ′ , cs₂ , conv-unbind v cs₁
conv-split (bind X α ∷ χ₁) (conv-bind v cs fr i) with conv-split χ₁ cs
conv-split (bind X α ∷ χ₁) (conv-bind v cs fr i) | Δ′ , cs₂ , cs₁ =
  Δ′ , cs₂ , conv-bind v cs₁ fr i
conv-split (bind X α ∷ χ₁) (conv-bind-live v cs d) with conv-split χ₁ cs
conv-split (bind X α ∷ χ₁) (conv-bind-live v cs d) | Δ′ , cs₂ , cs₁ =
  Δ′ , cs₂ , conv-bind-live v cs₁ d

merged-keeps₂ : ∀ {Δ Δ₂ᶜ Δ⋉ᶜ : Ctxᵗ} {Θ₁ Θ₂ : Boundary}
  → Δ ⊢ᶜ Θ₂ ⇒ Δ₂ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → names Δ₂ᶜ ⊆ᵃ names Δ⋉ᶜ
merged-keeps₂ {Θ₁ = Θ₁} (conversion cs₂) (conversion cs⋉)
  with conv-split Θ₁ cs⋉
merged-keeps₂ {Θ₁ = Θ₁} (conversion cs₂) (conversion cs⋉)
  | Δ′ , cs₂′ , cs₁ with conv-changes-functional cs₂ cs₂′
merged-keeps₂ {Θ₁ = Θ₁} (conversion cs₂) (conversion cs⋉)
  | Δ′ , cs₂′ , cs₁ | refl = conv-mono cs₁

merged-keeps₁ : ∀ {Δ Δᵢ Δ₂ᶜ Δ₁ᵢ Δ₁ᶜ Δ⋉ᶜ : Ctxᵗ} {Θ₁ Θ₂ : Boundary}
  → BoundaryWf Δ Θ₂ Δᵢ Δ₂ᶜ
  → BoundaryWf Δᵢ Θ₁ Δ₁ᵢ Δ₁ᶜ
  → Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ
  → names Δ₁ᶜ ⊆ᵃ names Δ⋉ᶜ
merged-keeps₁ mw₂ mw₁ r⋉ with merged-conversion-exists mw₂ mw₁
merged-keeps₁ mw₂ mw₁ r⋉ | Γ⋉ , r⋉′ , keep
  with conversion-functional r⋉′ r⋉
merged-keeps₁ mw₂ mw₁ r⋉ | Γ⋉ , r⋉′ , keep | refl = keep

------------------------------------------------------------------------
-- §2  Gluing two readings of one representation
------------------------------------------------------------------------

-- Two weakenings of one type `A` (read on η) denote one
-- representation.
same-glue : ∀ {η η′ η″ : TyCtx} {A A′ A″ : Ty}
  → ∃[ R ] ((η′ ⊢ A′ ~ R) × (η ⊢ A ~ R))
  → ∃[ S ] ((η″ ⊢ A″ ~ S) × (η ⊢ A ~ S))
  → ∃[ S ] ((η″ ⊢ A″ ~ S) × (η′ ⊢ A′ ~ S))
same-glue (R , p′ , p) (S , q″ , q) with same-rep-unique p q
same-glue (R , p′ , p) (S , q″ , q) | refl = R , q″ , p′

same-sym : ∀ {η η′ : TyCtx} {A A′ : Ty}
  → ∃[ R ] ((η ⊢ A ~ R) × (η′ ⊢ A′ ~ R))
  → ∃[ R ] ((η′ ⊢ A′ ~ R) × (η ⊢ A ~ R))
same-sym (R , p , q) = R , q , p

same-both : ∀ {η : TyCtx} {A B : Ty}
  → ∃[ S ] ((η ⊢ A ~ S) × (η ⊢ B ~ S))
  → ∃[ S ] ((η ⊢ A ~ S) × (η ⊢ B ~ S))
same-both p = p

------------------------------------------------------------------------
-- §3  MERGE
------------------------------------------------------------------------

-- Commentary.md § proof/MoveScope.agda / §3
preserve-Merge : MergeCase
preserve-Merge {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ₂ᶜ = Δ₂ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
               {U = U} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {t₁ = t₁} {t₁′ = t₁′}
               {c₂ = c₂} {c₂′ = c₂′} {C = C}
               wfΔ u it ri r₁ r₂ r⋉ (r₁ʳ , p⋉₁ , p₁) (r₂ʳ , p⋉₂ , p₂)
               (boundary mw₂ (boundary {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢U ⊢t₁ sm₁ se₁ wB)
                    ⊢c₂ sm₂ se₂ wE)
  with interior-functional (bw-interior mw₂) ri
     | conversion-functional (bw-conversion mw₂) r₂
preserve-Merge {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ₂ᶜ = Δ₂ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
               {U = U} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {t₁ = t₁} {t₁′ = t₁′}
               {c₂ = c₂} {c₂′ = c₂′} {C = C}
               wfΔ u it ri r₁ r₂ r⋉ (r₁ʳ , p⋉₁ , p₁) (r₂ʳ , p⋉₂ , p₂)
               (boundary mw₂ (boundary {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢U ⊢t₁ sm₁ se₁ wB)
                    ⊢c₂ sm₂ se₂ wE)
  | refl | refl
  with conversion-functional (bw-conversion mw₁) r₁
preserve-Merge {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ₂ᶜ = Δ₂ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
               {U = U} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {t₁ = t₁} {t₁′ = t₁′}
               {c₂ = c₂} {c₂′ = c₂′} {C = C}
               wfΔ u it ri r₁ r₂ r⋉ (r₁ʳ , p⋉₁ , p₁) (r₂ʳ , p⋉₂ , p₂)
               (boundary mw₂ (boundary {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢U ⊢t₁ sm₁ se₁ wB)
                    ⊢c₂ sm₂ se₂ wE)
  | refl | refl | refl
  with weaken-⊢ {Γ = Δ₁ᶜ} {Γ′ = Δ⋉ᶜ}
         (trans (conversion-reps r⋉)
                (sym (trans (conversion-reps r₁) (interior-reps ri))))
         (name-fn (bw-conversion-wf mw₁))
         (merged-keeps₁ mw₂ mw₁ r⋉) p₁ p⋉₁ ⊢t₁
     | weaken-⊢ {Γ = Δ₂ᶜ} {Γ′ = Δ⋉ᶜ}
         (trans (conversion-reps r⋉) (sym (conversion-reps r₂)))
         (name-fn (bw-conversion-wf mw₂))
         (merged-keeps₂ r₂ r⋉) p₂ p⋉₂ ⊢c₂
preserve-Merge {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ₂ᶜ = Δ₂ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
               {U = U} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {t₁ = t₁} {t₁′ = t₁′}
               {c₂ = c₂} {c₂′ = c₂′} {C = C}
               wfΔ u it ri r₁ r₂ r⋉ (r₁ʳ , p⋉₁ , p₁) (r₂ʳ , p⋉₂ , p₂)
               (boundary mw₂ (boundary {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢U ⊢t₁ sm₁ se₁ wB)
                    ⊢c₂ sm₂ se₂ wE)
  | refl | refl | refl
  | C₁′ , D₁′ , ⊢t₁′ , smC₁ , smD₁ | C₂′ , D₂′ , ⊢c₂′ , smC₂ , smD₂
  -- the middle type, weakened twice at the merged context
  with same-both (same-glue (same-sym (same-glue smD₁ se₁))
                            (same-sym (same-glue smC₂ sm₂)))
preserve-Merge {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ₂ᶜ = Δ₂ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
               {U = U} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {t₁ = t₁} {t₁′ = t₁′}
               {c₂ = c₂} {c₂′ = c₂′} {C = C}
               wfΔ u it ri r₁ r₂ r⋉ (r₁ʳ , p⋉₁ , p₁) (r₂ʳ , p⋉₂ , p₂)
               (boundary mw₂ (boundary {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢U ⊢t₁ sm₁ se₁ wB)
                    ⊢c₂ sm₂ se₂ wE)
  | refl | refl | refl
  | C₁′ , D₁′ , ⊢t₁′ , smC₁ , smD₁ | C₂′ , D₂′ , ⊢c₂′ , smC₂ , smD₂
  | S , qC , qD
  with same-target-unique (name-fn (conversion-wf wfΔ r⋉)) qC qD
preserve-Merge {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ₂ᶜ = Δ₂ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
               {U = U} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {t₁ = t₁} {t₁′ = t₁′}
               {c₂ = c₂} {c₂′ = c₂′} {C = C}
               wfΔ u it ri r₁ r₂ r⋉ (r₁ʳ , p⋉₁ , p₁) (r₂ʳ , p⋉₂ , p₂)
               (boundary mw₂ (boundary {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢U ⊢t₁ sm₁ se₁ wB)
                    ⊢c₂ sm₂ se₂ wE)
  | refl | refl | refl
  | C₁′ , D₁′ , ⊢t₁′ , smC₁ , smD₁ | C₂′ , D₂′ , ⊢c₂′ , smC₂ , smD₂
  | S , qC , qD | refl =
  boundary mw⋉ ⊢U ⊢merged sameᵢ sameₑ wE
  where
  mw⋉ : BoundaryWf Δ (Θ₁ ++ Θ₂) Δ₁ᵢ Δ⋉ᶜ
  mw⋉ = bw wfΔ (merged-interior (bw-interior mw₂) (bw-interior mw₁)) r⋉

  ⊢merged : Δ⋉ᶜ ⊢ (Δ⋉ᶜ ⊢ tail t₁′ ⨟ c₂′) ∶ C₁′ ⇝ D₂′
  ⊢merged = ⊢⨟ (name-fn (conversion-wf wfΔ r⋉)) ⊢t₁′ ⊢c₂′

  sameᵢ : Δ₁ᵢ ⊢ B₁ ≈ C₁′ ⊣ Δ⋉ᶜ
  sameᵢ = same-glue smC₁ sm₁

  sameₑ : Δ ⊢ C ≈ D₂′ ⊣ Δ⋉ᶜ
  sameₑ = same-glue smD₂ se₂
