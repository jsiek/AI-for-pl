module strong-rep-nu.proof.AddUnbind0 where

-- File Charter:
--   * THE MOVED BOUNDARY'S TYPING — `AddUnbind0Typing`, preservation's
--     last parameter.  §1 one inversion for the moved exterior
--     reading; §2 the three pieces (`moved-keep`, `moved-conv`,
--     `moved-sameᵢ`, `moved-sameₑ`); §3 the assembled `env`;
--     §4 `addUnbind0-⊢`.
--   * THE MOVE IS THE SIBLING SHIFT ON THE TERM (`renᴹᴿ suc`, because
--     the appended `unbind 0 0` acts FIRST and deletes the fresh
--     ordinary name) but NOT on the CONVERSION, because a conversion
--     reading SKIPS unbinds — which is why the rule carries the moved
--     spelling `s′` with a `SameConv` (notes/AddLock0Wall.agda).
--   * Nothing is postulated: the retention `respell-⊢` consumes is the
--     `keep` component of `snoc-unbind0-conversion-ren`.
-- Commentary: Commentary.md § proof/AddUnbind0.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product
  using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.TermSubst using (renᴹᴿ)
open import strong-rep-nu.Reduction
open import strong-rep-nu.proof.Preserve
open import strong-rep-nu.proof.RepWeaken using (⊢renᴿ)
open import strong-rep-nu.proof.PeelDual using (respell-⊢)

------------------------------------------------------------------------
-- §1  One inversion for the moved exterior reading
------------------------------------------------------------------------

-- The exterior reading of a `` `∀ `` splits, and the caller needs the
-- split BEFORE it knows the representation is a `` `∀ `` — which is why
-- this is an inversion and not a pattern match.
same-∀⁻ : ∀ {η : TyCtx} {A V : Ty} → η ⊢ `∀ A ~ V
  → Σ[ V₀ ∈ Ty ] ((V ≡ `∀ V₀) × ((zero ∷ shiftReps η) ⊢ A ~ V₀))
same-∀⁻ (same-∀ q) = _ , refl , q

------------------------------------------------------------------------
-- §2  The three pieces, each on its own premises
------------------------------------------------------------------------

-- The retention the moved conversion is re-spelled along.  `Δ⁺ᶜ` is the
-- rule's own reading, so the transport's output context is identified with
-- it by `conversion-functional`.
moved-keep : ∀ {Δ Δᶜ Δ⁺ᶜ : Ctxᵗ} {Θ : Boundary} {P : Ty}
  → WfCtx Δ
  → WfRepCtx (bindR P ∷ reps Δ)
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
      ⊢ᶜ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ [])) ⇒ Δ⁺ᶜ
  → (map suc (names Δᶜ)) ⊆ᵃ (names Δ⁺ᶜ)
moved-keep wfΔ wr rc r⁺
  with snoc-unbind0-conversion-ren (repwk-cons₀ _ (λ _ → wr)) (_ , here)
         (name-fn wfΔ) rc
moved-keep wfΔ wr rc r⁺ | Δ″ , r″ , keep
  with conversion-functional r″ r⁺
moved-keep wfΔ wr rc r⁺ | Δ″ , r″ , keep | refl = keep

-- The moved conversion's TYPING, with both of its types paired back to the
-- old ones.  Two moves, in this order: `conv-ren` changes the
-- representation context, `respell-⊢` changes the name map.
moved-conv : ∀ {Δᶜ Δ⁺ᶜ : Ctxᵗ} {ρ : Renameᵗ} {s s′ : Conv} {Cᵢ Cₑ : Ty}
  → RepWk ρ (reps Δᶜ) (reps Δ⁺ᶜ)
  → (map ρ (names Δᶜ)) ⊆ᵃ (names Δ⁺ᶜ)
  → SameConv (underΛ Δ⁺ᶜ) s′
      (underΛ (renNameCtx ρ Δ⁺ᶜ Δᶜ)) s
  → underΛ Δᶜ ⊢ s ∶ Cᵢ ⇝ Cₑ
  → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
      ((Δ⁺ᶜ ⊢ `∀ s′ ∶ `∀ A′ ⇝ `∀ B′)
        × (underΛ Δ⁺ᶜ ⊢ A′ ≈ Cᵢ ⊣
            underΛ (renNameCtx ρ Δ⁺ᶜ Δᶜ))
        × (underΛ Δ⁺ᶜ ⊢ B′ ≈ Cₑ ⊣
            underΛ (renNameCtx ρ Δ⁺ᶜ Δᶜ)))
moved-conv {Δᶜ = Δᶜ} {ρ = ρ} w keep (r , rd′ , rd) ⊢s
  with respell-⊢ refl (⊆ᵃ-underΛ keep) rd rd′
         (conv-cast (names-underΛ-ren ρ (names Δᶜ))
                    (conv-ren (repwk-abst w) ⊢s))
moved-conv w keep (r , rd′ , rd) ⊢s | A′ , B′ , ⊢s′ , smA , smB =
  A′ , B′ , conv-all ⊢s′ , smA , smB

-- and the same, on the premises the rule actually carries
moved-conv′ : ∀ {Δ Δᶜ Δ⁺ᶜ : Ctxᵗ} {Θ : Boundary} {s s′ : Conv}
  {Cᵢ Cₑ P : Ty}
  → WfCtx Δ
  → WfRepCtx (bindR P ∷ reps Δ)
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
      ⊢ᶜ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ [])) ⇒ Δ⁺ᶜ
  → SameConv (underΛ Δ⁺ᶜ) s′
      (underΛ (renNameCtx suc Δ⁺ᶜ Δᶜ)) s
  → underΛ Δᶜ ⊢ s ∶ Cᵢ ⇝ Cₑ
  → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
      ((Δ⁺ᶜ ⊢ `∀ s′ ∶ `∀ A′ ⇝ `∀ B′)
        × (underΛ Δ⁺ᶜ ⊢ A′ ≈ Cᵢ ⊣
            underΛ (renNameCtx suc Δ⁺ᶜ Δᶜ))
        × (underΛ Δ⁺ᶜ ⊢ B′ ≈ Cₑ ⊣
            underΛ (renNameCtx suc Δ⁺ᶜ Δᶜ)))
moved-conv′ {Δ = Δ} {Δᶜ = Δᶜ} {Δ⁺ᶜ = Δ⁺ᶜ} {P = P}
            wfΔ wr rc r⁺ sc ⊢s =
  moved-conv wᶜ (moved-keep wfΔ wr rc r⁺) sc ⊢s
  where
  w₀ : RepWk suc (reps Δ) (bindR P ∷ reps Δ)
  w₀ = repwk-cons₀ (bindR P) (λ _ → wr)

  wᶜ : RepWk suc (reps Δᶜ) (reps Δ⁺ᶜ)
  wᶜ = subst (λ Ξ → RepWk suc Ξ (reps Δ⁺ᶜ))
             (sym (conversion-reps rc))
             (subst (λ Ξ → RepWk suc (reps Δ) Ξ)
                    (sym (conversion-reps r⁺)) w₀)

-- The interior alignment.  The moved side is the old reading renamed; the
-- conversion side is `respell-⊢`'s, and the two representations are
-- identified because a reading determines its representation.
moved-sameᵢ : ∀ {Δᵢ Δᶜ Δ⁺ᶜ : Ctxᵗ} {Ξ : RepCtx} {ρ : Renameᵗ}
  {Bᵢ Cᵢ A′ : Ty}
  → Δᵢ ⊢ Bᵢ ≈ `∀ Cᵢ ⊣ Δᶜ
  → underΛ Δ⁺ᶜ ⊢ A′ ≈ Cᵢ ⊣
      underΛ (renNameCtx ρ Δ⁺ᶜ Δᶜ)
  → (Ξ ∣ map ρ (names Δᵢ)) ⊢ Bᵢ ≈ `∀ A′ ⊣ Δ⁺ᶜ
moved-sameᵢ {Δᶜ = Δᶜ} {ρ = ρ} (R , pᵢ , same-∀ qᵢ) (S , a , b)
  with same-rep-unique b
         (same-cast (names-underΛ-ren ρ (names Δᶜ))
                    (same-ren (extᵗ ρ) qᵢ))
moved-sameᵢ {ρ = ρ} (R , pᵢ , same-∀ qᵢ) (S , a , b) | refl =
  renameᵗ ρ R , same-ren ρ pᵢ , same-∀ a

-- The exterior alignment.  The new ordinary name weakens the exterior
-- reading, and that is all: the comparison is `≈` at equal depth, so no
-- bind-block shift has to commute with the renaming any more.
moved-sameₑ : ∀ {Δ Δᶜ Δ⁺ᶜ : Ctxᵗ} {Ξ : RepCtx} {A Cₑ B′ : Ty}
  → Δ ⊢ `∀ A ≈ `∀ Cₑ ⊣ Δᶜ
  → underΛ Δ⁺ᶜ ⊢ B′ ≈ Cₑ ⊣
      underΛ (renNameCtx suc Δ⁺ᶜ Δᶜ)
  → (Ξ ∣ (zero ∷ shiftReps (names Δ)))
      ⊢ `∀ (renameᵗ (extᵗ suc) A) ≈ `∀ B′ ⊣ Δ⁺ᶜ
moved-sameₑ {Δᶜ = Δᶜ} (T , pₑ , qₑ) (S , a , b)
  with same-∀⁻ qₑ
moved-sameₑ {Δᶜ = Δᶜ} (T , pₑ , qₑ) (S , a , b) | V₀ , refl , q₀
  with same-rep-unique b
         (same-cast (names-underΛ-ren suc (names Δᶜ))
                    (same-ren (extᵗ suc) q₀))
moved-sameₑ (T , pₑ , qₑ) (S , a , b) | V₀ , refl , q₀ | refl =
  `∀ (renameᵗ (extᵗ suc) V₀) , same-weaken pₑ , same-∀ a

------------------------------------------------------------------------
-- §3  The assembled `env`
------------------------------------------------------------------------

moved-env : ∀ {Δ Δᵢ Δᶜ Δ⁺ᶜ : Ctxᵗ} {W : Term} {Θ : Boundary}
  {s s′ : Conv} {A P Bᵢ Cᵢ Cₑ : Ty}
  → WfCtx ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
  → BoundaryWf Δ Θ Δᵢ Δᶜ
  → Δᵢ ∣ [] ⊢ W ⦂ Bᵢ
  → underΛ Δᶜ ⊢ s ∶ Cᵢ ⇝ Cₑ
  → Δᵢ ⊢ Bᵢ ≈ `∀ Cᵢ ⊣ Δᶜ
  → Δ ⊢ `∀ A ≈ `∀ Cₑ ⊣ Δᶜ
  → Δ ⊢ᵗ `∀ A
  → Δ ⊢ᶜ Θ ⇒ Δᶜ
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ)))
      ⊢ᶜ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ [])) ⇒ Δ⁺ᶜ
  → SameConv (underΛ Δ⁺ᶜ) s′
      (underΛ (renNameCtx suc Δ⁺ᶜ Δᶜ)) s
  → ((bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ))) ∣ [] ⊢
      (renᴹᴿ suc W ⟪ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ [])) , `∀ s′ ⟫)
      ⦂ `∀ (renameᵗ (extᵗ suc) A)
moved-env wf⁺ mwΘ ⊢W ⊢s sameᵢ sameₑ wE rc r⁺ sc
  with moved-conv′ (bw-exterior mwΘ) (wf-reps wf⁺) rc r⁺ sc ⊢s
moved-env {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δ⁺ᶜ = Δ⁺ᶜ} {W = W} {Θ = Θ}
          {A = A} {P = P} {Bᵢ = Bᵢ}
  wf⁺ mwΘ ⊢W ⊢s sameᵢ sameₑ wE rc r⁺ sc
  | A′ , B′ , ⊢c⁺ , smA , smB =
  env mw⁺ ⊢W⁺ ⊢c⁺ smᵢ smₑ wE⁺
  where
  Δ⁺ : Ctxᵗ
  Δ⁺ = (bindR P ∷ reps Δ) ∣ (zero ∷ shiftReps (names Δ))

  Δᵢ⁺ : Ctxᵗ
  Δᵢ⁺ = (bindR P ∷ reps Δ) ∣ map suc (names Δᵢ)

  w₀ : RepWk suc (reps Δ) (bindR P ∷ reps Δ)
  w₀ = repwk-cons₀ (bindR P) (λ _ → wf-reps wf⁺)

  wᵢ : RepWk suc (reps Δᵢ) (bindR P ∷ reps Δ)
  wᵢ = subst (λ Ξ → RepWk suc Ξ (bindR P ∷ reps Δ))
             (sym (interior-reps (bw-interior mwΘ))) w₀

  mw⁺ : BoundaryWf Δ⁺ (renᴮᴿ suc Θ ++ (unbind 0 0 ∷ [])) Δᵢ⁺ Δ⁺ᶜ
  mw⁺ = bw wf⁺
           (snoc-unbind0-interior-ren w₀ (_ , here) (bw-interior mwΘ))
           r⁺

  ⊢W⁺ : Δᵢ⁺ ∣ [] ⊢ renᴹᴿ suc W ⦂ Bᵢ
  ⊢W⁺ = ⊢renᴿ wᵢ ⊢W

  smᵢ : Δᵢ⁺ ⊢ Bᵢ ≈ `∀ A′ ⊣ Δ⁺ᶜ
  smᵢ = moved-sameᵢ {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δ⁺ᶜ = Δ⁺ᶜ}
                    {Ξ = bindR P ∷ reps Δ} {ρ = suc} sameᵢ smA

  smₑ : Δ⁺ ⊢ `∀ (renameᵗ (extᵗ suc) A) ≈ `∀ B′ ⊣ Δ⁺ᶜ
  smₑ = moved-sameₑ {Δ = Δ} {Δᶜ = Δᶜ} {Δ⁺ᶜ = Δ⁺ᶜ}
                    {Ξ = bindR P ∷ reps Δ} sameₑ smB

  wk⁺ : WfRen Δ Δ⁺ suc
  wk⁺ (α , d) = suc α , there (shiftReps-∋ d)

  wE⁺ : Δ⁺ ⊢ᵗ `∀ (renameᵗ (extᵗ suc) A)
  wE⁺ = wf-ren wk⁺ wE

------------------------------------------------------------------------
-- §4  The theorem
------------------------------------------------------------------------

addUnbind0-⊢ : AddUnbind0Typing
addUnbind0-⊢ wf⁺ (env mwΘ ⊢W ⊢c sameᵢ sameₑ wE) rc r⁺ sc
  with conversion-functional (bw-conversion mwΘ) rc
addUnbind0-⊢ wf⁺ (env mwΘ ⊢W ⊢c sameᵢ sameₑ wE) rc r⁺ sc | refl
  with conv-all-inv ⊢c
addUnbind0-⊢ wf⁺ (env mwΘ ⊢W ⊢c sameᵢ sameₑ wE) rc r⁺ sc
  | refl | Cᵢ , Cₑ , refl , refl , ⊢s =
  moved-env wf⁺ mwΘ ⊢W ⊢s sameᵢ sameₑ wE rc r⁺ sc
