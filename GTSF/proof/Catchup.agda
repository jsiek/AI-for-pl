{-# OPTIONS --allow-unsolved-metas --allow-incomplete-matches #-}

module proof.Catchup where

-- File Charter:
--   * Home for the GTSF catchup lemma used by the dynamic gradual guarantee.
--   * Uses `proof.CatchupStore` for the stable store-narrowing append helper
--     `combineStoreNrw` and its source-store algebra.
--   * The intended proof follows the cambridge25 "Catchup Lemma" section.
--   * The main statement is the strengthened Agda form needed by DGG: closed
--     source relation, an explicit source value after catchup, and de Bruijn
--     weakening of the unchanged target term/coercion index by the emitted
--     store changes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import Store using (StoreIncl; StoreIncl-cons; StoreIncl-drop)
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import Primitives using (κℕ; constTy)
open import proof.NarrowWidenProperties
  using
    ( StoreDetWf
    ; StoreDetWf-⟰ᵗ
    ; WfTyˢ-⇑ᵗ
    ; WfTyˢ-store-weaken
    ; narrowing-determinedᵐ
    ; narrow-⇑ᵗ-ᶜ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤
    ; narrow-⇑ᵗ-any
    ; narrow-drop-star-var
    ; narrow-drop-star
    ; srcStoreⁿ-⊒ˢ
    ; srcStoreⁿ-⇑ˢ
    ; ⇑ˢ-++
    ; ⊒ˢ-⇑ˢ
    ; ⊒ˢ-empty-⇑ˢ
    ; ⊒ˢ-empty-anyᵗ
    )
open import proof.CoercionProperties
  using
    ( coercion-src-tgtᵐ
    ; renameᶜ-left-inverse
    ; src-renameᶜ
    ; tgt-renameᶜ
    )
open import proof.NuTermProperties
  using
    ( renameᵗᵐ-left-inverse
    ; renameᵗᵐ-preserves-No•
    ; renameᵗᵐ-preserves-Value
    )
open import proof.NuPreservation
  using
    ( runtime-⟨⟩
    ; runtime-ν
    ; value-runtime-No•
    )
open import proof.ReductionProperties
  using
    ( applyCoercions
    ; applyCoercions-empty-id
    ; applyCoercions-++
    ; applyCoercions-⇑ᶜ
    ; applyCoercions-dual
    ; applyCoercions-last-bind
    ; applyCoercions-last-bind-open
    ; applyCoercions-open
    ; applyCoercions-∀
    ; applyCoercions-gen
    ; applyCoercions-inst
    ; applyCoercionUnderTyBinders
    ; applyCoercionUnderTyBinders-preserves-Inert
    ; applyStores-empty-id
    ; applyStores-last-bind
    ; applyTerms-++
    ; applyTerms-empty-id
    ; applyTerms-last-bind-open
    ; applyTerms-open
    ; applyTerms-Λ
    ; applyTerms-ν
    ; applyTerms-•
    ; applyTerms-cast
    ; applyTerms-cast-dual
    ; applyTermsUnderTyBinders
    ; applyTyVars
    ; applyTyCtxs-empty-id
    ; applyTyCtxs-last-bind
    ; applyTyCtxs-suc
    ; applyTys-empty-id
    ; applyTys-⇑ᵗ
    ; applyTys-∀
    ; applyTysUnderTyBinders
    ; applyTys-last-bind
    ; applyTys-★
    ; allKeep-applyStores-id
    ; applyStores-++
    ; ⟰ᵗ-empty-inv
    ; applyTyCtxs-++
    ; storeHead-∷≡
    ; storeTail-∷≡
    ; storeChangesLastBind
    ; StoreChangesLastBind
    ; no-bind
    ; last-bind
    ; applyTyCtxs-≤
    ; ↠-trans
    ; cast-↠
    ; cast-dual-↠
    ; applyCoercionUnderTyBinders-⇑ᶜ
    ; ν-↠
    ; shiftStore
    ; shiftStore-empty
    ; shiftStore-empty-inv
    ; shiftStore-cons
    ; shiftStore-⟰ᵗ
    )
open import proof.CatchupStore
  using
    ( combineStoreNrw
    ; combineStoreNrw-⇑ˢ
    ; combineStoreNrw-assoc
    ; combineStoreNrw-empty-⊒ˢ
    ; combineStoreNrw-applyStores
    ; combineStoreNrw-applyStores-store
    )

runtime-⇑ᵗᵐ :
  ∀ {M} →
  RuntimeOK M →
  RuntimeOK (⇑ᵗᵐ M)
runtime-⇑ᵗᵐ (ok-no noM) =
  ok-no (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-• vV noV) =
  ok-• (renameᵗᵐ-preserves-Value suc vV)
       (renameᵗᵐ-preserves-No• suc noV)
runtime-⇑ᵗᵐ (ok-·₁ okL noM) =
  ok-·₁ (runtime-⇑ᵗᵐ okL) (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-·₂ vV noV okM) =
  ok-·₂ (renameᵗᵐ-preserves-Value suc vV)
        (renameᵗᵐ-preserves-No• suc noV)
        (runtime-⇑ᵗᵐ okM)
runtime-⇑ᵗᵐ (ok-ν okL) = ok-ν (runtime-⇑ᵗᵐ okL)
runtime-⇑ᵗᵐ (ok-⊕₁ okL noM) =
  ok-⊕₁ (runtime-⇑ᵗᵐ okL) (renameᵗᵐ-preserves-No• suc noM)
runtime-⇑ᵗᵐ (ok-⊕₂ vL noL okM) =
  ok-⊕₂ (renameᵗᵐ-preserves-Value suc vL)
        (renameᵗᵐ-preserves-No• suc noL)
        (runtime-⇑ᵗᵐ okM)
runtime-⇑ᵗᵐ (ok-⟨⟩ okM) = ok-⟨⟩ (runtime-⇑ᵗᵐ okM)

postulate
  -- `split` changes which fresh type variable the source term is opened at.
  -- This should follow from `RuntimeOK` depending on the term/bullet shape
  -- rather than the particular type-variable names in casts and annotations.
  runtime-open-change :
    ∀ {N α β} →
    RuntimeOK (N [ α ]ᵀ) →
    RuntimeOK (N [ β ]ᵀ)

------------------------------------------------------------------------
-- Catchup
------------------------------------------------------------------------

-- Postulate audit:
-- * `left-widening-lemma` and `left-narrowing-lemma` correspond to named
--   cambridge25 lemmas.  The Agda statements add the emitted-store bookkeeping
--   (`χs`, `π`, and `combineStoreNrw`) needed by this mechanization.
-- * The other postulates in this file are not pre-existing named cambridge25
--   lemmas.  They are newly documented proof obligations/cases in
--   `cambridge25.lagda.md`, marked with `[New]`, and remain to be proved.

postulate
  -- cambridge25 "Left Widening Lemma": the source before the left cast is
  -- already a value.  The catchup induction that produces that value remains
  -- in `catchup-lemma`.  The Δ′ equality is Agda bookkeeping for the emitted
  -- store-change sequence.
  left-widening-lemma :
    ∀ {Δ σ V V′ p r t A B C D E Σ μ} →
    Value V →
    No• V →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    (wfΣ : StoreDetWf Δ Σ) →
    (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ E) →
    (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ E ⊒ B) →
    Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p ⦂ C ⊒ D →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
      No• W ×
      (V ⟨ - t ⟩ —↠[ χs ] W) ×
      (Δ′ ≡ applyTyCtxs χs Δ) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r
          ⦂ applyTys χs A ⊒ applyTys χs B

  -- cambridge25 "Left Narrowing Lemma", likewise value-level, with the same
  -- emitted-context bookkeeping.
  left-narrowing-lemma :
    ∀ {Δ σ V V′ p r t A B C D E Σ μ} →
    Value V →
    No• V →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    (wfΣ : StoreDetWf Δ Σ) →
    (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ E) →
    (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ E ⊒ B) →
    Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ r ⦂ A ⊒ B →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
      No• W ×
      (V ⟨ t ⟩ —↠[ χs ] W) ×
      (Δ′ ≡ applyTyCtxs χs Δ) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p
          ⦂ applyTys χs C ⊒ applyTys χs D

  -- [New] Shifted-source catchup inversion for the `⊒Λ` case.
  --
  -- Attempted proof notes.  A direct recursive call in the `⊒Λ` case catches
  -- up the shifted source `⇑ᵗᵐ N` under `(zero ꞉= ★ ⊒) ∷ ⇑ˢ σ`,
  -- but the final catchup conclusion needs an unshifted reduction from `N`
  -- under `σ`.  The useful next invariant is a reduction/store-prefix
  -- inversion lemma: peel the fresh source-only star entry from the emitted
  -- store changes, invert type-renamed source reductions, and rewrite target
  -- terms/coercions with the under-binder `applyTerms`/`applyCoercions`
  -- lemmas before rebuilding `⊒Λ`.
  shifted-source-catchup-Λ-inversion :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V′ p A B} →
    Value W →
    (⇑ᵗᵐ N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p
        ⦂ applyTys χs (⇑ᵗ A) ⊒ applyTys χs B →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (N —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      suc Δ″ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ) ∣ []
        ⊢ ⇑ᵗᵐ W′ ⊒ applyTermsUnderTyBinders χs′ V′
          ∶ applyCoercionUnderTyBinders χs′ p
            ⦂ ⇑ᵗ (applyTys χs′ A) ⊒ applyTysUnderTyBinders χs′ B

  -- [New] Same shifted-source catchup inversion for the `⊒⟨ν⟩` wrapper,
  -- where the target value remains outside the generated cast in the final
  -- result.
  -- The proof should share the same inversion lemma as `⊒Λ`; only the final
  -- rebuild differs, using `⊒⟨ν⟩` and inertness preservation for the
  -- under-binder coercion action.
  shifted-source-catchup-⟨ν⟩-inversion :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V′ p s A B} →
    Value W →
    (⇑ᵗᵐ N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (V′ ⟨ s ⟩) ∶ applyCoercions χs p
        ⦂ applyTys χs (⇑ᵗ A) ⊒ applyTys χs B →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (N —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      suc Δ″ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ) ∣ []
        ⊢ ⇑ᵗᵐ W′
          ⊒ applyTerms χs′ V′ ⟨ applyCoercionUnderTyBinders χs′ s ⟩
          ∶ applyCoercionUnderTyBinders χs′ p
            ⦂ ⇑ᵗ (applyTys χs′ A) ⊒ applyTysUnderTyBinders χs′ B

-- A mode-polymorphic version of this transport was tried first, but the final
-- catchup proof only needs coercions in `tag-or-idᵈ`; keeping the generic mode
-- action obscured the actual side condition.
gen-tag-or-id≤tag-or-id :
  ModeIncl (genᵈ tag-or-idᵈ) tag-or-idᵈ
gen-tag-or-id≤tag-or-id zero = refl
gen-tag-or-id≤tag-or-id (suc X) = refl

applyCoercion-narrow :
  ∀ χ {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ᶜ A ⊒ B →
  applyTyCtx χ Δ ∣ applyStore χ Σ
    ⊢ applyCoercion χ c ∶ᶜ applyTy χ A ⊒ applyTy χ B
applyCoercion-narrow keep c⊒ = c⊒
applyCoercion-narrow (bind Aν) c⊒ =
  narrow-mode-relax gen-tag-or-id≤tag-or-id
    (narrow-weaken ≤-refl StoreIncl-drop (narrow-⇑ᵗ-gen c⊒))

applyCoercions-narrow :
  ∀ χs {Δ Σ c A B} →
  Δ ∣ Σ ⊢ c ∶ᶜ A ⊒ B →
  applyTyCtxs χs Δ ∣ applyStores χs Σ
    ⊢ applyCoercions χs c ∶ᶜ applyTys χs A ⊒ applyTys χs B
applyCoercions-narrow [] c⊒ = c⊒
applyCoercions-narrow (χ ∷ χs) c⊒ =
  applyCoercions-narrow χs (applyCoercion-narrow χ c⊒)

catchup-coercion-typing-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
    ⊢ applyCoercions χs p ∶ᶜ applyTys χs A ⊒ applyTys χs B
catchup-coercion-typing-transport {Δ = Δ} {σ = σ} {π = π}
    {χs = χs} {p = p} {A = A} {B = B} pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  subst
    (λ Δ₀ → Δ₀ ∣ srcStoreⁿ (combineStoreNrw π σ)
      ⊢ applyCoercions χs p ∶ᶜ applyTys χs A ⊒ applyTys χs B)
    (sym Δ′≡)
    (subst
      (λ Σ → applyTyCtxs χs Δ ∣ Σ
        ⊢ applyCoercions χs p ∶ᶜ applyTys χs A ⊒ applyTys χs B)
      (sym
        (combineStoreNrw-applyStores-store
          {χs = χs} π⊒ Π≡ Π′≡ σ))
      (applyCoercions-narrow χs pᶜ))

catchup-gen-coercion-typing-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs p A B} →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
    ⊢ gen (applyTys χs A) (applyCoercionUnderTyBinders χs p)
      ∶ᶜ applyTys χs A ⊒ `∀ (applyTysUnderTyBinders χs B)
catchup-gen-coercion-typing-transport {Δ′ = Δ′} {σ = σ} {π = π}
    {χs = χs} {p = p} {A = A} {B = B} pᶜ Δ′≡ Π≡ Π′≡ π⊒ =
  subst
    (λ B₀ → Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
      ⊢ gen (applyTys χs A) (applyCoercionUnderTyBinders χs p)
        ∶ᶜ applyTys χs A ⊒ B₀)
    (applyTys-∀ χs B)
    (subst
      (λ p₀ → Δ′ ∣ srcStoreⁿ (combineStoreNrw π σ)
        ⊢ p₀ ∶ᶜ applyTys χs A ⊒ applyTys χs (`∀ B))
      (applyCoercions-gen χs A p)
      (catchup-coercion-typing-transport
        {σ = σ} {π = π} {χs = χs} {p = gen A p}
        {A = A} {B = `∀ B}
        pᶜ Δ′≡ Π≡ Π′≡ π⊒))

≈ⁿ-⇑ˢ :
  ∀ {Δ σ s t A B} →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ s ≈ ⇑ᶜ t ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
≈ⁿ-⇑ˢ (endpointsⁿ {s = s} {t = t}
    srcs tgts srct tgtt σ⊒ (hA , hB) (hA′ , hB′) s⊒ t⊒) =
  endpointsⁿ
    (trans (src-renameᶜ suc s) (cong ⇑ᵗ srcs))
    (trans (tgt-renameᶜ suc s) (cong ⇑ᵗ tgts))
    (trans (src-renameᶜ suc t) (cong ⇑ᵗ srct))
    (trans (tgt-renameᶜ suc t) (cong ⇑ᵗ tgtt))
    (⊒ˢ-⇑ˢ σ⊒)
    (WfTyˢ-⇑ᵗ hA , WfTyˢ-⇑ᵗ hB)
    (WfTyˢ-⇑ᵗ hA′ , WfTyˢ-⇑ᵗ hB′)
    (narrow-⇑ᵗ-any s⊒)
    (narrow-⇑ᵗ-any t⊒)

≈ⁿ-add-left-star-var :
  ∀ X {Δ σ s t A B} →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ (⊒ X ꞉=☆) ∷ σ ⊢ s ≈ t ∶ A ⊒ B
≈ⁿ-add-left-star-var X (endpointsⁿ {t = t}
    srcs tgts srct tgtt σ⊒ (hA , hB) (hA′ , hB′) s⊒ t⊒) =
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (⊒ˢ-left σ⊒)
    (hA , hB)
    ( WfTyˢ-store-weaken StoreIncl-drop hA′
    , WfTyˢ-store-weaken StoreIncl-drop hB′
    )
    s⊒
    (narrow-drop-star-var X t⊒)

data ExtendReplaceRel : TyCtx → StoreNrw → StoreNrw → Set where
  replace-here :
    ∀ {Δ α q A B σ} →
    Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
    ExtendReplaceRel Δ ((α ꞉= A ⊒) ∷ σ) ((α ꞉ q) ∷ σ)

  replace-right :
    ∀ {Δ X A σ σ′} →
    ExtendReplaceRel Δ σ σ′ →
    ExtendReplaceRel Δ ((X ꞉= A ⊒) ∷ σ) ((X ꞉= A ⊒) ∷ σ′)

  replace-left :
    ∀ {Δ X σ σ′} →
    ExtendReplaceRel Δ σ σ′ →
    ExtendReplaceRel Δ ((⊒ X ꞉=☆) ∷ σ) ((⊒ X ꞉=☆) ∷ σ′)

  replace-both :
    ∀ {Δ X q σ σ′} →
    ExtendReplaceRel Δ σ σ′ →
    ExtendReplaceRel Δ ((X ꞉ q) ∷ σ) ((X ꞉ q) ∷ σ′)

extendReplaceRel-⇑ˢ :
  ∀ {Δ σ σ′} →
  ExtendReplaceRel Δ σ σ′ →
  ExtendReplaceRel (suc Δ) (⇑ˢ σ) (⇑ˢ σ′)
extendReplaceRel-⇑ˢ (replace-here {σ = σ} qᶜ) =
  replace-here (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} qᶜ)
extendReplaceRel-⇑ˢ (replace-right rel) =
  replace-right (extendReplaceRel-⇑ˢ rel)
extendReplaceRel-⇑ˢ (replace-left rel) =
  replace-left (extendReplaceRel-⇑ˢ rel)
extendReplaceRel-⇑ˢ (replace-both rel) =
  replace-both (extendReplaceRel-⇑ˢ rel)

extendReplaceRel-src-incl :
  ∀ {Δ σ σ′} →
  ExtendReplaceRel Δ σ σ′ →
  StoreIncl (srcStoreⁿ σ) (srcStoreⁿ σ′)
extendReplaceRel-src-incl (replace-here qᶜ) = StoreIncl-drop
extendReplaceRel-src-incl (replace-right rel) =
  extendReplaceRel-src-incl rel
extendReplaceRel-src-incl (replace-left rel) =
  StoreIncl-cons (extendReplaceRel-src-incl rel)
extendReplaceRel-src-incl (replace-both rel) =
  StoreIncl-cons (extendReplaceRel-src-incl rel)

storeIncl-substˡ :
  ∀ {Σ Σ₀ Σ′} →
  Σ ≡ Σ₀ →
  StoreIncl Σ₀ Σ′ →
  StoreIncl Σ Σ′
storeIncl-substˡ refl incl = incl

narrow-weaken-store :
  ∀ {Δ Σ Σ′ c A B} →
  StoreIncl Σ Σ′ →
  Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  Δ ∣ Σ′ ⊢ c ∶ A ⊒ B
narrow-weaken-store incl (μ , c⊒) = μ , narrow-weaken ≤-refl incl c⊒

open-shiftᵐ :
  ∀ α M →
  (⇑ᵗᵐ M) [ α ]ᵀ ≡ M
open-shiftᵐ α M = renameᵗᵐ-left-inverse (λ X → refl) M

open-shiftᶜ :
  ∀ α c →
  (⇑ᶜ c) [ α ]ᶜ ≡ c
open-shiftᶜ α c = renameᶜ-left-inverse (λ X → refl) c

extendReplaceRel-⊒ˢ :
  ∀ {Δ σ σ′ Σ Σ′} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ⊢ σ ꞉ Σ ⊒ˢ Σ′ →
  Δ ⊢ σ′ ꞉ srcStoreⁿ σ′ ⊒ˢ Σ′
extendReplaceRel-⊒ˢ (replace-here {q = q} {A = A} qᶜ)
    (⊒ˢ-right hA σ⊒) =
  let
    srcq≡ = proj₁ (coercion-src-tgtᵐ (proj₁ qᶜ))
    qᶜ′ =
      subst
        (λ S → tag-or-idᵈ ∣ _ ∣ _ ⊢ q ∶ S ⊒ A)
        (sym srcq≡)
        qᶜ
    hsrcq = subst (λ S → WfTy _ S) (sym srcq≡) (narrow-src-wf qᶜ)
  in
  ⊒ˢ-both hsrcq hA (tag-or-idᵈ , qᶜ′)
    (subst (λ Σ₀ → _ ⊢ _ ꞉ Σ₀ ⊒ˢ _) (srcStoreⁿ-⊒ˢ σ⊒) σ⊒)
extendReplaceRel-⊒ˢ (replace-right rel) (⊒ˢ-right hA σ⊒) =
  ⊒ˢ-right hA (extendReplaceRel-⊒ˢ rel σ⊒)
extendReplaceRel-⊒ˢ (replace-left rel) (⊒ˢ-left σ⊒) =
  ⊒ˢ-left (extendReplaceRel-⊒ˢ rel σ⊒)
extendReplaceRel-⊒ˢ (replace-both {q = q} rel)
    (⊒ˢ-both hA hA′ s⊒ σ⊒) =
  let
    incl =
      storeIncl-substˡ (srcStoreⁿ-⊒ˢ σ⊒)
        (extendReplaceRel-src-incl rel)
    srcq≡ = proj₁ (coercion-src-tgtᵐ (proj₁ (proj₂ s⊒)))
    s⊒′ =
      subst
        (λ S → _ ∣ _ ⊢ q ∶ S ⊒ _)
        (sym srcq≡)
        (narrow-weaken-store incl s⊒)
    hsrcq = subst (λ S → WfTy _ S) (sym srcq≡) hA
  in
  ⊒ˢ-both hsrcq hA′ s⊒′ (extendReplaceRel-⊒ˢ rel σ⊒)

extendReplaceRel-≈ⁿ :
  ∀ {Δ σ σ′ s t A B} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ s ≈ t ∶ A ⊒ B
extendReplaceRel-≈ⁿ rel
    (endpointsⁿ srcs tgts srct tgtt σ⊒ wfΣ wfΣ′ s⊒ t⊒) =
  let
    incl =
      storeIncl-substˡ (srcStoreⁿ-⊒ˢ σ⊒)
        (extendReplaceRel-src-incl rel)
  in
  endpointsⁿ
    srcs
    tgts
    srct
    tgtt
    (extendReplaceRel-⊒ˢ rel σ⊒)
    wfΣ
    ( WfTyˢ-store-weaken incl (proj₁ wfΣ′)
    , WfTyˢ-store-weaken incl (proj₂ wfΣ′)
    )
    s⊒
    (narrow-weaken-store incl t⊒)

extendReplaceRel-coercionᶜ :
  ∀ {Δ σ σ′ c A B} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ c ∶ᶜ A ⊒ B →
  Δ ∣ srcStoreⁿ σ′ ⊢ c ∶ᶜ A ⊒ B
extendReplaceRel-coercionᶜ rel cᶜ =
  narrow-weaken ≤-refl (extendReplaceRel-src-incl rel) cᶜ

extendReplaceRel-fun-domain-dualᶜ :
  ∀ {Δ σ σ′ p q A A′ B B′} →
  (rel : ExtendReplaceRel Δ σ σ′) →
  (p↦qᶜ : Δ ∣ srcStoreⁿ σ ⊢ p ↦ q ∶ᶜ (A ⇒ B) ⊒ (A′ ⇒ B′)) →
  fun-narrow-domain-dualᶜ (extendReplaceRel-coercionᶜ rel p↦qᶜ) ≡
    fun-narrow-domain-dualᶜ p↦qᶜ
extendReplaceRel-fun-domain-dualᶜ rel
    (cast-fun p⊢ q⊢ , cross (pʷ ↦ qⁿ)) =
  refl

extendReplaceRel-coercion :
  ∀ {Δ σ σ′ μ c A B} →
  ExtendReplaceRel Δ σ σ′ →
  μ ∣ Δ ∣ srcStoreⁿ σ ⊢ c ∶ A ⊒ B →
  μ ∣ Δ ∣ srcStoreⁿ σ′ ⊢ c ∶ A ⊒ B
extendReplaceRel-coercion rel c⊒ =
  narrow-weaken ≤-refl (extendReplaceRel-src-incl rel) c⊒

extendReplaceRel-compose-left :
  ∀ {Δ σ σ′ q s r A B C Σ μ} →
  ExtendReplaceRel Δ σ σ′ →
  (wfΣ : StoreDetWf Δ Σ) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C) →
  (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B) →
  Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B
extendReplaceRel-compose-left rel wfΣ q⊒ s⊒ q⨟s≈r =
  extendReplaceRel-≈ⁿ rel q⨟s≈r

extendReplaceRel-compose-right :
  ∀ {Δ σ σ′ r t p A B C Σ μ} →
  ExtendReplaceRel Δ σ σ′ →
  (wfΣ : StoreDetWf Δ Σ) →
  (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ C) →
  (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ C ⊒ B) →
  Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B →
  Δ ∣ σ′ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B
extendReplaceRel-compose-right rel wfΣ t⊒ p⊒ r≈t⨟p =
  extendReplaceRel-≈ⁿ rel r≈t⨟p

id-constᶜ :
  ∀ {Δ Σ} κ →
  Δ ∣ Σ ⊢ id (constTy κ) ∶ᶜ constTy κ ⊒ constTy κ
id-constᶜ (κℕ n) = cast-id wfBase refl , cross (id-‵ `ℕ)

id-ℕᶜ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ⊢ id (‵ `ℕ) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ
id-ℕᶜ = cast-id wfBase refl , cross (id-‵ `ℕ)

value-•-impossible :
  ∀ {M} →
  Value (M •) →
  ⊥
value-•-impossible ()

extend-replace-here-typed-term :
  ∀ {Δ α q A B σ γ M T c C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ c ∶ᶜ C ⊒ D →
  Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c ⦂ C ⊒ D →
  Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c ⦂ C ⊒ D
extend-replace-here-typed-term {α = α} {q = q} {A = A} {σ = σ}
    {γ = γ} {M = M} {T = T} {c = c} {C = C} {D = D}
    qᶜ cᶜ M⊒T =
  let
    T≡ = open-shiftᵐ α T
    c≡ = open-shiftᶜ α c
    cᶜ′ =
      subst
        (λ c₀ → _ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ)
          ⊢ c₀ ∶ᶜ C ⊒ D)
        (sym c≡)
        cᶜ
    premise =
      subst
        (λ c₀ → _ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
          ⊢ M ⊒ (⇑ᵗᵐ T) [ α ]ᵀ ∶ c₀ ⦂ C ⊒ D)
        (sym c≡)
        (subst
          (λ T₀ → _ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ
            ⊢ M ⊒ T₀ ∶ c ⦂ C ⊒ D)
          (sym T≡)
          M⊒T)
    rebuilt = extendᵗ qᶜ cᶜ′ premise
  in
  subst
    (λ T₀ → _ ∣ (α ꞉ q) ∷ σ ∣ γ
      ⊢ M ⊒ T₀ ∶ c ⦂ C ⊒ D)
    T≡
    (subst
      (λ c₀ → _ ∣ (α ꞉ q) ∷ σ ∣ γ
        ⊢ M ⊒ (⇑ᵗᵐ T) [ α ]ᵀ ∶ c₀ ⦂ C ⊒ D)
      c≡
      rebuilt)

extend-replace-here-typed-current :
  ∀ {Δ α q A B σ γ M T c C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ σ) ⊢ c ∶ᶜ C ⊒ D →
  Δ ∣ (α ꞉= A ⊒) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c ⦂ C ⊒ D →
  Δ ∣ (α ꞉ q) ∷ σ ∣ γ ⊢ M ⊒ T ∶ c ⦂ C ⊒ D
extend-replace-here-typed-current qᶜ cᶜ =
  extend-replace-here-typed-term qᶜ
    (narrow-weaken ≤-refl StoreIncl-drop cᶜ)

extendReplaceRel-typed-term :
  ∀ {Δ σ σ′ γ M T c A B} →
  ExtendReplaceRel Δ σ σ′ →
  Δ ∣ σ ∣ γ ⊢ M ⊒ T ∶ c ⦂ A ⊒ B →
  Δ ∣ σ′ ∣ γ ⊢ M ⊒ T ∶ c ⦂ A ⊒ B
extendReplaceRel-typed-term (replace-here qᶜ)
    M⊒T@(splitᵗ _ pαᶜ _) =
  extend-replace-here-typed-current qᶜ pαᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(⊒blameᵗ pᶜ) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(x⊒xᵗ pᶜ _) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(ƛ⊒ƛᵗ p↦qᶜ _) =
  extend-replace-here-typed-current qᶜ p↦qᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(·⊒·ᵗ p↦qᶜ _ _) =
  extend-replace-here-typed-current qᶜ (fun-narrow-codomainᶜ p↦qᶜ) M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(Λ⊒Λᵗ allᶜ _ _) =
  extend-replace-here-typed-current qᶜ allᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(⊒Λᵗ pᶜ _) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(⊒⟨ν⟩ᵗ pᶜ _ _) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(⊒αᵗ _ pαᶜ _) =
  extend-replace-here-typed-current qᶜ pαᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(ν⊒νᵗ pᶜ _ _) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(⊒νᵗ pᶜ _) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(ν⊒ᵗ pᶜ _) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(κ⊒κᵗ κ) =
  extend-replace-here-typed-current qᶜ (id-constᶜ κ) M⊒T
extendReplaceRel-typed-term (replace-here qᶜ) M⊒T@(⊕⊒⊕ᵗ _ _) =
  extend-replace-here-typed-current qᶜ id-ℕᶜ M⊒T
extendReplaceRel-typed-term (replace-here qᶜ)
    M⊒T@(⊒cast+ᵗ q₀ᶜ _ _ _ _ _) =
  extend-replace-here-typed-current qᶜ q₀ᶜ M⊒T
extendReplaceRel-typed-term rel@(replace-here qᶜ)
    (⊒cast-ᵗ q₀ᶜ r⊒ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  ⊒cast-ᵗ
    (extendReplaceRel-coercionᶜ rel q₀ᶜ)
    (extendReplaceRel-coercion rel r⊒)
    wfΣ q⊒ s⊒
    (extendReplaceRel-compose-left rel wfΣ q⊒ s⊒ q⨟s≈r)
    (extend-replace-here-typed-current qᶜ q₀ᶜ M⊒M′)
extendReplaceRel-typed-term rel@(replace-here qᶜ)
    (cast+⊒ᵗ pᶜ r⊒ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  cast+⊒ᵗ
    (extendReplaceRel-coercionᶜ rel pᶜ)
    (extendReplaceRel-coercion rel r⊒)
    wfΣ t⊒ p⊒
    (extendReplaceRel-compose-right rel wfΣ t⊒ p⊒ r≈t⨟p)
    (extend-replace-here-typed-current qᶜ pᶜ M⊒M′)
extendReplaceRel-typed-term (replace-here qᶜ)
    M⊒T@(cast-⊒ᵗ pᶜ _ _ _ _ _) =
  extend-replace-here-typed-current qᶜ pᶜ M⊒T
extendReplaceRel-typed-term (replace-right rel) M⊒T = {!!}
extendReplaceRel-typed-term (replace-left rel) (⊒blameᵗ pᶜ) =
  ⊒blameᵗ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
extendReplaceRel-typed-term (replace-left rel) (x⊒xᵗ pᶜ x∋p) =
  x⊒xᵗ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ) x∋p
extendReplaceRel-typed-term (replace-left rel) (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) =
  ƛ⊒ƛᵗ (extendReplaceRel-coercionᶜ (replace-left rel) p↦qᶜ)
    (subst
      (λ c → _ ∣ _ ∣ ctx-nrw _ _ c ∷ _ ⊢ _ ⊒ _ ∶ _ ⦂ _ ⊒ _)
      (sym (extendReplaceRel-fun-domain-dualᶜ (replace-left rel) p↦qᶜ))
      (extendReplaceRel-typed-term (replace-left rel) N⊒N′))
extendReplaceRel-typed-term (replace-left rel)
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  ·⊒·ᵗ
    (extendReplaceRel-coercionᶜ (replace-left rel) p↦qᶜ)
    (extendReplaceRel-typed-term (replace-left rel) L⊒L′)
    (subst
      (λ c → _ ∣ _ ∣ _ ⊢ _ ⊒ _ ∶ c ⦂ _ ⊒ _)
      (sym (extendReplaceRel-fun-domain-dualᶜ (replace-left rel) p↦qᶜ))
      (extendReplaceRel-typed-term (replace-left rel) M⊒M′))
extendReplaceRel-typed-term (replace-left rel) (Λ⊒Λᵗ allᶜ vV V⊒V′) =
  Λ⊒Λᵗ (extendReplaceRel-coercionᶜ (replace-left rel) allᶜ) vV
    (extendReplaceRel-typed-term (replace-left (extendReplaceRel-⇑ˢ rel))
      V⊒V′)
extendReplaceRel-typed-term (replace-left rel) (⊒Λᵗ pᶜ N⊒V′) =
  ⊒Λᵗ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-typed-term
      (replace-right (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒V′)
extendReplaceRel-typed-term (replace-left rel)
    (⊒⟨ν⟩ᵗ pᶜ i N⊒V′s) =
  ⊒⟨ν⟩ᵗ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ) i
    (extendReplaceRel-typed-term
      (replace-right (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒V′s)
extendReplaceRel-typed-term (replace-left rel)
    (ν⊒νᵗ {q = q} pᶜ qᶜ N⊒N′) =
  ν⊒νᵗ
    (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-coercionᶜ (replace-left rel) qᶜ)
    (extendReplaceRel-typed-term
      (replace-both {q = ⇑ᶜ q}
        (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-typed-term (replace-left rel) (⊒νᵗ pᶜ N⊒N′) =
  ⊒νᵗ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-typed-term
      (replace-right (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-typed-term (replace-left rel) (ν⊒ᵗ pᶜ N⊒N′) =
  ν⊒ᵗ (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-typed-term
      (replace-left (replace-left (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-typed-term (replace-left rel) (κ⊒κᵗ κ) = κ⊒κᵗ κ
extendReplaceRel-typed-term (replace-left rel)
    (⊕⊒⊕ᵗ M⊒M′ N⊒N′) =
  ⊕⊒⊕ᵗ
    (extendReplaceRel-typed-term (replace-left rel) M⊒M′)
    (extendReplaceRel-typed-term (replace-left rel) N⊒N′)
extendReplaceRel-typed-term (replace-left rel)
    (⊒cast+ᵗ qᶜ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  ⊒cast+ᵗ
    (extendReplaceRel-coercionᶜ (replace-left rel) qᶜ)
    wfΣ q⊒ s⊒
    (extendReplaceRel-compose-left
      (replace-left rel) wfΣ q⊒ s⊒ q⨟s≈r)
    (extendReplaceRel-typed-term (replace-left rel) M⊒M′)
extendReplaceRel-typed-term (replace-left rel)
    (⊒cast-ᵗ qᶜ rᶜ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  ⊒cast-ᵗ
    (extendReplaceRel-coercionᶜ (replace-left rel) qᶜ)
    (extendReplaceRel-coercion (replace-left rel) rᶜ)
    wfΣ q⊒ s⊒
    (extendReplaceRel-compose-left
      (replace-left rel) wfΣ q⊒ s⊒ q⨟s≈r)
    (extendReplaceRel-typed-term (replace-left rel) M⊒M′)
extendReplaceRel-typed-term (replace-left rel)
    (cast+⊒ᵗ pᶜ rᶜ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  cast+⊒ᵗ
    (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    (extendReplaceRel-coercion (replace-left rel) rᶜ)
    wfΣ t⊒ p⊒
    (extendReplaceRel-compose-right
      (replace-left rel) wfΣ t⊒ p⊒ r≈t⨟p)
    (extendReplaceRel-typed-term (replace-left rel) M⊒M′)
extendReplaceRel-typed-term (replace-left rel)
    (cast-⊒ᵗ pᶜ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  cast-⊒ᵗ
    (extendReplaceRel-coercionᶜ (replace-left rel) pᶜ)
    wfΣ t⊒ p⊒
    (extendReplaceRel-compose-right
      (replace-left rel) wfΣ t⊒ p⊒ r≈t⨟p)
    (extendReplaceRel-typed-term (replace-left rel) M⊒M′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (extendᵗ qᶜ pαᶜ M⊒T) =
  extendᵗ
    (extendReplaceRel-coercionᶜ rel qᶜ)
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pαᶜ)
    (extendReplaceRel-typed-term (replace-right rel) M⊒T)
extendReplaceRel-typed-term (replace-both {q = qh} rel) (⊒blameᵗ pᶜ) =
  ⊒blameᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (x⊒xᵗ pᶜ x∋p) =
  x⊒xᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    x∋p
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (ƛ⊒ƛᵗ p↦qᶜ N⊒N′) =
  ƛ⊒ƛᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) p↦qᶜ)
    (subst
      (λ c → _ ∣ _ ∣ ctx-nrw _ _ c ∷ _ ⊢ _ ⊒ _ ∶ _ ⦂ _ ⊒ _)
      (sym
        (extendReplaceRel-fun-domain-dualᶜ
          (replace-both {q = qh} rel)
          p↦qᶜ))
      (extendReplaceRel-typed-term (replace-both {q = qh} rel) N⊒N′))
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′) =
  ·⊒·ᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) p↦qᶜ)
    (extendReplaceRel-typed-term (replace-both {q = qh} rel) L⊒L′)
    (subst
      (λ c → _ ∣ _ ∣ _ ⊢ _ ⊒ _ ∶ c ⦂ _ ⊒ _)
      (sym
        (extendReplaceRel-fun-domain-dualᶜ
          (replace-both {q = qh} rel)
          p↦qᶜ))
      (extendReplaceRel-typed-term (replace-both {q = qh} rel) M⊒M′))
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (Λ⊒Λᵗ allᶜ vV V⊒V′) =
  Λ⊒Λᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) allᶜ) vV
    (extendReplaceRel-typed-term
      (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel))
      V⊒V′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (⊒Λᵗ pᶜ N⊒V′) =
  ⊒Λᵗ (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-typed-term
      (replace-right
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒V′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (⊒⟨ν⟩ᵗ pᶜ i N⊒V′s) =
  ⊒⟨ν⟩ᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ) i
    (extendReplaceRel-typed-term
      (replace-right
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒V′s)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (ν⊒νᵗ {q = q} pᶜ qᶜ N⊒N′) =
  ν⊒νᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) qᶜ)
    (extendReplaceRel-typed-term
      (replace-both {q = ⇑ᶜ q}
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (⊒νᵗ pᶜ N⊒N′) =
  ⊒νᵗ (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-typed-term
      (replace-right
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (ν⊒ᵗ pᶜ N⊒N′) =
  ν⊒ᵗ (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-typed-term
      (replace-left
        (replace-both {q = ⇑ᶜ qh} (extendReplaceRel-⇑ˢ rel)))
      N⊒N′)
extendReplaceRel-typed-term (replace-both {q = qh} rel) (κ⊒κᵗ κ) =
  κ⊒κᵗ κ
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (⊕⊒⊕ᵗ M⊒M′ N⊒N′) =
  ⊕⊒⊕ᵗ
    (extendReplaceRel-typed-term (replace-both {q = qh} rel) M⊒M′)
    (extendReplaceRel-typed-term (replace-both {q = qh} rel) N⊒N′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (⊒cast+ᵗ qᶜ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  ⊒cast+ᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) qᶜ)
    wfΣ q⊒ s⊒
    (extendReplaceRel-compose-left
      (replace-both {q = qh} rel) wfΣ q⊒ s⊒ q⨟s≈r)
    (extendReplaceRel-typed-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (⊒cast-ᵗ qᶜ rᶜ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′) =
  ⊒cast-ᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) qᶜ)
    (extendReplaceRel-coercion (replace-both {q = qh} rel) rᶜ)
    wfΣ q⊒ s⊒
    (extendReplaceRel-compose-left
      (replace-both {q = qh} rel) wfΣ q⊒ s⊒ q⨟s≈r)
    (extendReplaceRel-typed-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (cast+⊒ᵗ pᶜ rᶜ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  cast+⊒ᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    (extendReplaceRel-coercion (replace-both {q = qh} rel) rᶜ)
    wfΣ t⊒ p⊒
    (extendReplaceRel-compose-right
      (replace-both {q = qh} rel) wfΣ t⊒ p⊒ r≈t⨟p)
    (extendReplaceRel-typed-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-typed-term (replace-both {q = qh} rel)
    (cast-⊒ᵗ pᶜ wfΣ t⊒ p⊒ r≈t⨟p M⊒M′) =
  cast-⊒ᵗ
    (extendReplaceRel-coercionᶜ (replace-both {q = qh} rel) pᶜ)
    wfΣ t⊒ p⊒
    (extendReplaceRel-compose-right
      (replace-both {q = qh} rel) wfΣ t⊒ p⊒ r≈t⨟p)
    (extendReplaceRel-typed-term (replace-both {q = qh} rel) M⊒M′)
extendReplaceRel-typed-term (replace-both {q = qh} rel) M⊒T = {!!}

catchup-extend-rel-shifted :
  ∀ n {Δ Δ′ σ π Π Π′ χs α q A B} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ shiftStore n (applyStores χs []) →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  ExtendReplaceRel Δ′
    (combineStoreNrw π ((α ꞉= A ⊒) ∷ σ))
    (combineStoreNrw π ((α ꞉ q) ∷ σ))
catchup-extend-rel-shifted n {Δ = Δ} {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ ⊒ˢ-nil =
  let
    empty≡ = shiftStore-empty-inv n (sym Π≡)
    Δ′≡Δ = trans Δ′≡ (applyTyCtxs-empty-id χs empty≡ Δ)
    qᶜ′ =
      subst
        (λ Δ₀ → Δ₀ ∣ _ ⊢ _ ∶ᶜ _ ⊒ _)
        (sym Δ′≡Δ)
        qᶜ
  in
  replace-here qᶜ′
catchup-extend-rel-shifted n qᶜ Δ′≡ Π≡ () (⊒ˢ-right hA π⊒)
catchup-extend-rel-shifted n {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    with storeChangesLastBind χs
catchup-extend-rel-shifted n {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps
    with trans Π≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
catchup-extend-rel-shifted n {χs = χs}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps | ()
catchup-extend-rel-shifted n {Δ = Δ} {σ = σ}
    {χs = .(χs ++ bind Aχ ∷ keeps)}
    {α = α} {q = q} {A = A}
    qᶜ Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | last-bind χs Aχ keeps keeps-ok =
  let
    Δtail≡ =
      trans Δ′≡
        (trans (applyTyCtxs-last-bind χs Aχ keeps keeps-ok Δ)
          (sym (applyTyCtxs-suc χs Δ)))
    Π-last≡ =
      trans Π≡
        (cong (shiftStore n)
          (applyStores-last-bind χs Aχ keeps keeps-ok []))
    Π-last-normal≡ =
      trans Π-last≡
        (shiftStore-cons n zero (⇑ᵗ Aχ) (⟰ᵗ (applyStores χs [])))
    Πtail≡ =
      trans (storeTail-∷≡ Π-last-normal≡)
        (shiftStore-⟰ᵗ n (applyStores χs []))
    tail =
      catchup-extend-rel-shifted (suc n) {χs = χs}
        {α = suc α} {q = ⇑ᶜ q} {A = ⇑ᵗ A}
        (narrow-⇑ᵗ-ᶜ-srcStoreⁿ {σ = σ} qᶜ)
        Δtail≡
        Πtail≡
        Π′≡
        π⊒
  in
  replace-left tail
catchup-extend-rel-shifted n qᶜ Δ′≡ Π≡ () (⊒ˢ-both hA hA′ s⊒ π⊒)

-- [New] Extend Prefix Transport.
--
-- The emitted prefix determines a single hidden store replacement:
-- `α ꞉= A ⊒` becomes `α ꞉ q`, shifted under every emitted source-only
-- binder.  The structural transport above then moves the term-imprecision
-- derivation across that replacement.  At the exact replacement head it wraps
-- non-endpoint constructors with `extend`; the cast endpoint constructors are
-- rebuilt structurally because their conclusion index is not necessarily
-- `∶ᶜ`.
catchup-extend-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs W N′ α p q A B C D} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ B ⊒ A →
  Δ ∣ srcStoreⁿ ((α ꞉ q) ∷ σ) ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π ((α ꞉= A ⊒) ∷ σ) ∣ []
    ⊢ W ⊒ applyTerms χs (N′ [ α ]ᵀ)
      ∶ applyCoercions χs (p [ α ]ᶜ)
        ⦂ applyTys χs C ⊒ applyTys χs D →
  Δ′ ∣ combineStoreNrw π ((α ꞉ q) ∷ σ) ∣ []
    ⊢ W ⊒ applyTerms χs (N′ [ α ]ᵀ)
      ∶ applyCoercions χs (p [ α ]ᶜ)
        ⦂ applyTys χs C ⊒ applyTys χs D
catchup-extend-transport {χs = χs}
    qᶜ pαᶜ Δ′≡ Π≡ Π′≡ π⊒ W⊒V =
  extendReplaceRel-typed-term
    (catchup-extend-rel-shifted zero {χs = χs}
      qᶜ Δ′≡ Π≡ Π′≡ π⊒)
    W⊒V

postulate
  -- [New] Split Catchup Case.
  --
  -- This is a new catchup case rather than a pre-existing named cambridge25
  -- lemma.  The recursive call catches up the premise opened at `α` under
  -- `(α ꞉ q) ∷ σ`, but the conclusion must reduce the source opened at the
  -- new source-only variable `αᵢ` under
  -- `(α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ`.
  --
  -- Attempted proof notes.  Reusing the `extend` transport shape is not enough:
  -- the proof must also change the source opening from `N [ α ]ᵀ` to
  -- `N [ αᵢ ]ᵀ` and move the emitted prefix through two fresh entries.  The
  -- apparent next lemma is a split-specific reduction transport/opening
  -- lemma for source type variables, paired with the same emitted-prefix
  -- bookkeeping used by `catchup-extend-transport`.
  catchup-split-catchup :
    ∀ {Δ σ χs W Δ′ Π Π′ π N N′ α αᵢ p q A C D} →
    Value W →
    No• W →
    (N [ α ]ᵀ —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs Δ →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
      ⊢ q ∶ᶜ ★ ⊒ A →
    Δ ∣ srcStoreⁿ ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ)
      ⊢ p [ α ]ᶜ ∶ᶜ C ⊒ D →
    Δ′ ∣ combineStoreNrw π ((α ꞉ q) ∷ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (N′ [ α ]ᵀ)
        ∶ applyCoercions χs (p [ α ]ᶜ)
          ⦂ applyTys χs C ⊒ applyTys χs D →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (N [ αᵢ ]ᵀ —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) ∣ []
        ⊢ W′ ⊒ applyTerms χs′ (N′ [ α ]ᵀ)
          ∶ applyCoercions χs′ (p [ α ]ᶜ)
            ⦂ applyTys χs′ C ⊒ applyTys χs′ D

catchup-⊒Λ-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p} →
  Value W →
  No• W →
  (⇑ᵗᵐ N —↠[ χs ] W) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p
      ⦂ applyTys χs (⇑ᵗ A) ⊒ applyTys χs B →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    No• W′ ×
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
          ⦂ applyTys χs′ A ⊒ applyTys χs′ (`∀ B)
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    with shifted-source-catchup-Λ-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , noW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
  let
    pᶜ′ =
      catchup-gen-coercion-typing-transport
        {σ = σ} {π = π′} {χs = χs′} {p = p} {A = A} {B = B}
        pᶜ Δ″≡ Π″≡ Π″′≡ π′⊒
    rebuilt = ⊒Λᵗ pᶜ′ body
    target≡ = applyTerms-Λ χs′ V′
    coercion≡ = applyCoercions-gen χs′ A p
  in
  χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
  vW′ ,
  noW′ ,
  N↠W′ ,
  Δ″≡ ,
  Π″≡ ,
  Π″′≡ ,
  π′⊒ ,
  subst
    (λ c → Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′) ∶ c
        ⦂ applyTys χs′ A ⊒ applyTys χs′ (`∀ B))
    (sym coercion≡)
    (subst
      (λ B₀ → Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ applyTerms χs′ (Λ V′)
          ∶ gen (applyTys χs′ A) (applyCoercionUnderTyBinders χs′ p)
          ⦂ applyTys χs′ A ⊒ B₀)
      (sym (applyTys-∀ χs′ B))
      (subst
        (λ T → Δ″ ∣ combineStoreNrw π′ σ ∣ []
          ⊢ W′ ⊒ T
            ∶ gen (applyTys χs′ A) (applyCoercionUnderTyBinders χs′ p)
            ⦂ applyTys χs′ A
              ⊒ `∀ (applyTysUnderTyBinders χs′ B))
        (sym target≡)
        rebuilt))

catchup-⊒⟨ν⟩-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p s} →
  Value W →
  No• W →
  (⇑ᵗᵐ N —↠[ χs ] W) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Inert s →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs (V′ ⟨ s ⟩) ∶ applyCoercions χs p
      ⦂ applyTys χs (⇑ᵗ A) ⊒ applyTys χs B →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    No• W′ ×
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (V′ ⟨ gen A s ⟩)
        ∶ applyCoercions χs′ (gen A p)
          ⦂ applyTys χs′ A ⊒ applyTys χs′ (`∀ B)
catchup-⊒⟨ν⟩-catchup
    {σ = σ} {A = A} {B = B} {V′ = V′} {p = p} {s = s}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    with shifted-source-catchup-⟨ν⟩-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′s
catchup-⊒⟨ν⟩-catchup
    {σ = σ} {A = A} {B = B} {V′ = V′} {p = p} {s = s}
    vW noW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , noW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
  let
    pᶜ′ =
      catchup-gen-coercion-typing-transport
        {σ = σ} {π = π′} {χs = χs′} {p = p} {A = A} {B = B}
        pᶜ Δ″≡ Π″≡ Π″′≡ π′⊒
    i′ = applyCoercionUnderTyBinders-preserves-Inert χs′ i
    rebuilt = ⊒⟨ν⟩ᵗ pᶜ′ i′ body
    target≡ =
      trans (applyTerms-cast χs′ V′ (gen A s))
        (cong (λ c → applyTerms χs′ V′ ⟨ c ⟩)
          (applyCoercions-gen χs′ A s))
    coercion≡ = applyCoercions-gen χs′ A p
  in
  χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
  vW′ ,
  noW′ ,
  N↠W′ ,
  Δ″≡ ,
  Π″≡ ,
  Π″′≡ ,
  π′⊒ ,
  subst
    (λ c → Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (V′ ⟨ gen A s ⟩) ∶ c
        ⦂ applyTys χs′ A ⊒ applyTys χs′ (`∀ B))
    (sym coercion≡)
    (subst
      (λ B₀ → Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ applyTerms χs′ (V′ ⟨ gen A s ⟩)
          ∶ gen (applyTys χs′ A) (applyCoercionUnderTyBinders χs′ p)
          ⦂ applyTys χs′ A ⊒ B₀)
      (sym (applyTys-∀ χs′ B))
      (subst
        (λ T → Δ″ ∣ combineStoreNrw π′ σ ∣ []
          ⊢ W′ ⊒ T
            ∶ gen (applyTys χs′ A) (applyCoercionUnderTyBinders χs′ p)
            ⦂ applyTys χs′ A
              ⊒ `∀ (applyTysUnderTyBinders χs′ B))
        (sym target≡)
        rebuilt))

postulate
  -- [New] Right ν Catchup Case.
  --
  -- This is a new catchup case, not a pre-existing named cambridge25 lemma.
  -- The recursive call catches up the shifted premise under
  -- `(⊒ zero ꞉=☆) ∷ ⇑ˢ σ`; the desired conclusion is for the
  -- unshifted wrapper `ν ★ N (⇑ᶜ p)` under `σ`.
  --
  -- Attempted proof notes.  Lifting the recursive source reduction through the
  -- `ν` wrapper is straightforward, but the remaining step needs more than a
  -- plain transport: one has to use the canonical runtime shape of the
  -- caught-up polymorphic value to take the `ν` store-opening step, then
  -- remove the source-only star entry from the emitted prefix and unshift the
  -- target relation.  This should probably be factored through the same
  -- shifted-source inversion lemma needed by `⊒Λ`, plus a small reduction
  -- lemma for `ν` opening and the corresponding store-prefix transport.
  catchup-ν⊒-catchup :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V p A B} →
    Value V →
    Value W →
    No• W →
    (N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
    Δ′ ∣ combineStoreNrw π ((⊒ zero ꞉=☆) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (⇑ᵗᵐ V) ∶ applyCoercions χs (⇑ᶜ p)
        ⦂ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B) →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      No• W′ ×
      (ν ★ N (⇑ᶜ p) —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ applyTerms χs′ V ∶ applyCoercions χs′ p
          ⦂ applyTys χs′ A ⊒ applyTys χs′ B

catchup-lemma :
  ∀ {Δ σ M V p A B} →
  RuntimeOK M →
  Value V →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ p ⦂ A ⊒ B →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    No• W ×
    (M —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V ∶ applyCoercions χs p
        ⦂ applyTys χs A ⊒ applyTys χs B
catchup-lemma okM vV M⊒V = {!!}
