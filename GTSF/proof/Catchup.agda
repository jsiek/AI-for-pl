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
open import Store using
  (StoreIncl; StoreIncl-refl; StoreIncl-cons; StoreIncl-drop)
open import Coercions
open import NuTerms
open import NuReduction
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.NarrowWidenProperties
  using
    ( StoreDetWf-⟰ᵗ
    ; WfTyˢ-⇑ᵗ
    ; WfTyˢ-store-weaken
    ; narrowing-determinedᵐ
    ; narrow-⇑ᵗ-ᶜ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ
    ; narrow-⇑ᵗ-ᶜ-srcStoreⁿ≤
    ; narrow-⇑ᵗ-open-srcStoreⁿ
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
    ; src-renameᶜ
    ; tgt-renameᶜ
    ; renameᶜ-open-commute
    )
open import proof.NuTermProperties using (renameᵗᵐ-preserves-Value)
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
    ; store-cons≢[]
    )

------------------------------------------------------------------------
-- Catchup
------------------------------------------------------------------------

postulate
  -- cambridge25 "Left Widening Lemma": the source before the left cast is
  -- already a value.  The catchup induction that produces that value remains
  -- in `catchup-lemma`.  The Δ′ equality is Agda bookkeeping for the emitted
  -- store-change sequence.
  left-widening-lemma :
    ∀ {Δ σ V V′ p r t A B C D} →
    Value V →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ p →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
      (V ⟨ - t ⟩ —↠[ χs ] W) ×
      (Δ′ ≡ applyTyCtxs χs Δ) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs r

  -- cambridge25 "Left Narrowing Lemma", likewise value-level, with the same
  -- emitted-context bookkeeping.
  left-narrowing-lemma :
    ∀ {Δ σ V V′ p r t A B C D} →
    Value V →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ C ⊒ D →
    Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
    Δ ∣ σ ∣ [] ⊢ V ⊒ V′ ∶ r →
    ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
      Value W ×
      (V ⟨ t ⟩ —↠[ χs ] W) ×
      (Δ′ ≡ applyTyCtxs χs Δ) ×
      (Π ≡ applyStores χs []) ×
      (Π′ ≡ applyStore keep []) ×
      Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
      Δ′ ∣ combineStoreNrw π σ ∣ []
        ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p

  -- cambridge25 Catchup Lemma, shifted-source diagrams for the `⊒Λ`
  -- case: peel a catchup of `⇑ᵗᵐ N` under `(zero := ★⊒) ∷ ⇑ˢ σ`
  -- back to a catchup of `N`, retaining the fresh-star premise needed to
  -- rebuild `⊒Λ`.
  shifted-source-catchup-Λ-inversion :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V′ p} →
    Value W →
    (⇑ᵗᵐ N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      (N —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      suc Δ″ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ) ∣ []
        ⊢ ⇑ᵗᵐ W′ ⊒ applyTermsUnderTyBinders χs′ V′
          ∶ applyCoercionUnderTyBinders χs′ p

  -- Same shifted-source catchup diagram for the `⊒⟨ν⟩` wrapper, where
  -- the target value remains outside the generated cast in the final result.
  shifted-source-catchup-⟨ν⟩-inversion :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V′ p s} →
    Value W →
    (⇑ᵗᵐ N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (V′ ⟨ s ⟩) ∶ applyCoercions χs p →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      (N —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      suc Δ″ ∣ (zero ꞉= ★ ⊒) ∷ ⇑ˢ (combineStoreNrw π′ σ) ∣ []
        ⊢ ⇑ᵗᵐ W′
          ⊒ applyTerms χs′ V′ ⟨ applyCoercionUnderTyBinders χs′ s ⟩
          ∶ applyCoercionUnderTyBinders χs′ p

applyMode : StoreChange → ModeEnv → ModeEnv
applyMode keep μ = μ
applyMode (bind A) μ = genᵈ μ

applyModes : StoreChanges → ModeEnv → ModeEnv
applyModes [] μ = μ
applyModes (χ ∷ χs) μ = applyModes χs (applyMode χ μ)

applyCoercion-narrowᵐ :
  ∀ χ {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  applyMode χ μ ∣ applyTyCtx χ Δ ∣ applyStore χ Σ
    ⊢ applyCoercion χ c ∶ applyTy χ A ⊒ applyTy χ B
applyCoercion-narrowᵐ keep c⊒ = c⊒
applyCoercion-narrowᵐ (bind Aν) c⊒ =
  narrow-weaken ≤-refl StoreIncl-drop (narrow-⇑ᵗ-gen c⊒)

applyCoercions-narrowᵐ :
  ∀ χs {μ Δ Σ c A B} →
  μ ∣ Δ ∣ Σ ⊢ c ∶ A ⊒ B →
  applyModes χs μ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
    ⊢ applyCoercions χs c ∶ applyTys χs A ⊒ applyTys χs B
applyCoercions-narrowᵐ [] c⊒ = c⊒
applyCoercions-narrowᵐ (χ ∷ χs) c⊒ =
  applyCoercions-narrowᵐ χs (applyCoercion-narrowᵐ χ c⊒)

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

≈ⁿ-add-left-star :
  ∀ {Δ σ s t A B} →
  Δ ∣ σ ⊢ s ≈ t ∶ A ⊒ B →
  Δ ∣ (⊒ zero ꞉=☆) ∷ σ ⊢ s ≈ t ∶ A ⊒ B
≈ⁿ-add-left-star = ≈ⁿ-add-left-star-var zero

compose-leftⁿ-⇑ˢ :
  ∀ {Δ σ q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ q ⨾ⁿ ⇑ᶜ s ≈ ⇑ᶜ r ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
compose-leftⁿ-⇑ˢ (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  let
    q⊒′ = narrow-⇑ᵗ-gen q⊒
    s⊒′ = narrow-⇑ᵗ-gen s⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒
    new = _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} q⊒′ s⊒′
    u≡ =
      narrowing-determinedᵐ (StoreDetWf-⟰ᵗ wfΣ)
        (proj₂ new)
        (narrow-⇑ᵗ-gen (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ u ≈ ⇑ᶜ _ ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-⇑ˢ q⨟s≈r)
  in
  compose-leftⁿ (StoreDetWf-⟰ᵗ wfΣ) q⊒′ s⊒′ eq′

compose-leftⁿ-add-left-star-var :
  ∀ X {Δ σ q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ (⊒ X ꞉=☆) ∷ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
compose-leftⁿ-add-left-star-var X (compose-leftⁿ wfΣ q⊒ s⊒ q⨟s≈r) =
  compose-leftⁿ wfΣ q⊒ s⊒ (≈ⁿ-add-left-star-var X q⨟s≈r)

compose-leftⁿ-add-left-star :
  ∀ {Δ σ q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ ∣ (⊒ zero ꞉=☆) ∷ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B
compose-leftⁿ-add-left-star = compose-leftⁿ-add-left-star-var zero

compose-rightⁿ-⇑ˢ :
  ∀ {Δ σ r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  suc Δ ∣ ⇑ˢ σ ⊢ ⇑ᶜ r ≈ ⇑ᶜ t ⨾ⁿ ⇑ᶜ p ∶ ⇑ᵗ A ⊒ ⇑ᵗ B
compose-rightⁿ-⇑ˢ (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  let
    t⊒′ = narrow-⇑ᵗ-gen t⊒
    p⊒′ = narrow-⇑ᵗ-gen p⊒
    old = _⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒
    new = _⨟ⁿ_ {wfΣ = StoreDetWf-⟰ᵗ wfΣ} t⊒′ p⊒′
    u≡ =
      narrowing-determinedᵐ (StoreDetWf-⟰ᵗ wfΣ)
        (proj₂ new)
        (narrow-⇑ᵗ-gen (proj₂ old))
    eq′ =
      subst
        (λ u → _ ∣ _ ⊢ ⇑ᶜ _ ≈ u ∶ _ ⊒ _)
        (sym u≡)
        (≈ⁿ-⇑ˢ r≈t⨟p)
  in
  compose-rightⁿ (StoreDetWf-⟰ᵗ wfΣ) t⊒′ p⊒′ eq′

compose-rightⁿ-add-left-star-var :
  ∀ X {Δ σ r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ (⊒ X ꞉=☆) ∷ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
compose-rightⁿ-add-left-star-var X (compose-rightⁿ wfΣ t⊒ p⊒ r≈t⨟p) =
  compose-rightⁿ wfΣ t⊒ p⊒ (≈ⁿ-add-left-star-var X r≈t⨟p)

compose-rightⁿ-add-left-star :
  ∀ {Δ σ r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ ∣ (⊒ zero ꞉=☆) ∷ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B
compose-rightⁿ-add-left-star = compose-rightⁿ-add-left-star-var zero

catchup-compose-left-transport-shifted :
  ∀ n {Δ Δ′ σ π Π Π′ χs q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ shiftStore n (applyStores χs []) →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
      ≈ applyCoercions χs r ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-left-transport-shifted n {Δ = Δ} {Δ′ = Δ′} {σ = σ}
    {χs = χs} {q = q} {s = s} {r = r} {A = A} {B = B}
    q⨟s≈r Δ′≡ Π≡ Π′≡ ⊒ˢ-nil =
  let
    empty≡ = shiftStore-empty-inv n (sym Π≡)
    Δ′≡Δ = trans Δ′≡ (applyTyCtxs-empty-id χs empty≡ Δ)
    q≡ = applyCoercions-empty-id χs empty≡ q
    s≡ = applyCoercions-empty-id χs empty≡ s
    r≡ = applyCoercions-empty-id χs empty≡ r
    A≡ = applyTys-empty-id χs empty≡ A
    B≡ = applyTys-empty-id χs empty≡ B
  in
  subst
    (λ Δ₀ → Δ₀ ∣ σ
      ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
        ≈ applyCoercions χs r ∶ applyTys χs A ⊒ applyTys χs B)
    (sym Δ′≡Δ)
    (subst
      (λ B₀ → Δ ∣ σ
        ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
          ≈ applyCoercions χs r ∶ applyTys χs A ⊒ B₀)
      (sym B≡)
      (subst
        (λ A₀ → Δ ∣ σ
          ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
            ≈ applyCoercions χs r ∶ A₀ ⊒ B)
        (sym A≡)
        (subst
          (λ r₀ → Δ ∣ σ
            ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
              ≈ r₀ ∶ A ⊒ B)
          (sym r≡)
          (subst
            (λ s₀ → Δ ∣ σ
              ⊢ applyCoercions χs q ⨾ⁿ s₀ ≈ r ∶ A ⊒ B)
            (sym s≡)
            (subst
              (λ q₀ → Δ ∣ σ ⊢ q₀ ⨾ⁿ s ≈ r ∶ A ⊒ B)
              (sym q≡)
              q⨟s≈r)))))
catchup-compose-left-transport-shifted n
    q⨟s≈r Δ′≡ Π≡ () (⊒ˢ-right hA π⊒)
catchup-compose-left-transport-shifted n {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    with storeChangesLastBind χs
catchup-compose-left-transport-shifted n {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps
    with trans Π≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
catchup-compose-left-transport-shifted n {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps | ()
catchup-compose-left-transport-shifted n {Δ = Δ} {σ = σ}
    {χs = .(χs ++ bind Aχ ∷ keeps)}
    {q = q} {s = s} {r = r} {A = A} {B = B}
    q⨟s≈r Δ′≡ Π≡ Π′≡ (⊒ˢ-left {X = X} π⊒)
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
      catchup-compose-left-transport-shifted (suc n) {χs = χs}
        (compose-leftⁿ-⇑ˢ q⨟s≈r)
        Δtail≡
        Πtail≡
        Π′≡
        π⊒
    lifted = compose-leftⁿ-add-left-star-var X tail
    q≡ =
      trans (applyCoercions-⇑ᶜ χs q)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok q))
    s≡ =
      trans (applyCoercions-⇑ᶜ χs s)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok s))
    r≡ =
      trans (applyCoercions-⇑ᶜ χs r)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok r))
    A≡ =
      trans (applyTys-⇑ᵗ χs A)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok A))
    B≡ =
      trans (applyTys-⇑ᵗ χs B)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok B))
  in
  subst
    (λ B₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
      ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) s
      ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) r
      ∶ applyTys (χs ++ bind Aχ ∷ keeps) A ⊒ B₀)
    B≡
    (subst
      (λ A₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
        ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) s
        ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) r
        ∶ A₀ ⊒ applyTys χs (⇑ᵗ B))
      A≡
      (subst
        (λ r₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
          ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) s
          ≈ r₀ ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
        r≡
        (subst
          (λ s₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) q
            ⨾ⁿ s₀ ≈ applyCoercions χs (⇑ᶜ r)
            ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
          s≡
          (subst
            (λ q₀ → _ ∣ _ ⊢ q₀
              ⨾ⁿ applyCoercions χs (⇑ᶜ s)
              ≈ applyCoercions χs (⇑ᶜ r)
              ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
            q≡
            lifted))))
catchup-compose-left-transport-shifted n
    q⨟s≈r Δ′≡ Π≡ () (⊒ˢ-both hA hA′ s⊒ π⊒)

catchup-compose-left-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs q s r A B} →
  Δ ∣ σ ⊢ q ⨾ⁿ s ≈ r ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs q ⨾ⁿ applyCoercions χs s
      ≈ applyCoercions χs r ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-left-transport {χs = χs} q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒ =
  catchup-compose-left-transport-shifted zero
    {χs = χs}
    q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒

catchup-compose-right-transport-shifted :
  ∀ n {Δ Δ′ σ π Π Π′ χs r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ shiftStore n (applyStores χs []) →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs r
      ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
      ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-right-transport-shifted n {Δ = Δ} {Δ′ = Δ′} {σ = σ}
    {χs = χs} {r = r} {t = t} {p = p} {A = A} {B = B}
    r≈t⨟p Δ′≡ Π≡ Π′≡ ⊒ˢ-nil =
  let
    empty≡ = shiftStore-empty-inv n (sym Π≡)
    Δ′≡Δ = trans Δ′≡ (applyTyCtxs-empty-id χs empty≡ Δ)
    r≡ = applyCoercions-empty-id χs empty≡ r
    t≡ = applyCoercions-empty-id χs empty≡ t
    p≡ = applyCoercions-empty-id χs empty≡ p
    A≡ = applyTys-empty-id χs empty≡ A
    B≡ = applyTys-empty-id χs empty≡ B
  in
  subst
    (λ Δ₀ → Δ₀ ∣ σ
      ⊢ applyCoercions χs r
        ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
        ∶ applyTys χs A ⊒ applyTys χs B)
    (sym Δ′≡Δ)
    (subst
      (λ B₀ → Δ ∣ σ
        ⊢ applyCoercions χs r
          ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
          ∶ applyTys χs A ⊒ B₀)
      (sym B≡)
      (subst
        (λ A₀ → Δ ∣ σ
          ⊢ applyCoercions χs r
            ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
            ∶ A₀ ⊒ B)
        (sym A≡)
        (subst
          (λ p₀ → Δ ∣ σ
            ⊢ applyCoercions χs r
              ≈ applyCoercions χs t ⨾ⁿ p₀ ∶ A ⊒ B)
          (sym p≡)
          (subst
            (λ t₀ → Δ ∣ σ
              ⊢ applyCoercions χs r ≈ t₀ ⨾ⁿ p ∶ A ⊒ B)
            (sym t≡)
            (subst
              (λ r₀ → Δ ∣ σ ⊢ r₀ ≈ t ⨾ⁿ p ∶ A ⊒ B)
              (sym r≡)
              r≈t⨟p)))))
catchup-compose-right-transport-shifted n
    r≈t⨟p Δ′≡ Π≡ () (⊒ˢ-right hA π⊒)
catchup-compose-right-transport-shifted n {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    with storeChangesLastBind χs
catchup-compose-right-transport-shifted n {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps
    with trans Π≡
      (trans (cong (shiftStore n) (allKeep-applyStores-id keeps []))
        (shiftStore-empty n))
catchup-compose-right-transport-shifted n {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left π⊒)
    | no-bind keeps | ()
catchup-compose-right-transport-shifted n {Δ = Δ} {σ = σ}
    {χs = .(χs ++ bind Aχ ∷ keeps)}
    {r = r} {t = t} {p = p} {A = A} {B = B}
    r≈t⨟p Δ′≡ Π≡ Π′≡ (⊒ˢ-left {X = X} π⊒)
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
      catchup-compose-right-transport-shifted (suc n) {χs = χs}
        (compose-rightⁿ-⇑ˢ r≈t⨟p)
        Δtail≡
        Πtail≡
        Π′≡
        π⊒
    lifted = compose-rightⁿ-add-left-star-var X tail
    r≡ =
      trans (applyCoercions-⇑ᶜ χs r)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok r))
    t≡ =
      trans (applyCoercions-⇑ᶜ χs t)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok t))
    p≡ =
      trans (applyCoercions-⇑ᶜ χs p)
        (sym (applyCoercions-last-bind χs Aχ keeps keeps-ok p))
    A≡ =
      trans (applyTys-⇑ᵗ χs A)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok A))
    B≡ =
      trans (applyTys-⇑ᵗ χs B)
        (sym (applyTys-last-bind χs Aχ keeps keeps-ok B))
  in
  subst
    (λ B₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
      ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) t
        ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) p
      ∶ applyTys (χs ++ bind Aχ ∷ keeps) A ⊒ B₀)
    B≡
    (subst
      (λ A₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
        ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) t
          ⨾ⁿ applyCoercions (χs ++ bind Aχ ∷ keeps) p
        ∶ A₀ ⊒ applyTys χs (⇑ᵗ B))
      A≡
      (subst
        (λ p₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
          ≈ applyCoercions (χs ++ bind Aχ ∷ keeps) t
            ⨾ⁿ p₀ ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
        p≡
        (subst
          (λ t₀ → _ ∣ _ ⊢ applyCoercions (χs ++ bind Aχ ∷ keeps) r
            ≈ t₀ ⨾ⁿ applyCoercions χs (⇑ᶜ p)
            ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
          t≡
          (subst
            (λ r₀ → _ ∣ _ ⊢ r₀
              ≈ applyCoercions χs (⇑ᶜ t)
                ⨾ⁿ applyCoercions χs (⇑ᶜ p)
              ∶ applyTys χs (⇑ᵗ A) ⊒ applyTys χs (⇑ᵗ B))
            r≡
            lifted))))
catchup-compose-right-transport-shifted n
    r≈t⨟p Δ′≡ Π≡ () (⊒ˢ-both hA hA′ s⊒ π⊒)

catchup-compose-right-transport :
  ∀ {Δ Δ′ σ π Π Π′ χs r t p A B} →
  Δ ∣ σ ⊢ r ≈ t ⨾ⁿ p ∶ A ⊒ B →
  Δ′ ≡ applyTyCtxs χs Δ →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ′ ∣ combineStoreNrw π σ
    ⊢ applyCoercions χs r
      ≈ applyCoercions χs t ⨾ⁿ applyCoercions χs p
      ∶ applyTys χs A ⊒ applyTys χs B
catchup-compose-right-transport {χs = χs} r≈t⨟p Δ′≡ Π≡ Π′≡ π⊒ =
  catchup-compose-right-transport-shifted zero
    {χs = χs}
    r≈t⨟p Δ′≡ Π≡ Π′≡ π⊒

postulate
  -- cambridge25 "Extend Prefix Transport" [New].  This is the paper-level
  -- opened-target statement needed by the `extend` case of
  -- catchup.  An earlier proof attempt showed that the arbitrary-target
  -- variant is too broad, specifically in the `⊒α` case.
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
        ∶ applyCoercions χs (p [ α ]ᶜ) →
    Δ′ ∣ combineStoreNrw π ((α ꞉ q) ∷ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (N′ [ α ]ᵀ)
        ∶ applyCoercions χs (p [ α ]ᶜ)

postulate
  -- cambridge25 "Split Catchup Case" [New].  This case transports the
  -- induction result for `N [ α ]ᵀ` across the split pair
  -- `(α := A⊒, αᵢ := ★)` to obtain the source reduction from `N [ αᵢ ]ᵀ`.
  catchup-split-catchup :
    ∀ {Δ σ χs W Δ′ Π Π′ π N N′ α αᵢ p q A C D} →
    Value W →
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
        ∶ applyCoercions χs (p [ α ]ᶜ) →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      (N [ αᵢ ]ᵀ —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′
        ((α ꞉= A ⊒) ∷ (⊒ αᵢ ꞉=☆) ∷ σ) ∣ []
        ⊢ W′ ⊒ applyTerms χs′ (N′ [ α ]ᵀ)
          ∶ applyCoercions χs′ (p [ α ]ᶜ)

catchup-⊒Λ-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p} →
  Value W →
  (⇑ᵗᵐ N —↠[ χs ] W) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs V′ ∶ applyCoercions χs p →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    with shifted-source-catchup-Λ-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′
catchup-⊒Λ-catchup {σ = σ} {A = A} {B = B} {V′ = V′} {p = p}
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
  let
    pᶜ′ =
      catchup-gen-coercion-typing-transport
        {σ = σ} {π = π′} {χs = χs′} {p = p} {A = A} {B = B}
        pᶜ Δ″≡ Π″≡ Π″′≡ π′⊒
    rebuilt = ⊒Λ pᶜ′ body
    target≡ = applyTerms-Λ χs′ V′
    coercion≡ = applyCoercions-gen χs′ A p
  in
  χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
  vW′ ,
  N↠W′ ,
  Δ″≡ ,
  Π″≡ ,
  Π″′≡ ,
  π′⊒ ,
  subst
    (λ c → Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (Λ V′) ∶ c)
    (sym coercion≡)
    (subst
      (λ T → Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ T ∶ gen (applyTys χs′ A)
          (applyCoercionUnderTyBinders χs′ p))
      (sym target≡)
      rebuilt)

catchup-⊒⟨ν⟩-catchup :
  ∀ {Δ σ χs W Δ′ Π Π′ π A B N V′ p s} →
  Value W →
  (⇑ᵗᵐ N —↠[ χs ] W) →
  Δ′ ≡ applyTyCtxs χs (suc Δ) →
  Π ≡ applyStores χs [] →
  Π′ ≡ [] →
  Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
  Δ ∣ srcStoreⁿ σ ⊢ gen A p ∶ᶜ A ⊒ `∀ B →
  Inert s →
  Δ′ ∣ combineStoreNrw π ((zero ꞉= ★ ⊒) ∷ ⇑ˢ σ) ∣ []
    ⊢ W ⊒ applyTerms χs (V′ ⟨ s ⟩) ∶ applyCoercions χs p →
  ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
    Value W′ ×
    (N —↠[ χs′ ] W′) ×
    (Δ″ ≡ applyTyCtxs χs′ Δ) ×
    (Π″ ≡ applyStores χs′ []) ×
    (Π″′ ≡ applyStore keep []) ×
    Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
    Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (V′ ⟨ gen A s ⟩)
        ∶ applyCoercions χs′ (gen A p)
catchup-⊒⟨ν⟩-catchup
    {σ = σ} {A = A} {B = B} {V′ = V′} {p = p} {s = s}
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    with shifted-source-catchup-⟨ν⟩-inversion
      vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ W⊒V′s
catchup-⊒⟨ν⟩-catchup
    {σ = σ} {A = A} {B = B} {V′ = V′} {p = p} {s = s}
    vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ i W⊒V′s
    | χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
      vW′ , N↠W′ , Δ″≡ , Π″≡ , Π″′≡ , π′⊒ , body =
  let
    pᶜ′ =
      catchup-gen-coercion-typing-transport
        {σ = σ} {π = π′} {χs = χs′} {p = p} {A = A} {B = B}
        pᶜ Δ″≡ Π″≡ Π″′≡ π′⊒
    i′ = applyCoercionUnderTyBinders-preserves-Inert χs′ i
    rebuilt = ⊒⟨ν⟩ pᶜ′ i′ body
    target≡ =
      trans (applyTerms-cast χs′ V′ (gen A s))
        (cong (λ c → applyTerms χs′ V′ ⟨ c ⟩)
          (applyCoercions-gen χs′ A s))
    coercion≡ = applyCoercions-gen χs′ A p
  in
  χs′ , W′ , Δ″ , Π″ , Π″′ , π′ ,
  vW′ ,
  N↠W′ ,
  Δ″≡ ,
  Π″≡ ,
  Π″′≡ ,
  π′⊒ ,
  subst
    (λ c → Δ″ ∣ combineStoreNrw π′ σ ∣ []
      ⊢ W′ ⊒ applyTerms χs′ (V′ ⟨ gen A s ⟩) ∶ c)
    (sym coercion≡)
    (subst
      (λ T → Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ T ∶ gen (applyTys χs′ A)
          (applyCoercionUnderTyBinders χs′ p))
      (sym target≡)
      rebuilt)

postulate
  -- cambridge25 "Right ν Catchup Case" [New].  The proof uses the canonical
  -- runtime shape of the caught-up polymorphic value to take the `ν` opening
  -- step and then transports the emitted store prefix back out of the fresh
  -- source-only star entry.
  catchup-ν⊒-catchup :
    ∀ {Δ σ χs W Δ′ Π Π′ π N V p A B} →
    Value V →
    Value W →
    (N —↠[ χs ] W) →
    Δ′ ≡ applyTyCtxs χs (suc Δ) →
    Π ≡ applyStores χs [] →
    Π′ ≡ [] →
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ →
    Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B →
    Δ′ ∣ combineStoreNrw π ((⊒ zero ꞉=☆) ∷ ⇑ˢ σ) ∣ []
      ⊢ W ⊒ applyTerms χs (⇑ᵗᵐ V) ∶ applyCoercions χs (⇑ᶜ p) →
    ∃[ χs′ ] ∃[ W′ ] ∃[ Δ″ ] ∃[ Π″ ] ∃[ Π″′ ] ∃[ π′ ]
      Value W′ ×
      (ν ★ N (⇑ᶜ p) —↠[ χs′ ] W′) ×
      (Δ″ ≡ applyTyCtxs χs′ Δ) ×
      (Π″ ≡ applyStores χs′ []) ×
      (Π″′ ≡ applyStore keep []) ×
      Δ″ ⊢ π′ ꞉ Π″ ⊒ˢ Π″′ ×
      Δ″ ∣ combineStoreNrw π′ σ ∣ []
        ⊢ W′ ⊒ applyTerms χs′ V ∶ applyCoercions χs′ p

catchup-lemma :
  ∀ {Δ σ M V p} →
  Value V →
  Δ ∣ σ ∣ [] ⊢ M ⊒ V ∶ p →
  ∃[ χs ] ∃[ W ] ∃[ Δ′ ] ∃[ Π ] ∃[ Π′ ] ∃[ π ]
    Value W ×
    (M —↠[ χs ] W) ×
    (Δ′ ≡ applyTyCtxs χs Δ) ×
    (Π ≡ applyStores χs []) ×
    (Π′ ≡ applyStore keep []) ×
    Δ′ ⊢ π ꞉ Π ⊒ˢ Π′ ×
    Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ applyTerms χs V ∶ applyCoercions χs p
catchup-lemma vV (extend qᶜ pαᶜ M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma vV (extend qᶜ pαᶜ M⊒V)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V =
  -- Need transport for catchup evidence through the de Bruijn store-prefix
  -- change made by `extend`: rebuild `extend` after moving the emitted
  -- narrowing `π` under the existing fresh α entry.  The side conditions
  -- `qᶜ` and `pαᶜ` must also be transported from the original Δ/σ to the
  -- emitted Δ′/`combineStoreNrw π σ` context.  This is source-only
  -- store-prefix transport, not ordinary `applyStore` transport on both
  -- source and target stores.
  χs , W , Δ′ , Π , Π′ , π ,
  vW ,
  M↠W ,
  Δ′≡ ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  catchup-extend-transport
    {π = π} {χs = χs}
    qᶜ pαᶜ Δ′≡ Π≡ Π′≡ π⊒ W⊒V
catchup-lemma vV (split qᶜ pαᶜ M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma vV (split qᶜ pαᶜ M⊒V)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V =
  catchup-split-catchup
    vW
    M↠W
    Δ′≡
    Π≡
    Π′≡
    π⊒
    qᶜ
    pαᶜ
    W⊒V
catchup-lemma () (⊒blame pᶜ)
catchup-lemma () (x⊒x pᶜ x∋p)
catchup-lemma (ƛ N′) (ƛ⊒ƛ {N = N} p↦qᶜ N⊒N′) =
  [] , ƛ N , _ , [] , [] , [] ,
  ƛ N ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  ƛ⊒ƛ p↦qᶜ N⊒N′
catchup-lemma () (·⊒· qᶜ L⊒L′ M⊒M′)
catchup-lemma (Λ vV′) (Λ⊒Λ allᶜ vV V⊒V′) =
  [] , Λ _ , _ , [] , [] , [] ,
  Λ vV ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  Λ⊒Λ allᶜ vV V⊒V′
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    with catchup-lemma vV′ N⊒V′
catchup-lemma (Λ vV′) (⊒Λ pᶜ N⊒V′)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′ =
  catchup-⊒Λ-catchup vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒V′
catchup-lemma (vV′ ⟨ i ⟩) (⊒⟨ν⟩ pᶜ sᵢ N⊒V′)
    with catchup-lemma (vV′ ⟨ sᵢ ⟩) N⊒V′
catchup-lemma (vV′ ⟨ i ⟩) (⊒⟨ν⟩ pᶜ sᵢ N⊒V′)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , ⇑N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒V′s =
  catchup-⊒⟨ν⟩-catchup vW ⇑N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ sᵢ W⊒V′s
catchup-lemma () (α⊒α qᶜ pαᶜ L⊒L′)
catchup-lemma () (⊒α pαᶜ L⊒L′)
catchup-lemma () (ν⊒ν pᶜ qᶜ N⊒N′)
catchup-lemma () (⊒ν pᶜ N⊒N′)
catchup-lemma vV (ν⊒ {p = p} pᶜ N⊒V)
    with catchup-lemma (renameᵗᵐ-preserves-Value suc vV) N⊒V
catchup-lemma vV (ν⊒ {p = p} pᶜ N⊒V)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , N↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒⇑V =
  catchup-ν⊒-catchup vV vW N↠W Δ′≡ Π≡ Π′≡ π⊒ pᶜ W⊒⇑V
catchup-lemma {Δ = Δ} ($ κ) (κ⊒κ κ) =
  [] , $ κ , Δ , [] , [] , [] ,
  $ κ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  ⊒ˢ-nil ,
  κ⊒κ κ
catchup-lemma () (⊕⊒⊕ M⊒M′ N⊒N′)
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast+ {M′ = M′} {q = q} {s = s} qᶜ q⨟s≈r M⊒M′)
    with catchup-lemma vV′ M⊒M′
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast+ {M′ = M′} {q = q} {s = s} qᶜ q⨟s≈r M⊒M′)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  -- Rebuild `⊒cast+` after transporting the side conditions through the
  -- emitted store changes, then rewrite the weakened target cast into the
  -- syntactic shape of `applyTerms χs`.
  χs , W , Δ′ , Π , Π′ , π ,
  vW ,
  M↠W ,
  Δ′≡ ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  subst
    (λ T → Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ T ∶ applyCoercions χs q)
    (sym (applyTerms-cast-dual χs M′ s))
    (⊒cast+
      (catchup-coercion-typing-transport
        {σ = σ} {π = π} {χs = χs} {p = q}
        qᶜ Δ′≡ Π≡ Π′≡ π⊒)
      (catchup-compose-left-transport
        {σ = σ} {π = π} {χs = χs} {q = q} {s = s}
        q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒)
      W⊒M′)
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast- {M′ = M′} {q = q} {r = r} {s = s}
      qᶜ q⨟s≈r M⊒M′)
    with catchup-lemma vV′ M⊒M′
catchup-lemma {σ = σ} (vV′ ⟨ i ⟩)
    (⊒cast- {M′ = M′} {q = q} {r = r} {s = s}
      qᶜ q⨟s≈r M⊒M′)
    | χs , W , Δ′ , Π , Π′ , π ,
      vW , M↠W , Δ′≡ , Π≡ , Π′≡ , π⊒ , W⊒M′ =
  -- Same as `⊒cast+`: the recursive narrowing is available, but the cast
  -- typing/equivalence side conditions must be transported to the emitted
  -- Δ′/store-prefix context before `⊒cast-` can be rebuilt.
  χs , W , Δ′ , Π , Π′ , π ,
  vW ,
  M↠W ,
  Δ′≡ ,
  Π≡ ,
  Π′≡ ,
  π⊒ ,
  subst
    (λ T → Δ′ ∣ combineStoreNrw π σ ∣ []
      ⊢ W ⊒ T ∶ applyCoercions χs r)
    (sym (applyTerms-cast χs M′ s))
    (⊒cast-
      (catchup-coercion-typing-transport
        {σ = σ} {π = π} {χs = χs}
        qᶜ Δ′≡ Π≡ Π′≡ π⊒)
      (catchup-compose-left-transport
        {σ = σ} {π = π} {χs = χs} {q = q} {s = s} {r = r}
        q⨟s≈r Δ′≡ Π≡ Π′≡ π⊒)
      W⊒M′)
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    with cast-dual-↠ {c = t} M↠W₁
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | M-t↠W₁-t
    with left-widening-lemma
           {Δ = Δ₁} {σ = combineStoreNrw π₁ σ}
           {p = applyCoercions χs₁ p}
           {r = applyCoercions χs₁ r}
           {t = applyCoercions χs₁ t}
           vW₁
           (catchup-coercion-typing-transport
             {σ = σ} {π = π₁} {χs = χs₁} {p = p}
             pᶜ Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           (catchup-compose-right-transport
             {σ = σ} {π = π₁} {χs = χs₁}
             {r = r} {t = t} {p = p}
             r≈t⨟p Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           W₁⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast+⊒ {p = p} {r = r} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | M-t↠W₁-t
    | χs₂ , W₂ , Δ₂ , Π₂ , Π₂′ , π₂ ,
      vW₂ , W₁-t↠W₂ , Δ₂≡ , Π₂≡ , Π₂′≡ , π₂⊒ , W₂⊒V =
  -- Catch up `M` to the value `W₁`, lift that reduction through the surrounding
  -- dual cast, invoke the value-level Left Widening Lemma on the transformed
  -- cast, and combine the two emitted source-only store prefixes.
  χs₁ ++ χs₂ , W₂ , Δ₂ ,
  srcStoreⁿ (combineStoreNrw π₂ π₁) , [] ,
  combineStoreNrw π₂ π₁ ,
  vW₂ ,
  ↠-trans M-t↠W₁-t W₁-t↠W₂ ,
  trans Δ₂≡
    (trans (cong (applyTyCtxs χs₂) Δ₁≡)
      (sym (applyTyCtxs-++ χs₁ χs₂ Δ))) ,
  combineStoreNrw-applyStores
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ ,
  refl ,
  combineStoreNrw-empty-⊒ˢ
    (subst (λ Π′ → _ ⊢ π₂ ꞉ _ ⊒ˢ Π′) Π₂′≡ π₂⊒)
    (⊒ˢ-empty-anyᵗ Δ₂
      (subst (λ Π′ → _ ⊢ π₁ ꞉ _ ⊒ˢ Π′) Π₁′≡ π₁⊒)) ,
  subst
    (λ c → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
      ⊢ W₂ ⊒ applyTerms (χs₁ ++ χs₂) V ∶ c)
    (sym (applyCoercions-++ χs₁ χs₂ r))
    (subst
      (λ T → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
        ⊢ W₂ ⊒ T ∶ applyCoercions χs₂ (applyCoercions χs₁ r))
      (sym (applyTerms-++ χs₁ χs₂ V))
      (subst
        (λ τ → Δ₂ ∣ τ ∣ [] ⊢ W₂
          ⊒ applyTerms χs₂ (applyTerms χs₁ V) ∶
            applyCoercions χs₂ (applyCoercions χs₁ r))
        (sym (combineStoreNrw-assoc π₂ π₁ σ))
        W₂⊒V))
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    with catchup-lemma vV M⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    with cast-↠ {c = t} M↠W₁
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | Mt↠W₁t
    with left-narrowing-lemma
           {Δ = Δ₁} {σ = combineStoreNrw π₁ σ}
           {p = applyCoercions χs₁ p}
           {t = applyCoercions χs₁ t}
           vW₁
           (catchup-coercion-typing-transport
             {σ = σ} {π = π₁} {χs = χs₁} {p = p}
             pᶜ Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           (catchup-compose-right-transport
             {σ = σ} {π = π₁} {χs = χs₁}
             {t = t} {p = p}
             r≈t⨟p Δ₁≡ Π₁≡ Π₁′≡ π₁⊒)
           W₁⊒V
catchup-lemma {Δ = Δ} {σ = σ} {V = V} vV
    (cast-⊒ {p = p} {t = t} pᶜ r≈t⨟p M⊒V)
    | χs₁ , W₁ , Δ₁ , Π₁ , Π₁′ , π₁ ,
      vW₁ , M↠W₁ , Δ₁≡ , Π₁≡ , Π₁′≡ , π₁⊒ , W₁⊒V
    | Mt↠W₁t
    | χs₂ , W₂ , Δ₂ , Π₂ , Π₂′ , π₂ ,
      vW₂ , W₁t↠W₂ , Δ₂≡ , Π₂≡ , Π₂′≡ , π₂⊒ , W₂⊒V =
  -- Same structure for Left Narrowing: the non-value source is handled by the
  -- recursive catchup call, and the paper lemma is applied only to the caught-up
  -- value, again using the transformed cast and composed source-only prefix.
  χs₁ ++ χs₂ , W₂ , Δ₂ ,
  srcStoreⁿ (combineStoreNrw π₂ π₁) , [] ,
  combineStoreNrw π₂ π₁ ,
  vW₂ ,
  ↠-trans Mt↠W₁t W₁t↠W₂ ,
  trans Δ₂≡
    (trans (cong (applyTyCtxs χs₂) Δ₁≡)
      (sym (applyTyCtxs-++ χs₁ χs₂ Δ))) ,
  combineStoreNrw-applyStores
    {χs₂ = χs₂} {χs₁ = χs₁}
    π₂⊒ Π₂≡ Π₂′≡ π₁⊒ Π₁≡ Π₁′≡ ,
  refl ,
  combineStoreNrw-empty-⊒ˢ
    (subst (λ Π′ → _ ⊢ π₂ ꞉ _ ⊒ˢ Π′) Π₂′≡ π₂⊒)
    (⊒ˢ-empty-anyᵗ Δ₂
      (subst (λ Π′ → _ ⊢ π₁ ꞉ _ ⊒ˢ Π′) Π₁′≡ π₁⊒)) ,
  subst
    (λ c → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
      ⊢ W₂ ⊒ applyTerms (χs₁ ++ χs₂) V ∶ c)
    (sym (applyCoercions-++ χs₁ χs₂ p))
    (subst
      (λ T → Δ₂ ∣ combineStoreNrw (combineStoreNrw π₂ π₁) σ ∣ []
        ⊢ W₂ ⊒ T ∶ applyCoercions χs₂ (applyCoercions χs₁ p))
      (sym (applyTerms-++ χs₁ χs₂ V))
      (subst
        (λ τ → Δ₂ ∣ τ ∣ [] ⊢ W₂
          ⊒ applyTerms χs₂ (applyTerms χs₁ V) ∶
            applyCoercions χs₂ (applyCoercions χs₁ p))
        (sym (combineStoreNrw-assoc π₂ π₁ σ))
        W₂⊒V))
