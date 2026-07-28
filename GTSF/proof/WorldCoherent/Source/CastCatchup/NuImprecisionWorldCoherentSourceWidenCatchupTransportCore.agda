module
  proof.WorldCoherent.Source.CastCatchup.NuImprecisionWorldCoherentSourceWidenCatchupTransportCore
  where

-- File Charter:
--   * Provides common composition, reduction, and transported widening-typing
--     support for the admissible source-widen catch-up cases.
--   * Is independent of the individual inert, identity, sequence, and
--     source-only instantiation proofs.
--   * Contains no source-widen dispatcher, postulate, hole, or termination
--     bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
import Coercions as C
open import Coercions using (_︔_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import ImprecisionComposition using (⌊_⌋; _；_≋_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
import NarrowWiden as NW
open import NarrowWiden using
  ( Widening
  ; widen-weaken
  ; widen-renameᵗ
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using
  ( applyStores
  ; applyTyCtxs
  ; applyTys
  ; bind
  ; keep
  ; pure-step
  ; β-seq
  ; _—→[_]_
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (Value; _⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Store using (StoreIncl-drop)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; cast-weaken
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportType
  ; weakIndexedResult
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (imprecision-composition-shape-transport)
open import
  proof.Core.Properties.ReductionProperties
  using (applyCoercions)
open import
  proof.Core.Properties.TypePreservation
  using
  ( modeRename-suc-weakenCast
  ; seal★-weaken
  ; seal★-weakenCast-bind
  )
open import
  proof.Core.Properties.TypeProperties
  using (TyRenameWf-suc)
open import
  proof.Core.Properties.NuWideningTransport
  using (apply-widens-typing)


transport-source-widening-composition :
  ∀ {Φ Δᴸ Δᴿ M M′ A B χ C D E s}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ C ⊑ E ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    (result : WeakOneStepResult ρ M M′ A B χ) →
  WeakOneStepTypeCoherence result →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  s ； ⌊ transportType result q ⌋ ≋
    ⌊ transportType result p ⌋
transport-source-widening-composition result coherence comp =
  imprecision-composition-shape-transport
    refl
    (transportShapeCoherent coherence _)
    (transportShapeCoherent coherence _)
    comp


applyCoercions-seq :
  ∀ χs s t →
  applyCoercions χs (s ︔ t) ≡
    applyCoercions χs s ︔ applyCoercions χs t
applyCoercions-seq [] s t = refl
applyCoercions-seq (keep ∷ χs) s t =
  applyCoercions-seq χs s t
applyCoercions-seq (bind A ∷ χs) s t =
  applyCoercions-seq χs (C.⇑ᶜ s) (C.⇑ᶜ t)


post-catchup-β-seq :
  ∀ χs {V s t} →
  Value V →
  V ⟨ applyCoercions χs (s ︔ t) ⟩ —→[ keep ]
    V ⟨ applyCoercions χs s ⟩ ⟨ applyCoercions χs t ⟩
post-catchup-β-seq χs {s = s} {t = t} vV
    rewrite applyCoercions-seq χs s t =
  pure-step (β-seq vV)


applyCoercions-preserves-Widening :
  ∀ χs {c} →
  Widening c →
  Widening (applyCoercions χs c)
applyCoercions-preserves-Widening [] cʷ = cʷ
applyCoercions-preserves-Widening (keep ∷ χs) cʷ =
  applyCoercions-preserves-Widening χs cʷ
applyCoercions-preserves-Widening (bind A ∷ χs) cʷ =
  applyCoercions-preserves-Widening χs (NW.renameʷ suc cʷ)


apply-widens-typing₂ :
  ∀ {χs μ Δ Σ s t A C B} →
  CastMode μ →
  SealModeStore★ μ Σ →
  μ ∣ Δ ∣ Σ ⊢ s ∶ A ⊑ C →
  μ ∣ Δ ∣ Σ ⊢ t ∶ C ⊑ B →
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (applyStores χs Σ) ×
    (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
      ⊢ applyCoercions χs s ∶ applyTys χs A ⊑ applyTys χs C) ×
    (μ′ ∣ applyTyCtxs χs Δ ∣ applyStores χs Σ
      ⊢ applyCoercions χs t ∶ applyTys χs C ⊑ applyTys χs B)
apply-widens-typing₂ {χs = []} {μ = μ} mode seal★ s⊑ t⊑ =
  μ , mode , seal★ , s⊑ , t⊑
apply-widens-typing₂ {χs = keep ∷ χs} mode seal★ s⊑ t⊑ =
  apply-widens-typing₂ {χs = χs} mode seal★ s⊑ t⊑
apply-widens-typing₂ {χs = bind Aχ ∷ χs} mode seal★ s⊑ t⊑ =
  apply-widens-typing₂ {χs = χs}
    (cast-weaken mode)
    (seal★-weakenCast-bind seal★)
    (widen-weaken ≤-refl StoreIncl-drop
      (widen-renameᵗ TyRenameWf-suc modeRename-suc-weakenCast s⊑))
    (widen-weaken ≤-refl StoreIncl-drop
      (widen-renameᵗ TyRenameWf-suc modeRename-suc-weakenCast t⊑))


indexed-source-precision :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = keep} {ρ = ρ} p) →
  let inner = weakIndexedResult indexed in
  resultCtx inner ∣ resultLeftCtx inner
    ⊢ applyTys (sourceChanges inner) A
      ⊑ applyTys (targetTailChanges inner) B
      ⊣ resultRightCtx inner
indexed-source-precision {p = p} indexed =
  transportType (weakIndexedResult indexed) p


result-widening-typingᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B C c μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ B ⊑ C →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = keep} {ρ = ρ⁺} p) →
  let inner = weakIndexedResult indexed in
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner)) ×
    (μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C)
result-widening-typingᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {c = c}
    prefix mode seal★ c⊑ indexed
    with apply-widens-typing
      {χs = sourceChanges (weakIndexedResult indexed)}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) c⊑)
result-widening-typingᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {c = c}
    prefix mode seal★ c⊑ indexed
    | μ′ , mode′ , seal★′ , c′⊑ =
  μ′ , mode′ , final-seal , final-cast
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) c
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C
  final-cast =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) c
          ∶ applyTys (sourceChanges inner) B
            ⊑ applyTys (sourceChanges inner) C)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) c
            ∶ applyTys (sourceChanges inner) B
              ⊑ applyTys (sourceChanges inner) C)
        (sym (sourceStoreResult inner)) c′⊑)


result-widening-typing₂ᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B C D s t μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ s ∶ B ⊑ C →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ t ∶ C ⊑ D →
  (indexed : WeakOneStepIndexedResult
    {M = M} {N′ = V′} {χ = keep} {ρ = ρ⁺} p) →
  let inner = weakIndexedResult indexed in
  ∃[ μ′ ]
    CastMode μ′ ×
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner)) ×
    (μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) s
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C) ×
    (μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) t
        ∶ applyTys (sourceChanges inner) C
          ⊑ applyTys (sourceChanges inner) D)
result-widening-typing₂ᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {D = D} {s = s} {t = t}
    prefix mode seal★ s⊑ t⊑ indexed
    with apply-widens-typing₂
      {χs = sourceChanges (weakIndexedResult indexed)}
      mode
      (seal★-weaken (leftStoreⁱ-prefix-inclusion prefix) seal★)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) s⊑)
      (widen-weaken ≤-refl
        (leftStoreⁱ-prefix-inclusion prefix) t⊑)
result-widening-typing₂ᵀ
    {Δᴸ = Δᴸ} {B = B} {C = C} {D = D} {s = s} {t = t}
    prefix mode seal★ s⊑ t⊑ indexed
    | μ′ , mode′ , seal★′ , s′⊑ , t′⊑ =
  μ′ , mode′ , final-seal , final-cast-s , final-cast-t
  where
  inner = weakIndexedResult indexed

  final-seal :
    SealModeStore★ μ′ (leftStoreⁱ (resultStore inner))
  final-seal =
    subst (SealModeStore★ μ′)
      (sym (sourceStoreResult inner)) seal★′

  final-cast-s :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) s
        ∶ applyTys (sourceChanges inner) B
          ⊑ applyTys (sourceChanges inner) C
  final-cast-s =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) s
          ∶ applyTys (sourceChanges inner) B
            ⊑ applyTys (sourceChanges inner) C)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) s
            ∶ applyTys (sourceChanges inner) B
              ⊑ applyTys (sourceChanges inner) C)
        (sym (sourceStoreResult inner)) s′⊑)

  final-cast-t :
    μ′ ∣ resultLeftCtx inner
      ∣ leftStoreⁱ (resultStore inner)
      ⊢ applyCoercions (sourceChanges inner) t
        ∶ applyTys (sourceChanges inner) C
          ⊑ applyTys (sourceChanges inner) D
  final-cast-t =
    subst
      (λ Δ → μ′ ∣ Δ ∣ leftStoreⁱ (resultStore inner)
        ⊢ applyCoercions (sourceChanges inner) t
          ∶ applyTys (sourceChanges inner) C
            ⊑ applyTys (sourceChanges inner) D)
      (sym (sourceCtxResult inner))
      (subst
        (λ Σ → μ′ ∣ applyTyCtxs (sourceChanges inner) Δᴸ ∣ Σ
          ⊢ applyCoercions (sourceChanges inner) t
            ∶ applyTys (sourceChanges inner) C
              ⊑ applyTys (sourceChanges inner) D)
        (sym (sourceStoreResult inner)) t′⊑)
