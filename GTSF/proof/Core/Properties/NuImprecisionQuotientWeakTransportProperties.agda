module
  proof.Core.Properties.NuImprecisionQuotientWeakTransportProperties
  where

-- File Charter:
--   * Proves that quotient arrow components commute with arbitrary weak-step
--     type transport, including a leading target allocation.
--   * Centralizes the quotient and permutation reindexing algebra shared by
--     quotient-down transport and right-value catch-up.
--   * Contains no simulation recursion, term relation, postulate, or hole.

open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import ForallPermutation using
  ( _≈∀_
  ; _∣_⊢_⊑ᵖ_⊣_
  ; ≈∀-arrow-components
  ; ≈∀-arrow-left
  ; ≈∀-arrow-right
  ; quotientᵖ
  ; ⊑ᵖ-arrow-components
  )
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_; _↦_)
open import NuReduction using
  (StoreChange; applyTy; applyTys; bind; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import NuTerms using (Term)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; subst; trans)
open import Types using (Ty; TyCtx; _⇒_)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; sourceChanges
  ; targetTailChanges
  ; transportArrowCoherent
  ; transportArrowType
  ; transportType
  )
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using (≈∀-arrow-components-renameᵗ)
open import proof.Core.Properties.ReductionProperties using
  (applyTys-⇒)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using
  ( applyTy-preserves-≈∀
  ; applyTys-preserves-≈∀
  ; weak-one-step-transport-quotientᵀ
  )


applyTys-⇒-leading :
  ∀ χ χs A B →
  applyTys-⇒ (χ ∷ χs) A B ≡
    trans
      (cong (applyTys χs) (applyTys-⇒ (χ ∷ []) A B))
      (applyTys-⇒ χs (applyTy χ A) (applyTy χ B))
applyTys-⇒-leading keep χs A B =
  refl
applyTys-⇒-leading (bind C) χs A B =
  refl


applyTy-preserves-arrow-≈∀ :
  ∀ {χ A A′ B B′} →
  A ⇒ B ≈∀ A′ ⇒ B′ →
  applyTy χ A ⇒ applyTy χ B ≈∀ applyTy χ A′ ⇒ applyTy χ B′
applyTy-preserves-arrow-≈∀ {χ = χ} {A = A} {A′ = A′}
    {B = B} {B′ = B′} equivalence =
  subst
    (λ X → X ≈∀ applyTy χ A′ ⇒ applyTy χ B′)
    (applyTys-⇒ (χ ∷ []) A B)
    (subst
      (λ X → applyTy χ (A ⇒ B) ≈∀ X)
      (applyTys-⇒ (χ ∷ []) A′ B′)
      (applyTy-preserves-≈∀ {χ = χ} equivalence))


applyTys-preserves-arrow-≈∀ :
  ∀ {χs A A′ B B′} →
  A ⇒ B ≈∀ A′ ⇒ B′ →
  applyTys χs A ⇒ applyTys χs B
    ≈∀ applyTys χs A′ ⇒ applyTys χs B′
applyTys-preserves-arrow-≈∀ {χs = χs} {A = A} {A′ = A′}
    {B = B} {B′ = B′} equivalence =
  subst
    (λ X → X ≈∀ applyTys χs A′ ⇒ applyTys χs B′)
    (applyTys-⇒ χs A B)
    (subst
      (λ X → applyTys χs (A ⇒ B) ≈∀ X)
      (applyTys-⇒ χs A′ B′)
      (applyTys-preserves-≈∀ {χs = χs} equivalence))


≈∀-arrow-components-applyTy :
  ∀ {χ A A′ B B′}
    (equivalence : A ⇒ B ≈∀ A′ ⇒ B′) →
  ≈∀-arrow-components
      (applyTy-preserves-arrow-≈∀ {χ = χ} equivalence) ≡
    ( applyTy-preserves-≈∀ {χ = χ}
        (proj₁ (≈∀-arrow-components equivalence))
    , applyTy-preserves-≈∀ {χ = χ}
        (proj₂ (≈∀-arrow-components equivalence))
    )
≈∀-arrow-components-applyTy {χ = keep} equivalence =
  refl
≈∀-arrow-components-applyTy {χ = bind C} equivalence =
  ≈∀-arrow-components-renameᵗ equivalence


≈∀-arrow-components-applyTys :
  ∀ {χs A A′ B B′}
    (equivalence : A ⇒ B ≈∀ A′ ⇒ B′) →
  ≈∀-arrow-components
      (applyTys-preserves-arrow-≈∀ {χs = χs} equivalence) ≡
    ( applyTys-preserves-≈∀ {χs = χs}
        (proj₁ (≈∀-arrow-components equivalence))
    , applyTys-preserves-≈∀ {χs = χs}
        (proj₂ (≈∀-arrow-components equivalence))
    )
≈∀-arrow-components-applyTys {χs = []} equivalence =
  refl
≈∀-arrow-components-applyTys {χs = keep ∷ χs} equivalence
    rewrite ≈∀-arrow-components-applyTy {χ = keep} equivalence
          | ≈∀-arrow-components-applyTys {χs = χs}
              (applyTy-preserves-≈∀ {χ = keep} equivalence) =
  refl
≈∀-arrow-components-applyTys {χs = bind C ∷ χs} equivalence
    rewrite ≈∀-arrow-components-applyTy {χ = bind C} equivalence
          | ≈∀-arrow-components-applyTys {χs = χs}
              (applyTy-preserves-≈∀ {χ = bind C} equivalence) =
  cong
    (λ components →
      ( applyTys-preserves-≈∀ {χs = χs} (proj₁ components)
      , applyTys-preserves-≈∀ {χs = χs} (proj₂ components)
      ))
    (≈∀-arrow-components-renameᵗ equivalence)


binary-subst-commute :
  ∀ {A B : Set} (P : A → B → Set)
    {x x′ : A} {y y′ : B}
    (source-eq : x ≡ x′)
    (target-eq : y ≡ y′)
    (proof : P x y) →
  subst (P x′) target-eq
      (subst (λ source → P source y) source-eq proof) ≡
    subst (λ source → P source y′) source-eq
      (subst (P x) target-eq proof)
binary-subst-commute P refl refl proof =
  refl


applyTys-preserves-arrow-≈∀-reindex :
  ∀ {χs A A′ B B′}
    (equivalence : A ⇒ B ≈∀ A′ ⇒ B′) →
  subst
      (λ target →
        applyTys χs A ⇒ applyTys χs B ≈∀ target)
      (applyTys-⇒ χs A′ B′)
      (subst
        (λ source →
          source ≈∀ applyTys χs (A′ ⇒ B′))
        (applyTys-⇒ χs A B)
        (applyTys-preserves-≈∀ {χs = χs} equivalence)) ≡
    applyTys-preserves-arrow-≈∀ {χs = χs} equivalence
applyTys-preserves-arrow-≈∀-reindex
    {χs = χs} {A = A} {A′ = A′} {B = B} {B′ = B′}
    equivalence =
  binary-subst-commute
    _≈∀_
    (applyTys-⇒ χs A B)
    (applyTys-⇒ χs A′ B′)
    (applyTys-preserves-≈∀ {χs = χs} equivalence)


quotientᵖ-reindex :
  ∀ {Φ Δᴸ Δᴿ A Ā B B̄ C C̄ D D̄}
    (source-eq : A ≡ Ā)
    (target-eq : B ≡ B̄)
    (left-middle-eq : C ≡ C̄)
    (right-middle-eq : D ≡ D̄)
    (left : A ≈∀ C)
    (middle : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ)
    (right : D ≈∀ B) →
  subst (λ T → Φ ∣ Δᴸ ⊢ Ā ⊑ᵖ T ⊣ Δᴿ) target-eq
      (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ᵖ B ⊣ Δᴿ) source-eq
        (quotientᵖ left middle right)) ≡
    quotientᵖ
      (subst (λ T → Ā ≈∀ T) left-middle-eq
        (subst (λ S → S ≈∀ C) source-eq left))
      (subst (λ T → Φ ∣ Δᴸ ⊢ C̄ ⊑ T ⊣ Δᴿ) right-middle-eq
        (subst (λ S → Φ ∣ Δᴸ ⊢ S ⊑ D ⊣ Δᴿ)
          left-middle-eq middle))
      (subst (λ T → D̄ ≈∀ T) target-eq
        (subst (λ S → S ≈∀ B) right-middle-eq right))
quotientᵖ-reindex refl refl refl refl left middle right =
  refl


quotientᵖ-middle-cong :
  ∀ {Φ Δᴸ Δᴿ A B C D}
    (left : A ≈∀ C)
    (right : D ≈∀ B)
    {middle middle′ : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ} →
  middle ≡ middle′ →
  quotientᵖ left middle right ≡ quotientᵖ left middle′ right
quotientᵖ-middle-cong left right refl =
  refl


quotientᵖ-cong :
  ∀ {Φ Δᴸ Δᴿ A B C D}
    {left left′ : A ≈∀ C}
    {middle middle′ : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ}
    {right right′ : D ≈∀ B} →
  left ≡ left′ →
  middle ≡ middle′ →
  right ≡ right′ →
  quotientᵖ left middle right ≡
    quotientᵖ left′ middle′ right′
quotientᵖ-cong refl refl refl =
  refl


quotientᵖ-arrow-components-explicit :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ D D′}
    (left : A ⇒ B ≈∀ C ⇒ D)
    (middle-domain : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (middle-codomain : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ)
    (right : C′ ⇒ D′ ≈∀ A′ ⇒ B′) →
  ⊑ᵖ-arrow-components
      (quotientᵖ left
        (middle-domain ↦ middle-codomain) right) ≡
    ( quotientᵖ
        (proj₁ (≈∀-arrow-components left))
        middle-domain
        (proj₁ (≈∀-arrow-components right))
    , quotientᵖ
        (proj₂ (≈∀-arrow-components left))
        middle-codomain
        (proj₂ (≈∀-arrow-components right))
    )
quotientᵖ-arrow-components-explicit
    left middle-domain middle-codomain right
    with ≈∀-arrow-right left
       | ≈∀-arrow-left right
quotientᵖ-arrow-components-explicit
    left middle-domain middle-codomain right
    | C , D , refl
    | C′ , D′ , refl
    with ≈∀-arrow-components left
       | ≈∀-arrow-components right
quotientᵖ-arrow-components-explicit
    left middle-domain middle-codomain right
    | C , D , refl
    | C′ , D′ , refl
    | left-domain , left-codomain
    | right-domain , right-codomain =
  refl


⊑ᵖ-arrow-components-cong :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′}
    {q q′ : Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ} →
  q ≡ q′ →
  ⊑ᵖ-arrow-components q ≡ ⊑ᵖ-arrow-components q′
⊑ᵖ-arrow-components-cong refl =
  refl


quotientᵖ-arrow-components-cong :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′ C C′ D D′}
    {left left′ : (A ≈∀ C) × (B ≈∀ D)}
    {right right′ : (C′ ≈∀ A′) × (D′ ≈∀ B′)}
    (middle-domain : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (middle-codomain : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  left ≡ left′ →
  right ≡ right′ →
  _≡_
    { A =
      (Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ) ×
      (Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ)
    }
    ( quotientᵖ (proj₁ left) middle-domain (proj₁ right)
    , quotientᵖ (proj₂ left) middle-codomain (proj₂ right)
    )
    ( quotientᵖ (proj₁ left′) middle-domain (proj₁ right′)
    , quotientᵖ (proj₂ left′) middle-codomain (proj₂ right′)
    )
quotientᵖ-arrow-components-cong
    middle-domain middle-codomain refl refl =
  refl


weak-one-step-transport-quotient-arrow-endpointsᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A₀ B₀ A A′ B B′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {χ : StoreChange} →
    (result : WeakOneStepResult ρ M N′ A₀ B₀ χ) →
  Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ →
  resultCtx result ∣ resultLeftCtx result
    ⊢ applyTys (sourceChanges result) A ⇒
        applyTys (sourceChanges result) B
      ⊑ᵖ
        applyTys (χ ∷ targetTailChanges result) A′ ⇒
        applyTys (χ ∷ targetTailChanges result) B′
    ⊣ resultRightCtx result
weak-one-step-transport-quotient-arrow-endpointsᵀ
    {A = A} {A′ = A′} {B = B} {B′ = B′} {χ = χ}
    result qF =
  subst
    (λ X → resultCtx result ∣ resultLeftCtx result
      ⊢ applyTys (sourceChanges result) A ⇒
          applyTys (sourceChanges result) B
        ⊑ᵖ X ⊣ resultRightCtx result)
    target-eq
    (subst
      (λ X → resultCtx result ∣ resultLeftCtx result
        ⊢ X ⊑ᵖ applyTys (χ ∷ targetTailChanges result)
            (A′ ⇒ B′)
        ⊣ resultRightCtx result)
      (applyTys-⇒ (sourceChanges result) A B)
      (weak-one-step-transport-quotientᵀ result qF))
  where
  target-eq =
    applyTys-⇒ (χ ∷ targetTailChanges result) A′ B′


transport-arrow-type-combined :
  ∀ {Φ Δᴸ Δᴿ M N′ A₀ B₀ C C′ D D′}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {χ : StoreChange}
    (result : WeakOneStepResult ρ M N′ A₀ B₀ χ)
    (pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ)
    (pD : Φ ∣ Δᴸ ⊢ D ⊑ D′ ⊣ Δᴿ) →
  subst
    (λ T → resultCtx result ∣ resultLeftCtx result
      ⊢ applyTys (sourceChanges result) C ⇒
          applyTys (sourceChanges result) D
        ⊑ T ⊣ resultRightCtx result)
    (applyTys-⇒ (χ ∷ targetTailChanges result) C′ D′)
    (subst
      (λ S → resultCtx result ∣ resultLeftCtx result
        ⊢ S ⊑ applyTys (targetTailChanges result)
            (applyTy χ (C′ ⇒ D′))
          ⊣ resultRightCtx result)
      (applyTys-⇒ (sourceChanges result) C D)
      (transportType result (pC ↦ pD))) ≡
  transportArrowType result pC pD
transport-arrow-type-combined
    {C = C} {C′ = C′} {D = D} {D′ = D′} {χ = χ}
    result pC pD =
  cong
    (λ target-eq →
      subst
        (λ T → resultCtx result ∣ resultLeftCtx result
          ⊢ applyTys (sourceChanges result) C ⇒
              applyTys (sourceChanges result) D
            ⊑ T ⊣ resultRightCtx result)
        target-eq
        (subst
          (λ S → resultCtx result ∣ resultLeftCtx result
            ⊢ S ⊑ applyTys (targetTailChanges result)
                (applyTy χ (C′ ⇒ D′))
              ⊣ resultRightCtx result)
          (applyTys-⇒ (sourceChanges result) C D)
          (transportType result (pC ↦ pD))))
    (applyTys-⇒-leading
      χ (targetTailChanges result) C′ D′)


weak-one-step-transport-quotient-arrow-components :
  ∀ {Φ Δᴸ Δᴿ M N′ A₀ B₀ A A′ B B′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {χ : StoreChange} →
    (result : WeakOneStepResult ρ M N′ A₀ B₀ χ) →
  (type-coherence : WeakOneStepTypeCoherence result) →
  (qF : Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ) →
  ⊑ᵖ-arrow-components
      (weak-one-step-transport-quotient-arrow-endpointsᵀ result qF) ≡
    ( weak-one-step-transport-quotientᵀ result
        (proj₁ (⊑ᵖ-arrow-components qF))
    , weak-one-step-transport-quotientᵀ result
        (proj₂ (⊑ᵖ-arrow-components qF))
    )
weak-one-step-transport-quotient-arrow-components
    {A = A} {A′ = A′} {B = B} {B′ = B′} {χ = χ}
    result type-coherence (quotientᵖ left middle right)
    with ≈∀-arrow-right left
       | ≈∀-arrow-left right
weak-one-step-transport-quotient-arrow-components
    {A = A} {A′ = A′} {B = B} {B′ = B′} {χ = χ}
    result type-coherence (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    with ≈∀-arrow-components left
       | middle
       | ≈∀-arrow-components right
weak-one-step-transport-quotient-arrow-components
    {A = A} {A′ = A′} {B = B} {B′ = B′} {χ = χ}
    result type-coherence (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain =
  trans
    (⊑ᵖ-arrow-components-cong
      {Φ = resultCtx result}
      {Δᴸ = resultLeftCtx result}
      {Δᴿ = resultRightCtx result}
      {A = applyTys (sourceChanges result) A}
      {A′ = applyTys (χ ∷ targetTailChanges result) A′}
      {B = applyTys (sourceChanges result) B}
      {B′ = applyTys (χ ∷ targetTailChanges result) B′}
      (quotientᵖ-reindex
        {Φ = resultCtx result}
        {Δᴸ = resultLeftCtx result}
        {Δᴿ = resultRightCtx result}
        {A = applyTys (sourceChanges result) (A ⇒ B)}
        {Ā = applyTys (sourceChanges result) A ⇒
          applyTys (sourceChanges result) B}
        {B = applyTys (χ ∷ targetTailChanges result) (A′ ⇒ B′)}
        {B̄ = applyTys (χ ∷ targetTailChanges result) A′ ⇒
          applyTys (χ ∷ targetTailChanges result) B′}
        {C = applyTys (sourceChanges result) (C ⇒ D)}
        {C̄ = applyTys (sourceChanges result) C ⇒
          applyTys (sourceChanges result) D}
        {D = applyTys (χ ∷ targetTailChanges result) (C′ ⇒ D′)}
        {D̄ = applyTys (χ ∷ targetTailChanges result) C′ ⇒
          applyTys (χ ∷ targetTailChanges result) D′}
        (applyTys-⇒ (sourceChanges result) A B)
        (applyTys-⇒ (χ ∷ targetTailChanges result) A′ B′)
        (applyTys-⇒ (sourceChanges result) C D)
        (applyTys-⇒ (χ ∷ targetTailChanges result) C′ D′)
        (applyTys-preserves-≈∀
          {χs = sourceChanges result} left)
        (transportType result
          (middle-domain ↦ middle-codomain))
        (applyTys-preserves-≈∀
          {χs = χ ∷ targetTailChanges result} right)))
    (trans
      (⊑ᵖ-arrow-components-cong
        (quotientᵖ-middle-cong
          (subst
            (λ T → applyTys (sourceChanges result) A ⇒
              applyTys (sourceChanges result) B ≈∀ T)
            (applyTys-⇒ (sourceChanges result) C D)
            (subst
              (λ S → S ≈∀
                applyTys (sourceChanges result) (C ⇒ D))
              (applyTys-⇒ (sourceChanges result) A B)
              (applyTys-preserves-≈∀
                {χs = sourceChanges result} left)))
          (subst
            (λ T → applyTys (χ ∷ targetTailChanges result) C′ ⇒
              applyTys (χ ∷ targetTailChanges result) D′ ≈∀ T)
            (applyTys-⇒
              (χ ∷ targetTailChanges result) A′ B′)
            (subst
              (λ S → S ≈∀
                applyTys (χ ∷ targetTailChanges result) (A′ ⇒ B′))
              (applyTys-⇒
                (χ ∷ targetTailChanges result) C′ D′)
              (applyTys-preserves-≈∀
                {χs = χ ∷ targetTailChanges result} right)))
          (transport-arrow-type-combined
            result middle-domain middle-codomain)))
      (trans
      (⊑ᵖ-arrow-components-cong
        {Φ = resultCtx result}
        {Δᴸ = resultLeftCtx result}
        {Δᴿ = resultRightCtx result}
        {A = applyTys (sourceChanges result) A}
        {A′ = applyTys (χ ∷ targetTailChanges result) A′}
        {B = applyTys (sourceChanges result) B}
        {B′ = applyTys (χ ∷ targetTailChanges result) B′}
        (quotientᵖ-cong
          {Φ = resultCtx result}
          {Δᴸ = resultLeftCtx result}
          {Δᴿ = resultRightCtx result}
          {A = applyTys (sourceChanges result) A ⇒
            applyTys (sourceChanges result) B}
          {B = applyTys (χ ∷ targetTailChanges result) A′ ⇒
            applyTys (χ ∷ targetTailChanges result) B′}
          {C = applyTys (sourceChanges result) C ⇒
            applyTys (sourceChanges result) D}
          {D = applyTys (χ ∷ targetTailChanges result) C′ ⇒
            applyTys (χ ∷ targetTailChanges result) D′}
          {middle =
            transportArrowType
              result middle-domain middle-codomain}
          {middle′ =
            transportArrowType
              result middle-domain middle-codomain}
          (applyTys-preserves-arrow-≈∀-reindex
            {χs = sourceChanges result} left)
          refl
          (applyTys-preserves-arrow-≈∀-reindex
            {χs = χ ∷ targetTailChanges result} right)))
      (trans
        (⊑ᵖ-arrow-components-cong
          {Φ = resultCtx result}
          {Δᴸ = resultLeftCtx result}
          {Δᴿ = resultRightCtx result}
          {A = applyTys (sourceChanges result) A}
          {A′ = applyTys (χ ∷ targetTailChanges result) A′}
          {B = applyTys (sourceChanges result) B}
          {B′ = applyTys (χ ∷ targetTailChanges result) B′}
          (quotientᵖ-middle-cong
            {Φ = resultCtx result}
            {Δᴸ = resultLeftCtx result}
            {Δᴿ = resultRightCtx result}
            {A = applyTys (sourceChanges result) A ⇒
              applyTys (sourceChanges result) B}
            {B = applyTys (χ ∷ targetTailChanges result) A′ ⇒
              applyTys (χ ∷ targetTailChanges result) B′}
            {C = applyTys (sourceChanges result) C ⇒
              applyTys (sourceChanges result) D}
            {D = applyTys (χ ∷ targetTailChanges result) C′ ⇒
              applyTys (χ ∷ targetTailChanges result) D′}
            (applyTys-preserves-arrow-≈∀
              {χs = sourceChanges result} left)
            (applyTys-preserves-arrow-≈∀
              {χs = χ ∷ targetTailChanges result} right)
            (transportArrowCoherent
              type-coherence middle-domain middle-codomain)))
        (trans
          (quotientᵖ-arrow-components-explicit
            (applyTys-preserves-arrow-≈∀
              {χs = sourceChanges result} left)
            (transportType result middle-domain)
            (transportType result middle-codomain)
            (applyTys-preserves-arrow-≈∀
              {χs = χ ∷ targetTailChanges result} right))
          (quotientᵖ-arrow-components-cong
            (transportType result middle-domain)
            (transportType result middle-codomain)
            (≈∀-arrow-components-applyTys
              {χs = sourceChanges result} left)
            (≈∀-arrow-components-applyTys
              {χs = χ ∷ targetTailChanges result} right))))))


weak-one-step-transport-quotient-arrow-components-at :
  ∀ {Φ Δᴸ Δᴿ M N′ A₀ B₀ A A′ B B′}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {χ : StoreChange} →
    (result : WeakOneStepResult ρ M N′ A₀ B₀ χ) →
  (type-coherence : WeakOneStepTypeCoherence result) →
  {qF : Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ}
  {qA : Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ}
  {qB : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ} →
  ⊑ᵖ-arrow-components qF ≡ (qA , qB) →
  ⊑ᵖ-arrow-components
      (weak-one-step-transport-quotient-arrow-endpointsᵀ result qF) ≡
    ( weak-one-step-transport-quotientᵀ result qA
    , weak-one-step-transport-quotientᵀ result qB
    )
weak-one-step-transport-quotient-arrow-components-at
    {χ = χ} result type-coherence {qF = qF} refl =
  weak-one-step-transport-quotient-arrow-components
    result type-coherence qF
