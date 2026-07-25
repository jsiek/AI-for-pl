module proof.Core.Properties.NuImprecisionQuotientBoundaryProperties where

-- File Charter:
--   * Transports proof-relevant quotient-boundary squares through left-only
--     and two-sided type renaming.
--   * Preserves the exact forall-permutation derivations used by the
--     canonical quotient-renaming operations.
--   * Factors the function-ground tag followed by the star identity out of
--     quotient-boundary squares, including symmetric and transitive
--     permutation evidence.
--   * Contains no term-imprecision, operational simulation, postulate, hole,
--     permissive option, or compatibility alias.

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import ForallPermutation using
  ( _≈∀_
  ; _∣_⊢_⊑ᵖ_⊣_
  ; ≈∀-refl
  ; ≈∀-sym
  ; ≈∀-trans
  ; ≈∀-⇒
  ; ≈∀-∀
  ; ≈∀-swap
  ; ≈∀-arrow-left
  ; ≈∀-arrow-right
  ; ≈∀-arrow-components
  ; quotientᵖ
  ; ⊑ᵖ-arrow-components
  )
open import ImprecisionComposition using
  ( ImprecisionShape
  ; id★ˢ
  ; _↦ˢ_
  ; ∀ˢ_
  ; tag_⇛ˢ_
  ; νˢ_
  ; _⊢_≈∀ˢ_
  ; source-perm-refl
  ; source-perm-sym
  ; source-perm-trans
  ; source-perm-↦
  ; source-perm-tag-⇛
  ; source-perm-∀
  ; source-perm-ν
  ; source-swap-∀∀
  ; source-swap-∀ν
  ; source-swap-ν∀
  ; source-swap-νν
  ; ⌊_⌋
  ; _；_≋_
  ; comp-id★
  ; comp-↦-tag
  ; comp-tag-⇛-id★
  ; comp-ν
  ; _；⌊_⌋≋ᵖ_；_
  ; quotient-boundary-square
  ; compose-right-id★
  )
open import ImprecisionWf using
  (ImpAssm; ImpCtx; _∣_⊢_⊑_⊣_; id★; _↦_; tag_⇛_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; refl; subst)
open import Types using
  (Renameᵗ; Ty; TyCtx; _⇒_; extᵗ; renameᵗ; `∀)
open import proof.Core.Permutation.ForallPermutationProperties using
  ( ≈∀-renameᵗ
  ; renameᵗ-swap01-ext²-commute
  ; ⊑ᵖ-rename-leftᵢ
  ; ⊑ᵖ-rename²ᵢ
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( imprecision-composition-shape-transport
  ; shape-rename
  ; shape-rename-left
  ; ⊑-rename-leftᵢ
  )
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ; ⊑-renameᵗ²ᵢ)


source-perm-double-all-body-subst :
  ∀ {A B C : Ty}
    {equivalence : `∀ (`∀ A) ≈∀ `∀ (`∀ B)}
    {s s′} →
  (eq : B ≡ C) →
  equivalence ⊢ s ≈∀ˢ s′ →
  subst
    (λ T → `∀ (`∀ A) ≈∀ `∀ (`∀ T))
    eq equivalence
    ⊢ s ≈∀ˢ s′
source-perm-double-all-body-subst refl shape = shape


source-perm-shape-rename :
  ∀ {τ A B s s′} {equivalence : A ≈∀ B} →
  equivalence ⊢ s ≈∀ˢ s′ →
  ≈∀-renameᵗ {τ = τ} equivalence ⊢ s ≈∀ˢ s′
source-perm-shape-rename source-perm-refl =
  source-perm-refl
source-perm-shape-rename (source-perm-sym shape) =
  source-perm-sym (source-perm-shape-rename shape)
source-perm-shape-rename (source-perm-trans left right) =
  source-perm-trans
    (source-perm-shape-rename left)
    (source-perm-shape-rename right)
source-perm-shape-rename (source-perm-↦ domain codomain) =
  source-perm-↦
    (source-perm-shape-rename domain)
    (source-perm-shape-rename codomain)
source-perm-shape-rename (source-perm-tag-⇛ domain codomain) =
  source-perm-tag-⇛
    (source-perm-shape-rename domain)
    (source-perm-shape-rename codomain)
source-perm-shape-rename (source-perm-∀ shape) =
  source-perm-∀ (source-perm-shape-rename shape)
source-perm-shape-rename (source-perm-ν shape) =
  source-perm-ν (source-perm-shape-rename shape)
source-perm-shape-rename {τ = τ}
    (source-swap-∀∀ {A = A}) =
  source-perm-double-all-body-subst
    (renameᵗ-swap01-ext²-commute τ A)
    source-swap-∀∀
source-perm-shape-rename {τ = τ}
    (source-swap-∀ν {A = A}) =
  source-perm-double-all-body-subst
    (renameᵗ-swap01-ext²-commute τ A)
    source-swap-∀ν
source-perm-shape-rename {τ = τ}
    (source-swap-ν∀ {A = A}) =
  source-perm-double-all-body-subst
    (renameᵗ-swap01-ext²-commute τ A)
    source-swap-ν∀
source-perm-shape-rename {τ = τ}
    (source-swap-νν {A = A}) =
  source-perm-double-all-body-subst
    (renameᵗ-swap01-ext²-commute τ A)
    source-swap-νν


quotient-boundary-square-rename-left :
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx}
    {τ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ}
    {s s′} →
  s ；⌊ p ⌋≋ᵖ q ； s′ →
  s ；⌊ ⊑-rename-leftᵢ τ assm hτ p ⌋≋ᵖ
    (⊑ᵖ-rename-leftᵢ τ assm hτ q) ； s′
quotient-boundary-square-rename-left
    {τ = τ} {assm = assm} {hτ = hτ}
    (quotient-boundary-square
      {middle = middle}
      source-shape left-composition target-shape right-composition) =
  quotient-boundary-square
    (source-perm-shape-rename {τ = τ} source-shape)
    (imprecision-composition-shape-transport
      refl (shape-rename-left assm hτ _) refl left-composition)
    target-shape
    (imprecision-composition-shape-transport
      (shape-rename-left assm hτ middle)
      refl refl right-composition)


quotient-boundary-square-rename² :
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
    {τ σ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} → a ∈ Φ →
      rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ}
    {s s′} →
  s ；⌊ p ⌋≋ᵖ q ； s′ →
  s ；⌊ ⊑-renameᵗ²ᵢ assm hτ hσ p ⌋≋ᵖ
    (⊑ᵖ-rename²ᵢ assm hτ hσ q) ； s′
quotient-boundary-square-rename²
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    (quotient-boundary-square
      {middle = middle}
      source-shape left-composition target-shape right-composition) =
  quotient-boundary-square
    (source-perm-shape-rename {τ = τ} source-shape)
    (imprecision-composition-shape-transport
      refl (shape-rename assm hτ hσ _) refl left-composition)
    (source-perm-shape-rename {τ = σ} target-shape)
    (imprecision-composition-shape-transport
      (shape-rename assm hτ hσ middle)
      refl refl right-composition)


rename-arrow-shape :
  ∀ {C : Ty} →
  (τ : Renameᵗ) →
  (∃[ A ] ∃[ B ] C ≡ A ⇒ B) →
  ∃[ A ] ∃[ B ] renameᵗ τ C ≡ A ⇒ B
rename-arrow-shape τ (A , B , refl) =
  renameᵗ τ A , renameᵗ τ B , refl


mutual
  ≈∀-arrow-right-renameᵗ :
    ∀ {τ A B C}
      (equivalence : A ⇒ B ≈∀ C) →
    ≈∀-arrow-right (≈∀-renameᵗ {τ = τ} equivalence) ≡
      rename-arrow-shape τ (≈∀-arrow-right equivalence)
  ≈∀-arrow-right-renameᵗ ≈∀-refl = refl
  ≈∀-arrow-right-renameᵗ (≈∀-sym equivalence) =
    ≈∀-arrow-left-renameᵗ equivalence
  ≈∀-arrow-right-renameᵗ {τ = τ}
      (≈∀-trans left right)
      with ≈∀-arrow-right left
         | ≈∀-arrow-right (≈∀-renameᵗ {τ = τ} left)
         | ≈∀-arrow-right-renameᵗ {τ = τ} left
  ≈∀-arrow-right-renameᵗ {τ = τ}
      (≈∀-trans left right)
      | C , D , refl
      | C′ , D′ , refl
      | refl =
    ≈∀-arrow-right-renameᵗ {τ = τ} right
  ≈∀-arrow-right-renameᵗ (≈∀-⇒ domain codomain) =
    refl

  ≈∀-arrow-left-renameᵗ :
    ∀ {τ A B C}
      (equivalence : C ≈∀ A ⇒ B) →
    ≈∀-arrow-left (≈∀-renameᵗ {τ = τ} equivalence) ≡
      rename-arrow-shape τ (≈∀-arrow-left equivalence)
  ≈∀-arrow-left-renameᵗ ≈∀-refl = refl
  ≈∀-arrow-left-renameᵗ (≈∀-sym equivalence) =
    ≈∀-arrow-right-renameᵗ equivalence
  ≈∀-arrow-left-renameᵗ {τ = τ}
      (≈∀-trans left right)
      with ≈∀-arrow-left right
         | ≈∀-arrow-left (≈∀-renameᵗ {τ = τ} right)
         | ≈∀-arrow-left-renameᵗ {τ = τ} right
  ≈∀-arrow-left-renameᵗ {τ = τ}
      (≈∀-trans left right)
      | C , D , refl
      | C′ , D′ , refl
      | refl =
    ≈∀-arrow-left-renameᵗ {τ = τ} left
  ≈∀-arrow-left-renameᵗ (≈∀-⇒ domain codomain) =
    refl


≈∀-arrow-components-renameᵗ :
  ∀ {τ A A′ B B′}
    (equivalence : A ⇒ B ≈∀ A′ ⇒ B′) →
  ≈∀-arrow-components (≈∀-renameᵗ {τ = τ} equivalence) ≡
    ( ≈∀-renameᵗ {τ = τ}
        (proj₁ (≈∀-arrow-components equivalence))
    , ≈∀-renameᵗ {τ = τ}
        (proj₂ (≈∀-arrow-components equivalence))
    )
≈∀-arrow-components-renameᵗ ≈∀-refl = refl
≈∀-arrow-components-renameᵗ
    (≈∀-sym equivalence) =
  cong
    (λ components →
      ≈∀-sym (proj₁ components) , ≈∀-sym (proj₂ components))
    (≈∀-arrow-components-renameᵗ equivalence)
≈∀-arrow-components-renameᵗ {τ = τ}
    (≈∀-trans left right)
    with ≈∀-arrow-right left
       | ≈∀-arrow-right (≈∀-renameᵗ {τ = τ} left)
       | ≈∀-arrow-right-renameᵗ {τ = τ} left
≈∀-arrow-components-renameᵗ {τ = τ}
    (≈∀-trans left right)
    | C , D , refl
    | C′ , D′ , refl
    | refl
    rewrite ≈∀-arrow-components-renameᵗ {τ = τ} left
          | ≈∀-arrow-components-renameᵗ {τ = τ} right =
  refl
≈∀-arrow-components-renameᵗ
    (≈∀-⇒ domain codomain) =
  refl


quotient-arrow-components-rename-left :
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx}
    {τ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {A A′ B B′ : Ty}
    (qF : Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ) →
  ⊑ᵖ-arrow-components (⊑ᵖ-rename-leftᵢ τ assm hτ qF) ≡
    ( ⊑ᵖ-rename-leftᵢ τ assm hτ
        (proj₁ (⊑ᵖ-arrow-components qF))
    , ⊑ᵖ-rename-leftᵢ τ assm hτ
        (proj₂ (⊑ᵖ-arrow-components qF))
    )
quotient-arrow-components-rename-left {τ = τ}
    (quotientᵖ left middle right)
    with ≈∀-arrow-right left
       | ≈∀-arrow-left right
quotient-arrow-components-rename-left {τ = τ}
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    with ≈∀-arrow-components left
       | middle
       | ≈∀-arrow-components right
quotient-arrow-components-rename-left {τ = τ}
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain
    with ≈∀-arrow-right (≈∀-renameᵗ {τ = τ} left)
       | ≈∀-arrow-components
           (≈∀-renameᵗ {τ = τ} left)
quotient-arrow-components-rename-left {τ = τ}
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain
    | renamed-C , renamed-D , refl
    | renamed-domain , renamed-codomain
    rewrite ≈∀-arrow-components-renameᵗ {τ = τ} left =
  refl


quotient-arrow-components-rename-left-at :
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx}
    {τ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {A A′ B B′ : Ty}
    {qF : Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ}
    {qA : Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ}
    {qB : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ} →
  ⊑ᵖ-arrow-components qF ≡ (qA , qB) →
  ⊑ᵖ-arrow-components (⊑ᵖ-rename-leftᵢ τ assm hτ qF) ≡
    ( ⊑ᵖ-rename-leftᵢ τ assm hτ qA
    , ⊑ᵖ-rename-leftᵢ τ assm hτ qB
    )
quotient-arrow-components-rename-left-at {qF = qF} refl =
  quotient-arrow-components-rename-left qF


quotient-arrow-components-rename² :
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
    {τ σ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} → a ∈ Φ →
      rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {A A′ B B′ : Ty}
    (qF : Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ) →
  ⊑ᵖ-arrow-components (⊑ᵖ-rename²ᵢ assm hτ hσ qF) ≡
    ( ⊑ᵖ-rename²ᵢ assm hτ hσ
        (proj₁ (⊑ᵖ-arrow-components qF))
    , ⊑ᵖ-rename²ᵢ assm hτ hσ
        (proj₂ (⊑ᵖ-arrow-components qF))
    )
quotient-arrow-components-rename² {τ = τ} {σ = σ}
    (quotientᵖ left middle right)
    with ≈∀-arrow-right left
       | ≈∀-arrow-left right
quotient-arrow-components-rename² {τ = τ} {σ = σ}
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    with ≈∀-arrow-components left
       | middle
       | ≈∀-arrow-components right
quotient-arrow-components-rename² {τ = τ} {σ = σ}
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain
    with ≈∀-arrow-right (≈∀-renameᵗ {τ = τ} left)
       | ≈∀-arrow-components
           (≈∀-renameᵗ {τ = τ} left)
       | ≈∀-arrow-left (≈∀-renameᵗ {τ = σ} right)
       | ≈∀-arrow-components
           (≈∀-renameᵗ {τ = σ} right)
quotient-arrow-components-rename² {τ = τ} {σ = σ}
    (quotientᵖ left middle right)
    | C , D , refl
    | C′ , D′ , refl
    | left-domain , left-codomain
    | middle-domain ↦ middle-codomain
    | right-domain , right-codomain
    | renamed-C , renamed-D , refl
    | renamed-left-domain , renamed-left-codomain
    | renamed-C′ , renamed-D′ , refl
    | renamed-right-domain , renamed-right-codomain
    rewrite ≈∀-arrow-components-renameᵗ {τ = τ} left
          | ≈∀-arrow-components-renameᵗ {τ = σ} right =
  refl


quotient-arrow-components-rename²-at :
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
    {τ σ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} → a ∈ Φ →
      rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {A A′ B B′ : Ty}
    {qF : Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ}
    {qA : Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ}
    {qB : Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ} →
  ⊑ᵖ-arrow-components qF ≡ (qA , qB) →
  ⊑ᵖ-arrow-components (⊑ᵖ-rename²ᵢ assm hτ hσ qF) ≡
    ( ⊑ᵖ-rename²ᵢ assm hτ hσ qA
    , ⊑ᵖ-rename²ᵢ assm hτ hσ qB
    )
quotient-arrow-components-rename²-at {qF = qF} refl =
  quotient-arrow-components-rename² qF


mutual
  source-perm-right-id-forward :
    ∀ {A B : Ty} {equivalence : A ≈∀ B}
      {s s′ p : ImprecisionShape} →
    equivalence ⊢ s ≈∀ˢ s′ →
    p ； id★ˢ ≋ s →
    ∃[ p′ ]
      (equivalence ⊢ p ≈∀ˢ p′) ×
      (p′ ； id★ˢ ≋ s′)
  source-perm-right-id-forward source-perm-refl composition =
    _ , source-perm-refl , composition
  source-perm-right-id-forward
      (source-perm-sym shape) composition
      with source-perm-right-id-backward shape composition
  source-perm-right-id-forward
      (source-perm-sym shape) composition
      | target , target-shape , target-composition =
    target , source-perm-sym target-shape , target-composition
  source-perm-right-id-forward
      (source-perm-trans first second) composition
      with source-perm-right-id-forward first composition
  source-perm-right-id-forward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      with source-perm-right-id-forward second middle-composition
  source-perm-right-id-forward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      | target , target-shape , target-composition =
    target ,
    source-perm-trans middle-shape target-shape ,
    target-composition
  source-perm-right-id-forward
      (source-perm-↦ domain codomain) ()
  source-perm-right-id-forward
      (source-perm-tag-⇛ domain codomain)
      (comp-tag-⇛-id★ domain-composition codomain-composition)
      with
        source-perm-right-id-forward domain domain-composition
       | source-perm-right-id-forward codomain codomain-composition
  source-perm-right-id-forward
      (source-perm-tag-⇛ domain codomain)
      (comp-tag-⇛-id★ domain-composition codomain-composition)
      | target-domain , target-domain-shape , target-domain-composition
      | target-codomain , target-codomain-shape ,
        target-codomain-composition =
    tag target-domain ⇛ˢ target-codomain ,
    source-perm-tag-⇛ target-domain-shape target-codomain-shape ,
    comp-tag-⇛-id★
      target-domain-composition target-codomain-composition
  source-perm-right-id-forward (source-perm-∀ shape) ()
  source-perm-right-id-forward
      (source-perm-ν shape) (comp-ν composition)
      with source-perm-right-id-forward shape composition
  source-perm-right-id-forward
      (source-perm-ν shape) (comp-ν composition)
      | target , target-shape , target-composition =
    νˢ target ,
    source-perm-ν target-shape ,
    comp-ν target-composition
  source-perm-right-id-forward source-swap-∀∀ ()
  source-perm-right-id-forward source-swap-∀ν ()
  source-perm-right-id-forward source-swap-ν∀ (comp-ν ())
  source-perm-right-id-forward source-swap-νν composition
      with compose-right-id★ composition
  source-perm-right-id-forward source-swap-νν composition
      | refl =
    _ , source-swap-νν , composition

  source-perm-right-id-backward :
    ∀ {A B : Ty} {equivalence : A ≈∀ B}
      {s s′ p′ : ImprecisionShape} →
    equivalence ⊢ s ≈∀ˢ s′ →
    p′ ； id★ˢ ≋ s′ →
    ∃[ p ]
      (equivalence ⊢ p ≈∀ˢ p′) ×
      (p ； id★ˢ ≋ s)
  source-perm-right-id-backward source-perm-refl composition =
    _ , source-perm-refl , composition
  source-perm-right-id-backward
      (source-perm-sym shape) composition
      with source-perm-right-id-forward shape composition
  source-perm-right-id-backward
      (source-perm-sym shape) composition
      | source , source-shape , source-composition =
    source , source-perm-sym source-shape , source-composition
  source-perm-right-id-backward
      (source-perm-trans first second) composition
      with source-perm-right-id-backward second composition
  source-perm-right-id-backward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      with source-perm-right-id-backward first middle-composition
  source-perm-right-id-backward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      | source , source-shape , source-composition =
    source ,
    source-perm-trans source-shape middle-shape ,
    source-composition
  source-perm-right-id-backward
      (source-perm-↦ domain codomain) ()
  source-perm-right-id-backward
      (source-perm-tag-⇛ domain codomain)
      (comp-tag-⇛-id★ domain-composition codomain-composition)
      with
        source-perm-right-id-backward domain domain-composition
       | source-perm-right-id-backward codomain codomain-composition
  source-perm-right-id-backward
      (source-perm-tag-⇛ domain codomain)
      (comp-tag-⇛-id★ domain-composition codomain-composition)
      | source-domain , source-domain-shape , source-domain-composition
      | source-codomain , source-codomain-shape ,
        source-codomain-composition =
    tag source-domain ⇛ˢ source-codomain ,
    source-perm-tag-⇛ source-domain-shape source-codomain-shape ,
    comp-tag-⇛-id★
      source-domain-composition source-codomain-composition
  source-perm-right-id-backward (source-perm-∀ shape) ()
  source-perm-right-id-backward
      (source-perm-ν shape) (comp-ν composition)
      with source-perm-right-id-backward shape composition
  source-perm-right-id-backward
      (source-perm-ν shape) (comp-ν composition)
      | source , source-shape , source-composition =
    νˢ source ,
    source-perm-ν source-shape ,
    comp-ν source-composition
  source-perm-right-id-backward source-swap-∀∀ ()
  source-perm-right-id-backward
      source-swap-∀ν (comp-ν ())
  source-perm-right-id-backward source-swap-ν∀ ()
  source-perm-right-id-backward source-swap-νν composition
      with compose-right-id★ composition
  source-perm-right-id-backward source-swap-νν composition
      | refl =
    _ , source-swap-νν , composition


mutual
  source-perm-function-tag-forward :
    ∀ {A B : Ty} {equivalence : A ≈∀ B}
      {s s′ p : ImprecisionShape} →
    equivalence ⊢ s ≈∀ˢ s′ →
    p ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ s →
    ∃[ p′ ]
      (equivalence ⊢ p ≈∀ˢ p′) ×
      (p′ ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ s′)
  source-perm-function-tag-forward source-perm-refl composition =
    _ , source-perm-refl , composition
  source-perm-function-tag-forward
      (source-perm-sym shape) composition
      with source-perm-function-tag-backward shape composition
  source-perm-function-tag-forward
      (source-perm-sym shape) composition
      | target , target-shape , target-composition =
    target , source-perm-sym target-shape , target-composition
  source-perm-function-tag-forward
      (source-perm-trans first second) composition
      with source-perm-function-tag-forward first composition
  source-perm-function-tag-forward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      with source-perm-function-tag-forward second middle-composition
  source-perm-function-tag-forward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      | target , target-shape , target-composition =
    target ,
    source-perm-trans middle-shape target-shape ,
    target-composition
  source-perm-function-tag-forward
      (source-perm-↦ domain codomain) ()
  source-perm-function-tag-forward
      (source-perm-tag-⇛ domain codomain)
      (comp-↦-tag domain-composition codomain-composition)
      with
        source-perm-right-id-forward domain domain-composition
       | source-perm-right-id-forward codomain codomain-composition
  source-perm-function-tag-forward
      (source-perm-tag-⇛ domain codomain)
      (comp-↦-tag domain-composition codomain-composition)
      | target-domain , target-domain-shape , target-domain-composition
      | target-codomain , target-codomain-shape ,
        target-codomain-composition =
    target-domain ↦ˢ target-codomain ,
    source-perm-↦ target-domain-shape target-codomain-shape ,
    comp-↦-tag target-domain-composition target-codomain-composition
  source-perm-function-tag-forward (source-perm-∀ shape) ()
  source-perm-function-tag-forward
      (source-perm-ν shape) (comp-ν composition)
      with source-perm-function-tag-forward shape composition
  source-perm-function-tag-forward
      (source-perm-ν shape) (comp-ν composition)
      | target , target-shape , target-composition =
    νˢ target ,
    source-perm-ν target-shape ,
    comp-ν target-composition
  source-perm-function-tag-forward source-swap-∀∀ ()
  source-perm-function-tag-forward source-swap-∀ν ()
  source-perm-function-tag-forward
      source-swap-ν∀ (comp-ν ())
  source-perm-function-tag-forward
      source-swap-νν (comp-ν (comp-ν composition)) =
    _ , source-swap-νν , comp-ν (comp-ν composition)

  source-perm-function-tag-backward :
    ∀ {A B : Ty} {equivalence : A ≈∀ B}
      {s s′ p′ : ImprecisionShape} →
    equivalence ⊢ s ≈∀ˢ s′ →
    p′ ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ s′ →
    ∃[ p ]
      (equivalence ⊢ p ≈∀ˢ p′) ×
      (p ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ s)
  source-perm-function-tag-backward source-perm-refl composition =
    _ , source-perm-refl , composition
  source-perm-function-tag-backward
      (source-perm-sym shape) composition
      with source-perm-function-tag-forward shape composition
  source-perm-function-tag-backward
      (source-perm-sym shape) composition
      | source , source-shape , source-composition =
    source , source-perm-sym source-shape , source-composition
  source-perm-function-tag-backward
      (source-perm-trans first second) composition
      with source-perm-function-tag-backward second composition
  source-perm-function-tag-backward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      with source-perm-function-tag-backward first middle-composition
  source-perm-function-tag-backward
      (source-perm-trans first second) composition
      | middle , middle-shape , middle-composition
      | source , source-shape , source-composition =
    source ,
    source-perm-trans source-shape middle-shape ,
    source-composition
  source-perm-function-tag-backward
      (source-perm-↦ domain codomain) ()
  source-perm-function-tag-backward
      (source-perm-tag-⇛ domain codomain)
      (comp-↦-tag domain-composition codomain-composition)
      with
        source-perm-right-id-backward domain domain-composition
       | source-perm-right-id-backward codomain codomain-composition
  source-perm-function-tag-backward
      (source-perm-tag-⇛ domain codomain)
      (comp-↦-tag domain-composition codomain-composition)
      | source-domain , source-domain-shape , source-domain-composition
      | source-codomain , source-codomain-shape ,
        source-codomain-composition =
    source-domain ↦ˢ source-codomain ,
    source-perm-↦ source-domain-shape source-codomain-shape ,
    comp-↦-tag source-domain-composition source-codomain-composition
  source-perm-function-tag-backward (source-perm-∀ shape) ()
  source-perm-function-tag-backward
      (source-perm-ν shape) (comp-ν composition)
      with source-perm-function-tag-backward shape composition
  source-perm-function-tag-backward
      (source-perm-ν shape) (comp-ν composition)
      | source , source-shape , source-composition =
    νˢ source ,
    source-perm-ν source-shape ,
    comp-ν source-composition
  source-perm-function-tag-backward source-swap-∀∀ ()
  source-perm-function-tag-backward
      source-swap-∀ν (comp-ν ())
  source-perm-function-tag-backward source-swap-ν∀ ()
  source-perm-function-tag-backward
      source-swap-νν (comp-ν (comp-ν composition)) =
    _ , source-swap-νν , comp-ν (comp-ν composition)


quotient-boundary-factor-left :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {C C′ : Ty}
    {qD : Φ ∣ Δᴸ ⊢ C ⊑ᵖ C′ ⊣ Δᴿ}
    {s₀ s₂ s′ : ImprecisionShape} →
  s₀ ； (tag id★ˢ ⇛ˢ id★ˢ) ≋ s₂ →
  (tag id★ˢ ⇛ˢ id★ˢ) ； id★ˢ ≋
    (tag id★ˢ ⇛ˢ id★ˢ) →
  s₂ ；⌊ id★ ⌋≋ᵖ qD ； s′ →
  s₀ ；⌊ tag id★ ⇛ id★ ⌋≋ᵖ qD ； s′
quotient-boundary-factor-left
    first (comp-tag-⇛-id★ comp-id★ comp-id★)
    (quotient-boundary-square
      source-shape left-shape target-shape right-shape)
    with source-perm-function-tag-forward source-shape first
quotient-boundary-factor-left
    first (comp-tag-⇛-id★ comp-id★ comp-id★)
    (quotient-boundary-square
      source-shape left-shape target-shape right-shape)
    | target , target-source-shape , target-composition
    rewrite compose-right-id★ left-shape =
  quotient-boundary-square
    target-source-shape target-composition target-shape right-shape
