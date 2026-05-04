module proof.DGGCatchup where

-- File Charter:
--   * Value catchup and convergence lemmas for the PolyConvert DGG proof.
--   * Owns the mutual terminal/value reasoning used by both simulations.
--   * Intended as one independent worker-owned proof surface.

open import Data.List using ([])
open import Data.Product using (_×_; ∃-syntax; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Types
open import Imprecision
  using
    ( Imp
    ; ★⊑★
    ; X⊑★
    ; A⊑★
    ; X⊑X
    ; α⊑α
    ; ι⊑ι
    ; A⇒B⊑A′⇒B′
    ; `∀A⊑∀B
    ; `∀A⊑B
    ; tgt⊑
    ; tgt⊑-correct
    ; ⊑-★★
    ; ⊑-★ν
    ; ⊑-★
    ; ⊑-＇
    ; ⊑-｀
    ; ⊑-‵
    ; ⊑-⇒
    ; ⊑-∀
    ; ⊑-ν
    ; _∣_⊢_⦂_⊑_
    ; _∣_⊢_⦂_⊒_
    )
open import Conversion using (Conv↑; Conv↓; _∣_∣_⊢_⦂_↑ˢ_; _∣_∣_⊢_⦂_↓ˢ_)
open import Store
open import Terms
open import TermImprecision
open import Reduction
open import proof.DGGCommon
open import proof.DGGMultistep
open import proof.Progress using (canonical-★; sv-⇑tag)
open import proof.ImprecisionCompose using (⊑-trans)
open import proof.TypeProperties using (ground-upper-unique-⊑)

Catchup :
  SealCtx → Store → Term → Ty → Ty →
  SealCtx → Store → Term → Set
Catchup Ψˡ Σˡ V A B Ψʳ Σʳ N′ =
  ∃[ Ψʳ′ ] ∃[ Σʳ′ ]
    (StoreWf 0 Ψʳ′ Σʳ′ ×
     ∃[ V′ ]
       (Value V′ ×
        (Σʳ ∣ N′ —↠ Σʳ′ ∣ V′) ×
        TermRel Ψˡ Σˡ Ψʳ′ Σʳ′ V V′ A B))

postulate
  right-extra-up-catchup-ν :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ Bν pν pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    Ψˡ ∣ [] ⊢ `∀A⊑B Bν pν ⦂ A′ ⊑ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B′ →
    Catchup Ψˡ Σˡ V A B′ Ψʳ Σʳ (V′ ⇑ `∀A⊑B Bν pν)

right-extra-up-catchup :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ p′ pB} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
  Ψˡ ∣ [] ⊢ p′ ⦂ A′ ⊑ B′ →
  Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B′ →
  Catchup Ψˡ Σˡ V A B′ Ψʳ Σʳ (V′ ⇑ p′)
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel ⊑-★★ pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇑ ★⊑★) —→⟨ pure-step (id-up-★ vV′) ⟩ _ ∎) ,
  rel
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-★ν xν) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , (vV′ ⇑ tagν) , ((_ ⇑ X⊑★ _) ∎) ,
  ⊑⇑R rel (⊑-★ν xν) pB⊢
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-★ g p′⊢) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , (vV′ ⇑ tag) , ((_ ⇑ A⊑★ _) ∎) ,
  ⊑⇑R rel (⊑-★ g p′⊢) pB⊢
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-＇ x∈) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇑ X⊑X _) —→⟨ pure-step (id-up-＇ vV′) ⟩ _ ∎) ,
  rel
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-｀ wfα) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇑ α⊑α _) —→⟨ pure-step (id-up-｀ vV′) ⟩ _ ∎) ,
  rel
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel ⊑-‵ pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇑ ι⊑ι _) —→⟨ pure-step (id-up-‵ vV′) ⟩ _ ∎) ,
  rel
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-⇒ p′⊢ q′⊢) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , (vV′ ⇑ (_↦_ {p = _} {q = _})) ,
  ((_ ⇑ A⇒B⊑A′⇒B′ _ _) ∎) ,
  ⊑⇑R rel (⊑-⇒ p′⊢ q′⊢) pB⊢
right-extra-up-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-∀ p′⊢) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , (vV′ ⇑ `∀) ,
  ((_ ⇑ `∀A⊑∀B _) ∎) ,
  ⊑⇑R rel (⊑-∀ p′⊢) pB⊢
right-extra-up-catchup wfΣˡ wfΣʳ vV vV′ rel (⊑-ν wfB occ p′⊢) pB⊢ =
  right-extra-up-catchup-ν wfΣˡ wfΣʳ vV vV′ rel
    (⊑-ν wfB occ p′⊢) pB⊢

postulate
  right-extra-up-catchup-left :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ p p′ pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    Ψˡ ∣ [] ⊢ p ⦂ A ⊑ B →
    Ψˡ ∣ [] ⊢ p′ ⦂ A′ ⊑ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ B ⊑ B′ →
    Catchup Ψˡ Σˡ (V ⇑ p) B B′ Ψʳ Σʳ (V′ ⇑ p′)

postulate
  right-tag-less-ground-catchup-⇑R-core :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W A A′ B G H p q pB} →
    Ground H →
    Ground G →
    tgt⊑ p ≡ tgt⊑ q →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V W A A′ →
    Ψˡ ∣ [] ⊢ p ⦂ A′ ⊑ H →
    Ψˡ ∣ [] ⊢ q ⦂ B ⊑ G →
    Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B →
    Catchup Ψˡ Σˡ V A B Ψʳ Σʳ ((W ⇑ p) ⇓ q)

  right-tag-less-ground-catchup-⇑-core :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M W A A′ B B₀ G H p p₀ q pB} →
    Ground H →
    Ground G →
    tgt⊑ p ≡ tgt⊑ q →
    Value (M ⇑ p₀) →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M W A A′ →
    Ψˡ ∣ [] ⊢ p₀ ⦂ A ⊑ B₀ →
    Ψˡ ∣ [] ⊢ p ⦂ A′ ⊑ H →
    Ψˡ ∣ [] ⊢ q ⦂ B ⊑ G →
    Ψˡ ∣ [] ⊢ pB ⦂ B₀ ⊑ B →
    Catchup Ψˡ Σˡ (M ⇑ p₀) B₀ B Ψʳ Σʳ ((W ⇑ p) ⇓ q)

  right-tag-less-ground-catchup-other :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V W A B G p q pB} →
    Ground G →
    Value V →
    Value W →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V (W ⇑ A⊑★ p) A ★ →
    Ψˡ ∣ [] ⊢ q ⦂ B ⊑ G →
    Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B →
    (tgt⊑ p ≡ tgt⊑ q) ×
    Catchup Ψˡ Σˡ V A B Ψʳ Σʳ ((W ⇑ p) ⇓ q)

tag-eq-two-step :
  ∀ {Ψ A A′ B G H pA p q pB} →
  Ground H →
  Ground G →
  Ψ ∣ [] ⊢ pA ⦂ A ⊑ A′ →
  Ψ ∣ [] ⊢ p ⦂ A′ ⊑ H →
  Ψ ∣ [] ⊢ q ⦂ B ⊑ G →
  Ψ ∣ [] ⊢ pB ⦂ A ⊑ B →
  tgt⊑ p ≡ tgt⊑ q
tag-eq-two-step h g pA⊢ p⊢ q⊢ pB⊢
    with ⊑-trans pA⊢ p⊢
       | ⊑-trans pB⊢ q⊢
... | rH , A⊑H | rG , A⊑G =
  trans (tgt⊑-correct p⊢)
    (trans H≡G (sym (tgt⊑-correct q⊢)))
  where
    H≡G = ground-upper-unique-⊑ h g A⊑H A⊑G

tag-eq-three-step :
  ∀ {Ψ A A′ B B₀ G H pA p p₀ q pB} →
  Ground H →
  Ground G →
  Ψ ∣ [] ⊢ pA ⦂ A ⊑ A′ →
  Ψ ∣ [] ⊢ p ⦂ A′ ⊑ H →
  Ψ ∣ [] ⊢ p₀ ⦂ A ⊑ B₀ →
  Ψ ∣ [] ⊢ q ⦂ B ⊑ G →
  Ψ ∣ [] ⊢ pB ⦂ B₀ ⊑ B →
  tgt⊑ p ≡ tgt⊑ q
tag-eq-three-step h g pA⊢ p⊢ p₀⊢ q⊢ pB⊢
    with ⊑-trans pA⊢ p⊢
       | ⊑-trans pB⊢ q⊢
... | rH , A⊑H | rBG , B₀⊑G
    with ⊑-trans p₀⊢ B₀⊑G
... | rG , A⊑G =
  trans (tgt⊑-correct p⊢)
    (trans H≡G (sym (tgt⊑-correct q⊢)))
  where
    H≡G = ground-upper-unique-⊑ h g A⊑H A⊑G

right-tag-eq-⇑R :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V W A A′ B G H p q pB} →
  Ground H →
  Ground G →
  Value V →
  Value W →
  TermRel Ψˡ Σˡ Ψʳ Σʳ V W A A′ →
  Ψˡ ∣ [] ⊢ p ⦂ A′ ⊑ H →
  Ψˡ ∣ [] ⊢ q ⦂ B ⊑ G →
  Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B →
  tgt⊑ p ≡ tgt⊑ q
right-tag-eq-⇑R h g vV vW rel p⊢ q⊢ pB⊢ with ⊑-type-imprecision rel
... | pA , pA⊢ = tag-eq-two-step h g pA⊢ p⊢ q⊢ pB⊢

right-tag-eq-⇑ :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ M W A A′ B B₀ G H p p₀ q pB} →
  Ground H →
  Ground G →
  Value (M ⇑ p₀) →
  Value W →
  TermRel Ψˡ Σˡ Ψʳ Σʳ M W A A′ →
  Ψˡ ∣ [] ⊢ p₀ ⦂ A ⊑ B₀ →
  Ψˡ ∣ [] ⊢ p ⦂ A′ ⊑ H →
  Ψˡ ∣ [] ⊢ q ⦂ B ⊑ G →
  Ψˡ ∣ [] ⊢ pB ⦂ B₀ ⊑ B →
  tgt⊑ p ≡ tgt⊑ q
right-tag-eq-⇑ h g vMp₀ vW rel p₀⊢ p⊢ q⊢ pB⊢
    with ⊑-type-imprecision rel
... | pA , pA⊢ = tag-eq-three-step h g pA⊢ p⊢ p₀⊢ q⊢ pB⊢

tag-eq-from-ground-eq :
  ∀ {Ψ A B G H p q} →
  H ≡ G →
  Ψ ∣ [] ⊢ p ⦂ A ⊑ H →
  Ψ ∣ [] ⊢ q ⦂ B ⊑ G →
  tgt⊑ p ≡ tgt⊑ q
tag-eq-from-ground-eq H≡G p⊢ q⊢ =
  trans (tgt⊑-correct p⊢) (trans H≡G (sym (tgt⊑-correct q⊢)))

right-tag-less-ground-catchup :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V W A B G p q pB} →
  Ground G →
  Value V →
  Value W →
  TermRel Ψˡ Σˡ Ψʳ Σʳ V (W ⇑ A⊑★ p) A ★ →
  Ψˡ ∣ [] ⊢ q ⦂ B ⊑ G →
  Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B →
  (tgt⊑ p ≡ tgt⊑ q) ×
  Catchup Ψˡ Σˡ V A B Ψʳ Σʳ ((W ⇑ p) ⇓ q)
right-tag-less-ground-catchup
  {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  {V = V} {W = W} {A = A} {B = B} {G = G} {p = p} {q = q}
  g vV vW
  (⊑⇑R rel (⊑-★ {G = H} h p⊢) p★⊢) q⊢ pB⊢ =
  tag-eq ,
  right-tag-less-ground-catchup-⇑R-core
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {V = V} {W = W} {A = A} {B = B} {G = G} {H = H}
    {p = p} {q = q}
    h g tag-eq vV vW rel p⊢ q⊢ pB⊢
  where
    tag-eq =
      right-tag-eq-⇑R
        {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
        {V = V} {W = W} {A = A} {B = B} {G = G} {H = H}
        {p = p} {q = q}
        h g vV vW rel p⊢ q⊢ pB⊢
right-tag-less-ground-catchup
  {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  {W = W} {B = B} {G = G} {p = p} {q = q}
  g vV vW
  (⊑⇑ rel p₀⊢ (⊑-★ {G = H} h p⊢) p★⊢) q⊢ pB⊢ =
  tag-eq ,
  right-tag-less-ground-catchup-⇑-core
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {W = W} {B = B} {G = G} {H = H} {p = p} {q = q}
    h g tag-eq vV vW rel p₀⊢ p⊢ q⊢ pB⊢
  where
    tag-eq =
      right-tag-eq-⇑
        {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
        {W = W} {B = B} {G = G} {H = H} {p = p} {q = q}
        h g vV vW rel p₀⊢ p⊢ q⊢ pB⊢
right-tag-less-ground-catchup
  {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  {V = V} {W = W} {A = A} {B = B} {G = G} {p = p} {q = q}
  g vV vW rel q⊢ pB⊢ =
  right-tag-less-ground-catchup-other
    {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
    {V = V} {W = W} {A = A} {B = B} {G = G} {p = p} {q = q}
    g vV vW rel q⊢ pB⊢

right-extra-down-catchup-tag :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ p′ pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    Ψˡ ∣ [] ⊢ A⊑★ p′ ⦂ A′ ⊒ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B′ →
    Catchup Ψˡ Σˡ V A B′ Ψʳ Σʳ (V′ ⇓ A⊑★ p′)
right-extra-down-catchup-tag
  {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  {V = V} {A = A} {B′ = B′}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-★ g q⊢) pB⊢
    with canonical-★ vV′ (⊑-right-typed rel)
right-extra-down-catchup-tag
  {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  {V = V} {A = A} {B′ = B′}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-★ {G = G} {p = q} g q⊢) pB⊢
  | sv-⇑tag {W = W′} {p = p} vW′ refl =
    result
  where
    tag-catchup =
      right-tag-less-ground-catchup
        {Ψˡ = Ψˡ} {Ψʳ = Ψʳ} {Σˡ = Σˡ} {Σʳ = Σʳ}
        {V = V} {W = W′} {A = A} {B = B′} {G = G}
        {p = p} {q = q}
        g vV vW′ rel q⊢ pB⊢
    result :
      Catchup Ψˡ Σˡ V A B′ Ψʳ Σʳ ((W′ ⇑ A⊑★ p) ⇓ A⊑★ q)
    result with tag-catchup
    result | tag-eq ,
      Ψʳ′ , Σʳ′ , wfΣʳ′ , W″ , vW″ , W⇑p⇓q↠W″ , V⊑W″ =
      Ψʳ′ , Σʳ′ , wfΣʳ′ , W″ , vW″ ,
      ((_ ⇓ A⊑★ _) —→⟨ pure-step (tag-untag-ok vW′ tag-eq) ⟩
       W⇑p⇓q↠W″) ,
      V⊑W″

right-extra-down-catchup :
  ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ p′ pB} →
  StoreWf 0 Ψˡ Σˡ →
  StoreWf 0 Ψʳ Σʳ →
  Value V →
  Value V′ →
  TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
  Ψˡ ∣ [] ⊢ p′ ⦂ A′ ⊒ B′ →
  Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B′ →
  Catchup Ψˡ Σˡ V A B′ Ψʳ Σʳ (V′ ⇓ p′)
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel ⊑-★★ pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇓ ★⊑★) —→⟨ pure-step (id-down-★ vV′) ⟩ _ ∎) ,
  rel
right-extra-down-catchup wfΣˡ wfΣʳ vV vV′ rel (⊑-★ν ()) pB⊢
right-extra-down-catchup
  wfΣˡ wfΣʳ vV vV′ rel (⊑-★ g p′⊢) pB⊢ =
  right-extra-down-catchup-tag wfΣˡ wfΣʳ vV vV′ rel
    (⊑-★ g p′⊢) pB⊢
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-＇ x∈) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇓ X⊑X _) —→⟨ pure-step (id-down-＇ vV′) ⟩ _ ∎) ,
  rel
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-｀ wfα) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇓ α⊑α _) —→⟨ pure-step (id-down-｀ vV′) ⟩ _ ∎) ,
  rel
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel ⊑-‵ pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , vV′ ,
  ((_ ⇓ ι⊑ι _) —→⟨ pure-step (id-down-‵ vV′) ⟩ _ ∎) ,
  rel
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-⇒ p′⊢ q′⊢) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , (vV′ ⇓ (_↦_ {p = _} {q = _})) ,
  ((_ ⇓ A⇒B⊑A′⇒B′ _ _) ∎) ,
  ⊑⇓R rel (⊑-⇒ p′⊢ q′⊢) pB⊢
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-∀ p′⊢) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , (vV′ ⇓ `∀) ,
  ((_ ⇓ `∀A⊑∀B _) ∎) ,
  ⊑⇓R rel (⊑-∀ p′⊢) pB⊢
right-extra-down-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ vV vV′ rel (⊑-ν wfB occ p′⊢) pB⊢ =
  Ψʳ , Σʳ , wfΣʳ , _ , (vV′ ⇓ ν_) ,
  ((_ ⇓ `∀A⊑B _ _) ∎) ,
  ⊑⇓R rel (⊑-ν wfB occ p′⊢) pB⊢

postulate
  right-extra-down-catchup-left :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ p p′ pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    Ψˡ ∣ [] ⊢ p ⦂ A ⊒ B →
    Ψˡ ∣ [] ⊢ p′ ⦂ A′ ⊒ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ B ⊑ B′ →
    Catchup Ψˡ Σˡ (V ⇓ p) B B′ Ψʳ Σʳ (V′ ⇓ p′)

  right-extra-reveal-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ c′ pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    0 ∣ Ψˡ ∣ Σˡ ⊢ c′ ⦂ A′ ↑ˢ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B′ →
    Catchup Ψˡ Σˡ V A B′ Ψʳ Σʳ (V′ ↑ c′)

  right-extra-reveal-catchup-left :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ c c′ pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    0 ∣ Ψˡ ∣ Σˡ ⊢ c ⦂ A ↑ˢ B →
    0 ∣ Ψˡ ∣ Σˡ ⊢ c′ ⦂ A′ ↑ˢ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ B ⊑ B′ →
    Catchup Ψˡ Σˡ (V ↑ c) B B′ Ψʳ Σʳ (V′ ↑ c′)

  right-extra-conceal-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B′ c′ pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    0 ∣ Ψˡ ∣ Σˡ ⊢ c′ ⦂ A′ ↓ˢ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ A ⊑ B′ →
    Catchup Ψˡ Σˡ V A B′ Ψʳ Σʳ (V′ ↓ c′)

  right-extra-conceal-catchup-left :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V V′ A A′ B B′ c c′ pB} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V V′ A A′ →
    0 ∣ Ψˡ ∣ Σˡ ⊢ c ⦂ A ↓ˢ B →
    0 ∣ Ψˡ ∣ Σˡ ⊢ c′ ⦂ A′ ↓ˢ B′ →
    Ψˡ ∣ [] ⊢ pB ⦂ B ⊑ B′ →
    Catchup Ψˡ Σˡ (V ↓ c) B B′ Ψʳ Σʳ (V′ ↓ c′)

left-value-right-catchup :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ V N′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V →
    TermRel Ψˡ Σˡ Ψʳ Σʳ V N′ A B →
    Catchup Ψˡ Σˡ V A B Ψʳ Σʳ N′
left-value-right-catchup wfΣˡ wfΣʳ () (⊑` h)
left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ (ƛ A ⇒ N)
  (⊑ƛ {A′ = A′} {M′ = N′} {pA = pA} {pB = pB}
       {pA⊢ = pA⊢} {pB⊢ = pB⊢} hA hA′ rel) =
  Ψʳ , Σʳ , wfΣʳ , (ƛ A′ ⇒ N′) , (ƛ A′ ⇒ N′) ,
  ((ƛ A′ ⇒ N′) ∎) ,
  ⊑ƛ {pA = pA} {pB = pB} {pA⊢ = pA⊢} {pB⊢ = pB⊢}
    hA hA′ rel
left-value-right-catchup wfΣˡ wfΣʳ () (⊑· relL relM)
left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ (Λ N) (⊑Λ {M′ = N′} vM vM′ rel) =
  Ψʳ , Σʳ , wfΣʳ , Λ N′ , Λ N′ , (Λ N′ ∎) , ⊑Λ vM vM′ rel
left-value-right-catchup wfΣˡ wfΣʳ () (⊑⦂∀ rel wfA wfB wfT pT⊢)
left-value-right-catchup wfΣˡ wfΣʳ () (⊑⦂∀-ν rel wfA wfT pT⊢)
left-value-right-catchup {Ψʳ = Ψʳ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ ($ κ) ⊑$ =
  Ψʳ , Σʳ , wfΣʳ , $ κ , $ κ , (($ κ) ∎) , ⊑$
left-value-right-catchup wfΣˡ wfΣʳ () (⊑⊕ relL relM)
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ (vV ⇑ upV) (⊑⇑ rel p⊢ p′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ (vV ⇑ upV) (⊑⇑ rel p⊢ p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-up-catchup-left wfΣˡ wfΣʳ′ vV vV′ V⊑V′ p⊢ p′⊢ pB⊢
left-value-right-catchup
  {Ψˡ = Ψˡ} {Σˡ = Σˡ} {Σʳ = Σʳ}
  wfΣˡ wfΣʳ (vV ⇑ upV) (⊑⇑ rel p⊢ p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′⇑↠W′ , V⇑⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (up-↠ M′↠V′) V′⇑↠W′ ,
  V⇑⊑W′
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ⇑ upV) (⊑⇑L rel p⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ⇑ upV) (⊑⇑L rel p⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
  ⊑⇑L V⊑V′ p⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑⇑R rel p′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑⇑R rel p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-up-catchup wfΣˡ wfΣʳ′ vV vV′ V⊑V′ p′⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑⇑R rel p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′⇑↠W′ , V⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (up-↠ M′↠V′) V′⇑↠W′ ,
  V⊑W′
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ⇓ downV) (⊑⇓ rel p⊢ p′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ⇓ downV) (⊑⇓ rel p⊢ p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-down-catchup-left wfΣˡ wfΣʳ′ vV vV′ V⊑V′ p⊢ p′⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ⇓ downV) (⊑⇓ rel p⊢ p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′⇓↠W′ , V⇓⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (down-↠ M′↠V′) V′⇓↠W′ ,
  V⇓⊑W′
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ⇓ downV) (⊑⇓L rel p⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ⇓ downV) (⊑⇓L rel p⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
  ⊑⇓L V⊑V′ p⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑⇓R rel p′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑⇓R rel p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-down-catchup wfΣˡ wfΣʳ′ vV vV′ V⊑V′ p′⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑⇓R rel p′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′⇓↠W′ , V⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (down-↠ M′↠V′) V′⇓↠W′ ,
  V⊑W′
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↑ revealV) (⊑↑ rel c⊢ c′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↑ revealV) (⊑↑ rel c⊢ c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-reveal-catchup-left wfΣˡ wfΣʳ′ vV vV′ V⊑V′ c⊢ c′⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↑ revealV) (⊑↑ rel c⊢ c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′↑↠W′ , V↑⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (reveal-↠ M′↠V′) V′↑↠W′ ,
  V↑⊑W′
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↑ revealV) (⊑↑L rel c⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↑ revealV) (⊑↑L rel c⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
  ⊑↑L V⊑V′ c⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑↑R rel c′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑↑R rel c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-reveal-catchup wfΣˡ wfΣʳ′ vV vV′ V⊑V′ c′⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑↑R rel c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′↑↠W′ , V⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (reveal-↠ M′↠V′) V′↑↠W′ ,
  V⊑W′
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↓ concealV) (⊑↓ rel c⊢ c′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↓ concealV) (⊑↓ rel c⊢ c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-conceal-catchup-left wfΣˡ wfΣʳ′ vV vV′ V⊑V′ c⊢ c′⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↓ concealV) (⊑↓ rel c⊢ c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′↓↠W′ , V↓⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (conceal-↠ M′↠V′) V′↓↠W′ ,
  V↓⊑W′
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↓ concealV) (⊑↓L rel c⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ (vV ↓ concealV) (⊑↓L rel c⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′ =
  Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ ,
  ⊑↓L V⊑V′ c⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑↓R rel c′⊢ pB⊢)
    with left-value-right-catchup wfΣˡ wfΣʳ vV rel
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑↓R rel c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
    with right-extra-conceal-catchup wfΣˡ wfΣʳ′ vV vV′ V⊑V′ c′⊢ pB⊢
left-value-right-catchup
  wfΣˡ wfΣʳ vV (⊑↓R rel c′⊢ pB⊢)
  | Ψʳ′ , Σʳ′ , wfΣʳ′ , V′ , vV′ , M′↠V′ , V⊑V′
  | Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ , V′↓↠W′ , V⊑W′ =
  Ψʳ″ , Σʳ″ , wfΣʳ″ , W′ , vW′ ,
  multi-trans (conceal-↠ M′↠V′) V′↓↠W′ ,
  V⊑W′
left-value-right-catchup wfΣˡ wfΣʳ () (⊑blameR hM p⊢)

postulate
  right-value-left-catchup-or-blame :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ N V′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    Value V′ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ N V′ A B →
    (∃[ Ψˡ′ ] ∃[ Σˡ′ ]
      (StoreWf 0 Ψˡ′ Σˡ′ ×
       ∃[ V ]
         (Value V ×
          (Σˡ ∣ N —↠ Σˡ′ ∣ V) ×
          TermRel Ψˡ′ Σˡ′ Ψʳ Σʳ V V′ A B)))
    ⊎ Blames Σˡ N

  right-converges-implies-left-converges :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ M M′ A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
    Converges Σʳ M′ →
    Converges Σˡ M

  right-diverges-implies-left-blame-or-step :
    ∀ {Ψˡ Ψʳ Σˡ Σʳ Σˡ′ M M′ N A B} →
    StoreWf 0 Ψˡ Σˡ →
    StoreWf 0 Ψʳ Σʳ →
    TermRel Ψˡ Σˡ Ψʳ Σʳ M M′ A B →
    Diverges Σʳ M′ →
    Σˡ ∣ M —↠ Σˡ′ ∣ N →
    Blame N ⊎ (∃[ Σ″ ] ∃[ N″ ] (Σˡ′ ∣ N —→ Σ″ ∣ N″))
