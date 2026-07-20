module proof.ForallPermutationProperties where

-- File Charter:
--   * Provides structural introduction and congruence lemmas for quotiented
--     type imprecision.
--   * Collapses quotiented imprecision to ordinary imprecision when its source
--     endpoint is ground.
--   * Exhibits adjacent-binder swapping as a bounded, involutive type-context
--     permutation.
--   * Provides ordinary imprecision composition with an `idᵢ` derivation on
--     the right, as needed when promoting a raw MLB candidate.
--   * Contains no selector-specific assumptions.

open import Data.Empty using (⊥-elim)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; cong₂; refl; subst; sym; trans)

open import Types
open import ForallPermutation
open import Imprecision using (idᵢ)
open import ImprecisionWf
open import proof.CastImprecision using
  ( ComposeRightCtx
  ; bound-empty
  ; ⊑-trans-compose-right
  )
open import proof.ImprecisionProperties using
  (idᵢ-no-star; idᵢ-var-identity)
open import proof.TypeProperties using
  ( TyPermutation; rename-cong; renameᵗ-compose; renameᵗ-id
  ; renameᵗ-preserves-WfTy
  )

------------------------------------------------------------------------
-- Adjacent-binder renaming
------------------------------------------------------------------------

swap01-involutive : ∀ X → swap01ᵗ (swap01ᵗ X) ≡ X
swap01-involutive zero = refl
swap01-involutive (suc zero) = refl
swap01-involutive (suc (suc X)) = refl

ext-swap01-involutive :
  ∀ X → extᵗ swap01ᵗ (extᵗ swap01ᵗ X) ≡ X
ext-swap01-involutive zero = refl
ext-swap01-involutive (suc X) = cong suc (swap01-involutive X)

renameᵗ-swap01-involutive :
  ∀ A → renameᵗ swap01ᵗ (renameᵗ swap01ᵗ A) ≡ A
renameᵗ-swap01-involutive A =
  trans
    (renameᵗ-compose swap01ᵗ swap01ᵗ A)
    (trans (rename-cong swap01-involutive A) (renameᵗ-id A))

renameᵗ-ext-swap01-involutive :
  ∀ A →
  renameᵗ (extᵗ swap01ᵗ) (renameᵗ (extᵗ swap01ᵗ) A) ≡ A
renameᵗ-ext-swap01-involutive A =
  trans
    (renameᵗ-compose (extᵗ swap01ᵗ) (extᵗ swap01ᵗ) A)
    (trans (rename-cong ext-swap01-involutive A) (renameᵗ-id A))

------------------------------------------------------------------------
-- Outer-forall shape is invariant under permutation equivalence
------------------------------------------------------------------------

mutual
  ≈∀-preserves-all-shape :
    ∀ {A B} →
    A ≈∀ B →
    ∃[ C ] A ≡ `∀ C →
    ∃[ D ] B ≡ `∀ D
  ≈∀-preserves-all-shape ≈∀-refl allA = allA
  ≈∀-preserves-all-shape (≈∀-sym A≈B) allA =
    ≈∀-reflects-all-shape A≈B allA
  ≈∀-preserves-all-shape (≈∀-trans A≈B B≈C) allA =
    ≈∀-preserves-all-shape B≈C
      (≈∀-preserves-all-shape A≈B allA)
  ≈∀-preserves-all-shape (≈∀-⇒ A≈A′ B≈B′) (C , ())
  ≈∀-preserves-all-shape (≈∀-∀ {B = B} A≈B) allA =
    B , refl
  ≈∀-preserves-all-shape (≈∀-swap {A = A}) allA =
    `∀ (renameᵗ swap01ᵗ A) , refl

  ≈∀-reflects-all-shape :
    ∀ {A B} →
    A ≈∀ B →
    ∃[ D ] B ≡ `∀ D →
    ∃[ C ] A ≡ `∀ C
  ≈∀-reflects-all-shape ≈∀-refl allB = allB
  ≈∀-reflects-all-shape (≈∀-sym A≈B) allB =
    ≈∀-preserves-all-shape A≈B allB
  ≈∀-reflects-all-shape (≈∀-trans A≈B B≈C) allC =
    ≈∀-reflects-all-shape A≈B
      (≈∀-reflects-all-shape B≈C allC)
  ≈∀-reflects-all-shape (≈∀-⇒ A≈A′ B≈B′) (D , ())
  ≈∀-reflects-all-shape (≈∀-∀ {A = A} A≈B) allB =
    A , refl
  ≈∀-reflects-all-shape (≈∀-swap {A = A}) allB =
    `∀ A , refl

≈∀-all-right :
  ∀ {A B} →
  `∀ A ≈∀ B →
  ∃[ C ] B ≡ `∀ C
≈∀-all-right {A = A} A≈B =
  ≈∀-preserves-all-shape A≈B (A , refl)

≈∀-all-left :
  ∀ {A B} →
  A ≈∀ `∀ B →
  ∃[ C ] A ≡ `∀ C
≈∀-all-left {B = B} A≈B =
  ≈∀-reflects-all-shape A≈B (B , refl)

mutual
  ≈∀-arrow-right :
    ∀ {A B C} →
    A ⇒ B ≈∀ C →
    ∃[ A′ ] ∃[ B′ ] C ≡ A′ ⇒ B′
  ≈∀-arrow-right ≈∀-refl = _ , _ , refl
  ≈∀-arrow-right (≈∀-sym C≈A⇒B) =
    ≈∀-arrow-left C≈A⇒B
  ≈∀-arrow-right (≈∀-trans A⇒B≈C C≈D)
      with ≈∀-arrow-right A⇒B≈C
  ≈∀-arrow-right (≈∀-trans A⇒B≈C C≈D)
      | A′ , B′ , refl =
    ≈∀-arrow-right C≈D
  ≈∀-arrow-right
      (≈∀-⇒ {A′ = A′} {B′ = B′} A≈A′ B≈B′) =
    A′ , B′ , refl

  ≈∀-arrow-left :
    ∀ {A B C} →
    C ≈∀ A ⇒ B →
    ∃[ A′ ] ∃[ B′ ] C ≡ A′ ⇒ B′
  ≈∀-arrow-left ≈∀-refl = _ , _ , refl
  ≈∀-arrow-left (≈∀-sym A⇒B≈C) =
    ≈∀-arrow-right A⇒B≈C
  ≈∀-arrow-left (≈∀-trans C≈D D≈A⇒B)
      with ≈∀-arrow-left D≈A⇒B
  ≈∀-arrow-left (≈∀-trans C≈D D≈A⇒B)
      | A′ , B′ , refl =
    ≈∀-arrow-left C≈D
  ≈∀-arrow-left
      (≈∀-⇒ {A = A′} {B = B′} A≈A′ B≈B′) =
    A′ , B′ , refl

------------------------------------------------------------------------
-- Ground types are fixed points of forall permutation
------------------------------------------------------------------------

mutual
  ≈∀-atom-left-eq :
    ∀ {A B} →
    Atom A →
    A ≈∀ B →
    A ≡ B
  ≈∀-atom-left-eq atomA ≈∀-refl = refl
  ≈∀-atom-left-eq atomA (≈∀-sym B≈A) =
    sym (≈∀-atom-right-eq atomA B≈A)
  ≈∀-atom-left-eq atomA (≈∀-trans A≈B B≈C) =
    trans A≡B (≈∀-atom-left-eq (subst Atom A≡B atomA) B≈C)
    where
    A≡B = ≈∀-atom-left-eq atomA A≈B
  ≈∀-atom-left-eq () (≈∀-⇒ A≈A′ B≈B′)
  ≈∀-atom-left-eq () (≈∀-∀ A≈B)
  ≈∀-atom-left-eq () ≈∀-swap

  ≈∀-atom-right-eq :
    ∀ {A B} →
    Atom B →
    A ≈∀ B →
    A ≡ B
  ≈∀-atom-right-eq atomB ≈∀-refl = refl
  ≈∀-atom-right-eq atomB (≈∀-sym B≈A) =
    sym (≈∀-atom-left-eq atomB B≈A)
  ≈∀-atom-right-eq atomC (≈∀-trans A≈B B≈C) =
    trans (≈∀-atom-right-eq atomB A≈B) B≡C
    where
    B≡C = ≈∀-atom-right-eq atomC B≈C
    atomB = subst Atom (sym B≡C) atomC
  ≈∀-atom-right-eq () (≈∀-⇒ A≈A′ B≈B′)
  ≈∀-atom-right-eq () (≈∀-∀ A≈B)
  ≈∀-atom-right-eq () ≈∀-swap

mutual
  ≈∀-ground-left-eq :
    ∀ {G H} →
    Ground G →
    G ≈∀ H →
    G ≡ H
  ≈∀-ground-left-eq gG ≈∀-refl = refl
  ≈∀-ground-left-eq gG (≈∀-sym H≈G) =
    sym (≈∀-ground-right-eq gG H≈G)
  ≈∀-ground-left-eq gG (≈∀-trans G≈H H≈K) =
    trans G≡H
      (≈∀-ground-left-eq (subst Ground G≡H gG) H≈K)
    where
    G≡H = ≈∀-ground-left-eq gG G≈H
  ≈∀-ground-left-eq ★⇒★ (≈∀-⇒ A≈A′ B≈B′) =
    cong₂ _⇒_ (≈∀-atom-left-eq ★ A≈A′)
      (≈∀-atom-left-eq ★ B≈B′)
  ≈∀-ground-left-eq () (≈∀-∀ A≈B)
  ≈∀-ground-left-eq () ≈∀-swap

  ≈∀-ground-right-eq :
    ∀ {G H} →
    Ground H →
    G ≈∀ H →
    G ≡ H
  ≈∀-ground-right-eq gH ≈∀-refl = refl
  ≈∀-ground-right-eq gH (≈∀-sym H≈G) =
    sym (≈∀-ground-left-eq gH H≈G)
  ≈∀-ground-right-eq gK (≈∀-trans G≈H H≈K) =
    trans (≈∀-ground-right-eq gH G≈H) H≡K
    where
    H≡K = ≈∀-ground-right-eq gK H≈K
    gH = subst Ground (sym H≡K) gK
  ≈∀-ground-right-eq ★⇒★ (≈∀-⇒ A≈A′ B≈B′) =
    cong₂ _⇒_ (≈∀-atom-right-eq ★ A≈A′)
      (≈∀-atom-right-eq ★ B≈B′)
  ≈∀-ground-right-eq () (≈∀-∀ A≈B)
  ≈∀-ground-right-eq () ≈∀-swap

ground-quotient-target :
  ∀ {Φ Δᴸ Δᴿ G B′ B} →
  (gG : Ground G) →
  (p : Φ ∣ Δᴸ ⊢ G ⊑ B′ ⊣ Δᴿ) →
  B′ ≈∀ B →
  Φ ∣ Δᴸ ⊢ G ⊑ B ⊣ Δᴿ
ground-quotient-target (＇ X) p@(idˣ X⊑Y X<Δᴸ Y<Δᴿ) B′≈B =
  subst (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
    (≈∀-atom-left-eq (＇ _) B′≈B) p
ground-quotient-target (＇ X) p@(tagˣ X⊑★ X<Δᴸ) B′≈B =
  subst (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
    (≈∀-atom-left-eq ★ B′≈B) p
ground-quotient-target (‵ ι) p@idι B′≈B =
  subst (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
    (≈∀-atom-left-eq (‵ _) B′≈B) p
ground-quotient-target (‵ ι) p@(tag ι) B′≈B =
  subst (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
    (≈∀-atom-left-eq ★ B′≈B) p
ground-quotient-target ★⇒★ p@(id★ ↦ id★) B′≈B =
  subst (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
    (≈∀-ground-left-eq ★⇒★ B′≈B) p
ground-quotient-target ★⇒★ p@(tag id★ ⇛ id★) B′≈B =
  subst (λ T → _ ∣ _ ⊢ _ ⊑ T ⊣ _)
    (≈∀-atom-left-eq ★ B′≈B) p

⊑ᵖ-ground-left :
  ∀ {Φ Δᴸ Δᴿ G B} →
  Ground G →
  Φ ∣ Δᴸ ⊢ G ⊑ᵖ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ G ⊑ B ⊣ Δᴿ
⊑ᵖ-ground-left gG (quotientᵖ G≈G′ G′⊑B′ B′≈B)
    with ≈∀-ground-left-eq gG G≈G′
⊑ᵖ-ground-left gG (quotientᵖ G≈G′ G′⊑B′ B′≈B)
    | refl =
  ground-quotient-target gG G′⊑B′ B′≈B

⊑ᵖ-star-left-eq :
  ∀ {Φ Δᴸ Δᴿ B} →
  Φ ∣ Δᴸ ⊢ ★ ⊑ᵖ B ⊣ Δᴿ →
  B ≡ ★
⊑ᵖ-star-left-eq (quotientᵖ ★≈A A⊑B′ B′≈B)
    with ≈∀-atom-left-eq ★ ★≈A
⊑ᵖ-star-left-eq (quotientᵖ ★≈A A⊑B′ B′≈B)
    | refl with A⊑B′
⊑ᵖ-star-left-eq (quotientᵖ ★≈A A⊑B′ B′≈B)
    | refl | id★ =
  sym (≈∀-atom-left-eq ★ B′≈B)

⊑ᵖ-arrow-left-shape :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ C ⊣ Δᴿ →
  (∃[ A′ ] ∃[ B′ ] C ≡ A′ ⇒ B′) ⊎ C ≡ ★
⊑ᵖ-arrow-left-shape (quotientᵖ A⇒B≈D D⊑E E≈C)
    with ≈∀-arrow-right A⇒B≈D
⊑ᵖ-arrow-left-shape (quotientᵖ A⇒B≈D D⊑E E≈C)
    | D₁ , D₂ , refl with D⊑E
⊑ᵖ-arrow-left-shape (quotientᵖ A⇒B≈D D⊑E E≈C)
    | D₁ , D₂ , refl | p ↦ q
    with ≈∀-arrow-right E≈C
⊑ᵖ-arrow-left-shape (quotientᵖ A⇒B≈D D⊑E E≈C)
    | D₁ , D₂ , refl | p ↦ q | C₁ , C₂ , refl =
  inj₁ (C₁ , C₂ , refl)
⊑ᵖ-arrow-left-shape (quotientᵖ A⇒B≈D D⊑E E≈C)
    | D₁ , D₂ , refl | tag p ⇛ q =
  inj₂ (sym (≈∀-atom-left-eq ★ E≈C))

⊑ᵖ-all-representatives :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ `∀ B ⊣ Δᴿ →
  ∃[ C ] ∃[ D ]
    ((`∀ A ≈∀ `∀ C) ×
     (Φ ∣ Δᴸ ⊢ `∀ C ⊑ `∀ D ⊣ Δᴿ) ×
     (`∀ D ≈∀ `∀ B))
⊑ᵖ-all-representatives
    (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    with ≈∀-all-right A≈A′ | ≈∀-all-left B′≈B
⊑ᵖ-all-representatives
    (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    | C , refl | D , refl =
  C , D , A≈A′ , A′⊑B′ , B′≈B

data AllImprecisionView
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {A : Ty} :
    ∀ {B} → (Φ ∣ Δᴸ ⊢ `∀ A ⊑ B ⊣ Δᴿ) → Set where
  all-paired :
    ∀ {C} →
    (p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
      ⊢ A ⊑ C ⊣ suc Δᴿ) →
    AllImprecisionView (∀ⁱ p)

  all-source :
    ∀ {B} →
    (occ : occurs zero A ≡ true) →
    (p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
      ⊢ A ⊑ B ⊣ Δᴿ) →
    AllImprecisionView (ν occ p)

all-imprecision-view :
  ∀ {Φ Δᴸ Δᴿ A B}
    (p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ B ⊣ Δᴿ) →
  AllImprecisionView p
all-imprecision-view (∀ⁱ p) = all-paired p
all-imprecision-view (ν occ p) = all-source occ p

⊑ᵖ-source-all-view :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ B ⊣ Δᴿ →
  ∃[ C ] ∃[ D ]
    ((`∀ A ≈∀ `∀ C) ×
     ∃[ p ] (AllImprecisionView p × (D ≈∀ B)))
⊑ᵖ-source-all-view
    (quotientᵖ {B′ = B′} A≈A′ A′⊑B′ B′≈B)
    with ≈∀-all-right A≈A′
⊑ᵖ-source-all-view
    (quotientᵖ {B′ = B′} A≈A′ A′⊑B′ B′≈B)
    | C , refl =
  C , B′ , A≈A′ , A′⊑B′ ,
    all-imprecision-view A′⊑B′ , B′≈B

⊑ᵖ-all-view :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ `∀ B ⊣ Δᴿ →
  ∃[ C ] ∃[ D ]
    ((`∀ A ≈∀ `∀ C) ×
     ∃[ p ]
       (AllImprecisionView p × (`∀ D ≈∀ `∀ B)))
⊑ᵖ-all-view (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    with ≈∀-all-right A≈A′ | ≈∀-all-left B′≈B
⊑ᵖ-all-view (quotientᵖ A≈A′ A′⊑B′ B′≈B)
    | C , refl | D , refl =
  C , D , A≈A′ , A′⊑B′ ,
    all-imprecision-view A′⊑B′ , B′≈B

swap01-pres-< :
  ∀ {Δ X} →
  X < suc (suc Δ) →
  swap01ᵗ X < suc (suc Δ)
swap01-pres-< {X = zero} z<s = s<s z<s
swap01-pres-< {X = suc zero} (s<s z<s) = z<s
swap01-pres-< {X = suc (suc X)} (s<s (s<s X<Δ)) =
  s<s (s<s X<Δ)

swap01-permutation :
  ∀ Δ → TyPermutation (suc (suc Δ)) (suc (suc Δ))
swap01-permutation Δ =
  record
    { forward = swap01ᵗ
    ; backward = swap01ᵗ
    ; forward-wf = swap01-pres-<
    ; backward-wf = swap01-pres-<
    ; backward-forward = swap01-involutive
    ; forward-backward = swap01-involutive
    }

swap01-preserves-WfTy :
  ∀ {Δ A} →
  WfTy (suc (suc Δ)) A →
  WfTy (suc (suc Δ)) (renameᵗ swap01ᵗ A)
swap01-preserves-WfTy hA = renameᵗ-preserves-WfTy hA swap01-pres-<

≈∀-double-swap :
  ∀ {A B} →
  renameᵗ swap01ᵗ A ≈∀ B →
  `∀ (`∀ A) ≈∀ `∀ (`∀ B)
≈∀-double-swap Aˢ≈B =
  ≈∀-trans ≈∀-swap (≈∀-∀ (≈∀-∀ Aˢ≈B))

≈∀-double-swap-sym :
  ∀ {A B} →
  A ≈∀ renameᵗ swap01ᵗ B →
  `∀ (`∀ A) ≈∀ `∀ (`∀ B)
≈∀-double-swap-sym A≈Bˢ =
  ≈∀-trans
    (≈∀-∀ (≈∀-∀ A≈Bˢ))
    (≈∀-sym ≈∀-swap)

------------------------------------------------------------------------
-- Ordinary composition with identity imprecision on the right
------------------------------------------------------------------------

compose-right-idᵢ :
  ∀ Δ Φ →
  ComposeRightCtx Δ Φ (idᵢ Δ) Φ
compose-right-idᵢ Δ Φ .ComposeRightCtx.compʳ-var-var x∈ y∈ =
  subst (λ Z → (_ ˣ⊑ˣ Z) ∈ Φ) (idᵢ-var-identity y∈) x∈
compose-right-idᵢ Δ Φ .ComposeRightCtx.compʳ-var-star x∈ Y<Δ y★∈ =
  ⊥-elim (idᵢ-no-star y★∈)
compose-right-idᵢ Δ Φ .ComposeRightCtx.compʳ-star x★∈ = x★∈

⊑-trans-right-idᵢ :
  ∀ {Φ Δᴸ Δᴿ A B C} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  idᵢ Δᴿ ∣ Δᴿ ⊢ B ⊑ C ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
⊑-trans-right-idᵢ {Φ = Φ} {Δᴿ = Δᴿ} A⊑B B⊑C =
  ⊑-trans-compose-right
    (compose-right-idᵢ Δᴿ Φ)
    (bound-empty {Φ = Φ})
    A⊑B
    B⊑C

------------------------------------------------------------------------
-- Quotient introduction and congruence
------------------------------------------------------------------------

⊑→⊑ᵖ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ B ⊣ Δᴿ
⊑→⊑ᵖ A⊑B = quotientᵖ ≈∀-refl A⊑B ≈∀-refl

⊑ᵖ-⇒ :
  ∀ {Φ Δᴸ Δᴿ A A′ B B′} →
  Φ ∣ Δᴸ ⊢ A ⊑ᵖ A′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ B ⊑ᵖ B′ ⊣ Δᴿ →
  Φ ∣ Δᴸ ⊢ A ⇒ B ⊑ᵖ A′ ⇒ B′ ⊣ Δᴿ
⊑ᵖ-⇒ (quotientᵖ A≈C C⊑C′ C′≈A′)
      (quotientᵖ B≈D D⊑D′ D′≈B′) =
  quotientᵖ
    (≈∀-⇒ A≈C B≈D)
    (C⊑C′ ↦ D⊑D′)
    (≈∀-⇒ C′≈A′ D′≈B′)

⊑ᵖ-∀ :
  ∀ {Φ Δᴸ Δᴿ A B} →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
    ⊢ A ⊑ᵖ B ⊣ suc Δᴿ →
  Φ ∣ Δᴸ ⊢ `∀ A ⊑ᵖ `∀ B ⊣ Δᴿ
⊑ᵖ-∀ (quotientᵖ A≈C C⊑D D≈B) =
  quotientᵖ (≈∀-∀ A≈C) (∀ⁱ C⊑D) (≈∀-∀ D≈B)
