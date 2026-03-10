module DynamicGradualGuaranteeCore where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Contexts
open import CastCalculus
open import Coercions

value-not-blame : Valueᶜ blame → ⊥
value-not-blame ()

value-—↠ᶜ-refl : ∀ {V N} → Valueᶜ V → V —↠ᶜ N → N ≡ V
value-—↠ᶜ-refl vV (V ∎ᶜ) = refl
value-—↠ᶜ-refl vV (V —→ᶜ⟨ V→M ⟩ M—↠N) = ⊥-elim (value-irreducible vV V→M)

blame-⊑-value
  : ∀ {V A A′}
  → Valueᶜ V
  → []⊑[] ⊢ blame ⦂ A ⊑ᶜᵀ V ⦂ A′
  → ⊥
blame-⊑-value (V-cast↦ vM′) (⊑castR blame⊑M′ _ _) = blame-⊑-value vM′ blame⊑M′

ground-upper-unique
  : ∀ {G H A}
  → Ground G
  → Ground H
  → G ⊑ A
  → H ⊑ A
  → G ≡ H
ground-upper-unique G-ℕ G-ℕ ⊑-ℕ ⊑-ℕ = refl
ground-upper-unique G-ℕ G-⇒ ⊑-ℕ ()
ground-upper-unique G-⇒ G-ℕ (⊑-⇒ _ _) ()
ground-upper-unique G-⇒ G-⇒ (⊑-⇒ _ _) (⊑-⇒ _ _) = refl

ground-not-⊑★ : ∀ {G} → Ground G → G ⊑ ★ → ⊥
ground-not-⊑★ G-ℕ ()
ground-not-⊑★ G-⇒ ()

--------------------------------------------------------------------------------
-- Precision Inversion Lemmas
--------------------------------------------------------------------------------

ℕ-⊑-inv : ∀ {A} → ℕ ⊑ A → A ≡ ℕ
ℕ-⊑-inv ⊑-ℕ = refl

cast-value-not-ℕ : ∀ {M c A} → Valueᶜ (cast M [ c ]) → ⊢ c ⦂ A ⇨ ℕ → ⊥
cast-value-not-ℕ (V-cast↦ vM) ()

inj-⊑-not-★ : ∀ {V V′ H A}
  → A ≢ ★
  → Valueᶜ V′
  → []⊑[] ⊢ inj V [ H ]! ⦂ ★ ⊑ᶜᵀ V′ ⦂ A
  → Ground H × []⊑[] ⊢ V ⦂ H ⊑ᶜᵀ V′ ⦂ A
inj-⊑-not-★ A≢★ vV′ (⊑inj prec x x₁ x₂) = ⊥-elim (A≢★ refl)
inj-⊑-not-★ A≢★ vV′ (⊑injL V⊑V′ vV h vV′′) = h , V⊑V′
inj-⊑-not-★ A≢★ (V-cast↦ vV′) (⊑castR V⊑V′ c⦂ id⊑c)
  with c⦂
... | ⊢↦ c₁⦂ c₂⦂
  with inj-⊑-not-★ (λ ()) vV′ V⊑V′
... | g , V⊑M′
  with g
... | G-⇒ =
  g , ⊑castR V⊑M′ (⊢↦ c₁⦂ c₂⦂)
      (⊑idL↦ (⊑id★ c₁⦂) (⊑id★ c₂⦂))
... | G-ℕ
  with ⊑ᶜᵀ-type-precision V⊑M′
... | ()

inj-⊑-inj : ∀{V V′}{G G′}
   → []⊑[] ⊢ inj V [ G ]! ⦂ ★ ⊑ᶜᵀ inj V′ [ G′ ]! ⦂ ★
   → []⊑[] ⊢ V ⦂ G ⊑ᶜᵀ V′ ⦂ G′
inj-⊑-inj (⊑inj injV≤injV′ x x₁ x₂) = injV≤injV′
inj-⊑-inj (⊑injL injV≤injV′ x g (V-! x₂))
    with ⊑ᶜᵀ-type-precision injV≤injV′ | g
... | ⊑-★ | ()

inj-left-typed
  : ∀ {V M′ G A′}
  → []⊑[] ⊢ inj V [ G ]! ⦂ ★ ⊑ᶜᵀ M′ ⦂ A′
  → [] ⊢ᶜ V ⦂ G
inj-left-typed injV⊑M′
    with ⊑ᶜᵀ-left-typed injV⊑M′
... | ⊢! V⦂ g vV = V⦂

star-to-inj
  : ∀ {V V′ G}
  → []⊑[] ⊢ V ⦂ ★ ⊑ᶜᵀ V′ ⦂ G
  → Valueᶜ V
  → Valueᶜ V′
  → Ground G
  → []⊑[] ⊢ V ⦂ ★ ⊑ᶜᵀ inj V′ [ G ]! ⦂ ★
star-to-inj V≤V′ vV vV′ G-ℕ
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl
    with inj-⊑-not-★ (λ ()) vV′ V≤V′
... | g′ , W≤V′
    with ground-upper-unique g′ G-ℕ (⊑ᶜᵀ-type-precision W≤V′) ⊑-ℕ
... | refl = ⊑inj W≤V′ vW vV′ G-ℕ
star-to-inj V≤V′ vV vV′ G-⇒
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl
    with inj-⊑-not-★ (λ ()) vV′ V≤V′
... | g′ , W≤V′
    with ground-upper-unique g′ G-⇒ (⊑ᶜᵀ-type-precision W≤V′) (⊑-⇒ ⊑-refl ⊑-refl)
... | refl = ⊑inj W≤V′ vW vV′ G-⇒


less-ground-not-★ : ∀ {G A}
  → Ground G
  → G ⊑ A
  → A ≢ ★
less-ground-not-★ G-ℕ () refl
less-ground-not-★ G-⇒ () refl

proj-?-less-ground
  : ∀ {V V′ A G}
  → Ground G
  → []⊑[] ⊢ V ⦂ ★ ⊑ᶜᵀ V′ ⦂ A
  → Valueᶜ V
  → Valueᶜ V′
  → G ⊑ A
  → ∃[ W ] Valueᶜ W × []⊑[] ⊢ W ⦂ G ⊑ᶜᵀ V′ ⦂ A × cast V [ G `? ] —↠ᶜ W
proj-?-less-ground gG V⊑V′ vV vV′ G⊑A
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V⊑V′)
... | H , W , vW , refl
    with inj-⊑-not-★ (less-ground-not-★ gG G⊑A) vV′ V⊑V′ 
... | g , W⊑V′
    with ground-upper-unique g gG (⊑ᶜᵀ-type-precision W⊑V′) G⊑A
... | refl =
    W
    , vW
    , W⊑V′
    , (cast (inj W [ _ ]!) [ _ `? ]
         —→ᶜ⟨ β-proj-inj-ok vW ⟩
       W
       ∎ᶜ)

⊑castR-id-inversion : ∀{A A′}{M M′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ cast M′ [ idᶜ A′ ] ⦂ A′
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
⊑castR-id-inversion (⊑cast M⊑M′ c≤ c⦂ ⊢idᶜ) = ⊑castL M⊑M′ c⦂ c≤
⊑castR-id-inversion (⊑castL M⊑M′ c⦂ c≤id) = ⊑castL (⊑castR-id-inversion M⊑M′) c⦂ c≤id
⊑castR-id-inversion (⊑castR M⊑M′ ⊢idᶜ id⊑c′) = M⊑M′

⊑castL-id-inversion : ∀{A A′}{M M′}
  → []⊑[] ⊢ cast M [ idᶜ A ] ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
⊑castL-id-inversion (⊑cast M⊑M′ c≤ ⊢idᶜ c′⦂) = ⊑castR M⊑M′ c′⦂ c≤
⊑castL-id-inversion (⊑castL M⊑M′ c⦂ c≤id)
  with coercion-type-unique c⦂ ⊢idᶜ
... | refl , refl = M⊑M′
⊑castL-id-inversion (⊑castR M⊑M′ c′⦂ id⊑c′) =
  ⊑castR (⊑castL-id-inversion M⊑M′) c′⦂ id⊑c′
⊑castL-id-inversion (⊑blameR (⊢cast M⦂ c⦂) A⊑A′)
  with coercion-type-unique c⦂ ⊢idᶜ
... | refl , refl = ⊑blameR M⦂ A⊑A′

--------------------------------------------------------------------------------
-- Substitution Preserves Precision
--------------------------------------------------------------------------------

renameᶜ-value : ∀ {ρ V} → Valueᶜ V → Valueᶜ (renameᶜ ρ V)
renameᶜ-value V-$ = V-$
renameᶜ-value V-ƛ = V-ƛ
renameᶜ-value (V-! vV) = V-! (renameᶜ-value vV)
renameᶜ-value (V-cast↦ vV) = V-cast↦ (renameᶜ-value vV)

substᶜ-value : ∀ {σ V} → Valueᶜ V → Valueᶜ (substᶜ σ V)
substᶜ-value V-$ = V-$
substᶜ-value V-ƛ = V-ƛ
substᶜ-value (V-! vV) = V-! (substᶜ-value vV)
substᶜ-value (V-cast↦ vV) = V-cast↦ (substᶜ-value vV)

Substᶜ-⊑
  : Ctx
  → Ctx
  → ∀ {Δ Δ′}
  → (ρ′ : Δ ⊑ᵉ Δ′)
  → Substᶜ
  → Substᶜ
  → Set
Substᶜ-⊑ Γ Γ′ ρ′ σ σ′ =
  ∀ {x A A′}
  → Γ ∋ x ⦂ A
  → Γ′ ∋ x ⦂ A′
  → ρ′ ⊢ σ x ⦂ A ⊑ᶜᵀ σ′ x ⦂ A′

renameᶜ-⊑
  : ∀ {Γ₁ Γ₂ Δ₁ Δ₂ A A′ M M′}
  → (r : Renameᶜ)
  → Renᶜ-typed r Γ₁ Δ₁
  → Renᶜ-typed r Γ₂ Δ₂
  → (ρ′ : Δ₁ ⊑ᵉ Δ₂)
  → {ρ : Γ₁ ⊑ᵉ Γ₂}
  → ρ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → ρ′ ⊢ renameᶜ r M ⦂ A ⊑ᶜᵀ renameᶜ r M′ ⦂ A′
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑` ∋x ∋x′) = ⊑` (r-typed ∋x) (r′-typed ∋x′)
renameᶜ-⊑ r r-typed r′-typed ρ′ ⊑$ = ⊑$
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑ƛ A⊑A′ N⊑M) =
  ⊑ƛ A⊑A′
    (renameᶜ-⊑ (extᶜ r)
      (ext-renᶜ-typed r-typed)
      (ext-renᶜ-typed r′-typed)
      (extend-⊑ᵉ A⊑A′ ρ′)
      N⊑M)
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑· L⊑L′ M⊑M′) =
  ⊑· (renameᶜ-⊑ r r-typed r′-typed ρ′ L⊑L′) (renameᶜ-⊑ r r-typed r′-typed ρ′ M⊑M′)
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑cast M⊑M′ c⊑c′ cwt c′wt) =
  ⊑cast (renameᶜ-⊑ r r-typed r′-typed ρ′ M⊑M′) c⊑c′ cwt c′wt
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑castL M⊑M′ cwt c⊑id) =
  ⊑castL (renameᶜ-⊑ r r-typed r′-typed ρ′ M⊑M′) cwt c⊑id
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑castR M⊑M′ c′wt id⊑c′) =
  ⊑castR (renameᶜ-⊑ r r-typed r′-typed ρ′ M⊑M′) c′wt id⊑c′
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑inj M⊑M′ vM vM′ g) =
  ⊑inj
    (renameᶜ-⊑ r r-typed r′-typed ρ′ M⊑M′)
    (renameᶜ-value vM)
    (renameᶜ-value vM′)
    g
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑injL M⊑M′ vM g vM′) =
  ⊑injL
    (renameᶜ-⊑ r r-typed r′-typed ρ′ M⊑M′)
    (renameᶜ-value vM)
    g
    (renameᶜ-value vM′)
renameᶜ-⊑ r r-typed r′-typed ρ′ (⊑blameR M⦂A A⊑A′) =
  ⊑blameR (renameᶜ-preserve r-typed M⦂A) A⊑A′

wk-suc-⊑
  : ∀ {Γ Γ′ A A′ B B′ M M′}
  → (B⊑B′ : B ⊑ B′)
  → (ρ : Γ ⊑ᵉ Γ′)
  → ρ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → (extend-⊑ᵉ B⊑B′ ρ) ⊢ renameᶜ suc M ⦂ A ⊑ᶜᵀ renameᶜ suc M′ ⦂ A′
wk-suc-⊑ B⊑B′ ρ M⊑M′ =
  renameᶜ-⊑ suc wk-renᶜ-typed wk-renᶜ-typed (extend-⊑ᵉ B⊑B′ ρ) M⊑M′

ext-substᶜ-⊑
  : ∀ {Γ Γ′ Δ Δ′ A A′ σ σ′}
  → (ρ′ : Δ ⊑ᵉ Δ′)
  → (A⊑A′ : A ⊑ A′)
  → Substᶜ-⊑ Γ Γ′ ρ′ σ σ′
  → Substᶜ-⊑ (A ∷ Γ) (A′ ∷ Γ′) (extend-⊑ᵉ A⊑A′ ρ′) (extsᶜ σ) (extsᶜ σ′)
ext-substᶜ-⊑ ρ′ A⊑A′ σ⊑σ′ {x = zero} Z Z = ⊑` Z Z
ext-substᶜ-⊑ ρ′ A⊑A′ σ⊑σ′ {x = suc x} (S ∋x) (S ∋x′) =
  wk-suc-⊑ A⊑A′ ρ′ (σ⊑σ′ ∋x ∋x′)

substᶜ-⊑
  : ∀ {Γ Γ′ Δ Δ′ M M′ A A′ σ σ′}
  → (ρ : Γ ⊑ᵉ Γ′)
  → (ρ′ : Δ ⊑ᵉ Δ′)
  → Substᶜ-typed σ Γ Δ
  → Substᶜ-typed σ′ Γ′ Δ′
  → Substᶜ-⊑ Γ Γ′ ρ′ σ σ′
  → ρ ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → ρ′ ⊢ substᶜ σ M ⦂ A ⊑ᶜᵀ substᶜ σ′ M′ ⦂ A′
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑` ∋x ∋x′) = σ⊑σ′ ∋x ∋x′
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ ⊑$ = ⊑$
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑ƛ A⊑A′ N⊑M) =
  ⊑ƛ A⊑A′
    (substᶜ-⊑
      (extend-⊑ᵉ A⊑A′ ρ)
      (extend-⊑ᵉ A⊑A′ ρ′)
      (ext-substᶜ-typed σ-typed)
      (ext-substᶜ-typed σ′-typed)
      (ext-substᶜ-⊑ ρ′ A⊑A′ σ⊑σ′)
      N⊑M)
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑· L⊑L′ M⊑M′) =
  ⊑· (substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ L⊑L′)
     (substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ M⊑M′)
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑cast M⊑M′ c⊑c′ cwt c′wt) =
  ⊑cast (substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ M⊑M′) c⊑c′ cwt c′wt
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑castL M⊑M′ cwt c⊑id) =
  ⊑castL (substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ M⊑M′) cwt c⊑id
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑castR M⊑M′ c′wt id⊑c′) =
  ⊑castR (substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ M⊑M′) c′wt id⊑c′
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑inj M⊑M′ vM vM′ g) =
  ⊑inj
    (substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ M⊑M′)
    (substᶜ-value vM)
    (substᶜ-value vM′)
    g
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑injL M⊑M′ vM g vM′) =
  ⊑injL
    (substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ M⊑M′)
    (substᶜ-value vM)
    g
    (substᶜ-value vM′)
substᶜ-⊑ ρ ρ′ σ-typed σ′-typed σ⊑σ′ (⊑blameR M⦂A A⊑A′) =
  ⊑blameR (substᶜ-preserve σ-typed M⦂A) A⊑A′

single-substᶜ-⊑
  : ∀ {A A′ V V′}
  → (A⊑A′ : A ⊑ A′)
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → Substᶜ-⊑ (A ∷ []) (A′ ∷ []) []⊑[] (singleEnvᶜ V) (singleEnvᶜ V′)
single-substᶜ-⊑ A⊑A′ V⊑V′ Z Z = V⊑V′
single-substᶜ-⊑ A⊑A′ V⊑V′ (S ()) ∋x′

[]ᶜ-⊑
  : ∀ {N N′ V V′ A A′ B B′}
  → (A⊑A′ : A ⊑ A′)
  → (extend-⊑ᵉ A⊑A′ []⊑[]) ⊢ N ⦂ B ⊑ᶜᵀ N′ ⦂ B′
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → []⊑[] ⊢ N [ V ]ᶜ ⦂ B ⊑ᶜᵀ N′ [ V′ ]ᶜ ⦂ B′
[]ᶜ-⊑ A⊑A′ N⊑N′ V⊑V′ =
  substᶜ-⊑
    (extend-⊑ᵉ A⊑A′ []⊑[])
    []⊑[]
    (single-substᶜ-typed (⊑ᶜᵀ-left-typed V⊑V′))
    (single-substᶜ-typed (⊑ᶜᵀ-right-typed V⊑V′))
    (single-substᶜ-⊑ A⊑A′ V⊑V′)
    N⊑N′

--------------------------------------------------------------------------------
-- Cast Left Value of id
--
-- If V ⊑ V′ and c ⊑ id
-- then V[c] —↠ᶜ V₂ and V₂ ⊑ V′ for some V₂.
---
--------------------------------------------------------------------------------

cast-seq-lift
  : ∀ {V V₁}{c d}
  → Valueᶜ V
  → cast V [ c ] —↠ᶜ V₁
  → cast V [ c ⨟ d ] —↠ᶜ cast V₁ [ d ]
cast-seq-lift {V} {V₁} {c} {d} vV V-c—↠V₁ =
  cast V [ c ⨟ d ]
    —→ᶜ⟨ β-seq vV ⟩
  cast (cast V [ c ]) [ d ]
    —↠ᶜ⟨ ξ* (cast□[ d ]) V-c—↠V₁ ⟩
  cast V₁ [ d ]
    ∎ᶜ

cast-left-id-val : ∀ {V V′}{A A′ B}{c}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → Valueᶜ V
  → Valueᶜ V′
  → ⊢ c ⦂ A ⇨ B
  → c ⊑ᶜ idᶜ A′
  → ∃[ V₂ ] cast V [ c ] —↠ᶜ V₂ × []⊑[] ⊢ V₂ ⦂ B ⊑ᶜᵀ V′ ⦂ A′ × Valueᶜ V₂
cast-left-id-val {V} {c = c} V≤V′ vV vV′ ⊢idᶜ (⊑idᶜ A⊑A′) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤V′ , vV
cast-left-id-val {V} {c = c} V≤V′ vV vV′ ⊢idᶜ (⊑idL nseq c⦂ A⊑B A⊑C) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤V′ , vV
cast-left-id-val {V} {c = c} V≤V′ vV vV′ ⊢idᶜ (⊑idR nseq ⊢idᶜ A⊑A′ B⊑A′) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤V′ , vV
cast-left-id-val {V} {V′}{G}{A′} {c = G !} V≤V′ vV vV′ (⊢!{G = G} g)
       (⊑idR nseq (⊢! g′) A⊑A′ B⊑A′) =
  let prec : []⊑[] ⊢ V ⦂ G ⊑ᶜᵀ V′ ⦂ A′
      prec = V≤V′ in
  let red = cast V [ G ! ] —→ᶜ⟨ β-inj vV ⟩
            inj V [ G ]! ∎ᶜ in
  let prec′ : []⊑[] ⊢ inj V [ G ]! ⦂ ★ ⊑ᶜᵀ V′ ⦂ A′
      prec′  = ⊑injL V≤V′ vV g vV′ in
  inj V [ G ]! , red , prec′ , V-! vV

cast-left-id-val {V} {V′} {A′ = A′} {c = c} V≤V′ vV vV′ (⊢? G-ℕ) (⊑idR nseq (⊢? g′) A⊑A′ B⊑A′)
    with proj-?-less-ground G-ℕ V≤V′ vV vV′ B⊑A′
... | W , vW , W⊑V′ , V-?—↠W =
    W , V-?—↠W , W⊑V′ , vW
  
cast-left-id-val {V} {V′} {A′ = A′} {c = c} V≤V′ vV vV′ (⊢? G-⇒) (⊑idR nseq (⊢? g′) A⊑A′ B⊑A′)
    with proj-?-less-ground G-⇒ V≤V′ vV vV′ B⊑A′
... | W , vW , W⊑V′ , V-?—↠W =
    W , V-?—↠W , W⊑V′ , vW

cast-left-id-val {V} {V′} {c = c} V≤V′ vV vV′ (⊢↦ cwt₁ dwt₁) (⊑idR↦ c≤id d≤id) =
  cast V [ c ] , (cast V [ c ] ∎ᶜ)
  , ⊑castL V≤V′ (⊢↦ cwt₁ dwt₁) (⊑idR↦ c≤id d≤id)
  , V-cast↦ vV
cast-left-id-val {V} {V′} {c = c ⨟ d} V≤V′ vV vV′ (⊢⨟ c⦂ d⦂) (⊑idR⨟ c≤id d≤id)
  with cast-left-id-val V≤V′ vV vV′ c⦂ c≤id
... | V₁ , V-c—↠V₁ , V₁⊑V′ , vV₁
  with cast-left-id-val V₁⊑V′ vV₁ vV′ d⦂ d≤id
... | V₂ , V₁-d—↠V₂ , V₂⊑V′ , vV₂ =
  V₂
  , (cast V [ c ⨟ d ]
       —↠ᶜ⟨ cast-seq-lift vV V-c—↠V₁ ⟩
     cast V₁ [ d ]
       —↠ᶜ⟨ V₁-d—↠V₂ ⟩
     V₂
     ∎ᶜ)
  , V₂⊑V′
  , vV₂
cast-left-id-val {V} {V′} {A′ = A′} {c = (★ ⇒ ★) `? ⨟ c} V≤V′ vV vV′ (⊢⨟ (⊢? G-⇒) c⦂) (⊑drop? c≤id)
  with ⊑ᶜ→⊑ ⊢idᶜ c⦂ c≤id
... | A⊑A′ , _
  with A⊑A′
... | ⊑-⇒ A₁⊑A₂ B₁⊑B₂
  with proj-?-less-ground G-⇒ V≤V′ vV vV′ A⊑A′
... | W , vW , W⊑V′ , V-?—↠W
  with cast-left-id-val W⊑V′ vW vV′ c⦂ c≤id
... | V₂ , W-c—↠V₂ , V₂⊑V′ , vV₂ =
  V₂
  , (cast V [ (★ ⇒ ★) `? ⨟ c ]
       —↠ᶜ⟨ cast-seq-lift vV V-?—↠W ⟩
     cast W [ c ]
       —↠ᶜ⟨ W-c—↠V₂ ⟩
     V₂
     ∎ᶜ)
  , V₂⊑V′
  , vV₂
cast-left-id-val {V} {V′} {c = c ⨟ (★ ⇒ ★) !} V≤V′ vV vV′ (⊢⨟ c⦂ (⊢! G-⇒)) (⊑drop! c≤id)
  with cast-left-id-val V≤V′ vV vV′ c⦂ c≤id
... | V₁ , V-c—↠V₁ , V₁⊑V′ , vV₁ =
  inj V₁ [ ★ ⇒ ★ ]!
  , (cast V [ c ⨟ (★ ⇒ ★) ! ]
       —↠ᶜ⟨ cast-seq-lift vV V-c—↠V₁ ⟩
     cast V₁ [ (★ ⇒ ★) ! ]
       —→ᶜ⟨ β-inj vV₁ ⟩
     inj V₁ [ ★ ⇒ ★ ]!
     ∎ᶜ)
  , ⊑injL V₁⊑V′ vV₁ G-⇒ vV′
  , V-! vV₁

--------------------------------------------------------------------------------
-- Cast Left of Arrow
--
-- If V ⊑ V′ and c ⊑ c₁↦c₂
-- then V[c] —↠ᶜ V₂ and V₂ ⊑ V′[c₁↦c₂] for some V₂.
---
--------------------------------------------------------------------------------

cast-left-↦-val-id : ∀ {V V′}{A A′ B B′ A₀}{c c₁ c₂}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → Valueᶜ V → ⊢ c ⦂ A ⇨ B → ⊢ (c₁ ↦ c₂) ⦂ A′ ⇨ B′
  → c ≡ idᶜ A₀ → c ⊑ᶜ (c₁ ↦ c₂)
  → ∃[ V₂ ] cast V [ c ] —↠ᶜ V₂ × []⊑[] ⊢ V₂ ⦂ B ⊑ᶜᵀ cast V′ [ c₁ ↦ c₂ ] ⦂ B′ × Valueᶜ V₂
cast-left-↦-val-id {V} {A₀ = A₀} V⊑V′ vV cwt c′wt refl id≤c′
  with coercion-type-unique cwt (⊢idᶜ {A = A₀})
... | refl , refl =
  V , (cast V [ _ ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ)
  , ⊑castR V⊑V′ c′wt id≤c′
  , vV

cast-left-↦-val : ∀ {V V′}{A A′ B B′}{c c₁ c₂}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → Valueᶜ V → Valueᶜ V′ → ⊢ c ⦂ A ⇨ B → ⊢ (c₁ ↦ c₂) ⦂ A′ ⇨ B′
  → c ⊑ᶜ (c₁ ↦ c₂)
  → ∃[ V₂ ] cast V [ c ] —↠ᶜ V₂ × []⊑[] ⊢ V₂ ⦂ B ⊑ᶜᵀ cast V′ [ c₁ ↦ c₂ ] ⦂ B′ × Valueᶜ V₂
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂) (⊑↦ c₁⊑c′₁ d₁⊑d′₁) =
  cast V [ _ ] , (cast V [ _ ] ∎ᶜ)
  , ⊑cast V⊑V′ (⊑↦ c₁⊑c′₁ d₁⊑d′₁) cwt c′wt
  , V-cast↦ vV
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt (⊑idL↦★ c≤id d≤id)
  = cast-left-↦-val-id V⊑V′ vV cwt c′wt refl (⊑idL↦★ c≤id d≤id)
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt (⊑idL↦ c≤id d≤id)
  = cast-left-↦-val-id V⊑V′ vV cwt c′wt refl (⊑idL↦ c≤id d≤id)
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
  = cast-left-↦-val-id V⊑V′ vV cwt c′wt refl (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ (⊢⨟ (⊢? G-⇒) dwt) c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑drop? {c = c₀} {c′ = d} d⊑c₀)
  with proj-?-less-ground G-⇒ V⊑V′ vV vV′ (⊑-⇒ ⊑-★ ⊑-★)
... | W , vW , W⊑V′ , V-?—↠W
  with cast-left-↦-val W⊑V′ vW vV′ dwt c′wt d⊑c₀
... | V₂ , W-d—↠V₂ , V₂⊑castV′ , vV₂ =
  V₂
  , (cast V [ _ ]
       —↠ᶜ⟨ cast-seq-lift vV V-?—↠W ⟩
     cast W [ d ]
       —↠ᶜ⟨ W-d—↠V₂ ⟩
     V₂
     ∎ᶜ)
  , V₂⊑castV′
  , vV₂
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ (⊢⨟ dwt (⊢! G-⇒)) c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑drop! {c = c₀} {c′ = d} d⊑c₀)
  with cast-left-↦-val V⊑V′ vV vV′ dwt c′wt d⊑c₀
... | V₁ , V-d—↠V₁ , V₁⊑castV′ , vV₁ =
  inj V₁ [ ★ ⇒ ★ ]!
  , (cast V [ _ ]
       —↠ᶜ⟨ cast-seq-lift vV V-d—↠V₁ ⟩
     cast V₁ [ (★ ⇒ ★) ! ]
       —→ᶜ⟨ β-inj vV₁ ⟩
     inj V₁ [ ★ ⇒ ★ ]!
     ∎ᶜ)
  , ⊑injL V₁⊑castV′ vV₁ G-⇒ (V-cast↦ vV′)
  , V-! vV₁

cast-left-⨟-val : ∀{V V′}{A A′ B B′ C′}{d c′ d′}
   → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
   → Valueᶜ V
   → Valueᶜ V′
   → d ⊑ᶜ c′ ⨟ d′
   → ⊢ d ⦂ A ⇨ B
   → ⊢ c′ ⦂ A′ ⇨ B′
   → ⊢ d′ ⦂ B′ ⇨ C′
   → ∃[ N₂ ] cast V [ d ] —↠ᶜ N₂ × []⊑[] ⊢ N₂ ⦂ B ⊑ᶜᵀ cast cast V′ [ c′ ] [ d′ ] ⦂ C′
cast-left-⨟-val{V} V≤V′ vV vV′ (⊑idL⨟ d≤c′⨟d′ d≤c′⨟d′₁) ⊢idᶜ c′⦂ d′⦂ =
  cast V [ idᶜ _ ] , (_ ∎ᶜ) , ⊑castR (⊑cast V≤V′ d≤c′⨟d′ ⊢idᶜ c′⦂) d′⦂ d≤c′⨟d′₁
cast-left-⨟-val {V} {V′} {cd} {c′} {d′} V≤V′ vV vV′ (⊑⨟ {c′ = c} {d′ = d} d≤c′⨟d′ d≤c′⨟d′₁) (⊢⨟ d⦂ d⦂₁) c′⦂ d′⦂ =
  cast cast V [ c ] [ d ]
  , (cast V [ c ⨟ d ] —→ᶜ⟨ β-seq vV ⟩ cast (cast V [ c ]) [ d ] ∎ᶜ )
  , ⊑cast (⊑cast V≤V′ d≤c′⨟d′ d⦂ c′⦂) d≤c′⨟d′₁ d⦂₁ d′⦂
cast-left-⨟-val {V} V≤V′ vV vV′ (⊑drop? {c′ = d} d≤c′⨟d′) (⊢⨟ (⊢? x) d⦂₁) c′⦂ d′⦂
    with ⊑ᶜ→⊑ (⊢⨟ c′⦂ d′⦂) d⦂₁ d≤c′⨟d′
... | aa , bb
    with cast-left-id-val V≤V′ vV vV′ (⊢? x) (⊑idR atom-? (⊢? x) ⊑-★ aa)
... | V₂ , →V₂ , V₂≤ , vV₂
    with cast-left-⨟-val V₂≤ vV₂ vV′ d≤c′⨟d′ d⦂₁ c′⦂ d′⦂
... | N₂ , →N₂ , N₂≤ =
     let red = cast V [ ((★ ⇒ ★) `?) ⨟ d ] —↠ᶜ⟨ cast-seq-lift vV →V₂ ⟩
               cast V₂ [ d ] —↠ᶜ⟨ →N₂ ⟩
               N₂ ∎ᶜ in
     N₂ , red , N₂≤
cast-left-⨟-val {V} V≤V′ vV vV′ (⊑drop!{c′ ⨟ d′}{d} d≤c′⨟d′) (⊢⨟ d⦂ (⊢! x)) c′⦂ d′⦂ 
    with ⊑ᶜ→⊑ (⊢⨟ c′⦂ d′⦂) d⦂ d≤c′⨟d′
... | aa , ⊑-⇒ bb bb₁
    with cast-left-⨟-val V≤V′ vV vV′ d≤c′⨟d′ d⦂ c′⦂ d′⦂
... | N₂ , →N₂ , N₂≤ =
    let red = cast V [ d ⨟ (★ ⇒ ★) ! ] —↠ᶜ⟨ cast-seq-lift vV →N₂ ⟩
              cast N₂ [ (★ ⇒ ★) ! ]
              ∎ᶜ in
    cast N₂ [ (★ ⇒ ★) ! ]
    , red
    , ⊑castL N₂≤ (⊢! x) (⊑idR atom-! (⊢! x) (⊑-⇒ bb bb₁) ⊑-★)

--------------------------------------------------------------------------------
cast-left-?-val : ∀ {V V′ A B A′}{c}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ inj V′ [ A′ ]! ⦂ ★
  → Valueᶜ V
  → Valueᶜ V′
  → c ⊑ᶜ (A′ `?)
  → ⊢ c ⦂ A ⇨ B
  → ∃[ N ] cast V [ c ] —↠ᶜ N × []⊑[] ⊢ N ⦂ B ⊑ᶜᵀ V′ ⦂ A′
cast-left-?-val {V} {V′} {A′ = A′} {c = A₁ `?}
  V≤V′! vV vV′ (⊑? A₁⊑A′) (⊢? gA₁)
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′!)
... | G , W , vW , refl
    with ⊑ᶜᵀ-left-typed V≤V′!
... | ⊢! W⦂ gG vW′
    with ⊑ᶜᵀ-right-typed V≤V′!
... | ⊢! V′⦂ gA′ vV′′
    with inj-⊑-inj V≤V′!
... | W≤V′
    with ground-upper-unique gG gA′ (⊑ᶜᵀ-type-precision W≤V′) ⊑-refl
... | refl
    with ground-upper-unique gA₁ gA′ A₁⊑A′ ⊑-refl
... | refl =
    W
    , (cast (inj W [ A′ ]!) [ A′ `? ]
         —→ᶜ⟨ β-proj-inj-ok vW ⟩
       W
       ∎ᶜ)
    , W≤V′
cast-left-?-val {V} {V′} {A′ = A′} {c = idᶜ A₀}
  V≤V′! vV vV′ (⊑idL atom-? (⊢? gA′) A₀⊑★ A₀⊑A′) ⊢idᶜ
    with A₀⊑★
... | ⊑-★
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′!)
... | G , W , vW , refl
    with ⊑ᶜᵀ-left-typed V≤V′!
... | ⊢! W⦂ gG vW′
    with inj-⊑-inj V≤V′!
... | W≤V′ =
    inj W [ G ]!
    , (cast (inj W [ G ]!) [ idᶜ ★ ]
         —→ᶜ⟨ β-id (V-! vW) ⟩
       inj W [ G ]!
       ∎ᶜ)
    , ⊑injL W≤V′ vW gG vV′
cast-left-?-val {A′ = A′}
  V≤V′! vV vV′ (⊑drop? {c′ = d} d≤?) (⊢⨟ (⊢? G-⇒) d⦂)
    with ⊑ᶜᵀ-right-typed V≤V′!
... | ⊢! V′⦂ gA′ vV′′
    with ⊑ᶜ→⊑ (⊢? gA′) d⦂ d≤?
... | A⊑★ , B⊑A′
    with A⊑★
... | ()
cast-left-?-val {V} {V′} {A′ = A′} {c = d ⨟ (★ ⇒ ★) !}
  V≤V′! vV vV′ (⊑drop! {c′ = d} d≤?) (⊢⨟ d⦂ (⊢! G-⇒))
    with cast-left-?-val V≤V′! vV vV′ d≤? d⦂
... | N , V-d—↠N , N≤
    = cast N [ (★ ⇒ ★) ! ]
    , (cast V [ d ⨟ (★ ⇒ ★) ! ]
         —↠ᶜ⟨ cast-seq-lift vV V-d—↠N ⟩
       cast N [ (★ ⇒ ★) ! ]
       ∎ᶜ)
  , ⊑castL N≤ (⊢! G-⇒)
      (⊑idR atom-! (⊢! G-⇒) (⊑ᶜᵀ-type-precision N≤) ⊑-★)

--------------------------------------------------------------------------------
-- Catchup
--
-- If N ⊑ V′
-- then N —↠ᶜ V and V ⊑ V′ for some V.
---
--------------------------------------------------------------------------------
catchup-cast-idL↦ : ∀ {M M′ V A A′ B B′ A₀}{c c′}
  → (M—↠V : M —↠ᶜ V)
  → Valueᶜ V
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → ⊢ c ⦂ A ⇨ B → ⊢ c′ ⦂ A′ ⇨ B′
  → c ≡ idᶜ A₀ → c ⊑ᶜ c′
  → ∃[ V₂ ] Valueᶜ V₂ × (cast M [ c ] —↠ᶜ V₂) × []⊑[] ⊢ V₂ ⦂ B ⊑ᶜᵀ cast M′ [ c′ ] ⦂ B′
catchup-cast-idL↦ {M = M} {A₀ = A₀}
  M—↠V vV V⊑M′ cwt c′wt refl id≤c′
  with coercion-type-unique cwt (⊢idᶜ {A = A₀})
... | refl , refl =
  _ , vV
  , (cast M [ _ ]
       —↠ᶜ⟨ ξ* (cast□[ _ ]) M—↠V ⟩
     cast _ [ _ ]
       —→ᶜ⟨ β-id vV ⟩
     _
     ∎ᶜ)
  , ⊑castR V⊑M′ c′wt id≤c′

catchup : ∀ {V′ N A A′}
  → Valueᶜ V′
  → []⊑[] ⊢ N ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → ∃[ V ] ((Valueᶜ V) × (N —↠ᶜ V) × ([]⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′))
catchup vV′ (⊑` _ ())
catchup vV′ ⊑$ = $ _ , V-$ , ($ _ ∎ᶜ) , ⊑$
catchup vV′ (⊑ƛ A⊑A′ N⊑M) = ƛ _ ⇒ _ , V-ƛ , (ƛ _ ⇒ _ ∎ᶜ) , (⊑ƛ A⊑A′ N⊑M)
catchup () (⊑· L⊑L′ M⊑M′)
catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂))
    with catchup vV′ M⊑M′
... | V , vV , M—↠V , V⊑M′
    with c⊑c′
... | ⊑↦ c₁⊑c′₁ d₁⊑d′₁ =
      cast V [ c ] , V-cast↦ vV
      , (cast M [ c ]
           —↠ᶜ⟨ ξ* (cast□[ c ]) M—↠V ⟩
         cast V [ c ]
         ∎ᶜ)
      , (⊑cast V⊑M′ (⊑↦ c₁⊑c′₁ d₁⊑d′₁) cwt c′wt)
catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt)
    | V , vV , M—↠V , V⊑M′
    | ⊑idL↦★ c≤id d≤id
    = catchup-cast-idL↦ M—↠V vV V⊑M′ cwt c′wt refl (⊑idL↦★ c≤id d≤id)
catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt)
    | V , vV , M—↠V , V⊑M′
    | ⊑idL↦ c≤id d≤id
    = catchup-cast-idL↦ M—↠V vV V⊑M′ cwt c′wt refl (⊑idL↦ c≤id d≤id)
catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt)
    | V , vV , M—↠V , V⊑M′
    | ⊑drop? {c = c₀} {c′ = d} d⊑c₀
    with cwt
... | ⊢⨟ (⊢? G-⇒) dwt
    with c′wt
... | ⊢↦ c₀wt₁ c₀wt₂
    with proj-?-less-ground G-⇒ V⊑M′ vV vV′ (⊑-⇒ ⊑-★ ⊑-★)
... | W , vW , W⊑M′ , V-?—↠W
    with cast-left-↦-val W⊑M′ vW vV′ dwt (⊢↦ c₀wt₁ c₀wt₂) d⊑c₀
... | V₂ , W-d—↠V₂ , V₂⊑castM′ , vV₂ =
      V₂
      , vV₂
      , (cast M [ ((★ ⇒ ★) `? ⨟ d) ]
           —↠ᶜ⟨ ξ* (cast□[ ((★ ⇒ ★) `? ⨟ d) ]) M—↠V ⟩
         cast V [ ((★ ⇒ ★) `? ⨟ d) ]
           —↠ᶜ⟨ cast-seq-lift vV V-?—↠W ⟩
         cast W [ d ]
           —↠ᶜ⟨ W-d—↠V₂ ⟩
         V₂
         ∎ᶜ)
      , V₂⊑castM′

catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂))
    | V , vV , M—↠V , V⊑M′
    | ⊑drop! {c = c₀} {c′ = d} d⊑c₀
    with cwt
... | ⊢⨟ dwt (⊢! G-⇒)
    with cast-left-↦-val V⊑M′ vV vV′ dwt (⊢↦ c′wt₁ c′wt₂) d⊑c₀
... | V₂ , V-d—↠V₂ , V₂⊑castM′ , vV₂ =
      inj V₂ [ ★ ⇒ ★ ]!
      , (V-! vV₂)
      , (cast M [ d ⨟ ((★ ⇒ ★) !) ]
           —↠ᶜ⟨ ξ* (cast□[ d ⨟ ((★ ⇒ ★) !) ]) M—↠V ⟩
         cast V [ d ⨟ ((★ ⇒ ★) !) ]
           —↠ᶜ⟨ cast-seq-lift vV V-d—↠V₂ ⟩
         cast V₂ [ (★ ⇒ ★) ! ]
           —→ᶜ⟨ β-inj vV₂ ⟩
         inj V₂ [ ★ ⇒ ★ ]!
         ∎ᶜ)
      , ⊑injL V₂⊑castM′ vV₂ G-⇒ (V-cast↦ vV′)

catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂))
    | V , vV , M—↠V , V⊑M′
    | ⊑idL nseq c′wt-id A⊑A′ B⊑A′
    = catchup-cast-idL↦ M—↠V vV V⊑M′ cwt c′wt refl (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
catchup vV′ (⊑castL M⊑M′ cwt c⊑id)
    with catchup vV′ M⊑M′
... | V , vV , M—↠V , V⊑V′
    with cast-left-id-val V⊑V′ vV vV′ cwt c⊑id
... | V₂ , castV—↠V₂ , V₂⊑V′ , vV₂ =
      V₂ , vV₂
      , (cast _ [ _ ]
           —↠ᶜ⟨ ξ* (cast□[ _ ]) M—↠V ⟩
         cast V [ _ ]
           —↠ᶜ⟨ castV—↠V₂ ⟩
         V₂
         ∎ᶜ)
      , V₂⊑V′
catchup (V-cast↦ vM′) (⊑castR M⊑M′ c′wt id⊑c′)
    with catchup vM′ M⊑M′
... | V , vV , M—↠V , V⊑M′ =
    V , vV , M—↠V , (⊑castR V⊑M′ c′wt id⊑c′)
catchup vV′ (⊑inj M⊑M′ vM vM′ g) =
    inj _ [ _ ]! , (V-! vM) , (inj _ [ _ ]! ∎ᶜ) , (⊑inj M⊑M′ vM vM′ g)
catchup vV′ (⊑injL M⊑M′ vM g vM′) =
    inj _ [ _ ]! , (V-! vM) , (inj _ [ _ ]! ∎ᶜ) , (⊑injL M⊑M′ vM g vM′)
catchup () (⊑blameR M⦂A₁ A₁⊑A₂)

--------------------------------------------------------------------------------
cast-left-!-val : ∀ {V V′ A B G}{c}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ G
  → Valueᶜ V
  → Valueᶜ V′
  → Ground G
  → c ⊑ᶜ (G !)
  → ⊢ c ⦂ A ⇨ B
  → ∃[ N ] cast V [ c ] —↠ᶜ N × []⊑[] ⊢ N ⦂ B ⊑ᶜᵀ inj V′ [ G ]! ⦂ ★
cast-left-!-val {V} {V′} {G = G} {c = H !}
  V≤V′ vV vV′ g (⊑! H⊑G) (⊢! gH)
    with ground-upper-unique gH g H⊑G ⊑-refl
... | refl =
  inj V [ G ]!
  , (cast V [ G ! ]
       —→ᶜ⟨ β-inj vV ⟩
     inj V [ G ]!
     ∎ᶜ)
  , ⊑inj V≤V′ vV vV′ g
cast-left-!-val {V} {V′} {G = G} {c = idᶜ A₀}
  V≤V′ vV vV′ g (⊑idL atom-! (⊢! g′) A₀⊑G A₀⊑★) ⊢idᶜ
    with A₀⊑★
... | ⊑-★
    with star-to-inj V≤V′ vV vV′ g
... | V≤injV′ =
  V
  , (cast V [ idᶜ ★ ]
       —→ᶜ⟨ β-id vV ⟩
     V
     ∎ᶜ)
  , V≤injV′
cast-left-!-val {V} {V′} {G = ℕ} {c = (★ ⇒ ★) `? ⨟ d}
  V≤V′ vV vV′ G-ℕ (⊑drop? {c′ = d} d≤!) (⊢⨟ (⊢? G-⇒) d⦂)
    with ⊑ᶜ→⊑ (⊢! G-ℕ) d⦂ d≤!
... | A⊑ℕ , B⊑★
    with A⊑ℕ
... | ()
cast-left-!-val {V} {V′} {G = ★ ⇒ ★} {c = (★ ⇒ ★) `? ⨟ d}
  V≤V′ vV vV′ G-⇒ (⊑drop? {c′ = d} d≤!) (⊢⨟ (⊢? G-⇒) d⦂)
    with star-to-inj V≤V′ vV vV′ G-⇒
... | V≤injV′
    with cast-left-?-val V≤injV′ vV vV′ (⊑? ⊑-refl) (⊢? G-⇒)
... | W , V-?—↠W , W≤V′
    with catchup vV′ W≤V′
... | W₁ , vW₁ , W—↠W₁ , W₁≤V′
    with cast-left-!-val W₁≤V′ vW₁ vV′ G-⇒ d≤! d⦂
... | N , W₁-d—↠N , N≤ =
  N
  , (cast V [ (★ ⇒ ★) `? ⨟ d ]
       —↠ᶜ⟨ cast-seq-lift vV V-?—↠W ⟩
     cast W [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) W—↠W₁ ⟩
     cast W₁ [ d ]
       —↠ᶜ⟨ W₁-d—↠N ⟩
     N
     ∎ᶜ)
  , N≤
cast-left-!-val {V} {V′} {G = G} {c = d ⨟ (★ ⇒ ★) !}
  V≤V′ vV vV′ g (⊑drop! {c′ = d} d≤!) (⊢⨟ d⦂ (⊢! G-⇒))
    with cast-left-!-val V≤V′ vV vV′ g d≤! d⦂
... | N , V-d—↠N , N≤ =
  cast N [ (★ ⇒ ★) ! ]
  , (cast V [ d ⨟ (★ ⇒ ★) ! ]
       —↠ᶜ⟨ cast-seq-lift vV V-d—↠N ⟩
     cast N [ (★ ⇒ ★) ! ]
     ∎ᶜ)
  , ⊑castL N≤ (⊢! G-⇒)
      (⊑idR atom-! (⊢! G-⇒) (⊑ᶜᵀ-type-precision N≤) ⊑-★)


--------------------------------------------------------------------------------
-- Simulation of Beta Reduction
--
-- (V · W) ⊑ (λ N′) · W′
--   —↠ᶜ        —→ᶜ
--    N    ⊑  N′ [ W′ ]
--
-- If V ⊑ λ N′ and W ⊑ W′
-- then V · W —↠ᶜ N and N ⊑ N′ [ W′] for some N.
---
--------------------------------------------------------------------------------
sim-beta : ∀{V W N′ W′}{A B A′ A′₂ B′}
  → []⊑[] ⊢ V ⦂ A ⇒ B ⊑ᶜᵀ ƛ A′₂ ⇒ N′ ⦂ (A′ ⇒ B′)
  → Valueᶜ V
  → []⊑[] ⊢ W ⦂ A ⊑ᶜᵀ W′ ⦂ A′
  → Valueᶜ W
  → Valueᶜ W′
  → Σ[ N ∈ Termᶜ ] (V · W —↠ᶜ N) × ([]⊑[] ⊢ N ⦂ B ⊑ᶜᵀ N′ [ W′ ]ᶜ ⦂ B′)
sim-beta {W = W} (⊑ƛ A⊑A′ N⊑N′) (V-ƛ {N = N}) W⊑W′ vW vW′ =
  N [ W ]ᶜ
  , ((ƛ _ ⇒ N) · W —→ᶜ⟨ β-ƛ vW ⟩ N [ W ]ᶜ ∎ᶜ)
  , []ᶜ-⊑ A⊑A′ N⊑N′ W⊑W′
sim-beta
  {V = cast U [ c₁ ↦ d₁ ]}{W}
  (⊑castL V⊑λN′ (⊢↦ cwt₁ dwt₁) c⊑id)
  (V-cast↦ vU) W⊑W′ vW vW′
    with ⊑ᶜ→⊑ ⊢idᶜ (⊢↦ cwt₁ dwt₁) c⊑id
... | A₁⇒B₁⊑A′⇒B′ , A⇒B⊑A′⇒B′
    with A₁⇒B₁⊑A′⇒B′ | A⇒B⊑A′⇒B′
... | ⊑-⇒ A₁⊑A′ B₁⊑B′ | ⊑-⇒ A⊑A′ B⊑B′
    with c⊑id
... | ⊑idR↦ c₁⊑id d₁⊑id
    with cast-left-id-val W⊑W′ vW vW′ cwt₁ c₁⊑id
... | W₁ , W-c₁—↠W₁ , W₁⊑W′ , vW₁
    with sim-beta V⊑λN′ vU W₁⊑W′ vW₁ vW′
... | N , UW₁—↠N , N⊑N′[W′] =
      cast N [ d₁ ]
      , (cast U [ c₁ ↦ d₁ ] · W
           —→ᶜ⟨ β-↦ vU vW ⟩
         cast (U · cast W [ c₁ ]) [ d₁ ]
           —↠ᶜ⟨ ξ* (cast□[ d₁ ]) (ξ* (U ·□ vU) W-c₁—↠W₁) ⟩
         cast (U · W₁) [ d₁ ]
           —↠ᶜ⟨ ξ* (cast□[ d₁ ]) UW₁—↠N ⟩
         cast N [ d₁ ]
         ∎ᶜ)
      , ⊑castL N⊑N′[W′] dwt₁ d₁⊑id

--------------------------------------------------------------------------------
sim-beta-cast : ∀{V W V′ W′}{A B A′ B′}{c′ d′}
  → []⊑[] ⊢ V ⦂ A ⇒ B ⊑ᶜᵀ cast V′ [ c′ ↦ d′ ] ⦂ (A′ ⇒ B′)
  → Valueᶜ V
  → []⊑[] ⊢ W ⦂ A ⊑ᶜᵀ W′ ⦂ A′
  → Valueᶜ W
  → Valueᶜ W′
  → Σ[ N ∈ Termᶜ ] (V · W —↠ᶜ N)
      × ([]⊑[] ⊢ N ⦂ B ⊑ᶜᵀ cast (V′ · (cast W′ [ c′ ])) [ d′ ] ⦂ B′)
sim-beta-cast
  {W = W}
  (⊑cast {M = V₁} V₁≤V′ c≤c′↦d′ c⦂ (⊢↦ c′⦂ d′⦂))
  (V-cast↦ {c = c} {d} vV₁) W≤W′ vW vW′
    with c≤c′↦d′ | c⦂
... | ⊑↦ c≤c′ d≤d′ | ⊢↦ c⦂₁ d⦂ =
  cast (V₁ · cast W [ c ]) [ d ]
  , (cast V₁ [ c ↦ d ] · W
       —→ᶜ⟨ β-↦ vV₁ vW ⟩
     cast (V₁ · cast W [ c ]) [ d ]
     ∎ᶜ)
  , ⊑cast (⊑· V₁≤V′ (⊑cast W≤W′ c≤c′ c⦂₁ c′⦂)) d≤d′ d⦂ d′⦂
sim-beta-cast
  {V = cast U [ c₁ ↦ d₁ ]}{W}
  (⊑castL V⊑V′cd (⊢↦ cwt₁ dwt₁) c⊑id)
  (V-cast↦ vU) W⊑W′ vW vW′
    with ⊑ᶜ→⊑ ⊢idᶜ (⊢↦ cwt₁ dwt₁) c⊑id
... | A₁⇒B₁⊑A⇒B , A⇒B⊑A′⇒B′
    with A₁⇒B₁⊑A⇒B | A⇒B⊑A′⇒B′
... | ⊑-⇒ A₁⊑A B₁⊑B | ⊑-⇒ A⊑A′ B⊑B′
    with c⊑id
... | ⊑idR↦ c₁⊑id d₁⊑id
    with cast-left-id-val W⊑W′ vW vW′ cwt₁ c₁⊑id
... | W₁ , W-c₁—↠W₁ , W₁⊑W′ , vW₁
    with sim-beta-cast V⊑V′cd vU W₁⊑W′ vW₁ vW′
... | N , UW₁—↠N , N⊑ =
      cast N [ d₁ ]
      , (cast U [ c₁ ↦ d₁ ] · W
           —→ᶜ⟨ β-↦ vU vW ⟩
         cast (U · cast W [ c₁ ]) [ d₁ ]
           —↠ᶜ⟨ ξ* (cast□[ d₁ ]) (ξ* (U ·□ vU) W-c₁—↠W₁) ⟩
         cast (U · W₁) [ d₁ ]
           —↠ᶜ⟨ ξ* (cast□[ d₁ ]) UW₁—↠N ⟩
         cast N [ d₁ ]
         ∎ᶜ)
      , ⊑castL N⊑ dwt₁ d₁⊑id
sim-beta-cast
  {W = W}
  (⊑castR {M = V₁} V₁⊑V′ (⊢↦ c′⦂ d′⦂) id⊑c′↦d′)
  vV W⊑W′ vW vW′
    with id⊑c′↦d′
... | ⊑idL↦ c≤c′ d≤d′ =
  V₁ · W
  , (_ ∎ᶜ)
  , ⊑castR (⊑· V₁⊑V′ (⊑castR W⊑W′ c′⦂ c≤c′)) d′⦂ d≤d′

--------------------------------------------------------------------------------
-- Simulation
--
-- If M ⊑ M′ and M′ —→ᶜ N′
-- then ∃ N, M —↠ᶜ N and N ⊑ N′
--
--------------------------------------------------------------------------------

sim-castL-result : ∀ {M N N′ A A′ B c}
  → ⊢ c ⦂ A ⇨ B
  → c ⊑ᶜ idᶜ A′
  → (M —↠ᶜ N)
  → []⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′
  → ∃[ N₂ ] ((cast M [ c ] —↠ᶜ N₂) × ([]⊑[] ⊢ N₂ ⦂ B ⊑ᶜᵀ N′ ⦂ A′))
sim-castL-result {M = M} {c = c} c⦂ c≤id M→N N⊑N′ =
  cast _ [ c ]
  , (cast M [ c ]
       —↠ᶜ⟨ ξ* (cast□[ c ]) M→N ⟩
     cast _ [ c ]
     ∎ᶜ)
  , ⊑castL N⊑N′ c⦂ c≤id

sim : ∀ {M M′ N′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M′ —→ᶜ N′
  → ∃[ N ] ((M —↠ᶜ N) × ([]⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′))
sim (⊑castL {M = M} {c = c} M⊑M′ c⦂ c≤id) (ξξ {F = F} refl refl M→N)
    with sim M⊑M′ (ξξ {F = F} refl refl M→N)
... | N , M→N₁ , N⊑N′ =
    sim-castL-result c⦂ c≤id M→N₁ N⊑N′
sim (⊑· {L = L} {L′ = L′} {M = M} {M′ = M′} L⊑L′ M⊑M′)
    (ξξ {F = □· .M′} refl refl L′→N′)
    with sim L⊑L′ L′→N′
... | N , L→N , N⊑N′ =
    N · M
    , ξ* (□· M) L→N
    , ⊑· N⊑N′ M⊑M′
sim (⊑· {L = L} {L′ = V′} {M = M} {M′ = M′} L⊑V′ M⊑M′)
    (ξξ {F = .V′ ·□ vV′} refl refl M′→N′)
    with catchup vV′ L⊑V′
... | V , vV , L→V , V⊑V′
    with sim M⊑M′ M′→N′
... | N , M→N , N⊑N′ =
    V · N
    , (L · M
         —↠ᶜ⟨ ξ* (□· M) L→V ⟩
       V · M
         —↠ᶜ⟨ ξ* (V ·□ vV) M→N ⟩
       V · N
       ∎ᶜ)
    , ⊑· V⊑V′ N⊑N′
sim (⊑cast {M = M} {M′ = M′} {c = c} {c′ = c′} M⊑M′ c≤c′ c⦂ c′⦂)
    (ξξ {F = cast□[ .c′ ]} refl refl M′→N′)
    with sim M⊑M′ M′→N′
... | N , M→N , N⊑N′ =
    cast N [ c ]
    , (cast M [ c ]
         —↠ᶜ⟨ ξ* (cast□[ c ]) M→N ⟩
       cast N [ c ]
       ∎ᶜ)
    , ⊑cast N⊑N′ c≤c′ c⦂ c′⦂
sim (⊑castR {M = M} {M′ = M′} M⊑M′ c′⦂ id≤c′)
    (ξξ {F = cast□[ _ ]} refl refl M′→N′)
    with sim M⊑M′ M′→N′
... | N , M→N , N⊑N′ =
    N
    , M→N
    , ⊑castR N⊑N′ c′⦂ id≤c′
sim ⊑$ (ξξ x x₁ x₂) = ⊥-elim (value-irreducible V-$ (ξξ x x₁ x₂))
sim (⊑ƛ A⊑A′ N⊑M) (ξξ x x₁ x₂) = ⊥-elim (value-irreducible V-ƛ (ξξ x x₁ x₂))
sim (⊑inj M⊑M′ vM vM′ g) (ξξ x x₁ x₂) =
    ⊥-elim (value-irreducible (V-! vM′) (ξξ x x₁ x₂))
sim (⊑injL M⊑M′ vM g vM′) (ξξ x x₁ x₂) =
    ⊥-elim (value-irreducible vM′ (ξξ x x₁ x₂))
sim (⊑blameR M⦂A₁ A₁⊑A₂) (ξξ x x₁ x₂) = ⊥-elim (blame-irreducible (ξξ x x₁ x₂))

-- Case β-ƛ

sim (⊑·{A}{A′}{B}{B′}{L}{L′}{M}{M′} L⊑L′ M⊑M′) (β-ƛ vM′)
    with catchup V-ƛ L⊑L′
... | V , vV , L→V , V⊑λN
    with catchup vM′ M⊑M′
... | W , vW , M→W , W⊑M′
    with sim-beta V⊑λN vV W⊑M′ vW vM′
... | N , VW→N , N⊑N′W′ =    
      let LM→N = L · M
                    —↠ᶜ⟨ ξ* (□· M) L→V ⟩
                 V · M
                    —↠ᶜ⟨ ξ* (V ·□ vV) M→W ⟩
                 V · W
                    —↠ᶜ⟨ VW→N ⟩
                 N              
              ∎ᶜ in
      N , LM→N , N⊑N′W′
sim (⊑castL{M = M}{c = c} M⊑M′ x x₁) (β-ƛ{N = N′}{V = V′} v)
    with sim M⊑M′ (β-ƛ v)
... | N , M→N , N⊑N′[V′] =
  sim-castL-result x x₁ M→N N⊑N′[V′]
sim (⊑injL x x₃ x₄ ()) (β-ƛ x₂)

-- Case β-id

sim (⊑cast{M = M}{c = c} M⊑M′ c≤ c⦂ ⊢idᶜ) (β-id vN′) =
  cast M [ c ] , (_ ∎ᶜ) , ⊑castL M⊑M′ c⦂ c≤
sim (⊑castL{M = M}{c = c} M⊑M′ x x₁) (β-id vN′)
    with ⊑ᶜᵀ-right-typed M⊑M′
... | ⊢cast M′⦂ ⊢idᶜ = 
    cast M [ c ] , (_ ∎ᶜ) , ⊑castL (⊑castR-id-inversion M⊑M′) x x₁
sim (⊑castR{M = M} M⊑M′ ⊢idᶜ x₁) (β-id vN′) = M , (M ∎ᶜ) , M⊑M′

-- Case β-seq

sim (⊑cast {M = M} {V′} {c = c} {c′ ⨟ d′} M⊑V′ c≤c′⨟d′ c⦂ (⊢⨟ c′⦂ d′⦂)) (β-seq vV′)
    with catchup vV′ M⊑V′
... | V , vV , M→V , V⊑V′ 
    with ⊑ᶜ→⊑ (⊢⨟ c′⦂ d′⦂) c⦂ c≤c′⨟d′
... | aa , B⊑B′ 
    with cast-left-⨟-val V⊑V′ vV vV′ c≤c′⨟d′ c⦂ c′⦂ d′⦂
... | N₂ , →N₂ , N₂≤ =
    let red = cast M [ c ] —↠ᶜ⟨ ξ* _ M→V ⟩
              cast V [ c ] —↠ᶜ⟨ →N₂ ⟩
              N₂ ∎ᶜ in
    N₂ , red , N₂≤
sim {M′ = cast V′ [ c′ ⨟ d′ ]} (⊑castL{M = M}{c = c} M⊑V′cd c⦂ c≤id) (β-seq vV′)
    with sim M⊑V′cd (β-seq vV′)
... | N , M→N , N≤ =    
    sim-castL-result c⦂ c≤id M→N N≤
sim (⊑castR{M = M} M⊑V′ (⊢⨟ c⦂ d⦂) (⊑idL⨟ id≤c id≤d)) (β-seq vV′) =
    M
    , (_ ∎ᶜ)
    , ⊑castR (⊑castR M⊑V′ c⦂ id≤c) d⦂ id≤d

-- Case β-↦

sim {L · M} (⊑· L⊑L′ M⊑W′) (β-↦ {V = V′}{W′}{c = c′} {d′} vV′ vW′)
    with catchup (V-cast↦ vV′) L⊑L′
... | V , vV , →V , V≤V′
    with catchup vW′  M⊑W′
... | W , vW , →W , W≤W′
    with sim-beta-cast V≤V′ vV W≤W′ vW vW′
... | N , VW→N , N≤ =
    let red = (L · M) —↠ᶜ⟨ ξ* (□· M) →V ⟩
              V · M —↠ᶜ⟨ ξ* (V ·□ vV) →W ⟩
              V · W —↠ᶜ⟨ VW→N ⟩
              N ∎ᶜ in
    N , red , N≤

sim (⊑castL {M = M} {c = c₁} M⊑M′ x x₁) (β-↦ {c = c} {d} vV vW)
    with sim M⊑M′ (β-↦ {c = c} {d} vV vW)
... | N , M→N , N≤ =
    sim-castL-result x x₁ M→N N≤

-- Case β-proj-inj-ok

sim {N′ = V′} (⊑cast {M = M} {c = c} M⊑M′ c≤c′ c⦂ (⊢? gA′)) (β-proj-inj-ok vV′)
    with catchup (V-! vV′) M⊑M′
... | V , vV , M→V , V≤M′
    with cast-left-?-val V≤M′ vV vV′ c≤c′ c⦂
... | N , Vc→N , N≤ =
    let red = cast M [ c ] —↠ᶜ⟨ ξ* (cast□[ c ]) M→V ⟩
              cast V [ c ] —↠ᶜ⟨ Vc→N ⟩
              N ∎ᶜ in
    N , red , N≤
    
sim {N′ = V′} (⊑castL {M = M} {c = c} M⊑M′ c⦂ c≤id) (β-proj-inj-ok vV′)
    with sim M⊑M′ (β-proj-inj-ok vV′)
... | N , M→N , N≤ =
    sim-castL-result c⦂ c≤id M→N N≤
    
sim {N′ = V′}
    (⊑castR {M = M} {M′ = inj V′ [ A′ ]!} M⊑M′ (⊢? gA′) id≤c′)
    (β-proj-inj-ok {G = A′} vV′)
    with id≤c′
... | (⊑idL atom-? (⊢? gA′) A⊑★ A⊑A′)
    with catchup (V-! vV′) M⊑M′
... | V , vV , M→V , V≤M′
    with A⊑★
... | ⊑-★
    with cast-left-?-val V≤M′ vV vV′ (⊑idL atom-? (⊢? gA′) ⊑-★ A⊑A′) ⊢idᶜ
... | .(cast V [ idᶜ ★ ]) , (cast V [ idᶜ ★ ] ∎ᶜ) , N≤ =
    V
    , M→V
    , ⊑castL-id-inversion N≤
... | N , (cast V [ idᶜ ★ ] —→ᶜ⟨ β-id vV ⟩ V→N) , N≤ =
    N
    , (M→V ++ᶜ V→N)
    , N≤
... | _ , (cast V [ idᶜ ★ ] —→ᶜ⟨ ξ (cast□[ idᶜ ★ ]) V→W ⟩ W→N) , _ =
    ⊥-elim (value-irreducible vV V→W)
... | _ , (cast V [ idᶜ ★ ] —→ᶜ⟨ ξ-blame (cast□[ idᶜ ★ ]) ⟩ W→N) , _ =
    ⊥-elim (value-not-blame vV)

-- Case β-proj-inj-bad

sim {M = M} {A = A} {A′ = A′} M⊑M′ (β-proj-inj-bad x x₁) =
  M
  , (M ∎ᶜ)
  , ⊑blameR (⊑ᶜᵀ-left-typed M⊑M′) (⊑ᶜᵀ-type-precision M⊑M′)

-- Case ξξ-blame

sim {M = M} {A = A} {A′ = A′} M⊑M′ (ξξ-blame x) =
  M
  , (M ∎ᶜ)
  , ⊑blameR (⊑ᶜᵀ-left-typed M⊑M′) (⊑ᶜᵀ-type-precision M⊑M′)

-- Case β-inj

sim (⊑cast {M = M} {M′ = V′} {c = c} {c′ = G !} M⊑V′ c≤! c⦂ (⊢! g)) (β-inj vV′)
    with catchup vV′ M⊑V′
... | V , vV , M→V , V≤V′
    with cast-left-!-val V≤V′ vV vV′ g c≤! c⦂
... | N , V-c—↠N , N≤ =
    let red = cast M [ c ]
              —↠ᶜ⟨ ξ* (cast□[ c ]) M→V ⟩
              cast V [ c ]
              —↠ᶜ⟨ V-c—↠N ⟩
              N
              ∎ᶜ in
    N , red , N≤
sim (⊑castL {M = M} {M′ = M′} {c = c} M⊑M′ c⦂ c≤id) (β-inj vV′)
    with sim M⊑M′ (β-inj vV′)
... | N , M→N , N≤ =
    sim-castL-result c⦂ c≤id M→N N≤
sim (⊑castR {M = M} {M′ = V′} M⊑V′ (⊢! g) id≤!) (β-inj vV′)
    with id≤!
... | (⊑idL atom-! (⊢! g) A⊑G A⊑★)
    with catchup vV′ M⊑V′
... | V , vV , M→V , V≤V′
    with A⊑★
... | ⊑-★ = V , M→V , star-to-inj V≤V′ vV vV′ g
sim (⊑injL M⊑M′ vM g ()) (β-inj vV′)

--------------------------------------------------------------------------------
-- Multi-step Simulation
--------------------------------------------------------------------------------

sim* : ∀ {M M′ N′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M′ —↠ᶜ N′
  → ∃[ N ] ((M —↠ᶜ N) × ([]⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′))
sim* {M = M} M≤M′ (M′ ∎ᶜ) = M , (M ∎ᶜ) , M≤M′
sim* {M = M} M≤M′ (M′ —→ᶜ⟨ M′→N₁ ⟩ N₁→N′)
    with sim M≤M′ M′→N₁
... | N₁ , M→N₁ , N₁≤N₁′
    with sim* N₁≤N₁′ N₁→N′
... | N , N₁→N , N≤N′ =
    N
    , (M→N₁ ++ᶜ N₁→N)
    , N≤N′

--------------------------------------------------------------------------------
-- Dynamic Gradual Guarantee (when M terminates)
--------------------------------------------------------------------------------

gg : ∀ {M M′ V A A′}
  → []⊑[] ⊢ M′ ⦂ A′ ⊑ᶜᵀ M ⦂ A
  → M —↠ᶜ V
  → Valueᶜ V
  → ∃[ V′ ] ((Valueᶜ V′) × (M′ —↠ᶜ V′) × ([]⊑[] ⊢ V′ ⦂ A′ ⊑ᶜᵀ V ⦂ A))
gg M⊑M′ M—↠V vV
  with sim* M⊑M′ M—↠V
... | N′ , M′—↠N′ , N′⊑V
  with catchup vV N′⊑V
... | V′ , vV′ , N′—↠V′ , V′⊑V =
  V′ , vV′ , (M′—↠N′ ++ᶜ N′—↠V′) , V′⊑V
