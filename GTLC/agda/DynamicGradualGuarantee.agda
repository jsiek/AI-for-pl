module DynamicGradualGuarantee where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Contexts
open import CastCalculus
open import Coercions

[]⊑[] : [] ⊑ᵉ []
[]⊑[] x A A′ ()

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

ℕ-⊑-inv : ∀ {A} → ℕ ⊑ A → A ≡ ℕ
ℕ-⊑-inv ⊑-ℕ = refl

inj-⊑-fun
  : ∀ {V V′ H A B}
  → Valueᶜ V′
  → []⊑[] ⊢ inj V [ H ]! ⦂ ★ ⊑ᶜᵀ V′ ⦂ (A ⇒ B)
  → Ground H × []⊑[] ⊢ V ⦂ H ⊑ᶜᵀ V′ ⦂ (A ⇒ B)
inj-⊑-fun vV′ (⊑injL V⊑V′ vV g vV′′) = g , V⊑V′
inj-⊑-fun (V-cast↦ vV′) (⊑castR V⊑V′ c⦂ id⊑c)
  with c⦂
... | ⊢↦ c₁⦂ c₂⦂
  with inj-⊑-fun vV′ V⊑V′
... | g , V⊑M′
  with g
... | G-⇒ =
  g , ⊑castR V⊑M′ (⊢↦ c₁⦂ c₂⦂)
      (⊑idL↦ (⊑id★ c₁⦂) (⊑id★ c₂⦂))
... | G-ℕ
  with ⊑ᶜᵀ-type-precision V⊑M′
... | ()
inj-⊑-fun vV′ (⊑blameR M⦂A₁ A₁⊑A₂) = ⊥-elim (value-not-blame vV′)

cast-value-not-ℕ : ∀ {M c A} → Valueᶜ (cast M [ c ]) → ⊢ c ⦂ A ⇨ ℕ → ⊥
cast-value-not-ℕ (V-cast↦ vM) ()

postulate
  []ᶜ-⊑
    : ∀ {N N′ V V′ A A′ B B′}
    → (A⊑A′ : A ⊑ A′)
    → (extend-⊑ᵉ A⊑A′ []⊑[]) ⊢ N ⦂ B ⊑ᶜᵀ N′ ⦂ B′
    → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
    → []⊑[] ⊢ N [ V ]ᶜ ⦂ B ⊑ᶜᵀ N′ [ V′ ]ᶜ ⦂ B′

--------------------------------------------------------------------------------
-- Cast Left of id
--
-- If V ⊑ V′ and c ⊑ id
-- then V[c] —↠ᶜ V₂ and V₂ ⊑ V′ for some V₂.
---
--------------------------------------------------------------------------------

cast-left : ∀ {V V′}{A A′ B}{c}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → Valueᶜ V
  → Valueᶜ V′
  → ⊢ c ⦂ A ⇨ B
  → c ⊑ᶜ idᶜ A′
  → ∃[ V₂ ] cast V [ c ] —↠ᶜ V₂ × []⊑[] ⊢ V₂ ⦂ B ⊑ᶜᵀ V′ ⦂ A′ × Valueᶜ V₂
cast-left {V} {c = c} V≤V′ vV vV′ ⊢idᶜ (⊑idᶜ A⊑A′) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤V′ , vV
cast-left {V} {c = c} V≤V′ vV vV′ ⊢idᶜ (⊑idL nseq c⦂ A⊑B A⊑C) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤V′ , vV
cast-left {V} {c = c} V≤V′ vV vV′ ⊢idᶜ (⊑idR nseq ⊢idᶜ A⊑A′ B⊑A′) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤V′ , vV
cast-left {V} {V′} {c = c} V≤V′ vV vV′ (⊢! g) (⊑idR nseq (⊢! g′) A⊑A′ B⊑A′) =
  inj V [ _ ]! , (cast V [ c ] —→ᶜ⟨ β-inj ⟩ inj V [ _ ]! ∎ᶜ)
  , ⊑injL V≤V′ vV g vV′
  , V-! vV
cast-left {V} {V′} {A′ = A′} {c = c} V≤V′ vV vV′ (⊢? G-ℕ) (⊑idR nseq (⊢? g′) A⊑A′ B⊑A′)
  with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl with V≤V′
... | ⊑inj W⊑W′ vW vW′ g″ = ⊥-elim (ground-not-⊑★ G-ℕ B⊑A′)
... | ⊑castR W⊑M′ c′⦂ id⊑c′
  rewrite ℕ-⊑-inv B⊑A′ = ⊥-elim (cast-value-not-ℕ vV′ c′⦂)
... | ⊑injL W⊑V′ vW g″ vV′
  with ground-upper-unique g″ G-ℕ (⊑ᶜᵀ-type-precision W⊑V′) B⊑A′
... | refl =
  W , (cast (inj W [ _ ]!) [ c ] —→ᶜ⟨ β-proj-inj-ok vW ⟩ W ∎ᶜ) , W⊑V′ , vW
cast-left {V} {V′} {A′ = A′} {c = c} V≤V′ vV vV′ (⊢? G-⇒) (⊑idR nseq (⊢? g′) A⊑A′ B⊑A′)
  with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl
  with B⊑A′
... | ⊑-⇒ A₁⊑A₂ B₁⊑B₂
  with inj-⊑-fun vV′ V≤V′
... | g″ , W⊑V′
  with ground-upper-unique g″ G-⇒ (⊑ᶜᵀ-type-precision W⊑V′) (⊑-⇒ A₁⊑A₂ B₁⊑B₂)
... | refl =
  W , (cast (inj W [ _ ]!) [ c ] —→ᶜ⟨ β-proj-inj-ok vW ⟩ W ∎ᶜ) , W⊑V′ , vW
cast-left {V} {V′} {c = c} V≤V′ vV vV′ (⊢↦ cwt₁ dwt₁) (⊑idR↦ c≤id d≤id) =
  cast V [ c ] , (cast V [ c ] ∎ᶜ)
  , ⊑castL V≤V′ (⊢↦ cwt₁ dwt₁) (⊑idR↦ c≤id d≤id)
  , V-cast↦ vV
cast-left {V} {V′} {c = c ⨟ d} V≤V′ vV vV′ (⊢⨟ c⦂ d⦂) (⊑idR⨟ c≤id d≤id)
  with cast-left V≤V′ vV vV′ c⦂ c≤id
... | V₁ , V-c—↠V₁ , V₁⊑V′ , vV₁
  with cast-left V₁⊑V′ vV₁ vV′ d⦂ d≤id
... | V₂ , V₁-d—↠V₂ , V₂⊑V′ , vV₂ =
  V₂
  , (cast V [ c ⨟ d ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ c ]) [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) V-c—↠V₁ ⟩
     cast V₁ [ d ]
       —↠ᶜ⟨ V₁-d—↠V₂ ⟩
     V₂
     ∎ᶜ)
  , V₂⊑V′
  , vV₂
cast-left {V} {V′} {A′ = A′} {c = (★ ⇒ ★) `? ⨟ c} V≤V′ vV vV′ (⊢⨟ (⊢? G-⇒) c⦂) (⊑drop? c≤id)
  with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl
  with ⊑ᶜ→⊑ ⊢idᶜ c⦂ c≤id
... | A⊑A′ , _
  with A⊑A′
... | ⊑-⇒ A₁⊑A₂ B₁⊑B₂
  with inj-⊑-fun vV′ V≤V′
... | g″ , W⊑V′
  with ground-upper-unique g″ G-⇒ (⊑ᶜᵀ-type-precision W⊑V′) (⊑-⇒ A₁⊑A₂ B₁⊑B₂)
... | refl
  with cast-left W⊑V′ vW vV′ c⦂ c≤id
... | V₂ , W-c—↠V₂ , V₂⊑V′ , vV₂ =
  V₂
  , (cast V [ (★ ⇒ ★) `? ⨟ c ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ (★ ⇒ ★) `? ]) [ c ]
       —↠ᶜ⟨ ξ* (cast□[ c ]) (cast (inj W [ ★ ⇒ ★ ]!) [ (★ ⇒ ★) `? ] —→ᶜ⟨ β-proj-inj-ok vW ⟩ W ∎ᶜ) ⟩
     cast W [ c ]
       —↠ᶜ⟨ W-c—↠V₂ ⟩
     V₂
     ∎ᶜ)
  , V₂⊑V′
  , vV₂
cast-left {V} {V′} {c = c ⨟ (★ ⇒ ★) !} V≤V′ vV vV′ (⊢⨟ c⦂ (⊢! G-⇒)) (⊑drop! c≤id)
  with cast-left V≤V′ vV vV′ c⦂ c≤id
... | V₁ , V-c—↠V₁ , V₁⊑V′ , vV₁ =
  inj V₁ [ ★ ⇒ ★ ]!
  , (cast V [ c ⨟ (★ ⇒ ★) ! ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ c ]) [ (★ ⇒ ★) ! ]
       —↠ᶜ⟨ ξ* (cast□[ (★ ⇒ ★) ! ]) V-c—↠V₁ ⟩
     cast V₁ [ (★ ⇒ ★) ! ]
       —→ᶜ⟨ β-inj ⟩
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

cast-left-↦ : ∀ {V V′}{A A′ B B′}{c c₁ c₂}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → Valueᶜ V
  → Valueᶜ V′
  → ⊢ c ⦂ A ⇨ B
  → ⊢ (c₁ ↦ c₂) ⦂ A′ ⇨ B′
  → c ⊑ᶜ (c₁ ↦ c₂)
  → ∃[ V₂ ] cast V [ c ] —↠ᶜ V₂ × []⊑[] ⊢ V₂ ⦂ B ⊑ᶜᵀ cast V′ [ c₁ ↦ c₂ ] ⦂ B′ × Valueᶜ V₂
cast-left-↦ {V} {V′} V⊑V′ vV vV′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂) (⊑↦ c₁⊑c′₁ d₁⊑d′₁) =
  cast V [ _ ] , (cast V [ _ ] ∎ᶜ)
  , ⊑cast V⊑V′ (⊑↦ c₁⊑c′₁ d₁⊑d′₁) cwt c′wt
  , V-cast↦ vV
cast-left-↦ {V} {V′} V⊑V′ vV vV′ cwt c′wt (⊑idL↦★ c≤id d≤id)
  with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
  V , (cast V [ _ ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ)
  , ⊑castR V⊑V′ c′wt (⊑idL↦★ c≤id d≤id)
  , vV
cast-left-↦ {V} {V′} V⊑V′ vV vV′ cwt c′wt (⊑idL↦ c≤id d≤id)
  with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
  V , (cast V [ _ ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ)
  , ⊑castR V⊑V′ c′wt (⊑idL↦ c≤id d≤id)
  , vV
cast-left-↦ {V} {V′} V⊑V′ vV vV′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
  with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
  V , (cast V [ _ ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ)
  , ⊑castR V⊑V′ c′wt (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
  , vV
cast-left-↦ {V} {V′} V⊑V′ vV vV′ (⊢⨟ (⊢? G-⇒) dwt) c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑drop? {c = c₀} {c′ = d} d⊑c₀)
  with canonical-★-inj vV (⊑ᶜᵀ-left-typed V⊑V′)
... | H , W , vW , refl
  with inj-⊑-fun vV′ V⊑V′
... | g , W⊑V′
  with ground-upper-unique g G-⇒ (⊑ᶜᵀ-type-precision W⊑V′) (⊑-⇒ ⊑-★ ⊑-★)
... | refl
  with cast-left-↦ W⊑V′ vW vV′ dwt c′wt d⊑c₀
... | V₂ , W-d—↠V₂ , V₂⊑castV′ , vV₂ =
  V₂
  , (cast V [ _ ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ (★ ⇒ ★) `? ]) [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) (cast (inj W [ ★ ⇒ ★ ]!) [ (★ ⇒ ★) `? ] —→ᶜ⟨ β-proj-inj-ok vW ⟩ W ∎ᶜ) ⟩
     cast W [ d ]
       —↠ᶜ⟨ W-d—↠V₂ ⟩
     V₂
     ∎ᶜ)
  , V₂⊑castV′
  , vV₂
cast-left-↦ {V} {V′} V⊑V′ vV vV′ (⊢⨟ dwt (⊢! G-⇒)) c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑drop! {c = c₀} {c′ = d} d⊑c₀)
  with cast-left-↦ V⊑V′ vV vV′ dwt c′wt d⊑c₀
... | V₁ , V-d—↠V₁ , V₁⊑castV′ , vV₁ =
  inj V₁ [ ★ ⇒ ★ ]!
  , (cast V [ _ ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ d ]) [ (★ ⇒ ★) ! ]
       —↠ᶜ⟨ ξ* (cast□[ (★ ⇒ ★) ! ]) V-d—↠V₁ ⟩
     cast V₁ [ (★ ⇒ ★) ! ]
       —→ᶜ⟨ β-inj ⟩
     inj V₁ [ ★ ⇒ ★ ]!
     ∎ᶜ)
  , ⊑injL V₁⊑castV′ vV₁ G-⇒ (V-cast↦ vV′)
  , V-! vV₁

--------------------------------------------------------------------------------
-- Catchup
--
-- If N ⊑ V′
-- then N —↠ᶜ V and V ⊑ V′ for some V.
---
--------------------------------------------------------------------------------
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
    with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
      V , vV
      , (cast M [ c ]
           —↠ᶜ⟨ ξ* (cast□[ c ]) M—↠V ⟩
         cast V [ c ]
           —→ᶜ⟨ β-id vV ⟩
         V
         ∎ᶜ)
      , ⊑castR V⊑M′ c′wt (⊑idL↦★ c≤id d≤id)
catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt)
    | V , vV , M—↠V , V⊑M′
    | ⊑idL↦ c≤id d≤id
    with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
      V , vV
      , (cast M [ c ]
           —↠ᶜ⟨ ξ* (cast□[ c ]) M—↠V ⟩
         cast V [ c ]
           —→ᶜ⟨ β-id vV ⟩
         V
         ∎ᶜ)
      , ⊑castR V⊑M′ c′wt (⊑idL↦ c≤id d≤id)
catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt)
    | V , vV , M—↠V , V⊑M′
    | ⊑drop? {c = c₀} {c′ = d} d⊑c₀
    with cwt
... | ⊢⨟ (⊢? G-⇒) dwt
    with c′wt
... | ⊢↦ c₀wt₁ c₀wt₂
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V⊑M′)
... | H , W , vW , refl
    with inj-⊑-fun vV′ V⊑M′
... | g , W⊑M′
    with ground-upper-unique g G-⇒ (⊑ᶜᵀ-type-precision W⊑M′) (⊑-⇒ ⊑-★ ⊑-★)
... | refl
    with cast-left-↦ W⊑M′ vW vV′ dwt (⊢↦ c₀wt₁ c₀wt₂) d⊑c₀
... | V₂ , W-d—↠V₂ , V₂⊑castM′ , vV₂ =
      V₂
      , vV₂
      , (cast M [ ((★ ⇒ ★) `? ⨟ d) ]
           —↠ᶜ⟨ ξ* (cast□[ ((★ ⇒ ★) `? ⨟ d) ]) M—↠V ⟩
         cast V [ ((★ ⇒ ★) `? ⨟ d) ]
           —→ᶜ⟨ β-seq vV ⟩
         cast (cast V [ (★ ⇒ ★) `? ]) [ d ]
           —↠ᶜ⟨ ξ* (cast□[ d ]) (cast (inj W [ ★ ⇒ ★ ]!) [ (★ ⇒ ★) `? ] —→ᶜ⟨ β-proj-inj-ok vW ⟩ W ∎ᶜ) ⟩
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
    with cast-left-↦ V⊑M′ vV vV′ dwt (⊢↦ c′wt₁ c′wt₂) d⊑c₀
... | V₂ , V-d—↠V₂ , V₂⊑castM′ , vV₂ =
      inj V₂ [ ★ ⇒ ★ ]!
      , (V-! vV₂)
      , (cast M [ d ⨟ ((★ ⇒ ★) !) ]
           —↠ᶜ⟨ ξ* (cast□[ d ⨟ ((★ ⇒ ★) !) ]) M—↠V ⟩
         cast V [ d ⨟ ((★ ⇒ ★) !) ]
           —→ᶜ⟨ β-seq vV ⟩
         cast (cast V [ d ]) [ (★ ⇒ ★) ! ]
           —↠ᶜ⟨ ξ* (cast□[ (★ ⇒ ★) ! ]) V-d—↠V₂ ⟩
         cast V₂ [ (★ ⇒ ★) ! ]
           —→ᶜ⟨ β-inj ⟩
         inj V₂ [ ★ ⇒ ★ ]!
         ∎ᶜ)
      , ⊑injL V₂⊑castM′ vV₂ G-⇒ (V-cast↦ vV′)

catchup (V-cast↦ vV′) (⊑cast {M = M} {c = c} {c′ = c′} M⊑M′ c⊑c′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂))
    | V , vV , M—↠V , V⊑M′
    | ⊑idL nseq c′wt-id A⊑A′ B⊑A′
    with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
      V , vV
      , (cast M [ c ]
           —↠ᶜ⟨ ξ* (cast□[ c ]) M—↠V ⟩
         cast V [ c ]
           —→ᶜ⟨ β-id vV ⟩
         V
         ∎ᶜ)
      , ⊑castR V⊑M′ c′wt (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
catchup vV′ (⊑castL M⊑M′ cwt c⊑id)
    with catchup vV′ M⊑M′
... | V , vV , M—↠V , V⊑V′
    with cast-left V⊑V′ vV vV′ cwt c⊑id
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

⊑castR-id-inversion : ∀{A A′}{M M′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ cast M′ [ idᶜ A′ ] ⦂ A′
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
⊑castR-id-inversion (⊑cast M⊑M′ c≤ c⦂ ⊢idᶜ) = ⊑castL M⊑M′ c⦂ c≤
⊑castR-id-inversion (⊑castL M⊑M′ c⦂ c≤id) = ⊑castL (⊑castR-id-inversion M⊑M′) c⦂ c≤id
⊑castR-id-inversion (⊑castR M⊑M′ ⊢idᶜ id⊑c′) = M⊑M′

--------------------------------------------------------------------------------

cast-⊑⨟ : ∀{V V′}{A A′ B B′ C′}{d c′ d′}
   → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
   → Valueᶜ V
   → Valueᶜ V′
   → d ⊑ᶜ c′ ⨟ d′
   → ⊢ d ⦂ A ⇨ B
   → ⊢ c′ ⦂ A′ ⇨ B′
   → ⊢ d′ ⦂ B′ ⇨ C′
   → ∃[ N₂ ] cast V [ d ] —↠ᶜ N₂ × []⊑[] ⊢ N₂ ⦂ B ⊑ᶜᵀ cast cast V′ [ c′ ] [ d′ ] ⦂ C′
cast-⊑⨟{V} V≤V′ vV vV′ (⊑idL⨟ d≤c′⨟d′ d≤c′⨟d′₁) ⊢idᶜ c′⦂ d′⦂ =
  cast V [ idᶜ _ ] , (_ ∎ᶜ) , ⊑castR (⊑cast V≤V′ d≤c′⨟d′ ⊢idᶜ c′⦂) d′⦂ d≤c′⨟d′₁
cast-⊑⨟ {V} {V′} {cd} {c′} {d′} V≤V′ vV vV′ (⊑⨟ {c′ = c} {d′ = d} d≤c′⨟d′ d≤c′⨟d′₁) (⊢⨟ d⦂ d⦂₁) c′⦂ d′⦂ =
  cast cast V [ c ] [ d ]
  , (cast V [ c ⨟ d ] —→ᶜ⟨ β-seq vV ⟩ cast (cast V [ c ]) [ d ] ∎ᶜ )
  , ⊑cast (⊑cast V≤V′ d≤c′⨟d′ d⦂ c′⦂) d≤c′⨟d′₁ d⦂₁ d′⦂
cast-⊑⨟ {V} V≤V′ vV vV′ (⊑drop? {c′ = d} d≤c′⨟d′) (⊢⨟ (⊢? x) d⦂₁) c′⦂ d′⦂
    with ⊑ᶜ→⊑ (⊢⨟ c′⦂ d′⦂) d⦂₁ d≤c′⨟d′
... | aa , bb
    with cast-left V≤V′ vV vV′ (⊢? x) (⊑idR atom-? (⊢? x) ⊑-★ aa)
... | V₂ , →V₂ , V₂≤ , vV₂
    with cast-⊑⨟ V₂≤ vV₂ vV′ d≤c′⨟d′ d⦂₁ c′⦂ d′⦂
... | N₂ , →N₂ , N₂≤ =
     let red = cast V [ ((★ ⇒ ★) `?) ⨟ d ] —→ᶜ⟨ β-seq vV ⟩
               cast (cast V [ (★ ⇒ ★) `? ]) [ d ] —↠ᶜ⟨ ξ* _ →V₂ ⟩
               cast V₂ [ d ] —↠ᶜ⟨ →N₂ ⟩
               N₂ ∎ᶜ in
     N₂ , red , N₂≤
cast-⊑⨟ V≤V′ vV vV′ (⊑drop! d≤c′⨟d′) (⊢⨟ d⦂ d⦂₁) c′⦂ d′⦂ = {!!}

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
    with cast-left W⊑W′ vW vW′ cwt₁ c₁⊑id
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

sim : ∀ {M M′ N′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M′ —→ᶜ N′
  → ∃[ N ] ((M —↠ᶜ N) × ([]⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′))
sim M⊑M′ (ξξ {F = F} refl refl M→N) = {!!}
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
  cast N [ c ]
  , (cast M [ c ]
        —↠ᶜ⟨ ξ* cast□[ c ] M→N ⟩
     cast N [ c ] ∎ᶜ)
  , ⊑castL N⊑N′[V′] x x₁
sim (⊑injL x x₃ x₄ ()) (β-ƛ x₂)
sim (⊑cast{M = M}{c = c} M⊑M′ c≤ c⦂ ⊢idᶜ) (β-id vN′) =
  cast M [ c ] , (_ ∎ᶜ) , ⊑castL M⊑M′ c⦂ c≤
sim (⊑castL{M = M}{c = c} M⊑M′ x x₁) (β-id vN′)
    with ⊑ᶜᵀ-right-typed M⊑M′
... | ⊢cast M′⦂ ⊢idᶜ = 
    cast M [ c ] , (_ ∎ᶜ) , ⊑castL (⊑castR-id-inversion M⊑M′) x x₁
sim (⊑castR{M = M} M⊑M′ ⊢idᶜ x₁) (β-id vN′) = M , (M ∎ᶜ) , M⊑M′
-- Case
--sim M′⊑M (β-seq vV) = {!!}
sim (⊑cast {M = M} {V′} {c = c} {c′ ⨟ d′} M⊑V′ c≤c′⨟d′ c⦂ (⊢⨟ c′⦂ d′⦂)) (β-seq vV′)
    with catchup vV′ M⊑V′
... | V , vV , M→V , V⊑V′ 
    with ⊑ᶜ→⊑ (⊢⨟ c′⦂ d′⦂) c⦂ c≤c′⨟d′
... | aa , B⊑B′ 
    with cast-⊑⨟ V⊑V′ vV vV′ c≤c′⨟d′ c⦂ c′⦂ d′⦂
... | N₂ , →N₂ , N₂≤ =
    let red = cast M [ c ] —↠ᶜ⟨ ξ* _ M→V ⟩
              cast V [ c ] —↠ᶜ⟨ →N₂ ⟩
              N₂ ∎ᶜ in
    N₂ , red , N₂≤
sim {M′ = cast V′ [ c′ ⨟ d′ ]} (⊑castL{M = M} M⊑V′cd c⦂ c≤id) (β-seq vV′) =

  {!!}
sim (⊑castR M⊑M′ x x₁) (β-seq vV) = {!!}
sim M⊑M′ (β-↦ x x₁) = {!!}
sim M⊑M′ (β-proj-inj-ok x) = {!!}
sim M⊑M′ (β-proj-inj-bad x x₁) = {!!}
sim M⊑M′ (ξξ-blame x) = {!!}
sim M⊑M′ β-inj = {!!}

postulate
  sim-back
    : ∀ {M M′ N A A′}
    → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → M —→ᶜ N
    → ∃[ N′ ] ((M′ —↠ᶜ N′) × ([]⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′))

  sim*
    : ∀ {M M′ N′ A A′}
    → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → M′ —↠ᶜ N′
    → ∃[ N ] ((M —↠ᶜ N) × ([]⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′))

  sim-back*
    : ∀ {M M′ N A A′}
    → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → M —↠ᶜ N
    → ∃[ N′ ] ∃[ N₂ ] ∃[ B ] ∃[ B′ ] ((M′ —↠ᶜ N′) × (N —↠ᶜ N₂)
          × ([]⊑[] ⊢ N₂ ⦂ B ⊑ᶜᵀ N′ ⦂ B′))

  sim-back-converges
    : ∀ {M M′ A A′}
    → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
    → Convergesᶜ M
    → Convergesᶜ M′


gg
  : ∀ {M M′ V A A′}
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

gg-diverge-cp
  : ∀ {M M′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → ¬ Convergesᶜ M′
  → ¬ Convergesᶜ M
gg-diverge-cp M⊑M′ ¬M′⇓ M⇓ = ¬M′⇓ (sim-back-converges M⊑M′ M⇓)

gg-diverge
  : ∀ {M M′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → Divergesᶜ M′
  → Divergesᶜ M
gg-diverge M⊑M′ M′⇑ = gg-diverge-cp M⊑M′ M′⇑
