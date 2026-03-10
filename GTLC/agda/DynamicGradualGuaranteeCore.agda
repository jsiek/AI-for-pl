module DynamicGradualGuaranteeCore where

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

--------------------------------------------------------------------------------
-- Precision Inversion Lemmas
--------------------------------------------------------------------------------

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

inj-⊑-nat
  : ∀ {V V′ H}
  → Valueᶜ V′
  → []⊑[] ⊢ inj V [ H ]! ⦂ ★ ⊑ᶜᵀ V′ ⦂ ℕ
  → Ground H × []⊑[] ⊢ V ⦂ H ⊑ᶜᵀ V′ ⦂ ℕ
inj-⊑-nat vV′ (⊑injL V⊑V′ vV g vV′′) = g , V⊑V′
inj-⊑-nat (V-cast↦ vV′) (⊑castR V⊑V′ c⦂ id⊑c′) = ⊥-elim (cast-value-not-ℕ (V-cast↦ vV′) c⦂)
inj-⊑-nat vV′ (⊑blameR M⦂A₁ A₁⊑A₂) = ⊥-elim (value-not-blame vV′)

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
    with inj-⊑-nat vV′ V≤V′
... | g′ , W≤V′
    with ground-upper-unique g′ G-ℕ (⊑ᶜᵀ-type-precision W≤V′) ⊑-ℕ
... | refl = ⊑inj W≤V′ vW vV′ G-ℕ
star-to-inj V≤V′ vV vV′ G-⇒
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl
    with inj-⊑-fun vV′ V≤V′
... | g′ , W≤V′
    with ground-upper-unique g′ G-⇒ (⊑ᶜᵀ-type-precision W≤V′) (⊑-⇒ ⊑-refl ⊑-refl)
... | refl = ⊑inj W≤V′ vW vV′ G-⇒

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
-- If V ⊑ M′ and c ⊑ id
-- then V[c] —↠ᶜ N₂ and N₂ ⊑ M′ for some N₂.
---
--------------------------------------------------------------------------------

cast-left-id : ∀ {V M′}{A A′ B}{c}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → Valueᶜ V
  → ⊢ c ⦂ A ⇨ B
  → c ⊑ᶜ idᶜ A′
  → ∃[ N₂ ] cast V [ c ] —↠ᶜ N₂ × []⊑[] ⊢ N₂ ⦂ B ⊑ᶜᵀ M′ ⦂ A′
cast-left-id {V} {c = c} V≤M′ vV ⊢idᶜ (⊑idᶜ x) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤M′
cast-left-id {V} {c = c} V≤M′ vV ⊢idᶜ (⊑idL atm ⊢idᶜ A≤A′ x₃) =
  V , (cast V [ c ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ) , V≤M′
cast-left-id {V} {c = c} V≤M′ vV c⦂ (⊑idR x c⦂₂ x₂ x₃)
    with coercion-type-unique c⦂ c⦂₂
... | refl , refl = cast V [ c ] , (_ ∎ᶜ) , ⊑castL V≤M′ c⦂ (⊑idR x c⦂ x₂ x₃)
cast-left-id {V} {c = c ↦ d} V≤M′ vV (⊢↦ c⦂ d⦂) (⊑idR↦ c≤id d≤id) =
    cast V [ c ↦ d ] , (_ ∎ᶜ) , ⊑castL V≤M′ (⊢↦ c⦂ d⦂) (⊑idR↦ c≤id d≤id)
cast-left-id {V} {c = c ⨟ d} V≤M′ vV (⊢⨟ c⦂ d⦂) (⊑idR⨟ c≤id d≤id)  =
  cast cast V [ c ] [ d ]
  , (cast V [ c ⨟ d ] —→ᶜ⟨ β-seq vV ⟩ cast (cast V [ c ]) [ d ] ∎ᶜ)
  , ⊑castL (⊑castL V≤M′ c⦂ c≤id) d⦂ d≤id
cast-left-id {V} {c = ((★ ⇒ ★) `?) ⨟ d} V≤M′ vV (⊢⨟ (⊢? x) c⦂₁) (⊑drop? d≤id)
    with ⊑ᶜ→⊑ ⊢idᶜ c⦂₁ d≤id
... | ⊑-⇒ aa aa₁ , bb =
      cast cast V [ (★ ⇒ ★) `? ] [ d ]
      , (cast V [ ((★ ⇒ ★) `?) ⨟ d ] —→ᶜ⟨ β-seq vV ⟩
        (cast (cast V [ ((★ ⇒ ★) `?) ]) [ d ]) ∎ᶜ)
      , ⊑castL (⊑castL V≤M′ (⊢? x) (⊑idR atom-? (⊢? x) ⊑-★ (⊑-⇒ aa aa₁))) c⦂₁ d≤id
cast-left-id {V} {c = c ⨟ ((★ ⇒ ★) !)} V≤M′ vV (⊢⨟ c⦂ (⊢! x)) (⊑drop! c≤id)
    with ⊑ᶜ→⊑ ⊢idᶜ c⦂ c≤id
... | aa , ⊑-⇒ bb bb₁ =
  cast cast V [ c ] [ (★ ⇒ ★) ! ]
  , (cast V [ c ⨟ ((★ ⇒ ★) !) ] —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ c ]) [ ((★ ⇒ ★) !) ] ∎ᶜ)
  , ⊑castL (⊑castL V≤M′ c⦂ c≤id) (⊢! x) (⊑idR atom-! (⊢! x) (⊑-⇒ bb bb₁) ⊑-★)

--------------------------------------------------------------------------------
-- Cast Left Value of id
--
-- If V ⊑ V′ and c ⊑ id
-- then V[c] —↠ᶜ V₂ and V₂ ⊑ V′ for some V₂.
---
--------------------------------------------------------------------------------

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
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl with V≤V′
... | ⊑inj W⊑W′ vW vW′ g″ = ⊥-elim (ground-not-⊑★ G-ℕ B⊑A′)
... | ⊑castR W⊑M′ c′⦂ id⊑c′
    rewrite ℕ-⊑-inv B⊑A′ = ⊥-elim (cast-value-not-ℕ vV′ c′⦂)
... | ⊑injL W⊑V′ vW g″ vV′
    with ground-upper-unique g″ G-ℕ (⊑ᶜᵀ-type-precision W⊑V′) B⊑A′
... | refl =
    let prec : []⊑[] ⊢ inj W [ ℕ ]! ⦂ ★ ⊑ᶜᵀ V′ ⦂ A′
        prec = V≤V′ in
    let red = cast (inj W [ ℕ ]!) [ c ] —→ᶜ⟨ β-proj-inj-ok vW ⟩
              W ∎ᶜ in
    let prec′ : []⊑[] ⊢ W ⦂ ℕ ⊑ᶜᵀ V′ ⦂ A′
        prec′ = W⊑V′ in        
    W , red , prec′ , vW
  
cast-left-id-val {V} {V′} {A′ = A′} {c = c} V≤V′ vV vV′ (⊢? G-⇒) (⊑idR nseq (⊢? g′) A⊑A′ B⊑A′)
    with canonical-★-inj vV (⊑ᶜᵀ-left-typed V≤V′)
... | H , W , vW , refl
    with B⊑A′
... | ⊑-⇒ A₁⊑A₂ B₁⊑B₂
    with inj-⊑-fun vV′ V≤V′
... | g″ , W⊑V′
    with ground-upper-unique g″ G-⇒ (⊑ᶜᵀ-type-precision W⊑V′) (⊑-⇒ A₁⊑A₂ B₁⊑B₂)
... | refl =
    let prec : []⊑[] ⊢ inj W [ ★ ⇒ ★ ]! ⦂ ★ ⊑ᶜᵀ V′ ⦂ (_ ⇒ _)
        prec = V≤V′ in
    let red = cast (inj W [ ★ ⇒ ★ ]!) [ c ] —→ᶜ⟨ β-proj-inj-ok vW ⟩
              W ∎ᶜ in
    let prec′ : []⊑[] ⊢ W ⦂ ★ ⇒ ★ ⊑ᶜᵀ V′ ⦂ (_ ⇒ _)
        prec′ = W⊑V′ in
    W , red , prec′ , vW

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
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ c ]) [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) V-c—↠V₁ ⟩
     cast V₁ [ d ]
       —↠ᶜ⟨ V₁-d—↠V₂ ⟩
     V₂
     ∎ᶜ)
  , V₂⊑V′
  , vV₂
cast-left-id-val {V} {V′} {A′ = A′} {c = (★ ⇒ ★) `? ⨟ c} V≤V′ vV vV′ (⊢⨟ (⊢? G-⇒) c⦂) (⊑drop? c≤id)
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
  with cast-left-id-val W⊑V′ vW vV′ c⦂ c≤id
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
cast-left-id-val {V} {V′} {c = c ⨟ (★ ⇒ ★) !} V≤V′ vV vV′ (⊢⨟ c⦂ (⊢! G-⇒)) (⊑drop! c≤id)
  with cast-left-id-val V≤V′ vV vV′ c⦂ c≤id
... | V₁ , V-c—↠V₁ , V₁⊑V′ , vV₁ =
  inj V₁ [ ★ ⇒ ★ ]!
  , (cast V [ c ⨟ (★ ⇒ ★) ! ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ c ]) [ (★ ⇒ ★) ! ]
       —↠ᶜ⟨ ξ* (cast□[ (★ ⇒ ★) ! ]) V-c—↠V₁ ⟩
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

cast-left-↦-val : ∀ {V V′}{A A′ B B′}{c c₁ c₂}
  → []⊑[] ⊢ V ⦂ A ⊑ᶜᵀ V′ ⦂ A′
  → Valueᶜ V
  → Valueᶜ V′
  → ⊢ c ⦂ A ⇨ B
  → ⊢ (c₁ ↦ c₂) ⦂ A′ ⇨ B′
  → c ⊑ᶜ (c₁ ↦ c₂)
  → ∃[ V₂ ] cast V [ c ] —↠ᶜ V₂ × []⊑[] ⊢ V₂ ⦂ B ⊑ᶜᵀ cast V′ [ c₁ ↦ c₂ ] ⦂ B′ × Valueᶜ V₂
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂) (⊑↦ c₁⊑c′₁ d₁⊑d′₁) =
  cast V [ _ ] , (cast V [ _ ] ∎ᶜ)
  , ⊑cast V⊑V′ (⊑↦ c₁⊑c′₁ d₁⊑d′₁) cwt c′wt
  , V-cast↦ vV
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt (⊑idL↦★ c≤id d≤id)
  with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
  V , (cast V [ _ ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ)
  , ⊑castR V⊑V′ c′wt (⊑idL↦★ c≤id d≤id)
  , vV
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt (⊑idL↦ c≤id d≤id)
  with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
  V , (cast V [ _ ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ)
  , ⊑castR V⊑V′ c′wt (⊑idL↦ c≤id d≤id)
  , vV
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ cwt c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
  with coercion-type-unique cwt ⊢idᶜ
... | refl , refl =
  V , (cast V [ _ ] —→ᶜ⟨ β-id vV ⟩ V ∎ᶜ)
  , ⊑castR V⊑V′ c′wt (⊑idL nseq c′wt-id A⊑A′ B⊑A′)
  , vV
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ (⊢⨟ (⊢? G-⇒) dwt) c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑drop? {c = c₀} {c′ = d} d⊑c₀)
  with canonical-★-inj vV (⊑ᶜᵀ-left-typed V⊑V′)
... | H , W , vW , refl
  with inj-⊑-fun vV′ V⊑V′
... | g , W⊑V′
  with ground-upper-unique g G-⇒ (⊑ᶜᵀ-type-precision W⊑V′) (⊑-⇒ ⊑-★ ⊑-★)
... | refl
  with cast-left-↦-val W⊑V′ vW vV′ dwt c′wt d⊑c₀
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
cast-left-↦-val {V} {V′} V⊑V′ vV vV′ (⊢⨟ dwt (⊢! G-⇒)) c′wt@(⊢↦ c′wt₁ c′wt₂)
  (⊑drop! {c = c₀} {c′ = d} d⊑c₀)
  with cast-left-↦-val V⊑V′ vV vV′ dwt c′wt d⊑c₀
... | V₁ , V-d—↠V₁ , V₁⊑castV′ , vV₁ =
  inj V₁ [ ★ ⇒ ★ ]!
  , (cast V [ _ ]
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ d ]) [ (★ ⇒ ★) ! ]
       —↠ᶜ⟨ ξ* (cast□[ (★ ⇒ ★) ! ]) V-d—↠V₁ ⟩
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
     let red = cast V [ ((★ ⇒ ★) `?) ⨟ d ] —→ᶜ⟨ β-seq vV ⟩
               cast (cast V [ (★ ⇒ ★) `? ]) [ d ] —↠ᶜ⟨ ξ* _ →V₂ ⟩
               cast V₂ [ d ] —↠ᶜ⟨ →N₂ ⟩
               N₂ ∎ᶜ in
     N₂ , red , N₂≤
cast-left-⨟-val {V} V≤V′ vV vV′ (⊑drop!{c′ ⨟ d′}{d} d≤c′⨟d′) (⊢⨟ d⦂ (⊢! x)) c′⦂ d′⦂ 
    with ⊑ᶜ→⊑ (⊢⨟ c′⦂ d′⦂) d⦂ d≤c′⨟d′
... | aa , ⊑-⇒ bb bb₁
    with cast-left-⨟-val V≤V′ vV vV′ d≤c′⨟d′ d⦂ c′⦂ d′⦂
... | N₂ , →N₂ , N₂≤ =
    let red = cast V [ d ⨟ (★ ⇒ ★) ! ] —→ᶜ⟨ β-seq vV ⟩
              cast (cast V [ d ]) [ (★ ⇒ ★) ! ] —↠ᶜ⟨ ξ* _ →N₂ ⟩ 
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
         —→ᶜ⟨ β-seq vV ⟩
       cast (cast V [ d ]) [ (★ ⇒ ★) ! ]
         —↠ᶜ⟨ ξ* (cast□[ (★ ⇒ ★) ! ]) V-d—↠N ⟩
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
    with cast-left-↦-val W⊑M′ vW vV′ dwt (⊢↦ c₀wt₁ c₀wt₂) d⊑c₀
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
    with cast-left-↦-val V⊑M′ vV vV′ dwt (⊢↦ c′wt₁ c′wt₂) d⊑c₀
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
           —→ᶜ⟨ β-inj vV₂ ⟩
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
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ (★ ⇒ ★) `? ]) [ d ]
       —↠ᶜ⟨ ξ* (cast□[ d ]) V-?—↠W ⟩
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
       —→ᶜ⟨ β-seq vV ⟩
     cast (cast V [ d ]) [ (★ ⇒ ★) ! ]
       —↠ᶜ⟨ ξ* (cast□[ (★ ⇒ ★) ! ]) V-d—↠N ⟩
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

sim : ∀ {M M′ N′ A A′}
  → []⊑[] ⊢ M ⦂ A ⊑ᶜᵀ M′ ⦂ A′
  → M′ —→ᶜ N′
  → ∃[ N ] ((M —↠ᶜ N) × ([]⊑[] ⊢ N ⦂ A ⊑ᶜᵀ N′ ⦂ A′))
sim (⊑castL {M = M} {c = c} M⊑M′ c⦂ c≤id) (ξξ {F = F} refl refl M→N)
    with sim M⊑M′ (ξξ {F = F} refl refl M→N)
... | N , M→N₁ , N⊑N′ =
    cast N [ c ]
    , (cast M [ c ]
         —↠ᶜ⟨ ξ* (cast□[ c ]) M→N₁ ⟩
       cast N [ c ]
       ∎ᶜ)
    , ⊑castL N⊑N′ c⦂ c≤id
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
  cast N [ c ]
  , (cast M [ c ]
        —↠ᶜ⟨ ξ* cast□[ c ] M→N ⟩
     cast N [ c ] ∎ᶜ)
  , ⊑castL N⊑N′[V′] x x₁
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
    cast N [ c ]
    , ξ* _ M→N
    , ⊑castL N≤ c⦂ c≤id
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
    cast N [ c₁ ]
    , (cast M [ c₁ ]
         —↠ᶜ⟨ ξ* (cast□[ c₁ ]) M→N ⟩
       cast N [ c₁ ] ∎ᶜ)
    , ⊑castL N≤ x x₁

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
    cast N [ c ]
    , (cast M [ c ]
         —↠ᶜ⟨ ξ* (cast□[ c ]) M→N ⟩
       cast N [ c ] ∎ᶜ)
    , ⊑castL N≤ c⦂ c≤id
    
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
    cast N [ c ]
    , (cast M [ c ]
         —↠ᶜ⟨ ξ* (cast□[ c ]) M→N ⟩
       cast N [ c ] ∎ᶜ)
    , ⊑castL N≤ c⦂ c≤id
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
