module Reduction where

-- File Charter:
--   * Value, one-step reduction, and multi-step closure for PolyNuBar.
--   * Follows the active Scheme `reduce.ss` rules declaratively.
--   * Re-exports `Terms` for examples and downstream files.

open import Data.Bool using (true; false)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Terms public

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : Term → Set where
  v-const : ∀ {c} → Value ($ c)
  v-ƛ     : ∀ {A M} → Value (ƛ[ A ] M)
  v-Λ     : ∀ {p V A} → Value V → Value (Λ[ p ] V :: A)
  v-dyn   : ∀ {V G} → Value V → Ground G → Value (V ⦂ G ⇒[ - ] ★)
  v-bar   : ∀ {V A X} → Value V → Value (V ⦂ A ⇒⟨ unbind X ⟩ (` zero))
  v-pair  : ∀ {V W} → Value V → Value W → Value (pair V W)

------------------------------------------------------------------------
-- Auxiliary negative consistency facts used by conflict rules
------------------------------------------------------------------------

infix 4 _∦_
data _∦_ : Ty → Ty → Set where
  ∦-𝕀-𝔹 : (`ι 𝕀) ∦ (`ι 𝔹)
  ∦-𝔹-𝕀 : (`ι 𝔹) ∦ (`ι 𝕀)
  ∦-base-fun : ∀ {ι A B} → (`ι ι) ∦ (A ⇒ B)
  ∦-fun-base : ∀ {A B ι} → (A ⇒ B) ∦ (`ι ι)
  ∦-base-prod : ∀ {ι A B} → (`ι ι) ∦ (A `× B)
  ∦-prod-base : ∀ {A B ι} → (A `× B) ∦ (`ι ι)

------------------------------------------------------------------------
-- One-step reduction
------------------------------------------------------------------------

infix 2 _—→_
data _—→_ : Term → Term → Set where
  -- Evaluation contexts
  ξ-·₁ :
    ∀ {L L′ M} →
    L —→ L′ →
    L · M —→ L′ · M

  ξ-·₂ :
    ∀ {V M M′} →
    Value V →
    M —→ M′ →
    V · M —→ V · M′

  ξ-let :
    ∀ {L L′ M} →
    L —→ L′ →
    letin L M —→ letin L′ M

  ξ-Λ :
    ∀ {p M M′ A} →
    M —→ M′ →
    Λ[ p ] M :: A —→ Λ[ p ] M′ :: A

  ξ-inst :
    ∀ {M M′ A} →
    M —→ M′ →
    M • A —→ M′ • A

  ξ-ν :
    ∀ {A p M M′} →
    M —→ M′ →
    ν[ A ] p ∙ M —→ ν[ A ] p ∙ M′

  ξ-cast :
    ∀ {M M′ A p B} →
    M —→ M′ →
    (M ⦂ A ⇒[ p ] B) —→ (M′ ⦂ A ⇒[ p ] B)

  ξ-bar :
    ∀ {M M′ A P B} →
    M —→ M′ →
    (M ⦂ A ⇒⟨ P ⟩ B) —→ (M′ ⦂ A ⇒⟨ P ⟩ B)

  ξ-is :
    ∀ {p M M′ G} →
    M —→ M′ →
    is p M G —→ is p M′ G

  ξ-pair₁ :
    ∀ {L L′ M} →
    L —→ L′ →
    pair L M —→ pair L′ M

  ξ-pair₂ :
    ∀ {V M M′} →
    Value V →
    M —→ M′ →
    pair V M —→ pair V M′

  ξ-fst :
    ∀ {M M′} →
    M —→ M′ →
    fst M —→ fst M′

  ξ-snd :
    ∀ {M M′} →
    M —→ M′ →
    snd M —→ snd M′

  ξ-if :
    ∀ {L L′ M N} →
    L —→ L′ →
    ifte L M N —→ ifte L′ M N

  ξ-prim :
    ∀ {op M M′} →
    M —→ M′ →
    prim op M —→ prim op M′

  -- System F and functions
  β-ty :
    ∀ {p V B A} →
    Value V →
    (Λ[ p ] V :: B) • A
      —→ ν[ A ] p ∙ (V ⦂ B ⇒⟨ bind zero ⟩ (B [ A ]ᵗ))

  β-ƛ :
    ∀ {A M V} →
    Value V →
    (ƛ[ A ] M) · V —→ M [ V ]

  β-let :
    ∀ {V M} →
    Value V →
    letin V M —→ M [ V ]

  -- Casts
  cast-generalize :
    ∀ {V A p B} →
    Value V →
    (V ⦂ A ⇒[ p ] (`∀ B))
      —→ Λ[ p ] ((renameᵀ suc V) ⦂ ⇑ᵗ A ⇒[ p ] B) :: B

  cast-instantiate :
    ∀ {V A p B} →
    Value V →
    (V ⦂ (`∀ A) ⇒[ p ] B) —→ (V • ★ ⦂ A [ ★ ]ᵗ ⇒[ p ] B)

  cast-wrap :
    ∀ {C M A₁ B₁ A₂ B₂ p} →
    ((ƛ[ C ] M) ⦂ (A₁ ⇒ B₁) ⇒[ p ] (A₂ ⇒ B₂))
      —→ ƛ[ A₂ ]
          ((rename suc (ƛ[ C ] M) · ((` zero) ⦂ A₂ ⇒[ neg p ] A₁))
            ⦂ B₁ ⇒[ p ] B₂)

  cast-id-base :
    ∀ {V ι p} →
    Value V →
    (V ⦂ (`ι ι) ⇒[ p ] (`ι ι)) —→ V

  cast-id-var :
    ∀ {V X p} →
    Value V →
    (V ⦂ (` X) ⇒[ p ] (` X)) —→ V

  cast-ground :
    ∀ {V A p G} →
    Value V →
    GroundOf A G →
    (V ⦂ A ⇒[ p ] ★) —→ ((V ⦂ A ⇒[ p ] G) ⦂ G ⇒[ - ] ★)

  cast-collapse :
    ∀ {V G A p} →
    Value V →
    Ground G →
    G ∼ A →
    ((V ⦂ G ⇒[ - ] ★) ⦂ ★ ⇒[ p ] A) —→ (V ⦂ G ⇒[ p ] A)

  cast-conflict :
    ∀ {V G A p} →
    Value V →
    Ground G →
    G ∦ A →
    ((V ⦂ G ⇒[ - ] ★) ⦂ ★ ⇒[ p ] A) —→ blame p

  -- Dynamic type tests.  The Scheme `IsFalse` clause is duplicated with
  -- the same guard/result as `IsTrue`, so the active semantics has only
  -- this positive ground-tag test.
  is-true :
    ∀ {p V H} →
    Value V →
    is p (V ⦂ H ⇒[ - ] ★) H —→ $ bool true

  is-seal :
    ∀ {q V X p G} →
    Value V →
    is q (V ⦂ (` X) ⇒[ p ] ★) G —→ blame q

  -- ν rules
  ν-const :
    ∀ {A p c} →
    (ν[ A ] p ∙ ($ c)) —→ $ c

  ν-pair :
    ∀ {A p V W} →
    Value V →
    Value W →
    (ν[ A ] p ∙ (pair V W)) —→ pair (ν[ A ] p ∙ V) (ν[ A ] p ∙ W)

  ν-wrap :
    ∀ {A p B M} →
    (ν[ A ] p ∙ (ƛ[ B ] M)) —→ ƛ[ B ] (ν[ A ] p ∙ M)

  ν-tywrap :
    ∀ {A p q M B} →
    ν[ A ] p ∙ (Λ[ q ] M :: B) —→ Λ[ q ] (ν[ ⇑ᵗ A ] p ∙ M) :: B

  ν-ground :
    ∀ {A p V G} →
    Value V →
    Ground G →
    ν[ A ] p ∙ (V ⦂ G ⇒[ - ] ★) —→ ((ν[ A ] p ∙ V) ⦂ G ⇒[ - ] ★)

  ν-tamper :
    ∀ {A q V X p} →
    Value V →
    ν[ A ] q ∙ (V ⦂ (` X) ⇒[ p ] ★) —→ blame q

  ν-bar :
    ∀ {A p V B X Y} →
    Value (V ⦂ B ⇒⟨ unbind (suc X) ⟩ Y) →
    ν[ A ] p ∙ (V ⦂ B ⇒⟨ unbind (suc X) ⟩ Y)
      —→ ((ν[ A ] p ∙ V) ⦂ B ⇒⟨ unbind X ⟩ Y)

  -- Barriers
  bar-const :
    ∀ {V ι P} →
    Value V →
    (V ⦂ (`ι ι) ⇒⟨ P ⟩ (`ι ι)) —→ V

  bar-pair :
    ∀ {V W A B A′ B′ P} →
    Value V →
    Value W →
    ((pair V W) ⦂ (A `× B) ⇒⟨ P ⟩ (A′ `× B′))
      —→ pair (V ⦂ A ⇒⟨ P ⟩ A′) (W ⦂ B ⇒⟨ P ⟩ B′)

  bar-wrap :
    ∀ {C M A B P A′ B′} →
    ((ƛ[ C ] M) ⦂ (A ⇒ B) ⇒⟨ P ⟩ (A′ ⇒ B′))
      —→ ƛ[ A′ ]
            ((letin
              ((` zero) ⦂ A′ ⇒⟨ negBind P ⟩ A)
              (rename (ext suc) M))
              ⦂ B ⇒⟨ P ⟩ B′)
      -- The bound argument is available at `⇑ᵗ A′` inside the protected
      -- side of an enclosing `bind`; the nested `negBind P` checks its
      -- source annotation back in the opposite context.

  bar-tywrap-bind :
    ∀ {p V B B₁ B₂ X} →
    Value V →
    ((Λ[ p ] V :: B) ⦂ (`∀ B₁) ⇒⟨ bind X ⟩ (`∀ B₂))
      —→
    Λ[ p ]
      ((renameᵀ swap₀₁ V) ⦂ renameᵗ swap₀₁ B ⇒⟨ bind X ⟩ B₂)
      :: B₂

  bar-tywrap-unbind :
    ∀ {p V B B₁ B₂ X} →
    Value V →
    ((Λ[ p ] V :: B) ⦂ (`∀ B₁) ⇒⟨ unbind X ⟩ (`∀ B₂))
      —→
    Λ[ p ] (V ⦂ B ⇒⟨ unbind X ⟩ B₂) :: B₂

  bar-ground :
    ∀ {V G Q} →
    Value V →
    Ground G →
    ((V ⦂ G ⇒[ - ] ★) ⦂ ★ ⇒⟨ Q ⟩ ★) —→ (V ⦂ G ⇒[ - ] ★)

  bar-cancel :
    ∀ {V A′ X A} →
    Value V →
    ((V ⦂ A′ ⇒⟨ unbind X ⟩ (` zero)) ⦂ (` zero) ⇒⟨ bind X ⟩ A)
      —→ V

  bar-drop-bind :
    ∀ {V X α} →
    Value (renameᵀ suc V) →
    ((renameᵀ suc V) ⦂ (` suc X) ⇒⟨ bind α ⟩ (` X)) —→ V

  bar-drop-unbind :
    ∀ {V X α} →
    Value V →
    (V ⦂ (` X) ⇒⟨ unbind α ⟩ (` suc X)) —→ renameᵀ suc V

  -- Base computation
  δ :
    ∀ {op c} →
    prim op ($ c) —→ $ delta op c

  if-true :
    ∀ {M N} →
    ifte ($ bool true) M N —→ M

  if-false :
    ∀ {M N} →
    ifte ($ bool false) M N —→ N

  fst-pair :
    ∀ {V W} →
    Value V →
    Value W →
    fst (pair V W) —→ V

  snd-pair :
    ∀ {V W} →
    Value V →
    Value W →
    snd (pair V W) —→ W

------------------------------------------------------------------------
-- Multi-step closure
------------------------------------------------------------------------

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Term → Term → Set where
  _∎ : (M : Term) → M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} → L —→ M → M —↠ N → L —↠ N

private
  multi-trans : ∀ {M N L} → M —↠ N → N —↠ L → M —↠ L
  multi-trans (_ ∎) ns = ns
  multi-trans (_ —→⟨ step ⟩ ms) ns = _ —→⟨ step ⟩ multi-trans ms ns

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ (L : Term) {M N : Term} → L —↠ M → M —↠ N → L —↠ N
L —↠⟨ LM ⟩ MN = multi-trans LM MN
