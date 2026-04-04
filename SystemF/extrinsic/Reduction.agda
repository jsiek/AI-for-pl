module extrinsic.Reduction where

-- File Charter:
--   * Dynamic semantics for extrinsic System F.
--   * Defines values, one-step reduction, and multi-step closure.
--   * Re-exports `extrinsic.Terms` for shared syntax/typing.

open import extrinsic.Terms public

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

data Value : Term → Set where
  vLam  : {N : Term} → Value (ƛ N)
  vTrue : Value `true
  vFalse : Value `false
  vZero : Value `zero
  vSuc  : {V : Term} → Value V → Value (`suc V)
  vTlam : {N : Term} → Value (Λ N)

infix 2 _—→_
data _—→_ : Term → Term → Set where
  ξ-·₁ : {L L' M : Term} →
         L —→ L' →
         (L · M) —→ (L' · M)

  ξ-·₂ : {V M M' : Term} →
         Value V →
         M —→ M' →
         (V · M) —→ (V · M')

  β-ƛ : {N W : Term} →
        Value W →
        ((ƛ N) · W) —→ N [ W ]

  ξ-suc : {M M' : Term} →
          M —→ M' →
          (`suc M) —→ (`suc M')

  ξ-if : {L L' M N : Term} →
         L —→ L' →
         (`if_then_else L M N) —→ (`if_then_else L' M N)

  ξ-case : {L L' M N : Term} →
           L —→ L' →
           (case_[zero⇒_|suc⇒_] L M N) —→ (case_[zero⇒_|suc⇒_] L' M N)

  β-true : {M N : Term} →
           (`if_then_else `true M N) —→ M

  β-false : {M N : Term} →
            (`if_then_else `false M N) —→ N

  β-zero : {M N : Term} →
           (case_[zero⇒_|suc⇒_] `zero M N) —→ M

  β-suc : {V M N : Term} →
          Value V →
          (case_[zero⇒_|suc⇒_] (`suc V) M N) —→ N [ V ]

  ξ-·[] : {M M' : Term} →
          M —→ M' →
          M ·[] —→ M' ·[]

  β-Λ : {N : Term} {A : Ty} →
        (Λ N) ·[] —→ N

infix 3 _∎
infixr 2 _—→⟨_⟩_
infix 2 _—↠_
data _—↠_ : Term → Term → Set where
  _∎ : (M : Term) → M —↠ M
  _—→⟨_⟩_ : (L : Term) {M N : Term} → L —→ M → M —↠ N → L —↠ N

multi-trans : {M N L : Term} → M —↠ N → N —↠ L → M —↠ L
multi-trans (_ ∎) ms2          = ms2
multi-trans (_ —→⟨ s ⟩ ms1') ms2    = _ —→⟨ s ⟩ (multi-trans ms1' ms2)

infixr 2 _—↠⟨_⟩_
_—↠⟨_⟩_ : ∀ (L : Term) {M N : Term}
    → L —↠ M
    → M —↠ N
      ---------
    → L —↠ N
L —↠⟨ L—↠M ⟩ M—↠N = multi-trans L—↠M M—↠N
