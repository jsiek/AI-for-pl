module experimental.ContextualBetaInst where

-- File Charter:
--   * Gives the leaf-local contextual-coercion experiment a small term and
--     reduction layer.
--   * Records the pending-to-active typing change required by `β-inst` while
--     keeping the raw body coercion unchanged.
--   * Lowers active `inst-in` and `inst-out` leaves to raw identity coercions.
--   * Proves preservation for the experimental `β-inst` rule.
--   * Leaves the live GTSFImp term and reduction definitions unchanged.

import Data.Fin as Fin
open import Data.List using ([])
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore using (store-empty; Z∋)
open import TermCtx using (Z)
open import Conversion using (Conv↑; replaceTy; 〖_,_↑_〗; _⊢↑[_⦂_]_)
open import Primitives using (κℕ)
import CastTerms as Live
import Reduction as LiveReduction
import proof.TypeInTermSubst as LiveTypeSubst
import proof.TypeSafety.Preservation as LivePreservation
import experimental.ContextualCoercion as CC
import experimental.ContextualCoercionActivation as CCA

private
  variable
    Δ Δ′ : TyCtx

------------------------------------------------------------------------
-- Experimental terms
------------------------------------------------------------------------

infixl 7 _⦂∀_[_]
infixl 7 _↑_
infixl 7 _⟨_⟩

data Term : (Δ : TyCtx) → Set where
  live : Live.Term Δ → Term Δ

  _⦂∀_[_] : Term Δ → Ty (Nat.suc Δ) → Ty Δ → Term Δ

  _↑_ : Term Δ → {A B : Ty Δ} → Conv↑ Δ A B → Term Δ

  _⟨_⟩ : Term Δ → CC.Coercion Δ → Term Δ

------------------------------------------------------------------------
-- Typing for the experimental wrappers
------------------------------------------------------------------------

infix 4 _⊢_⦂_

data _⊢_⦂_ (Γ : Live.Ctx) : Term (Live.Δᵉ Γ) →
    Ty (Live.Δᵉ Γ) → Set where

  ⊢live : ∀ {M A}
    → Γ Live.⊢ M ⦂ A
    → Γ ⊢ live M ⦂ A

  ⊢• : ∀ {M A B}
    → Γ ⊢ M ⦂ (`∀ B)
    → Γ ⊢ M ⦂∀ B [ A ] ⦂ B [ A ]ᵗ

  ⊢reveal : ∀ {M A B X R} {c : Conv↑ (Live.Δᵉ Γ) A B}
    → Live.Σᵉ Γ ⊢↑[ X ⦂ R ] c
    → Γ ⊢ M ⦂ A
    → Γ ⊢ M ↑ c ⦂ B

  ⊢cast : ∀ {M κ c A B}
    → κ CC.⊢ c ∶ A ⇒ B
    → Γ ⊢ M ⦂ A
    → Γ ⊢ M ⟨ c ⟩ ⦂ B

------------------------------------------------------------------------
-- Values and pure coercion steps
------------------------------------------------------------------------

data Value {Δ : TyCtx} : Term Δ → Set where
  live : ∀ {V}
    → Live.Value V
    → Value (live V)

infix 2 _—→_

data _—→_ {Δ : TyCtx} : Term Δ → Term Δ → Set where

  id-step : ∀ {V}
    → Live.Value V
    → live V ⟨ CC.id ⟩ —→ live V

  inst-out-step : ∀ {V X}
    → Live.Value V
    → live V ⟨ CC.inst-out X ⟩ —→ live V ⟨ CC.id ⟩

  inst-in-step : ∀ {V X}
    → Live.Value V
    → live V ⟨ CC.inst-in X ⟩ —→ live V ⟨ CC.id ⟩

------------------------------------------------------------------------
-- Store-changing instantiation
------------------------------------------------------------------------

infix 2 _—→[_]_

data _—→[_]_ : ∀ {Δ Δ′}
  → Term Δ
  → LiveReduction.StoreChange Δ Δ′
  → Term Δ′
  → Set where

  β-inst : ∀ {Δ} {V : Live.Term Δ}
      {A : Ty (Nat.suc Δ)} {B : Ty Δ}
      {c : CC.Coercion (Nat.suc Δ)}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CC.instCtx CC.pending (CC.ordinaryCtx {Δ = Δ})
        CC.⊢ c ∶ A ⇒ ⇑ᵗ B
    → Live.Value V
    → B ≢ ★
    → live V ⟨ CC.inst c ⟩
        —→[ LiveReduction.bind ★ ]
      ((live (Live.⇑ᵗᵐ V)
          ⦂∀ LiveReduction.applyBody (LiveReduction.bind ★) A
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.zero , ★ ↑ A 〗)
        ⟨ c ⟩

------------------------------------------------------------------------
-- Type preservation for `β-inst`
------------------------------------------------------------------------

transport-typing : ∀ {Γ : Live.Ctx} {M A B}
  → A ≡ B
  → Γ ⊢ M ⦂ A
  → Γ ⊢ M ⦂ B
transport-typing refl M⊢ = M⊢

β-inst-redex-typing : ∀ {Γ : Live.Ctx}
    {V : Live.Term (Live.Δᵉ Γ)}
    {A : Ty (Nat.suc (Live.Δᵉ Γ))}
    {B : Ty (Live.Δᵉ Γ)}
    {c : CC.Coercion (Nat.suc (Live.Δᵉ Γ))}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → CC.instCtx CC.pending
      (CC.ordinaryCtx {Δ = Live.Δᵉ Γ}) CC.⊢ c ∶ A ⇒ ⇑ᵗ B
  → (B≢★ : B ≢ ★)
  → Γ Live.⊢ V ⦂ (`∀ A)
  → Γ ⊢ live V ⟨ CC.inst c ⟩ ⦂ B
β-inst-redex-typing nonvar occurs pending-c⊢ B≢★ V⊢ =
  ⊢cast (CC.⊢inst nonvar occurs pending-c⊢ B≢★) (⊢live V⊢)

β-inst-contractum-typing : ∀ {Γ : Live.Ctx}
    {V : Live.Term (Live.Δᵉ Γ)}
    {A : Ty (Nat.suc (Live.Δᵉ Γ))}
    {B : Ty (Live.Δᵉ Γ)}
    {c : CC.Coercion (Nat.suc (Live.Δᵉ Γ))}
  → CC.instCtx CC.pending
      (CC.ordinaryCtx {Δ = Live.Δᵉ Γ}) CC.⊢ c ∶ A ⇒ ⇑ᵗ B
  → Γ Live.⊢ V ⦂ (`∀ A)
  → (Γ Live.,ˢ ★) ⊢
      ((live (Live.⇑ᵗᵐ V)
          ⦂∀ LiveReduction.applyBody (LiveReduction.bind ★) A
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.zero , ★ ↑ A 〗)
      ⟨ c ⟩
      ⦂ ⇑ᵗ B
β-inst-contractum-typing {A = A} pending-c⊢ V⊢ =
  ⊢cast active-c⊢ revealed⊢
  where
  active-c⊢ = CCA.activate-newest-typing pending-c⊢

  shifted⊢ =
    ⊢live (LiveTypeSubst.typing-shiftᵗ-bind {C = ★} V⊢)

  applied⊢ = ⊢• shifted⊢

  opened⊢ =
    transport-typing (LivePreservation.applyBody-open-zero A) applied⊢

  reveal⊢ =
    LivePreservation.structural-reveal-typing A (Z∋ refl)

  revealed⊢ = ⊢reveal reveal⊢ opened⊢

β-inst-preservation : ∀ {Γ : Live.Ctx}
    {V : Live.Term (Live.Δᵉ Γ)}
    {A : Ty (Nat.suc (Live.Δᵉ Γ))}
    {B : Ty (Live.Δᵉ Γ)}
    {c : CC.Coercion (Nat.suc (Live.Δᵉ Γ))}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → CC.instCtx CC.pending
      (CC.ordinaryCtx {Δ = Live.Δᵉ Γ}) CC.⊢ c ∶ A ⇒ ⇑ᵗ B
  → Live.Value V
  → B ≢ ★
  → Γ Live.⊢ V ⦂ (`∀ A)
  → Σ[ N ∈ Term (Nat.suc (Live.Δᵉ Γ)) ]
      (live V ⟨ CC.inst c ⟩ —→[ LiveReduction.bind ★ ] N)
      × ((Γ Live.,ˢ ★) ⊢ N ⦂ ⇑ᵗ B)
β-inst-preservation nonvar occurs pending-c⊢ vV B≢★ V⊢ =
  _ , β-inst nonvar occurs pending-c⊢ vV B≢★
    , β-inst-contractum-typing pending-c⊢ V⊢

------------------------------------------------------------------------
-- Focused checked examples
------------------------------------------------------------------------

Dyn⇒Dyn0 : Ty 0
Dyn⇒Dyn0 = ★ ⇒ ★

identity-inst-coercion : CC.Coercion 0
identity-inst-coercion = CC.inst CC.identity-body-coercion

identity-inst-typing :
  CC.ordinaryCtx CC.⊢ identity-inst-coercion
    ∶ (`∀ CC.X⇒X) ⇒ Dyn⇒Dyn0
identity-inst-typing =
  CC.⊢inst nonvar-fun (∈-fun-left var-∈)
    CC.identity-body-pending (λ ())

poly-id : Live.Term 0
poly-id = Live.Λ (Live.ƛ (Live.` 0))

poly-id-value : Live.Value poly-id
poly-id-value = Live.Λ (Live.ƛ (Live.` 0))

identity-inst-redex : Term 0
identity-inst-redex = live poly-id ⟨ identity-inst-coercion ⟩

identity-inst-contractum : Term 1
identity-inst-contractum =
  ((live (Live.⇑ᵗᵐ poly-id)
      ⦂∀ LiveReduction.applyBody (LiveReduction.bind ★) CC.X⇒X
        [ ＇ Fin.zero ])
    ↑ 〖 Fin.zero , ★ ↑ CC.X⇒X 〗)
    ⟨ CC.identity-body-coercion ⟩

identity-β-inst :
  identity-inst-redex —→[ LiveReduction.bind ★ ]
    identity-inst-contractum
identity-β-inst =
  β-inst nonvar-fun (∈-fun-left var-∈)
    CC.identity-body-pending poly-id-value (λ ())

identity-ctx : Live.Ctx
identity-ctx = Live.⟨ 0 , store-empty , [] ⟩

poly-id-⊢ : identity-ctx Live.⊢ poly-id ⦂ (`∀ CC.X⇒X)
poly-id-⊢ =
  Live.⊢Λ (Live.ƛ (Live.` 0)) (Live.⊢ƛ (Live.⊢` Z))

identity-inst-redex-⊢ :
  identity-ctx ⊢ identity-inst-redex ⦂ Dyn⇒Dyn0
identity-inst-redex-⊢ =
  β-inst-redex-typing nonvar-fun (∈-fun-left var-∈)
    CC.identity-body-pending (λ ()) poly-id-⊢

identity-inst-contractum-⊢ :
  (identity-ctx Live.,ˢ ★) ⊢ identity-inst-contractum ⦂ ⇑ᵗ Dyn⇒Dyn0
identity-inst-contractum-⊢ =
  proj₂ (proj₂ (β-inst-preservation nonvar-fun
    (∈-fun-left var-∈) CC.identity-body-pending
    poly-id-value (λ ()) poly-id-⊢))

nat-value : Live.Term 1
nat-value = Live.$ (κℕ 0)

nat-value-value : Live.Value nat-value
nat-value-value = Live.$ (κℕ 0)

inst-out-lowers-to-id :
  live nat-value ⟨ CC.inst-out Fin.zero ⟩ —→
    live nat-value ⟨ CC.id ⟩
inst-out-lowers-to-id = inst-out-step nat-value-value

inst-in-lowers-to-id :
  live nat-value ⟨ CC.inst-in Fin.zero ⟩ —→
    live nat-value ⟨ CC.id ⟩
inst-in-lowers-to-id = inst-in-step nat-value-value
