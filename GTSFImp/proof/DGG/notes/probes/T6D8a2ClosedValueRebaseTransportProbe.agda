module T6D8a2ClosedValueRebaseTransportProbe where

-- File Charter:
--   * Calibration probe for D8a2 closed-value CTI2 transport across
--     concrete rebase evidence.
--   * Reuses the T10-style moving-source-pivot world, with `ℕ`
--     store representations so sealed constant values are available.
--   * Records proven transport for a rebase-unrelated constant pair and
--     checked exact-boundary refutations for a rebase-entangled sealed pair.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using (Ty; TyVar; ‵_; `ℕ; ★; ＇_; nonstar-ι)
open import TyStore using (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using (empty; keep; skip; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms using (Term; Value; $; _↓_)
import CastTerms as CT
open import Primitives using (κℕ)
open import Imprecision using (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; instᵐ; ι⊑ι)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CompilePreservesImprecision2 as CPI2


empty-μ : ImpEnv 0
empty-μ ()

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

ℕ₁ : Ty 1
ℕ₁ = ‵ `ℕ

ℕ₂ : Ty 2
ℕ₂ = ‵ `ℕ

W₀ : CTI2.World 0 0 0
W₀ = CPI2.initialWorld empty-μ store-empty

W-paired : CTI2.World 1 1 1
W-paired = CTI2.bothBindWorld X⊑X W₀ ℕ₀ ℕ₀

W : CTI2.World 1 2 2
W = CTI2.rightOnlyWorld W-paired ℕ₁

source-store : TyStore 1
source-store = store-bind store-empty ℕ₀

target-store : TyStore 2
target-store = store-bind (store-bind store-empty ℕ₀) ℕ₁

μ : ImpEnv 2
μ = instᵐ (extendᵐ X⊑X empty-μ)

ηᴸ-fresh : 1 Consistency.↪ᵗ 2
ηᴸ-fresh = keep empty

ηᴿ-id : 2 Consistency.↪ᵗ 2
ηᴿ-id = keep (keep empty)

Wᵖ : CTI2.World 1 2 2
Wᵖ = CTI2.world ηᴸ-fresh ηᴿ-id μ source-store target-store

X : TyVar 1
X = Fin.zero

Y-fresh : TyVar 2
Y-fresh = Fin.zero

Y-old : TyVar 2
Y-old = Fin.suc Fin.zero

fresh-representation : CTI2.StoreRepImp Wᵖ X Y-fresh
fresh-representation = CTI2.store-rep-imp ι⊑ι

old-representation : CTI2.StoreRepImp W X Y-old
old-representation = CTI2.store-rep-imp ι⊑ι

forward-rebase : CTI2.RebaseAt W Wᵖ X Y-fresh
forward-rebase =
  CTI2.rebase-at (CTI2.same-runtime refl refl)
    (λ { {Fin.zero} X≢X → ⊥-elim (X≢X refl) })
    (λ { Fin.zero → refl ; (Fin.suc Fin.zero) → refl })
    refl fresh-representation

reversed-rebase : CTI2.RebaseAt Wᵖ W X Y-old
reversed-rebase =
  CTI2.rebase-at (CTI2.same-runtime refl refl)
    (λ { {Fin.zero} X≢X → ⊥-elim (X≢X refl) })
    (λ { Fin.zero → refl ; (Fin.suc Fin.zero) → refl })
    refl old-representation

mono-forward : CTI2.ImpEnvMono W Wᵖ
mono-forward Z eq = eq

source-entry : CTI2.sourceStoreʷ W ∋ X ⦂ ℕ₁
source-entry = Z∋ refl

target-old-entry : CTI2.targetStoreʷ W ∋ Y-old ⦂ ℕ₂
target-old-entry = S-bind∋ (Z∋ refl) refl

source-seal-typed :
  CTI2.sourceStoreʷ W CTI2.⊢↓[ just X ] seal X ℕ₁
source-seal-typed = CTI2.⊢↓-sealˣ source-entry

target-old-seal-typed :
  CTI2.targetStoreʷ W CTI2.⊢↓[ just Y-old ] seal Y-old ℕ₂
target-old-seal-typed = CTI2.⊢↓-sealˣ target-old-entry

source-value : Term 1
source-value = $ (κℕ 0)

target-value : Term 2
target-value = $ (κℕ 0)

source-value-value : Value source-value
source-value-value = $ (κℕ 0)

target-value-value : Value target-value
target-value-value = $ (κℕ 0)

ℕ-at-W : ℕ₁ CTI2.⊑ᵂ⟨ W ⟩ ℕ₂
ℕ-at-W = ι⊑ι

ℕ-at-Wᵖ : ℕ₁ CTI2.⊑ᵂ⟨ Wᵖ ⟩ ℕ₂
ℕ-at-Wᵖ = ι⊑ι

unrelated-at-W : W CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ ℕ-at-W
unrelated-at-W = CTI2.κ⊑κ² (κℕ 0) ℕ-at-W

unrelated-RebaseAtᴸ-transport :
  W CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ ℕ-at-W
  → CTI2.RebaseAtᴸ W Wᵖ (just X)
  → Σ[ p′ ∈ ℕ₁ CTI2.⊑ᵂ⟨ Wᵖ ⟩ ℕ₂ ]
      (Wᵖ CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ p′)
unrelated-RebaseAtᴸ-transport rel rb =
  ℕ-at-Wᵖ , CTI2.κ⊑κ² (κℕ 0) ℕ-at-Wᵖ

unrelated-RebaseAtᴿ-transport :
  W CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ ℕ-at-W
  → CTI2.RebaseAtᴿ W Wᵖ (just Y-fresh)
  → Σ[ p′ ∈ ℕ₁ CTI2.⊑ᵂ⟨ Wᵖ ⟩ ℕ₂ ]
      (Wᵖ CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ p′)
unrelated-RebaseAtᴿ-transport rel rb =
  ℕ-at-Wᵖ , CTI2.κ⊑κ² (κℕ 0) ℕ-at-Wᵖ

unrelated-TagRebaseAtᴸ-transport :
  W CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ ℕ-at-W
  → CTI2.TagRebaseAtᴸ W Wᵖ (just X) (just Y-fresh)
  → Σ[ p′ ∈ ℕ₁ CTI2.⊑ᵂ⟨ Wᵖ ⟩ ℕ₂ ]
      (Wᵖ CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ p′)
unrelated-TagRebaseAtᴸ-transport rel rb =
  ℕ-at-Wᵖ , CTI2.κ⊑κ² (κℕ 0) ℕ-at-Wᵖ

unrelated-RebaseAtᴸ-verdict :
  Σ[ p′ ∈ ℕ₁ CTI2.⊑ᵂ⟨ Wᵖ ⟩ ℕ₂ ]
    (Wᵖ CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ p′)
unrelated-RebaseAtᴸ-verdict =
  unrelated-RebaseAtᴸ-transport unrelated-at-W
    (CTI2.rebase-varᴸ forward-rebase)

unrelated-RebaseAtᴿ-verdict :
  Σ[ p′ ∈ ℕ₁ CTI2.⊑ᵂ⟨ Wᵖ ⟩ ℕ₂ ]
    (Wᵖ CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ p′)
unrelated-RebaseAtᴿ-verdict =
  unrelated-RebaseAtᴿ-transport unrelated-at-W
    (CTI2.rebase-varᴿ forward-rebase)

unrelated-TagRebaseAtᴸ-verdict :
  Σ[ p′ ∈ ℕ₁ CTI2.⊑ᵂ⟨ Wᵖ ⟩ ℕ₂ ]
    (Wᵖ CTI2.∣ [] ⊢² source-value ⊑ target-value ∶ p′)
unrelated-TagRebaseAtᴸ-verdict =
  unrelated-TagRebaseAtᴸ-transport unrelated-at-W
    (CTI2.tag-rebase-varᴸ forward-rebase)

source-sealed : Term 1
source-sealed = source-value ↓ seal X ℕ₁

target-old-sealed : Term 2
target-old-sealed = target-value ↓ seal Y-old ℕ₂

source-sealed-value : Value source-sealed
source-sealed-value = source-value-value CT.↓ CT.seal

target-old-sealed-value : Value target-old-sealed
target-old-sealed-value = target-value-value CT.↓ CT.seal

pivot-old-at-W : (＇ X) CTI2.⊑ᵂ⟨ W ⟩ (＇ Y-old)
pivot-old-at-W = X⊑X

pivot-old-at-Wᵖ-empty : (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) → ⊥
pivot-old-at-Wᵖ-empty ()

EntangledAtWᵖExact : (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) → Set
EntangledAtWᵖExact p′ =
  CTI2._∣_⊢²_⊑_∶_
    Wᵖ [] source-sealed target-old-sealed
    {A = ＇ X} {B = ＇ Y-old} p′

entangled-at-W :
  W CTI2.∣ [] ⊢² source-sealed ⊑ target-old-sealed ∶ pivot-old-at-W
entangled-at-W =
  CTI2.conceal⊑conceal²
    (CTI2.matched-seal-nonstar nonstar-ι)
    mono-forward
    reversed-rebase
    CTI2.same-[]
    source-seal-typed
    target-old-seal-typed
    (CTI2.κ⊑κ² (κℕ 0) ℕ-at-Wᵖ)
    pivot-old-at-W

entangled-RebaseAtᴸ-exact-empty :
  CTI2.RebaseAtᴸ W Wᵖ (just X)
  → Σ[ p′ ∈ (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) ]
      EntangledAtWᵖExact p′
  → ⊥
entangled-RebaseAtᴸ-exact-empty rb (p′ , rel) =
  pivot-old-at-Wᵖ-empty p′

entangled-RebaseAtᴿ-exact-empty :
  CTI2.RebaseAtᴿ W Wᵖ (just Y-fresh)
  → Σ[ p′ ∈ (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) ]
      EntangledAtWᵖExact p′
  → ⊥
entangled-RebaseAtᴿ-exact-empty rb (p′ , rel) =
  pivot-old-at-Wᵖ-empty p′

entangled-TagRebaseAtᴸ-exact-empty :
  CTI2.TagRebaseAtᴸ W Wᵖ (just X) (just Y-fresh)
  → Σ[ p′ ∈ (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) ]
      EntangledAtWᵖExact p′
  → ⊥
entangled-TagRebaseAtᴸ-exact-empty rb (p′ , rel) =
  pivot-old-at-Wᵖ-empty p′

entangled-RebaseAtᴸ-transport-refuted :
  (W CTI2.∣ [] ⊢² source-sealed ⊑ target-old-sealed ∶ pivot-old-at-W
    → CTI2.RebaseAtᴸ W Wᵖ (just X)
    → Σ[ p′ ∈ (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) ]
        EntangledAtWᵖExact p′)
  → ⊥
entangled-RebaseAtᴸ-transport-refuted claim =
  entangled-RebaseAtᴸ-exact-empty (CTI2.rebase-varᴸ forward-rebase)
    (claim entangled-at-W (CTI2.rebase-varᴸ forward-rebase))

entangled-RebaseAtᴿ-transport-refuted :
  (W CTI2.∣ [] ⊢² source-sealed ⊑ target-old-sealed ∶ pivot-old-at-W
    → CTI2.RebaseAtᴿ W Wᵖ (just Y-fresh)
    → Σ[ p′ ∈ (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) ]
        EntangledAtWᵖExact p′)
  → ⊥
entangled-RebaseAtᴿ-transport-refuted claim =
  entangled-RebaseAtᴿ-exact-empty (CTI2.rebase-varᴿ forward-rebase)
    (claim entangled-at-W (CTI2.rebase-varᴿ forward-rebase))

entangled-TagRebaseAtᴸ-transport-refuted :
  (W CTI2.∣ [] ⊢² source-sealed ⊑ target-old-sealed ∶ pivot-old-at-W
    → CTI2.TagRebaseAtᴸ W Wᵖ (just X) (just Y-fresh)
    → Σ[ p′ ∈ (＇ X) CTI2.⊑ᵂ⟨ Wᵖ ⟩ (＇ Y-old) ]
        EntangledAtWᵖExact p′)
  → ⊥
entangled-TagRebaseAtᴸ-transport-refuted claim =
  entangled-TagRebaseAtᴸ-exact-empty
    (CTI2.tag-rebase-varᴸ forward-rebase)
    (claim entangled-at-W (CTI2.tag-rebase-varᴸ forward-rebase))
