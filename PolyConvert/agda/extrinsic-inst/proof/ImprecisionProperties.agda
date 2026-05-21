module proof.ImprecisionProperties where

-- File Charter:
--   * Properties of type imprecision.
--   * Includes seal-context weakening and small structural facts about
--     imprecision contexts.
--   * Includes insertion/opening helpers for imprecision evidence.
--   * Includes structural transitivity for type imprecision.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (_<_; _≤_; zero; suc; z<s; s<s)
open import Data.Nat.Properties using (<-≤-trans; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types
open import Imprecision
open import Store
open import proof.ConsistencyProperties using (drop-⇑ᵗ-WfTy-extend-X⊑X)
open import proof.TypeProperties
open import proof.StoreProperties using (len<suc-StoreWf)

------------------------------------------------------------------------
-- Correctness of src⊑ and tgt⊑
------------------------------------------------------------------------

dropVarFrom-raise-same :
  ∀ k X →
  dropVarFrom k (raiseVarFrom k X) ≡ X
dropVarFrom-raise-same zero X = refl
dropVarFrom-raise-same (suc k) zero = refl
dropVarFrom-raise-same (suc k) (suc X) =
  cong suc (dropVarFrom-raise-same k X)

dropTyFrom-raise-same :
  ∀ k A →
  dropTyFrom k (renameᵗ (raiseVarFrom k) A) ≡ A
dropTyFrom-raise-same k (＇ X) =
  cong ＇_ (dropVarFrom-raise-same k X)
dropTyFrom-raise-same k (｀ α) = refl
dropTyFrom-raise-same k (‵ ι) = refl
dropTyFrom-raise-same k ★ = refl
dropTyFrom-raise-same k (A ⇒ B) =
  cong₂ _⇒_ (dropTyFrom-raise-same k A) (dropTyFrom-raise-same k B)
dropTyFrom-raise-same k (`∀ A)
  rewrite rename-raise-ext k A =
  cong `∀ (dropTyFrom-raise-same (suc k) A)

src⊑-correct : ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  src⊑ p ≡ A
src⊑-correct ⊢★-⊑-★ = refl
src⊑-correct (⊢X-⊑-★ xν) = refl
src⊑-correct (⊢A-⊑-★ g p⊢) = src⊑-correct p⊢
src⊑-correct (⊢X-⊑-X x∈) = refl
src⊑-correct (⊢α-⊑-α wfα) = refl
src⊑-correct ⊢ι-⊑-ι = refl
src⊑-correct (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  cong₂ _⇒_ (src⊑-correct p⊢) (src⊑-correct q⊢)
src⊑-correct (⊢∀A-⊑-∀B p⊢) = cong `∀ (src⊑-correct p⊢)
src⊑-correct (⊢∀A-⊑-B wfB p⊢) = cong `∀ (src⊑-correct p⊢)

tgt⊑-correct : ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  tgt⊑ p ≡ B
tgt⊑-correct ⊢★-⊑-★ = refl
tgt⊑-correct (⊢X-⊑-★ xν) = refl
tgt⊑-correct (⊢A-⊑-★ g p⊢) = refl
tgt⊑-correct (⊢X-⊑-X x∈) = refl
tgt⊑-correct (⊢α-⊑-α wfα) = refl
tgt⊑-correct ⊢ι-⊑-ι = refl
tgt⊑-correct (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  cong₂ _⇒_ (tgt⊑-correct p⊢) (tgt⊑-correct q⊢)
tgt⊑-correct (⊢∀A-⊑-∀B p⊢) = cong `∀ (tgt⊑-correct p⊢)
tgt⊑-correct (⊢∀A-⊑-B {B = B} wfB p⊢) =
  trans (cong (dropTyFrom zero) (tgt⊑-correct p⊢))
        (dropTyFrom-raise-same zero B)

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

⊑-src-wf : ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  WfTy (length Γ) Ψ A
⊑-src-wf ⊢★-⊑-★ = wf★
⊑-src-wf (⊢X-⊑-★ xν) = wfVar (∋→< xν)
⊑-src-wf (⊢A-⊑-★ g p⊢) = ⊑-src-wf p⊢
⊑-src-wf (⊢X-⊑-X x∈) = wfVar (∋→< x∈)
⊑-src-wf (⊢α-⊑-α wfα) = wfα
⊑-src-wf ⊢ι-⊑-ι = wfBase
⊑-src-wf (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  wf⇒ (⊑-src-wf p⊢) (⊑-src-wf q⊢)
⊑-src-wf (⊢∀A-⊑-∀B p⊢) = wf∀ (⊑-src-wf p⊢)
⊑-src-wf (⊢∀A-⊑-B wfB p⊢) = wf∀ (⊑-src-wf p⊢)

⊑-tgt-wf : ∀ {Ψ Γ p A B} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  WfTy (length Γ) Ψ B
⊑-tgt-wf ⊢★-⊑-★ = wf★
⊑-tgt-wf (⊢X-⊑-★ xν) = wf★
⊑-tgt-wf (⊢A-⊑-★ g p⊢) = wf★
⊑-tgt-wf (⊢X-⊑-X x∈) = wfVar (∋→< x∈)
⊑-tgt-wf (⊢α-⊑-α wfα) = wfα
⊑-tgt-wf ⊢ι-⊑-ι = wfBase
⊑-tgt-wf (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  wf⇒ (⊑-tgt-wf p⊢) (⊑-tgt-wf q⊢)
⊑-tgt-wf (⊢∀A-⊑-∀B p⊢) = wf∀ (⊑-tgt-wf p⊢)
⊑-tgt-wf (⊢∀A-⊑-B wfB p⊢) = wfB

⊑-tgt-non∀ :
  ∀ {Ψ Γ p A B} →
  Non∀ A →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Non∀ B
⊑-tgt-non∀ non∀-★ ⊢★-⊑-★ = non∀-★
⊑-tgt-non∀ non∀A (⊢X-⊑-★ xν) = non∀-★
⊑-tgt-non∀ non∀A (⊢A-⊑-★ g p⊢) = non∀-★
⊑-tgt-non∀ non∀A (⊢X-⊑-X x∈) = non∀-＇
⊑-tgt-non∀ non∀A (⊢α-⊑-α wfα) = non∀-｀
⊑-tgt-non∀ non∀A ⊢ι-⊑-ι = non∀-‵
⊑-tgt-non∀ non∀-⇒ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) = non∀-⇒

wk-⊑ :
  ∀ {Ψ Ψ′ Γᵢ p A B} →
  Ψ ≤ Ψ′ →
  Ψ ∣ Γᵢ ⊢ p ⦂ A ⊑ B →
  Ψ′ ∣ Γᵢ ⊢ p ⦂ A ⊑ B
wk-⊑ Ψ≤Ψ′ ⊢★-⊑-★ = ⊢★-⊑-★
wk-⊑ Ψ≤Ψ′ (⊢X-⊑-★ xν) = ⊢X-⊑-★ xν
wk-⊑ Ψ≤Ψ′ (⊢A-⊑-★ g p⊢) = ⊢A-⊑-★ g (wk-⊑ Ψ≤Ψ′ p⊢)
wk-⊑ Ψ≤Ψ′ (⊢X-⊑-X x∈) = ⊢X-⊑-X x∈
wk-⊑ Ψ≤Ψ′ (⊢α-⊑-α wfα) = ⊢α-⊑-α (WfTy-weakenˢ wfα Ψ≤Ψ′)
wk-⊑ Ψ≤Ψ′ ⊢ι-⊑-ι = ⊢ι-⊑-ι
wk-⊑ Ψ≤Ψ′ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (wk-⊑ Ψ≤Ψ′ p⊢) (wk-⊑ Ψ≤Ψ′ q⊢)
wk-⊑ Ψ≤Ψ′ (⊢∀A-⊑-∀B p⊢) = ⊢∀A-⊑-∀B (wk-⊑ Ψ≤Ψ′ p⊢)
wk-⊑ Ψ≤Ψ′ (⊢∀A-⊑-B wfB p⊢) =
  ⊢∀A-⊑-B (WfTy-weakenˢ wfB Ψ≤Ψ′) (wk-⊑ Ψ≤Ψ′ p⊢)

wk-⊒ :
  ∀ {Ψ Ψ′ Γᵢ p A B} →
  Ψ ≤ Ψ′ →
  Ψ ∣ Γᵢ ⊢ p ⦂ A ⊒ B →
  Ψ′ ∣ Γᵢ ⊢ p ⦂ A ⊒ B
wk-⊒ = wk-⊑

length-extend-X⊑X[] :
  ∀ Δ →
  length (extend-X⊑X Δ []) ≡ Δ
length-extend-X⊑X[] zero = refl
length-extend-X⊑X[] (suc Δ) = cong suc (length-extend-X⊑X[] Δ)

extend-X⊑X-lookup :
  ∀ {Δ X} →
  X < Δ →
  extend-X⊑X Δ [] ∋ X ∶ X⊑X
extend-X⊑X-lookup {Δ = zero} ()
extend-X⊑X-lookup {Δ = suc Δ} {X = zero} z<s = here
extend-X⊑X-lookup {Δ = suc Δ} {X = suc X} (s<s X<Δ) =
  there (extend-X⊑X-lookup X<Δ)

reflImp-wt-extend-X⊑X :
  ∀ {Δ Ψ A} →
  WfTy Δ Ψ A →
  Ψ ∣ extend-X⊑X Δ [] ⊢ reflImp A ⦂ A ⊑ A
reflImp-wt-extend-X⊑X (wfVar X<Δ) =
  ⊢X-⊑-X (extend-X⊑X-lookup X<Δ)
reflImp-wt-extend-X⊑X (wfSeal α<Ψ) = ⊢α-⊑-α (wfSeal α<Ψ)
reflImp-wt-extend-X⊑X wfBase = ⊢ι-⊑-ι
reflImp-wt-extend-X⊑X wf★ = ⊢★-⊑-★
reflImp-wt-extend-X⊑X (wf⇒ wfA wfB) =
  ⊢A⇒B-⊑-A′⇒B′
    (reflImp-wt-extend-X⊑X wfA)
    (reflImp-wt-extend-X⊑X wfB)
reflImp-wt-extend-X⊑X (wf∀ wfA) =
  ⊢∀A-⊑-∀B (reflImp-wt-extend-X⊑X wfA)

⊑-src-wf-extend-X⊑X :
  ∀ {Δ p A B} →
  0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy Δ 0 A
⊑-src-wf-extend-X⊑X {Δ = Δ} p⊢ =
  subst (λ n → WfTy n 0 _) (length-extend-X⊑X[] Δ) (⊑-src-wf p⊢)

⊑-tgt-wf-extend-X⊑X :
  ∀ {Δ p A B} →
  0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy Δ 0 B
⊑-tgt-wf-extend-X⊑X {Δ = Δ} p⊢ =
  subst (λ n → WfTy n 0 _) (length-extend-X⊑X[] Δ) (⊑-tgt-wf p⊢)

⊑-tgt-wf-prefix :
  ∀ {Δ Φ A B p} →
  WfTy (length Φ) 0 A →
  0 ∣ Φ ++ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy (length Φ) 0 B
⊑-tgt-wf-prefix wf★ ⊢★-⊑-★ = wf★
⊑-tgt-wf-prefix wfA (⊢X-⊑-★ xν) = wf★
⊑-tgt-wf-prefix wfA (⊢A-⊑-★ g p⊢) = wf★
⊑-tgt-wf-prefix (wfVar X<Φ) (⊢X-⊑-X x∈) = wfVar X<Φ
⊑-tgt-wf-prefix (wfSeal ()) (⊢α-⊑-α wfα)
⊑-tgt-wf-prefix wfBase ⊢ι-⊑-ι = wfBase
⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} (wf⇒ wfA wfB) (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  wf⇒ (⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} wfA p⊢)
       (⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} wfB q⊢)
⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} (wf∀ wfA) (⊢∀A-⊑-∀B p⊢) =
  wf∀ (⊑-tgt-wf-prefix {Δ = Δ} {Φ = X⊑X ∷ Φ} wfA p⊢)
⊑-tgt-wf-prefix {Δ = Δ} {Φ = Φ} (wf∀ wfA) (⊢∀A-⊑-B wfB p⊢) =
  drop-⇑ᵗ-WfTy-extend-X⊑X {Δ = length Φ}
    (⊑-tgt-wf-prefix {Δ = Δ} {Φ = X⊑★ ∷ Φ} wfA p⊢)

⊑-tgt-wf-closed-extend-X⊑X :
  ∀ {Δ A B p} →
  WfTy 0 0 A →
  0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B →
  WfTy 0 0 B
⊑-tgt-wf-closed-extend-X⊑X wfA p⊢ =
  ⊑-tgt-wf-prefix {Φ = []} wfA p⊢

⊑-tgt-wf-prefix-any :
  ∀ {Φ Γ A B p} →
  WfTy (length Φ) 0 A →
  0 ∣ Φ ++ Γ ⊢ p ⦂ A ⊑ B →
  WfTy (length Φ) 0 B
⊑-tgt-wf-prefix-any wf★ ⊢★-⊑-★ = wf★
⊑-tgt-wf-prefix-any wfA (⊢X-⊑-★ xν) = wf★
⊑-tgt-wf-prefix-any wfA (⊢A-⊑-★ g p⊢) = wf★
⊑-tgt-wf-prefix-any (wfVar X<Φ) (⊢X-⊑-X x∈) = wfVar X<Φ
⊑-tgt-wf-prefix-any (wfSeal ()) (⊢α-⊑-α wfα)
⊑-tgt-wf-prefix-any wfBase ⊢ι-⊑-ι = wfBase
⊑-tgt-wf-prefix-any {Φ = Φ} {Γ = Γ}
    (wf⇒ wfA wfB) (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  wf⇒ (⊑-tgt-wf-prefix-any {Φ = Φ} {Γ = Γ} wfA p⊢)
       (⊑-tgt-wf-prefix-any {Φ = Φ} {Γ = Γ} wfB q⊢)
⊑-tgt-wf-prefix-any {Φ = Φ} {Γ = Γ} (wf∀ wfA) (⊢∀A-⊑-∀B p⊢) =
  wf∀ (⊑-tgt-wf-prefix-any {Φ = X⊑X ∷ Φ} {Γ = Γ} wfA p⊢)
⊑-tgt-wf-prefix-any {Φ = Φ} {Γ = Γ} (wf∀ wfA) (⊢∀A-⊑-B wfB p⊢) =
  drop-⇑ᵗ-WfTy-extend-X⊑X {Δ = length Φ}
    (⊑-tgt-wf-prefix-any {Φ = X⊑★ ∷ Φ} {Γ = Γ} wfA p⊢)

⊑-tgt-wf-closed :
  ∀ {Φ A B p} →
  WfTy 0 0 A →
  0 ∣ Φ ⊢ p ⦂ A ⊑ B →
  WfTy 0 0 B
⊑-tgt-wf-closed wfA p⊢ =
  ⊑-tgt-wf-prefix-any {Φ = []} wfA p⊢

cong-⊢⊑ :
  ∀ {Ψ Γ p A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ p ⦂ A′ ⊑ B′
cong-⊢⊑ refl refl p⊢ = p⊢

cong-⊢⊑-raw :
  ∀ {Ψ Γ p p′ A A′ B B′} →
  p ≡ p′ →
  A ≡ A′ →
  B ≡ B′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ p′ ⦂ A′ ⊑ B′
cong-⊢⊑-raw refl refl refl p⊢ = p⊢

VarSubst : SealCtx → VarPrecCtx → Ty → VarPrec → Set
VarSubst Ψ Γ A X⊑X = Ψ ∣ Γ ⊢ reflImp A ⦂ A ⊑ A
VarSubst Ψ Γ A X⊑★ = Ψ ∣ Γ ⊢ starImp A ⦂ A ⊑ ★

rename⊑-refl :
  ∀ ρ A →
  rename⊑ ρ (reflImp A) ≡ reflImp (renameᵗ ρ A)
rename⊑-refl ρ (＇ X) = refl
rename⊑-refl ρ (｀ α) = refl
rename⊑-refl ρ (‵ ι) = refl
rename⊑-refl ρ ★ = refl
rename⊑-refl ρ (A ⇒ B) =
  cong₂ _↦_ (rename⊑-refl ρ A) (rename⊑-refl ρ B)
rename⊑-refl ρ (`∀ A) = cong ‵∀_ (rename⊑-refl (extᵗ ρ) A)

rename⊑-star :
  ∀ ρ A →
  rename⊑ ρ (starImp A) ≡ starImp (renameᵗ ρ A)
rename⊑-star ρ (＇ X) = refl
rename⊑-star ρ (｀ α) = refl
rename⊑-star ρ (‵ ι) = refl
rename⊑-star ρ ★ = refl
rename⊑-star ρ (A ⇒ B) =
  cong _!
    (cong₂ _↦_ (rename⊑-star ρ A) (rename⊑-star ρ B))
rename⊑-star ρ (`∀ A) = cong ν_ (rename⊑-star (extᵗ ρ) A)

rename⊑-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  (p : Imp) →
  rename⊑ ρ p ≡ rename⊑ ρ′ p
rename⊑-cong h id★ = refl
rename⊑-cong h (‵ X !) = cong ‵_! (h X)
rename⊑-cong h (p !) = cong _! (rename⊑-cong h p)
rename⊑-cong h (idₓ X) = cong idₓ_ (h X)
rename⊑-cong h (idₛ α) = refl
rename⊑-cong h (idι ι) = refl
rename⊑-cong h (p ↦ q) =
  cong₂ _↦_ (rename⊑-cong h p) (rename⊑-cong h q)
rename⊑-cong {ρ = ρ} {ρ′ = ρ′} h (‵∀ p) =
  cong ‵∀_ (rename⊑-cong h′ p)
  where
    h′ : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    h′ zero = refl
    h′ (suc X) = cong suc (h X)
rename⊑-cong {ρ = ρ} {ρ′ = ρ′} h (ν p) =
  cong ν_ (rename⊑-cong h′ p)
  where
    h′ : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    h′ zero = refl
    h′ (suc X) = cong suc (h X)

rename∋-insert :
  ∀ {Φ Γ X m m′} →
  (Φ ++ Γ) ∋ X ∶ m →
  (Φ ++ m′ ∷ Γ) ∋ raiseVarFrom (length Φ) X ∶ m
rename∋-insert {Φ = []} x∈ = there x∈
rename∋-insert {Φ = m₀ ∷ Φ} here = here
rename∋-insert {Φ = m₀ ∷ Φ} (there x∈) =
  there (rename∋-insert {Φ = Φ} x∈)

lookup-mode :
  ∀ Γ {X} →
  X < length Γ →
  Σ VarPrec (λ m → Γ ∋ X ∶ m)
lookup-mode [] ()
lookup-mode (m ∷ Γ) {zero} z<s = m , here
lookup-mode (m ∷ Γ) {suc X} (s<s X<Γ) with lookup-mode Γ X<Γ
lookup-mode (m ∷ Γ) {suc X} (s<s X<Γ) | m′ , x∈ = m′ , there x∈

raiseWf :
  ∀ {Φ Γ m′} →
  TyRenameWf (length (Φ ++ Γ)) (length (Φ ++ m′ ∷ Γ))
    (raiseVarFrom (length Φ))
raiseWf {Φ = Φ} X<len =
  ∋→< (rename∋-insert {Φ = Φ} (proj₂ (lookup-mode _ X<len)))

wkImpAt :
  ∀ {Ψ Φ Γ p A B m′} →
  Ψ ∣ (Φ ++ Γ) ⊢ p ⦂ A ⊑ B →
  Ψ ∣ (Φ ++ m′ ∷ Γ) ⊢
    rename⊑ (raiseVarFrom (length Φ)) p ⦂
    renameᵗ (raiseVarFrom (length Φ)) A ⊑
    renameᵗ (raiseVarFrom (length Φ)) B
wkImpAt {Φ = Φ} ⊢★-⊑-★ = ⊢★-⊑-★
wkImpAt {Φ = Φ} (⊢X-⊑-★ xν) = ⊢X-⊑-★ (rename∋-insert {Φ = Φ} xν)
wkImpAt {Φ = Φ} (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (renameᵗ-ground _ g) (wkImpAt {Φ = Φ} p⊢)
wkImpAt {Φ = Φ} (⊢X-⊑-X x∈) =
  ⊢X-⊑-X (rename∋-insert {Φ = Φ} x∈)
wkImpAt {Φ = Φ} (⊢α-⊑-α (wfSeal α<Ψ)) = ⊢α-⊑-α (wfSeal α<Ψ)
wkImpAt {Φ = Φ} ⊢ι-⊑-ι = ⊢ι-⊑-ι
wkImpAt {Φ = Φ} (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (wkImpAt {Φ = Φ} p⊢) (wkImpAt {Φ = Φ} q⊢)
wkImpAt {Φ = Φ} (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B
    (cong-⊢⊑-raw
      (sym (rename⊑-cong (raise-ext (length Φ)) _))
      (sym (rename-raise-ext (length Φ) _))
      (sym (rename-raise-ext (length Φ) _))
      (wkImpAt {Φ = X⊑X ∷ Φ} p⊢))
wkImpAt {Φ = Φ} (⊢∀A-⊑-B {A = A} {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (renameᵗ-preserves-WfTy wfB (raiseWf {Φ = Φ}))
    (cong-⊢⊑-raw
      (sym (rename⊑-cong (raise-ext (length Φ)) _))
      (sym (rename-raise-ext (length Φ) A))
      (rename-raise-⇑ᵗ (length Φ) B)
      (wkImpAt {Φ = X⊑★ ∷ Φ} p⊢))

wk-VarSubst :
  ∀ {Ψ Γ A m m′} →
  VarSubst Ψ Γ A m →
  VarSubst Ψ (m′ ∷ Γ) (⇑ᵗ A) m
wk-VarSubst {m = X⊑X} h =
  cong-⊢⊑-raw (rename⊑-refl suc _) refl refl
    (wkImpAt {Φ = []} h)
wk-VarSubst {m = X⊑★} h =
  cong-⊢⊑-raw (rename⊑-star suc _) refl refl
    (wkImpAt {Φ = []} h)

plain-var-subst :
  ∀ {Δ Ψ X m} →
  extend-X⊑X Δ [] ∋ X ∶ m →
  VarSubst Ψ (extend-X⊑X Δ []) (＇ X) m
plain-var-subst {Δ = zero} ()
plain-var-subst {Δ = suc Δ} here = ⊢X-⊑-X here
plain-var-subst {Δ = suc Δ} {Ψ = Ψ} (there x∈) =
  wk-VarSubst {m′ = X⊑X} (plain-var-subst {Ψ = Ψ} x∈)

subst-var-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ X m} →
  StoreWf Δ Ψ Σ →
  (Φ ++ X⊑★ ∷ extend-X⊑X Δ []) ∋ X ∶ m →
  VarSubst (suc Ψ) (Φ ++ extend-X⊑X Δ [])
    (substVarFrom (length Φ) (｀ (length Σ)) X) m
subst-var-prefix {Φ = []} wfΣ here =
  ⊢A-⊑-★ (｀ _) (⊢α-⊑-α (wfSeal (len<suc-StoreWf wfΣ)))
subst-var-prefix {Ψ = Ψ} {Φ = []} wfΣ (there x∈) =
  plain-var-subst {Ψ = suc Ψ} x∈
subst-var-prefix {Φ = X⊑X ∷ Φ} wfΣ here = ⊢X-⊑-X here
subst-var-prefix {Φ = X⊑X ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-prefix {Φ = Φ} wfΣ x∈)
subst-var-prefix {Φ = X⊑★ ∷ Φ} wfΣ here = ⊢X-⊑-★ here
subst-var-prefix {Φ = X⊑★ ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-prefix {Φ = Φ} wfΣ x∈)

varSubst-wf :
  ∀ {Ψ Γ A m} →
  VarSubst Ψ Γ A m →
  WfTy (length Γ) Ψ A
varSubst-wf {m = X⊑X} h = ⊑-src-wf h
varSubst-wf {m = X⊑★} h = ⊑-src-wf h

substWf-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ} →
  StoreWf Δ Ψ Σ →
  TySubstWf
    (length (Φ ++ X⊑★ ∷ extend-X⊑X Δ []))
    (length (Φ ++ extend-X⊑X Δ []))
    (suc Ψ)
    (substVarFrom (length Φ) (｀ (length Σ)))
substWf-prefix {Φ = Φ} wfΣ X<len =
  varSubst-wf (subst-var-prefix {Φ = Φ} wfΣ (proj₂ (lookup-mode _ X<len)))

open-fresh-ν⊑-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ : VarPrecCtx}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (Φ ++ X⊑★ ∷ extend-X⊑X Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ (Φ ++ extend-X⊑X Δ []) ⊢
    substAt⊑ (length Φ) (｀ (length Σ)) p ⦂
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) A ⊑
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) B
open-fresh-ν⊑-prefix wfΣ ⊢★-⊑-★ = ⊢★-⊑-★
open-fresh-ν⊑-prefix wfΣ (⊢X-⊑-★ xν) = subst-var-prefix wfΣ xν
open-fresh-ν⊑-prefix wfΣ (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (substᵗ-ground _ g) (open-fresh-ν⊑-prefix wfΣ p⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊢X-⊑-X x∈) =
  subst-var-prefix {Φ = Φ} wfΣ x∈
open-fresh-ν⊑-prefix wfΣ (⊢α-⊑-α (wfSeal α<Ψ)) =
  ⊢α-⊑-α (wfSeal (<-≤-trans α<Ψ (n≤1+n _)))
open-fresh-ν⊑-prefix wfΣ ⊢ι-⊑-ι = ⊢ι-⊑-ι
open-fresh-ν⊑-prefix wfΣ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (open-fresh-ν⊑-prefix wfΣ p⊢)
       (open-fresh-ν⊑-prefix wfΣ q⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B (open-fresh-ν⊑-prefix {Φ = X⊑X ∷ Φ} wfΣ p⊢)
open-fresh-ν⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-B {A = A} {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (n≤1+n _))
      (substWf-prefix {Φ = Φ} wfΣ))
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc
        (substVarFrom (length Φ) (｀ _))
        B)
      (open-fresh-ν⊑-prefix {Φ = X⊑★ ∷ Φ} wfΣ p⊢))

open-fresh-ν⊑ :
  ∀ {Δ Ψ}{Σ : Store}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (X⊑★ ∷ extend-X⊑X Δ []) ⊢ p ⦂ A ⊑ ⇑ᵗ B →
  suc Ψ ∣ extend-X⊑X Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
    (A [ ｀ (length Σ) ]ᵗ) ⊑ B
open-fresh-ν⊑ {Σ = Σ} {B = B} wfΣ p⊢ =
  cong-⊢⊑ refl (open-renᵗ-suc B (｀ (length Σ)))
    (open-fresh-ν⊑-prefix {Φ = []} wfΣ p⊢)

subst-var-plain-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ X m} →
  StoreWf Δ Ψ Σ →
  (Φ ++ X⊑X ∷ extend-X⊑X Δ []) ∋ X ∶ m →
  VarSubst (suc Ψ) (Φ ++ extend-X⊑X Δ [])
    (substVarFrom (length Φ) (｀ (length Σ)) X) m
subst-var-plain-prefix {Φ = []} wfΣ here =
  ⊢α-⊑-α (wfSeal (len<suc-StoreWf wfΣ))
subst-var-plain-prefix {Ψ = Ψ} {Φ = []} wfΣ (there x∈) =
  plain-var-subst {Ψ = suc Ψ} x∈
subst-var-plain-prefix {Φ = X⊑X ∷ Φ} wfΣ here = ⊢X-⊑-X here
subst-var-plain-prefix {Φ = X⊑X ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-plain-prefix {Φ = Φ} wfΣ x∈)
subst-var-plain-prefix {Φ = X⊑★ ∷ Φ} wfΣ here = ⊢X-⊑-★ here
subst-var-plain-prefix {Φ = X⊑★ ∷ Φ} wfΣ (there x∈) =
  wk-VarSubst (subst-var-plain-prefix {Φ = Φ} wfΣ x∈)

substWf-plain-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ} →
  StoreWf Δ Ψ Σ →
  TySubstWf
    (length (Φ ++ X⊑X ∷ extend-X⊑X Δ []))
    (length (Φ ++ extend-X⊑X Δ []))
    (suc Ψ)
    (substVarFrom (length Φ) (｀ (length Σ)))
substWf-plain-prefix {Φ = Φ} wfΣ X<len =
  varSubst-wf
    (subst-var-plain-prefix {Φ = Φ} wfΣ (proj₂ (lookup-mode _ X<len)))

open-fresh-∀⊑-prefix :
  ∀ {Δ Ψ}{Σ : Store}{Φ : VarPrecCtx}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (Φ ++ X⊑X ∷ extend-X⊑X Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ (Φ ++ extend-X⊑X Δ []) ⊢
    substAt⊑ (length Φ) (｀ (length Σ)) p ⦂
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) A ⊑
    substᵗ (substVarFrom (length Φ) (｀ (length Σ))) B
open-fresh-∀⊑-prefix wfΣ ⊢★-⊑-★ = ⊢★-⊑-★
open-fresh-∀⊑-prefix wfΣ (⊢X-⊑-★ xν) =
  subst-var-plain-prefix wfΣ xν
open-fresh-∀⊑-prefix wfΣ (⊢A-⊑-★ g p⊢) =
  ⊢A-⊑-★ (substᵗ-ground _ g) (open-fresh-∀⊑-prefix wfΣ p⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊢X-⊑-X x∈) =
  subst-var-plain-prefix {Φ = Φ} wfΣ x∈
open-fresh-∀⊑-prefix wfΣ (⊢α-⊑-α (wfSeal α<Ψ)) =
  ⊢α-⊑-α (wfSeal (<-≤-trans α<Ψ (n≤1+n _)))
open-fresh-∀⊑-prefix wfΣ ⊢ι-⊑-ι = ⊢ι-⊑-ι
open-fresh-∀⊑-prefix wfΣ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) =
  ⊢A⇒B-⊑-A′⇒B′ (open-fresh-∀⊑-prefix wfΣ p⊢)
       (open-fresh-∀⊑-prefix wfΣ q⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-∀B p⊢) =
  ⊢∀A-⊑-∀B (open-fresh-∀⊑-prefix {Φ = X⊑X ∷ Φ} wfΣ p⊢)
open-fresh-∀⊑-prefix {Φ = Φ} wfΣ (⊢∀A-⊑-B {A = A} {B = B} wfB p⊢) =
  ⊢∀A-⊑-B
    (substᵗ-preserves-WfTy
      (WfTy-weakenˢ wfB (n≤1+n _))
      (substWf-plain-prefix {Φ = Φ} wfΣ))
    (cong-⊢⊑
      refl
      (substᵗ-suc-renameᵗ-suc
        (substVarFrom (length Φ) (｀ _))
        B)
      (open-fresh-∀⊑-prefix {Φ = X⊑★ ∷ Φ} wfΣ p⊢))

open-fresh-∀⊑ :
  ∀ {Δ Ψ}{Σ : Store}{A B : Ty}{p : Imp} →
  StoreWf Δ Ψ Σ →
  Ψ ∣ (X⊑X ∷ extend-X⊑X Δ []) ⊢ p ⦂ A ⊑ B →
  suc Ψ ∣ extend-X⊑X Δ [] ⊢ p [ ｀ (length Σ) ]⊑ ⦂
    A [ ｀ (length Σ) ]ᵗ ⊑ B [ ｀ (length Σ) ]ᵗ
open-fresh-∀⊑ wfΣ p⊢ =
  open-fresh-∀⊑-prefix {Φ = []} wfΣ p⊢

------------------------------------------------------------------------
-- Context imprecision for transitivity
------------------------------------------------------------------------

data ModeLe : VarPrec → VarPrec → Set where
  X⊑X≤X⊑X : ModeLe X⊑X X⊑X
  X⊑X≤ν : ModeLe X⊑X X⊑★
  ν≤ν : ModeLe X⊑★ X⊑★

infix 4 _≤ᵢ_
data _≤ᵢ_ : VarPrecCtx → VarPrecCtx → Set where
  []≤ᵢ : [] ≤ᵢ []
  _∷≤ᵢ_ : ∀ {m m′ Γ Γ′} →
    ModeLe m m′ →
    Γ ≤ᵢ Γ′ →
    (m ∷ Γ) ≤ᵢ (m′ ∷ Γ′)

≤ᵢ-refl : ∀ {Γ} → Γ ≤ᵢ Γ
≤ᵢ-refl {Γ = []} = []≤ᵢ
≤ᵢ-refl {Γ = X⊑X ∷ Γ} = X⊑X≤X⊑X ∷≤ᵢ ≤ᵢ-refl
≤ᵢ-refl {Γ = X⊑★ ∷ Γ} = ν≤ν ∷≤ᵢ ≤ᵢ-refl

≤ᵢ-length :
  ∀ {Γ Γ′} →
  Γ ≤ᵢ Γ′ →
  length Γ ≡ length Γ′
≤ᵢ-length []≤ᵢ = refl
≤ᵢ-length (m≤m′ ∷≤ᵢ Γ≤Γ′) = cong suc (≤ᵢ-length Γ≤Γ′)

≤ᵢ-ν-lookup :
  ∀ {Γ Γ′ X} →
  Γ ≤ᵢ Γ′ →
  Γ ∋ X ∶ X⊑★ →
  Γ′ ∋ X ∶ X⊑★
≤ᵢ-ν-lookup (ν≤ν ∷≤ᵢ Γ≤Γ′) here = here
≤ᵢ-ν-lookup (m≤m′ ∷≤ᵢ Γ≤Γ′) (there xν) =
  there (≤ᵢ-ν-lookup Γ≤Γ′ xν)

wf-length-cast :
  ∀ {Ψ Γ Γ′ A} →
  Γ ≤ᵢ Γ′ →
  WfTy (length Γ) Ψ A →
  WfTy (length Γ′) Ψ A
wf-length-cast Γ≤Γ′ wfA =
  subst (λ Δ → WfTy Δ _ _) (≤ᵢ-length Γ≤Γ′) wfA

------------------------------------------------------------------------
-- Occurrence inversion for X⊑X variables
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

occurs-⇑ᵗ-suc :
  ∀ X A →
  occurs (suc X) (⇑ᵗ A) ≡ occurs X A
occurs-⇑ᵗ-suc X A = occurs-raise zero X A

plain-target-occurs-source :
  ∀ {Ψ Γ X A B p} →
  Γ ∋ X ∶ X⊑X →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  occurs X B ≡ true →
  occurs X A ≡ true
plain-target-occurs-source x∈ ⊢★-⊑-★ ()
plain-target-occurs-source x∈ (⊢X-⊑-★ xν) ()
plain-target-occurs-source x∈ (⊢A-⊑-★ g p⊢) ()
plain-target-occurs-source x∈ (⊢X-⊑-X wfY) occ = occ
plain-target-occurs-source x∈ (⊢α-⊑-α wfα) ()
plain-target-occurs-source x∈ ⊢ι-⊑-ι ()
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    with occurs X A′ in occA′ | occurs X A in occA
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | true | true = refl
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | true | false =
  ⊥-elim (false≢true
    (trans (sym occA) (plain-target-occurs-source x∈ p⊢ occA′)))
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | false | true = refl
plain-target-occurs-source {X = X} x∈
    (⊢A⇒B-⊑-A′⇒B′ {A = A} {A′ = A′} {B = B} {B′ = B′} p⊢ q⊢) occ
    | false | false =
  plain-target-occurs-source x∈ q⊢ occ
plain-target-occurs-source x∈ (⊢∀A-⊑-∀B p⊢) occ =
  plain-target-occurs-source (there x∈) p⊢ occ
plain-target-occurs-source {X = X} x∈ (⊢∀A-⊑-B {B = B} wfB p⊢) occB =
  plain-target-occurs-source (there x∈) p⊢
    (trans (occurs-⇑ᵗ-suc X B) occB)

------------------------------------------------------------------------
-- Transport across plain-to-ν context changes
------------------------------------------------------------------------

change-plain-to-ν-ν∋ :
  ∀ {Δ Φ X} →
  (Φ ++ (X⊑X ∷ extend-X⊑X Δ [])) ∋ X ∶ X⊑★ →
  (Φ ++ (X⊑★ ∷ extend-X⊑X Δ [])) ∋ X ∶ X⊑★
change-plain-to-ν-ν∋ {Φ = []} {X = zero} ()
change-plain-to-ν-ν∋ {Φ = []} {X = suc X} (there x∈) = there x∈
change-plain-to-ν-ν∋ {Φ = X⊑X ∷ Φ} {X = zero} ()
change-plain-to-ν-ν∋ {Φ = X⊑★ ∷ Φ} {X = zero} here = here
change-plain-to-ν-ν∋ {Φ = m ∷ Φ} {X = suc X} (there x∈) =
  there (change-plain-to-ν-ν∋ {Φ = Φ} x∈)

change-plain-to-ν-raised∋ :
  ∀ {Δ Φ X m} →
  (Φ ++ (X⊑X ∷ extend-X⊑X Δ [])) ∋
    raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ (X⊑★ ∷ extend-X⊑X Δ [])) ∋
    raiseVarFrom (length Φ) X ∶ m
change-plain-to-ν-raised∋ {Φ = []} (there x∈) = there x∈
change-plain-to-ν-raised∋ {Φ = m₀ ∷ Φ} {X = zero} here = here
change-plain-to-ν-raised∋ {Φ = m₀ ∷ Φ} {X = suc X} (there x∈) =
  there (change-plain-to-ν-raised∋ {Φ = Φ} {X = X} x∈)

length-plain-to-ν :
  ∀ Δ (Φ : VarPrecCtx) →
  length (Φ ++ (X⊑X ∷ extend-X⊑X Δ [])) ≡
  length (Φ ++ (X⊑★ ∷ extend-X⊑X Δ []))
length-plain-to-ν Δ [] = refl
length-plain-to-ν Δ (m ∷ Φ) = cong suc (length-plain-to-ν Δ Φ)

plain-to-ν-raised-at-⊑ :
  ∀ {Δ Φ A B p} →
  0 ∣ Φ ++ (X⊑X ∷ extend-X⊑X Δ []) ⊢ p ⦂ A ⊑
    renameᵗ (raiseVarFrom (length Φ)) B →
  Σ[ q ∈ Imp ]
    0 ∣ Φ ++ (X⊑★ ∷ extend-X⊑X Δ []) ⊢ q ⦂ A ⊑
      renameᵗ (raiseVarFrom (length Φ)) B
plain-to-ν-raised-at-⊑ {B = ★} ⊢★-⊑-★ = id★ , ⊢★-⊑-★
plain-to-ν-raised-at-⊑ {B = ★} (⊢X-⊑-★ xν) =
  ‵ _ ! , ⊢X-⊑-★ (change-plain-to-ν-ν∋ xν)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = ★} (⊢A-⊑-★ {G = G} g p⊢)
    with plain-to-ν-raised-at-⊑ {Φ = Φ} {B = G}
      (cong-⊢⊑ refl (sym (renameᵗ-ground-id g)) p⊢)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = ★} (⊢A-⊑-★ {G = G} g p⊢)
    | q , q⊢ =
  q ! , ⊢A-⊑-★ g (cong-⊢⊑ refl (renameᵗ-ground-id g) q⊢)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = ＇ X} (⊢X-⊑-X x∈) =
  idₓ (raiseVarFrom (length Φ) X) ,
  ⊢X-⊑-X (change-plain-to-ν-raised∋ {Φ = Φ} x∈)
plain-to-ν-raised-at-⊑ {Δ = Δ} {Φ = Φ} {B = ｀ α} (⊢α-⊑-α wfα) =
  idₛ α ,
  ⊢α-⊑-α (subst (λ n → WfTy n 0 (｀ α)) (length-plain-to-ν Δ Φ) wfα)
plain-to-ν-raised-at-⊑ {B = ‵ ι} ⊢ι-⊑-ι = idι ι , ⊢ι-⊑-ι
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = A ⇒ B} (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
    with plain-to-ν-raised-at-⊑ {Φ = Φ} {B = A} p⊢
       | plain-to-ν-raised-at-⊑ {Φ = Φ} {B = B} q⊢
plain-to-ν-raised-at-⊑ {B = A ⇒ B} (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
    | p , p⊢′ | q , q⊢′ =
  p ↦ q , ⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = `∀ B} (⊢∀A-⊑-∀B p⊢)
    with plain-to-ν-raised-at-⊑ {Φ = X⊑X ∷ Φ} {B = B}
      (cong-⊢⊑ refl (rename-raise-ext (length Φ) B) p⊢)
plain-to-ν-raised-at-⊑ {Φ = Φ} {B = `∀ B} (⊢∀A-⊑-∀B p⊢)
    | q , q⊢ =
  ‵∀ q ,
  cong-⊢⊑ refl (cong `∀ (sym (rename-raise-ext (length Φ) B)))
    (⊢∀A-⊑-∀B q⊢)
plain-to-ν-raised-at-⊑ {Δ = Δ} {Φ = Φ} {B = B}
    (⊢∀A-⊑-B {A = A} wfB p⊢)
    with plain-to-ν-raised-at-⊑ {Φ = X⊑★ ∷ Φ} {B = ⇑ᵗ B}
      (cong-⊢⊑ refl (sym (rename-raise-⇑ᵗ (length Φ) B)) p⊢)
plain-to-ν-raised-at-⊑ {Δ = Δ} {Φ = Φ} {B = B}
    (⊢∀A-⊑-B {A = A} wfB p⊢)
    | q , q⊢ =
  ν q ,
  ⊢∀A-⊑-B
    (subst (λ n → WfTy n 0 (renameᵗ (raiseVarFrom (length Φ)) B))
      (length-plain-to-ν Δ Φ) wfB)
    (cong-⊢⊑ refl (rename-raise-⇑ᵗ (length Φ) B) q⊢)

plain-to-ν-raised-⊑ :
  ∀ {Δ A B p} →
  0 ∣ X⊑X ∷ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ ⇑ᵗ B →
  Σ[ q ∈ Imp ] 0 ∣ X⊑★ ∷ extend-X⊑X Δ [] ⊢ q ⦂ A ⊑ ⇑ᵗ B
plain-to-ν-raised-⊑ p⊢ = plain-to-ν-raised-at-⊑ {Φ = []} p⊢

mutual
  transport-to-star-⊑ :
    ∀ {Ψ Γ Γ′ A p} →
    Γ ≤ᵢ Γ′ →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ ★ →
    Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ ★
  transport-to-star-⊑ Γ≤Γ′ ⊢★-⊑-★ = id★ , ⊢★-⊑-★
  transport-to-star-⊑ Γ≤Γ′ (⊢X-⊑-★ xν) =
    _ , ⊢X-⊑-★ (≤ᵢ-ν-lookup Γ≤Γ′ xν)
  transport-to-star-⊑ Γ≤Γ′ (⊢A-⊑-★ g p⊢)
      with transport-to-ground-⊑ Γ≤Γ′ g p⊢
  transport-to-star-⊑ Γ≤Γ′ (⊢A-⊑-★ g p⊢) | r , r⊢ =
    r ! , ⊢A-⊑-★ g r⊢
  transport-to-star-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = ★} wf★ p⊢)
      with transport-to-star-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢
  transport-to-star-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = ★} wf★ p⊢)
      | r , r⊢ =
    ν r , ⊢∀A-⊑-B (wf-length-cast Γ≤Γ′ wf★) r⊢

  transport-to-ground-⊑ :
    ∀ {Ψ Γ Γ′ A G p} →
    Γ ≤ᵢ Γ′ →
    Ground G →
    Ψ ∣ Γ ⊢ p ⦂ A ⊑ G →
    Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ G
  transport-to-ground-⊑ Γ≤Γ′ (｀ α) (⊢α-⊑-α wfα) =
    idₛ α , ⊢α-⊑-α (wf-length-cast Γ≤Γ′ wfα)
  transport-to-ground-⊑ Γ≤Γ′ (‵ ι) ⊢ι-⊑-ι =
    idι ι , ⊢ι-⊑-ι
  transport-to-ground-⊑ Γ≤Γ′ ★⇒★ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
      with transport-to-star-⊑ Γ≤Γ′ p⊢
         | transport-to-star-⊑ Γ≤Γ′ q⊢
  transport-to-ground-⊑ Γ≤Γ′ ★⇒★ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢)
      | p′ , p′⊢ | q′ , q′⊢ =
    p′ ↦ q′ , ⊢A⇒B-⊑-A′⇒B′ p′⊢ q′⊢
  transport-to-ground-⊑ Γ≤Γ′ g (⊢∀A-⊑-B {B = B} wfB p⊢)
      with transport-to-ground-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) (renameᵗ-ground suc g) p⊢
  transport-to-ground-⊑ Γ≤Γ′ g (⊢∀A-⊑-B {B = B} wfB p⊢)
      | r , r⊢ =
    ν r , ⊢∀A-⊑-B (wf-length-cast Γ≤Γ′ wfB) r⊢

------------------------------------------------------------------------
-- Full transitivity
------------------------------------------------------------------------

trans-ctx-⊑ :
  ∀ {Ψ Γ Γ′ A B C p q} →
  Γ ≤ᵢ Γ′ →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ′ ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ C
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = B} wfB p⊢) q⊢
    with trans-ctx-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢ (wkImpAt {Φ = []} q⊢)
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-B {B = B} wfB p⊢) q⊢
    | r , r⊢ =
  ν r , ⊢∀A-⊑-B (⊑-tgt-wf q⊢) r⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ ⊢★-⊑-★ = transport-to-star-⊑ Γ≤Γ′ p⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢X-⊑-★ xν) =
  trans-to-starν Γ≤Γ′ p⊢ xν
  where
    trans-to-starν :
      ∀ {Ψ Γ Γ′ A X p} →
      Γ ≤ᵢ Γ′ →
      Ψ ∣ Γ ⊢ p ⦂ A ⊑ ＇ X →
      Γ′ ∋ X ∶ X⊑★ →
      Σ[ r ∈ Imp ] Ψ ∣ Γ′ ⊢ r ⦂ A ⊑ ★
    trans-to-starν Γ≤Γ′ (⊢X-⊑-X wfX) xν = ‵ _ ! , ⊢X-⊑-★ xν
    trans-to-starν Γ≤Γ′ (⊢∀A-⊑-B {B = ＇ X} wfB p⊢) xν
        with trans-ctx-⊑ (ν≤ν ∷≤ᵢ Γ≤Γ′) p⊢ (wkImpAt {Φ = []} (⊢X-⊑-★ xν))
    trans-to-starν Γ≤Γ′ (⊢∀A-⊑-B {B = ＇ X} wfB p⊢) xν
        | r , r⊢ =
      ν r , ⊢∀A-⊑-B wf★ r⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢A-⊑-★ g q⊢)
    with trans-ctx-⊑ Γ≤Γ′ p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢A-⊑-★ g q⊢) | r , r⊢ =
  r ! , ⊢A-⊑-★ g r⊢
trans-ctx-⊑ Γ≤Γ′ (⊢X-⊑-X wfX) (⊢X-⊑-X wfX′) =
  _ , ⊢X-⊑-X wfX′
trans-ctx-⊑ Γ≤Γ′ p⊢ (⊢α-⊑-α wfα) =
  transport-to-ground-⊑ Γ≤Γ′ (｀ _) p⊢
trans-ctx-⊑ Γ≤Γ′ p⊢ ⊢ι-⊑-ι =
  transport-to-ground-⊑ Γ≤Γ′ (‵ _) p⊢
trans-ctx-⊑ Γ≤Γ′ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
    with trans-ctx-⊑ Γ≤Γ′ p⊢ p⊢′
       | trans-ctx-⊑ Γ≤Γ′ q⊢ q⊢′
trans-ctx-⊑ Γ≤Γ′ (⊢A⇒B-⊑-A′⇒B′ p⊢ q⊢) (⊢A⇒B-⊑-A′⇒B′ p⊢′ q⊢′)
    | r₁ , r₁⊢ | r₂ , r₂⊢ =
  r₁ ↦ r₂ , ⊢A⇒B-⊑-A′⇒B′ r₁⊢ r₂⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-∀B q⊢)
    with trans-ctx-⊑ (X⊑X≤X⊑X ∷≤ᵢ Γ≤Γ′) p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-∀B q⊢) | r , r⊢ =
  ‵∀ r , ⊢∀A-⊑-∀B r⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-B {B = B} wfB q⊢)
    with trans-ctx-⊑ (X⊑X≤ν ∷≤ᵢ Γ≤Γ′) p⊢ q⊢
trans-ctx-⊑ Γ≤Γ′ (⊢∀A-⊑-∀B p⊢) (⊢∀A-⊑-B {B = B} wfB q⊢)
    | r , r⊢ =
  ν r , ⊢∀A-⊑-B wfB r⊢

⊑-trans :
  ∀ {Ψ Γ A B C p q} →
  Ψ ∣ Γ ⊢ p ⦂ A ⊑ B →
  Ψ ∣ Γ ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] Ψ ∣ Γ ⊢ r ⦂ A ⊑ C
⊑-trans = trans-ctx-⊑ ≤ᵢ-refl

trans-⊑-extend-X⊑X :
  ∀ {Δ A B C p q} →
  0 ∣ extend-X⊑X Δ [] ⊢ p ⦂ A ⊑ B →
  0 ∣ extend-X⊑X Δ [] ⊢ q ⦂ B ⊑ C →
  Σ[ r ∈ Imp ] 0 ∣ extend-X⊑X Δ [] ⊢ r ⦂ A ⊑ C
trans-⊑-extend-X⊑X = ⊑-trans
