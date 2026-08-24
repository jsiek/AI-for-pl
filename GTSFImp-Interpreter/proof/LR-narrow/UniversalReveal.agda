module proof.LR-narrow.UniversalReveal where

-- File Charter:
--   * Ingredients for the universal cases of the structural reveal and
--     conceal: the evaluator's step at a revealed or concealed universal
--     value, the fresh paired slot allocated by a type application, and
--     the body-level lifting laws for `replaceTy`.
--   * A type application of a revealed universal allocates and produces
--     two nested reveals: the old slot inside the body, then the freshly
--     allocated slot.

open import Data.Nat using (ℕ; zero; suc)
import Data.Fin as Fin
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (≤∧≢⇒<)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; `∀↑_; `∀↓_; replaceTy; 〖_,_↑_〗; makeConceal)
import Imprecision as I
open import Reduction
import Eval as E
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective; ty-all-injective)
open import Consistency using (toRenameᵗ; keep)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete)
open import proof.LR-narrow.BetaExpansion using (value-step-none)
open import proof.LR-narrow.RevealSteps using
  (reveal-all-value; conceal-all-value)
open import proof.LR-narrow.RevealLifting using
  (PairedSlot; paired-slot; renameᵗ-replaceTy)
open import proof.LR-narrow.SlotLifting using
  (slotXᴾ; slotXᴵ; slotRᴾ; slotRᴵ)
open import LR-narrow.World
open import LR-narrow.Atoms

------------------------------------------------------------------------
-- The evaluator steps a revealed or concealed universal value
------------------------------------------------------------------------

reveal-type-app-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {A : Ty Δ} {C B : Ty (suc Δ)} {V : Term Δ}
    (c : Conv↑ (suc Δ) C B)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ ((V ↑ `∀↑ c) ⦂∀ B [ A ]) ≡
        just (E.step-result (bind A)
          ((⇑ᵗᵐ V ⦂∀ bind A ▷ᵇ C [ ＇ Fin.zero ]) ↑ c
            ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
          (β-reveal-∀ vV′))
reveal-type-app-step-question {Σ = Σ} {A = A} {B = B} {V = V} c vV
    with E.step? Σ (V ↑ `∀↑ c)
       | value-step-none {Σ = Σ} {V = V ↑ `∀↑ c} (vV ↑ all)
reveal-type-app-step-question c vV | just _ | ()
reveal-type-app-step-question {Σ = Σ} {A = A} {B = B} {V = V} c vV
    | nothing | _ with reveal-all-value c vV
reveal-type-app-step-question {Σ = Σ} {A = A} {B = B} {V = V} c vV
    | nothing | _ | vV′ , value-eq rewrite value-eq with B ≟Ty B
reveal-type-app-step-question c vV
    | nothing | _ | vV′ , value-eq | yes refl = vV′ , refl
reveal-type-app-step-question c vV
    | nothing | _ | vV′ , value-eq | no B≢B with B≢B refl
reveal-type-app-step-question c vV
    | nothing | _ | vV′ , value-eq | no B≢B | ()

conceal-type-app-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {A : Ty Δ} {C B : Ty (suc Δ)} {V : Term Δ}
    (c : Conv↓ (suc Δ) C B)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ ((V ↓ `∀↓ c) ⦂∀ B [ A ]) ≡
        just (E.step-result (bind A)
          ((⇑ᵗᵐ V ⦂∀ bind A ▷ᵇ C [ ＇ Fin.zero ]) ↓ c
            ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
          (β-conceal-∀ vV′))
conceal-type-app-step-question {Σ = Σ} {A = A} {B = B} {V = V} c vV
    with E.step? Σ (V ↓ `∀↓ c)
       | value-step-none {Σ = Σ} {V = V ↓ `∀↓ c} (vV ↓ all)
conceal-type-app-step-question c vV | just _ | ()
conceal-type-app-step-question {Σ = Σ} {A = A} {B = B} {V = V} c vV
    | nothing | _ with conceal-all-value c vV
conceal-type-app-step-question {Σ = Σ} {A = A} {B = B} {V = V} c vV
    | nothing | _ | vV′ , value-eq rewrite value-eq with B ≟Ty B
conceal-type-app-step-question c vV
    | nothing | _ | vV′ , value-eq | yes refl = vV′ , refl
conceal-type-app-step-question c vV
    | nothing | _ | vV′ , value-eq | no B≢B with B≢B refl
conceal-type-app-step-question c vV
    | nothing | _ | vV′ , value-eq | no B≢B | ()

------------------------------------------------------------------------
-- The slot allocated by a paired type application
------------------------------------------------------------------------

fresh-slot : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (Rᴾ : Ty Δᴾ) (Rᴵ : Ty Δᴵ) (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → PairedSlot (pairedBindWorld W Rᴾ Rᴵ r)
fresh-slot W Rᴾ Rᴵ r = paired-slot Fin.zero
  (fresh-semantic-atom (core W) Rᴾ Rᴵ r) refl refl

fresh-slot-precise-variable : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (Rᴾ : Ty Δᴾ) (Rᴵ : Ty Δᴵ) (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → slotXᴾ (fresh-slot W Rᴾ Rᴵ r) ≡ Fin.zero
fresh-slot-precise-variable W Rᴾ Rᴵ r = refl

fresh-slot-precise-rep : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (Rᴾ : Ty Δᴾ) (Rᴵ : Ty Δᴵ) (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → slotRᴾ (fresh-slot W Rᴾ Rᴵ r) ≡ ⇑ᵗ Rᴾ
fresh-slot-precise-rep W Rᴾ Rᴵ r = refl

------------------------------------------------------------------------
-- Replacement under a binder commutes with future lifting
------------------------------------------------------------------------

shift-body-replace : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ) (B : Ty (suc Δ))
  → renameᵗ (extᵗ Fin.suc) (replaceTy (Fin.suc X) (⇑ᵗ R) B)
      ≡ replaceTy (Fin.suc (Fin.suc X)) (⇑ᵗ (⇑ᵗ R))
          (renameᵗ (extᵗ Fin.suc) B)
shift-body-replace X R B =
  trans (renameᵗ-replaceTy (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (Fin.suc X) (⇑ᵗ R) B)
    (cong (λ T → replaceTy (Fin.suc (Fin.suc X)) T
      (renameᵗ (extᵗ Fin.suc) B))
      (renameᵗ-shift Fin.suc R))

liftPreciseBody-replace : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᴾ) (R : Ty Δᴾ) (B : Ty (suc Δᴾ))
  → liftPreciseBody W≼W′ (replaceTy (Fin.suc X) (⇑ᵗ R) B)
      ≡ replaceTy (Fin.suc (liftPreciseVariable W≼W′ X))
          (⇑ᵗ (liftPreciseTy W≼W′ R)) (liftPreciseBody W≼W′ B)
liftPreciseBody-replace future-refl X R B = refl
liftPreciseBody-replace (future-paired W≼W′ r) X R B
    rewrite liftPreciseBody-replace W≼W′ X R B =
  shift-body-replace (liftPreciseVariable W≼W′ X)
    (liftPreciseTy W≼W′ R) (liftPreciseBody W≼W′ B)
liftPreciseBody-replace (future-precise W≼W′ r) X R B
    rewrite liftPreciseBody-replace W≼W′ X R B =
  shift-body-replace (liftPreciseVariable W≼W′ X)
    (liftPreciseTy W≼W′ R) (liftPreciseBody W≼W′ B)
liftPreciseBody-replace (future-imprecise W≼W′) X R B =
  liftPreciseBody-replace W≼W′ X R B

liftImpreciseBody-replace : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᴵ) (R : Ty Δᴵ) (B : Ty (suc Δᴵ))
  → liftImpreciseBody W≼W′ (replaceTy (Fin.suc X) (⇑ᵗ R) B)
      ≡ replaceTy (Fin.suc (liftImpreciseVariable W≼W′ X))
          (⇑ᵗ (liftImpreciseTy W≼W′ R)) (liftImpreciseBody W≼W′ B)
liftImpreciseBody-replace future-refl X R B = refl
liftImpreciseBody-replace (future-paired W≼W′ r) X R B
    rewrite liftImpreciseBody-replace W≼W′ X R B =
  shift-body-replace (liftImpreciseVariable W≼W′ X)
    (liftImpreciseTy W≼W′ R) (liftImpreciseBody W≼W′ B)
liftImpreciseBody-replace (future-precise W≼W′ r) X R B =
  liftImpreciseBody-replace W≼W′ X R B
liftImpreciseBody-replace (future-imprecise W≼W′) X R B
    rewrite liftImpreciseBody-replace W≼W′ X R B =
  shift-body-replace (liftImpreciseVariable W≼W′ X)
    (liftImpreciseTy W≼W′ R) (liftImpreciseBody W≼W′ B)

------------------------------------------------------------------------
-- Heads of a universal relation
------------------------------------------------------------------------

open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product using (proj₁; proj₂)
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.CastComposition using
  (map-computations-related)

universals-head : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ} {W : World Δᴾ Δᴵ Δᶜ}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ∀ {n : ℕ} (m : ℕ) → suc m ≤ n
  → UniversalsRelated W p Bᴾ Bᴵ n Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (s : liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ Bᴵ [ Rᴵ ]ᵗ)
  → ComputationsRelated W′
      (PostBindValueRelation (future-paired (future-refl {W = W′}) r) s)
      (suc m)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ liftImpreciseBody W≼W′ Bᴵ [ Rᴵ ])
      (liftPreciseTerm W≼W′ Vᴾ ⦂∀ liftPreciseBody W≼W′ Bᴾ [ Rᴾ ])
universals-head {W = W} {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc n} m (s≤s m≤n) universals
    with m ≟ℕ n
universals-head {n = suc n} .n (s≤s m≤n) universals | yes refl =
  proj₁ universals
universals-head {W = W} {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc n} m (s≤s m≤n) universals
    | no m≢n =
  universals-head {W = W} {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = n} m (≤∧≢⇒< m≤n m≢n) (proj₂ universals)

------------------------------------------------------------------------
-- A post-bind relation implies the plain future relation
------------------------------------------------------------------------

post-bind-weaken : ∀ {Δᴾ Δᴵ Δᶜ Δᴾᵇ Δᴵᵇ Δᶜᵇ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {bound : World Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    (W≼B : Future W bound)
    (q : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    {k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W (PostBindValueRelation W≼B q) k Mᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation q) k Mᴵ Mᴾ
post-bind-weaken W≼B q =
  map-computations-related (λ W′ W≼W′ related → proj₂ (proj₂ related))

------------------------------------------------------------------------
-- Embedding a body into the paired-bind center context
------------------------------------------------------------------------

embed-precise-bind-body : ∀ {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
    (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ) (B : Ty (suc Δᴾ))
  → embedPrecise (pairedBindCore W Aᴾ Aᴵ) B
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding W))) B
embed-precise-bind-body W Aᴾ Aᴵ B =
  renameᵗ-cong B (toRename-keep-eq (preciseEmbedding W))

embed-imprecise-bind-body : ∀ {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
    (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ) (B : Ty (suc Δᴵ))
  → embedImprecise (pairedBindCore W Aᴾ Aᴵ) B
      ≡ renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding W))) B
embed-imprecise-bind-body W Aᴾ Aᴵ B =
  renameᵗ-cong B (toRename-keep-eq (impreciseEmbedding W))

------------------------------------------------------------------------
-- Embedding commutes with future lifting at the body level
------------------------------------------------------------------------

embed-body-lift-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (B : Ty (suc Δᴾ))
  → renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W′))))
      (liftPreciseBody W≼W′ B)
    ≡ liftCenterBody W≼W′
        (renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W)))) B)
embed-body-lift-precise {W = W} {W′ = W′} W≼W′ B = ty-all-injective
  (trans (cong (embedPrecise (core W′))
      (sym (liftPreciseTy-universal W≼W′ B)))
    (trans (embedPrecise-lift W≼W′ (`∀ B))
      (liftCenterTy-universal W≼W′ _)))

embed-body-lift-imprecise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (B : Ty (suc Δᴵ))
  → renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding (core W′))))
      (liftImpreciseBody W≼W′ B)
    ≡ liftCenterBody W≼W′
        (renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding (core W)))) B)
embed-body-lift-imprecise {W = W} {W′ = W′} W≼W′ B = ty-all-injective
  (trans (cong (embedImprecise (core W′))
      (sym (liftImpreciseTy-universal W≼W′ B)))
    (trans (embedImprecise-lift W≼W′ (`∀ B))
      (liftCenterTy-universal W≼W′ _)))

embed-precise-precise-bind-body : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (B : Ty (suc Δᴾ))
  → embedPrecise (preciseBindCore W Aᴾ) B
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding W))) B
embed-precise-precise-bind-body W Aᴾ B =
  renameᵗ-cong B (toRename-keep-eq (preciseEmbedding W))

right-universals-head : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ} {W : World Δᴾ Δᴵ Δᶜ}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ∀ {n : ℕ} (m : ℕ) → suc m ≤ n
  → RightUniversalsRelated W p Bᴾ Bᴵ n Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′)
      (r : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (s : liftPreciseBody W≼W′ Bᴾ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
  → ComputationsRelated W′
      (PostBindValueRelation
        (future-precise (future-refl {W = W′}) r) s)
      (suc m)
      (liftImpreciseTerm W≼W′ Vᴵ)
      (liftPreciseTerm W≼W′ Vᴾ ⦂∀ liftPreciseBody W≼W′ Bᴾ [ Rᴾ ])
right-universals-head {W = W} {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc n} m (s≤s m≤n) universals
    with m ≟ℕ n
right-universals-head {n = suc n} .n (s≤s m≤n) universals
    | yes refl = proj₁ universals
right-universals-head {W = W} {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc n} m (s≤s m≤n) universals
    | no m≢n =
  right-universals-head {W = W} {p = p} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = n} m (≤∧≢⇒< m≤n m≢n)
    (proj₂ universals)
