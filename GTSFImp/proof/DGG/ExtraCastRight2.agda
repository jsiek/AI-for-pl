module proof.DGG.ExtraCastRight2 where

-- File Charter:
--   * Ports the extra-cast-on-the-right development to the version-2
--     cast-term imprecision relation, in stages.
--   * Stage 1: the statements of extra-cast-right and its inst
--     catch-up companion as Set-level definitions, together with the
--     world-extension interface their conclusions need.  Compared with
--     version 1 the statement carries no transport function for the
--     source type: A : Ty Δᴸ is untouched by target-side allocation,
--     and only the world and the target types evolve.
--   * Stage 2: the right-injection inversion lemma, proved for spine
--     values (values built from constants, lambdas, type abstractions,
--     and inert casts).  Reveal- and conceal-wrapped values are the
--     open frontier: inverting through a wrapper must reconstruct the
--     pre-conversion obligation from the post-conversion one, which
--     the free-q wrapper rules do not support locally; see SpineValue.
--   * Version-2 pay-offs visible here: no renaming wrapper around the
--     relation, the Λ⊑² case recurses with the target data unchanged,
--     and the ground lemmas of proof.ImprecisionConsistency apply
--     directly to world-embedded obligations.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; keep; skip; toRenameᵗ;
   _!; ∀ᶜ_; gen_; inst_)
import Consistency as C
open import Conversion using (Conv↑; Conv↓; `∀↑_; `∀↓_)
open import Imprecision
open import Primitives using (Const)
open import CastTerms
open import Reduction
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; ηᴸʷ; ηᴿʷ; impEnvʷ; sourceStoreʷ; targetStoreʷ; embedᴿ;
   _⊑ᵂ⟨_⟩_; CtxImp; ctx-imp; _∣_⊢²_⊑_∶_)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; source-occurs-target; rename-occurs;
   ext-injective; toRenameᵗ-injective; nonstar-from-≢★)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using (toRename-keep-eq)

------------------------------------------------------------------------
-- Target polymorphic value views (for the inst catch-up statement)
------------------------------------------------------------------------

data AllValueView {Δ : TyCtx} (V : Term Δ) : Set where
  allv-Λ : ∀ {W}
    → Value W
    → V ≡ Λ W
    → AllValueView V

  allv-∀ : ∀ {μ : Env∼ Δ} {W} {A B : Ty (suc Δ)}
      {c : C.extᵐ μ ⊢ A ∼ B}
    → Value W
    → V ≡ W ⟨ ∀ᶜ c ⟩
    → AllValueView V

  allv-gen : ∀ {μ : Env∼ Δ} {W} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : C.genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    → Value W
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → V ≡ W ⟨ (gen c) A≢★ ⟩
    → AllValueView V

  allv-reveal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↑ (suc Δ) A B}
    → Value W
    → V ≡ W ↑ `∀↑ c
    → AllValueView V

  allv-conceal : ∀ {W} {A B : Ty (suc Δ)} {c : Conv↓ (suc Δ) A B}
    → Value W
    → V ≡ W ↓ `∀↓ c
    → AllValueView V

------------------------------------------------------------------------
-- Stage 1: statements
------------------------------------------------------------------------

-- A right-side world extension: the source store is untouched, the
-- target store follows the machine's store changes, and every type
-- obligation transports with the change.

record WorldExtendᴿ {Δᴸ Δᴿ Δᴿ′ Δ Δ′} (χs : StoreChanges Δᴿ Δᴿ′)
    (W : World Δᴸ Δᴿ Δ) (W′ : World Δᴸ Δᴿ′ Δ′) : Set where
  field
    sourceStore-kept : sourceStoreʷ W′ ≡ sourceStoreʷ W
    targetStore-follows : targetStoreʷ W′ ≡ (χs ▶ˢ targetStoreʷ W)
    transport⊑ᵂ : ∀ {A : Ty Δᴸ} {C : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ C
      → A ⊑ᵂ⟨ W′ ⟩ (χs ▶ᵗ C)

open WorldExtendᴿ public

mapCtxᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′} {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → WorldExtendᴿ χs W W′
  → CtxImp W
  → CtxImp W′
mapCtxᴿ ext [] = []
mapCtxᴿ {χs = χs} ext (ctx-imp A B p ∷ γ) =
  ctx-imp A (χs ▶ᵗ B) (transport⊑ᵂ ext p) ∷ mapCtxᴿ ext γ

-- Extra cast on the right: if related values face an extra target
-- cast, the target alone reduces to a value in an extended world that
-- still relates them.

ExtraCastRight² : Set
ExtraCastRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ c′ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))

-- The inst catch-up companion: instantiating a polymorphic target
-- value allocates on the right and reduces to a value related in the
-- extended world.

InstCatchupRight² : Set
InstCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : C.instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
        × (W′ ∣ mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶ transport⊑ᵂ ext q))

------------------------------------------------------------------------
-- Stage 2: helpers
------------------------------------------------------------------------

renameᵗ-skip-eq : ∀ {Δᴿ Δ} (η : Δᴿ ↪ᵗ Δ) (B : Ty Δᴿ)
  → renameᵗ (toRenameᵗ (skip η)) B ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) B)
renameᵗ-skip-eq η B =
  trans (renameᵗ-cong B (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc B))

-- The ∀⊑ view of a world obligation for `∀ A against B is exactly a
-- premise for the left-only lifted world: the instᵐ environment is the
-- lifted world's environment, and B's embedding gains one shift.

liftWorldLeft-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
  → instᵐ (impEnvʷ W)
      ⊢ renameᵗ (extᵗ (toRenameᵗ (ηᴸʷ W))) A ⊑ ⇑ᵗ (embedᴿ W B)
  → A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B
liftWorldLeft-⊑ᵂ {W = W} {A = A} {B = B} body =
  subst≡
    (λ T → extendᵐ X⊑★ (impEnvʷ W) ⊢
       T ⊑ renameᵗ (toRenameᵗ (skip (ηᴿʷ W))) B)
    (sym (renameᵗ-cong A (toRename-keep-eq (ηᴸʷ W))))
    (subst≡
      (λ T → extendᵐ X⊑★ (impEnvʷ W) ⊢
         renameᵗ (extᵗ (toRenameᵗ (ηᴸʷ W))) A ⊑ T)
      (sym (renameᵗ-skip-eq (ηᴿʷ W) B))
      body)

------------------------------------------------------------------------
-- Stage 2: right-injection inversion for spine values
------------------------------------------------------------------------

-- Values whose spine contains no reveal or conceal wrapper.  Inverting
-- through a wrapper must rebuild the pre-conversion obligation from
-- the post-conversion one; with the free-q wrapper rules that needs
-- representation-substitution coherence the relation does not yet
-- record, so wrapped values are excluded here and left as the open
-- frontier.

data SpineValue {Δ : TyCtx} : Term Δ → Set where
  sv-ƛ : (N : Term Δ) → SpineValue (ƛ N)

  sv-Λ : ∀ {V} → SpineValue V → SpineValue (Λ V)

  sv-$ : (κ : Const) → SpineValue ($ κ)

  sv-cast : ∀ {V} {μ : Env∼ Δ} {A B : Ty Δ} {c : μ ⊢ A ∼ B}
    → SpineValue V → Inert c → SpineValue (V ⟨ c ⟩)

-- If a spine value is related to a tagged target value, the tag can be
-- peeled off the target at any obligation for the tag's ground type.

right-inj-inversion² : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ} {A : Ty Δᴸ} {H : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {gH : Ground H} {H∼★ : ν ⊢ H ∼★} {Hns : NonStar H}
    {cH : ν ⊢ H ∼ H}
    {p : A ⊑ᵂ⟨ W ⟩ ★}
  → SpineValue M
  → W ∣ γ ⊢² M ⊑ N ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩ ∶ p
  → (q : A ⊑ᵂ⟨ W ⟩ H)
  → W ∣ γ ⊢² M ⊑ N ∶ q

-- Target-only cast: the premise already carries the tag obligation.
right-inj-inversion² sv (CTI2.⊑cast² {p = p₀} c′ prem q₀) q =
  subst≡ (λ r → _ ∣ _ ⊢² _ ⊑ _ ∶ r) (PI.⊑-unique p₀ q) prem

-- Paired cast: keep the source cast as a source-only cast.
right-inj-inversion² sv (CTI2.cast⊑cast² c c′ prem q₀) q =
  CTI2.cast⊑² c prem q

-- Source-only cast around an injection value: no obligation matches.
right-inj-inversion² {gH = ＇ Y} (sv-cast sv inj)
  (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ‵ ι} (sv-cast sv inj)
  (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ★⇒★} (sv-cast sv inj)
  (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ∀★} (sv-cast sv inj)
  (CTI2.cast⊑² c prem q₀) ()

-- Source-only function cast: the premise components rebuild the
-- premise-level tag obligation.
right-inj-inversion² {gH = ★⇒★} (sv-cast sv fun)
    (CTI2.cast⊑² {p = ⇒⊑★ pA pB} c prem q₀) (⇒⊑⇒ qA qB) =
  CTI2.cast⊑² c
    (right-inj-inversion² sv prem (⇒⊑⇒ pA pB))
    (⇒⊑⇒ qA qB)
right-inj-inversion² {gH = ＇ Y} (sv-cast sv fun)
  (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ‵ ι} (sv-cast sv fun)
  (CTI2.cast⊑² c prem q₀) ()
right-inj-inversion² {gH = ∀★} (sv-cast sv fun)
  (CTI2.cast⊑² c prem q₀) ()

-- Source-only universal cast: chase the tag through the cast with the
-- embedded consistency evidence.
right-inj-inversion² {W = W} {gH = gH} (sv-cast sv (all {c = c₁}))
    (CTI2.cast⊑² {p = p₀} .(∀ᶜ c₁) prem q₀) q =
  CTI2.cast⊑² (∀ᶜ c₁)
    (right-inj-inversion² sv prem
      (ground-cast-source⊑ (C.renameGroundᵐ (ηᴿʷ W) gH) nonstar-∀
        (C.renameᵐᶜ (ηᴸʷ W) (∀ᶜ c₁)) p₀ q₀ q))
    q

-- Source-only generalization cast: same, with the gen tag's source.
right-inj-inversion² {W = W} {gH = gH} (sv-cast sv (genᵥ A≢★ safe))
    (CTI2.cast⊑² {p = p₀} c prem q₀) q =
  CTI2.cast⊑² c
    (right-inj-inversion² sv prem
      (ground-cast-source⊑ (C.renameGroundᵐ (ηᴿʷ W) gH)
        (C.renameNonStar (toRenameᵗ (ηᴸʷ W)) (nonstar-from-≢★ A≢★))
        (C.renameᵐᶜ (ηᴸʷ W) c) p₀ q₀ q))
    q

-- Type abstraction against a non-∀ ground: only the ∀⊑ view is
-- possible, and its body is exactly a left-only lifted premise.
right-inj-inversion² {W = W} {gH = ＇ Y} (sv-Λ sv)
    (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² sv prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ＇ Y} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ‵ ι} (sv-Λ sv)
    (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² sv prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ‵ ι} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ★⇒★} (sv-Λ sv)
    (CTI2.Λ⊑² {A = A₀} Anv z∈A liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv z∈A liftγ vV N⊢
    (right-inj-inversion² sv prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = ★ ⇒ ★} body))
    (∀⊑ Anv′ z∈A′ body)

-- Type abstraction against the ∀★ ground.  The Λ⊑² occurrence premise
-- exposes the body's head, which rules out bot-elim, refutes ∀⊑∀ by
-- occurrence preservation, and leaves the ∀⊑ rebuild.
right-inj-inversion² {gH = ∀★} (sv-Λ sv)
  (CTI2.Λ⊑² () var-∈ liftγ vV M′⊢ prem q₀) q
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-left z∈) liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV N⊢
    (right-inj-inversion² sv prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    (CTI2.Λ⊑² Anv (∈-fun-left z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-fun-left z∈))
... | ()
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    (CTI2.Λ⊑² {A = A₀} Anv (∈-fun-right z∉ z∈) liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV N⊢
    (right-inj-inversion² sv prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    (CTI2.Λ⊑² Anv (∈-fun-right z∉ z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-fun-right z∉ z∈))
... | ()
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    (CTI2.Λ⊑² {A = A₀} Anv (∈-all z∈) liftγ vV (⊢⟨⟩ N⊢ _) prem q₀)
    (∀⊑ Anv′ z∈A′ body) =
  CTI2.Λ⊑² Anv (∈-all z∈) liftγ vV N⊢
    (right-inj-inversion² sv prem
      (liftWorldLeft-⊑ᵂ {W = W} {A = A₀} {B = `∀ ★} body))
    (∀⊑ Anv′ z∈A′ body)
right-inj-inversion² {W = W} {gH = ∀★} (sv-Λ sv)
    (CTI2.Λ⊑² Anv (∈-all z∈) liftγ vV M′⊢ prem q₀)
    (∀⊑∀ qbody)
  with source-occurs-target refl qbody
         (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W)))
           (ext-injective (toRenameᵗ-injective (ηᴸʷ W)))
           (∈-all z∈))
... | ()

-- Wrapped values and type applications are not spine values.
right-inj-inversion² () (CTI2.reveal⊑² _ _ _ _ _) q
right-inj-inversion² () (CTI2.conceal⊑² _ _ _ _ _) q
right-inj-inversion² () (CTI2.•⊑² _ _ _ _) q
