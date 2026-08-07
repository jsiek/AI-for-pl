module proof.DGG.CenterCrossingProbe where

-- File Charter:
--   * This probe records the target-seal variable case blocked by the
--     center-crossing obstruction in bare right-injection inversion.
--   * The derivable call-site premise moves the target pivot `Y₀` from
--     center `a` to center `b`, with source variables parked at `a,b`.
--   * Any direct output for `Y₀ : ＇ Y₁` would force the sealed source
--     pivot `X₀` to cross the in-between parked source variable `X₁`;
--     order-preserving embeddings built from `keep`/`skip` forbid this.
--   * The refutation is the target-side companion to the
--     SourceStarCounterScratch/SourceStarRideCounterScratch lineage, now
--     captured permanently by SourceStarProbe.  Together they justify
--     keeping variable-target source-star/target-seal rides out of the
--     downstream chain interface.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using
  (TyStore; store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using
  (Env∼; X∼★; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ;
   id; _!)
open import Conversion using (seal)
open import CastTerms
import CastTerms as CTerms
open import Imprecision
open import Primitives using (κℕ)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open CTI2 using
  (World; world; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   rebase-at; same-runtime; store-rep-imp; ηᴸʷ; ηᴿʷ)

private
  X₀ : TyVar 2
  X₀ = Fin.zero

  X₁ : TyVar 2
  X₁ = Fin.suc Fin.zero

  Y₀ : TyVar 2
  Y₀ = Fin.zero

  Y₁ : TyVar 2
  Y₁ = Fin.suc Fin.zero

  a : TyVar 3
  a = Fin.zero

  b : TyVar 3
  b = Fin.suc Fin.zero

  c : TyVar 3
  c = Fin.suc (Fin.suc Fin.zero)

------------------------------------------------------------------------
-- Stores, embeddings, and worlds
------------------------------------------------------------------------

source-store : TyStore 2
source-store = store-bind (store-bind store-empty ★) ★

target-store : TyStore 2
target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

probe-μ : ImpEnv 3
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★
probe-μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

ηᴸ-ab : 2 ↪ᵗ 3
ηᴸ-ab = keep (keep (skip empty))

ηᴸ-ac : 2 ↪ᵗ 3
ηᴸ-ac = keep (skip (keep empty))

ηᴿ-ac : 2 ↪ᵗ 3
ηᴿ-ac = keep (skip (keep empty))

ηᴿ-bc : 2 ↪ᵗ 3
ηᴿ-bc = skip (keep (keep empty))

-- Placement table:
--
--             X₀  X₁  Y₀  Y₁
--   W          a   b   a   c
--   W′         a   b   b   c
--   Wᵖ         a   c   b   c

W : World 2 2 3
W = world ηᴸ-ab ηᴿ-ac probe-μ source-store target-store

W′ : World 2 2 3
W′ = world ηᴸ-ab ηᴿ-bc probe-μ source-store target-store

Wᵖ : World 2 2 3
Wᵖ = world ηᴸ-ac ηᴿ-bc probe-μ source-store target-store

------------------------------------------------------------------------
-- Store typing, casts, and terms
------------------------------------------------------------------------

X₀∈ : source-store ∋ X₀ ⦂ ★
X₀∈ = Z∋ refl

X₁∈ : source-store ∋ X₁ ⦂ ★
X₁∈ = S-bind∋ (Z∋ refl) refl

Y₀∈ : target-store ∋ Y₀ ⦂ ＇ Y₁
Y₀∈ = Z∋ refl

Y₁∈ : target-store ∋ Y₁ ⦂ ★
Y₁∈ = S-bind∋ (Z∋ refl) refl

source-env : Env∼ 2
source-env Fin.zero = X∼★
source-env (Fin.suc Fin.zero) = X∼★

target-env : Env∼ 2
target-env Fin.zero = X∼★
target-env (Fin.suc Fin.zero) = X∼★

X₁! : source-env ⊢ (＇ X₁) ∼ ★
X₁! = id (＇ X₁) !

Y₀id : target-env ⊢ (＇ Y₀) ∼ (＇ Y₀)
Y₀id = id (＇ Y₀)

Y₀! : target-env ⊢ (＇ Y₀) ∼ ★
Y₀! = Y₀id !

ℕ!ᴸ : source-env ⊢ (‵ `ℕ) ∼ ★
ℕ!ᴸ = id (‵ `ℕ) !

ℕ!ᴿ : target-env ⊢ (‵ `ℕ) ∼ ★
ℕ!ᴿ = id (‵ `ℕ) !

V₀ : Term 2
V₀ = ($ (κℕ 0)) ⟨ ℕ!ᴸ ⟩

V : Term 2
V = V₀ ↓ seal X₁ ★

U₀ : Term 2
U₀ = ($ (κℕ 0)) ⟨ ℕ!ᴿ ⟩

U : Term 2
U = U₀ ↓ seal Y₁ ★

------------------------------------------------------------------------
-- Rebase witnesses
------------------------------------------------------------------------

X₀-Y₀-rep : CTI2.StoreRepImp W X₀ Y₀
X₀-Y₀-rep = store-rep-imp ★⊑★

rb-outer : RebaseAt W′ W X₀ Y₀
rb-outer =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} X≢ → ⊥-elim (X≢ refl)
       ; {Fin.suc Fin.zero} X₁≢ → refl })
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl)
       ; {Fin.suc Fin.zero} Y₁≢ → refl })
    refl (λ moved → X₁ , refl) X₀-Y₀-rep

X₁-Y₀-rep : CTI2.StoreRepImp W′ X₁ Y₀
X₁-Y₀-rep = store-rep-imp ★⊑★

rb-target-input : RebaseAt Wᵖ W′ X₁ Y₀
rb-target-input =
  rebase-at (same-runtime refl refl)
    (λ { {Fin.zero} X₀≢ → refl
       ; {Fin.suc Fin.zero} X₁≢ → ⊥-elim (X₁≢ refl) })
    (λ { {Fin.zero} Y≢ → ⊥-elim (Y≢ refl)
       ; {Fin.suc Fin.zero} Y₁≢ → refl })
    refl (λ moved → ⊥-elim (moved refl)) X₁-Y₀-rep

X₁-Y₁-rep : CTI2.StoreRepImp Wᵖ X₁ Y₁
X₁-Y₁-rep = store-rep-imp ★⊑★

rb-inner : RebaseAt Wᵖ Wᵖ X₁ Y₁
rb-inner = CTI2.sameWorldRebaseAt refl X₁-Y₁-rep

------------------------------------------------------------------------
-- Checkpoint 1: the target-seal call-site premise is derivable
------------------------------------------------------------------------

p-inner : ＇ X₁ ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y₁
p-inner = X⊑X

p-input : ＇ X₁ ⊑ᵂ⟨ W′ ⟩ ＇ Y₀
p-input = X⊑X

q-out : ＇ X₀ ⊑ᵂ⟨ W ⟩ ＇ Y₀
q-out = X⊑X

base² : Wᵖ ∣ [] ⊢² V₀ ⊑ U₀ ∶ ★⊑★
base² =
  CTI2.cast⊑cast² ℕ!ᴸ ℕ!ᴿ
    (CTI2.κ⊑κ² (κℕ 0) ι⊑ι) ★⊑★

inner² : Wᵖ ∣ [] ⊢² V ⊑ U ∶ p-inner
inner² =
  CTI2.conceal⊑conceal² (λ Z eq → eq) rb-inner CTI2.same-[]
    (CTI2.⊢↓-sealˣ X₁∈) (CTI2.⊢↓-sealˣ Y₁∈) base² p-inner

input-target-seal-variable :
  W′ ∣ [] ⊢² V ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ p-input
input-target-seal-variable =
  CTI2.⊑conceal² (λ Z eq → eq) (CTI2.rebase-varᴿ rb-target-input)
    CTI2.same-[] (CTI2.⊢↓-sealˣ Y₀∈) inner² p-input

source-spine : ECR.SpineValue V
source-spine =
  ECR.sv-seal (ECR.sv-cast (ECR.sv-$ (κℕ 0)) CTerms.inj)

inert-X₁! : Inert X₁!
inert-X₁! = CTerms.inj

target-base-value : Value U₀
target-base-value = CTerms.$ (κℕ 0) CTerms.《 CTerms.inj 》

target-value : Value U
target-value =
  target-base-value CTerms.↓ (CTerms.seal {X = Y₁} {R = ★})

target-outer-value : Value (U ↓ seal Y₀ (＇ Y₁))
target-outer-value =
  target-value CTerms.↓ (CTerms.seal {X = Y₀} {R = ＇ Y₁})

source-outer-spine :
  ECR.SpineValue ((V ⟨ X₁! ⟩) ↓ seal X₀ ★)
source-outer-spine =
  ECR.sv-seal (ECR.sv-cast source-spine inert-X₁!)

q-star : ＇ X₀ ⊑ᵂ⟨ W ⟩ ★
q-star = X⊑★ refl

right-inj-premise :
  W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
    ⊑ (U ↓ seal Y₀ (＇ Y₁)) ⟨ Y₀! ⟩ ∶ q-star
right-inj-premise =
  CTI2.conceal⊑² (λ Z eq → eq) (CTI2.rebase-varᴸ rb-outer)
    CTI2.same-[] (CTI2.⊢↓-sealˣ X₀∈)
    (CTI2.cast⊑cast² X₁! Y₀! input-target-seal-variable ★⊑★)
    q-star

------------------------------------------------------------------------
-- Checkpoint 2: the target-seal variable output is empty
------------------------------------------------------------------------

private
  two≢zero : c ≢ a
  two≢zero ()

  one≢zero : b ≢ a
  one≢zero ()

  one≢two : b ≢ c
  one≢two ()

  X₁≢X₀ : X₁ ≢ X₀
  X₁≢X₀ ()

  Y₁≢Y₀ : Y₁ ≢ Y₀
  Y₁≢Y₀ ()

  W-wf : CTI2.WFWorld W
  W-wf Fin.zero ()
  W-wf (Fin.suc Fin.zero) ()

call-site-ra′-is-rb-outer :
  ECR.seal-rebase-target (CTI2.rebase-varᴸ rb-outer) q-out
    ≡ rb-outer
call-site-ra′-is-rb-outer = refl

call-site-ra′-moves-target :
  toRenameᵗ (ηᴿʷ W′) Y₀ ≢ toRenameᵗ (ηᴿʷ W) Y₀
call-site-ra′-moves-target = one≢zero

no-η-zero-two-one : ∀ (η : 2 ↪ᵗ 3)
  → toRenameᵗ η X₀ ≡ c
  → toRenameᵗ η X₁ ≡ b
  → ⊥
no-η-zero-two-one (keep (keep (skip empty))) ()
no-η-zero-two-one (keep (skip (keep empty))) eq₀ ()
no-η-zero-two-one (skip (keep (keep empty))) ()

no-η-zero-one-same : ∀ (η : 2 ↪ᵗ 3)
  → toRenameᵗ η X₀ ≡ toRenameᵗ η X₁
  → ⊥
no-η-zero-one-same (keep (keep (skip empty))) ()
no-η-zero-one-same (keep (skip (keep empty))) ()
no-η-zero-one-same (skip (keep (keep empty))) ()
no-η-zero-one-same (skip (skip (keep ())))
no-η-zero-one-same (skip (skip (skip ())))

outer-target-premise-refuted : ∀ {Wᵒ : World 2 2 3}
    {γᵒ : CtxImp Wᵒ} {p : ＇ X₀ ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y₁}
  → CTI2.RebaseAtᴿ Wᵒ W (just Y₀)
  → Wᵒ ∣ γᵒ ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★ ⊑ U ∶ p
  → ⊥
outer-target-premise-refuted {Wᵒ = Wᵒ} {p = p}
    (CTI2.rebase-varᴿ {Xᴸ = Fin.zero} rb) prem =
  no-η-zero-two-one (ηᴸʷ Wᵒ)
    (trans
      (ECR.variable-obligation-aligns
        {W = Wᵒ} {X = X₀} {Y = Y₁} p)
      (sym (CTI2.RebaseAt.ηᴿ-off-pivot rb Y₁≢Y₀)))
    (sym (CTI2.RebaseAt.ηᴸ-off-pivot rb X₁≢X₀))
outer-target-premise-refuted
    (CTI2.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero} rb) prem =
  one≢zero (CTI2.RebaseAt.pivotAligned rb)

outer-target-premise-refuted-any-world :
  ∀ {Wᵒ Wᵢ : World 2 2 3}
    {γᵢ : CtxImp Wᵢ} {p : ＇ X₀ ⊑ᵂ⟨ Wᵢ ⟩ ＇ Y₁}
  → RebaseAt Wᵒ W X₀ Y₀
  → (qᵒ : ＇ X₀ ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y₀)
  → CTI2.RebaseAtᴿ Wᵢ Wᵒ (just Y₀)
  → Wᵢ ∣ γᵢ ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★ ⊑ U ∶ p
  → ⊥
outer-target-premise-refuted-any-world {Wᵒ = Wᵒ} {Wᵢ = Wᵢ}
    {p = p} rbᵒ qᵒ
    (CTI2.rebase-varᴿ {Xᴸ = Fin.zero} rb) prem =
  no-η-zero-two-one (ηᴸʷ Wᵢ)
    (trans
      (ECR.variable-obligation-aligns
        {W = Wᵢ} {X = X₀} {Y = Y₁} p)
      (trans
        (sym (CTI2.RebaseAt.ηᴿ-off-pivot rb Y₁≢Y₀))
        (sym (CTI2.RebaseAt.ηᴿ-off-pivot rbᵒ Y₁≢Y₀))))
    (sym
      (trans
        (CTI2.RebaseAt.ηᴸ-off-pivot rbᵒ X₁≢X₀)
        (CTI2.RebaseAt.ηᴸ-off-pivot rb X₁≢X₀)))
outer-target-premise-refuted-any-world {Wᵒ = Wᵒ} rbᵒ qᵒ
    (CTI2.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero} rb) prem =
  no-η-zero-one-same (ηᴸʷ Wᵒ)
    (trans
      (ECR.variable-obligation-aligns
        {W = Wᵒ} {X = X₀} {Y = Y₀} qᵒ)
      (sym (CTI2.RebaseAt.pivotAligned rb)))

no-target-seal-variable-output :
  ¬ (Σ[ q ∈ ＇ X₀ ⊑ᵂ⟨ W ⟩ ＇ Y₀ ]
      (W ∣ [] ⊢²
        (V ⟨ X₁! ⟩) ↓ seal X₀ ★
        ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ q))
no-target-seal-variable-output (q , out) with out
no-target-seal-variable-output (q , out)
    | CTI2.conceal⊑² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) prem .q
    with p
no-target-seal-variable-output (q , out)
    | CTI2.conceal⊑² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) prem .q | ()
no-target-seal-variable-output (q , out)
    | CTI2.⊑conceal² rb-mono rb sc
        (CTI2.⊢↓-sealˣ Y∈) prem .q =
  outer-target-premise-refuted rb prem
no-target-seal-variable-output (q , out)
    | CTI2.conceal⊑conceal² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈) prem .q
    with p
no-target-seal-variable-output (q , out)
    | CTI2.conceal⊑conceal² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈) prem .q
    | ()

no-target-seal-variable-output-any-world :
  ¬ (Σ[ Wᵒ ∈ World 2 2 3 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W X₀ Y₀
      × CTI2.ImpEnvMono W Wᵒ
      × CTI2.SameCtx {W = W} [] γᵒ
      × Σ[ qᵒ ∈ ＇ X₀ ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y₀ ]
          (Wᵒ ∣ γᵒ ⊢²
            (V ⟨ X₁! ⟩) ↓ seal X₀ ★
            ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ qᵒ) ))
no-target-seal-variable-output-any-world
    (Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , qᵒ , out) with out
no-target-seal-variable-output-any-world
    (Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , qᵒ , out)
    | CTI2.conceal⊑² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) prem .qᵒ
    with p
no-target-seal-variable-output-any-world
    (Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , qᵒ , out)
    | CTI2.conceal⊑² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) prem .qᵒ | ()
no-target-seal-variable-output-any-world
    (Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , qᵒ , out)
    | CTI2.⊑conceal² rb-mono rb sc
        (CTI2.⊢↓-sealˣ Y∈) prem .qᵒ =
  outer-target-premise-refuted-any-world rbᵒ qᵒ rb prem
no-target-seal-variable-output-any-world
    (Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , qᵒ , out)
    | CTI2.conceal⊑conceal² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈) prem .qᵒ
    with p
no-target-seal-variable-output-any-world
    (Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , qᵒ , out)
    | CTI2.conceal⊑conceal² {p = p} mono rb sc
        (CTI2.⊢↓-sealˣ X∈) (CTI2.⊢↓-sealˣ Y∈) prem .qᵒ
    | ()

------------------------------------------------------------------------
-- Checkpoint 3: bare right-injection inversion needs open strata
------------------------------------------------------------------------

no-right-inj-output :
  ¬ (W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
      ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ q-out)
no-right-inj-output out =
  no-target-seal-variable-output (q-out , out)

right-inj-inversion²-refutes-open-strata :
  ECR.OpenStrata → ⊥
right-inj-inversion²-refutes-open-strata open-strata =
  no-right-inj-output
    (ECR.right-inj-inversion² W-wf open-strata source-outer-spine
      target-outer-value right-inj-premise q-out)

right-inj-inversion²-bare-statement-refuted :
  ( ECR.SpineValue ((V ⟨ X₁! ⟩) ↓ seal X₀ ★)
  → Value (U ↓ seal Y₀ (＇ Y₁))
  → W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
      ⊑ (U ↓ seal Y₀ (＇ Y₁)) ⟨ Y₀! ⟩ ∶ q-star
  → (q : ＇ X₀ ⊑ᵂ⟨ W ⟩ ＇ Y₀)
  → W ∣ [] ⊢² (V ⟨ X₁! ⟩) ↓ seal X₀ ★
      ⊑ U ↓ seal Y₀ (＇ Y₁) ∶ q )
  → ⊥
right-inj-inversion²-bare-statement-refuted bare-inversion =
  no-right-inj-output
    (bare-inversion source-outer-spine target-outer-value
      right-inj-premise q-out)
