module M5SmartCommaCalibrationScratch where

-- File Charter:
--   * Notes scratch for calibrating smart-comma layouts against E4 and
--     the M5 depth-1 obstruction.
--   * Checks finite world/reveal/type/term leaves for A0 current rules,
--     A1 smart-at-alias with an X⊑X mark, A2 smart-at-name with an X⊑X mark,
--     and A3 smart-at-alias with dynamic marks.
--   * This file is not imported by the live development.
--   * Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--     -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--     GTSFImp/proof/DGG/notes/M5SmartCommaCalibrationScratch.agda`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types using (Ty; ★; ＇_; _⇒_; ⇑ᵗ; var-∈; ∈-fun-left)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Conversion using (〖_,_↑_〗; replaceTy)
open import CastTerms using (`_)
open import Reduction using (applyBody; bind)
import Imprecision as I
open import Imprecision using (_⊢_⊑_)

import M5InterleaveScratch as IL
import M5UnderLiftRevealScratch as UL
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.Catchup.InstInversionDef as IID
import proof.DGG.Catchup.InstInversionProof as IIP
import proof.DGG.TargetBindLift as TBL

------------------------------------------------------------------------
-- Shared stores, bodies, and reveal typing.
------------------------------------------------------------------------

target-β : Fin.Fin 2
target-β = Fin.zero

target-α : Fin.Fin 2
target-α = Fin.suc Fin.zero

target-store-βα : TyStore 2
target-store-βα =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

target-β-entry :
  target-store-βα ∋ target-β ⦂ ＇ target-α
target-β-entry = Z∋ refl

target-α-entry :
  target-store-βα ∋ target-α ⦂ ★
target-α-entry = S-bind∋ (Z∋ refl) refl

e4-source-body : Ty 1
e4-source-body = ＇ Fin.zero ⇒ ＇ Fin.zero

e4-target-alias-body : Ty 2
e4-target-alias-body = ＇ target-β ⇒ ＇ target-β

e4-target-name-body : Ty 2
e4-target-name-body = ＇ target-α ⇒ ＇ target-α

d1-source-body : Ty 2
d1-source-body = ＇ Fin.zero ⇒ ★

d1-target-alias-body : Ty 2
d1-target-alias-body = ＇ target-β ⇒ ★

d1-target-name-body : Ty 2
d1-target-name-body = ＇ target-α ⇒ ★

e4-inner-reveal-⊢↑ :
  target-store-βα Conv.⊢↑[ just target-β ]
    〖 target-β , ＇ target-α ↑ e4-target-alias-body 〗
e4-inner-reveal-⊢↑ =
  IIP.generated-reveal-⊢↑-present
    (∈-fun-left var-∈) target-β-entry

e4-outer-reveal-⊢↑ :
  target-store-βα Conv.⊢↑[ just target-α ]
    〖 target-α , ★ ↑ e4-target-name-body 〗
e4-outer-reveal-⊢↑ =
  IIP.generated-reveal-⊢↑-present
    (∈-fun-left var-∈) target-α-entry

d1-inner-reveal-⊢↑ :
  target-store-βα Conv.⊢↑[ just target-β ]
    〖 target-β , ＇ target-α ↑ d1-target-alias-body 〗
d1-inner-reveal-⊢↑ =
  IIP.generated-reveal-⊢↑-present
    (∈-fun-left var-∈) target-β-entry

d1-outer-reveal-⊢↑ :
  target-store-βα Conv.⊢↑[ just target-α ]
    〖 target-α , ★ ↑ d1-target-name-body 〗
d1-outer-reveal-⊢↑ =
  IIP.generated-reveal-⊢↑-present
    (∈-fun-left var-∈) target-α-entry

------------------------------------------------------------------------
-- Small finite refutation helpers.
------------------------------------------------------------------------

mark-X⊑X : I.VarImp
mark-X⊑X = I.X⊑X

mark-X⊑★ : I.VarImp
mark-X⊑★ = I.X⊑★

mark-X⊑X≢mark-X⊑★ : mark-X⊑X ≢ mark-X⊑★
mark-X⊑X≢mark-X⊑★ ()

no-var⊑star-at-X⊑X : ∀ {Δ} {μ : I.ImpEnv Δ} {X}
  → μ X ≡ I.X⊑X
  → μ ⊢ ＇ X ⊑ ★
  → ⊥
no-var⊑star-at-X⊑X precise (I.X⊑★ dyn) =
  mark-X⊑X≢mark-X⊑★ (trans (sym precise) dyn)

no-var1⊑var0 : ∀ {Δ}
    {μ : I.ImpEnv (suc (suc Δ))}
  → μ ⊢ ＇ (Fin.suc Fin.zero) ⊑ ＇ Fin.zero
  → ⊥
no-var1⊑var0 ()

var-leaf : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (p : A CTX.⊑ᵂ⟨ W ⟩ B)
  → W ∣ CTX.ctx-imp A B p ∷ []
      ⊢² ` 0 ⊑ ` 0 ∶ p
var-leaf p = CTI2.x⊑x² CTX.Zʷ

------------------------------------------------------------------------
-- A0: current rules.
------------------------------------------------------------------------

a0-e4-depth0-transport :
  IID.Λ⊑Λ²PostBodyTransportᵀ
a0-e4-depth0-transport = IIP.Λ⊑Λ²-post-body-transport

a0-e4-inner-rebaseᴿ :
  CTX.RebaseAtᴿ (IIP.ΛPostMidWorld IL.base-world)
    (TBL.ΛLiftToBindFreshWorld I.X⊑★ IL.base-world)
    (just target-β)
a0-e4-inner-rebaseᴿ = IIP.Λ-inner-rebaseᴿ IL.base-world

a0-e4-outer-rebaseᴿ :
  CTX.RebaseAtᴿ
    (CTX.liftWorldLeft I.X⊑★
      (CTX.rightOnlyWorld
        (CTX.rightOnlyWorld IL.base-world ★) (＇ Fin.zero)))
    (IIP.ΛPostMidWorld IL.base-world)
    (just target-α)
a0-e4-outer-rebaseᴿ = IIP.Λ-outer-rebaseᴿ IL.base-world

a0-d1-all-orders-die : (o : IL.PeelOrder) → IL.DiesWhere o
a0-d1-all-orders-die = IL.all-orders-die

a0-d1-sameWorld-type-refuted :
  (＇ Fin.zero ⇒ ★) CTX.⊑ᵂ⟨
    TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ IL.base-world
  ⟩
  replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
    (applyBody (bind ★) (＇ Fin.zero ⇒ ★))
  → ⊥
a0-d1-sameWorld-type-refuted p =
  UL.depth1-inner-sameWorld-q-empty {W = IL.base-world} p

------------------------------------------------------------------------
-- A1: smart-at-alias with X⊑X at c_β.
------------------------------------------------------------------------

imp-alias-X-2 : I.ImpEnv 2
imp-alias-X-2 Fin.zero = I.X⊑X
imp-alias-X-2 (Fin.suc Fin.zero) = I.X⊑★

imp-alias-X-3 : I.ImpEnv 3
imp-alias-X-3 Fin.zero = I.X⊑X
imp-alias-X-3 (Fin.suc Fin.zero) = I.X⊑★
imp-alias-X-3 (Fin.suc (Fin.suc Fin.zero)) = I.X⊑★

e4-source-store : TyStore 1
e4-source-store = store-lift store-empty

d1-source-store : TyStore 2
d1-source-store = store-lift (store-lift store-empty)

η-src-β-1 : 1 ↪ᵗ 2
η-src-β-1 = keep (skip empty)

η-src-α-1 : 1 ↪ᵗ 2
η-src-α-1 = skip (keep empty)

η-tgt-βα-2 : 2 ↪ᵗ 2
η-tgt-βα-2 = keep (keep empty)

η-src-βℓ-2 : 2 ↪ᵗ 3
η-src-βℓ-2 = keep (skip (keep empty))

η-src-αℓ-2 : 2 ↪ᵗ 3
η-src-αℓ-2 = skip (keep (keep empty))

η-tgt-βα-3 : 2 ↪ᵗ 3
η-tgt-βα-3 = keep (keep (skip empty))

a1-e4-alias-world : CTX.World 1 2 2
a1-e4-alias-world =
  CTX.world η-src-β-1 η-tgt-βα-2 imp-alias-X-2
    e4-source-store target-store-βα

a1-e4-name-world : CTX.World 1 2 2
a1-e4-name-world =
  CTX.world η-src-α-1 η-tgt-βα-2 imp-alias-X-2
    e4-source-store target-store-βα

a1-e4-alias-WFWorld : CTX.WFWorld a1-e4-alias-world
a1-e4-alias-WFWorld Fin.zero eq = target-β , refl

a1-e4-source-off-name-to-alias : ∀ {Y}
  → Y ≢ Fin.zero
  → toRenameᵗ (CTX.ηᴸʷ a1-e4-name-world) Y
    ≡ toRenameᵗ (CTX.ηᴸʷ a1-e4-alias-world) Y
a1-e4-source-off-name-to-alias {Fin.zero} neq = ⊥-elim (neq refl)

a1-e4-outer-rebaseᴿ :
  CTX.RebaseAtᴿ a1-e4-alias-world a1-e4-name-world
    (just target-α)
a1-e4-outer-rebaseᴿ =
  CTX.rebase-varᴿ
    (CTX.rebase-at (CTX.same-runtime refl refl)
      a1-e4-source-off-name-to-alias
      (λ Y → refl)
      refl
      (CTX.store-rep-imp (I.X⊑★ refl)))

a1-e4-inner-rebase-refuted :
  CTX.RebaseAtᴿ a1-e4-name-world a1-e4-alias-world
    (just target-β)
  → ⊥
a1-e4-inner-rebase-refuted
    (CTX.rebase-varᴿ {Xᴸ = Fin.zero} rb) =
  no-var⊑star-at-X⊑X refl
    (CTX.StoreRepImp.represented
      (CTX.RebaseAt.storeRepresentations rb))

a1-e4-type-leaf-ok :
  e4-source-body CTX.⊑ᵂ⟨ a1-e4-name-world ⟩ e4-target-name-body
a1-e4-type-leaf-ok = I.⇒⊑⇒ I.X⊑X I.X⊑X

a1-e4-term-var-p :
  ＇ Fin.zero CTX.⊑ᵂ⟨ a1-e4-alias-world ⟩ ＇ target-β
a1-e4-term-var-p = I.X⊑X

a1-e4-term-var-leaf-ok :
  a1-e4-alias-world ∣
    CTX.ctx-imp (＇ Fin.zero) (＇ target-β) a1-e4-term-var-p ∷ []
    ⊢² ` 0 ⊑ ` 0 ∶ a1-e4-term-var-p
a1-e4-term-var-leaf-ok = var-leaf a1-e4-term-var-p

a1-d1-alias-world : CTX.World 2 2 3
a1-d1-alias-world = IL.candidate-world

a1-d1-name-world : CTX.World 2 2 3
a1-d1-name-world =
  CTX.world η-src-αℓ-2 η-tgt-βα-3 imp-alias-X-3
    d1-source-store target-store-βα

a1-d1-alias-WFWorld : CTX.WFWorld a1-d1-alias-world
a1-d1-alias-WFWorld = IL.candidate-WFWorld

a1-d1-name-WFWorld : CTX.WFWorld a1-d1-name-world
a1-d1-name-WFWorld Fin.zero ()
a1-d1-name-WFWorld (Fin.suc Fin.zero) ()

a1-d1-outer-rebaseᴿ :
  CTX.RebaseAtᴿ a1-d1-alias-world a1-d1-name-world
    (just target-α)
a1-d1-outer-rebaseᴿ =
  CTX.rebase-varᴿ
    (CTX.rebase-at (CTX.same-runtime refl refl)
      source-off (λ Y → refl) refl
      (CTX.store-rep-imp (I.X⊑★ refl)))
  where
  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTX.ηᴸʷ a1-d1-name-world) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ a1-d1-alias-world) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)
  source-off {Fin.suc Fin.zero} neq = refl

a1-d1-inner-rebase-refuted :
  CTX.RebaseAtᴿ a1-d1-name-world a1-d1-alias-world
    (just target-β)
  → ⊥
a1-d1-inner-rebase-refuted
    (CTX.rebase-varᴿ {Xᴸ = Fin.zero} rb) =
  no-var⊑star-at-X⊑X refl
    (CTX.StoreRepImp.represented
      (CTX.RebaseAt.storeRepresentations rb))
a1-d1-inner-rebase-refuted
    (CTX.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero}
      (CTX.rebase-at _ _ _ () _))

a1-d1-type-leaf-ok :
  d1-source-body CTX.⊑ᵂ⟨ a1-d1-name-world ⟩ d1-target-name-body
a1-d1-type-leaf-ok = I.⇒⊑⇒ I.X⊑X I.★⊑★

a1-d1-term-var-p :
  ＇ Fin.zero CTX.⊑ᵂ⟨ a1-d1-alias-world ⟩ ＇ target-β
a1-d1-term-var-p = I.X⊑X

a1-d1-term-var-leaf-ok :
  a1-d1-alias-world ∣
    CTX.ctx-imp (＇ Fin.zero) (＇ target-β) a1-d1-term-var-p ∷ []
    ⊢² ` 0 ⊑ ` 0 ∶ a1-d1-term-var-p
a1-d1-term-var-leaf-ok = var-leaf a1-d1-term-var-p

------------------------------------------------------------------------
-- A2: smart-at-name with X⊑X at c_α.
------------------------------------------------------------------------

imp-name-X-2 : I.ImpEnv 2
imp-name-X-2 Fin.zero = I.X⊑★
imp-name-X-2 (Fin.suc Fin.zero) = I.X⊑X

imp-name-X-3 : I.ImpEnv 3
imp-name-X-3 Fin.zero = I.X⊑★
imp-name-X-3 (Fin.suc Fin.zero) = I.X⊑X
imp-name-X-3 (Fin.suc (Fin.suc Fin.zero)) = I.X⊑★

a2-e4-name-world : CTX.World 1 2 2
a2-e4-name-world =
  CTX.world η-src-α-1 η-tgt-βα-2 imp-name-X-2
    e4-source-store target-store-βα

a2-e4-name-WFWorld : CTX.WFWorld a2-e4-name-world
a2-e4-name-WFWorld Fin.zero eq = target-α , refl

a2-e4-outer-rebase-refuted :
  CTX.RebaseAtᴿ a2-e4-name-world a2-e4-name-world
    (just target-α)
  → ⊥
a2-e4-outer-rebase-refuted
    (CTX.rebase-varᴿ {Xᴸ = Fin.zero} rb) =
  no-var⊑star-at-X⊑X refl
    (CTX.StoreRepImp.represented
      (CTX.RebaseAt.storeRepresentations rb))

a2-e4-type-leaf-ok :
  e4-source-body CTX.⊑ᵂ⟨ a2-e4-name-world ⟩ e4-target-name-body
a2-e4-type-leaf-ok = I.⇒⊑⇒ I.X⊑X I.X⊑X

a2-e4-term-var-refuted :
  ＇ Fin.zero CTX.⊑ᵂ⟨ a2-e4-name-world ⟩ ＇ target-β
  → ⊥
a2-e4-term-var-refuted = no-var1⊑var0

a2-d1-name-world : CTX.World 2 2 3
a2-d1-name-world =
  CTX.world η-src-αℓ-2 η-tgt-βα-3 imp-name-X-3
    d1-source-store target-store-βα

a2-d1-name-WFWorld : CTX.WFWorld a2-d1-name-world
a2-d1-name-WFWorld Fin.zero eq = target-α , refl
a2-d1-name-WFWorld (Fin.suc Fin.zero) ()

a2-d1-outer-rebase-refuted :
  CTX.RebaseAtᴿ a2-d1-name-world a2-d1-name-world
    (just target-α)
  → ⊥
a2-d1-outer-rebase-refuted
    (CTX.rebase-varᴿ {Xᴸ = Fin.zero} rb) =
  no-var⊑star-at-X⊑X refl
    (CTX.StoreRepImp.represented
      (CTX.RebaseAt.storeRepresentations rb))
a2-d1-outer-rebase-refuted
    (CTX.rebase-varᴿ {Xᴸ = Fin.suc Fin.zero}
      (CTX.rebase-at _ _ _ () _))

a2-d1-type-leaf-ok :
  d1-source-body CTX.⊑ᵂ⟨ a2-d1-name-world ⟩ d1-target-name-body
a2-d1-type-leaf-ok = I.⇒⊑⇒ I.X⊑X I.★⊑★

a2-d1-term-var-refuted :
  ＇ Fin.zero CTX.⊑ᵂ⟨ a2-d1-name-world ⟩ ＇ target-β
  → ⊥
a2-d1-term-var-refuted = no-var1⊑var0

------------------------------------------------------------------------
-- A3: smart-at-alias with dynamic marks.  This is the natural variant that
-- appears once reveal evidence is checked against canonical store reps.
------------------------------------------------------------------------

imp-star-2 : I.ImpEnv 2
imp-star-2 _ = I.X⊑★

imp-star-3 : I.ImpEnv 3
imp-star-3 _ = I.X⊑★

a3-e4-alias-world : CTX.World 1 2 2
a3-e4-alias-world =
  CTX.world η-src-β-1 η-tgt-βα-2 imp-star-2
    e4-source-store target-store-βα

a3-e4-name-world : CTX.World 1 2 2
a3-e4-name-world =
  CTX.world η-src-α-1 η-tgt-βα-2 imp-star-2
    e4-source-store target-store-βα

a3-e4-alias-WFWorld : CTX.WFWorld a3-e4-alias-world
a3-e4-alias-WFWorld Fin.zero ()

a3-e4-name-WFWorld : CTX.WFWorld a3-e4-name-world
a3-e4-name-WFWorld Fin.zero ()

a3-e4-source-off-name-to-alias : ∀ {Y}
  → Y ≢ Fin.zero
  → toRenameᵗ (CTX.ηᴸʷ a3-e4-name-world) Y
    ≡ toRenameᵗ (CTX.ηᴸʷ a3-e4-alias-world) Y
a3-e4-source-off-name-to-alias {Fin.zero} neq = ⊥-elim (neq refl)

a3-e4-source-off-alias-to-name : ∀ {Y}
  → Y ≢ Fin.zero
  → toRenameᵗ (CTX.ηᴸʷ a3-e4-alias-world) Y
    ≡ toRenameᵗ (CTX.ηᴸʷ a3-e4-name-world) Y
a3-e4-source-off-alias-to-name {Fin.zero} neq = ⊥-elim (neq refl)

a3-e4-outer-rebaseᴿ :
  CTX.RebaseAtᴿ a3-e4-alias-world a3-e4-name-world
    (just target-α)
a3-e4-outer-rebaseᴿ =
  CTX.rebase-varᴿ
    (CTX.rebase-at (CTX.same-runtime refl refl)
      a3-e4-source-off-name-to-alias
      (λ Y → refl)
      refl
      (CTX.store-rep-imp (I.X⊑★ refl)))

a3-e4-inner-rebaseᴿ :
  CTX.RebaseAtᴿ a3-e4-name-world a3-e4-alias-world
    (just target-β)
a3-e4-inner-rebaseᴿ =
  CTX.rebase-varᴿ
    (CTX.rebase-at (CTX.same-runtime refl refl)
      a3-e4-source-off-alias-to-name
      (λ Y → refl)
      refl
      (CTX.store-rep-imp (I.X⊑★ refl)))

a3-e4-type-leaf-ok :
  e4-source-body CTX.⊑ᵂ⟨ a3-e4-name-world ⟩ e4-target-name-body
a3-e4-type-leaf-ok = I.⇒⊑⇒ I.X⊑X I.X⊑X

a3-e4-term-var-p :
  ＇ Fin.zero CTX.⊑ᵂ⟨ a3-e4-alias-world ⟩ ＇ target-β
a3-e4-term-var-p = I.X⊑X

a3-e4-term-var-leaf-ok :
  a3-e4-alias-world ∣
    CTX.ctx-imp (＇ Fin.zero) (＇ target-β) a3-e4-term-var-p ∷ []
    ⊢² ` 0 ⊑ ` 0 ∶ a3-e4-term-var-p
a3-e4-term-var-leaf-ok = var-leaf a3-e4-term-var-p

a3-d1-alias-world : CTX.World 2 2 3
a3-d1-alias-world =
  CTX.world η-src-βℓ-2 η-tgt-βα-3 imp-star-3
    d1-source-store target-store-βα

a3-d1-name-world : CTX.World 2 2 3
a3-d1-name-world =
  CTX.world η-src-αℓ-2 η-tgt-βα-3 imp-star-3
    d1-source-store target-store-βα

a3-d1-alias-WFWorld : CTX.WFWorld a3-d1-alias-world
a3-d1-alias-WFWorld Fin.zero ()
a3-d1-alias-WFWorld (Fin.suc Fin.zero) ()

a3-d1-name-WFWorld : CTX.WFWorld a3-d1-name-world
a3-d1-name-WFWorld Fin.zero ()
a3-d1-name-WFWorld (Fin.suc Fin.zero) ()

a3-d1-outer-rebaseᴿ :
  CTX.RebaseAtᴿ a3-d1-alias-world a3-d1-name-world
    (just target-α)
a3-d1-outer-rebaseᴿ =
  CTX.rebase-varᴿ
    (CTX.rebase-at (CTX.same-runtime refl refl)
      source-off (λ Y → refl) refl
      (CTX.store-rep-imp (I.X⊑★ refl)))
  where
  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTX.ηᴸʷ a3-d1-name-world) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ a3-d1-alias-world) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)
  source-off {Fin.suc Fin.zero} neq = refl

a3-d1-inner-rebaseᴿ :
  CTX.RebaseAtᴿ a3-d1-name-world a3-d1-alias-world
    (just target-β)
a3-d1-inner-rebaseᴿ =
  CTX.rebase-varᴿ
    (CTX.rebase-at (CTX.same-runtime refl refl)
      source-off (λ Y → refl) refl
      (CTX.store-rep-imp (I.X⊑★ refl)))
  where
  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTX.ηᴸʷ a3-d1-alias-world) Y
      ≡ toRenameᵗ (CTX.ηᴸʷ a3-d1-name-world) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)
  source-off {Fin.suc Fin.zero} neq = refl

a3-d1-type-leaf-ok :
  d1-source-body CTX.⊑ᵂ⟨ a3-d1-name-world ⟩ d1-target-name-body
a3-d1-type-leaf-ok = I.⇒⊑⇒ I.X⊑X I.★⊑★

a3-d1-term-var-p :
  ＇ Fin.zero CTX.⊑ᵂ⟨ a3-d1-alias-world ⟩ ＇ target-β
a3-d1-term-var-p = I.X⊑X

a3-d1-term-var-leaf-ok :
  a3-d1-alias-world ∣
    CTX.ctx-imp (＇ Fin.zero) (＇ target-β) a3-d1-term-var-p ∷ []
    ⊢² ` 0 ⊑ ` 0 ∶ a3-d1-term-var-p
a3-d1-term-var-leaf-ok = var-leaf a3-d1-term-var-p
