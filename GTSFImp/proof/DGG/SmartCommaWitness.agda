module proof.DGG.SmartCommaWitness where

-- File Charter:
--   * Leaf-gated witness that the live smart-comma rule overcomes the M5
--     depth-1 blocker.
--   * Builds the concrete two-target-allocation D1 world from
--     M5-DEPTH1-RAW-REPORT.md and derives the live `⊢²` relation for
--     `Λ (Λ V)` against the generated reveal-wrapped target post term.
--   * No simulation theorem consumes this file; `All.agda` imports it so the
--     blocker-overcome witness stays checked.

open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; cong)
  renaming (subst to subst≡)

open import Types using
  (Ty; ★; ＇_; ‵_; _⇒_; `∀; ⇑ᵗ; NonVar; _∈ᵗ_; renameᵗ;
   substᵗ; substᵗ-cong; substᵗ-rename; extsᵗ; extᵗ;
   nonvar-fun; nonvar-all; ∈-fun-left; var-∈)
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; _∋_⦂_; Z∋; S-bind∋)
open import TermCtx as TC using ()
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; `_; ƛ_; Λ_; _↑_; blame;
   ⊢`; ⊢ƛ; ⊢reveal; ⊢blame)
import Imprecision as I

import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.CastTermImprecision2Typing as CTI2Typing
import proof.DGG.Catchup.InstInversionProof as IIP
open import proof.ImprecisionConsistency using (subst-⊑)
open import proof.TypeInTermSubst using (rename-occurs)

------------------------------------------------------------------------
-- The D1 two-allocation world and generated target post term.
------------------------------------------------------------------------

empty-imp : I.ImpEnv 0
empty-imp ()

base-world : CTX.World 0 0 0
base-world =
  CTX.world empty empty empty-imp store-empty store-empty

W₂ : CTX.World 0 2 2
W₂ =
  CTX.rightOnlyWorld (CTX.rightOnlyWorld base-world ★) (＇ Fin.zero)

γ₂ : CTX.CtxImp W₂
γ₂ = []

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

★⇒★ : Ty 2
★⇒★ = ★ ⇒ ★

d1-source-body : Ty 2
d1-source-body = ＇ Fin.zero ⇒ ★

d1-target-alias-body : Ty 2
d1-target-alias-body = ＇ target-β ⇒ ★

d1-target-name-body : Ty 2
d1-target-name-body = ＇ target-α ⇒ ★

d1-source-lam : Term 2
d1-source-lam = ƛ blame

d1-target-lam : Term 2
d1-target-lam = ƛ blame

d1-inner-conv =
  〖 target-β , ＇ target-α ↑ d1-target-alias-body 〗

d1-outer-conv =
  〖 target-α , ★ ↑ d1-target-name-body 〗

post : Term 2
post = (d1-target-lam ↑ d1-inner-conv) ↑ d1-outer-conv

d1-inner-reveal-⊢↑ :
  target-store-βα Conv.⊢↑[ just target-β ] d1-inner-conv
d1-inner-reveal-⊢↑ =
  IIP.generated-reveal-⊢↑-present
    (∈-fun-left var-∈) target-β-entry

d1-outer-reveal-⊢↑ :
  target-store-βα Conv.⊢↑[ just target-α ] d1-outer-conv
d1-outer-reveal-⊢↑ =
  IIP.generated-reveal-⊢↑-present
    (∈-fun-left var-∈) target-α-entry

d1-target-lam-⊢ :
  ⟨ 2 , target-store-βα , [] ⟩ ⊢ d1-target-lam ⦂ d1-target-alias-body
d1-target-lam-⊢ = ⊢ƛ ⊢blame

post-⊢ : ⟨ 2 , target-store-βα , [] ⟩ ⊢ post ⦂ ★⇒★
post-⊢ =
  ⊢reveal (CTI2Typing.erase-⊢↑ d1-outer-reveal-⊢↑)
    (⊢reveal (CTI2Typing.erase-⊢↑ d1-inner-reveal-⊢↑)
      d1-target-lam-⊢)

------------------------------------------------------------------------
-- A3 D1 worlds: alias merge for the inner binder, fresh-behind for outer.
------------------------------------------------------------------------

all-star₃ : I.ImpEnv 3
all-star₃ _ = I.X⊑★

d1-source-store : TyStore 2
d1-source-store = store-lift (store-lift store-empty)

η-src-βℓ-2 : 2 ↪ᵗ 3
η-src-βℓ-2 = keep (skip (keep empty))

η-src-αℓ-2 : 2 ↪ᵗ 3
η-src-αℓ-2 = skip (keep (keep empty))

η-tgt-βα-3 : 2 ↪ᵗ 3
η-tgt-βα-3 = keep (keep (skip empty))

d1-outer-smart-world : CTX.World 1 2 3
d1-outer-smart-world =
  CTX.world (skip (skip (keep empty))) η-tgt-βα-3 all-star₃
    (store-lift store-empty) target-store-βα

a3-d1-alias-world : CTX.World 2 2 3
a3-d1-alias-world =
  CTX.world η-src-βℓ-2 η-tgt-βα-3 all-star₃
    d1-source-store target-store-βα

a3-d1-name-world : CTX.World 2 2 3
a3-d1-name-world =
  CTX.world η-src-αℓ-2 η-tgt-βα-3 all-star₃
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
a3-d1-term-var-leaf-ok = CTI2.x⊑x² CTX.Zʷ

------------------------------------------------------------------------
-- Obligation transport fields for the live smart guards.
------------------------------------------------------------------------

rename-as-subst : ∀ {Δ Δ′}
  → (ρ : Fin.Fin Δ → Fin.Fin Δ′)
  → (A : Ty Δ)
  → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
rename-as-subst ρ (＇ X) = refl
rename-as-subst ρ (‵ ι) = refl
rename-as-subst ρ ★ = refl
rename-as-subst ρ (A ⇒ B)
    rewrite rename-as-subst ρ A | rename-as-subst ρ B =
  refl
rename-as-subst ρ (`∀ A) =
  cong `∀
    (trans (substᵗ-cong A exts-eq)
      (rename-as-subst (extᵗ ρ) A))
  where
  exts-eq : ∀ X
    → extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
  exts-eq Fin.zero = refl
  exts-eq (Fin.suc X) = refl

transport⊑ᵂ-by-subst : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (σ : Fin.Fin Δ → Ty Δ′)
  → (∀ Z → CTX.impEnvʷ W Z ≡ I.X⊑★
      → I._⊢_⊑_ (CTX.impEnvʷ W′) (σ Z) ★)
  → (∀ C → substᵗ σ (CTX.embedᴸ W C) ≡ CTX.embedᴸ W′ C)
  → (∀ C → substᵗ σ (CTX.embedᴿ W C) ≡ CTX.embedᴿ W′ C)
  → A CTX.⊑ᵂ⟨ W ⟩ B
  → A CTX.⊑ᵂ⟨ W′ ⟩ B
transport⊑ᵂ-by-subst {W = W} {W′ = W′} {A = A} {B = B}
    σ star-map source-eq target-eq p =
  subst≡
    (λ L → I._⊢_⊑_ (CTX.impEnvʷ W′) L (CTX.embedᴿ W′ B))
    (source-eq A)
    (subst≡
      (λ R → I._⊢_⊑_ (CTX.impEnvʷ W′)
        (substᵗ σ (CTX.embedᴸ W A)) R)
      (target-eq B)
      (subst-⊑ star-map p))

d1-fresh-subst : Fin.Fin 3 → Ty 3
d1-fresh-subst Fin.zero = ＇ (Fin.suc (Fin.suc Fin.zero))
d1-fresh-subst (Fin.suc Fin.zero) = ＇ Fin.zero
d1-fresh-subst (Fin.suc (Fin.suc Fin.zero)) = ＇ (Fin.suc Fin.zero)

d1-fresh-star : ∀ Z
  → CTX.impEnvʷ (CTX.liftWorldLeft I.X⊑★ W₂) Z ≡ I.X⊑★
  → I._⊢_⊑_ (CTX.impEnvʷ d1-outer-smart-world)
      (d1-fresh-subst Z) ★
d1-fresh-star Fin.zero star = I.X⊑★ refl
d1-fresh-star (Fin.suc Fin.zero) star = I.X⊑★ refl
d1-fresh-star (Fin.suc (Fin.suc Fin.zero)) star = I.X⊑★ refl

d1-fresh-source-point : ∀ X
  → d1-fresh-subst (toRenameᵗ (keep (CTX.ηᴸʷ W₂)) X)
    ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ d1-outer-smart-world) X)
d1-fresh-source-point Fin.zero = refl

d1-fresh-target-point : ∀ Y
  → d1-fresh-subst (toRenameᵗ (skip (CTX.ηᴿʷ W₂)) Y)
    ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ d1-outer-smart-world) Y)
d1-fresh-target-point Fin.zero = refl
d1-fresh-target-point (Fin.suc Fin.zero) = refl

d1-fresh-source-eq : ∀ C
  → substᵗ d1-fresh-subst
      (CTX.embedᴸ (CTX.liftWorldLeft I.X⊑★ W₂) C)
    ≡ CTX.embedᴸ d1-outer-smart-world C
d1-fresh-source-eq C =
  trans (substᵗ-rename d1-fresh-subst
      (toRenameᵗ (keep (CTX.ηᴸʷ W₂))) C)
    (trans (substᵗ-cong C d1-fresh-source-point)
      (rename-as-subst (toRenameᵗ (CTX.ηᴸʷ d1-outer-smart-world)) C))

d1-fresh-target-eq : ∀ C
  → substᵗ d1-fresh-subst
      (CTX.embedᴿ (CTX.liftWorldLeft I.X⊑★ W₂) C)
    ≡ CTX.embedᴿ d1-outer-smart-world C
d1-fresh-target-eq C =
  trans (substᵗ-rename d1-fresh-subst
      (toRenameᵗ (skip (CTX.ηᴿʷ W₂))) C)
    (trans (substᵗ-cong C d1-fresh-target-point)
      (rename-as-subst (toRenameᵗ (CTX.ηᴿʷ d1-outer-smart-world)) C))

d1-fresh-transport : ∀ {A : Ty 1} {B : Ty 2}
  → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft I.X⊑★ W₂ ⟩ B
  → A CTX.⊑ᵂ⟨ d1-outer-smart-world ⟩ B
d1-fresh-transport =
  transport⊑ᵂ-by-subst
    {W = CTX.liftWorldLeft I.X⊑★ W₂}
    {W′ = d1-outer-smart-world}
    d1-fresh-subst d1-fresh-star d1-fresh-source-eq
    d1-fresh-target-eq

d1-merge-subst : Fin.Fin 4 → Ty 3
d1-merge-subst Fin.zero = ＇ Fin.zero
d1-merge-subst (Fin.suc Fin.zero) = ＇ Fin.zero
d1-merge-subst (Fin.suc (Fin.suc Fin.zero)) = ＇ (Fin.suc Fin.zero)
d1-merge-subst (Fin.suc (Fin.suc (Fin.suc Fin.zero))) =
  ＇ (Fin.suc (Fin.suc Fin.zero))

d1-merge-star : ∀ Z
  → CTX.impEnvʷ
      (CTX.liftWorldLeft I.X⊑★ d1-outer-smart-world) Z
    ≡ I.X⊑★
  → I._⊢_⊑_ (CTX.impEnvʷ a3-d1-alias-world)
      (d1-merge-subst Z) ★
d1-merge-star Fin.zero star = I.X⊑★ refl
d1-merge-star (Fin.suc Fin.zero) star = I.X⊑★ refl
d1-merge-star (Fin.suc (Fin.suc Fin.zero)) star = I.X⊑★ refl
d1-merge-star (Fin.suc (Fin.suc (Fin.suc Fin.zero))) star =
  I.X⊑★ refl

d1-merge-source-point : ∀ X
  → d1-merge-subst
      (toRenameᵗ (keep (CTX.ηᴸʷ d1-outer-smart-world)) X)
    ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ a3-d1-alias-world) X)
d1-merge-source-point Fin.zero = refl
d1-merge-source-point (Fin.suc Fin.zero) = refl

d1-merge-target-point : ∀ Y
  → d1-merge-subst
      (toRenameᵗ (skip (CTX.ηᴿʷ d1-outer-smart-world)) Y)
    ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ a3-d1-alias-world) Y)
d1-merge-target-point Fin.zero = refl
d1-merge-target-point (Fin.suc Fin.zero) = refl

d1-merge-source-eq : ∀ C
  → substᵗ d1-merge-subst
      (CTX.embedᴸ
        (CTX.liftWorldLeft I.X⊑★ d1-outer-smart-world) C)
    ≡ CTX.embedᴸ a3-d1-alias-world C
d1-merge-source-eq C =
  trans (substᵗ-rename d1-merge-subst
      (toRenameᵗ (keep (CTX.ηᴸʷ d1-outer-smart-world))) C)
    (trans (substᵗ-cong C d1-merge-source-point)
      (rename-as-subst
        (toRenameᵗ (CTX.ηᴸʷ a3-d1-alias-world)) C))

d1-merge-target-eq : ∀ C
  → substᵗ d1-merge-subst
      (CTX.embedᴿ
        (CTX.liftWorldLeft I.X⊑★ d1-outer-smart-world) C)
    ≡ CTX.embedᴿ a3-d1-alias-world C
d1-merge-target-eq C =
  trans (substᵗ-rename d1-merge-subst
      (toRenameᵗ (skip (CTX.ηᴿʷ d1-outer-smart-world))) C)
    (trans (substᵗ-cong C d1-merge-target-point)
      (rename-as-subst
        (toRenameᵗ (CTX.ηᴿʷ a3-d1-alias-world)) C))

d1-merge-transport : ∀ {A : Ty 2} {B : Ty 2}
  → A CTX.⊑ᵂ⟨
      CTX.liftWorldLeft I.X⊑★ d1-outer-smart-world
    ⟩ B
  → A CTX.⊑ᵂ⟨ a3-d1-alias-world ⟩ B
d1-merge-transport =
  transport⊑ᵂ-by-subst
    {W = CTX.liftWorldLeft I.X⊑★ d1-outer-smart-world}
    {W′ = a3-d1-alias-world}
    d1-merge-subst d1-merge-star d1-merge-source-eq
    d1-merge-target-eq

------------------------------------------------------------------------
-- The live D1 derivation.
------------------------------------------------------------------------

star-mono-d1-name-alias :
  CTX.ImpEnvMono a3-d1-name-world a3-d1-alias-world
star-mono-d1-name-alias _ _ = refl

star-mono-d1-alias-name :
  CTX.ImpEnvMono a3-d1-alias-world a3-d1-name-world
star-mono-d1-alias-name _ _ = refl

d1-alias-body-p :
  d1-source-body CTX.⊑ᵂ⟨ a3-d1-alias-world ⟩ d1-target-alias-body
d1-alias-body-p =
  I.⇒⊑⇒ a3-d1-term-var-p I.★⊑★

d1-final-body-p :
  d1-source-body CTX.⊑ᵂ⟨ a3-d1-alias-world ⟩ ★⇒★
d1-final-body-p =
  I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★

d1-base-rel :
  a3-d1-alias-world ∣ []
    ⊢² d1-source-lam ⊑ d1-target-lam ∶ d1-alias-body-p
d1-base-rel =
  CTI2.ƛ⊑ƛ² (CTI2.blame⊑² ⊢blame I.★⊑★)

d1-inner-rel :
  a3-d1-name-world ∣ []
    ⊢² d1-source-lam ⊑ d1-target-lam ↑ d1-inner-conv
    ∶ a3-d1-type-leaf-ok
d1-inner-rel =
  CTI2.⊑reveal² star-mono-d1-name-alias a3-d1-inner-rebaseᴿ
    CTX.same-[] d1-inner-reveal-⊢↑ d1-base-rel
    a3-d1-type-leaf-ok

d1-post-rel :
  a3-d1-alias-world ∣ []
    ⊢² d1-source-lam ⊑ post ∶ d1-final-body-p
d1-post-rel =
  CTI2.⊑reveal² star-mono-d1-alias-name a3-d1-outer-rebaseᴿ
    CTX.same-[] d1-outer-reveal-⊢↑ d1-inner-rel d1-final-body-p

d1-fresh-guard :
  CTX.SmartFreshBehindGuard W₂ d1-outer-smart-world
d1-fresh-guard =
  CTX.smart-fresh-behind-guard η-tgt-βα-3 refl refl
    d1-fresh-transport (λ _ _ → refl)
    target-frozen (λ ()) fresh-not-target refl
    (λ _ _ → refl)
  where
  target-frozen : ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ d1-outer-smart-world) Xᴿ
      ≡ toRenameᵗ η-tgt-βα-3 (toRenameᵗ (CTX.ηᴿʷ W₂) Xᴿ)
  target-frozen Fin.zero = refl
  target-frozen (Fin.suc Fin.zero) = refl

  fresh-not-target : ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ d1-outer-smart-world) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ d1-outer-smart-world) Fin.zero
  fresh-not-target Fin.zero ()
  fresh-not-target (Fin.suc Fin.zero) ()

d1-merge-guard :
  CTX.SmartAliasMergeGuard d1-outer-smart-world a3-d1-alias-world
    target-β target-α
d1-merge-guard =
  CTX.smart-alias-merge-guard target-β-entry target-α-entry
    refl refl d1-merge-transport (λ _ _ → refl)
    (λ _ → refl) refl old-source-frozen no-old-source
    refl refl target-mark-off-footprint
  where
  old-source-frozen : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ a3-d1-alias-world) (Fin.suc Xᴸ)
      ≡ toRenameᵗ (CTX.ηᴸʷ d1-outer-smart-world) Xᴸ
  old-source-frozen Fin.zero = refl

  no-old-source : ∀ Xᴸ
    → toRenameᵗ (CTX.ηᴸʷ d1-outer-smart-world) Xᴸ
      ≢ toRenameᵗ (CTX.ηᴿʷ d1-outer-smart-world) target-β
  no-old-source Fin.zero ()

  target-mark-off-footprint : ∀ Xᴿ
    → Xᴿ ≢ target-β
    → Xᴿ ≢ target-α
    → CTX.impEnvʷ d1-outer-smart-world
        (toRenameᵗ (CTX.ηᴿʷ d1-outer-smart-world) Xᴿ) ≡ I.X⊑★
    → CTX.impEnvʷ a3-d1-alias-world
        (toRenameᵗ (CTX.ηᴿʷ a3-d1-alias-world) Xᴿ) ≡ I.X⊑★
  target-mark-off-footprint Fin.zero neqβ neqα dyn = ⊥-elim (neqβ refl)
  target-mark-off-footprint (Fin.suc Fin.zero) neqβ neqα dyn =
    ⊥-elim (neqα refl)

d1-inner-smart-p :
  `∀ d1-source-body CTX.⊑ᵂ⟨ d1-outer-smart-world ⟩ ★⇒★
d1-inner-smart-p =
  I.∀⊑ nonvar-fun (∈-fun-left var-∈)
    (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★)

d1-inner-smart-live :
  d1-outer-smart-world ∣ []
    ⊢² Λ d1-source-lam ⊑ post ∶ d1-inner-smart-p
d1-inner-smart-live =
  CTI2.Λ⊑²-smart-comma
    nonvar-fun (∈-fun-left var-∈)
    (CTX.smart-merge-alias d1-merge-guard)
    CTX.smart-lift-[] (ƛ blame) post-⊢ d1-post-rel
    d1-inner-smart-p

p₂-front-premise :
  `∀ d1-source-body CTX.⊑ᵂ⟨ CTX.liftWorldLeft I.X⊑★ W₂ ⟩ ★⇒★
p₂-front-premise =
  I.∀⊑ nonvar-fun (∈-fun-left var-∈)
    (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★)

p₂ :
  Fin.zero ∈ᵗ `∀ d1-source-body
  → `∀ (`∀ d1-source-body) CTX.⊑ᵂ⟨ W₂ ⟩ ★⇒★
p₂ outer∈ =
  I.∀⊑ nonvar-all
    (rename-occurs (extᵗ (toRenameᵗ (CTX.ηᴸʷ W₂))) outer∈)
    p₂-front-premise

d1-top-smart-live-at :
  Fin.zero ∈ᵗ `∀ d1-source-body
  → (p : `∀ d1-source-body
       CTX.⊑ᵂ⟨ d1-outer-smart-world ⟩ ★⇒★)
  → (q : `∀ (`∀ d1-source-body) CTX.⊑ᵂ⟨ W₂ ⟩ ★⇒★)
  → W₂ ∣ γ₂ ⊢² Λ (Λ d1-source-lam) ⊑ post ∶ q
d1-top-smart-live-at outer∈ p q =
  CTI2.Λ⊑²-smart-comma
    nonvar-all outer∈
    (CTX.smart-fresh-behind d1-fresh-guard)
    CTX.smart-lift-[] (Λ (ƛ blame)) post-⊢
    (d1-inner-smart-live-at-p p) q
  where
  d1-inner-smart-live-at-p :
    (p′ : `∀ d1-source-body
       CTX.⊑ᵂ⟨ d1-outer-smart-world ⟩ ★⇒★)
    → d1-outer-smart-world ∣ []
        ⊢² Λ d1-source-lam ⊑ post ∶ p′
  d1-inner-smart-live-at-p p′ =
    CTI2.Λ⊑²-smart-comma
      nonvar-fun (∈-fun-left var-∈)
      (CTX.smart-merge-alias d1-merge-guard)
      CTX.smart-lift-[] (ƛ blame) post-⊢ d1-post-rel p′

d1-top-smart-live :
  (outer∈ : Fin.zero ∈ᵗ `∀ d1-source-body)
  → W₂ ∣ γ₂ ⊢² Λ (Λ d1-source-lam) ⊑ post ∶ p₂ outer∈
d1-top-smart-live outer∈ =
  d1-top-smart-live-at outer∈ d1-inner-smart-p (p₂ outer∈)
