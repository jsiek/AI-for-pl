module M5SmartCommaRuleScratch where

-- File Charter:
--   * Root-only M-1 scratch for the proposed A3 smart-comma Λ⊑² surface.
--   * Defines the guarded premise-world surface without editing the live
--     `⊢²` relation.
--   * Checks concrete E4 and D1 instantiations against the A3 calibration
--     worlds and reveal witnesses.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types using
  (Ty; ★; ＇_; ‵_; _⇒_; `∀; ⇑ᵗ; NonVar; _∈ᵗ_; renameᵗ;
   substᵗ; substᵗ-cong; substᵗ-id; substᵗ-rename; extsᵗ; extᵗ;
   nonvar-fun; nonvar-all; ∈-fun-left; var-∈)
open import TyStore using (store-empty; store-lift; _∋_⦂_)
open import TermCtx as TC using ()
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Conversion using (〖_,_↑_〗)
open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; `_; ƛ_; Λ_; _↑_; blame;
   ⊢`; ⊢ƛ; ⊢reveal; ⊢blame)
import Imprecision as I

import M5InterleaveScratch as IL
import M5SmartCommaCalibrationScratch as Cal
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.CastTermImprecision2Typing as CTI2Typing
open import proof.ImprecisionConsistency using (subst-⊑)

------------------------------------------------------------------------
-- Smart-comma premise-world surface.
------------------------------------------------------------------------

data SmartLiftCtxᴸ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ} :
    CTI2.CtxImp W → CTI2.CtxImp Wᵐ → Set where
  smart-lift-[] : SmartLiftCtxᴸ [] []

  smart-lift-∷ : ∀ {γ γᵐ A B p pᵐ}
    → SmartLiftCtxᴸ γ γᵐ
      -------------------------------------------------------------
    → SmartLiftCtxᴸ (CTI2.ctx-imp A B p ∷ γ)
        (CTI2.ctx-imp (⇑ᵗ A) B pᵐ ∷ γᵐ)


record SmartFreshBehindGuard {Δᴸ Δᴿ Δ Δᵐ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ) : Set where
  constructor smart-fresh-behind-guard
  field
    oldCenters : Δ ↪ᵗ Δᵐ
    sourceStore-lifted :
      CTI2.sourceStoreʷ Wᵐ ≡ store-lift (CTI2.sourceStoreʷ W)
    targetStore-same :
      CTI2.targetStoreʷ Wᵐ ≡ CTI2.targetStoreʷ W
    transport⊑ᵂ : ∀ {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ B
      → A CTI2.⊑ᵂ⟨ Wᵐ ⟩ B
    old-mark-mono : ∀ Z
      → CTI2.impEnvʷ W Z ≡ I.X⊑★
      → CTI2.impEnvʷ Wᵐ (toRenameᵗ oldCenters Z) ≡ I.X⊑★
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Xᴿ
        ≡ toRenameᵗ oldCenters (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ oldCenters (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
    fresh-not-target : ∀ Xᴿ
      → toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Xᴿ
        ≢ toRenameᵗ (CTI2.ηᴸʷ Wᵐ) Fin.zero
    fresh-mark-dynamic :
      CTI2.impEnvʷ Wᵐ (toRenameᵗ (CTI2.ηᴸʷ Wᵐ) Fin.zero)
        ≡ I.X⊑★


record SmartAliasMergeGuard {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ)
    (β α : Fin.Fin Δᴿ) : Set where
  constructor smart-alias-merge-guard
  field
    β:=＇α : CTI2.targetStoreʷ W ∋ β ⦂ ＇ α
    α:=★ : CTI2.targetStoreʷ W ∋ α ⦂ ★
    sourceStore-lifted :
      CTI2.sourceStoreʷ Wᵐ ≡ store-lift (CTI2.sourceStoreʷ W)
    targetStore-same :
      CTI2.targetStoreʷ Wᵐ ≡ CTI2.targetStoreʷ W
    transport⊑ᵂ : ∀ {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ B
      → A CTI2.⊑ᵂ⟨ Wᵐ ⟩ B
    old-mark-mono : ∀ Z
      → CTI2.impEnvʷ W Z ≡ I.X⊑★
      → CTI2.impEnvʷ Wᵐ Z ≡ I.X⊑★
    target-frozen : ∀ Xᴿ
      → toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Xᴿ
        ≡ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
    pending-at-alias :
      toRenameᵗ (CTI2.ηᴸʷ Wᵐ) Fin.zero
        ≡ toRenameᵗ (CTI2.ηᴿʷ W) β
    old-source-frozen : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ Wᵐ) (Fin.suc Xᴸ)
        ≡ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
    no-old-source-at-alias : ∀ Xᴸ
      → toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (CTI2.ηᴿʷ W) β
    alias-mark-dynamic :
      CTI2.impEnvʷ Wᵐ (toRenameᵗ (CTI2.ηᴿʷ W) β) ≡ I.X⊑★
    name-mark-dynamic :
      CTI2.impEnvʷ Wᵐ (toRenameᵗ (CTI2.ηᴿʷ W) α) ≡ I.X⊑★


data SmartCommaLiftᴸ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) :
    ∀ {Δᵐ} → CTI2.World (suc Δᴸ) Δᴿ Δᵐ → Set where
  smart-fresh-behind :
    ∀ {Δᵐ} {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    → SmartFreshBehindGuard W Wᵐ
    → SmartCommaLiftᴸ W Wᵐ

  smart-merge-alias :
    ∀ {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ} {β α}
    → SmartAliasMergeGuard W Wᵐ β α
    → SmartCommaLiftᴸ W Wᵐ


infix 4 _∣_⊢²ˢ_⊑_∶_

data _∣_⊢²ˢ_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (γ : CTI2.CtxImp W) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A CTI2.⊑ᵂ⟨ W ⟩ B → Set where

  from-⊢² : ∀ {M M′ A B}
      {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
    → W ∣ γ ⊢² M ⊑ M′ ∶ p
      -----------------------------
    → W ∣ γ ⊢²ˢ M ⊑ M′ ∶ p

  Λ⊑²-smart-comma :
      ∀ {Δᵐ}
      {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
      {γᵐ : CTI2.CtxImp Wᵐ}
      {V : Term (suc Δᴸ)} {M : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      {p : A CTI2.⊑ᵂ⟨ Wᵐ ⟩ B}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → SmartCommaLiftᴸ W Wᵐ
    → SmartLiftCtxᴸ {W = W} {Wᵐ = Wᵐ} γ γᵐ
    → Value V
    → ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩ ⊢ M ⦂ B
    → Wᵐ ∣ γᵐ ⊢²ˢ V ⊑ M ∶ p
    → (q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ B)
      -------------------------------------------
    → W ∣ γ ⊢²ˢ Λ V ⊑ M ∶ q

------------------------------------------------------------------------
-- Concrete E4 and D1 post bodies.
------------------------------------------------------------------------

★⇒★ : Ty 2
★⇒★ = ★ ⇒ ★

e4-source-lam : Term 1
e4-source-lam = ƛ ` 0

e4-target-lam : Term 2
e4-target-lam = ƛ ` 0

e4-inner-conv =
  〖 Cal.target-β , ＇ Cal.target-α ↑ Cal.e4-target-alias-body 〗

e4-outer-conv =
  〖 Cal.target-α , ★ ↑ Cal.e4-target-name-body 〗

e4-target-post : Term 2
e4-target-post = (e4-target-lam ↑ e4-inner-conv) ↑ e4-outer-conv

d1-source-lam : Term 2
d1-source-lam = ƛ blame

d1-target-lam : Term 2
d1-target-lam = ƛ blame

d1-inner-conv =
  〖 Cal.target-β , ＇ Cal.target-α ↑ Cal.d1-target-alias-body 〗

d1-outer-conv =
  〖 Cal.target-α , ★ ↑ Cal.d1-target-name-body 〗

d1-target-post : Term 2
d1-target-post = (d1-target-lam ↑ d1-inner-conv) ↑ d1-outer-conv


e4-target-lam-⊢ :
  ⟨ 2 , Cal.target-store-βα , [] ⟩
    ⊢ e4-target-lam ⦂ Cal.e4-target-alias-body
e4-target-lam-⊢ = ⊢ƛ (⊢` TC.Z)

e4-target-post-⊢ :
  ⟨ 2 , Cal.target-store-βα , [] ⟩ ⊢ e4-target-post ⦂ ★⇒★
e4-target-post-⊢ =
  ⊢reveal (CTI2Typing.erase-⊢↑ Cal.e4-outer-reveal-⊢↑)
    (⊢reveal (CTI2Typing.erase-⊢↑ Cal.e4-inner-reveal-⊢↑)
      e4-target-lam-⊢)

d1-target-lam-⊢ :
  ⟨ 2 , Cal.target-store-βα , [] ⟩
    ⊢ d1-target-lam ⦂ Cal.d1-target-alias-body
d1-target-lam-⊢ = ⊢ƛ ⊢blame

d1-target-post-⊢ :
  ⟨ 2 , Cal.target-store-βα , [] ⟩ ⊢ d1-target-post ⦂ ★⇒★
d1-target-post-⊢ =
  ⊢reveal (CTI2Typing.erase-⊢↑ Cal.d1-outer-reveal-⊢↑)
    (⊢reveal (CTI2Typing.erase-⊢↑ Cal.d1-inner-reveal-⊢↑)
      d1-target-lam-⊢)

------------------------------------------------------------------------
-- E4: the A3 witnesses slot into the smart-alias constructor.
------------------------------------------------------------------------

all-star₃ : I.ImpEnv 3
all-star₃ _ = I.X⊑★

d1-outer-smart-world : CTI2.World 1 2 3
d1-outer-smart-world =
  CTI2.world (skip (skip (keep empty))) Cal.η-tgt-βα-3 all-star₃
    (store-lift store-empty) Cal.target-store-βα

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
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (σ : Fin.Fin Δ → Ty Δ′)
  → (∀ Z → CTI2.impEnvʷ W Z ≡ I.X⊑★
      → I._⊢_⊑_ (CTI2.impEnvʷ W′) (σ Z) ★)
  → (∀ C → substᵗ σ (CTI2.embedᴸ W C) ≡ CTI2.embedᴸ W′ C)
  → (∀ C → substᵗ σ (CTI2.embedᴿ W C) ≡ CTI2.embedᴿ W′ C)
  → A CTI2.⊑ᵂ⟨ W ⟩ B
  → A CTI2.⊑ᵂ⟨ W′ ⟩ B
transport⊑ᵂ-by-subst {W = W} {W′ = W′} {A = A} {B = B}
    σ star-map source-eq target-eq p =
  subst≡
    (λ L → I._⊢_⊑_ (CTI2.impEnvʷ W′) L (CTI2.embedᴿ W′ B))
    (source-eq A)
    (subst≡
      (λ R → I._⊢_⊑_ (CTI2.impEnvʷ W′)
        (substᵗ σ (CTI2.embedᴸ W A)) R)
      (target-eq B)
      (subst-⊑ star-map p))

e4-merge-subst : Fin.Fin 3 → Ty 2
e4-merge-subst Fin.zero = ＇ Fin.zero
e4-merge-subst (Fin.suc Fin.zero) = ＇ Fin.zero
e4-merge-subst (Fin.suc (Fin.suc Fin.zero)) = ＇ (Fin.suc Fin.zero)

e4-merge-star : ∀ Z
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ IL.post-world) Z
    ≡ I.X⊑★
  → I._⊢_⊑_ (CTI2.impEnvʷ Cal.a3-e4-alias-world)
      (e4-merge-subst Z) ★
e4-merge-star Fin.zero star = I.X⊑★ refl
e4-merge-star (Fin.suc Fin.zero) star = I.X⊑★ refl
e4-merge-star (Fin.suc (Fin.suc Fin.zero)) star = I.X⊑★ refl

e4-merge-source-point : ∀ X
  → e4-merge-subst
      (toRenameᵗ (keep (CTI2.ηᴸʷ IL.post-world)) X)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴸʷ Cal.a3-e4-alias-world) X)
e4-merge-source-point Fin.zero = refl

e4-merge-target-point : ∀ Y
  → e4-merge-subst
      (toRenameᵗ (skip (CTI2.ηᴿʷ IL.post-world)) Y)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴿʷ Cal.a3-e4-alias-world) Y)
e4-merge-target-point Fin.zero = refl
e4-merge-target-point (Fin.suc Fin.zero) = refl

e4-merge-source-eq : ∀ C
  → substᵗ e4-merge-subst
      (CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ IL.post-world) C)
    ≡ CTI2.embedᴸ Cal.a3-e4-alias-world C
e4-merge-source-eq C =
  trans (substᵗ-rename e4-merge-subst
      (toRenameᵗ (keep (CTI2.ηᴸʷ IL.post-world))) C)
    (trans (substᵗ-cong C e4-merge-source-point)
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴸʷ Cal.a3-e4-alias-world)) C))

e4-merge-target-eq : ∀ C
  → substᵗ e4-merge-subst
      (CTI2.embedᴿ (CTI2.liftWorldLeft I.X⊑★ IL.post-world) C)
    ≡ CTI2.embedᴿ Cal.a3-e4-alias-world C
e4-merge-target-eq C =
  trans (substᵗ-rename e4-merge-subst
      (toRenameᵗ (skip (CTI2.ηᴿʷ IL.post-world))) C)
    (trans (substᵗ-cong C e4-merge-target-point)
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴿʷ Cal.a3-e4-alias-world)) C))

e4-merge-transport : ∀ {A : Ty 1} {B : Ty 2}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ IL.post-world ⟩ B
  → A CTI2.⊑ᵂ⟨ Cal.a3-e4-alias-world ⟩ B
e4-merge-transport =
  transport⊑ᵂ-by-subst
    {W = CTI2.liftWorldLeft I.X⊑★ IL.post-world}
    {W′ = Cal.a3-e4-alias-world}
    e4-merge-subst e4-merge-star e4-merge-source-eq
    e4-merge-target-eq

d1-fresh-subst : Fin.Fin 3 → Ty 3
d1-fresh-subst Fin.zero = ＇ (Fin.suc (Fin.suc Fin.zero))
d1-fresh-subst (Fin.suc Fin.zero) = ＇ Fin.zero
d1-fresh-subst (Fin.suc (Fin.suc Fin.zero)) = ＇ (Fin.suc Fin.zero)

d1-fresh-star : ∀ Z
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ IL.post-world) Z
    ≡ I.X⊑★
  → I._⊢_⊑_ (CTI2.impEnvʷ d1-outer-smart-world)
      (d1-fresh-subst Z) ★
d1-fresh-star Fin.zero star = I.X⊑★ refl
d1-fresh-star (Fin.suc Fin.zero) star = I.X⊑★ refl
d1-fresh-star (Fin.suc (Fin.suc Fin.zero)) star = I.X⊑★ refl

d1-fresh-source-point : ∀ X
  → d1-fresh-subst
      (toRenameᵗ (keep (CTI2.ηᴸʷ IL.post-world)) X)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴸʷ d1-outer-smart-world) X)
d1-fresh-source-point Fin.zero = refl

d1-fresh-target-point : ∀ Y
  → d1-fresh-subst
      (toRenameᵗ (skip (CTI2.ηᴿʷ IL.post-world)) Y)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴿʷ d1-outer-smart-world) Y)
d1-fresh-target-point Fin.zero = refl
d1-fresh-target-point (Fin.suc Fin.zero) = refl

d1-fresh-source-eq : ∀ C
  → substᵗ d1-fresh-subst
      (CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ IL.post-world) C)
    ≡ CTI2.embedᴸ d1-outer-smart-world C
d1-fresh-source-eq C =
  trans (substᵗ-rename d1-fresh-subst
      (toRenameᵗ (keep (CTI2.ηᴸʷ IL.post-world))) C)
    (trans (substᵗ-cong C d1-fresh-source-point)
      (rename-as-subst (toRenameᵗ (CTI2.ηᴸʷ d1-outer-smart-world)) C))

d1-fresh-target-eq : ∀ C
  → substᵗ d1-fresh-subst
      (CTI2.embedᴿ (CTI2.liftWorldLeft I.X⊑★ IL.post-world) C)
    ≡ CTI2.embedᴿ d1-outer-smart-world C
d1-fresh-target-eq C =
  trans (substᵗ-rename d1-fresh-subst
      (toRenameᵗ (skip (CTI2.ηᴿʷ IL.post-world))) C)
    (trans (substᵗ-cong C d1-fresh-target-point)
      (rename-as-subst (toRenameᵗ (CTI2.ηᴿʷ d1-outer-smart-world)) C))

d1-fresh-transport : ∀ {A : Ty 1} {B : Ty 2}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ IL.post-world ⟩ B
  → A CTI2.⊑ᵂ⟨ d1-outer-smart-world ⟩ B
d1-fresh-transport =
  transport⊑ᵂ-by-subst
    {W = CTI2.liftWorldLeft I.X⊑★ IL.post-world}
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
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ d1-outer-smart-world) Z
    ≡ I.X⊑★
  → I._⊢_⊑_ (CTI2.impEnvʷ Cal.a3-d1-alias-world)
      (d1-merge-subst Z) ★
d1-merge-star Fin.zero star = I.X⊑★ refl
d1-merge-star (Fin.suc Fin.zero) star = I.X⊑★ refl
d1-merge-star (Fin.suc (Fin.suc Fin.zero)) star = I.X⊑★ refl
d1-merge-star (Fin.suc (Fin.suc (Fin.suc Fin.zero))) star =
  I.X⊑★ refl

d1-merge-source-point : ∀ X
  → d1-merge-subst
      (toRenameᵗ (keep (CTI2.ηᴸʷ d1-outer-smart-world)) X)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴸʷ Cal.a3-d1-alias-world) X)
d1-merge-source-point Fin.zero = refl
d1-merge-source-point (Fin.suc Fin.zero) = refl

d1-merge-target-point : ∀ Y
  → d1-merge-subst
      (toRenameᵗ (skip (CTI2.ηᴿʷ d1-outer-smart-world)) Y)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴿʷ Cal.a3-d1-alias-world) Y)
d1-merge-target-point Fin.zero = refl
d1-merge-target-point (Fin.suc Fin.zero) = refl

d1-merge-source-eq : ∀ C
  → substᵗ d1-merge-subst
      (CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ d1-outer-smart-world) C)
    ≡ CTI2.embedᴸ Cal.a3-d1-alias-world C
d1-merge-source-eq C =
  trans (substᵗ-rename d1-merge-subst
      (toRenameᵗ (keep (CTI2.ηᴸʷ d1-outer-smart-world))) C)
    (trans (substᵗ-cong C d1-merge-source-point)
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴸʷ Cal.a3-d1-alias-world)) C))

d1-merge-target-eq : ∀ C
  → substᵗ d1-merge-subst
      (CTI2.embedᴿ (CTI2.liftWorldLeft I.X⊑★ d1-outer-smart-world) C)
    ≡ CTI2.embedᴿ Cal.a3-d1-alias-world C
d1-merge-target-eq C =
  trans (substᵗ-rename d1-merge-subst
      (toRenameᵗ (skip (CTI2.ηᴿʷ d1-outer-smart-world))) C)
    (trans (substᵗ-cong C d1-merge-target-point)
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴿʷ Cal.a3-d1-alias-world)) C))

d1-merge-transport : ∀ {A : Ty 2} {B : Ty 2}
  → A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ d1-outer-smart-world
    ⟩ B
  → A CTI2.⊑ᵂ⟨ Cal.a3-d1-alias-world ⟩ B
d1-merge-transport =
  transport⊑ᵂ-by-subst
    {W = CTI2.liftWorldLeft I.X⊑★ d1-outer-smart-world}
    {W′ = Cal.a3-d1-alias-world}
    d1-merge-subst d1-merge-star d1-merge-source-eq
    d1-merge-target-eq

star-mono-e4-name-alias :
  CTI2.ImpEnvMono Cal.a3-e4-name-world Cal.a3-e4-alias-world
star-mono-e4-name-alias _ _ = refl

star-mono-e4-alias-name :
  CTI2.ImpEnvMono Cal.a3-e4-alias-world Cal.a3-e4-name-world
star-mono-e4-alias-name _ _ = refl

star-mono-d1-name-alias :
  CTI2.ImpEnvMono Cal.a3-d1-name-world Cal.a3-d1-alias-world
star-mono-d1-name-alias _ _ = refl

star-mono-d1-alias-name :
  CTI2.ImpEnvMono Cal.a3-d1-alias-world Cal.a3-d1-name-world
star-mono-d1-alias-name _ _ = refl

e4-alias-body-p :
  Cal.e4-source-body CTI2.⊑ᵂ⟨ Cal.a3-e4-alias-world ⟩
    Cal.e4-target-alias-body
e4-alias-body-p =
  I.⇒⊑⇒ Cal.a3-e4-term-var-p Cal.a3-e4-term-var-p

e4-final-body-p :
  Cal.e4-source-body CTI2.⊑ᵂ⟨ Cal.a3-e4-alias-world ⟩ ★⇒★
e4-final-body-p =
  I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)

e4-base-rel :
  Cal.a3-e4-alias-world ∣ []
    ⊢² e4-source-lam ⊑ e4-target-lam ∶ e4-alias-body-p
e4-base-rel = CTI2.ƛ⊑ƛ² Cal.a3-e4-term-var-leaf-ok

e4-inner-rel :
  Cal.a3-e4-name-world ∣ []
    ⊢² e4-source-lam ⊑ e4-target-lam ↑ e4-inner-conv
    ∶ Cal.a3-e4-type-leaf-ok
e4-inner-rel =
  CTI2.⊑reveal² star-mono-e4-name-alias Cal.a3-e4-inner-rebaseᴿ
    CTI2.same-[] Cal.e4-inner-reveal-⊢↑ e4-base-rel
    Cal.a3-e4-type-leaf-ok

e4-post-rel :
  Cal.a3-e4-alias-world ∣ []
    ⊢² e4-source-lam ⊑ e4-target-post ∶ e4-final-body-p
e4-post-rel =
  CTI2.⊑reveal² star-mono-e4-alias-name Cal.a3-e4-outer-rebaseᴿ
    CTI2.same-[] Cal.e4-outer-reveal-⊢↑ e4-inner-rel e4-final-body-p

e4-merge-guard :
  SmartAliasMergeGuard IL.post-world Cal.a3-e4-alias-world
    Cal.target-β Cal.target-α
e4-merge-guard =
  smart-alias-merge-guard Cal.target-β-entry Cal.target-α-entry
    refl refl e4-merge-transport (λ _ _ → refl)
    (λ _ → refl) refl (λ ()) (λ ())
    refl refl

e4-smart-preflight :
  (q : `∀ Cal.e4-source-body CTI2.⊑ᵂ⟨ IL.post-world ⟩ ★⇒★)
  → IL.post-world ∣ []
      ⊢²ˢ Λ e4-source-lam ⊑ e4-target-post ∶ q
e4-smart-preflight q =
  Λ⊑²-smart-comma
    nonvar-fun (∈-fun-left var-∈)
    (smart-merge-alias e4-merge-guard)
    smart-lift-[] (ƛ ` 0) e4-target-post-⊢
    (from-⊢² e4-post-rel) q

------------------------------------------------------------------------
-- D1: top fresh-behind smart comma, then inner alias merge.
------------------------------------------------------------------------

d1-alias-body-p :
  Cal.d1-source-body CTI2.⊑ᵂ⟨ Cal.a3-d1-alias-world ⟩
    Cal.d1-target-alias-body
d1-alias-body-p =
  I.⇒⊑⇒ Cal.a3-d1-term-var-p I.★⊑★

d1-final-body-p :
  Cal.d1-source-body CTI2.⊑ᵂ⟨ Cal.a3-d1-alias-world ⟩ ★⇒★
d1-final-body-p =
  I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★

d1-base-rel :
  Cal.a3-d1-alias-world ∣ []
    ⊢² d1-source-lam ⊑ d1-target-lam ∶ d1-alias-body-p
d1-base-rel =
  CTI2.ƛ⊑ƛ² (CTI2.blame⊑² ⊢blame I.★⊑★)

d1-inner-rel :
  Cal.a3-d1-name-world ∣ []
    ⊢² d1-source-lam ⊑ d1-target-lam ↑ d1-inner-conv
    ∶ Cal.a3-d1-type-leaf-ok
d1-inner-rel =
  CTI2.⊑reveal² star-mono-d1-name-alias Cal.a3-d1-inner-rebaseᴿ
    CTI2.same-[] Cal.d1-inner-reveal-⊢↑ d1-base-rel
    Cal.a3-d1-type-leaf-ok

d1-post-rel :
  Cal.a3-d1-alias-world ∣ []
    ⊢² d1-source-lam ⊑ d1-target-post ∶ d1-final-body-p
d1-post-rel =
  CTI2.⊑reveal² star-mono-d1-alias-name Cal.a3-d1-outer-rebaseᴿ
    CTI2.same-[] Cal.d1-outer-reveal-⊢↑ d1-inner-rel d1-final-body-p

d1-fresh-guard :
  SmartFreshBehindGuard IL.post-world d1-outer-smart-world
d1-fresh-guard =
  smart-fresh-behind-guard Cal.η-tgt-βα-3 refl refl
    d1-fresh-transport (λ _ _ → refl)
    target-frozen (λ ()) fresh-not-target refl
  where
  target-frozen : ∀ Xᴿ
    → toRenameᵗ (CTI2.ηᴿʷ d1-outer-smart-world) Xᴿ
      ≡ toRenameᵗ Cal.η-tgt-βα-3
          (toRenameᵗ (CTI2.ηᴿʷ IL.post-world) Xᴿ)
  target-frozen Fin.zero = refl
  target-frozen (Fin.suc Fin.zero) = refl

  fresh-not-target : ∀ Xᴿ
    → toRenameᵗ (CTI2.ηᴿʷ d1-outer-smart-world) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴸʷ d1-outer-smart-world) Fin.zero
  fresh-not-target Fin.zero ()
  fresh-not-target (Fin.suc Fin.zero) ()

d1-merge-guard :
  SmartAliasMergeGuard d1-outer-smart-world Cal.a3-d1-alias-world
    Cal.target-β Cal.target-α
d1-merge-guard =
  smart-alias-merge-guard Cal.target-β-entry Cal.target-α-entry
    refl refl d1-merge-transport (λ _ _ → refl)
    (λ _ → refl) refl old-source-frozen no-old-source
    refl refl
  where
  old-source-frozen : ∀ Xᴸ
    → toRenameᵗ (CTI2.ηᴸʷ Cal.a3-d1-alias-world) (Fin.suc Xᴸ)
      ≡ toRenameᵗ (CTI2.ηᴸʷ d1-outer-smart-world) Xᴸ
  old-source-frozen Fin.zero = refl

  no-old-source : ∀ Xᴸ
    → toRenameᵗ (CTI2.ηᴸʷ d1-outer-smart-world) Xᴸ
      ≢ toRenameᵗ (CTI2.ηᴿʷ d1-outer-smart-world) Cal.target-β
  no-old-source Fin.zero ()

d1-inner-smart-preflight :
  (q : `∀ Cal.d1-source-body
       CTI2.⊑ᵂ⟨ d1-outer-smart-world ⟩ ★⇒★)
  → d1-outer-smart-world ∣ []
      ⊢²ˢ Λ d1-source-lam ⊑ d1-target-post ∶ q
d1-inner-smart-preflight q =
  Λ⊑²-smart-comma
    nonvar-fun (∈-fun-left var-∈)
    (smart-merge-alias d1-merge-guard)
    smart-lift-[] (ƛ blame) d1-target-post-⊢
    (from-⊢² d1-post-rel) q

d1-top-smart-preflight :
  Fin.zero ∈ᵗ `∀ Cal.d1-source-body
  →
  (p : `∀ Cal.d1-source-body
       CTI2.⊑ᵂ⟨ d1-outer-smart-world ⟩ ★⇒★)
  → (q : `∀ (`∀ Cal.d1-source-body)
       CTI2.⊑ᵂ⟨ IL.post-world ⟩ ★⇒★)
  → IL.post-world ∣ []
      ⊢²ˢ Λ (Λ d1-source-lam) ⊑ d1-target-post ∶ q
d1-top-smart-preflight outer∈ p q =
  Λ⊑²-smart-comma
    nonvar-all outer∈
    (smart-fresh-behind d1-fresh-guard)
    smart-lift-[] (Λ (ƛ blame)) d1-target-post-⊢
    (d1-inner-smart-preflight p) q
