module proof.DGG.ExtraCastRightProbe where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Fin using (zero)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _↪ᵗ_; id; _↦_; ∀ᶜ_; _!; ？_;
   keep; skip; wk↪ᵗ; toRenameᵗ; extᵐ; instᵐ; genᵐ; inst_; gen_;
   bot-elim; bot-intro; renameᵐᶜ; ↑ᶜ_; close-instᶜ)
import Consistency as C
open import Conversion using (Conv↑; Conv↓; `∀↑_; `∀↓_; 〖_,_↑_〗)
open import CastTerms using
  (Term; Value; _⊢_⦂_; ⊢⟨⟩; ⟨_,_,_⟩; ƛ_; Λ_; $; _⦂∀_[_];
   _⟨_⟩; _↑_; _↓_; GenSafe; Inert; inj; fun; all; seal; genᵥ;
   safe-⇒; safe-∀; safe-inst; safe-gen; _《_》; renameᵗᵐ; ⇑ᵗᵐ)
open import Imprecision using (_⊢_⊑_)
import Imprecision as I
import Reduction as R
import GradualTermImprecision as GTI
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.RightInjInversion as RII
open CTI using (_∣_⊢ᶜ_⊑_∶_; _∣_∣_∣_⊢ᶜ_⊑_∶_)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; ground-cast-target⊑; ground-targets-unique⊑;
   ground-target-nonvar-to-star⊑; expand-cast-source⊑; nonstar-from-≢★;
   rename-⊑; fin-suc-injective; renameᵗ-injective;
   source-occurs-target; toRenameᵗ-injective; unshift-nonvar)
import proof.Imprecision as PI
import proof.TypeSafety.Progress as Prog
open import proof.TypeSafety.Progress using (gen-safe)
open import proof.TypeInTermSubst using
  (rename-star-injective; rename-occurs; renameᵗ-wk-eq;
   renameᵗᵐ-preserves-Value; toRename-keep-eq)

applyEnvs : ∀ {Δ Δ′}
  → R.StoreChanges Δ Δ′
  → Env∼ Δ
  → Env∼ Δ′
applyEnvs R.[] μ = μ
applyEnvs (χ R.∷ χs) μ = applyEnvs χs (R.applyEnv χ μ)

applyConsistencies : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (χs : R.StoreChanges Δ Δ′)
  → μ ⊢ A ∼ B
  → applyEnvs χs μ ⊢ R.applyTys χs A ∼ R.applyTys χs B
applyConsistencies R.[] c = c
applyConsistencies (χ R.∷ χs) c =
  applyConsistencies χs (R.applyConsistency χ c)

cast-↠ : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′}
    {χs : R.StoreChanges Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
  → (c : μ ⊢ A ∼ B)
  → M R.—↠[ χs ] N
  → M ⟨ c ⟩ R.—↠[ χs ] N ⟨ applyConsistencies χs c ⟩
cast-↠ {M = M} c (_ R.∎[]) = (M ⟨ c ⟩) R.∎[]
cast-↠ {M = M} {χs = χ R.∷ χs} c
    (_ R.—→[ χ ]⟨ M→N ⟩ N↠P) =
  (M ⟨ c ⟩)
    R.—→[ χ ]⟨ R.ξ-⟨⟩ M→N refl ⟩
  cast-↠ (R.applyConsistency χ c) N↠P

applyStoreChange-Inert : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (χ : R.StoreChange Δ Δ′)
  → Inert c
  → Inert (R.applyConsistency χ c)
applyStoreChange-Inert R.keep inert = inert
applyStoreChange-Inert (R.bind A)
    (inj ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = C.⇒∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ★⇒★ ⦄ ⦃ G∼★ = C.⇒∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (R.bind A)
    (inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = C.ι∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ‵ ι ⦄ ⦃ G∼★ = C.ι∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (R.bind A)
    (inj {G = ＇ X} ⦃ Gᵍ = ＇ .X ⦄
      ⦃ G∼★ = C.X∼★ᵍ eq ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ＇ Fin.suc X ⦄ ⦃ G∼★ = C.X∼★ᵍ eq ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (R.bind A)
    (inj ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = C.∀∼★ ⦄ ⦃ Gns = Gns ⦄) =
  inj ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = C.∀∼★ ⦄
    ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
applyStoreChange-Inert (R.bind A) fun = fun
applyStoreChange-Inert (R.bind A) all = all
applyStoreChange-Inert (R.bind A)
    (genᵥ {A = A₀} {B = B} {c = c}
      ⦃ Bnv = Bnv ⦄ ⦃ z∈B = z∈B ⦄ A≢★ safe) =
  subst≡
    (λ z → Inert (gen_ ⦃ Bnv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
      ⦃ z∈B = z ⦄ _ _))
    (PI.∈ᵗ-unique (rename-occurs (extᵗ Fin.suc) z∈B) _)
    (genᵥ ⦃ Bnv = renameNonVar (extᵗ Fin.suc) Bnv ⦄
      ⦃ z∈B = rename-occurs (extᵗ Fin.suc) z∈B ⦄
      A′≢★
      (gen-safe _ A′≢★ (renameNonVar (extᵗ Fin.suc) Bnv)
        (rename-occurs (extᵗ Fin.suc) z∈B)))
  where
  A′≢★ = λ eq → A≢★ (rename-star-injective Fin.suc eq)

applyConsistencies-Inert : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (χs : R.StoreChanges Δ Δ′)
  → Inert c
  → Inert (applyConsistencies χs c)
applyConsistencies-Inert R.[] inert = inert
applyConsistencies-Inert (χ R.∷ χs) inert =
  applyConsistencies-Inert χs (applyStoreChange-Inert χ inert)

gen-safe-source-nonvar : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → GenSafe c
  → NonVar A
gen-safe-source-nonvar safe-⇒ = nonvar-fun
gen-safe-source-nonvar safe-∀ = nonvar-all
gen-safe-source-nonvar (safe-inst B≢★) = nonvar-all
gen-safe-source-nonvar (safe-gen A≢★ safe) =
  unshift-nonvar (gen-safe-source-nonvar safe)

liftCtx-inst : ∀ {Δ} {μ : I.ImpEnv Δ}
  → (γ : GTI.CtxImp μ)
  → Σ[ γ′ ∈ GTI.CtxImp (I.instᵐ μ) ] GTI.LiftCtxⁱ (I.instᵐ μ) γ γ′
liftCtx-inst [] = [] , GTI.lift-[]
liftCtx-inst (GTI.ctx-imp A B p ∷ γ) with liftCtx-inst γ
liftCtx-inst (GTI.ctx-imp A B p ∷ γ) | γ′ , liftγ =
  GTI.ctx-imp (⇑ᵗ A) (⇑ᵗ B)
    (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p) ∷ γ′ ,
  GTI.lift-∷ liftγ

lift-rightOnly-⊑ : ∀ {Δᴿ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {μ : I.ImpEnv Δ} {A : Ty Δ} {B : Ty Δᴿ}
  → μ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B
  → I.instᵐ μ ⊢ ⇑ᵗ A ⊑ renameᵗ (toRenameᵗ (keep ηᴿ)) (⇑ᵗ B)
lift-rightOnly-⊑ {ηᴿ = ηᴿ} {B = B} p =
  subst≡ (λ T → _ ⊢ _ ⊑ T)
    (sym
      (trans (renameᵗ-cong (⇑ᵗ B) (toRename-keep-eq ηᴿ))
        (renameᵗ-shift (toRenameᵗ ηᴿ) B)))
    (rename-⊑ Fin.suc fin-suc-injective (λ X eq → eq) p)

unrename-star-view : ∀ {Δ Δ′} {η : Δ ↪ᵗ Δ′} {V : Term Δ}
  → Value V
  → Prog.StarView (renameᵗᵐ η V)
  → Prog.StarView V
unrename-star-view (ƛ N) (Prog.sv-tag vW ())
unrename-star-view (Λ vV) (Prog.sv-tag vW ())
unrename-star-view ($ κ) (Prog.sv-tag vW ())
unrename-star-view
    (vV 《 inj {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
      ⦃ Gns = Gns ⦄ 》)
    star =
  Prog.sv-tag vV refl
unrename-star-view (vV 《 fun 》) (Prog.sv-tag vW ())
unrename-star-view (vV 《 all 》) (Prog.sv-tag vW ())
unrename-star-view (vV 《 genᵥ A≢★ safe 》) (Prog.sv-tag vW ())
unrename-star-view (vV ↑ fun) (Prog.sv-tag vW ())
unrename-star-view (vV ↑ all) (Prog.sv-tag vW ())
unrename-star-view (vV ↓ seal) (Prog.sv-tag vW ())
unrename-star-view (vV ↓ fun) (Prog.sv-tag vW ())
unrename-star-view (vV ↓ all) (Prog.sv-tag vW ())

data AllValueView {Δ : TyCtx} (V : Term Δ) : Set where
  allv-Λ : ∀ {W}
    → Value W
    → V ≡ Λ W
    → AllValueView V
  allv-∀ : ∀ {μ W A B} {c : extᵐ μ ⊢ A ∼ B}
    → Value W
    → V ≡ W ⟨ ∀ᶜ c ⟩
    → AllValueView V
  allv-gen : ∀ {μ W A B} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → Value W
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → V ≡ W ⟨ (gen c) A≢★ ⟩
    → AllValueView V
  allv-reveal : ∀ {W A B} {c : Conv↑ (suc Δ) A B}
    → Value W
    → V ≡ W ↑ `∀↑ c
    → AllValueView V
  allv-conceal : ∀ {W A B} {c : Conv↓ (suc Δ) A B}
    → Value W
    → V ≡ W ↓ `∀↓ c
    → AllValueView V

unrename-all-value-view : ∀ {Δ Δ′} {η : Δ ↪ᵗ Δ′}
    {V : Term Δ} {A : Ty (suc Δ)}
  → Value V
  → Prog.AllView (renameᵗ (extᵗ (toRenameᵗ η)) A) (renameᵗᵐ η V)
  → AllValueView V
unrename-all-value-view (ƛ N) (Prog.av-Λ vW ())
unrename-all-value-view (ƛ N) (Prog.av-∀ vW ())
unrename-all-value-view (ƛ N) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (ƛ N) (Prog.av-reveal vW ())
unrename-all-value-view (ƛ N) (Prog.av-conceal vW ())
unrename-all-value-view (Λ vV) (Prog.av-Λ vW refl) =
  allv-Λ vV refl
unrename-all-value-view (Λ vV) (Prog.av-∀ vW ())
unrename-all-value-view (Λ vV) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (Λ vV) (Prog.av-reveal vW ())
unrename-all-value-view (Λ vV) (Prog.av-conceal vW ())
unrename-all-value-view ($ κ) (Prog.av-Λ vW ())
unrename-all-value-view ($ κ) (Prog.av-∀ vW ())
unrename-all-value-view ($ κ) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view ($ κ) (Prog.av-reveal vW ())
unrename-all-value-view ($ κ) (Prog.av-conceal vW ())
unrename-all-value-view (vV 《 inj 》) (Prog.av-Λ vW ())
unrename-all-value-view (vV 《 inj 》) (Prog.av-∀ vW ())
unrename-all-value-view (vV 《 inj 》) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV 《 inj 》) (Prog.av-reveal vW ())
unrename-all-value-view (vV 《 inj 》) (Prog.av-conceal vW ())
unrename-all-value-view (vV 《 fun 》) (Prog.av-Λ vW ())
unrename-all-value-view (vV 《 fun 》) (Prog.av-∀ vW ())
unrename-all-value-view (vV 《 fun 》) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV 《 fun 》) (Prog.av-reveal vW ())
unrename-all-value-view (vV 《 fun 》) (Prog.av-conceal vW ())
unrename-all-value-view (vV 《 all 》) (Prog.av-Λ vW ())
unrename-all-value-view (vV 《 all 》) (Prog.av-∀ vW eq) =
  allv-∀ vV refl
unrename-all-value-view (vV 《 all 》) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV 《 all 》) (Prog.av-reveal vW ())
unrename-all-value-view (vV 《 all 》) (Prog.av-conceal vW ())
unrename-all-value-view (vV 《 genᵥ A≢★ safe 》) (Prog.av-Λ vW ())
unrename-all-value-view (vV 《 genᵥ A≢★ safe 》) (Prog.av-∀ vW ())
unrename-all-value-view (vV 《 genᵥ A≢★ safe 》) (Prog.av-gen vW A≢★′ safe′ eq) =
  allv-gen vV A≢★ safe refl
unrename-all-value-view (vV 《 genᵥ A≢★ safe 》) (Prog.av-reveal vW ())
unrename-all-value-view (vV 《 genᵥ A≢★ safe 》) (Prog.av-conceal vW ())
unrename-all-value-view (vV ↑ fun) (Prog.av-Λ vW ())
unrename-all-value-view (vV ↑ fun) (Prog.av-∀ vW ())
unrename-all-value-view (vV ↑ fun) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV ↑ fun) (Prog.av-reveal vW ())
unrename-all-value-view (vV ↑ fun) (Prog.av-conceal vW ())
unrename-all-value-view (vV ↑ all) (Prog.av-Λ vW ())
unrename-all-value-view (vV ↑ all) (Prog.av-∀ vW ())
unrename-all-value-view (vV ↑ all) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV ↑ all) (Prog.av-reveal vW eq) =
  allv-reveal vV refl
unrename-all-value-view (vV ↑ all) (Prog.av-conceal vW ())
unrename-all-value-view (vV ↓ seal) (Prog.av-Λ vW ())
unrename-all-value-view (vV ↓ seal) (Prog.av-∀ vW ())
unrename-all-value-view (vV ↓ seal) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV ↓ seal) (Prog.av-reveal vW ())
unrename-all-value-view (vV ↓ seal) (Prog.av-conceal vW ())
unrename-all-value-view (vV ↓ fun) (Prog.av-Λ vW ())
unrename-all-value-view (vV ↓ fun) (Prog.av-∀ vW ())
unrename-all-value-view (vV ↓ fun) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV ↓ fun) (Prog.av-reveal vW ())
unrename-all-value-view (vV ↓ fun) (Prog.av-conceal vW ())
unrename-all-value-view (vV ↓ all) (Prog.av-Λ vW ())
unrename-all-value-view (vV ↓ all) (Prog.av-∀ vW ())
unrename-all-value-view (vV ↓ all) (Prog.av-gen vW A≢★ safe ())
unrename-all-value-view (vV ↓ all) (Prog.av-reveal vW ())
unrename-all-value-view (vV ↓ all) (Prog.av-conceal vW eq) =
  allv-conceal vV refl

right-inj-index-forces-core : ∀ {Δ} {ρ : CTI.StoreImp Δ}
    {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M W : Term Δ} {A G H : Ty Δ} {κ : Env∼ Δ}
    {gH : Ground H} {H∼★ : κ ⊢ H ∼★}
    {Hns : NonStar H}
    {cH : κ ⊢ H ∼ H}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ ★}
  → (gG : Ground G)
  → Value M
  → ρ ∣ γ ⊢ᶜ M
      ⊑ W ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ cH ⦃ Hns ⦄ ⟩
      ∶ p
  → CTI.impEnvⁱ ρ ⊢ A ⊑ G
  → CTI.impEnvⁱ ρ ⊢ A ⊑ H
right-inj-index-forces-core gG vM
    (CTI.⊑castᶜ {p = A⊑H} c′ M⊑W A⊑★) A⊑G =
  A⊑H
right-inj-index-forces-core () (vM 《 inj 》)
    (CTI.cast⊑castᶜ c c′ M⊑W A⊑★) I.★⊑★
right-inj-index-forces-core {gH = ★⇒★} ★⇒★
    (vM 《 fun 》)
    (CTI.cast⊑castᶜ {p = I.⇒⊑⇒ pA pB} (c ↦ d) c′ M⊑W
      A⊑★)
    (I.⇒⊑⇒ qA qB) =
  I.⇒⊑⇒ qA qB
right-inj-index-forces-core {ρ = ρ} {A = A′} {gH = gH} gG
    (vM 《 all {c = c} 》)
    (CTI.cast⊑castᶜ {p = C⊑H} .(∀ᶜ c) c′ M⊑W A′⊑★)
    A′⊑G =
  subst≡ (λ T → CTI.impEnvⁱ ρ ⊢ A′ ⊑ T)
    (ground-targets-unique⊑ gG gH
      (ground-cast-source⊑ gG nonstar-∀ (∀ᶜ c)
        (ground-target-nonvar-to-star⊑ gH nonvar-all C⊑H)
        A′⊑★ A′⊑G)
      C⊑H)
    A′⊑G
right-inj-index-forces-core {ρ = ρ} {A = A′} {gH = gH} gG
    (vM 《 genᵥ A≢★ safe 》)
    (CTI.cast⊑castᶜ {p = C⊑H} c c′ M⊑W A′⊑★)
    A′⊑G =
  subst≡ (λ T → CTI.impEnvⁱ ρ ⊢ A′ ⊑ T)
    (ground-targets-unique⊑ gG gH
      (ground-cast-source⊑ gG (nonstar-from-≢★ A≢★) c
        (ground-target-nonvar-to-star⊑ gH
          (unshift-nonvar (gen-safe-source-nonvar safe)) C⊑H)
        A′⊑★ A′⊑G)
      C⊑H)
    A′⊑G
right-inj-index-forces-core () (vM 《 inj 》)
    (CTI.cast⊑ᶜ c M⊑W! A⊑★) I.★⊑★
right-inj-index-forces-core {ρ = ρ} {γ = γ} {A = A′} {H = H}
    {κ = κH} {gH = gH} {H∼★ = H∼★} {cH = cH}
    ★⇒★ (vM 《 fun 》)
    (CTI.cast⊑ᶜ {A = A₀} {p = I.⇒⊑★ pA pB}
      c M⊑W! A⊑★)
    (I.⇒⊑⇒ qA qB) =
  subst≡ (λ T → CTI.impEnvⁱ ρ ⊢ A′ ⊑ T) eq (I.⇒⊑⇒ qA qB)
  where
  A₀⊑G : CTI.impEnvⁱ ρ ⊢ A₀ ⊑ ★ ⇒ ★
  A₀⊑G = I.⇒⊑⇒ pA pB

  A₀⊑H : CTI.impEnvⁱ ρ ⊢ A₀ ⊑ H
  A₀⊑H =
    right-inj-index-forces-core {ρ = ρ} {γ = γ} {A = A₀}
      {G = ★ ⇒ ★} {κ = κH}
      {gH = gH} {H∼★ = H∼★} {cH = cH}
      ★⇒★ vM M⊑W! A₀⊑G

  eq : ★ ⇒ ★ ≡ H
  eq = ground-targets-unique⊑ ★⇒★ gH A₀⊑G A₀⊑H
right-inj-index-forces-core {ρ = ρ} {A = A′} {gH = gH} gG
    (vM 《 all {c = c} 》)
    (CTI.cast⊑ᶜ {p = p} .(∀ᶜ c) M⊑W! A⊑★) A⊑G =
  subst≡ (λ T → CTI.impEnvⁱ ρ ⊢ A′ ⊑ T)
    (ground-targets-unique⊑ gG gH
      (ground-cast-source⊑ gG nonstar-∀ (∀ᶜ c) p A⊑★ A⊑G)
      (right-inj-index-forces-core gG vM M⊑W!
        (ground-cast-source⊑ gG nonstar-∀ (∀ᶜ c) p A⊑★ A⊑G)))
    A⊑G
right-inj-index-forces-core {ρ = ρ} {A = A′} {gH = gH} gG
    (vM 《 genᵥ A≢★ safe 》)
    (CTI.cast⊑ᶜ {p = p} c M⊑W! A⊑★) A⊑G =
  subst≡ (λ T → CTI.impEnvⁱ ρ ⊢ A′ ⊑ T)
    (ground-targets-unique⊑ gG gH
      (ground-cast-source⊑ gG (nonstar-from-≢★ A≢★) c p
        A⊑★ A⊑G)
      (right-inj-index-forces-core gG vM M⊑W!
        (ground-cast-source⊑ gG (nonstar-from-≢★ A≢★) c p
          A⊑★ A⊑G)))
    A⊑G
right-inj-index-forces-core {ρ = ρ} {W = W} {G = G} {H = H}
    {κ = κH} {gH = gH} {H∼★ = H∼★} {cH = cH}
    gG (Λ vV₀)
    (CTI.Λ⊑ᶜ {γ′ = γ′} {A = A₀}
      Anv zero∈A liftγ vV W!⊢ V⊑⇑W!)
    (I.∀⊑ Anv′ zero∈A′ A₀⊑⇑G) =
  I.∀⊑ Anv′ zero∈A′
    (subst≡ (λ T → I.instᵐ (CTI.impEnvⁱ ρ) ⊢ A₀ ⊑ T)
      (renameᵗ-wk-eq H)
      (right-inj-index-forces-core
        {ρ = CTI.liftStoreImp I.X⊑★ ρ} {γ = γ′}
        {W = renameᵗᵐ wk↪ᵗ W}
        {G = renameᵗ (toRenameᵗ wk↪ᵗ) G}
        {H = renameᵗ (toRenameᵗ wk↪ᵗ) H}
        {κ = C.renameEnv∼ wk↪ᵗ κH}
        {gH = C.renameGroundᵐ wk↪ᵗ gH}
        {H∼★ = C.rename∼★ᵐ wk↪ᵗ H∼★}
        (C.renameGroundᵐ wk↪ᵗ gG) vV V⊑⇑W!
        (subst≡ (λ T → I.instᵐ (CTI.impEnvⁱ ρ) ⊢ A₀ ⊑ T)
          (sym (renameᵗ-wk-eq G)) A₀⊑⇑G)))
right-inj-index-forces-core ∀★ (Λ vV₀)
    (CTI.Λ⊑ᶜ Anv zero∈A liftγ vV W!⊢ V⊑⇑W!)
    (I.∀⊑∀ A⊑★)
    with source-occurs-target refl A⊑★ zero∈A
right-inj-index-forces-core ∀★ (Λ vV₀)
    (CTI.Λ⊑ᶜ Anv zero∈A liftγ vV W!⊢ V⊑⇑W!)
    (I.∀⊑∀ A⊑★) | ()
right-inj-index-forces-core gG (Λ vV₀)
    (CTI.Λ⊑ᶜ () zero∈A liftγ vV W!⊢ V⊑⇑W!)
    I.bot-elim
right-inj-index-forces-core gG () (CTI.•⊑ᶜ M⊑M′ q′ p) A⊑G

right-inj-index-forces-indexed : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : CTI.StoreImp Δ} {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M : Term Δᴸ} {W : Term Δᴿ}
    {A : Ty Δ} {G H : Ty Δᴿ} {κ : Env∼ Δᴿ}
    {gH : Ground H} {H∼★ : κ ⊢ H ∼★}
    {Hns : NonStar H}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ ★}
  → (gG : Ground G)
  → Value M
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M
      ⊑ W ⟨ _! ⦃ gH ⦄ ⦃ H∼★ ⦄ (C.idᵍ gH) ⦃ Hns ⦄ ⟩
      ∶ p
  → CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) G
  → CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) H
right-inj-index-forces-indexed {ηᴿ = ηᴿ} gG vM
    (CTI.rename⊑renameᶜ categorize M⊑W!) A⊑G =
  right-inj-index-forces-core (C.renameGroundᵐ ηᴿ gG)
    (renameᵗᵐ-preserves-Value _ vM) M⊑W! A⊑G

extra-cast-right : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : CTI.StoreImp Δ} {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → (q : CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ χs ∈ R.StoreChanges Δᴿ Δᴿ′ ]
    Σ[ ηᴸ′ ∈ Δᴸ ↪ᵗ Δ′ ] Σ[ ηᴿ′ ∈ Δᴿ′ ↪ᵗ Δ′ ]
    Σ[ ρ′ ∈ CTI.StoreImp Δ′ ]
    Σ[ γ′ ∈ GTI.CtxImp (CTI.impEnvⁱ ρ′) ]
    Σ[ A′ ∈ Ty Δ′ ]
    Σ[ transport⊑ ∈ (∀ {C : Ty Δᴿ}
      → CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) C
      → CTI.impEnvⁱ ρ′
          ⊢ A′ ⊑ renameᵗ (toRenameᵗ ηᴿ′) (R.applyTys χs C)) ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
       × (M′ ⟨ c′ ⟩ R.—↠[ χs ] N′)
       × (ηᴸ′ ∣ ηᴿ′ ∣ ρ′ ∣ γ′ ⊢ᶜ M ⊑ N′ ∶ transport⊑ q))

inst-catchup-right : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : CTI.StoreImp Δ} {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) (`∀ B)}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : C.instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (q : CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B′)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ χs ∈ R.StoreChanges Δᴿ Δᴿ′ ]
    Σ[ ηᴸ′ ∈ Δᴸ ↪ᵗ Δ′ ] Σ[ ηᴿ′ ∈ Δᴿ′ ↪ᵗ Δ′ ]
    Σ[ ρ′ ∈ CTI.StoreImp Δ′ ]
    Σ[ γ′ ∈ GTI.CtxImp (CTI.impEnvⁱ ρ′) ]
    Σ[ A′ ∈ Ty Δ′ ]
    Σ[ transport⊑ ∈ (∀ {C : Ty Δᴿ}
      → CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) C
      → CTI.impEnvⁱ ρ′
          ⊢ A′ ⊑ renameᵗ (toRenameᵗ ηᴿ′) (R.applyTys χs C)) ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
       × (M′ ⟨ (inst c′) B′≢★ ⟩ R.—↠[ χs ] N′)
       × (ηᴸ′ ∣ ηᴿ′ ∣ ρ′ ∣ γ′ ⊢ᶜ M ⊑ N′ ∶ transport⊑ q))

-- Case: c′ = id a
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {p = p}
    M⊑M′ vM vM′ (id a) q =
  Δᴿ , Δ , _ , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vM′ ,
  ((M′ ⟨ id a ⟩)
    R.—→[ R.keep ]⟨ R.pure-step (R.β-id vM′) ⟩
  M′ R.∎[]) ,
  subst≡ (λ r → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ r)
    (PI.⊑-unique p q) M⊑M′

-- Case: c′ = c ↦ d
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′) vM vM′ (c ↦ d) q =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vM′ 《 fun 》 , ((M′ ⟨ c ↦ d ⟩) R.∎[]) ,
  CTI.rename⊑renameᶜ categorize
    (CTI.⊑castᶜ (renameᵐᶜ ηᴿ (c ↦ d)) M⊑M′ q)

-- Case: c′ = ∀ᶜ c
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′) vM vM′ (∀ᶜ c) q =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vM′ 《 all 》 , ((M′ ⟨ ∀ᶜ c ⟩) R.∎[]) ,
  CTI.rename⊑renameᶜ categorize
    (CTI.⊑castᶜ (renameᵐᶜ ηᴿ (∀ᶜ c)) M⊑M′ q)

-- Case: c′ = _! c
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄) q
    with Prog.to-ground Gᵍ c

-- Subcase: Prog.to-ground Gᵍ c = same
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    (CTI.rename⊑renameᶜ categorize M⊑M′) vM vM′
    (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ .(C.idᵍ Gᵍ) ⦃ Bns ⦄) q
    | Prog.same
    rewrite nonStar-unique Bns (C.ground-nonstar Gᵍ) =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vM′ 《 inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
    ⦃ Gns = C.ground-nonstar Gᵍ ⦄ 》 ,
  ((M′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (C.idᵍ Gᵍ)
    ⦃ C.ground-nonstar Gᵍ ⦄ ⟩) R.∎[]) ,
  CTI.rename⊑renameᶜ categorize
    (CTI.⊑castᶜ
      (renameᵐᶜ ηᴿ
        (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (C.idᵍ Gᵍ)
          ⦃ C.ground-nonstar Gᵍ ⦄))
      M⊑M′ q)

-- Subcase: Prog.to-ground Gᵍ c = other B≢G
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {p = p}
    M⊑M′ vM vM′ (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄) q
    | Prog.other B≢G
    with extra-cast-right M⊑M′ vM vM′ c
      (ground-cast-target⊑ (C.renameGroundᵐ ηᴿ Gᵍ)
        (C.renameNonStar (toRenameᵗ ηᴿ) Bns)
        (renameᵐᶜ ηᴿ c) p q)

-- Subcase: recursive call returns Δᴿ′ , Δ′ , χs , ... , M⊑N′
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄) q
    | Prog.other B≢G
    | Δᴿ′ , Δ′ , χs , ηᴸ′ , ηᴿ′ , ρ′ , γ′ , A′ ,
      transport⊑ , N′ , vN′ , M′c↠N′ ,
      CTI.rename⊑renameᶜ categorize′ M⊑N′ =
  Δᴿ′ , Δ′ , R.keep R.∷ χs , ηᴸ′ , ηᴿ′ , ρ′ , γ′ ,
  A′ , transport⊑ ,
  N′
    ⟨ applyConsistencies χs
        (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (C.idᵍ Gᵍ)
          ⦃ C.ground-nonstar Gᵍ ⦄) ⟩ ,
  vN′
    《 applyConsistencies-Inert χs
        (inj ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
          ⦃ Gns = C.ground-nonstar Gᵍ ⦄) 》 ,
  ((M′ ⟨ _! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Bns ⦄ ⟩)
    R.—→[ R.keep ]⟨
      R.pure-step
      (R.ground ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
        ⦃ Ans = Bns ⦄ ⦃ Gns = C.ground-nonstar Gᵍ ⦄ vM′ B≢G)
    ⟩
  cast-↠
    (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (C.idᵍ Gᵍ)
      ⦃ C.ground-nonstar Gᵍ ⦄)
    M′c↠N′) ,
  CTI.rename⊑renameᶜ categorize′
    (CTI.⊑castᶜ
      (renameᵐᶜ ηᴿ′
        (applyConsistencies χs
          (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ (C.idᵍ Gᵍ)
            ⦃ C.ground-nonstar Gᵍ ⦄)))
      M⊑N′ (transport⊑ q))

-- Case: c′ = ？_ ⦃ g ⦄ ⦃ ★∼G ⦄ c
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (？_ {G = G} {B = B′} ⦃ g ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q
    with unrename-star-view vM′
      (Prog.canonical-★
        (renameᵗᵐ-preserves-Value ηᴿ vM′)
        (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ))

-- Subcase: target star view is an injected value
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {A = A} {B′ = B′} {p = p}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (？_ {G = G} {B = B′} ⦃ g ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q
    | Prog.sv-tag {W = W} {G = H} {Gᵍ = h} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = Hns ⦄ vW refl
    with G ≟Ty H

-- Subcase: G ≟Ty H = yes refl
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {A = A} {B′ = B′} {p = p}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (？_ {G = G} {B = B′} ⦃ g ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q
    | Prog.sv-tag {W = W} {G = .G} {Gᵍ = h} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = Hns ⦄ vW refl
    | yes refl
    with Prog.from-ground g c

-- Subcase: Prog.from-ground g c = same
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = ._}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (？_ {B = ._} ⦃ g ⦄ ⦃ ★∼G ⦄ .(C.idᵍ g) ⦃ Bns ⦄) q
    | Prog.sv-tag {W = W} {G = ._} {Gᵍ = h} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = Hns ⦄ vW refl
    | yes refl | Prog.same
    rewrite nonStar-unique Bns Hns | ground-unique g h =
  Δᴿ , Δ , R.keep R.∷ R.[] , ηᴸ , ηᴿ , ρ , γ , A ,
  (λ r → r) , W ,
  vW ,
  ((M′ ⟨ ？_ ⦃ Gᵍ = h ⦄ ⦃ ★∼G = ★∼G ⦄ (C.idᵍ h)
      ⦃ Bns = Hns ⦄ ⟩)
    R.—→[ R.keep ]⟨
      R.pure-step
      (R.tag-untag ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = Hns ⦄ vW)
    ⟩
  W R.∎[]) ,
  RII.right-inj-inversion-indexed vM
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) q

-- Subcase: Prog.from-ground g c = other B≢G
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′} {p = p}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (？_ {G = G} {B = B′} ⦃ g ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q
    | Prog.sv-tag {W = W} {G = .G} {Gᵍ = h} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = Hns ⦄ vW refl
    | yes refl | Prog.other B′≢G
    with extra-cast-right
      (RII.right-inj-inversion-indexed vM
        (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ)
        (expand-cast-source⊑ (C.renameGroundᵐ ηᴿ g)
          (C.renameNonStar (toRenameᵗ ηᴿ) Bns)
          (renameᵐᶜ ηᴿ c) p q))
      vM vW c q

-- Subcase: recursive call returns Δᴿ′ , Δ′ , χs , ... , M⊑N′
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′} {p = p}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (？_ {G = G} {B = B′} ⦃ g ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q
    | Prog.sv-tag {W = W} {G = .G} {Gᵍ = h} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = Hns ⦄ vW refl
    | yes refl | Prog.other B′≢G
    | Δᴿ′ , Δ′ , χs , ηᴸ′ , ηᴿ′ , ρ′ , γ′ , A′ ,
      transport⊑ , N′ , vN′ , Wc↠N′ , M⊑N′
    rewrite ground-unique g h
          | sym (nonStar-unique Hns (C.ground-nonstar h)) =
  Δᴿ′ , Δ′ , R.keep R.∷ R.keep R.∷ χs ,
  ηᴸ′ , ηᴿ′ , ρ′ , γ′ , A′ , transport⊑ , N′ , vN′ ,
  (_
    R.—→[ R.keep ]⟨
      R.pure-step
      (R.expand ⦃ Gᵍ = h ⦄ ⦃ ★∼G = ★∼G ⦄
        ⦃ Bns = Bns ⦄ ⦃ Gns = Hns ⦄
        vM′ (λ eq → B′≢G (sym eq)))
    ⟩
  _
    R.—→[ R.keep ]⟨
      (R.ξ-⟨⟩
        (R.pure-step
          (R.tag-untag ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
            ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = Hns ⦄ vW))
        refl)
    ⟩
  Wc↠N′) ,
  M⊑N′

-- Subcase: G ≟Ty H = no G≢H
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {A = A} {B′ = B′} {p = p}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (？_ {G = G} {B = B′} ⦃ g ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) q
    | Prog.sv-tag {W = W} {G = H} {Gᵍ = h} ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = Hns ⦄ vW refl
    | no G≢H =
  ⊥-elim
    (G≢H
      (renameᵗ-injective (toRenameᵗ-injective ηᴿ)
        (ground-targets-unique⊑ (C.renameGroundᵐ ηᴿ g)
          (C.renameGroundᵐ ηᴿ h) A⊑G
          (right-inj-index-forces-indexed g vM
            (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) A⊑G))))
  where
  A⊑G =
    expand-cast-source⊑ (C.renameGroundᵐ ηᴿ g)
      (C.renameNonStar (toRenameᵗ ηᴿ) Bns)
      (renameᵐᶜ ηᴿ c) p q

-- Case: c′ = inst c B≢★
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = Asrc} {B′ = Btgt}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (inst_ {A = Body} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) q
    with unrename-all-value-view vM′
      (Prog.canonical-∀ (renameᵗᵐ-preserves-Value ηᴿ vM′)
        (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ))
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = Asrc} {B′ = Btgt}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′
    (inst_ {A = Body} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) q
    | view =
  inst-catchup-right
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c B≢★ q

-- Case: c′ = gen c A≢★
extra-cast-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′) vM vM′
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) q
    =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vM′ 《 genᵥ A≢★ (gen-safe c A≢★ Bnv z∈B) 》 ,
  ((M′ ⟨ gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★ ⟩) R.∎[]) ,
  CTI.rename⊑renameᶜ categorize
    (CTI.⊑castᶜ
      (renameᵐᶜ ηᴿ (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★))
      M⊑M′ q)

-- Case: c′ = bot-elim
extra-cast-right {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-elim q
    with M⊑M′

-- Subcase: M⊑M′ = rename⊑renameᶜ categorize M⊑M′ᶜ
extra-cast-right {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-elim q
    | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ =
  ⊥-elim
    (Prog.no-bot-value (renameᵗᵐ-preserves-Value ηᴿ vM′)
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ))

-- Case: c′ = bot-intro
extra-cast-right {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    with q

-- Subcase: q = ∀⊑∀ qbody
extra-cast-right {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑∀ qbody
    with M⊑M′

-- Subcase: M⊑M′ = rename⊑renameᶜ categorize M⊑M′ᶜ
extra-cast-right {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑∀ qbody | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ =
  ⊥-elim
    (Prog.no-bot-value (renameᵗᵐ-preserves-Value ηᴸ vM)
      (subst≡
        (λ T → ⟨ _ , _ , _ ⟩ ⊢ renameᵗᵐ ηᴸ M ⦂ `∀ T)
        (PI.imprecision-to-fresh qbody)
        (CTI.cast-term-imprecision-source-typing M⊑M′ᶜ)))

-- Subcase: q = ∀⊑ Anv zero∈A qbody
extra-cast-right {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑ Anv zero∈A qbody =
  ⊥-elim (PI.imprecision-no-star-to-bot refl qbody zero∈A)

-- Inst catch-up helper.  The induction is on the value imprecision proof,
-- following the left ν widening proof shape in the Cambridge notes.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    with vM | vM′

-- Case: both values are type abstractions.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    with M⊑M′ᶜ

-- Subcase: term imprecision = Λ⊑Λᶜ
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑Λᶜ liftγ vRV vRV′ V⊑V′
    with B′
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑Λᶜ liftγ vRV vRV′ V⊑V′
    | ＇ X
    with q
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑Λᶜ liftγ vRV vRV′ V⊑V′
    | ＇ X
    | I.∀⊑ Anv zero∈A qbody = {!!}
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑Λᶜ liftγ vRV vRV′ V⊑V′
    | ‵ ι = {!!}
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑Λᶜ liftγ vRV vRV′ V⊑V′
    | ★ = ⊥-elim (B′≢★ refl)
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑Λᶜ liftγ vRV vRV′ V⊑V′
    | B₁ ⇒ B₂ = {!!}
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑Λᶜ liftγ vRV vRV′ V⊑V′
    | `∀ B″ = {!!}

-- Subcase: term imprecision = Λ⊑ᶜ
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = .(Λ V)} {M′ = .(Λ V′)} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | Λ_ {V = V} vV | Λ_ {V = V′} vV′
    | CTI.Λ⊑ᶜ Anv zero∈A liftγ vRV M′⊢ V⊑M′ = {!!}

-- Remaining value shapes are handled by the recursive cast/reveal/conceal
-- cases of the inst catch-up induction.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | vM₀ | vM′₀
    with view

-- Residual case: target value view is a type abstraction.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | vM₀ | vM′₀ | allv-Λ vW eq = {!!}

-- Residual case: target value view is a universal cast.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | vM₀ | vM′₀ | allv-∀ vW eq = {!!}

-- Residual case: target value view is a gen cast.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | vM₀ | vM′₀ | allv-gen vW A≢★ safe eq = {!!}

-- Residual case: target value view is a universal reveal.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | vM₀ | vM′₀ | allv-reveal vW eq = {!!}

-- Residual case: target value view is a universal conceal.
inst-catchup-right {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B = B} {B′ = B′}
    (CTI.rename⊑renameᶜ categorize M⊑M′ᶜ) vM vM′ view c′ B′≢★ q
    | vM₀ | vM′₀ | allv-conceal vW eq = {!!}
