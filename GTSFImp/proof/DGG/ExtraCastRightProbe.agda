module proof.DGG.ExtraCastRightProbe where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Data.Fin using (zero)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; id; _↦_; ∀ᶜ_; _!; ？_; keep; skip;
   wk↪ᵗ; toRenameᵗ; instᵐ; inst_; gen_; bot-elim; bot-intro;
   renameᵐᶜ; ↑ᶜ_; close-instᶜ)
import Consistency as C
open import Conversion using (〖_,_↑_〗)
open import CastTerms using
  (Term; Value; _⊢_⦂_; ⊢⟨⟩; ⟨_,_,_⟩; ƛ_; Λ_; $; _⦂∀_[_];
   _⟨_⟩; _↑_; _↓_; GenSafe; Inert; inj; fun; all; seal; genᵥ;
   safe-⇒; safe-∀; safe-inst; safe-gen; _《_》; renameᵗᵐ; ⇑ᵗᵐ)
open import Imprecision using (_⊢_⊑_)
import Imprecision as I
import Reduction as R
import GradualTermImprecision as GTI
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.ExtraCastRight as ECR
import proof.DGG.RightInjInversion as RII
open CTI using (_∣_⊢ᶜ_⊑_∶_; _∣_∣_∣_⊢ᶜ_⊑_∶_)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; ground-cast-target⊑; ground-targets-unique⊑;
   ground-target-nonvar-to-star⊑; nonstar-from-≢★;
   renameᵗ-injective; source-occurs-target; toRenameᵗ-injective;
   unshift-nonvar)
import proof.Imprecision as PI
import proof.TypeSafety.Progress as Prog
open import proof.TypeSafety.Progress using (gen-safe)
open import proof.TypeInTermSubst using
  (rename-star-injective; rename-occurs; renameᵗ-wk-eq;
   renameᵗᵐ-preserves-Value)

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
cast-↠ c R.↠-refl = R.↠-refl
cast-↠ {χs = χ R.∷ χs} c (R.↠-step M→N N↠P) =
  R.↠-step (R.ξ-⟨⟩ M→N refl)
    (cast-↠ (R.applyConsistency χ c) N↠P)

applyStoreChange-Inert : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (χ : R.StoreChange Δ Δ′)
  → Inert c
  → Inert (R.applyConsistency χ c)
applyStoreChange-Inert R.keep inert = inert
applyStoreChange-Inert (R.bind A)
    (inj ⦃ g = C.g-⇒ ⦄ ⦃ Gns = Gns ⦄ ⦃ match = match ⦄)
    rewrite C.groundMatch-unique match C.match-⇒ =
  inj ⦃ g = C.g-⇒ ⦄ ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
    ⦃ match = C.match-⇒ ⦄
applyStoreChange-Inert (R.bind A)
    (inj ⦃ g = C.g-ι ⦄ ⦃ Gns = Gns ⦄ ⦃ match = match ⦄)
    rewrite C.groundMatch-unique match C.match-ι =
  inj ⦃ g = C.g-ι ⦄ ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
    ⦃ match = C.match-ι ⦄
applyStoreChange-Inert (R.bind A)
    (inj ⦃ g = C.g-X eq ⦄ ⦃ Gns = Gns ⦄ ⦃ match = match ⦄)
    rewrite C.groundMatch-unique match C.match-X =
  inj ⦃ g = C.g-X eq ⦄ ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
    ⦃ match = C.match-X ⦄
applyStoreChange-Inert (R.bind A)
    (inj ⦃ g = C.g-∀ ⦄ ⦃ Gns = Gns ⦄ ⦃ match = match ⦄)
    rewrite C.groundMatch-unique match C.match-∀ =
  inj ⦃ g = C.g-∀ ⦄ ⦃ Gns = C.renameNonStar Fin.suc Gns ⦄
    ⦃ match = C.match-∀ ⦄
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

right-inj-index-forces-core : ∀ {Δ} {ρ : CTI.StoreImp Δ}
    {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M W : Term Δ} {A G H : Ty Δ} {ν κ : Env∼ Δ}
    {r : C.Var∼}
    {gH : C.Groundʳ κ C.X∼★ H}
    {Hns : NonStar H} {hmatch : C.GroundMatch gH H}
    {cH : κ ⊢ H ∼ H}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ ★}
  → (gG : C.Groundʳ ν r G)
  → Value M
  → ρ ∣ γ ⊢ᶜ M
      ⊑ W ⟨ _! ⦃ gH ⦄ cH ⦃ Hns ⦄ ⦃ hmatch ⦄ ⟩
      ∶ p
  → CTI.impEnvⁱ ρ ⊢ A ⊑ G
  → CTI.impEnvⁱ ρ ⊢ A ⊑ H
right-inj-index-forces-core gG vM
    (CTI.⊑castᶜ {p = A⊑H} c′ M⊑W A⊑★) A⊑G =
  A⊑H
right-inj-index-forces-core () (vM 《 inj 》)
    (CTI.cast⊑castᶜ c c′ M⊑W A⊑★) I.★⊑★
right-inj-index-forces-core {gH = C.g-⇒} C.g-⇒
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
    {ν = νG} {κ = κH} {r = rG} {gH = gH} {cH = cH}
    C.g-⇒ (vM 《 fun 》)
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
      {G = ★ ⇒ ★} {ν = νG} {κ = κH} {r = rG}
      {gH = gH} {cH = cH}
      C.g-⇒ vM M⊑W! A₀⊑G

  eq : ★ ⇒ ★ ≡ H
  eq = ground-targets-unique⊑ {ν = νG} {κ = κH}
    {r = rG} C.g-⇒ gH A₀⊑G A₀⊑H
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
    {ν = νG} {κ = κH} {r = rG} {gH = gH} {cH = cH}
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
        {ν = C.renameEnv∼ wk↪ᵗ νG}
        {κ = C.renameEnv∼ wk↪ᵗ κH} {r = rG}
        (ECR.rename-groundʳ wk↪ᵗ gG) vV V⊑⇑W!
        (subst≡ (λ T → I.instᵐ (CTI.impEnvⁱ ρ) ⊢ A₀ ⊑ T)
          (sym (renameᵗ-wk-eq G)) A₀⊑⇑G)))
right-inj-index-forces-core C.g-∀ (Λ vV₀)
    (CTI.Λ⊑ᶜ Anv zero∈A liftγ vV W!⊢ V⊑⇑W!)
    (I.∀⊑∀ A⊑★)
    with source-occurs-target refl A⊑★ zero∈A
right-inj-index-forces-core C.g-∀ (Λ vV₀)
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
    {A : Ty Δ} {G H : Ty Δᴿ} {ν κ : Env∼ Δᴿ}
    {r : C.Var∼}
    {gH : C.Groundʳ κ C.X∼★ H}
    {Hns : NonStar H} {hmatch : C.GroundMatch gH H}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ ★}
  → (gG : C.Groundʳ ν r G)
  → Value M
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M
      ⊑ W ⟨ _! ⦃ gH ⦄ (C.idᵍ gH) ⦃ Hns ⦄ ⦃ hmatch ⦄ ⟩
      ∶ p
  → CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) G
  → CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) H
right-inj-index-forces-indexed {ηᴿ = ηᴿ} gG vM
    (CTI.rename⊑renameᶜ categorize M⊑W!) A⊑G =
  right-inj-index-forces-core (ECR.rename-groundʳ ηᴿ gG)
    (renameᵗᵐ-preserves-Value _ vM) M⊑W! A⊑G

extra-cast-right-top-partial : ∀ {Δᴸ Δᴿ Δ}
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
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (id a) q
    with ECR.extra-cast-right-idᶜ M⊑M′ vM vM′ a q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (id a) q
    | M′c′↠N′ , M⊑N′ =
  Δᴿ , Δ , _ , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vM′ , M′c′↠N′ , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (c ↦ d) q
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′ (c ↦ d) fun q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (c ↦ d) q
    | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vN′ , R.↠-refl , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (∀ᶜ c) q
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′ (∀ᶜ c) all q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′ (∀ᶜ c) q
    | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vN′ , R.↠-refl , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    with Prog.to-ground g match c
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same
    rewrite nonStar-unique Bns (C.ground-nonstar g)
          | C.groundMatch-unique match (C.ground-match g)
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′
      (_! ⦃ g = g ⦄ (C.idᵍ g)
        ⦃ Ans = C.ground-nonstar g ⦄
        ⦃ match = C.ground-match g ⦄)
      (inj ⦃ g = g ⦄ ⦃ Gns = C.ground-nonstar g ⦄
           ⦃ match = C.ground-match g ⦄)
      q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vN′ , R.↠-refl , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {p = p}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G
    with extra-cast-right-top-partial M⊑M′ vM vM′ c
      (ground-cast-target⊑ (ECR.rename-groundʳ ηᴿ g)
        (C.renameNonStar (toRenameᵗ ηᴿ) Bns)
        (renameᵐᶜ ηᴿ c) p q)
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A}
    M⊑M′ vM vM′ (_! ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G
    | Δᴿ′ , Δ′ , χs , ηᴸ′ , ηᴿ′ , ρ′ , γ′ , A′ ,
      transport⊑ , N′ , vN′ , M′c↠N′ , M⊑N′ =
  Δᴿ′ , Δ′ , R.keep R.∷ χs , ηᴸ′ , ηᴿ′ , ρ′ , γ′ ,
  A′ , transport⊑ ,
  N′
    ⟨ applyConsistencies χs
        (_! ⦃ g = g ⦄ (C.idᵍ g)
          ⦃ Ans = C.ground-nonstar g ⦄
          ⦃ match = C.ground-match g ⦄) ⟩ ,
  vN′
    《 applyConsistencies-Inert χs
        (inj ⦃ g = g ⦄ ⦃ Gns = C.ground-nonstar g ⦄
          ⦃ match = C.ground-match g ⦄) 》 ,
  R.↠-step
    (R.pure-step
      (R.ground ⦃ g = g ⦄ ⦃ Ans = Bns ⦄ ⦃ match = match ⦄
        ⦃ Gns = C.ground-nonstar g ⦄
        ⦃ gmatch = C.ground-match g ⦄ vM′ B≢G))
    (cast-↠
      (_! ⦃ g = g ⦄ (C.idᵍ g)
        ⦃ Ans = C.ground-nonstar g ⦄
        ⦃ match = C.ground-match g ⦄)
      M′c↠N′) ,
  proj₂
    (ECR.extra-cast-right-inertᶜ M⊑N′ vM vN′
      (applyConsistencies χs
        (_! ⦃ g = g ⦄ (C.idᵍ g)
          ⦃ Ans = C.ground-nonstar g ⦄
          ⦃ match = C.ground-match g ⦄))
      (applyConsistencies-Inert χs
        (inj ⦃ g = g ⦄ ⦃ Gns = C.ground-nonstar g ⦄
          ⦃ match = C.ground-match g ⦄))
      (transport⊑ q))
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    with Prog.from-ground g match c
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same
    with vM′ | M⊑M′
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | ƛ N | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (ƛ N))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | ƛ N | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vW ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | $ κ | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ ($ κ))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | $ κ | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vW ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | Λ_ {V = V} vV
    | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (Λ vV))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | Λ vV | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vW ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW 《 fun 》 | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW 《 fun 》))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW 《 fun 》 | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW 《 all 》 | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW 《 all 》))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW 《 all 》 | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW 《 genᵥ A≠★ safe 》
    | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW 《 genᵥ A≠★ safe 》))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW 《 genᵥ A≠★ safe 》
    | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↑ fun | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW ↑ fun))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↑ fun | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↑ all | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW ↑ all))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↑ all | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↓ seal | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW ↓ seal))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↓ seal | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↓ fun | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW ↓ fun))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↓ fun | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ}
    M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↓ all | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    with Prog.canonical-★
      (renameᵗᵐ-preserves-Value ηᴿ (vW ↓ all))
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ)
extra-cast-right-top-partial M⊑M′ vM vM′
    (？_ ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same | vW ↓ all | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ
    | Prog.sv-tag vU ()
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same
    | _《_》 {V = W} vW
        (inj {G = H} ⦃ g = h ⦄ ⦃ Gns = Hns ⦄
          ⦃ match = hmatch ⦄)
    | M⊑M′tag
    with B′ ≟Ty H
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {A = A} {B′ = ._}
    M⊑M′ vM vM′
    (？_ {B = ._} ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same
    | _《_》 {V = W} vW
        (inj {G = H} ⦃ g = h ⦄ ⦃ Gns = Hns ⦄
          ⦃ match = hmatch ⦄)
    | M⊑M′tag | yes refl
    rewrite nonStar-unique Bns Hns =
  Δᴿ , Δ , R.keep R.∷ R.[] , ηᴸ , ηᴿ , ρ , γ , A ,
  (λ r → r) , W ,
  vW ,
  R.↠-step
    (R.pure-step
      (R.tag-untag
        ⦃ g = h ⦄ ⦃ h = g ⦄
        ⦃ Gns = Hns ⦄
        ⦃ gmatch = hmatch ⦄
        ⦃ hmatch = match ⦄ vW))
    R.↠-refl ,
  RII.right-inj-inversion-indexed vM M⊑M′tag q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ .(C.idᵍ g) ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.same
    | _《_》 {V = W} vW
        (inj {G = H} ⦃ g = h ⦄ ⦃ Gns = Hns ⦄
          ⦃ match = hmatch ⦄)
    | M⊑M′tag | no B′≢H =
  ⊥-elim
    (B′≢H
      (renameᵗ-injective (toRenameᵗ-injective ηᴿ)
        (ground-targets-unique⊑ (ECR.rename-groundʳ ηᴿ g)
          (ECR.rename-groundʳ ηᴿ h) q
          (right-inj-index-forces-indexed g vM M⊑M′tag q))))
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G
    with ECR.extra-cast-right-expandᶜ M⊑M′ vM vM′
      c Bns match (λ eq → B≢G (sym eq)) q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (？_ {B = B′} ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) q
    | Prog.other B≢G | M′c′↠N′ , M⊑N′ =
  Δᴿ , Δ , R.keep R.∷ R.[] , ηᴸ , ηᴿ , ρ , γ , A ,
  (λ r → r) , _ , {!!} , M′c′↠N′ , M⊑N′
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ}
    {M = M} {M′ = M′} {A = Asrc} {B′ = Btgt}
    M⊑M′ vM vM′
    (inst_ {A = Body} ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) q =
  suc Δᴿ , suc Δ , R.bind ★ R.∷ R.[] ,
  skip ηᴸ , keep ηᴿ , CTI.rightOnly★StoreImp ρ , {!!} ,
  ⇑ᵗ Asrc , {!!} ,
  (⇑ᵗᵐ M′ ⦂∀ R.applyBody (R.bind ★) Body [ ＇ zero ]
    ↑ 〖 zero , ★ ↑ Body 〗)
    ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩ ,
  {!!} ,
  R.↠-step (R.β-inst vM′ B≢★) R.↠-refl ,
  {!!}
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) q
    with ECR.extra-cast-right-inertᶜ M⊑M′ vM vM′
      (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★)
      (genᵥ A≢★ (gen-safe c A≢★ Bnv z∈B)) q
extra-cast-right-top-partial {Δᴿ = Δᴿ} {Δ = Δ}
    {ηᴸ = ηᴸ} {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′} {A = A} {B′ = B′}
    M⊑M′ vM vM′
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) q
    | vN′ , M⊑N′ =
  Δᴿ , Δ , R.[] , ηᴸ , ηᴿ , ρ , γ , A , (λ r → r) , _ ,
  vN′ , R.↠-refl , M⊑N′
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-elim q
    with M⊑M′
extra-cast-right-top-partial {ηᴿ = ηᴿ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-elim q
    | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ =
  ⊥-elim
    (Prog.no-bot-value (renameᵗᵐ-preserves-Value ηᴿ vM′)
      (CTI.cast-term-imprecision-target-typing M⊑M′ᶜ))
extra-cast-right-top-partial {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    with q
extra-cast-right-top-partial {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑∀ qbody
    with M⊑M′
extra-cast-right-top-partial {ηᴸ = ηᴸ} {ρ = ρ} {γ = γ}
    {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑∀ qbody | CTI.rename⊑renameᶜ categorize M⊑M′ᶜ =
  ⊥-elim
    (Prog.no-bot-value (renameᵗᵐ-preserves-Value ηᴸ vM)
      (subst≡
        (λ T → ⟨ _ , _ , _ ⟩ ⊢ renameᵗᵐ ηᴸ M ⦂ `∀ T)
        (PI.imprecision-to-fresh qbody)
        (CTI.cast-term-imprecision-source-typing M⊑M′ᶜ)))
extra-cast-right-top-partial {M = M} {M′ = M′}
    M⊑M′ vM vM′ bot-intro q
    | I.∀⊑ Anv zero∈A qbody =
  ⊥-elim (PI.imprecision-no-star-to-bot refl qbody zero∈A)

β-inst-body-hole : ∀ {Δ}
    {ρ : CTI.StoreImp Δ}
    {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {γ∀ : GTI.CtxImp (I.extᵐ (CTI.impEnvⁱ ρ))}
    {γ★ : GTI.CtxImp (I.instᵐ (CTI.impEnvⁱ ρ))}
    {γbody : GTI.CtxImp (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ)))}
    {V V′ : Term (suc Δ)}
    {A B : Ty (suc Δ)}
    {A★ : Ty (suc (suc Δ))}
    {B′ : Ty (suc Δ)}
    {M : Term (suc Δ)}
    {p : I.extᵐ (CTI.impEnvⁱ ρ) ⊢ A ⊑ B}
    {pBody : I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))
      ⊢ A★ ⊑ ⇑ᵗ B′}
  → (Anv★ : NonVar A★)
  → (zero∈A★ : zero ∈ᵗ A★)
  → GTI.LiftCtxⁱ (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))) γ★ γbody
  → Value V
  → Value V′
  → CTI.liftStoreImp I.X⊑X ρ ∣ γ∀ ⊢ᶜ V ⊑ V′ ∶ p
  → ⟨ suc Δ , CTI.targetStoreⁱ (CTI.rightOnly★StoreImp ρ) ,
        GTI.tgtCtxⁱ γ★ ⟩ ⊢ M ⦂ B′
  → CTI.rightOnly★StoreImp ρ ∣ γ★
      ⊢ᶜ Λ (renameᵗᵐ (keep wk↪ᵗ) V) ⊑ M
      ∶ I.∀⊑ Anv★ zero∈A★ pBody
β-inst-body-hole Anv★ zero∈A★ liftγbody vV vV′ V⊑V′ M⊢ =
  CTI.Λ⊑ᶜ Anv★ zero∈A★ liftγbody
    (renameᵗᵐ-preserves-Value (keep wk↪ᵗ) vV)
    M⊢
    {!!}

β-inst-extra-cast-right-partial : ∀ {Δ}
    {ρ : CTI.StoreImp Δ}
    {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {γ∀ : GTI.CtxImp (I.extᵐ (CTI.impEnvⁱ ρ))}
    {γ★ : GTI.CtxImp (I.instᵐ (CTI.impEnvⁱ ρ))}
    {γbody : GTI.CtxImp (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ)))}
    {V V′ : Term (suc Δ)}
    {A B : Ty (suc Δ)}
    {B′ : Ty Δ}
    {A★ : Ty (suc (suc Δ))}
    {ν : Env∼ Δ}
    ⦃ Bnv : NonVar B ⦄
    ⦃ zero∈B : zero ∈ᵗ B ⦄
    {c : instᵐ ν ⊢ B ∼ ⇑ᵗ B′}
    {B′≢★ : B′ ≢ ★}
    {p : I.extᵐ (CTI.impEnvⁱ ρ) ⊢ A ⊑ B}
    {pBody : I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))
      ⊢ A★ ⊑ ⇑ᵗ (⇑ᵗ B′)}
  → (Anv★ : NonVar A★)
  → (zero∈A★ : zero ∈ᵗ A★)
  → GTI.LiftCtxⁱ (I.instᵐ (I.instᵐ (CTI.impEnvⁱ ρ))) γ★ γbody
  → Value V
  → Value V′
  → CTI.liftStoreImp I.X⊑X ρ ∣ γ∀ ⊢ᶜ V ⊑ V′ ∶ p
  → ⟨ suc Δ , CTI.targetStoreⁱ (CTI.rightOnly★StoreImp ρ) ,
        GTI.tgtCtxⁱ γ★ ⟩
      ⊢ (⇑ᵗᵐ (Λ V′) ⦂∀ R.applyBody (R.bind ★) B [ ＇ zero ]
          ↑ 〖 zero , ★ ↑ B 〗)
        ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩ ⦂ ⇑ᵗ B′
  → ((Λ V′) ⟨ (inst c) B′≢★ ⟩
       R.—↠[ R.bind ★ R.∷ R.[] ]
     (⇑ᵗᵐ (Λ V′) ⦂∀ R.applyBody (R.bind ★) B [ ＇ zero ]
       ↑ 〖 zero , ★ ↑ B 〗)
       ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩)
    ×
    (CTI.rightOnly★StoreImp ρ ∣ γ★
      ⊢ᶜ Λ (renameᵗᵐ (keep wk↪ᵗ) V)
        ⊑ (⇑ᵗᵐ (Λ V′) ⦂∀ R.applyBody (R.bind ★) B [ ＇ zero ]
             ↑ 〖 zero , ★ ↑ B 〗)
           ⟨ ↑ᶜ (c [ ★/0 ]ᶜ) ⟩
        ∶ I.∀⊑ Anv★ zero∈A★ pBody)
β-inst-extra-cast-right-partial {B′≢★ = B′≢★}
    Anv★ zero∈A★ liftγbody vV vV′ V⊑V′ reduct⊢ =
  R.↠-step (R.β-inst (Λ vV′) B′≢★) R.↠-refl
  , CTI.Λ⊑ᶜ Anv★ zero∈A★ liftγbody
      (renameᵗᵐ-preserves-Value (keep wk↪ᵗ) vV)
      reduct⊢
      {!!}
