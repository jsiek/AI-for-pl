module proof.DGG.ExtraCastRight where

-- File Charter:
--   * Proves the indexed-by-renamings form of the extra-cast-on-the-right
--     cast-term imprecision lemma.
--   * Keeps the cast evidence local to the right type context and lifts it
--     through the right embedding before using the core right-cast rule.
--   * Depends only on the cast-term imprecision relation and consistency
--     renaming.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; id; _!; ？_; toRenameᵗ; renameᵐᶜ)
import Consistency as C
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _《_》)
open import Imprecision using (_⊢_⊑_)
import Imprecision as I
import Reduction as R
import GradualTermImprecision as GTI
open import proof.Imprecision using (⊑-unique)
open import proof.ImprecisionConsistency using
  (shift-occurs; source-occurs-target; target-occurs-source;
   unshift-occurs)
import proof.DGG.CastTermImprecision as CTI

open CTI using
  ( StoreImp
  ; impEnvⁱ
  ; _∣_∣_∣_⊢ᶜ_⊑_∶_
  )

rename-groundʳ : ∀ {Δ Δ′ ν r G}
  → (η : Δ ↪ᵗ Δ′)
  → C.Groundʳ ν r G
  → C.Groundʳ (C.renameEnv∼ η ν) r (renameᵗ (toRenameᵗ η) G)
rename-groundʳ η C.g-⇒ = C.g-⇒
rename-groundʳ η C.g-ι = C.g-ι
rename-groundʳ {ν = ν} η (C.g-X {X = X} eq) =
  C.g-X (trans (C.renameEnv∼-preserves η ν X) eq)
rename-groundʳ η C.g-∀ = C.g-∀

var∼-self-not-star : C.X∼X ≡ C.X∼★ → ⊥
var∼-self-not-star ()

ground-self-occurs⊥ : ∀ {Δ : TyCtx} {ν : Env∼ Δ} {X : TyVar Δ}
    {G : Ty Δ}
  → ν X ≡ C.X∼X
  → C.Groundʳ {Δ} ν C.X∼★ G
  → X ∈ᵗ G
  → ⊥
ground-self-occurs⊥ same C.g-⇒ (∈-fun-left ())
ground-self-occurs⊥ same C.g-⇒ (∈-fun-right X∉A ())
ground-self-occurs⊥ same C.g-ι ()
ground-self-occurs⊥ same (C.g-X eq) var-∈ =
  var∼-self-not-star (trans (sym same) eq)
ground-self-occurs⊥ same C.g-∀ (∈-all ())

consistency-source-occurs-target : ∀ {Δ : TyCtx} {ν : Env∼ Δ}
    {X : TyVar Δ} {A B : Ty Δ}
  → ν X ≡ C.X∼X
  → ν ⊢ A ∼ B
  → X ∈ᵗ A
  → X ∈ᵗ B
consistency-source-occurs-target same (id a) X∈A = X∈A
consistency-source-occurs-target {A = A ⇒ B} {B = A′ ⇒ B′}
    same (c C.↦ d) (∈-fun-left X∈A) =
  ∈-fun-left (consistency-source-occurs-target same c X∈A)
consistency-source-occurs-target {X = X} {A = A ⇒ B}
    {B = A′ ⇒ B′} same (c C.↦ d) (∈-fun-right X∉A X∈B)
    with occurs? X A′
consistency-source-occurs-target {X = X} {A = A ⇒ B}
    {B = A′ ⇒ B′} same (c C.↦ d) (∈-fun-right X∉A X∈B)
    | present X∈A′ = ∈-fun-left X∈A′
consistency-source-occurs-target {X = X} {A = A ⇒ B}
    {B = A′ ⇒ B′} same (c C.↦ d) (∈-fun-right X∉A X∈B)
    | absent X∉A′ =
  ∈-fun-right X∉A′ (consistency-source-occurs-target same d X∈B)
consistency-source-occurs-target {X = X} {A = `∀ A} {B = `∀ B}
    same (C.∀ᶜ c) (∈-all X∈A) =
  ∈-all (consistency-source-occurs-target {X = suc X} same c X∈A)
consistency-source-occurs-target {B = ★} same
    (_! ⦃ g ⦄ c ⦃ Ans ⦄ ⦃ match ⦄) X∈A =
  ⊥-elim (ground-self-occurs⊥ same g
    (consistency-source-occurs-target same c X∈A))
consistency-source-occurs-target {A = ★} same
    (C.？_ ⦃ g ⦄ c ⦃ Bns ⦄ ⦃ match ⦄) ()
consistency-source-occurs-target {X = X} {A = `∀ A} same
    (C.inst_ ⦃ Anv ⦄ ⦃ z∈A ⦄ c B≢★) (∈-all X∈A) =
  unshift-occurs
    (consistency-source-occurs-target {X = suc X} same c X∈A)
consistency-source-occurs-target {X = X} {B = `∀ B} same
    (C.gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) X∈A =
  ∈-all (consistency-source-occurs-target {X = suc X} same c
    (shift-occurs X∈A))
consistency-source-occurs-target {A = `∀ (＇ zero)}
    same C.bot-elim (∈-all ())
consistency-source-occurs-target {A = `∀ ★}
    same C.bot-intro (∈-all ())

lift-groundʳ : ∀ {Δ μ r G}
  → C.Groundʳ {Δ} μ r G
  → C.Groundʳ (C.extᵐ μ) r (⇑ᵗ G)
lift-groundʳ C.g-⇒ = C.g-⇒
lift-groundʳ C.g-ι = C.g-ι
lift-groundʳ (C.g-X eq) = C.g-X eq
lift-groundʳ C.g-∀ = C.g-∀

inst-groundʳ : ∀ {Δ μ r G}
  → C.Groundʳ {Δ} μ r G
  → C.Groundʳ (C.instᵐ μ) r (⇑ᵗ G)
inst-groundʳ C.g-⇒ = C.g-⇒
inst-groundʳ C.g-ι = C.g-ι
inst-groundʳ (C.g-X eq) = C.g-X eq
inst-groundʳ C.g-∀ = C.g-∀

lift-ground-match : ∀ {Δ μ r G B} {g : C.Groundʳ {Δ} μ r G}
  → C.GroundMatch g B
  → C.GroundMatch (lift-groundʳ g) (⇑ᵗ B)
lift-ground-match C.match-⇒ = C.match-⇒
lift-ground-match C.match-ι = C.match-ι
lift-ground-match C.match-X = C.match-X
lift-ground-match C.match-∀ = C.match-∀

weaken-star-map-ext : ∀ {Δ} {μ ν : I.ImpEnv Δ}
  → (∀ X → μ X ≡ I.X⊑★ → ν X ≡ I.X⊑★)
  → ∀ X → I.extᵐ μ X ≡ I.X⊑★ → I.extᵐ ν X ≡ I.X⊑★
weaken-star-map-ext h zero ()
weaken-star-map-ext h (suc X) eq = h X eq

weaken-star-map-inst : ∀ {Δ} {μ ν : I.ImpEnv Δ}
  → (∀ X → μ X ≡ I.X⊑★ → ν X ≡ I.X⊑★)
  → ∀ X → I.instᵐ μ X ≡ I.X⊑★ → I.instᵐ ν X ≡ I.X⊑★
weaken-star-map-inst h zero eq = refl
weaken-star-map-inst h (suc X) eq = h X eq

imp-env-weaken : ∀ {Δ} {μ ν : I.ImpEnv Δ} {A B : Ty Δ}
  → (∀ X → μ X ≡ I.X⊑★ → ν X ≡ I.X⊑★)
  → μ ⊢ A ⊑ B
  → ν ⊢ A ⊑ B
imp-env-weaken h I.★⊑★ = I.★⊑★
imp-env-weaken h I.ι⊑ι = I.ι⊑ι
imp-env-weaken h I.X⊑X = I.X⊑X
imp-env-weaken h (I.⇒⊑⇒ A⊑B C⊑D) =
  I.⇒⊑⇒ (imp-env-weaken h A⊑B) (imp-env-weaken h C⊑D)
imp-env-weaken h (I.∀⊑∀ A⊑B) =
  I.∀⊑∀ (imp-env-weaken (weaken-star-map-ext h) A⊑B)
imp-env-weaken h (I.⇒⊑★ A⊑★ B⊑★) =
  I.⇒⊑★ (imp-env-weaken h A⊑★) (imp-env-weaken h B⊑★)
imp-env-weaken h I.ι⊑★ = I.ι⊑★
imp-env-weaken h (I.X⊑★ x⊑★) = I.X⊑★ (h _ x⊑★)
imp-env-weaken h (I.∀⊑ Anv zero∈A A⊑B) =
  I.∀⊑ Anv zero∈A
    (imp-env-weaken (weaken-star-map-inst h) A⊑B)
imp-env-weaken h I.∀★⊑★ = I.∀★⊑★
imp-env-weaken h (I.∀⊑★ Ans A⊑★) =
  I.∀⊑★ Ans (imp-env-weaken (weaken-star-map-ext h) A⊑★)
imp-env-weaken h I.bot-elim = I.bot-elim
imp-env-weaken h I.bot⊑★ = I.bot⊑★

ext-to-inst-star-map : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X → I.extᵐ μ X ≡ I.X⊑★ → I.instᵐ μ X ≡ I.X⊑★
ext-to-inst-star-map zero ()
ext-to-inst-star-map (suc X) eq = eq

nonvar-occurs-nonstar : ∀ {Δ X} {A : Ty Δ}
  → NonVar A
  → X ∈ᵗ A
  → NonStar A
nonvar-occurs-nonstar nonvar-base ()
nonvar-occurs-nonstar nonvar-star ()
nonvar-occurs-nonstar nonvar-fun X∈A = nonstar-⇒
nonvar-occurs-nonstar nonvar-all X∈A = nonstar-∀

zero-not-consistent-shift-ground : ∀ {Δ ν G}
  → C.Groundʳ {Δ} ν C.X∼★ G
  → C.instᵐ ν ⊢ ＇ zero ∼ ⇑ᵗ G
  → ⊥
zero-not-consistent-shift-ground C.g-⇒ ()
zero-not-consistent-shift-ground C.g-ι ()
zero-not-consistent-shift-ground (C.g-X eq) ()
zero-not-consistent-shift-ground C.g-∀
    (C.gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≢★)

var-star-universal-ground : ∀ {Δ} {φ ψ : I.ImpEnv Δ}
    {X : TyVar Δ} {A : Ty Δ}
  → φ X ≡ I.X⊑X
  → ψ X ≡ I.X⊑★
  → φ ⊢ A ⊑ ＇ X
  → ψ ⊢ A ⊑ ★
  → NonVar A
  → ψ ⊢ A ⊑ `∀ ★
var-star-universal-ground same to-star I.X⊑X A⊑★ ()
var-star-universal-ground same to-star
    (I.∀⊑ Anv () A⊑X) I.∀★⊑★ nonvar-all
var-star-universal-ground same to-star
    (I.∀⊑ Anv zero∈A A⊑X) (I.∀⊑★ Ans A⊑★) nonvar-all =
  I.∀⊑∀ A⊑★
var-star-universal-ground same to-star
    (I.∀⊑ Anv zero∈A A⊑X)
    (I.∀⊑ Bnv zero∈B A⊑★) nonvar-all =
  I.∀⊑ Bnv zero∈B
    (var-star-universal-ground same to-star A⊑X A⊑★ Bnv)
var-star-universal-ground same to-star
    (I.∀⊑ () zero∈A A⊑X) I.bot⊑★ nonvar-all

ground-cast-target⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {ν : Env∼ Δ}
    {A B G : Ty Δ}
  → (g : C.Groundʳ ν C.X∼★ G)
  → NonStar B
  → ν ⊢ B ∼ G
  → μ ⊢ A ⊑ B
  → μ ⊢ A ⊑ ★
  → μ ⊢ A ⊑ G
ground-cast-target⊑ g () c I.★⊑★ I.★⊑★
ground-cast-target⊑ g Bns (id (‵ ι)) I.ι⊑ι I.ι⊑★ =
  I.ι⊑ι
ground-cast-target⊑ g () c I.ι⊑★ I.ι⊑★
ground-cast-target⊑ g Bns (id (＇ X)) I.X⊑X (I.X⊑★ x⊑★) =
  I.X⊑X
ground-cast-target⊑ g () c (I.X⊑★ x⊑★) (I.X⊑★ x⊑★′)
ground-cast-target⊑ C.g-⇒ Bns (c₁ C.↦ c₂)
    (I.⇒⊑⇒ A⊑B C⊑D) (I.⇒⊑★ A⊑★ C⊑★) =
  I.⇒⊑⇒ A⊑★ C⊑★
ground-cast-target⊑ g () c (I.⇒⊑★ A⊑★ B⊑★)
    (I.⇒⊑★ A⊑★′ B⊑★′)
ground-cast-target⊑ g Bns c
    (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑ Anv′ zero∈A′ A⊑★) =
  I.∀⊑ Anv zero∈A
    (ground-cast-target⊑ (lift-groundʳ g) (C.renameNonStar suc Bns)
      (C.renameEnvᶜ suc (λ X → refl) c) A⊑B A⊑★)
ground-cast-target⊑ g Bns c
    (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑★ Ans A⊑★)
    with source-occurs-target refl A⊑★ zero∈A
ground-cast-target⊑ g Bns c
    (I.∀⊑ Anv zero∈A A⊑B) (I.∀⊑★ Ans A⊑★)
    | ()
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★) =
  I.∀⊑ Anv zero∈A
    (ground-cast-target⊑ (inst-groundʳ g)
      (nonvar-occurs-nonstar Bnv zero∈B) c
      (imp-env-weaken ext-to-inst-star-map A⊑B) A⊑★)
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) I.∀★⊑★
    with target-occurs-source A⊑B zero∈B
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) I.∀★⊑★
    | ()
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    with target-occurs-source A⊑B zero∈B
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A with source-occurs-target refl A⊑★ zero∈A
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A | ()
ground-cast-target⊑ g Bns
    (C.inst_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c B≢★)
    (I.∀⊑∀ I.X⊑X) I.bot⊑★ =
  ⊥-elim (zero-not-consistent-shift-ground g c)
ground-cast-target⊑ C.g-∀ Bns
    (C.gen_ ⦃ Bnv ⦄ ⦃ () ⦄ c A≢★) A⊑B A⊑★
ground-cast-target⊑ C.g-∀ Bns (C.∀ᶜ c)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★)
    with source-occurs-target refl A⊑B zero∈A
ground-cast-target⊑ C.g-∀ Bns (C.∀ᶜ c)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★)
    | zero∈B with consistency-source-occurs-target refl c zero∈B
ground-cast-target⊑ C.g-∀ Bns (C.∀ᶜ c)
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★)
    | zero∈B | ()
ground-cast-target⊑ C.g-∀ Bns (C.∀ᶜ c)
    A⊑B I.∀★⊑★ =
  I.∀⊑∀ I.★⊑★
ground-cast-target⊑ C.g-∀ Bns (C.∀ᶜ c)
    A⊑B (I.∀⊑★ Ans A⊑★) =
  I.∀⊑∀ A⊑★
ground-cast-target⊑ C.g-∀ Bns (C.∀ᶜ c)
    A⊑B I.bot⊑★ =
  I.bot-elim
ground-cast-target⊑ C.g-∀ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    with target-occurs-source A⊑B var-∈
ground-cast-target⊑ C.g-∀ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A with source-occurs-target refl A⊑★ zero∈A
ground-cast-target⊑ C.g-∀ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑★ Ans A⊑★)
    | zero∈A | ()
ground-cast-target⊑ C.g-∀ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) (I.∀⊑ Anv zero∈A A⊑★) =
  I.∀⊑ Anv zero∈A
    (var-star-universal-ground refl refl A⊑B A⊑★ Anv)
ground-cast-target⊑ C.g-∀ Bns C.bot-elim
    (I.∀⊑∀ A⊑B) I.bot⊑★ =
  I.bot-elim

expand-cast-source⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {ν : Env∼ Δ}
    {A B G : Ty Δ}
  → (g : C.Groundʳ ν C.★∼X G)
  → NonStar B
  → ν ⊢ G ∼ B
  → μ ⊢ A ⊑ ★
  → μ ⊢ A ⊑ B
  → μ ⊢ A ⊑ G
expand-cast-source⊑ g Bns c A⊑★ A⊑B =
  ground-cast-target⊑ (C.flip-Groundʳ g) Bns (C.sym∼ c) A⊑B A⊑★

extra-cast-rightᶜ′ : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : StoreImp Δ} {γ : GTI.CtxImp (impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → (c′ : ν ⊢ B ∼ B′)
  → (q : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B′)
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ⟨ c′ ⟩ ∶ q
extra-cast-rightᶜ′ {ηᴿ = ηᴿ}
    (CTI.rename⊑renameᶜ categorize M⊑M′) c′ q =
  CTI.rename⊑renameᶜ categorize
    (CTI.⊑castᶜ (renameᵐᶜ ηᴿ c′) M⊑M′ q)

extra-cast-rightᶜ : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : StoreImp Δ} {γ : GTI.CtxImp (impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → (q : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B′)
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ⟨ c′ ⟩ ∶ q
extra-cast-rightᶜ M⊑M′ vM vM′ c′ q =
  extra-cast-rightᶜ′ M⊑M′ c′ q

extra-cast-right-inertᶜ : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : StoreImp Δ} {γ : GTI.CtxImp (impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ B′)
  → Inert c′
  → (q : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B′)
  → Value (M′ ⟨ c′ ⟩)
    × ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ⟨ c′ ⟩ ∶ q
extra-cast-right-inertᶜ M⊑M′ vM vM′ c′ inert q =
  (vM′ 《 inert 》) , extra-cast-rightᶜ M⊑M′ vM vM′ c′ q

extra-cast-right-idᶜ : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : StoreImp Δ} {γ : GTI.CtxImp (impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (a : Atom B)
  → (q : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B)
  → (M′ ⟨ id {μ = ν} a ⟩ R.—↠[ R.keep R.∷ R.[] ] M′)
    × ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ q
extra-cast-right-idᶜ {p = p} M⊑M′ vM vM′ a q =
  R.↠-step (R.pure-step (R.β-id vM′)) R.↠-refl
  , subst≡ (λ r → _ ∣ _ ∣ _ ∣ _ ⊢ᶜ _ ⊑ _ ∶ r)
      (⊑-unique p q) M⊑M′

extra-cast-right-groundᶜ : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : StoreImp Δ} {γ : GTI.CtxImp (impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B G : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {g : C.Groundʳ ν C.X∼★ G}
    {p : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ B ∼ G)
  → (Bns : NonStar B)
  → (match : C.GroundMatch g B)
  → B ≢ G
  → (q : impEnvⁱ ρ ⊢ A ⊑ ★)
  → (M′ ⟨ _! ⦃ g ⦄ c′ ⦃ Bns ⦄ ⦃ match ⦄ ⟩
       R.—↠[ R.keep R.∷ R.[] ]
     M′ ⟨ c′ ⟩
       ⟨ _! ⦃ g ⦄ (C.idᵍ g)
           ⦃ C.ground-nonstar g ⦄ ⦃ C.ground-match g ⦄ ⟩)
    × ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑
        M′ ⟨ c′ ⟩
          ⟨ _! ⦃ g ⦄ (C.idᵍ g)
              ⦃ C.ground-nonstar g ⦄ ⦃ C.ground-match g ⦄ ⟩
        ∶ q
extra-cast-right-groundᶜ {ηᴿ = ηᴿ} {g = g} {p = p}
    M⊑M′ vM vM′ c′ Bns match B≢G q =
  R.↠-step
    (R.pure-step
      (R.ground ⦃ g = g ⦄ ⦃ Ans = Bns ⦄ ⦃ match = match ⦄
        ⦃ Gns = C.ground-nonstar g ⦄
        ⦃ gmatch = C.ground-match g ⦄ vM′ B≢G))
    R.↠-refl
  , extra-cast-rightᶜ′
      (extra-cast-rightᶜ′ M⊑M′ c′
        (ground-cast-target⊑ (rename-groundʳ ηᴿ g)
          (C.renameNonStar (toRenameᵗ ηᴿ) Bns)
          (renameᵐᶜ ηᴿ c′) p q))
      (_! ⦃ g ⦄ (C.idᵍ g)
        ⦃ C.ground-nonstar g ⦄ ⦃ C.ground-match g ⦄)
      q

extra-cast-right-expandᶜ : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : StoreImp Δ} {γ : GTI.CtxImp (impEnvⁱ ρ)}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δ} {B G : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {g : C.Groundʳ ν C.★∼X G}
    {p : impEnvⁱ ρ ⊢ A ⊑ ★}
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → (c′ : ν ⊢ G ∼ B)
  → (Bns : NonStar B)
  → (match : C.GroundMatch g B)
  → G ≢ B
  → (q : impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) B)
  → (M′ ⟨ ？_ ⦃ g ⦄ c′ ⦃ Bns ⦄ ⦃ match ⦄ ⟩
       R.—↠[ R.keep R.∷ R.[] ]
     M′
       ⟨ ？_ ⦃ g ⦄ (C.idᵍ g)
           ⦃ C.ground-nonstar g ⦄ ⦃ C.ground-match g ⦄ ⟩
       ⟨ c′ ⟩)
    × ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑
        M′
          ⟨ ？_ ⦃ g ⦄ (C.idᵍ g)
              ⦃ C.ground-nonstar g ⦄ ⦃ C.ground-match g ⦄ ⟩
          ⟨ c′ ⟩
        ∶ q
extra-cast-right-expandᶜ {ηᴿ = ηᴿ} {g = g} {p = p}
    M⊑M′ vM vM′ c′ Bns match G≢B q =
  R.↠-step
    (R.pure-step
      (R.expand ⦃ g = g ⦄ ⦃ Bns = Bns ⦄ ⦃ match = match ⦄
        ⦃ Gns = C.ground-nonstar g ⦄
        ⦃ gmatch = C.ground-match g ⦄ vM′ G≢B))
    R.↠-refl
  , extra-cast-rightᶜ′
      (extra-cast-rightᶜ′ M⊑M′
        (？_ ⦃ g ⦄ (C.idᵍ g)
          ⦃ C.ground-nonstar g ⦄ ⦃ C.ground-match g ⦄)
        (expand-cast-source⊑ (rename-groundʳ ηᴿ g)
          (C.renameNonStar (toRenameᵗ ηᴿ) Bns)
          (renameᵐᶜ ηᴿ c′) p q))
      c′ q
