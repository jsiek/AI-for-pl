module proof.DGG.ExtraCastRight where

-- File Charter:
--   * Proves the indexed-by-renamings form of the extra-cast-on-the-right
--     cast-term imprecision lemma.
--   * Keeps the cast evidence local to the right type context and lifts it
--     through the right embedding before using the core right-cast rule.
--   * Depends only on the cast-term imprecision relation and consistency
--     renaming.

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≢_; trans)
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
  (expand-cast-source⊑; ground-cast-target⊑)
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
