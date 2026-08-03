module proof.DGG.RightInjInversion where

-- File Charter:
--   * Proves the inversion lemma for cast-term imprecision whose right term is
--     a tagged value produced by an injection cast.
--   * Exposes both the same-context core inversion and the indexed-by-renaming
--     wrapper used by the extra-cast-on-the-right proof.
--   * Depends on cast-term imprecision typing projections, uniqueness of type
--     imprecision, and occurrence preservation across imprecision.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; ∀ᶜ_; _!; gen_; toRenameᵗ)
import Consistency as C
open import CastTerms using
  (Term; Value; ⊢⟨⟩; Λ_; _⟨_⟩; inj; fun; all; genᵥ; _《_》;
   ⇑ᵗᵐ)
open import Imprecision using (_⊢_⊑_)
import Imprecision as I
import GradualTermImprecision as GTI
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢ᶜ_⊑_∶_; _∣_∣_∣_⊢ᶜ_⊑_∶_)
open import proof.ImprecisionConsistency using
  (ground-cast-source⊑; nonstar-from-≢★; source-occurs-target)
import proof.Imprecision as PI
open import proof.TypeInTermSubst using
  (renameᵗ-wk-eq; renameᵗᵐ-preserves-Value)

private
  transport-⊑ᶜ-right-index : ∀ {Δ} {ρ : CTI.StoreImp Δ}
      {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)} {M N : Term Δ}
      {A B B′ : Ty Δ}
    → (eq : B ≡ B′)
    → {q : CTI.impEnvⁱ ρ ⊢ A ⊑ B′}
    → ρ ∣ γ ⊢ᶜ M ⊑ N ∶
        subst≡ (λ T → CTI.impEnvⁱ ρ ⊢ A ⊑ T) (sym eq) q
    → ρ ∣ γ ⊢ᶜ M ⊑ N ∶ q
  transport-⊑ᶜ-right-index refl M⊑N = M⊑N

right-inj-inversion-core : ∀ {Δ} {ρ : CTI.StoreImp Δ}
    {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M W : Term Δ} {A H : Ty Δ} {ν : Env∼ Δ}
    {h : C.Groundʳ ν C.X∼★ H}
    {Hns : NonStar H} {hmatch : C.GroundMatch h H}
    {c′ : ν ⊢ H ∼ H}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ ★}
  → Value M
  → ρ ∣ γ ⊢ᶜ M ⊑ W ⟨ _! ⦃ h ⦄ c′ ⦃ Hns ⦄ ⦃ hmatch ⦄ ⟩
      ∶ p
  → (q : CTI.impEnvⁱ ρ ⊢ A ⊑ H)
  → ρ ∣ γ ⊢ᶜ M ⊑ W ∶ q
right-inj-inversion-core {p = p} vM
    (CTI.⊑castᶜ c′ M⊑W p) q =
  subst≡ (λ r → _ ∣ _ ⊢ᶜ _ ⊑ _ ∶ r) (PI.⊑-unique _ q) M⊑W
right-inj-inversion-core vM
    (CTI.cast⊑castᶜ c c′ M⊑W p) q =
  CTI.cast⊑ᶜ c M⊑W q
right-inj-inversion-core {Hns = ()} (vM 《 inj 》)
    (CTI.cast⊑ᶜ c M⊑W! q′) I.★⊑★
right-inj-inversion-core {h = C.g-⇒} (vM 《 fun 》)
    (CTI.cast⊑ᶜ {p = I.⇒⊑★ pA pB} c M⊑W! q′)
    (I.⇒⊑⇒ qA qB) =
  CTI.cast⊑ᶜ c
    (right-inj-inversion-core vM M⊑W! (I.⇒⊑⇒ pA pB))
    (I.⇒⊑⇒ qA qB)
right-inj-inversion-core {h = h} (vM 《 all {c = c} 》)
    (CTI.cast⊑ᶜ {p = p} .(∀ᶜ c) M⊑W! q′) q =
  CTI.cast⊑ᶜ (∀ᶜ c)
    (right-inj-inversion-core vM M⊑W!
      (ground-cast-source⊑ h nonstar-∀ (∀ᶜ c) p q′ q))
    q
right-inj-inversion-core {h = h} (vM 《 genᵥ A≠★ safe 》)
    (CTI.cast⊑ᶜ {p = p} c M⊑W! q′) q =
  CTI.cast⊑ᶜ c
    (right-inj-inversion-core vM M⊑W!
      (ground-cast-source⊑ h (nonstar-from-≢★ A≠★) c p q′ q))
    q
right-inj-inversion-core {ρ = ρ} {H = H} (Λ vV₀)
    (CTI.Λ⊑ᶜ {A = A₀} Anv zero∈A liftγ vV
      (⊢⟨⟩ W⊢ c!) V⊑⇑W!)
    (I.∀⊑ Anv′ zero∈A′ qbody) =
  CTI.Λ⊑ᶜ Anv′ zero∈A′ liftγ vV W⊢
    (transport-⊑ᶜ-right-index (renameᵗ-wk-eq H)
      (right-inj-inversion-core vV V⊑⇑W!
        (subst≡
          (λ T → I.instᵐ (CTI.impEnvⁱ ρ) ⊢ A₀ ⊑ T)
          (sym (renameᵗ-wk-eq H))
          qbody)))
right-inj-inversion-core {h = C.g-∀} (Λ vV₀)
    (CTI.Λ⊑ᶜ {A = A₀} Anv zero∈A liftγ vV W!⊢ V⊑⇑W!)
    (I.∀⊑∀ qbody)
    with source-occurs-target refl qbody zero∈A
right-inj-inversion-core {h = C.g-∀} (Λ vV₀)
    (CTI.Λ⊑ᶜ {A = A₀} Anv zero∈A liftγ vV W!⊢ V⊑⇑W!)
    (I.∀⊑∀ qbody)
    | ()
right-inj-inversion-core (Λ vV₀)
    (CTI.Λ⊑ᶜ () zero∈A liftγ vV W!⊢ V⊑⇑W!)
    I.bot-elim
right-inj-inversion-core () (CTI.•⊑ᶜ M⊑M′ q′ p) q

right-inj-inversion-indexed : ∀ {Δᴸ Δᴿ Δ}
    {ηᴸ : Δᴸ ↪ᵗ Δ} {ηᴿ : Δᴿ ↪ᵗ Δ}
    {ρ : CTI.StoreImp Δ} {γ : GTI.CtxImp (CTI.impEnvⁱ ρ)}
    {M : Term Δᴸ} {W : Term Δᴿ} {A : Ty Δ}
    {H : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {h : C.Groundʳ ν C.X∼★ H}
    {Hns : NonStar H} {hmatch : C.GroundMatch h H}
    {p : CTI.impEnvⁱ ρ ⊢ A ⊑ ★}
  → Value M
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M
      ⊑ W ⟨ _! ⦃ h ⦄ (C.idᵍ h)
          ⦃ Hns ⦄ ⦃ hmatch ⦄ ⟩
      ∶ p
  → (q : CTI.impEnvⁱ ρ ⊢ A ⊑ renameᵗ (toRenameᵗ ηᴿ) H)
  → ηᴸ ∣ ηᴿ ∣ ρ ∣ γ ⊢ᶜ M ⊑ W ∶ q
right-inj-inversion-indexed vM
    (CTI.rename⊑renameᶜ categorize M⊑W!) q =
  CTI.rename⊑renameᶜ categorize
    (right-inj-inversion-core (renameᵗᵐ-preserves-Value _ vM) M⊑W! q)
