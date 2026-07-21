module proof.NuImprecisionTargetSealCancellationProof where

-- File Charter:
--   * Proves exact-world cancellation of a terminal target seal.
--   * Uses world coherence to connect matched seal names across stores.
--   * Depends on atomic target reindexing for proof-relevant indices.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
import Coercions as C
import Conversion
open import Conversion using (conceal-seal)
import NarrowWiden
open import Imprecision using (_ˣ⊑ˣ_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; idˣ; tagˣ; ν)
open import NuStore using (StoreWf; unique)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-left
  ; store-link
  ; store-matched
  ; store-right
  )
open import NuTerms using
  (No•; Term; Value; no•-⟨⟩; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; allocation-prefixᵀ
  ; cast⊒⊑ᵀ
  ; cast⊑⊑ᵀ
  ; conv↑⊑ᵀ
  ; conv↓⊑ᵀ
  ; conv⊑convᵀ
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; prefix-∷ⁱ
  ; prefix-reflⁱ
  ; quotient-cast-widening
  ; quotient-id-widening
  ; up⊑upᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑conv↓ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (_∣_∣_⊢_⦂_; ⊢⟨⟩↓; ⊢⟨⟩⊒; ⊢⟨⟩⊑)
import Types as T
open import Types using (Atom; Ty; TyVar; ＇_)
open import proof.MaximalLowerBoundsWf using
  (no-occurs-var-lower-νctxᵢ)
open import proof.NuImprecisionTargetSealCancellationDef using
  (TargetSealCancellationᵀ)
open import proof.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent; idˣ-corresponds)


left-prefix-inclusionᵀ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ∀ {α A} →
  (α , A) ∈ leftStoreⁱ ρ₀ →
  (α , A) ∈ leftStoreⁱ ρ⁺
left-prefix-inclusionᵀ prefix-reflⁱ x∈ = x∈
left-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) x∈ =
  there (left-prefix-inclusionᵀ prefix x∈)
left-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) x∈ =
  there (left-prefix-inclusionᵀ prefix x∈)
left-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) x∈ =
  left-prefix-inclusionᵀ prefix x∈
left-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) x∈ =
  left-prefix-inclusionᵀ prefix x∈

right-prefix-inclusionᵀ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ∀ {β B} →
  (β , B) ∈ rightStoreⁱ ρ₀ →
  (β , B) ∈ rightStoreⁱ ρ⁺
right-prefix-inclusionᵀ prefix-reflⁱ x∈ = x∈
right-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) x∈ =
  there (right-prefix-inclusionᵀ prefix x∈)
right-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) x∈ =
  right-prefix-inclusionᵀ prefix x∈
right-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) x∈ =
  there (right-prefix-inclusionᵀ prefix x∈)
right-prefix-inclusionᵀ
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) x∈ =
  right-prefix-inclusionᵀ prefix x∈

prefix-transᵀ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ₁ ρ₂ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ₁ →
  StoreImpPrefix ρ₁ ρ₂ →
  StoreImpPrefix ρ₀ ρ₂
prefix-transᵀ prefix₀₁ prefix-reflⁱ = prefix₀₁
prefix-transᵀ prefix₀₁ (prefix-∷ⁱ prefix₁₂) =
  prefix-∷ⁱ (prefix-transᵀ prefix₀₁ prefix₁₂)


target-seal-typing⁻¹ :
  ∀ {Δ Σ Γ V X β} →
  Δ ∣ Σ ∣ Γ ⊢ V ⟨ C.seal X β ⟩ ⦂ ＇ β →
  ((β , X) ∈ Σ) × (Δ ∣ Σ ∣ Γ ⊢ V ⦂ X)
target-seal-typing⁻¹
    (⊢⟨⟩↓ (Conversion.conv↓-seal hX β∈Σ ok) V⊢) =
  β∈Σ , V⊢
target-seal-typing⁻¹
    (⊢⟨⟩⊒ mode seal★ (C.cast-seal hX β∈Σ ok ,
      NarrowWiden.sealⁿ _ _) V⊢) =
  β∈Σ , V⊢
target-seal-typing⁻¹
    (⊢⟨⟩⊑ mode seal★
      (C.cast-seal hX β∈Σ ok , NarrowWiden.cross ()) V⊢)

target-atomᵀ :
  ∀ {Φ Δᴸ Δᴿ α B} →
  Φ ∣ Δᴸ ⊢ ＇ α ⊑ B ⊣ Δᴿ →
  Atom B
target-atomᵀ (idˣ a∈Φ α< β<) = T.＇ _
target-atomᵀ (tagˣ a∈Φ α<) = T.★

inert-reveal-target-var-impossibleᵀ :
  ∀ {μ Δ Σ α X c A β} →
  Conversion.RevealConversion μ Δ Σ α X c A (＇ β) →
  C.Inert c →
  ⊥
inert-reveal-target-var-impossibleᵀ
    (Conversion.reveal-id-var hY ok) ()
inert-reveal-target-var-impossibleᵀ
    (Conversion.reveal-unseal hX αX∈Σ ok) ()


target-seal-cancellation-prefixᵀ :
  ∀ {Φ Δᴸ Δᴿ} {W V : Term} {A X X′ : Ty} {β : TyVar}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ＇ β ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  Value W →
  No• W →
  Value V →
  (β , X′) ∈ rightStoreⁱ ρ⁺ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ W ⊑ V ⟨ C.seal X β ⟩ ⦂ A ⊑ ＇ β ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ X′ ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ W ⊑ V ⦂ A ⊑ X′ ∶ q
target-seal-cancellation-prefixᵀ
    {p = ν occ p} prefix coh wfΣ vW noW vV β∈Σ W⊑V q =
  ⊥-elim (no-occurs-var-lower-νctxᵢ occ p)
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (up⊑upᵀ inner
      (quotient-id-widening u⊑
        (C.cast-seal hX βX∈Σ ok , NarrowWiden.cross ())) oldq)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (up⊑upᵀ inner
      (quotient-cast-widening mode seal★ u⊑ mode′ seal★′
        (C.cast-seal hX βX∈Σ ok , NarrowWiden.cross ())) oldq)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (⊑cast⊑ᵀ mode seal★
      (C.cast-seal hX βX∈Σ ok , NarrowWiden.cross ())
      inner oldq)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (⊑cast⊑idᵀ seal★
      (C.cast-seal hX βX∈Σ ok , NarrowWiden.cross ())
      inner oldq)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (conv⊑convᵀ
      (paired-conversion (paired-reveal corr c↑ ())) inner)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (conv⊑convᵀ
      (paired-widening mode seal★ c⊑ mode′ seal★′
        (C.cast-seal hX βX∈Σ ok , NarrowWiden.cross ())) inner)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ
    (vM ⟨ C.seal Y α ⟩) (no•-⟨⟩ noM) vV βX′∈Σ
    (cast⊑⊑ᵀ mode seal★
      (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ())
      M⊑Vβ oldq)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ
    (vM ⟨ inert ⟩) noW vV βX′∈Σ
    (conv↑⊑ᵀ c↑ M⊑Vβ oldq) q =
  ⊥-elim (inert-reveal-target-var-impossibleᵀ c↑ inert)
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ
    (vM ⟨ C.seal Y α ⟩) (no•-⟨⟩ noM) vV βX′∈Σ
    (cast⊒⊑ᵀ mode seal★
      (C.cast-seal hY αY∈Σ ok , NarrowWiden.sealⁿ .Y .α)
      M⊑Vβ oldq)
    q
    with idˣ-corresponds coh a∈Φ
      (left-prefix-inclusionᵀ prefix αY∈Σ) βX′∈Σ
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ
    (vM ⟨ C.seal Y α ⟩) (no•-⟨⟩ noM) vV βX′∈Σ
    (cast⊒⊑ᵀ mode seal★
      (C.cast-seal hY αY∈Σ ok , NarrowWiden.sealⁿ .Y .α)
      M⊑Vβ oldq)
    q | pY , corr =
  cast⊒⊑ᵀ mode seal★
    (C.cast-seal hY αY∈Σ ok , NarrowWiden.sealⁿ Y α)
    (target-seal-cancellation-prefixᵀ
      prefix coh wfΣ vM noM vV βX′∈Σ M⊑Vβ pY)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ
    (vM ⟨ C.seal Y α ⟩) (no•-⟨⟩ noM) vV βX′∈Σ
    (conv↓⊑ᵀ {μ = μ}
      (conceal-seal hY αY∈Σ ok) M⊑Vβ oldq)
    q
    with idˣ-corresponds coh a∈Φ
      (left-prefix-inclusionᵀ prefix αY∈Σ) βX′∈Σ
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ
    (vM ⟨ C.seal Y α ⟩) (no•-⟨⟩ noM) vV βX′∈Σ
    (conv↓⊑ᵀ {μ = μ}
      (conceal-seal hY αY∈Σ ok) M⊑Vβ oldq)
    q | pY , corr =
  conv↓⊑ᵀ {μ = μ} (conceal-seal hY αY∈Σ ok)
    (target-seal-cancellation-prefixᵀ
      prefix coh wfΣ vM noM vV βX′∈Σ M⊑Vβ pY)
    q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (⊑cast⊒ᵀ mode seal★
      (C.cast-seal hX βX∈Σ ok , NarrowWiden.sealⁿ X β)
      W⊑V oldq)
    q
    rewrite unique wfΣ
      (right-prefix-inclusionᵀ prefix βX∈Σ) βX′∈Σ =
  atomic-target-value-reindexᵀ (target-atomᵀ q) vV W⊑V q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (⊑conv↓ᵀ (conceal-seal hX βX∈Σ ok) W⊑V oldq)
    q
    rewrite unique wfΣ
      (right-prefix-inclusionᵀ prefix βX∈Σ) βX′∈Σ =
  atomic-target-value-reindexᵀ (target-atomᵀ q) vV W⊑V q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ
    (vM ⟨ C.seal Y α ⟩) (no•-⟨⟩ noM) vV βX′∈Σ
    (conv⊑convᵀ
      (paired-conversion
        (paired-conceal {μ = μ} {μ′ = μ′} corr
          (conceal-seal hY αY∈Σ ok)
          (conceal-seal hX βX∈Σ ok′)))
      M⊑V)
    q
    rewrite unique wfΣ
      (right-prefix-inclusionᵀ prefix βX∈Σ) βX′∈Σ =
  conv↓⊑ᵀ {μ = μ} (conceal-seal hY αY∈Σ ok) M⊑V q
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (allocation-prefixᵀ prefix₀ inner W⊢ Vseal⊢) q
    with target-seal-typing⁻¹ Vseal⊢
target-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<} prefix coh wfΣ vW noW vV βX′∈Σ
    (allocation-prefixᵀ prefix₀ inner W⊢ Vseal⊢) q
    | βX∈Σ , V⊢
    rewrite unique wfΣ
      (right-prefix-inclusionᵀ prefix βX∈Σ) βX′∈Σ =
  allocation-prefixᵀ prefix₀
    (target-seal-cancellation-prefixᵀ
      (prefix-transᵀ prefix₀ prefix) coh wfΣ
      vW noW vV βX′∈Σ inner q)
    W⊢ V⊢


target-seal-cancellation-proofᵀ : TargetSealCancellationᵀ
target-seal-cancellation-proofᵀ coh wfΣ vW noW vV β∈Σ W⊑V q =
  target-seal-cancellation-prefixᵀ
    prefix-reflⁱ coh wfΣ vW noW vV β∈Σ W⊑V q
