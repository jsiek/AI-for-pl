module proof.NuImprecisionSourceSealCancellationProof where

-- File Charter:
--   * Proves exact-world cancellation of a terminal source seal.
--   * Uses world coherence for matched names and source-name exclusivity to
--     eliminate a source-only name hidden beneath a target tag.
--   * Depends on atomic target reindexing for proof-relevant indices.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
import Coercions as C
open import Coercions using (_!)
import Conversion
open import Conversion using (conceal-seal)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; idˣ; tagˣ)
import NarrowWiden
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
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (_∣_∣_⊢_⦂_; ⊢⟨⟩↓; ⊢⟨⟩⊒; ⊢⟨⟩⊑)
import Types as T
open import Types using (Atom; Ty; TyVar; ＇_)
open import proof.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionSourceSealCancellationDef using
  (SourceSealCancellationᵀ)
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


source-seal-typing⁻¹ :
  ∀ {Δ Σ Γ V X α} →
  Δ ∣ Σ ∣ Γ ⊢ V ⟨ C.seal X α ⟩ ⦂ ＇ α →
  ((α , X) ∈ Σ) × (Δ ∣ Σ ∣ Γ ⊢ V ⦂ X)
source-seal-typing⁻¹
    (⊢⟨⟩↓ (Conversion.conv↓-seal hX α∈Σ ok) V⊢) =
  α∈Σ , V⊢
source-seal-typing⁻¹
    (⊢⟨⟩⊒ mode seal★
      (C.cast-seal hX α∈Σ ok , NarrowWiden.sealⁿ _ _) V⊢) =
  α∈Σ , V⊢
source-seal-typing⁻¹
    (⊢⟨⟩⊑ mode seal★
      (C.cast-seal hX α∈Σ ok , NarrowWiden.cross ()) V⊢)


target-atomᵀ :
  ∀ {Φ Δᴸ Δᴿ α B} →
  Φ ∣ Δᴸ ⊢ ＇ α ⊑ B ⊣ Δᴿ →
  Atom B
target-atomᵀ (idˣ a∈Φ α< β<) = T.＇ _
target-atomᵀ (tagˣ a∈Φ α<) = T.★


inert-reveal-target-atom-impossibleᵀ :
  ∀ {μ Δ Σ α X c A B} →
  Conversion.RevealConversion μ Δ Σ α X c A B →
  Atom B →
  C.Inert c →
  ⊥
inert-reveal-target-atom-impossibleᵀ
    (Conversion.reveal-id-var hY ok) atom ()
inert-reveal-target-atom-impossibleᵀ
    Conversion.reveal-id-base atom ()
inert-reveal-target-atom-impossibleᵀ
    Conversion.reveal-id-★ atom ()
inert-reveal-target-atom-impossibleᵀ
    (Conversion.reveal-unseal hX αX∈Σ ok) atom ()
inert-reveal-target-atom-impossibleᵀ
    (Conversion.reveal-fun c↓ c↑) () inert
inert-reveal-target-atom-impossibleᵀ
    (Conversion.reveal-all c↑) () inert


inert-conceal-target-star-impossibleᵀ :
  ∀ {μ Δ Σ α X c A} →
  Conversion.ConcealConversion μ Δ Σ α X c A T.★ →
  C.Inert c →
  ⊥
inert-conceal-target-star-impossibleᵀ
    Conversion.conceal-id-★ ()


source-seal-cancellation-prefixᵀ :
  ∀ {Φ Δᴸ Δᴿ} {V W : Term} {B X Y : Ty} {α : TyVar}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ ＇ α ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  Value V →
  Value W →
  No• W →
  (α , X) ∈ leftStoreⁱ ρ⁺ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⟨ C.seal Y α ⟩ ⊑ W ⦂ ＇ α ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ X ⊑ B ⊣ Δᴿ) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ W ⦂ X ⊑ B ∶ q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (up⊑upᵀ inner
      (quotient-id-widening
        (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ()) u′⊑)
      oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (up⊑upᵀ inner
      (quotient-cast-widening mode seal★
        (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ())
        mode′ seal★′ u′⊑)
      oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (cast⊑⊑ᵀ mode seal★
      (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ())
      inner oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (conv⊑convᵀ
      (paired-conversion (paired-reveal corr () c′↑)) inner)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (conv⊑convᵀ
      (paired-widening mode seal★
        (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ())
        mode′ seal★′ c′⊑ _)
      inner)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ C.seal Z β ⟩) (no•-⟨⟩ noM) αX∈Σ
    (⊑cast⊑ᵀ mode seal★
      (C.cast-seal hZ βZ∈Σ ok , NarrowWiden.cross ())
      Vα⊑M oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ C.seal Z β ⟩) (no•-⟨⟩ noM) αX∈Σ
    (⊑cast⊑idᵀ seal★
      (C.cast-seal hZ βZ∈Σ ok , NarrowWiden.cross ())
      Vα⊑M oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ inert ⟩) noW αX∈Σ
    (⊑conv↑ᵀ c′↑ Vα⊑M oldq) q =
  ⊥-elim
    (inert-reveal-target-atom-impossibleᵀ
      c′↑ (target-atomᵀ oldq) inert)
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ C.seal Z β ⟩) (no•-⟨⟩ noM) αX∈Σ
    (⊑cast⊒ᵀ mode seal★
      (C.cast-seal hZ βZ∈Σ ok , NarrowWiden.sealⁿ .Z .β)
      Vα⊑M oldq)
    q
    with idˣ-corresponds coh a∈Φ αX∈Σ
      (right-prefix-inclusionᵀ prefix βZ∈Σ)
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ C.seal Z β ⟩) (no•-⟨⟩ noM) αX∈Σ
    (⊑cast⊒ᵀ mode seal★
      (C.cast-seal hZ βZ∈Σ ok , NarrowWiden.sealⁿ .Z .β)
      Vα⊑M oldq)
    q | pX , corr =
  ⊑cast⊒ᵀ mode seal★
    (C.cast-seal hZ βZ∈Σ ok , NarrowWiden.sealⁿ Z β)
    (source-seal-cancellation-prefixᵀ
      prefix coh exclusive wfΣ vV vM noM αX∈Σ Vα⊑M pX)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ C.seal Z β ⟩) (no•-⟨⟩ noM) αX∈Σ
    (⊑conv↓ᵀ { μ′ = μ′ }
      (conceal-seal hZ βZ∈Σ ok) Vα⊑M oldq)
    q
    with idˣ-corresponds coh a∈Φ αX∈Σ
      (right-prefix-inclusionᵀ prefix βZ∈Σ)
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ C.seal Z β ⟩) (no•-⟨⟩ noM) αX∈Σ
    (⊑conv↓ᵀ { μ′ = μ′ }
      (conceal-seal hZ βZ∈Σ ok) Vα⊑M oldq)
    q | pX , corr =
  ⊑conv↓ᵀ { μ′ = μ′ } (conceal-seal hZ βZ∈Σ ok)
    (source-seal-cancellation-prefixᵀ
      prefix coh exclusive wfΣ vV vM noM αX∈Σ Vα⊑M pX)
    q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (cast⊒⊑ᵀ mode seal★
      (C.cast-seal hY αY∈Σ ok , NarrowWiden.sealⁿ Y α)
      V⊑W oldq)
    q
    rewrite unique wfΣ
      (left-prefix-inclusionᵀ prefix αY∈Σ) αX∈Σ =
  atomic-target-value-reindexᵀ
    (target-atomᵀ (idˣ a∈Φ α< β<)) vW V⊑W q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (conv↓⊑ᵀ (conceal-seal hY αY∈Σ ok) V⊑W oldq)
    q
    rewrite unique wfΣ
      (left-prefix-inclusionᵀ prefix αY∈Σ) αX∈Σ =
  atomic-target-value-reindexᵀ
    (target-atomᵀ (idˣ a∈Φ α< β<)) vW V⊑W q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ C.seal Z β ⟩) (no•-⟨⟩ noM) αX∈Σ
    (conv⊑convᵀ
      (paired-conversion
        (paired-conceal { μ = μ } { μ′ = μ′ } corr
          (conceal-seal hY αY∈Σ ok)
          (conceal-seal hZ βZ∈Σ ok′)))
      V⊑M)
    q
    rewrite unique wfΣ
      (left-prefix-inclusionᵀ prefix αY∈Σ) αX∈Σ =
  ⊑conv↓ᵀ { μ′ = μ′ } (conceal-seal hZ βZ∈Σ ok′) V⊑M q
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (allocation-prefixᵀ prefix₀ inner Vseal⊢ W⊢) q
    with source-seal-typing⁻¹ Vseal⊢
source-seal-cancellation-prefixᵀ
    {p = idˣ a∈Φ α< β<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (allocation-prefixᵀ prefix₀ inner Vseal⊢ W⊢) q
    | αY∈Σ , V⊢
    rewrite unique wfΣ
      (left-prefix-inclusionᵀ prefix αY∈Σ) αX∈Σ =
  allocation-prefixᵀ prefix₀
    (source-seal-cancellation-prefixᵀ
      (prefix-transᵀ prefix₀ prefix) coh exclusive wfΣ
      vV vW noW αX∈Σ inner q)
    V⊢ W⊢
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (up⊑upᵀ inner
      (quotient-id-widening
        (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ()) u′⊑)
      oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (up⊑upᵀ inner
      (quotient-cast-widening mode seal★
        (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ())
        mode′ seal★′ u′⊑)
      oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (cast⊑⊑ᵀ mode seal★
      (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ())
      inner oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (conv⊑convᵀ
      (paired-conversion (paired-reveal corr () c′↑)) inner)
    q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (conv⊑convᵀ
      (paired-widening mode seal★
        (C.cast-seal hY αY∈Σ ok , NarrowWiden.cross ())
        mode′ seal★′ c′⊑ _)
      inner)
    q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ inert′ ⟩) noW αX∈Σ
    (conv⊑convᵀ
      (paired-conversion
        (paired-conceal corr
          (conceal-seal hY αY∈Σ ok) c′↓))
      V⊑M)
    q =
  ⊥-elim (inert-conceal-target-star-impossibleᵀ c′↓ inert′)
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (cast⊒⊑ᵀ mode seal★
      (C.cast-seal hY αY∈Σ ok , NarrowWiden.sealⁿ Y α)
      V⊑W oldq)
    q
    rewrite unique wfΣ
      (left-prefix-inclusionᵀ prefix αY∈Σ) αX∈Σ =
  atomic-target-value-reindexᵀ
    T.★ vW V⊑W q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ G ! ⟩) noW αX∈Σ
    (⊑cast⊒ᵀ mode seal★
      (C.cast-tag hG gG ok , NarrowWiden.cross ()) Vα⊑M oldq)
    q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ (T.＇ β) ! ⟩) noW αX∈Σ
    (⊑cast⊑ᵀ {p = idˣ match∈ α<′ β<}
      mode seal★
      (C.cast-tag hβ (T.＇ β) ok , NarrowWiden.tag (T.＇ β))
      Vα⊑M oldq)
    q =
  ⊥-elim (exclusive star∈ match∈)
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ (T.＇ β) ! ⟩) noW αX∈Σ
    (⊑cast⊑idᵀ {p = idˣ match∈ α<′ β<}
      seal★
      (C.cast-tag hβ (T.＇ β) ok , NarrowWiden.tag (T.＇ β))
      Vα⊑M oldq)
    q =
  ⊥-elim (exclusive star∈ match∈)
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (conv↓⊑ᵀ (conceal-seal hY αY∈Σ ok) V⊑W oldq)
    q
    rewrite unique wfΣ
      (left-prefix-inclusionᵀ prefix αY∈Σ) αX∈Σ =
  atomic-target-value-reindexᵀ
    T.★ vW V⊑W q
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ inert ⟩) noW αX∈Σ
    (⊑conv↑ᵀ c′↑ Vα⊑M oldq) q =
  ⊥-elim
    (inert-reveal-target-atom-impossibleᵀ c′↑ T.★ inert)
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV
    (vM ⟨ inert ⟩) noW αX∈Σ
    (⊑conv↓ᵀ c′↓ Vα⊑M oldq) q =
  ⊥-elim (inert-conceal-target-star-impossibleᵀ c′↓ inert)
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (allocation-prefixᵀ prefix₀ inner Vseal⊢ W⊢) q
    with source-seal-typing⁻¹ Vseal⊢
source-seal-cancellation-prefixᵀ
    {p = tagˣ star∈ α<}
    prefix coh exclusive wfΣ vV vW noW αX∈Σ
    (allocation-prefixᵀ prefix₀ inner Vseal⊢ W⊢) q
    | αY∈Σ , V⊢
    rewrite unique wfΣ
      (left-prefix-inclusionᵀ prefix αY∈Σ) αX∈Σ =
  allocation-prefixᵀ prefix₀
    (source-seal-cancellation-prefixᵀ
      (prefix-transᵀ prefix₀ prefix) coh exclusive wfΣ
      vV vW noW αX∈Σ inner q)
    V⊢ W⊢


source-seal-cancellation-proofᵀ : SourceSealCancellationᵀ
source-seal-cancellation-proofᵀ coh exclusive wfΣ vV vW noW αX∈Σ
    Vseal⊑W q =
  source-seal-cancellation-prefixᵀ
    prefix-reflⁱ coh exclusive wfΣ vV vW noW αX∈Σ Vseal⊑W q
