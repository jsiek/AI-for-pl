module proof.Core.Properties.TermNarrowingProperties where

-- File Charter:
--   * Reserved for admissible rules and structural lemmas for typed term
--     narrowing.
--   * Contains the experimental derived two-sided cast narrowing rules,
--     obtained from the one-sided cast rules and narrowing composition.

open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import NarrowWiden
open import NarrowWidenComposition
open import TermNarrowing
open import proof.Core.Properties.CoercionProperties using (coercion-src-tgtᵐ; minus-src-tgtᵐ)
import proof.Core.Properties.NarrowWidenProperties as NWP
open import proof.Core.Properties.NarrowWidenProperties using (StoreDetWf; srcStoreⁿ-⊒ˢ)

≈ⁿ-right-typing :
  ∀ {Δ σ l r A B} →
  Δ ∣ σ ⊢ l ≈ r ∶ A ⊒ B →
  Δ ∣ srcStoreⁿ σ ⊢ r ∶ A ⊒ B
≈ⁿ-right-typing {Δ = Δ} {σ = σ} {r = r} {A = A} {B = B}
    (endpointsⁿ srcl tgtl srcr tgtr σ⊒ wfΣ wfΣ′ l⊒ r⊒) =
  subst (λ Σ → Δ ∣ Σ ⊢ r ∶ A ⊒ B) (srcStoreⁿ-⊒ˢ σ⊒) r⊒

⨟ⁿ≈-right-typing :
  ∀ {Δ σ Σ μ q s r A B C} →
  (wfΣ : StoreDetWf Δ Σ) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C) →
  (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B) →
  Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B →
  Δ ∣ srcStoreⁿ σ ⊢ r ∶ A ⊒ B
⨟ⁿ≈-right-typing wfΣ q⊒ s⊒ q⨟s≈r =
  ≈ⁿ-right-typing q⨟s≈r

inner-cast-typing :
  ∀ {Δ σ γ M M′ p r s t A B C Ap Bp Σ μ} →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ Ap ⊒ Bp →
  (wfΣ : StoreDetWf Δ Σ) →
  (t⊒ : μ ∣ Δ ∣ Σ ⊢ t ∶ A ⊒ C) →
  (p⊒ : μ ∣ Δ ∣ Σ ⊢ p ∶ C ⊒ B) →
  Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} t⊒ p⊒) ∶ A ⊒ B →
  TermTypingEndpoints Δ σ γ (M ⟨ t ⟩) (M′ ⟨ s ⟩) Ap Bp →
  TermTypingEndpoints Δ σ γ M (M′ ⟨ s ⟩) A B
inner-cast-typing {Δ = Δ} {σ = σ} {γ = γ} {M = M}
    {M′ = M′} {s = s} {t = t} {A = A} {B = B} {Bp = Bp}
    pᶜ wfΣ t⊒ p⊒ t⨟p≈r typing
    with sourceTermTyping typing
inner-cast-typing {Δ = Δ} {σ = σ} {γ = γ} {M = M}
    {M′ = M′} {s = s} {t = t} {A = A} {B = B} {Bp = Bp}
    pᶜ wfΣ t⊒ p⊒ t⨟p≈r typing
    | ⊢⟨⟩ {A = At} t⊢ M⊢ =
  term-typing-endpoints M⊢A M′⟨s⟩⊢B
  where
    t-src : At ≡ A
    t-src =
      trans (sym (proj₁ (coercion-src-tgtᵐ t⊢)))
        (proj₁ (coercion-src-tgtᵐ (proj₁ t⊒)))

    M⊢A :
      Δ ∣ srcStoreⁿ σ ∣ srcCtxⁿ γ ⊢ M ⦂ A
    M⊢A =
      subst (λ T → Δ ∣ srcStoreⁿ σ ∣ srcCtxⁿ γ ⊢ M ⦂ T)
        t-src M⊢

    p-tgt : Bp ≡ B
    p-tgt =
      trans (sym (proj₂ (coercion-src-tgtᵐ (proj₁ pᶜ))))
        (proj₂ (coercion-src-tgtᵐ (proj₁ p⊒)))

    M′⟨s⟩⊢B :
      Δ ∣ tgtStoreⁿ σ ∣ tgtCtxⁿ γ ⊢ M′ ⟨ s ⟩ ⦂ B
    M′⟨s⟩⊢B =
      subst (λ T → Δ ∣ tgtStoreⁿ σ ∣ tgtCtxⁿ γ ⊢ M′ ⟨ s ⟩ ⦂ T)
        p-tgt
        (targetTermTyping typing)

cast-⊒cast-derivedᵗ :
  ∀ {Δ σ γ M M′ p q r s t A B Ap Bp Aq Bq C D Σ Π μ ν}
  → {typing :
      TermTypingEndpoints Δ σ γ (M ⟨ t ⟩) (M′ ⟨ s ⟩) Ap Bp}
  → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ Ap ⊒ Bp
  → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ Aq ⊒ Bq
  → (wfΣ : StoreDetWf Δ Σ)
  → (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C)
  → (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B)
  → Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B
  → (wfΠ : StoreDetWf Δ Π)
  → (t⊒ : ν ∣ Δ ∣ Π ⊢ t ∶ A ⊒ D)
  → (p⊒ : ν ∣ Δ ∣ Π ⊢ p ∶ D ⊒ B)
  → Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΠ} t⊒ p⊒) ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ q ⦂ Aq ⊒ Bq
  → Δ ∣ σ ∣ γ ⊢ M ⟨ t ⟩ ⊒ M′ ⟨ s ⟩ ∶ p ⦂ Ap ⊒ Bp
cast-⊒cast-derivedᵗ {typing = typing}
    pᶜ qᶜ wfΣ q⊒ s⊒ q⨟s≈r wfΠ t⊒ p⊒ r≈t⨟p M⊒M′
    with ⨟ⁿ≈-right-typing wfΣ q⊒ s⊒ q⨟s≈r
cast-⊒cast-derivedᵗ {typing = typing}
    pᶜ qᶜ wfΣ q⊒ s⊒ q⨟s≈r wfΠ t⊒ p⊒ r≈t⨟p M⊒M′
    | μ , r⊒ =
  cast-⊒ᵗ {typing = typing} pᶜ wfΠ t⊒ p⊒ r≈t⨟p
    (⊒cast-ᵗ
      {typing = inner-cast-typing pᶜ wfΠ t⊒ p⊒ r≈t⨟p typing}
      qᶜ r⊒ wfΣ q⊒ s⊒ q⨟s≈r M⊒M′)

inner-cast+-typing :
  ∀ {Δ σ γ M M′ q r s t A B C Aq Bq Σ μ} →
  Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ Aq ⊒ Bq →
  (wfΣ : StoreDetWf Δ Σ) →
  (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C) →
  (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B) →
  Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B →
  TermTypingEndpoints Δ σ γ (M ⟨ - t ⟩) (M′ ⟨ - s ⟩) Aq Bq →
  TermTypingEndpoints Δ σ γ (M ⟨ - t ⟩) M′ A B
inner-cast+-typing {Δ = Δ} {σ = σ} {γ = γ} {M = M}
    {M′ = M′} {s = s} {t = t} {A = A} {B = B} {Aq = Aq}
    qᶜ wfΣ q⊒ s⊒ q⨟s≈r typing
    with targetTermTyping typing
inner-cast+-typing {Δ = Δ} {σ = σ} {γ = γ} {M = M}
    {M′ = M′} {s = s} {t = t} {A = A} {B = B} {Aq = Aq}
    qᶜ wfΣ q⊒ s⊒ q⨟s≈r typing
    | ⊢⟨⟩ {A = Bt} negs⊢ M′⊢ =
  term-typing-endpoints M⟨-t⟩⊢A M′⊢B
  where
    q-src : Aq ≡ A
    q-src =
      trans (sym (proj₁ (coercion-src-tgtᵐ (proj₁ qᶜ))))
        (proj₁ (coercion-src-tgtᵐ (proj₁ q⊒)))

    M⟨-t⟩⊢A :
      Δ ∣ srcStoreⁿ σ ∣ srcCtxⁿ γ ⊢ M ⟨ - t ⟩ ⦂ A
    M⟨-t⟩⊢A =
      subst (λ T → Δ ∣ srcStoreⁿ σ ∣ srcCtxⁿ γ ⊢ M ⟨ - t ⟩ ⦂ T)
        q-src
        (sourceTermTyping typing)

    s-tgt : Bt ≡ B
    s-tgt =
      trans (sym (proj₁ (coercion-src-tgtᵐ negs⊢)))
        (minus-src-tgtᵐ (NWP.StoreDetWf.at wfΣ) (proj₁ s⊒))

    M′⊢B :
      Δ ∣ tgtStoreⁿ σ ∣ tgtCtxⁿ γ ⊢ M′ ⦂ B
    M′⊢B =
      subst (λ T → Δ ∣ tgtStoreⁿ σ ∣ tgtCtxⁿ γ ⊢ M′ ⦂ T)
        s-tgt M′⊢

cast+⊒cast+-derivedᵗ :
  ∀ {Δ σ γ M M′ p q r s t A B Ap Bp Aq Bq C D Σ Π μ ν}
  → {typing :
      TermTypingEndpoints Δ σ γ
        (M ⟨ - t ⟩) (M′ ⟨ - s ⟩) Aq Bq}
  → Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ Ap ⊒ Bp
  → Δ ∣ srcStoreⁿ σ ⊢ q ∶ᶜ Aq ⊒ Bq
  → (wfΣ : StoreDetWf Δ Σ)
  → (q⊒ : μ ∣ Δ ∣ Σ ⊢ q ∶ A ⊒ C)
  → (s⊒ : μ ∣ Δ ∣ Σ ⊢ s ∶ C ⊒ B)
  → Δ ∣ σ ⊢ proj₁ (_⨟ⁿ_ {wfΣ = wfΣ} q⊒ s⊒) ≈ r ∶ A ⊒ B
  → (wfΠ : StoreDetWf Δ Π)
  → (t⊒ : ν ∣ Δ ∣ Π ⊢ t ∶ A ⊒ D)
  → (p⊒ : ν ∣ Δ ∣ Π ⊢ p ∶ D ⊒ B)
  → Δ ∣ σ ⊢ r ≈ proj₁ (_⨟ⁿ_ {wfΣ = wfΠ} t⊒ p⊒) ∶ A ⊒ B
  → Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ Ap ⊒ Bp
  → Δ ∣ σ ∣ γ ⊢ M ⟨ - t ⟩ ⊒ M′ ⟨ - s ⟩ ∶ q ⦂ Aq ⊒ Bq
cast+⊒cast+-derivedᵗ {M = M} {M′ = M′} {s = s} {t = t}
    {typing = typing}
    pᶜ qᶜ wfΣ q⊒ s⊒ q⨟s≈r wfΠ t⊒ p⊒ r≈t⨟p M⊒M′
    with ⨟ⁿ≈-right-typing wfΣ q⊒ s⊒ q⨟s≈r
cast+⊒cast+-derivedᵗ {M = M} {M′ = M′} {s = s} {t = t}
    {typing = typing}
    pᶜ qᶜ wfΣ q⊒ s⊒ q⨟s≈r wfΠ t⊒ p⊒ r≈t⨟p M⊒M′
    | μ , r⊒ =
  ⊒cast+ᵗ {typing = typing} qᶜ wfΣ q⊒ s⊒ q⨟s≈r
    (cast+⊒ᵗ
      {typing =
        inner-cast+-typing {M = M} {M′ = M′} {s = s} {t = t}
          qᶜ wfΣ q⊒ s⊒ q⨟s≈r typing}
      pᶜ r⊒ wfΠ t⊒ p⊒ r≈t⨟p M⊒M′)
