module strong-rep-nu.proof.PeelDual where

-- File Charter:
--   * THE PEEL CROSSING — the dual is an INVERSE, and both of its
--     readings are theorems of strong-rep-nu.Boundary §3a.  §1
--     re-spells a TYPED conversion across the crossing (`respell-⊢`);
--     §2 splits the redex's `env` premises at the arrow; §3 is
--     `preserve-Peel`.
--   * THE ARGUMENT DOES NOT MOVE.  `dual-interior` says the dual's
--     interior IS the exterior, and since the store there is no bind
--     block, so it is the exterior ON THE NOSE — `⊢W` is reused
--     verbatim.
--   * THE DUAL'S CONVERSION CONTEXT is not free: (P) is FALSE here,
--     (Q) is what survives, and `Peel` therefore carries the dual's
--     own spelling `s′` with a `SameConv`.
-- Commentary: Commentary.md § proof/PeelDual.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.proof.Preserve using (PeelCase; same-wf)

------------------------------------------------------------------------
-- §1  Re-spelling a TYPED conversion
------------------------------------------------------------------------

sameTy-⇒ : ∀ (Γ Γ′ : Ctxᵗ) {A B C D : Ty}
  → Γ ⊢ A ≈ B ⊣ Γ′ → Γ ⊢ C ≈ D ⊣ Γ′
  → Γ ⊢ A ⇒ C ≈ B ⇒ D ⊣ Γ′
sameTy-⇒ Γ Γ′ (R , p , q) (S , p′ , q′) =
  R ⇒ S , same-⇒ p p′ , same-⇒ q q′

sameTy-∀ : ∀ (Γ Γ′ : Ctxᵗ) {A B : Ty}
  → underΛ Γ ⊢ A ≈ B ⊣ underΛ Γ′
  → Γ ⊢ `∀ A ≈ `∀ B ⊣ Γ′
sameTy-∀ Γ Γ′ (R , p , q) = `∀ R , same-∀ p , same-∀ q

-- `respell` (strong-rep-nu.Conversion §2c) produces a conversion's
-- other spelling; this produces its TYPING.  The two contexts share a
-- representation context and differ only in their ordinary name map.
-- Commentary.md § proof/PeelDual.agda / §1
respell-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {s s′ r : Conv} {A B : Ty}
  → reps Γ′ ≡ reps Γ
  → (names Γ) ⊆ᵃ (names Γ′)
  → names Γ ⊩ s ~ r
  → names Γ′ ⊩ s′ ~ r
  → Γ ⊢ s ∶ A ⇝ B
  → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
      ((Γ′ ⊢ s′ ∶ A′ ⇝ B′)
        × (Γ′ ⊢ A′ ≈ A ⊣ Γ) × (Γ′ ⊢ B′ ≈ B ⊣ Γ))
respell-⊢ eq f (sameᶜ-id same-ℕ) (sameᶜ-id same-ℕ) (conv-id base-ℕ) =
  `ℕ , `ℕ , conv-id base-ℕ
  , (`ℕ , same-ℕ , same-ℕ) , (`ℕ , same-ℕ , same-ℕ)
respell-⊢ eq f (sameᶜ-id same-𝔹) (sameᶜ-id same-𝔹) (conv-id base-𝔹) =
  `𝔹 , `𝔹 , conv-id base-𝔹
  , (`𝔹 , same-𝔹 , same-𝔹) , (`𝔹 , same-𝔹 , same-𝔹)
respell-⊢ eq f (sameᶜ-id (same-var d)) (sameᶜ-id (same-var d′))
          (conv-idv tv) =
  _ , _ , conv-idv (_ , d′)
  , (` _ , same-var d′ , same-var d) , (` _ , same-var d′ , same-var d)
respell-⊢ {Γ′ = Γ′} eq f (sameᶜ-seal d) (sameᶜ-seal d′)
          (conv-seal (α , R , dn , dr , pA))
  with respell-ty f pA
respell-⊢ {Γ′ = Γ′} eq f (sameᶜ-seal d) (sameᶜ-seal d′)
          (conv-seal (α , R , dn , dr , pA))
  | A′ , qA′ =
  A′ , _
  , conv-seal (α
              , R
              , subst (λ a → names Γ′ ∋ˡ _ := a) (∋ˡ-det d dn) d′
              , subst (λ Ξ → Ξ ∋ʳ α := bindR R) (sym eq) dr
              , qA′)
  , (R , qA′ , pA)
  , (` _ , same-var d′ , same-var d)
respell-⊢ {Γ′ = Γ′} eq f (sameᶜ-unseal d) (sameᶜ-unseal d′)
          (conv-unseal (α , R , dn , dr , pA))
  with respell-ty f pA
respell-⊢ {Γ′ = Γ′} eq f (sameᶜ-unseal d) (sameᶜ-unseal d′)
          (conv-unseal (α , R , dn , dr , pA))
  | A′ , qA′ =
  _ , A′
  , conv-unseal (α
                , R
                , subst (λ a → names Γ′ ∋ˡ _ := a) (∋ˡ-det d dn) d′
                , subst (λ Ξ → Ξ ∋ʳ α := bindR R) (sym eq) dr
                , qA′)
  , (` _ , same-var d′ , same-var d)
  , (R , qA′ , pA)
respell-⊢ {Γ = Γ} {Γ′ = Γ′} eq f (sameᶜ-fun a b) (sameᶜ-fun a′ b′)
          (conv-fun ⊢x ⊢y)
  with respell-⊢ eq f a a′ ⊢x | respell-⊢ eq f b b′ ⊢y
respell-⊢ {Γ = Γ} {Γ′ = Γ′} eq f (sameᶜ-fun a b) (sameᶜ-fun a′ b′)
          (conv-fun ⊢x ⊢y)
  | P₁ , Q₁ , ⊢x′ , smP₁ , smQ₁ | P₂ , Q₂ , ⊢y′ , smP₂ , smQ₂ =
  Q₁ ⇒ P₂ , P₁ ⇒ Q₂ , conv-fun ⊢x′ ⊢y′
  , sameTy-⇒ Γ′ Γ smQ₁ smP₂ , sameTy-⇒ Γ′ Γ smP₁ smQ₂
respell-⊢ {Γ = Γ} {Γ′ = Γ′} eq f (sameᶜ-all a) (sameᶜ-all a′)
          (conv-all ⊢x)
  with respell-⊢ {Γ = underΛ Γ} {Γ′ = underΛ Γ′}
                 (cong (abstR ∷_) eq) (⊆ᵃ-underΛ f) a a′ ⊢x
respell-⊢ {Γ = Γ} {Γ′ = Γ′} eq f (sameᶜ-all a) (sameᶜ-all a′)
          (conv-all ⊢x)
  | A₀ , B₀ , ⊢x′ , smA , smB =
  `∀ A₀ , `∀ B₀ , conv-all ⊢x′
  , sameTy-∀ Γ′ Γ smA , sameTy-∀ Γ′ Γ smB

------------------------------------------------------------------------
-- §2  Splitting the redex's premises at the arrow
------------------------------------------------------------------------

-- The interior type of a `_↦_` boundary is an arrow, because its
-- reading is.  Since the store this ONE inversion serves BOTH `env`
-- premises.
sameTy-⇒⁻ : ∀ {η η′ : TyCtx} {B A₁ B₁ : Ty}
  → ∃[ R ] ((η ⊢ B ~ R) × (η′ ⊢ A₁ ⇒ B₁ ~ R))
  → Σ[ Aᵢ ∈ Ty ] Σ[ Bᵢ ∈ Ty ] ((B ≡ Aᵢ ⇒ Bᵢ)
      × (∃[ R ] ((η ⊢ Aᵢ ~ R) × (η′ ⊢ A₁ ~ R)))
      × (∃[ S ] ((η ⊢ Bᵢ ~ S) × (η′ ⊢ B₁ ~ S))))
sameTy-⇒⁻ (R ⇒ S , same-⇒ p q , same-⇒ p′ q′) =
  _ , _ , refl , (R , p , p′) , (S , q , q′)

------------------------------------------------------------------------
-- §3  The crossing
------------------------------------------------------------------------

-- THE ARGUMENT DOES NOT MOVE ANY MORE: `⊢W` is reused verbatim.
-- Commentary.md § proof/PeelDual.agda / §3
preserve-Peel : PeelCase
preserve-Peel {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
              {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
              wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
              (⊢· (env mwΘ ⊢V (conv-fun ⊢s ⊢t) sameᵢ sameₑ
                       (wf-⇒ wA wC)) ⊢W)
  with interior-functional (bw-interior mwΘ) ri
     | conversion-functional (bw-conversion mwΘ) rc
preserve-Peel {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
              {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
              wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
              (⊢· (env mwΘ ⊢V (conv-fun ⊢s ⊢t) sameᵢ sameₑ
                       (wf-⇒ wA wC)) ⊢W)
  | refl | refl
  with sameTy-⇒⁻ sameᵢ | sameTy-⇒⁻ sameₑ
     | respell-⊢ (trans (conversion-reps rd)
                   (trans (interior-reps ri)
                          (sym (conversion-reps rc))))
                 (Q ri rc rd) rcᶜ rdᶜ ⊢s
preserve-Peel {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
              {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
              wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
              (⊢· (env mwΘ ⊢V (conv-fun ⊢s ⊢t) sameᵢ sameₑ
                       (wf-⇒ wA wC)) ⊢W)
  | refl | refl
  | Aᵢ , Bᵢ , refl , smAᵢ , smBᵢ
  | Aₑ , Cₑ , refl , smAₑ , smCₑ
  | P′ , Q′ , ⊢s′ , smP , smQ =
  env mwΘ (⊢· ⊢V arg) ⊢t smBᵢ smCₑ wC
  where
  -- the dual's frame: the exterior itself
  mwD : BoundaryWf Δᵢ (dual Θ) Δ Δᵈ
  mwD = bw (bw-interior-wf mwΘ) (dual-interior ri) rd

  -- the crossing argument's own exterior reading is the source spelling
  -- the dual's conversion wants
  sameᵢ-d : Δ ⊢ _ ≈ P′ ⊣ Δᵈ
  sameᵢ-d =
    proj₁ smAₑ , proj₁ (proj₂ smAₑ)
    , subst (λ T → names Δᵈ ⊢ P′ ~ T)
            (same-rep-unique (proj₂ (proj₂ smP)) (proj₂ (proj₂ smAₑ)))
            (proj₁ (proj₂ smP))

  sameₑ-d : Δᵢ ⊢ Aᵢ ≈ Q′ ⊣ Δᵈ
  sameₑ-d =
    proj₁ smAᵢ , proj₁ (proj₂ smAᵢ)
    , subst (λ T → names Δᵈ ⊢ Q′ ~ T)
            (same-rep-unique (proj₂ (proj₂ smQ))
                             (proj₂ (proj₂ smAᵢ)))
            (proj₁ (proj₂ smQ))

  arg : Δᵢ ∣ [] ⊢ (W ⟪ dual Θ , s′ ⟫) ⦂ Aᵢ
  arg = env mwD ⊢W ⊢s′ sameᵢ-d sameₑ-d
            (same-wf (proj₁ (proj₂ smAᵢ)))
