module strong-rep-store.proof.PeelDual where

-- THE PEEL CROSSING — the dual is an INVERSE, and both of its readings
-- are theorems of `strong-rep-store.Boundary` §3a.
--
--   Δ ⊢ⁱ Θ ⇒ Δᵢ  →  Δᵢ ⊢ⁱ dualBoundary Θ ⇒ Δ
--
-- is `dual-interior`: the crossing argument's frame IS THE EXTERIOR.
-- Since the store experiment (2026-09-22) a boundary scope carries no
-- bind block, so that is the exterior ON THE NOSE — the argument, typed
-- at Δ, crosses VERBATIM and gains neither ordinary scope nor a
-- representation binder.  The rule's old
-- `renᴹ² (ren² idᵗ (wkN (numBinds Θ)))`, and with it this module's
-- `RepWeakenTyping` parameter and the `renᴹ²-ord-id` bridge, are gone.
--
-- The dual's CONVERSION context is the one thing the crossing does not
-- get for free.  It is not `convCtx Θ Δ` renumbered: (P), the identity
-- `conv(dual Θ, int(Θ, Δ)) ≡ conv(Θ, Δ)`, is a theorem on `main` and is
-- FALSE here, because deleting a name from a SEQUENCE renumbers the rest
-- (notes/CrossingAudit §§4–6).  What survives is (Q) — the two contexts
-- name the same representation VARIABLES (`Q`,
-- strong-rep-store.Boundary §3b) — and `Peel` therefore carries the
-- dual's own spelling `s′` together with a `SameConv` relating it to
-- `s`.  §1 below is what turns that premise into the dual boundary's
-- conversion typing.
--
--   §1  re-spelling a TYPED conversion across the crossing
--   §2  the ⇒-splitting the redex's `env` premises need
--   §3  the crossing, and `preserve-Peel`
--
-- WHAT WAS DELETED (2026-09-19).  The whole masked-entry development:
-- `applyChanges-dualScope`, `⊢ˢ-dualScope`, `applyUnlocks-dualScope` and
-- their `updateAt` commutations (old §2); `interior-dual`, `convCtx-dual`
-- — which was (P) — and `applyUnlocks-hideBinds` (old §3); and the
-- `Ren`/`wkN` crossing machinery `⊢ᵐ-dual`, `Ren-wkN`, `crossing` (old
-- §4).  None of them has a two-universe counterpart: there is no computed
-- context to state an equality between, (P) is refuted, and the frame
-- identity is `dual-interior`.  AND (2026-09-22) `shiftRep-⇒` and
-- `sameTyExt-⇒⁻`: the exterior comparison is now the same relation at the
-- same depth, so `sameTy-⇒⁻` serves both `env` premises.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.proof.Preserve using (PeelCase; same-wf)

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

-- `respell` (strong-rep-store.Conversion §2c) produces a conversion's other
-- spelling; this produces its TYPING.  The two contexts share a
-- representation context and differ only in their ordinary name map, so
-- every leaf transports: a `seal`/`unseal` cites the SAME binder and only
-- its ordinary spelling changes, and an identity's payload is re-spelled
-- by `respell-ty`.  The source and target types come back paired with
-- `_⊢_≈_⊣_`s, which is what the crossing boundary's `env` consumes.
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

-- The interior type of a boundary whose conversion is a `_↦_` is an
-- arrow, because its reading is.  Since the store experiment the
-- EXTERIOR comparison is the same relation at the same depth, so this
-- one inversion serves both `env` premises.
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

-- THE ARGUMENT DOES NOT MOVE ANY MORE.  W is typed on the exterior Δ,
-- and the dual's interior IS Δ (`dual-interior`, strong-rep-store.Boundary
-- §3a): since the store experiment a boundary scope carries no bind
-- block, so there is nothing for the crossing argument to be shifted
-- past.  The rule's old `renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W` — and
-- with it the whole `RepWeakenTyping` parameter this module used to take
-- — is gone; `⊢W` is reused verbatim.
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
  mwD : BoundaryWf Δᵢ (dualBoundary Θ) Δ Δᵈ
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

  arg : Δᵢ ∣ [] ⊢ (W ⟪ dualBoundary Θ , s′ ⟫) ⦂ Aᵢ
  arg = env mwD ⊢W ⊢s′ sameᵢ-d sameₑ-d
            (same-wf (proj₁ (proj₂ smAᵢ)))
