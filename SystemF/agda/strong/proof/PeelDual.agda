module strong.proof.PeelDual where

-- THE PEEL CROSSING — the dual is an INVERSE, and both of its readings
-- are theorems of `strong.CtxMorph` §3a.
--
--   Δ ⊢ⁱ Θ ⇒ Δᵢ  →  Δᵢ ⊢ⁱ dualMorph Θ ⇒ extendReps (binds Θ) Δ
--
-- is `dual-interior`: the crossing argument's frame IS THE EXTERIOR, one
-- bind block in.  So the argument, typed at Δ, crosses by a
-- REPRESENTATION-ONLY weakening — `renᴹ² (ren² idᵗ (wkN (numBinds Θ)))`
-- — and gains no ordinary scope whatever.
--
-- The dual's CONVERSION context is the one thing the crossing does not
-- get for free.  It is not `convCtx Θ Δ` renumbered: (P), the identity
-- `conv(dual Θ, int(Θ, Δ)) ≡ conv(Θ, Δ)`, is a theorem on `main` and is
-- FALSE here, because deleting a name from a SEQUENCE renumbers the rest
-- (notes/CrossingAudit §§4–6).  What survives is (Q) — the two contexts
-- name the same representation VARIABLES (`Q`, strong.CtxMorph §3b) —
-- and `Peel` therefore carries the dual's own spelling `s′` together with
-- a `SameConv` relating it to `s`.  §1 below is what turns that premise
-- into the dual boundary's conversion typing.
--
--   §1  re-spelling a TYPED conversion across the crossing
--   §2  the ⇒-splittings the redex's `env` premises need
--   §3  the crossing, and `preserve-Peel`
--
-- WHAT WAS DELETED (2026-09-19).  The whole masked-entry development:
-- `applyChanges-dualScope`, `⊢ˢ-dualScope`, `applyUnlocks-dualScope` and
-- their `updateAt` commutations (old §2); `interior-dual`, `convCtx-dual`
-- — which was (P) — and `applyUnlocks-hideBinds` (old §3); and the
-- `Ren`/`wkN` crossing machinery `⊢ᵐ-dual`, `Ren-wkN`, `crossing` (old
-- §4).  None of them has a two-universe counterpart: there is no computed
-- context to state an equality between, (P) is refuted, and the frame
-- identity is `dual-interior`.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst using (renᴹ²; ren²; idᵗ; wkN)
open import strong.CtxMorph
open import strong.proof.Preserve
  using (PeelCase; RepWeakenTyping; same-shiftRVars; shiftRep-shiftBy;
         same-wf)

------------------------------------------------------------------------
-- §1  Re-spelling a TYPED conversion
------------------------------------------------------------------------

sameTy-⇒ : ∀ (Γ Γ′ : Ctxᵗ) {A B C D : Ty}
  → SameTy Γ A Γ′ B → SameTy Γ C Γ′ D → SameTy Γ (A ⇒ C) Γ′ (B ⇒ D)
sameTy-⇒ Γ Γ′ (R , p , q) (S , p′ , q′) =
  R ⇒ S , same-⇒ p p′ , same-⇒ q q′

sameTy-∀ : ∀ (Γ Γ′ : Ctxᵗ) {A B : Ty}
  → SameTy (underΛ Γ) A (underΛ Γ′) B → SameTy Γ (`∀ A) Γ′ (`∀ B)
sameTy-∀ Γ Γ′ (R , p , q) = `∀ R , same-∀ p , same-∀ q

-- `respell` (strong.Conversion §2c) produces a conversion's other
-- spelling; this produces its TYPING.  The two contexts share a
-- representation context and differ only in their ordinary name map, so
-- every leaf transports: a `seal`/`unseal` cites the SAME binder and only
-- its ordinary spelling changes, and an identity's payload is re-spelled
-- by `respell-ty`.  The source and target types come back paired with
-- `SameTy`s, which is what the crossing boundary's `env` consumes.
respell-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {s s′ r : Conv} {A B : Ty}
  → reps Γ′ ≡ reps Γ
  → Keeps (names Γ) (names Γ′)
  → names Γ ⊩ s ~ r
  → names Γ′ ⊩ s′ ~ r
  → Γ ⊢ s ∶ A ⇝ B
  → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
      ((Γ′ ⊢ s′ ∶ A′ ⇝ B′) × SameTy Γ′ A′ Γ A × SameTy Γ′ B′ Γ B)
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
                 (cong (abstR ∷_) eq) (keeps-underΛ f) a a′ ⊢x
respell-⊢ {Γ = Γ} {Γ′ = Γ′} eq f (sameᶜ-all a) (sameᶜ-all a′)
          (conv-all ⊢x)
  | A₀ , B₀ , ⊢x′ , smA , smB =
  `∀ A₀ , `∀ B₀ , conv-all ⊢x′
  , sameTy-∀ Γ′ Γ smA , sameTy-∀ Γ′ Γ smB

------------------------------------------------------------------------
-- §2  Splitting the redex's premises at the arrow
------------------------------------------------------------------------

shiftRep-⇒ : (n : ℕ) (R S : Ty)
  → shiftRep n (R ⇒ S) ≡ shiftRep n R ⇒ shiftRep n S
shiftRep-⇒ zero R S = refl
shiftRep-⇒ (suc n) R S rewrite shiftRep-⇒ n R S = refl

-- The interior type of a boundary whose conversion is a `_↦_` is an
-- arrow, because its reading is.
sameTy-⇒⁻ : ∀ {η η′ : TyCtx} {B A₁ B₁ : Ty}
  → ∃[ R ] ((η ⊢ B ~ R) × (η′ ⊢ A₁ ⇒ B₁ ~ R))
  → Σ[ Aᵢ ∈ Ty ] Σ[ Bᵢ ∈ Ty ] ((B ≡ Aᵢ ⇒ Bᵢ)
      × (∃[ R ] ((η ⊢ Aᵢ ~ R) × (η′ ⊢ A₁ ~ R)))
      × (∃[ S ] ((η ⊢ Bᵢ ~ S) × (η′ ⊢ B₁ ~ S))))
sameTy-⇒⁻ (R ⇒ S , same-⇒ p q , same-⇒ p′ q′) =
  _ , _ , refl , (R , p , p′) , (S , q , q′)

sameTyExt-⇒⁻ : ∀ (n : ℕ) {η η′ : TyCtx} {A C A₁ B₁ : Ty}
  → ∃[ R ] ((η ⊢ A ⇒ C ~ R) × (η′ ⊢ A₁ ⇒ B₁ ~ shiftRep n R))
  → (∃[ R ] ((η ⊢ A ~ R) × (η′ ⊢ A₁ ~ shiftRep n R)))
    × (∃[ S ] ((η ⊢ C ~ S) × (η′ ⊢ B₁ ~ shiftRep n S)))
sameTyExt-⇒⁻ n {η′ = η′} (R ⇒ S , same-⇒ p q , t)
  with subst (λ T → η′ ⊢ _ ~ T) (shiftRep-⇒ n R S) t
sameTyExt-⇒⁻ n {η′ = η′} (R ⇒ S , same-⇒ p q , t)
  | same-⇒ p′ q′ = (R , p , p′) , (S , q , q′)

------------------------------------------------------------------------
-- §3  The crossing
------------------------------------------------------------------------

-- THE ONE THING THE CASE CANNOT BUILD.  The argument W is typed on the
-- exterior Δ and must be retyped on `extendReps (binds Θ) Δ`, which is
-- the same context with the boundary's representation bind block pushed
-- on.  Its ordinary name map is untouched, so the argument's TYPE does
-- not change; only representation occurrences inside its own frames move,
-- which is exactly what `renᴹ² (ren² idᵗ (wkN (numBinds Θ)))` does.  This
-- is the third representation-only typing transport the port has needed
-- (`CrossΛTyping`, `AddLock0Typing`, strong.proof.Preserve §4), and like
-- those it is a NEW MAJOR STATEMENT, deferred for review rather than
-- proved here.
module _ (repWeaken : RepWeakenTyping) where

  preserve-Peel : PeelCase
  preserve-Peel {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
                {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
                wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
                (⊢· (env mwΘ ⊢V (conv-fun ⊢s ⊢t) sameᵢ sameₑ
                         (wf-⇒ wA wC)) ⊢W)
    with interior-functional (mw-interior mwΘ) ri
       | conversion-functional (mw-conversion mwΘ) rc
  preserve-Peel {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
                {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
                wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
                (⊢· (env mwΘ ⊢V (conv-fun ⊢s ⊢t) sameᵢ sameₑ
                         (wf-⇒ wA wC)) ⊢W)
    | refl | refl
    with sameTy-⇒⁻ sameᵢ | sameTyExt-⇒⁻ (numBinds Θ) sameₑ
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
    | (Ra , pA , qA) , (Rc , pC , qC)
    | P′ , Q′ , ⊢s′ , smP , smQ =
    env mwΘ (⊢· ⊢V arg) ⊢t smBᵢ (Rc , pC , qC) wC
    where
    n : ℕ
    n = numBinds Θ

    -- the dual's frame: the exterior, one bind block in
    mwD : MorphWf Δᵢ (dualMorph Θ) (extendReps (binds Θ) Δ) Δᵈ
    mwD = mw (mw-interior-wf mwΘ) binds[] (dual-interior ri) rd

    -- the crossing argument's own exterior reading, lifted past the
    -- bind block, is the source spelling the dual's conversion wants
    sameᵢ-d : SameTy (extendReps (binds Θ) Δ) _ Δᵈ P′
    sameᵢ-d =
      shiftBy n Ra
      , same-shiftRVars n pA
      , subst (λ T → names Δᵈ ⊢ P′ ~ T)
              (trans (same-rep-unique (proj₂ (proj₂ smP)) qA)
                     (shiftRep-shiftBy n Ra))
              (proj₁ (proj₂ smP))

    sameₑ-d : SameTyExt (numBinds (dualMorph Θ)) Δᵢ Aᵢ Δᵈ Q′
    sameₑ-d =
      proj₁ smAᵢ , proj₁ (proj₂ smAᵢ)
      , subst (λ T → names Δᵈ ⊢ Q′ ~ T)
              (same-rep-unique (proj₂ (proj₂ smQ))
                               (proj₂ (proj₂ smAᵢ)))
              (proj₁ (proj₂ smQ))

    arg : Δᵢ ∣ [] ⊢
        (renᴹ² (ren² (λ X → X) (wkN n)) W ⟪ dualMorph Θ , s′ ⟫) ⦂ Aᵢ
    arg = env mwD (repWeaken (binds Θ) ⊢W) ⊢s′ sameᵢ-d sameₑ-d
              (same-wf (proj₁ (proj₂ smAᵢ)))
