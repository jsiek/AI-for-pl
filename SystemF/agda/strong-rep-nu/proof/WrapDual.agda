module strong-rep-nu.proof.WrapDual where

-- File Charter:
--   * THE PEEL CROSSING — the dual is an INVERSE, and both of its
--     readings are theorems of strong-rep-nu.Boundary §3a.  §1
--     weakens a TYPED conversion across the crossing (`weaken-⊢`);
--     §2 splits the redex's `boundary` premises at the arrow; §3 is
--     `preserve-Wrap`.
--   * THE ARGUMENT DOES NOT MOVE.  `dual-interior` says the dual's
--     interior IS the exterior, and since the store there is no bind
--     block, so it is the exterior ON THE NOSE — `⊢W` is reused
--     verbatim.
--   * THE DUAL'S CONVERSION CONTEXT is not free: (P) is FALSE here,
--     (Q) is what survives, and `Wrap` therefore carries the dual's
--     own spelling `s′` with a `SameConv`.
--   * THE TYPES DO NOT MOVE (the Δ ∣ Θ experiment): `s′` has `s`'s
--     REPRESENTATION types, and its permissions move by `pm-dual` —
--     checked at `⁻` under `Θ`, it is checked at `⁺` under `dual Θ`.
-- Commentary: Commentary.md § proof/WrapDual.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-nu.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ; base-ℕ; base-𝔹)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.proof.Preserve using (WrapCase; same-wf)

------------------------------------------------------------------------
-- §1  Weakening a TYPED conversion
------------------------------------------------------------------------

-- A weakening keeps the SHAPE, so it keeps identity and the
-- cancellation side condition (the latter because names are unique).
mutual
  isIdᵐ-~ : ∀ {η g r} → η ⊩ᵐ g ~ r → IsIdᵐ g → IsIdᵐ r
  isIdᵐ-~ (sameᶜ-id p) i = tt
  isIdᵐ-~ (sameᶜ-fun p q) (i , j) = isIdᶜ-~ p i , isIdᶜ-~ q j
  isIdᵐ-~ (sameᶜ-all p) i = isIdᶜ-~ p i

  isIdᶜ-~ : ∀ {η c r} → η ⊩ c ~ r → IsIdᶜ c → IsIdᶜ r
  isIdᶜ-~ (sameᶜ-tail (sameᶜ-mid p)) i = isIdᵐ-~ p i
  isIdᶜ-~ (sameᶜ-tail (sameᶜ-seal d)) ()
  isIdᶜ-~ (sameᶜ-tail (sameᶜ-seal-seq p d)) ()
  isIdᶜ-~ (sameᶜ-unseal d) ()
  isIdᶜ-~ (sameᶜ-unseal-seq d p) ()

mutual
  isIdᵐ-~⁻ : ∀ {η g r} → η ⊩ᵐ g ~ r → IsIdᵐ r → IsIdᵐ g
  isIdᵐ-~⁻ (sameᶜ-id p) i = tt
  isIdᵐ-~⁻ (sameᶜ-fun p q) (i , j) = isIdᶜ-~⁻ p i , isIdᶜ-~⁻ q j
  isIdᵐ-~⁻ (sameᶜ-all p) i = isIdᶜ-~⁻ p i

  isIdᶜ-~⁻ : ∀ {η c r} → η ⊩ c ~ r → IsIdᶜ r → IsIdᶜ c
  isIdᶜ-~⁻ (sameᶜ-tail (sameᶜ-mid p)) i = isIdᵐ-~⁻ p i
  isIdᶜ-~⁻ (sameᶜ-tail (sameᶜ-seal d)) ()
  isIdᶜ-~⁻ (sameᶜ-tail (sameᶜ-seal-seq p d)) ()
  isIdᶜ-~⁻ (sameᶜ-unseal d) ()
  isIdᶜ-~⁻ (sameᶜ-unseal-seq d p) ()

¬isIdᶜ-~ : ∀ {η η′ c c′ r} → η ⊩ c ~ r → η′ ⊩ c′ ~ r
  → ¬ IsIdᶜ c → ¬ IsIdᶜ c′
¬isIdᶜ-~ p p′ n i′ = n (isIdᶜ-~⁻ p (isIdᶜ-~ p′ i′))

¬isIdᵀ-~ : ∀ {η η′ t t′ r} → η ⊩ᵀ t ~ r → η′ ⊩ᵀ t′ ~ r
  → ¬ IsIdᵀ t → ¬ IsIdᵀ t′
¬isIdᵀ-~ p p′ n = ¬isIdᶜ-~ (sameᶜ-tail p) (sameᶜ-tail p′) n

noCancelᵀ-~ : ∀ {η η′ X X′ α t t′ r} → Unique η
  → η ∋ˡ X := α → η′ ∋ˡ X′ := α
  → η ⊩ᵀ t ~ r → η′ ⊩ᵀ t′ ~ r → NoCancelᵀ X t → NoCancelᵀ X′ t′
noCancelᵀ-~ uq d d′ (sameᶜ-mid p) (sameᶜ-mid p′) nc = tt
noCancelᵀ-~ uq d d′ (sameᶜ-seal e) (sameᶜ-seal e′) nc refl =
  nc (unique-lookup uq d (subst (λ a → _ ∋ˡ _ := a)
                                (sym (∋ˡ-det d′ e′)) e))
noCancelᵀ-~ uq d d′ (sameᶜ-seal-seq p e) (sameᶜ-seal-seq p′ e′) nc =
  noCancelᵀ-~ uq d d′ p p′ nc

noCancel-~ : ∀ {η η′ X X′ α c c′ r} → Unique η
  → η ∋ˡ X := α → η′ ∋ˡ X′ := α
  → η ⊩ c ~ r → η′ ⊩ c′ ~ r → NoCancel X c → NoCancel X′ c′
noCancel-~ uq d d′ (sameᶜ-tail p) (sameᶜ-tail p′) nc =
  noCancelᵀ-~ uq d d′ p p′ nc
noCancel-~ uq d d′ (sameᶜ-unseal e) (sameᶜ-unseal e′) nc = tt
noCancel-~ uq d d′ (sameᶜ-unseal-seq e p) (sameᶜ-unseal-seq e′ p′) nc = tt

-- `weaken` (strong-rep-nu.Conversion §2c) produces a conversion's
-- other spelling; this produces its TYPING, at the SAME representation
-- types, under any scope that grants at least the same permissions
-- (`PermMap`).  The two contexts share a representation context; the
-- source context's names are unique, so `NoCancel` survives.
-- Commentary.md § proof/WrapDual.agda / §1
leaf-~ : ∀ {Γ Γ′ : Ctxᵗ} {X X′ α β A}
  → reps Γ′ ≡ reps Γ → names Γ ⊆ᵃ names Γ′
  → names Γ ∋ˡ X := α → names Γ′ ∋ˡ X′ := α
  → Γ ∋ X ⊸ β := A → Γ′ ∋ X′ ⊸ α := A
leaf-~ eq f d d′ (e , rd , B , q) with ∋ˡ-det d e
leaf-~ eq f d d′ (e , rd , B , q) | refl =
  d′ , subst (λ Ξ → Ξ ∋ʳ _ := bindR _) (sym eq) rd , weaken-ty f q

mutual
  weakenᵐ-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {Θ Θ′ p p′ g g′ r} {A B : Ty}
    → reps Γ′ ≡ reps Γ → Unique (names Γ) → names Γ ⊆ᵃ names Γ′
    → PermMap Θ p Θ′ p′
    → names Γ ⊩ᵐ g ~ r → names Γ′ ⊩ᵐ g′ ~ r
    → Γ ∣ Θ ⊢ᵐ[ p ] g ∶ A ⇝ B
    → Γ′ ∣ Θ′ ⊢ᵐ[ p′ ] g′ ∶ A ⇝ B
  weakenᵐ-⊢ eq uq f m (sameᶜ-id same-ℕ) (sameᶜ-id same-ℕ) (conv-id base-ℕ) =
    conv-id base-ℕ
  weakenᵐ-⊢ eq uq f m (sameᶜ-id same-𝔹) (sameᶜ-id same-𝔹) (conv-id base-𝔹) =
    conv-id base-𝔹
  weakenᵐ-⊢ eq uq f m (sameᶜ-id (same-var d)) (sameᶜ-id (same-var d′))
            (conv-idv e) with ∋ˡ-det d e
  ... | refl = conv-idv d′
  weakenᵐ-⊢ eq uq f m (sameᶜ-fun a b) (sameᶜ-fun a′ b′) (conv-fun ⊢x ⊢y) =
    conv-fun (weaken-⊢ eq uq f (pm-flip m) a a′ ⊢x)
             (weaken-⊢ eq uq f m b b′ ⊢y)
  weakenᵐ-⊢ {Γ = Γ} eq uq f m (sameᶜ-all a) (sameᶜ-all a′) (conv-all ⊢x) =
    conv-all (weaken-⊢ (cong (abstR ∷_) eq) (unique-underΛ {Γ = Γ} uq)
                       (⊆ᵃ-underΛ f) (pm-lift m) a a′ ⊢x)

  weakenᵀ-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {Θ Θ′ p p′ t t′ r} {A B : Ty}
    → reps Γ′ ≡ reps Γ → Unique (names Γ) → names Γ ⊆ᵃ names Γ′
    → PermMap Θ p Θ′ p′
    → names Γ ⊩ᵀ t ~ r → names Γ′ ⊩ᵀ t′ ~ r
    → Γ ∣ Θ ⊢ᵀ[ p ] t ∶ A ⇝ B
    → Γ′ ∣ Θ′ ⊢ᵀ[ p′ ] t′ ∶ A ⇝ B
  weakenᵀ-⊢ eq uq f m (sameᶜ-mid a) (sameᶜ-mid a′) (conv-mid ⊢g) =
    conv-mid (weakenᵐ-⊢ eq uq f m a a′ ⊢g)
  weakenᵀ-⊢ eq uq f m (sameᶜ-seal d) (sameᶜ-seal d′) (conv-seal dX ok)
    with leaf-~ eq f d d′ dX | ∋ˡ-det d (proj₁ dX)
  ... | dX′ | refl = conv-seal dX′ (pm-seal m ok)
  weakenᵀ-⊢ eq uq f m (sameᶜ-seal-seq a d) (sameᶜ-seal-seq a′ d′)
            (conv-seal-seq ⊢t dX ok n)
    with leaf-~ eq f d d′ dX | ∋ˡ-det d (proj₁ dX)
  ... | dX′ | refl =
    conv-seal-seq (weakenᵀ-⊢ eq uq f m a a′ ⊢t) dX′ (pm-seal m ok)
                  (¬isIdᵀ-~ a a′ n)

  weaken-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {Θ Θ′ p p′} {s s′ r : Conv} {A B : Ty}
    → reps Γ′ ≡ reps Γ → Unique (names Γ) → names Γ ⊆ᵃ names Γ′
    → PermMap Θ p Θ′ p′
    → names Γ ⊩ s ~ r
    → names Γ′ ⊩ s′ ~ r
    → Γ ∣ Θ ⊢[ p ] s ∶ A ⇝ B
    → Γ′ ∣ Θ′ ⊢[ p′ ] s′ ∶ A ⇝ B
  weaken-⊢ eq uq f m (sameᶜ-tail a) (sameᶜ-tail a′) (conv-tail ⊢t) =
    conv-tail (weakenᵀ-⊢ eq uq f m a a′ ⊢t)
  weaken-⊢ eq uq f m (sameᶜ-unseal d) (sameᶜ-unseal d′) (conv-unseal dX ok)
    with leaf-~ eq f d d′ dX | ∋ˡ-det d (proj₁ dX)
  ... | dX′ | refl = conv-unseal dX′ (pm-unseal m ok)
  weaken-⊢ eq uq f m (sameᶜ-unseal-seq d a) (sameᶜ-unseal-seq d′ a′)
           (conv-unseal-seq dX ok ⊢c n nc)
    with leaf-~ eq f d d′ dX | ∋ˡ-det d (proj₁ dX)
  ... | dX′ | refl =
    conv-unseal-seq dX′ (pm-unseal m ok) (weaken-⊢ eq uq f m a a′ ⊢c)
                    (¬isIdᶜ-~ a a′ n) (noCancel-~ uq d d′ a a′ nc)

------------------------------------------------------------------------
-- §2  Splitting the redex's premises at the arrow
------------------------------------------------------------------------

-- The interior type of a `_↦_` boundary is an arrow, because its
-- representation is.
same-⇒⁻ : ∀ {η : TyCtx} {B R S : Ty}
  → η ⊢ B ~ R ⇒ S
  → Σ[ B₁ ∈ Ty ] Σ[ B₂ ∈ Ty ]
      ((B ≡ B₁ ⇒ B₂) × (η ⊢ B₁ ~ R) × (η ⊢ B₂ ~ S))
same-⇒⁻ (same-⇒ p q) = _ , _ , refl , p , q

------------------------------------------------------------------------
-- §3  The crossing
------------------------------------------------------------------------

-- THE ARGUMENT DOES NOT MOVE, AND NEITHER DO THE TYPES: `⊢W` is reused
-- verbatim, and the crossed `s` is respelled at the SAME representation
-- types.  Its permissions move by `pm-dual`: checked at `⁻` under `Θ`,
-- it is checked at `⁺` under `dual Θ`.
-- Commentary.md § proof/WrapDual.agda / §3
preserve-Wrap : WrapCase
preserve-Wrap {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
              {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
              wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
              (⊢· (boundary mwΘ ⊢V (conv-tail (conv-mid (conv-fun ⊢s ⊢t)))
                       sameᵢ sameₑ (wf-⇒ wA wC)) ⊢W)
  with interior-functional (bw-interior mwΘ) ri
     | conversion-functional (bw-conversion mwΘ) rc
preserve-Wrap {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
              {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
              wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
              (⊢· (boundary mwΘ ⊢V (conv-tail (conv-mid (conv-fun ⊢s ⊢t)))
                       sameᵢ sameₑ (wf-⇒ wA wC)) ⊢W)
  | refl | refl
  with same-⇒⁻ sameᵢ | same-⇒⁻ sameₑ
preserve-Wrap {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
              {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
              wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
              (⊢· (boundary mwΘ ⊢V (conv-tail (conv-mid (conv-fun ⊢s ⊢t)))
                       sameᵢ sameₑ (wf-⇒ wA wC)) ⊢W)
  | refl | refl
  | Aᵢ , Bᵢ , refl , smAᵢ , smBᵢ
  | Aₑ , Cₑ , refl , smAₑ , smCₑ =
  boundary mwΘ (⊢· ⊢V arg) ⊢t smBᵢ smCₑ wC
  where
  -- the dual's frame: the exterior itself
  mwD : BoundaryWf Δᵢ (dual Θ) Δ Δᵈ
  mwD = bw (bw-interior-wf mwΘ) (dual-interior ri) rd

  ⊢s′ = weaken-⊢ (trans (conversion-reps rd)
                    (trans (interior-reps ri)
                           (sym (conversion-reps rc))))
                 (name-fn (bw-conversion-wf mwΘ))
                 (Q ri rc rd) pm-dual rcᶜ rdᶜ ⊢s

  arg : Δᵢ ∣ [] ⊢ (W ⟪ dual Θ , s′ ⟫) ⦂ Aᵢ
  arg = boundary mwD ⊢W ⊢s′ smAₑ smAᵢ (same-wf smAᵢ)
