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
-- Commentary: Commentary.md § proof/WrapDual.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.proof.Preserve using (WrapCase; same-wf)

------------------------------------------------------------------------
-- §1  Weakening a TYPED conversion
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
-- other spelling; this produces its TYPING.  The two contexts share a
-- representation context and differ only in their ordinary name map;
-- the source context's names are unique, so `NoCancel` survives.
-- Commentary.md § proof/WrapDual.agda / §1
-- the lookup square, re-read on the second name map
lookup-~ : ∀ {Γ Γ′ : Ctxᵗ} {X X′ α A}
  → reps Γ′ ≡ reps Γ → names Γ ⊆ᵃ names Γ′
  → names Γ ∋ˡ X := α → names Γ′ ∋ˡ X′ := α
  → Γ ∋ X := A
  → Σ[ A′ ∈ Ty ] ((Γ′ ∋ X′ := A′) × (Γ′ ⊢ A′ ≈ A ⊣ Γ))
lookup-~ {Γ′ = Γ′} eq f d d′ (α , R , dn , dr , pA)
  with weaken-ty f pA
lookup-~ {Γ′ = Γ′} eq f d d′ (α , R , dn , dr , pA) | A′ , qA′ =
  A′
  , (α , R
    , subst (λ a → names Γ′ ∋ˡ _ := a) (∋ˡ-det d dn) d′
    , subst (λ Ξ → Ξ ∋ʳ α := bindR R) (sym eq) dr
    , qA′)
  , (R , qA′ , pA)

-- the same, when the representation's second spelling is already known
lookup-~′ : ∀ {Γ Γ′ : Ctxᵗ} {X X′ α A A′}
  → reps Γ′ ≡ reps Γ
  → names Γ ∋ˡ X := α → names Γ′ ∋ˡ X′ := α
  → Γ ∋ X := A → Γ′ ⊢ A′ ≈ A ⊣ Γ
  → Γ′ ∋ X′ := A′
lookup-~′ {Γ′ = Γ′} eq d d′ (α , R , dn , dr , pA) (S , q′ , q) =
  α , R
  , subst (λ a → names Γ′ ∋ˡ _ := a) (∋ˡ-det d dn) d′
  , subst (λ Ξ → Ξ ∋ʳ α := bindR R) (sym eq) dr
  , subst (λ T → names Γ′ ⊢ _ ~ T) (same-rep-unique q pA) q′

mutual
  weakenᵐ-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {g g′ r} {A B : Ty}
    → reps Γ′ ≡ reps Γ → Unique (names Γ)
    → (names Γ) ⊆ᵃ (names Γ′)
    → names Γ ⊩ᵐ g ~ r → names Γ′ ⊩ᵐ g′ ~ r
    → Γ ⊢ᵐ g ∶ A ⇝ B
    → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
        ((Γ′ ⊢ᵐ g′ ∶ A′ ⇝ B′)
          × (Γ′ ⊢ A′ ≈ A ⊣ Γ) × (Γ′ ⊢ B′ ≈ B ⊣ Γ))
  weakenᵐ-⊢ eq uq f (sameᶜ-id same-ℕ) (sameᶜ-id same-ℕ) (conv-id base-ℕ) =
    `ℕ , `ℕ , conv-id base-ℕ
    , (`ℕ , same-ℕ , same-ℕ) , (`ℕ , same-ℕ , same-ℕ)
  weakenᵐ-⊢ eq uq f (sameᶜ-id same-𝔹) (sameᶜ-id same-𝔹) (conv-id base-𝔹) =
    `𝔹 , `𝔹 , conv-id base-𝔹
    , (`𝔹 , same-𝔹 , same-𝔹) , (`𝔹 , same-𝔹 , same-𝔹)
  weakenᵐ-⊢ eq uq f (sameᶜ-id (same-var d)) (sameᶜ-id (same-var d′))
            (conv-idv tv) =
    _ , _ , conv-idv (_ , d′)
    , (` _ , same-var d′ , same-var d) , (` _ , same-var d′ , same-var d)
  weakenᵐ-⊢ {Γ = Γ} {Γ′ = Γ′} eq uq f (sameᶜ-fun a b) (sameᶜ-fun a′ b′)
            (conv-fun ⊢x ⊢y)
    with weaken-⊢ eq uq f a a′ ⊢x | weaken-⊢ eq uq f b b′ ⊢y
  weakenᵐ-⊢ {Γ = Γ} {Γ′ = Γ′} eq uq f (sameᶜ-fun a b) (sameᶜ-fun a′ b′)
            (conv-fun ⊢x ⊢y)
    | P₁ , Q₁ , ⊢x′ , smP₁ , smQ₁ | P₂ , Q₂ , ⊢y′ , smP₂ , smQ₂ =
    Q₁ ⇒ P₂ , P₁ ⇒ Q₂ , conv-fun ⊢x′ ⊢y′
    , sameTy-⇒ Γ′ Γ smQ₁ smP₂ , sameTy-⇒ Γ′ Γ smP₁ smQ₂
  weakenᵐ-⊢ {Γ = Γ} {Γ′ = Γ′} eq uq f (sameᶜ-all a) (sameᶜ-all a′)
            (conv-all ⊢x)
    with weaken-⊢ {Γ = underΛ Γ} {Γ′ = underΛ Γ′}
                   (cong (abstR ∷_) eq) (unique-underΛ {Γ = Γ} uq)
                   (⊆ᵃ-underΛ f) a a′ ⊢x
  weakenᵐ-⊢ {Γ = Γ} {Γ′ = Γ′} eq uq f (sameᶜ-all a) (sameᶜ-all a′)
            (conv-all ⊢x)
    | A₀ , B₀ , ⊢x′ , smA , smB =
    `∀ A₀ , `∀ B₀ , conv-all ⊢x′
    , sameTy-∀ Γ′ Γ smA , sameTy-∀ Γ′ Γ smB

  weakenᵀ-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {t t′ r} {A B : Ty}
    → reps Γ′ ≡ reps Γ → Unique (names Γ)
    → (names Γ) ⊆ᵃ (names Γ′)
    → names Γ ⊩ᵀ t ~ r → names Γ′ ⊩ᵀ t′ ~ r
    → Γ ⊢ᵀ t ∶ A ⇝ B
    → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
        ((Γ′ ⊢ᵀ t′ ∶ A′ ⇝ B′)
          × (Γ′ ⊢ A′ ≈ A ⊣ Γ) × (Γ′ ⊢ B′ ≈ B ⊣ Γ))
  weakenᵀ-⊢ eq uq f (sameᶜ-mid a) (sameᶜ-mid a′) (conv-mid ⊢g)
    with weakenᵐ-⊢ eq uq f a a′ ⊢g
  weakenᵀ-⊢ eq uq f (sameᶜ-mid a) (sameᶜ-mid a′) (conv-mid ⊢g)
    | A′ , B′ , ⊢g′ , smA , smB = A′ , B′ , conv-mid ⊢g′ , smA , smB
  weakenᵀ-⊢ eq uq f (sameᶜ-seal d) (sameᶜ-seal d′) (conv-seal dX)
    with lookup-~ eq f d d′ dX
  weakenᵀ-⊢ eq uq f (sameᶜ-seal d) (sameᶜ-seal d′) (conv-seal dX)
    | A′ , dX′ , smA =
    A′ , _ , conv-seal dX′ , smA , (` _ , same-var d′ , same-var d)
  weakenᵀ-⊢ eq uq f (sameᶜ-seal-seq a d) (sameᶜ-seal-seq a′ d′)
            (conv-seal-seq ⊢t dX n)
    with weakenᵀ-⊢ eq uq f a a′ ⊢t
  weakenᵀ-⊢ eq uq f (sameᶜ-seal-seq a d) (sameᶜ-seal-seq a′ d′)
            (conv-seal-seq ⊢t dX n)
    | A′ , R′ , ⊢t′ , smA , smR =
    A′ , _
    , conv-seal-seq ⊢t′ (lookup-~′ eq d d′ dX smR) (¬isIdᵀ-~ a a′ n)
    , smA , (` _ , same-var d′ , same-var d)

  weaken-⊢ : ∀ {Γ Γ′ : Ctxᵗ} {s s′ r : Conv} {A B : Ty}
    → reps Γ′ ≡ reps Γ → Unique (names Γ)
    → (names Γ) ⊆ᵃ (names Γ′)
    → names Γ ⊩ s ~ r
    → names Γ′ ⊩ s′ ~ r
    → Γ ⊢ s ∶ A ⇝ B
    → Σ[ A′ ∈ Ty ] Σ[ B′ ∈ Ty ]
        ((Γ′ ⊢ s′ ∶ A′ ⇝ B′)
          × (Γ′ ⊢ A′ ≈ A ⊣ Γ) × (Γ′ ⊢ B′ ≈ B ⊣ Γ))
  weaken-⊢ eq uq f (sameᶜ-tail a) (sameᶜ-tail a′) (conv-tail ⊢t)
    with weakenᵀ-⊢ eq uq f a a′ ⊢t
  weaken-⊢ eq uq f (sameᶜ-tail a) (sameᶜ-tail a′) (conv-tail ⊢t)
    | A′ , B′ , ⊢t′ , smA , smB = A′ , B′ , conv-tail ⊢t′ , smA , smB
  weaken-⊢ eq uq f (sameᶜ-unseal d) (sameᶜ-unseal d′) (conv-unseal dX)
    with lookup-~ eq f d d′ dX
  weaken-⊢ eq uq f (sameᶜ-unseal d) (sameᶜ-unseal d′) (conv-unseal dX)
    | B′ , dX′ , smB =
    _ , B′ , conv-unseal dX′ , (` _ , same-var d′ , same-var d) , smB
  weaken-⊢ eq uq f (sameᶜ-unseal-seq d a) (sameᶜ-unseal-seq d′ a′)
            (conv-unseal-seq dX ⊢c n m)
    with weaken-⊢ eq uq f a a′ ⊢c
  weaken-⊢ eq uq f (sameᶜ-unseal-seq d a) (sameᶜ-unseal-seq d′ a′)
            (conv-unseal-seq dX ⊢c n m)
    | R′ , B′ , ⊢c′ , smR , smB =
    _ , B′
    , conv-unseal-seq (lookup-~′ eq d d′ dX smR) ⊢c′ (¬isIdᶜ-~ a a′ n)
                      (noCancel-~ uq d d′ a a′ m)
    , (` _ , same-var d′ , same-var d) , smB

------------------------------------------------------------------------
-- §2  Splitting the redex's premises at the arrow
------------------------------------------------------------------------

-- The interior type of a `_↦_` boundary is an arrow, because its
-- reading is.  Since the store this ONE inversion serves BOTH `boundary`
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
  with sameTy-⇒⁻ sameᵢ | sameTy-⇒⁻ sameₑ
     | weaken-⊢ (trans (conversion-reps rd)
                   (trans (interior-reps ri)
                          (sym (conversion-reps rc))))
                 (name-fn (bw-conversion-wf mwΘ))
                 (Q ri rc rd) rcᶜ rdᶜ ⊢s
preserve-Wrap {Δ = Δ} {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} {Δᵈ = Δᵈ} {V = V} {W = W}
              {Θ = Θ} {s = s} {s′ = s′} {t = t} {C = C}
              wfΔ v w rc ri rd (r , rdᶜ , rcᶜ)
              (⊢· (boundary mwΘ ⊢V (conv-tail (conv-mid (conv-fun ⊢s ⊢t)))
                       sameᵢ sameₑ (wf-⇒ wA wC)) ⊢W)
  | refl | refl
  | Aᵢ , Bᵢ , refl , smAᵢ , smBᵢ
  | Aₑ , Cₑ , refl , smAₑ , smCₑ
  | P′ , Q′ , ⊢s′ , smP , smQ =
  boundary mwΘ (⊢· ⊢V arg) ⊢t smBᵢ smCₑ wC
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
  arg = boundary mwD ⊢W ⊢s′ sameᵢ-d sameₑ-d
            (same-wf (proj₁ (proj₂ smAᵢ)))
