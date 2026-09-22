module strong-rep-store.proof.Progress where

-- File Charter:
--   * PROGRESS for the two-universe conversion-boundary calculus.
--     §1 local inversions and representation readings; §2 the boundary
--     reading packages (`MergedReading`, `addLock0-reading`); §3 base
--     identities; §4 the boundary cases; §5 the induction.
--   * The ordinary cases are the standard induction over
--     strong-rep-store.proof.Canonical; the boundary cases additionally
--     CONSTRUCT the relational readings and re-spellings the rules
--     carry.  Nothing is a parameter: `MergedReading` comes from
--     `merged-conversion-exists` and `addLock0-reading` from
--     `snoc-lock0-conversion-ren`.
--   * PROGRESS RETURNS THE STORE CHANGE TOO: every clause names the
--     `δ` its rule makes.
-- Commentary: Commentary.md § proof/Progress.agda

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; _++_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; extᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.TermSubst
open import strong-rep-store.Reduction
open import strong-rep-store.proof.Canonical
open import strong-rep-store.proof.Preserve using (inst-boundarywf)

private
  variable
    Δ Δ′ : Ctxᵗ
    A B R : Ty
    X α : ℕ

------------------------------------------------------------------------
-- 1. Local inversions and representation readings
------------------------------------------------------------------------

wf-same : Δ ⊢ᵗ A → ∃[ R ] names Δ ⊢ A ~ R
wf-same (wf-var (α , name)) = ` α , same-var name
wf-same wf-ℕ = `ℕ , same-ℕ
wf-same wf-𝔹 = `𝔹 , same-𝔹
wf-same (wf-⇒ wA wB) with wf-same wA | wf-same wB
wf-same (wf-⇒ wA wB) | R , p | S , q = R ⇒ S , same-⇒ p q
wf-same (wf-∀ wA) with wf-same wA
wf-same (wf-∀ wA) | R , p = `∀ R , same-∀ p

sameTy-base-src : Base A → Δ ⊢ B ≈ A ⊣ Δ′ → B ≡ A
sameTy-base-src base-ℕ (`ℕ , same-ℕ , same-ℕ) = refl
sameTy-base-src base-𝔹 (`𝔹 , same-𝔹 , same-𝔹) = refl

sameTy-target-var⁻ : Δ ⊢ A ≈ ` X ⊣ Δ′
  → Σ[ Y ∈ ℕ ] ((A ≡ ` Y) × (Δ ⊢ ` Y ≈ ` X ⊣ Δ′))
sameTy-target-var⁻ (` α , same-var p , same-var q) =
  _ , refl , (` α , same-var p , same-var q)

sameTy-target-∀⁻ : Δ ⊢ A ≈ `∀ B ⊣ Δ′
  → Σ[ A₀ ∈ Ty ] ((A ≡ `∀ A₀)
      × (underΛ Δ ⊢ A₀ ≈ B ⊣ underΛ Δ′))
sameTy-target-∀⁻ (`∀ R , same-∀ p , same-∀ q) =
  _ , refl , (R , p , q)

------------------------------------------------------------------------
-- 2. The boundary reading packages
------------------------------------------------------------------------

-- The conversion reading of `Θ₁ ++ Θ₂` retains the source whose
-- spelling both id-layer rules move into that merged frame.  `` ⊆ᵃ
-- states only NAME availability; `respell-ty` then constructs the
-- `_⊢_≈_⊣_` premise at the exact type being moved.
-- Commentary.md § proof/Progress.agda / §2
MergedReading : Set
MergedReading = ∀ {Δ Δᵢ Δᶜ Δ₁ᵢ Δ₁ᶜ Θ₁ Θ₂}
  → BoundaryWf Δ Θ₂ Δᵢ Δᶜ
  → BoundaryWf Δᵢ Θ₁ Δ₁ᵢ Δ₁ᶜ
  → Σ[ Δ⋉ᶜ ∈ Ctxᵗ ]
      ((Δ ⊢ᶜ Θ₁ ++ Θ₂ ⇒ Δ⋉ᶜ)
        × (names Δ₁ᶜ) ⊆ᵃ (names Δ⋉ᶜ))

merged-reading : MergedReading
merged-reading = merged-conversion-exists

-- THE MOVED BOUNDARY'S OWN READING (2026-09-20, the repair's progress
-- obligation).  THE RENAMING IS THE WHOLE POINT: the retained names
-- are `map suc (names Δ′ᶜ)`, not `names Δ′ᶜ`; the unrenamed inclusion
-- is FALSE, and §6b of strong-rep-store.Examples is the witness.
-- Commentary.md § proof/Progress.agda / §2
addLock0-reading : ∀ {Δ Δᵢ Δᶜ Δ′ᵢ Δ′ᶜ Θ Θ′ A R}
  → BoundaryWf Δ Θ Δᵢ Δᶜ
  → BoundaryWf Δᵢ Θ′ Δ′ᵢ Δ′ᶜ
  → names Δ ⊢ A ~ R
  → Σ[ Δ″ᶜ ∈ Ctxᵗ ]
      ((((bindR R ∷ reps Δᵢ) ∣ (zero ∷ shiftReps (names Δᵢ)))
          ⊢ᶜ (renᴮᴿ suc Θ′ ++ (lock 0 0 ∷ [])) ⇒ Δ″ᶜ)
        × (map suc (names Δ′ᶜ) ⊆ᵃ (names Δ″ᶜ)))
addLock0-reading {R = R} mwΘ mw′ p =
  snoc-lock0-conversion-ren
    (repwk-cons₀ (bindR R)
      (λ _ → wf-reps (bw-interior-wf (inst-boundarywf mwΘ p))))
    (_ , here)
    (name-fn (bw-interior-wf mwΘ))
    (bw-conversion mw′)

------------------------------------------------------------------------
-- 3. Base identities
------------------------------------------------------------------------

progress-id-base : ∀ {Δ Δᵢ Θ M A}
  → Value M
  → Base A
  → Δᵢ ∣ [] ⊢ M ⦂ A
  → Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ] (Δ ⊢ M ⟪ Θ , id A ⟫ -→ M′ ∣ δ)
progress-id-base v b ⊢M with canon-base v b ⊢M
progress-id-base v b ⊢M | inj₁ (n , refl) = $ n , none , Drop$ b
progress-id-base v base-ℕ ⊢M | inj₂ (inj₁ refl) with ⊢M
progress-id-base v base-ℕ ⊢M | inj₂ (inj₁ refl) | ()
progress-id-base v base-𝔹 ⊢M | inj₂ (inj₁ refl) =
  `true , none , Drop-true
progress-id-base v base-ℕ ⊢M | inj₂ (inj₂ refl) with ⊢M
progress-id-base v base-ℕ ⊢M | inj₂ (inj₂ refl) | ()
progress-id-base v base-𝔹 ⊢M | inj₂ (inj₂ refl) =
  `false , none , Drop-false

------------------------------------------------------------------------
-- 4. Progress
------------------------------------------------------------------------

module Impl where

  -- An active `unseal` sees a value at a variable type.  `canon-var`
  -- exposes either CancelR's or IdPush's inner layer; the two `BoundaryWf`
  -- witnesses then feed the proved merged-reading theorem.
  progress-unseal : ∀ {Δ Δᵢ Δᶜ Θ Y M Bᵢ A}
    → Value M
    → BoundaryWf Δ Θ Δᵢ Δᶜ
    → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → Δᵢ ⊢ Bᵢ ≈ ` Y ⊣ Δᶜ
    → Δᶜ ∋ Y := A
    → Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
        (Δ ⊢ M ⟪ Θ , unseal Y ⟫ -→ M′ ∣ δ)
  progress-unseal {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} v mwΘ ⊢M sameᵢ d
    with sameTy-target-var⁻ {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
  progress-unseal v mwΘ ⊢M sameᵢ d | Z , refl , sameZ
    with canon-var v ⊢M
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl with ⊢M
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    with merged-reading mwΘ mw₁
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₁ with dX
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₁
    | α , R , nameX , repX , sameA with respell-ty keep₁ sameA
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₁ refl
    | env mw₁ ⊢W (conv-seal dX) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₁
    | α , R , nameX , repX , sameA | A′ , sameA′ =
    _ , _ , CancelR vW (bw-interior mwΘ) (bw-conversion mw₁)
                (α , R , nameX , repX , sameA)
                r⋉ (R , sameA′ , sameA) (bw-conversion mwΘ) d
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl with ⊢M
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl
    | env mw₁ ⊢W (conv-idv (α , nameX)) same₁ sameₑ₁ wE₁
    with merged-reading mwΘ mw₁
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl
    | env mw₁ ⊢W (conv-idv (α , nameX)) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₁ with keep₁ (_ , nameX)
  progress-unseal v mwΘ ⊢M sameᵢ d
    | Z , refl , sameZ | W , Θ₁ , X , vW , inj₂ refl
    | env mw₁ ⊢W (conv-idv (α , nameX)) same₁ sameₑ₁ wE₁
    | Δ⋉ᶜ , r⋉ , keep₁ | X′ , nameX′ =
    _ , _ , IdPush vW (bw-interior mwΘ) (bw-conversion mw₁) r⋉
               (` α , same-var nameX′ , same-var nameX)
               (bw-conversion mwΘ) d

  -- Once the interior is a value, conversion classification decides whether
  -- the whole boundary is a value or one of the four active redex shapes.
  progress-env : ∀ {Δ Δᵢ Δᶜ Θ c M Bᵢ Cᵢ Cₑ}
    → Value M
    → BoundaryWf Δ Θ Δᵢ Δᶜ
    → Δᵢ ∣ [] ⊢ M ⦂ Bᵢ
    → Δᶜ ⊢ c ∶ Cᵢ ⇝ Cₑ
    → Δᵢ ⊢ Bᵢ ≈ Cᵢ ⊣ Δᶜ
    → Value (M ⟪ Θ , c ⟫)
      ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ]
           (Δ ⊢ M ⟪ Θ , c ⟫ -→ M′ ∣ δ))
  progress-env v mwΘ ⊢M ⊢c sameᵢ with act-or-inert ⊢c
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₂ ic = inj₁ (V-⟪⟫ v ic)
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₁ (A-idb b)
    with conv-id-base-src b ⊢c
  progress-env {Δᵢ = Δᵢ} {Δᶜ = Δᶜ} v mwΘ ⊢M ⊢c sameᵢ
    | inj₁ (A-idb b) | refl =
    inj₂ (progress-id-base v b
      (⊢ty≡ (sameTy-base-src {Δ = Δᵢ} {Δ′ = Δᶜ} b sameᵢ) ⊢M))
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₁ A-unseal
    with conv-unseal-src ⊢c
  progress-env v mwΘ ⊢M ⊢c sameᵢ | inj₁ A-unseal | refl =
    inj₂ (progress-unseal v mwΘ ⊢M sameᵢ
             (unseal-target-is-rep ⊢c))

  -- A function-conversion wrapper carries its own BoundaryWf and the domain
  -- conversion typing needed by the core `peel-premises-env` theorem.
  progress-peel : ∀ {Δ W M Θ s t A B}
    → Value W
    → Value M
    → Δ ∣ [] ⊢ W ⟪ Θ , s ↦ t ⟫ ⦂ (A ⇒ B)
    → Σ[ N ∈ Term ] Σ[ δ ∈ Alloc ]
        (Δ ⊢ (W ⟪ Θ , s ↦ t ⟫) · M -→ N ∣ δ)
  progress-peel vW vM
    (env mwΘ ⊢W (conv-fun ⊢s ⊢t) sameᵢ sameₑ wE)
    with peel-premises-env mwΘ ⊢s
  progress-peel vW vM
    (env mwΘ ⊢W (conv-fun ⊢s ⊢t) sameᵢ sameₑ wE)
    | Δᵈ , s′ , rd , sc =
    _ , _ , Peel vW vM (bw-conversion mwΘ) (bw-interior mwΘ) rd sc

  -- The outer conversion's `_⊢_≈_⊣_` premise exposes the interior ∀
  -- body and
  -- is exactly TyPeelR-⟪⟫'s re-spelling premise.
  progress-·[]-∀conv : ∀ {Δ V Θ s B A C}
    → Value V
    → Δ ∣ [] ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] ⦂ C
    → Σ[ M ∈ Term ] Σ[ δ ∈ Alloc ]
        (Δ ⊢ (V ⟪ Θ , `∀ s ⟫) ·[ B , A ] -→ M ∣ δ)
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    with conv-all-inv ⊢c
  progress-·[]-∀conv v
    (⊢·[] (env {Δᵢ = Δᵢ} {Δᶜ = Δᶜ}
                mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s
    with sameTy-target-∀⁻ {Δ = Δᵢ} {Δ′ = Δᶜ} sameᵢ
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s | D , refl , sameD
    with canon-∀ v ⊢V | wf-same wA
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s | D , refl , sameD
    | inj₁ (N , vN , refl) | R , p =
    _ , _ , TyPeelR-Λ vN (bw-conversion mwΘ) ⊢s p
  progress-·[]-∀conv v
    (⊢·[] (env mwΘ ⊢V ⊢c sameᵢ sameₑ wE) wA)
    | A₀ , B₀ , refl , eqₑ , ⊢s | D , refl , sameD
    | inj₂ (W , Θ′ , s′ , vW , refl) | R , p =
    tyPeelR-⟪⟫ vW mwΘ ⊢V ⊢s sameD p
    where
    tyPeelR-⟪⟫ : ∀ {Δ Δᵢ Δᶜ W Θ′ s′ Θ s B A R Bᵢ Bᵢ′ Bₑ}
      → Value W
      → BoundaryWf Δ Θ Δᵢ Δᶜ
      → Δᵢ ∣ [] ⊢ W ⟪ Θ′ , `∀ s′ ⟫ ⦂ `∀ Bᵢ′
      → underΛ Δᶜ ⊢ s ∶ Bᵢ ⇝ Bₑ
      → underΛ Δᵢ ⊢ Bᵢ′ ≈ Bᵢ ⊣ underΛ Δᶜ
      → names Δ ⊢ A ~ R
      → Σ[ M ∈ Term ] Σ[ δ ∈ Alloc ]
          (Δ ⊢ ((W ⟪ Θ′ , `∀ s′ ⟫) ⟪ Θ , `∀ s ⟫) ·[ B , A ] -→ M ∣ δ)
    -- THE MOVED READING IS REPRESENTATION-SHIFTED FIRST, and only
    -- then respelled into the moved boundary's own context.  Doing the
    -- respell first — the 2026-09-20 dead end — leaves the reading in
    -- the unrenamed map.
    -- Commentary.md § proof/Progress.agda / §4
    tyPeelR-⟪⟫ {Θ′ = Θ′} vW mwΘ@(bw _ (interior _) _)
      (env {Δᶜ = Δ′ᶜ} mw′ ⊢W (conv-all ⊢s′) sameᵢ′ sameₑ′ wE′)
      ⊢s sameD p
      with addLock0-reading mwΘ mw′ p
    tyPeelR-⟪⟫ {Θ′ = Θ′} vW mwΘ@(bw _ (interior _) _)
      (env {Δᶜ = Δ′ᶜ} mw′ ⊢W (conv-all ⊢s′) sameᵢ′ sameₑ′ wE′)
      ⊢s sameD p
      | Δ″ᶜ , r″ , keep with readable ⊢s′
    tyPeelR-⟪⟫ {Θ′ = Θ′} vW mwΘ@(bw _ (interior _) _)
      (env {Δᶜ = Δ′ᶜ} mw′ ⊢W (conv-all ⊢s′) sameᵢ′ sameₑ′ wE′)
      ⊢s sameD p
      | Δ″ᶜ , r″ , keep | r , rd
      with sameᶜ-cast
             (names-underΛ-ren suc (names Δ′ᶜ))
             (sameᶜ-ren (extᵗ suc) rd)
    tyPeelR-⟪⟫ {Θ′ = Θ′} vW mwΘ@(bw _ (interior _) _)
      (env {Δᶜ = Δ′ᶜ} mw′ ⊢W (conv-all ⊢s′) sameᵢ′ sameₑ′ wE′)
      ⊢s sameD p
      | Δ″ᶜ , r″ , keep | r , rd | rdᴿ
      with respell (⊆ᵃ-underΛ keep) rdᴿ
    tyPeelR-⟪⟫ {Θ′ = Θ′} vW mwΘ@(bw _ (interior _) _)
      (env {Δᶜ = Δ′ᶜ} mw′ ⊢W (conv-all ⊢s′) sameᵢ′ sameₑ′ wE′)
      ⊢s sameD p
      | Δ″ᶜ , r″ , keep | r , rd | rdᴿ | s″ , rd″ =
      _ , _ , TyPeelR-⟪⟫ vW (bw-interior mwΘ) (bw-conversion mwΘ)
            (bw-conversion mw′) (inst-interior (bw-interior mwΘ))
            r″ (_ , rd″ , rdᴿ) ⊢s sameD p

  ----------------------------------------------------------------------
  -- 5. The induction
  ----------------------------------------------------------------------

  progress : ∀ {Δ M A} → Δ ∣ [] ⊢ M ⦂ A
    → Value M ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ] (Δ ⊢ M -→ M′ ∣ δ))
  progress (⊢` ())
  progress ⊢$ = inj₁ V-$
  progress ⊢true = inj₁ V-true
  progress ⊢false = inj₁ V-false
  progress (⊢ƛ _ _) = inj₁ V-ƛ
  -- the value restriction: `⊢Λ` hands us the body's value proof
  progress (⊢Λ vN ⊢N) = inj₁ (V-Λ vN)
  progress (⊢· ⊢L ⊢M) with progress ⊢L
  progress (⊢· ⊢L ⊢M) | inj₂ (L′ , δ , st) =
    inj₂ (L′ · ↑ᴹ[ δ ] _ , δ , ξ-·-l st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL with progress ⊢M
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₂ (M′ , δ , st) =
    inj₂ (↑ᴹ[ δ ] _ · M′ , δ , ξ-·-r vL st)
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM with canon-⇒ vL ⊢L
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM | inj₁ (N , refl) =
    inj₂ (_ , none , Beta vM)
  progress (⊢· ⊢L ⊢M) | inj₁ vL | inj₁ vM
    | inj₂ (W , Θ , s , t , vW , refl) =
    inj₂ (progress-peel vW vM ⊢L)
  progress (⊢·[] ⊢L wA) with progress ⊢L
  progress (⊢·[] ⊢L wA) | inj₂ (L′ , δ , st) =
    inj₂ (L′ ·[ _ , _ ] , δ , ξ-·[] st)
  progress (⊢·[] ⊢L wA) | inj₁ vL with canon-∀ vL ⊢L
  progress (⊢·[] ⊢L wA) | inj₁ vL | inj₁ (N , vN , refl)
    with wf-same wA
  progress (⊢·[] ⊢L wA) | inj₁ vL | inj₁ (N , vN , refl)
    | R , p = inj₂ (_ , _ , TyBeta vN p)
  progress (⊢·[] ⊢L wA) | inj₁ vL
    | inj₂ (W , Θ , s , vW , refl) =
    inj₂ (progress-·[]-∀conv vW (⊢·[] ⊢L wA))
  progress (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) with progress ⊢M
  progress (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₂ (M′ , δ , st) =
    inj₂ (M′ ⟪ ↑ᴮ[ δ ] _ , _ ⟫ , δ , ξ-⟪⟫ (bw-interior mwΘ) st)
  progress (env mwΘ ⊢M ⊢c sameᵢ sameₑ wE) | inj₁ vM =
    progress-env vM mwΘ ⊢M ⊢c sameᵢ
