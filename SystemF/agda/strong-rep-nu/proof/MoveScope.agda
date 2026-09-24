module strong-rep-nu.proof.MoveScope where

-- File Charter:
--   * THE SCOPE MOVE — the ONE-LAYER contractum `CancelR` and `IdPush`
--     build, and the preservation cases they owe.  §1 the small
--     inversions both cases share; §2 IDPUSH, PROVED; §3 CANCELR,
--     PROVED on the rule repaired 2026-09-19.
--   * THE MOVE.  Both rules neutralise the OUTER conversion, so the
--     surviving boundary starts presenting Y's REPRESENTATION — which
--     inside Θ₂'s unbinds need not be nameable.  So the frames move too:
--     the merge `Θ₁ ++ Θ₂` presents it OUTSIDE Θ₂'s unbinds.
--   * The readings the contractum needs are theorems of
--     strong-rep-nu.Boundary §3a (`merged-interior`); the MERGED
--     frame's conversion context is not, so both rules carry it as a
--     premise.
-- Commentary: Commentary.md § proof/MoveScope.agda

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong-rep-nu.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-nu.Ctx
open import strong-rep-nu.proof.Ctx
open import strong-rep-nu.Conversion
open import strong-rep-nu.Terms
open import strong-rep-nu.Boundary
open import strong-rep-nu.proof.Preserve
  using (CancelRCase; IdPushCase; same-wf)

------------------------------------------------------------------------
-- §1  The small inversions
------------------------------------------------------------------------

-- Two ordinary spellings of ONE representation variable.  Both sides of a
-- `_⊢_≈_⊣_` between variables are `same-var`s, so the judgement is a pair
-- of lookups at a common representation variable.
sameTy-var : ∀ {η η′ : TyCtx} {X Y : ℕ}
  → ∃[ R ] ((η ⊢ ` X ~ R) × (η′ ⊢ ` Y ~ R))
  → ∃[ α ] ((η ∋ˡ X := α) × (η′ ∋ˡ Y := α))
sameTy-var (` α , same-var d , same-var d′) = α , d , d′

-- The same, when only the TARGET is known to be a variable.
sameTy-tgt-var : ∀ {η η′ : TyCtx} {A : Ty} {Y : ℕ}
  → ∃[ R ] ((η ⊢ A ~ R) × (η′ ⊢ ` Y ~ R))
  → ∃[ α ] ((η ⊢ A ~ ` α) × (η′ ∋ˡ Y := α))
sameTy-tgt-var (` α , p , same-var d) = α , p , d

-- A representation binding determines its payload.
bindR-inj : ∀ {R S : Ty} → bindR R ≡ bindR S → R ≡ S
bindR-inj refl = refl

-- … and a representation VARIABLE is determined by the type it reads as.
var-inj : ∀ {α β : ℕ} → _≡_ {A = Ty} (` α) (` β) → α ≡ β
var-inj refl = refl

------------------------------------------------------------------------
-- §2  IDPUSH
------------------------------------------------------------------------

-- The surviving boundary is the revealing one, so its exterior type
-- becomes the redex's own C, presented OUTSIDE Θ₂'s unbinds — at the plain
-- exterior Δ, so C is nameable there.  That retires the old wall: the
-- case needs no scoping invariant.
-- The four moves, one per premise of the `env`:
-- Commentary.md § proof/MoveScope.agda / §2
preserve-IdPush : IdPushCase
preserve-IdPush {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
                {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {X′ = X′}
                {Y = Y} {C = C}
                wfΔ v ri r₁ r⋉ sm
                (env {Δᶜ = Δᶜ} mw₂
                     (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-idv tvX)
                          sm₁ se₁ wB)
                     (conv-unseal {A = A} dY) sm₂ se₂ wE)
  with interior-functional (bw-interior mw₂) ri
preserve-IdPush {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
                {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {X′ = X′}
                {Y = Y} {C = C}
                wfΔ v ri r₁ r⋉ sm
                (env {Δᶜ = Δᶜ} mw₂
                     (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-idv tvX)
                          sm₁ se₁ wB)
                     (conv-unseal {A = A} dY) sm₂ se₂ wE)
  | refl
  with conversion-functional (bw-conversion mw₁) r₁
preserve-IdPush {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
                {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {X′ = X′}
                {Y = Y} {C = C}
                wfΔ v ri r₁ r⋉ sm
                (env {Δᶜ = Δᶜ} mw₂
                     (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-idv tvX)
                          sm₁ se₁ wB)
                     (conv-unseal {A = A} dY) sm₂ se₂ wE)
  | refl | refl =
  contractum
  where
  -- THE BINDER Y NAMES, and the exterior type it represents
  αY : ℕ
  αY = proj₁ (sameTy-tgt-var sm₂)

  Rc : Ty
  Rc = proj₁ se₂

  pC : names Δ ⊢ C ~ Rc
  pC = proj₁ (proj₂ se₂)

  pA : names Δᶜ ⊢ A ~ Rc
  pA = proj₂ (proj₂ se₂)

  -- Y's own representation payload IS that same type, read on the outer
  -- conversion context.
  dYrep : reps Δ ∋ʳ αY := bindR Rc
  dYrep =
    subst (λ Ξ → Ξ ∋ʳ αY := bindR Rc)
      (conversion-reps (bw-conversion mw₂))
      (subst (λ a → reps Δᶜ ∋ʳ a := bindR Rc)
        (∋ˡ-det (proj₁ (proj₂ (proj₂ dY)))
                (proj₂ (proj₂ (sameTy-tgt-var sm₂))))
        (subst (λ T → reps Δᶜ ∋ʳ proj₁ dY := bindR T)
          (same-rep-unique (proj₂ (proj₂ (proj₂ (proj₂ dY)))) pA)
          (proj₁ (proj₂ (proj₂ (proj₂ dY))))))

  -- X's representation IS Y's: `idpush-name` with no bind block to cross.
  αX : ℕ
  αX = proj₁ (sameTy-var sm)

  eqX : αX ≡ αY
  eqX =
    trans (sym (∋ˡ-det (proj₂ (proj₂ (sameTy-tgt-var se₁)))
                       (proj₂ (proj₂ (sameTy-var sm)))))
          (var-inj (same-rep-unique
                      (proj₁ (proj₂ (sameTy-tgt-var se₁)))
                      (proj₁ (proj₂ (sameTy-tgt-var sm₂)))))

  -- the re-spelled exterior type, and the conversion it lets us mint
  A″ : Ty
  A″ = proj₁ (respell-ty (conversion-live r⋉) pC)

  qA″ : names Δ⋉ᶜ ⊢ A″ ~ Rc
  qA″ = proj₂ (respell-ty (conversion-live r⋉) pC)

  dA″ : Δ⋉ᶜ ∋ X′ := A″
  dA″ =
    αX , Rc
    , proj₁ (proj₂ (sameTy-var sm))
    , subst (λ Ξ → Ξ ∋ʳ αX := bindR Rc)
        (sym (conversion-reps r⋉))
        (subst (λ a → reps Δ ∋ʳ a := bindR Rc) (sym eqX) dYrep)
    , qA″

  mw⋉ : BoundaryWf Δ (Θ₁ ++ Θ₂) Δ₁ᵢ Δ⋉ᶜ
  mw⋉ = bw wfΔ (merged-interior (bw-interior mw₂) (bw-interior mw₁)) r⋉

  sameᵢ : Δ₁ᵢ ⊢ B₁ ≈ ` X′ ⊣ Δ⋉ᶜ
  sameᵢ =
    ` αX
    , subst (λ a → names Δ₁ᵢ ⊢ B₁ ~ ` a)
            (∋ˡ-det (proj₂ (proj₂ (sameTy-tgt-var sm₁)))
                    (proj₂ (proj₂ (sameTy-var sm))))
            (proj₁ (proj₂ (sameTy-tgt-var sm₁)))
    , same-var (proj₁ (proj₂ (sameTy-var sm)))

  sameₑ : Δ ⊢ C ≈ A″ ⊣ Δ⋉ᶜ
  sameₑ = Rc , pC , qA″

  contractum : Δ ∣ [] ⊢ V ⟪ Θ₁ ++ Θ₂ , unseal X′ ⟫ ⦂ C
  contractum = env mw⋉ ⊢V (conv-unseal dA″) sameᵢ sameₑ wE

------------------------------------------------------------------------
-- §3  CANCELR — PROVED, on the repaired rule
------------------------------------------------------------------------

-- THE PROOF IS `preserve-IdPush`'s.  It diverges only in the
-- conversion: `mkId A′`'s source and target are the SAME type, so ONE
-- type must satisfy both premises of the `env`.
-- What the 2026-09-19 repair bought, and what the store shrank:
-- Commentary.md § proof/MoveScope.agda / §3
preserve-CancelR : CancelRCase
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm
                 (env {Δᶜ = Δᶜ} mw₂
                      (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                           sm₁ se₁ wB)
                      (conv-unseal {A = A} dY) sm₂ se₂ wE)
  with interior-functional (bw-interior mw₂) ri
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm
                 (env {Δᶜ = Δᶜ} mw₂
                      (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                           sm₁ se₁ wB)
                      (conv-unseal {A = A} dY) sm₂ se₂ wE)
  | refl
  with conversion-functional (bw-conversion mw₁) r₁
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm
                 (env {Δᶜ = Δᶜ} mw₂
                      (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                           sm₁ se₁ wB)
                      (conv-unseal {A = A} dY) sm₂ se₂ wE)
  | refl | refl
  with ∋:=-det (name-fn (bw-conversion-wf mw₁)) dX d₁
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm
                 (env {Δᶜ = Δᶜ} mw₂
                      (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                           sm₁ se₁ wB)
                      (conv-unseal {A = A} dY) sm₂ se₂ wE)
  | refl | refl | refl =
  contractum
  where
  -- THE BINDER Y NAMES, and the exterior type it represents
  αY : ℕ
  αY = proj₁ (sameTy-tgt-var sm₂)

  Rc : Ty
  Rc = proj₁ se₂

  pC : names Δ ⊢ C ~ Rc
  pC = proj₁ (proj₂ se₂)

  pA : names Δᶜ ⊢ A ~ Rc
  pA = proj₂ (proj₂ se₂)

  dYrep : reps Δ ∋ʳ αY := bindR Rc
  dYrep =
    subst (λ Ξ → Ξ ∋ʳ αY := bindR Rc)
      (conversion-reps (bw-conversion mw₂))
      (subst (λ a → reps Δᶜ ∋ʳ a := bindR Rc)
        (∋ˡ-det (proj₁ (proj₂ (proj₂ dY)))
                (proj₂ (proj₂ (sameTy-tgt-var sm₂))))
        (subst (λ T → reps Δᶜ ∋ʳ proj₁ dY := bindR T)
          (same-rep-unique (proj₂ (proj₂ (proj₂ (proj₂ dY)))) pA)
          (proj₁ (proj₂ (proj₂ (proj₂ dY))))))

  -- THE CANCELLED BINDER, read on Θ₁'s own conversion context.  Its
  -- representation variable is X's, its payload the type `Aᵢ` denotes.
  αX : ℕ
  αX = proj₁ dX

  RB : Ty
  RB = proj₁ (proj₂ dX)

  pAᵢ : names Δ₁ᶜ ⊢ Aᵢ ~ RB
  pAᵢ = proj₂ (proj₂ (proj₂ (proj₂ dX)))

  dXrep : reps Δ₁ᶜ ∋ʳ αX := bindR RB
  dXrep = proj₁ (proj₂ (proj₂ (proj₂ dX)))

  -- X's representation IS Y's: `cancel-name` with no bind block to cross.
  eqX : αX ≡ αY
  eqX =
    trans (sym (∋ˡ-det (proj₂ (proj₂ (sameTy-tgt-var se₁)))
                       (proj₁ (proj₂ (proj₂ dX)))))
          (var-inj (same-rep-unique
                      (proj₁ (proj₂ (sameTy-tgt-var se₁)))
                      (proj₁ (proj₂ (sameTy-tgt-var sm₂)))))

  -- so the cancelled seal's source denotes the outer binder's payload.
  dXrep′ : reps Δ₁ᶜ ∋ʳ αX := bindR Rc
  dXrep′ =
    subst (λ Ξ → Ξ ∋ʳ αX := bindR Rc)
      (sym (trans (conversion-reps r₁) (interior-reps ri)))
      (subst (λ a → reps Δ ∋ʳ a := bindR Rc) (sym eqX) dYrep)

  eqRB : RB ≡ Rc
  eqRB = bindR-inj (∋ʳ-det dXrep dXrep′)

  -- the rule-carried re-spelling, and the representation it transports
  RA′ : Ty
  RA′ = proj₁ sm

  qA′ : names Δ⋉ᶜ ⊢ A′ ~ RA′
  qA′ = proj₁ (proj₂ sm)

  eqA′ : RA′ ≡ RB
  eqA′ = same-rep-unique (proj₂ (proj₂ sm)) pAᵢ

  mw⋉ : BoundaryWf Δ (Θ₁ ++ Θ₂) Δ₁ᵢ Δ⋉ᶜ
  mw⋉ = bw wfΔ (merged-interior (bw-interior mw₂) (bw-interior mw₁)) r⋉

  sameᵢ : Δ₁ᵢ ⊢ B₁ ≈ A′ ⊣ Δ⋉ᶜ
  sameᵢ =
    RA′
    , subst (λ T → names Δ₁ᵢ ⊢ B₁ ~ T)
            (same-rep-unique (proj₂ (proj₂ sm₁)) (proj₂ (proj₂ sm)))
            (proj₁ (proj₂ sm₁))
    , qA′

  sameₑ : Δ ⊢ C ≈ A′ ⊣ Δ⋉ᶜ
  sameₑ =
    Rc , pC
    , subst (λ T → names Δ⋉ᶜ ⊢ A′ ~ T) (trans eqA′ eqRB) qA′

  contractum : Δ ∣ [] ⊢ V ⟪ Θ₁ ++ Θ₂ , mkId A′ ⟫ ⦂ C
  contractum = env mw⋉ ⊢V (mkId-⊢ (same-wf qA′)) sameᵢ sameₑ wE
