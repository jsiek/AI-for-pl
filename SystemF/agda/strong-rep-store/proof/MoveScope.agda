module strong-rep-store.proof.MoveScope where

-- THE SCOPE MOVE — the two-layer contractum `CancelR` and `IdPush` build,
-- and the preservation cases they owe.
--
-- THE MOVE.  Both rules SWAP the two conversions of a two-layer wrapper,
-- so the INNER boundary stops presenting the abstract name `` ` Y `` and
-- starts presenting Y's REP.  A rep is a type over the exterior; inside
-- Θ₂'s LOCKS it need not be nameable at all, and `env`'s last premise
-- would then fail.  So the frames move with the conversions:
--
--   (V ⟪ Θ₁ , c ⟫) ⟪ Θ₂ , unseal Y ⟫
--     -→ (V ⟪ Θ₁ ⋉ Θ₂ , c′ ⟫) ⟪ rewind Θ₂ , mkId A ⟫
--
-- In the two-universe design the frame algebra is RELATIONAL, and the
-- three readings the contractum needs are theorems of
-- `strong-rep-store.Boundary` §3a:
--
--   rewind-interior    the outer frame's interior IS the plain exterior;
--   rewind-conversion  the outer frame's conversion context IS Θ₂'s;
--   merged-interior    the merged frame's interior IS the inner frame's.
--
-- The merged frame's CONVERSION context is not a theorem of the readings
-- the redex carries — it is a rule premise, and both rules carry it.
--
--   §1  the small inversions the two cases share
--   §2  IDPUSH — PROVED
--   §3  CANCELR — PROVED, on the rule repaired 2026-09-19
--
-- WHAT THE STORE DELETED (2026-09-22).  Every `shiftBy`/`shiftRep`
-- occurrence, and with them `ext-lookup`, `same-shiftRVars`,
-- `shiftRep-shiftBy`, `tvMono-extendReps` and `wf-mono`.  A boundary
-- scope carries no bind block, so `rewind Θ₂`'s interior is Δ ITSELF
-- rather than `extendReps (binds Θ₂) Δ`; the cancelled binder's
-- representation variable IS the outer binder's, not `numBinds Θ₁ +` it;
-- and the two `env` comparisons are the SAME relation at the same depth.
-- Both cases lost about a third of their lines to that.
--
-- WHAT WAS DELETED EARLIER (2026-09-19).  Everything this module used to
-- hold about the retired masked-entry design: `applyUnlocks`/
-- `applyChanges` lookup transports (§1), the `shiftScope`/`rewind`/`_⋉_`
-- list algebra (§2), the `scope`/`interior` context identities (§3), the
-- frame lemmas as EQUALITIES and the lock-only refutation (§4, §4b), and
-- `_⊢ᵐ_` for the two new frames (§5).

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong-rep-store.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-store.Ctx
open import strong-rep-store.proof.Ctx
open import strong-rep-store.Conversion
open import strong-rep-store.Terms
open import strong-rep-store.Boundary
open import strong-rep-store.proof.Preserve
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

-- The swap makes the INNER boundary the revealing one, so its exterior
-- type becomes the redex's own exterior type C, presented OUTSIDE Θ₂'s
-- locks — `rewind Θ₂`'s interior is exactly the plain exterior, which is
-- where C is nameable.  That is what retires the old wall: the case needs
-- no scoping invariant.
--
-- FOUR MOVES, one per premise of the contractum's inner `env`:
--
--   FRAME       `Θ₁ ⋉ Θ₂`, whose interior is the inner frame's own
--               (`merged-interior`) and whose conversion context the rule
--               carries.
--   INTERIOR    `V`, retyped EXACTLY where it was.
--   CONVERSION  `unseal X′`.  Its rep IS the OUTER binder's — with the
--               store there is no bind block to shift it past, which is
--               the `idpush-name` equation of proof/IdLayer.agda in its
--               store form.  Its ordinary spelling is the rule-carried
--               `X′`.
--   EXTERIOR    C, re-spelled into the merged conversion context.  The
--               re-spelling exists because a conversion reading only ADDS
--               names (`conversion-live`), so every name of the merged
--               frame's OWN exterior survives into it.
preserve-IdPush : IdPushCase
preserve-IdPush {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {X′ = X′}
                {Y = Y} {A = A} {C = C}
                wfΔ v ri r₁ r⋉ sm r₂ d
                (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-idv tvX)
                              sm₁ se₁ wB)
                     (conv-unseal dY) sm₂ se₂ wE)
  with interior-functional (bw-interior mw₂) ri
     | conversion-functional (bw-conversion mw₂) r₂
preserve-IdPush {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {X′ = X′}
                {Y = Y} {A = A} {C = C}
                wfΔ v ri r₁ r⋉ sm r₂ d
                (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-idv tvX)
                              sm₁ se₁ wB)
                     (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl
  with conversion-functional (bw-conversion mw₁) r₁
     | ∋:=-det (name-fn (bw-conversion-wf mw₂)) dY d
preserve-IdPush {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {X′ = X′}
                {Y = Y} {A = A} {C = C}
                wfΔ v ri r₁ r⋉ sm r₂ d
                (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-idv tvX)
                              sm₁ se₁ wB)
                     (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl | refl | refl =
  env mwR inner (mkId-⊢ (same-wf pA)) outerᵢ se₂ wE
  where
  -- the outer frame: the plain exterior
  mwR : BoundaryWf Δ (rewind Θ₂) Δ Δᶜ
  mwR = bw wfΔ (rewind-interior ri) (rewind-conversion ri r₂)

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
      (conversion-reps r₂)
      (subst (λ a → reps Δᶜ ∋ʳ a := bindR Rc)
        (∋ˡ-det (proj₁ (proj₂ (proj₂ d)))
                (proj₂ (proj₂ (sameTy-tgt-var sm₂))))
        (subst (λ T → reps Δᶜ ∋ʳ proj₁ d := bindR T)
          (same-rep-unique (proj₂ (proj₂ (proj₂ (proj₂ d)))) pA)
          (proj₁ (proj₂ (proj₂ (proj₂ d))))))

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

  mw⋉ : BoundaryWf Δ (Θ₁ ⋉ Θ₂) Δ₁ᵢ Δ⋉ᶜ
  mw⋉ = bw wfΔ (merged-interior (bw-interior mw₂) (bw-interior mw₁)) r⋉

  innerᵢ : Δ₁ᵢ ⊢ B₁ ≈ ` X′ ⊣ Δ⋉ᶜ
  innerᵢ =
    ` αX
    , subst (λ a → names Δ₁ᵢ ⊢ B₁ ~ ` a)
            (∋ˡ-det (proj₂ (proj₂ (sameTy-tgt-var sm₁)))
                    (proj₂ (proj₂ (sameTy-var sm))))
            (proj₁ (proj₂ (sameTy-tgt-var sm₁)))
    , same-var (proj₁ (proj₂ (sameTy-var sm)))

  innerₑ : Δ ⊢ C ≈ A″ ⊣ Δ⋉ᶜ
  innerₑ = Rc , pC , qA″

  inner : Δ ∣ [] ⊢ V ⟪ Θ₁ ⋉ Θ₂ , unseal X′ ⟫ ⦂ C
  inner = env mw⋉ ⊢V (conv-unseal dA″) innerᵢ innerₑ wE

  outerᵢ : Δ ⊢ C ≈ A ⊣ Δᶜ
  outerᵢ = Rc , pC , pA

------------------------------------------------------------------------
-- §3  CANCELR — PROVED, on the repaired rule
------------------------------------------------------------------------

-- WHAT THE 2026-09-19 REPAIR BOUGHT.  The old rule re-spelled the inner
-- layer's identity type FROM the OUTER conversion context and so asserted
-- that `A′` denotes the SAME representation as `A`, where the inner
-- `env`'s `SameTyExt (numBinds Θ₁)` demanded `shiftBy (numBinds Θ₁)` of
-- it.  That was refuted at a reachable redex
-- (notes/CancelRShiftWall.agda, notes/CancelRReachabilityWitness.agda).
-- The repaired premise reads the cancelled `seal X`'s OWN source `Aᵢ` at
-- Θ₁'s conversion context `Δ₁ᶜ`.
--
-- WITH THE STORE the two readings that had to be reconciled are the same
-- reading: there is no bind block, so the shift the old proof had to
-- recover (`∋ʳ-push`, `eqRB`) is the identity, and the cancelled binder's
-- representation variable IS the outer binder's.  The premise is still
-- read at `Δ₁ᶜ` — a different NAME MAP, which is what `_⊢_≈_⊣_` is for —
-- so the rule is unchanged; only its proof shrinks.
--
-- THE PROOF IS `preserve-IdPush`'s, and the outer layer is LITERALLY it.
-- The inner layer diverges: `IdPush` mints `unseal X′`, whose SOURCE is a
-- variable and whose TARGET is a LOOKUP; `CancelR` mints `mkId A′`, whose
-- source and target are the SAME type, so ONE type must satisfy both
-- premises of the inner `env` — and the two meet because the rep the
-- seal's source names at `Δ₁ᶜ` is the outer binder's payload `Rc`.
preserve-CancelR : CancelRCase
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm r₂ d
                 (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                               sm₁ se₁ wB)
                      (conv-unseal dY) sm₂ se₂ wE)
  with interior-functional (bw-interior mw₂) ri
     | conversion-functional (bw-conversion mw₂) r₂
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm r₂ d
                 (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                               sm₁ se₁ wB)
                      (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl
  with conversion-functional (bw-conversion mw₁) r₁
     | ∋:=-det (name-fn (bw-conversion-wf mw₂)) dY d
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm r₂ d
                 (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                               sm₁ se₁ wB)
                      (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl | refl | refl
  with ∋:=-det (name-fn (bw-conversion-wf mw₁)) dX d₁
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm r₂ d
                 (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                               sm₁ se₁ wB)
                      (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl | refl | refl | refl =
  env mwR inner (mkId-⊢ (same-wf pA)) outerᵢ se₂ wE
  where
  -- the outer frame: the plain exterior
  mwR : BoundaryWf Δ (rewind Θ₂) Δ Δᶜ
  mwR = bw wfΔ (rewind-interior ri) (rewind-conversion ri r₂)

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
      (conversion-reps r₂)
      (subst (λ a → reps Δᶜ ∋ʳ a := bindR Rc)
        (∋ˡ-det (proj₁ (proj₂ (proj₂ d)))
                (proj₂ (proj₂ (sameTy-tgt-var sm₂))))
        (subst (λ T → reps Δᶜ ∋ʳ proj₁ d := bindR T)
          (same-rep-unique (proj₂ (proj₂ (proj₂ (proj₂ d)))) pA)
          (proj₁ (proj₂ (proj₂ (proj₂ d))))))

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

  mw⋉ : BoundaryWf Δ (Θ₁ ⋉ Θ₂) Δ₁ᵢ Δ⋉ᶜ
  mw⋉ = bw wfΔ (merged-interior (bw-interior mw₂) (bw-interior mw₁)) r⋉

  innerᵢ : Δ₁ᵢ ⊢ B₁ ≈ A′ ⊣ Δ⋉ᶜ
  innerᵢ =
    RA′
    , subst (λ T → names Δ₁ᵢ ⊢ B₁ ~ T)
            (same-rep-unique (proj₂ (proj₂ sm₁)) (proj₂ (proj₂ sm)))
            (proj₁ (proj₂ sm₁))
    , qA′

  innerₑ : Δ ⊢ C ≈ A′ ⊣ Δ⋉ᶜ
  innerₑ =
    Rc , pC
    , subst (λ T → names Δ⋉ᶜ ⊢ A′ ~ T) (trans eqA′ eqRB) qA′

  inner : Δ ∣ [] ⊢ V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫ ⦂ C
  inner = env mw⋉ ⊢V (mkId-⊢ (same-wf qA′)) innerᵢ innerₑ wE

  outerᵢ : Δ ⊢ C ≈ A ⊣ Δᶜ
  outerᵢ = Rc , pC , pA
