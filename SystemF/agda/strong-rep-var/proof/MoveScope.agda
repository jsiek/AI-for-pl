module strong-rep-var.proof.MoveScope where

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
-- `strong-rep-var.CtxMorph`
-- §3a:
--
--   rewind-interior    the outer frame's interior IS the plain exterior
--                      under Θ₂'s bind block;
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
-- WHAT WAS DELETED (2026-09-19).  Everything this module used to hold was
-- about the retired masked-entry design: `applyUnlocks`/`applyChanges`
-- lookup transports (§1), the `shiftScope`/`rewind`/`_⋉_` list algebra
-- (§2), the `scope`/`interior` context identities (§3), the frame lemmas
-- as EQUALITIES and the lock-only refutation (§4, §4b), and `_⊢ᵐ_` for
-- the two new frames (§5).  None of it has a two-universe counterpart:
-- there is no computed context to state an equality between, and the
-- relational readings above replace all of it.  The old §6 cases are
-- replaced by §2 and §3 here.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import strong-rep-var.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong-rep-var.Ctx
open import strong-rep-var.proof.Ctx
open import strong-rep-var.Conversion
open import strong-rep-var.Terms
open import strong-rep-var.CtxMorph
open import strong-rep-var.proof.Preserve
  using (CancelRCase; IdPushCase; same-shiftRVars; shiftRep-shiftBy;
         shiftRep-var; same-wf; wf-mono; tvMono-extendReps)

------------------------------------------------------------------------
-- §1  The small inversions
------------------------------------------------------------------------

-- Two ordinary spellings of ONE representation variable.  Both sides of a
-- `_⊢_≈_⊣_` between variables are `same-var`s, so the judgement is a
-- pair
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

-- A name that reads a representation variable ACROSS a bind block reads
-- it shifted, so the lookup lands at `k + α`.
ext-lookup : (k α : ℕ) {η : TyCtx} {X : ℕ}
  → η ⊢ ` X ~ shiftRep k (` α) → η ∋ˡ X := k + α
ext-lookup k α {η = η} {X = X} q
  with subst (λ T → η ⊢ ` X ~ T) (shiftRep-var k α) q
ext-lookup k α {η = η} {X = X} q | same-var d = d

------------------------------------------------------------------------
-- §2  IDPUSH
------------------------------------------------------------------------

-- The swap makes the INNER boundary the revealing one, so its exterior
-- type becomes the redex's own exterior type C, presented OUTSIDE Θ₂'s
-- locks — `rewind Θ₂`'s interior is exactly the plain exterior under the
-- bind block, which is where C is nameable.  That is what retires the old
-- wall: the case needs no scoping invariant.
--
-- FOUR MOVES, one per premise of the contractum's inner `env`:
--
--   FRAME       `Θ₁ ⋉ Θ₂`, whose interior is the inner frame's own
--               (`merged-interior`) and whose conversion context the rule
--               carries.
--   INTERIOR    `V`, retyped EXACTLY where it was.
--   CONVERSION  `unseal X′`.  Its rep is the OUTER binder's, shifted past
--               Θ₁'s bind block — which is what `∋ʳ-push` says and what
--               makes the minted conversion self-shifting.  Its ordinary
--               spelling is the rule-carried `X′`, and typing forces
--               X′'s rep to be `numBinds Θ₁ + αY`, the old
--               `idpush-name` equation one universe up.
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
  with interior-functional (mw-interior mw₂) ri
     | conversion-functional (mw-conversion mw₂) r₂
preserve-IdPush {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {X′ = X′}
                {Y = Y} {A = A} {C = C}
                wfΔ v ri r₁ r⋉ sm r₂ d
                (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-idv tvX)
                              sm₁ se₁ wB)
                     (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl
  with conversion-functional (mw-conversion mw₁) r₁
     | ∋:=-det (name-fn (mw-conversion-wf mw₂)) dY d
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
  n : ℕ
  n = numBinds Θ₁

  m : ℕ
  m = numBinds Θ₂

  -- the outer frame: the plain exterior under Θ₂'s bind block
  Δᵣᵢ : Ctxᵗ
  Δᵣᵢ = extendReps (binds Θ₂) Δ

  mwR : MorphWf Δ (rewind Θ₂) Δᵣᵢ Δᶜ
  mwR = mw wfΔ (mw-binds mw₂)
           (rewind-interior ri) (rewind-conversion ri r₂)

  -- THE BINDER Y NAMES, and the exterior type it represents
  αY : ℕ
  αY = proj₁ (sameTy-tgt-var sm₂)

  Rc : Ty
  Rc = proj₁ se₂

  pA : names Δᶜ ⊢ A ~ shiftBy m Rc
  pA = subst (λ T → names Δᶜ ⊢ A ~ T)
             (shiftRep-shiftBy m Rc) (proj₂ (proj₂ se₂))

  pCᵣ : names Δᵣᵢ ⊢ C ~ shiftBy m Rc
  pCᵣ = same-shiftRVars m (proj₁ (proj₂ se₂))

  -- Y's own representation payload IS that same type, read on the outer
  -- conversion context.
  dYrep : pushRepBinds (binds Θ₂) (reps Δ)
            ∋ʳ αY := bindR (shiftBy m Rc)
  dYrep =
    subst (λ Ξ → Ξ ∋ʳ αY := bindR (shiftBy m Rc))
      (conversion-reps r₂)
      (subst (λ a → reps Δᶜ ∋ʳ a := bindR (shiftBy m Rc))
        (∋ˡ-det (proj₁ (proj₂ (proj₂ d)))
                (proj₂ (proj₂ (sameTy-tgt-var sm₂))))
        (subst (λ T → reps Δᶜ ∋ʳ proj₁ d := bindR T)
          (same-rep-unique (proj₂ (proj₂ (proj₂ (proj₂ d)))) pA)
          (proj₁ (proj₂ (proj₂ (proj₂ d))))))

  -- X's representation is Y's, one bind block in: `idpush-name`.
  αX : ℕ
  αX = proj₁ (sameTy-var sm)

  eqX : αX ≡ n + αY
  eqX =
    ∋ˡ-det (proj₂ (proj₂ (sameTy-var sm)))
      (ext-lookup n αY
        (subst (λ T → names Δ₁ᶜ ⊢ ` X ~ shiftRep n T)
               (sym (same-rep-unique (proj₁ (proj₂ (sameTy-tgt-var sm₂)))
                                     (proj₁ (proj₂ se₁))))
               (proj₂ (proj₂ se₁))))

  -- the re-spelled exterior type, and the conversion it lets us mint
  A″ : Ty
  A″ = proj₁ (respell-ty (conversion-live r⋉) (same-shiftRVars n pCᵣ))

  qA″ : names Δ⋉ᶜ ⊢ A″ ~ shiftBy n (shiftBy m Rc)
  qA″ = proj₂ (respell-ty (conversion-live r⋉) (same-shiftRVars n pCᵣ))

  dA″ : Δ⋉ᶜ ∋ X′ := A″
  dA″ =
    αX , shiftBy n (shiftBy m Rc)
    , proj₁ (proj₂ (sameTy-var sm))
    , subst (λ Ξ → Ξ ∋ʳ αX := bindR (shiftBy n (shiftBy m Rc)))
        (sym (conversion-reps r⋉))
        (subst (λ a → pushRepBinds (binds Θ₁)
                        (pushRepBinds (binds Θ₂) (reps Δ))
                        ∋ʳ a := bindR (shiftBy n (shiftBy m Rc)))
               (sym eqX) (∋ʳ-push (binds Θ₁) dYrep))
    , qA″

  mw⋉ : MorphWf Δᵣᵢ (Θ₁ ⋉ Θ₂) Δ₁ᵢ Δ⋉ᶜ
  mw⋉ = mw (mw-interior-wf mwR)
           (subst (λ Ξ → Ξ ⊢ᴮ binds Θ₁) (interior-reps ri) (mw-binds mw₁))
           (merged-interior (mw-interior mw₂) (mw-interior mw₁))
           r⋉

  innerᵢ : Δ₁ᵢ ⊢ B₁ ≈ ` X′ ⊣ Δ⋉ᶜ
  innerᵢ =
    ` αX
    , subst (λ a → names Δ₁ᵢ ⊢ B₁ ~ ` a)
            (∋ˡ-det (proj₂ (proj₂ (sameTy-tgt-var sm₁)))
                    (proj₂ (proj₂ (sameTy-var sm))))
            (proj₁ (proj₂ (sameTy-tgt-var sm₁)))
    , same-var (proj₁ (proj₂ (sameTy-var sm)))

  innerₑ : SameTyExt (numBinds (Θ₁ ⋉ Θ₂)) Δᵣᵢ C Δ⋉ᶜ A″
  innerₑ =
    shiftBy m Rc , pCᵣ
    , subst (λ T → names Δ⋉ᶜ ⊢ A″ ~ T)
            (sym (shiftRep-shiftBy n (shiftBy m Rc))) qA″

  inner : Δᵣᵢ ∣ [] ⊢ V ⟪ Θ₁ ⋉ Θ₂ , unseal X′ ⟫ ⦂ C
  inner = env mw⋉ ⊢V (conv-unseal dA″) innerᵢ innerₑ
              (wf-mono Δ Δᵣᵢ (tvMono-extendReps (binds Θ₂) Δ) wE)

  outerᵢ : Δᵣᵢ ⊢ C ≈ A ⊣ Δᶜ
  outerᵢ = shiftBy m Rc , pCᵣ , pA

------------------------------------------------------------------------
-- §3  CANCELR — PROVED, on the repaired rule
------------------------------------------------------------------------

-- WHAT THE REPAIR BOUGHT (2026-09-19).  The old rule re-spelled the inner
-- layer's identity type FROM the OUTER conversion context —
-- `SameTy Δ⋉ᶜ A′ Δᶜ A` — and so asserted that `A′` denotes the SAME
-- representation as `A`, where the inner `env`'s `SameTyExt (numBinds Θ₁)`
-- demands `shiftBy (numBinds Θ₁)` of it.  That was refuted, at a redex
-- reachable from a closed plain source program
-- (notes/CancelRShiftWall.agda, notes/CancelRReachabilityWitness.agda).
-- The repaired premise reads the cancelled `seal X`'s OWN source `Aᵢ` at
-- Θ₁'s conversion context `Δ₁ᶜ`, which is where the shifted reading
-- already lives.
--
-- THE PROOF IS `preserve-IdPush`'s, and the outer layer is LITERALLY it:
-- the same `rewind Θ₂` frame from `rewind-interior`/`rewind-conversion`,
-- the same `mkId A` minted at the outer binder's own payload, the same
-- `outerᵢ`, and the redex's own `se₂`/`wE` reused unchanged.
--
-- THE INNER LAYER IS WHERE THE TWO CASES DIVERGE.  `IdPush` mints
-- `unseal X′`, whose SOURCE is a variable and whose TARGET is a LOOKUP —
-- and a lookup shifts itself past Θ₁'s bind block (`∋ʳ-push`).  `CancelR`
-- mints `mkId A′`, whose source and target are the SAME type, so ONE type
-- must satisfy both premises of the inner `env`:
--
--   innerᵢ  `A′` denotes what `V`'s type `B₁` denotes — which is what the
--           rule's re-spelling premise says, since `sm₁` reads `B₁`
--           against the cancelled seal's source `Aᵢ` at `Δ₁ᶜ`;
--   innerₑ  `A′` denotes `shiftBy (numBinds Θ₁)` of what the redex's
--           exterior type `C` denotes.
--
-- The two meet because the LOOKUP still shifts itself, one level up: the
-- cancelled binder's representation variable is `numBinds Θ₁ + αY` (`eqX`,
-- the old `cancel-name` equation one universe up), and `∋ʳ-push` reads Y's
-- payload through Θ₁'s bind block as `shiftBy (numBinds Θ₁)` of it
-- (`eqRB`).  So the rep the seal's source names at `Δ₁ᶜ` IS the shifted
-- one, and the repaired premise transports exactly that to `Δ⋉ᶜ`.  Read
-- against `Δᶜ` it was the UNshifted one, and nothing could have fixed it.
preserve-CancelR : CancelRCase
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm r₂ d
                 (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                               sm₁ se₁ wB)
                      (conv-unseal dY) sm₂ se₂ wE)
  with interior-functional (mw-interior mw₂) ri
     | conversion-functional (mw-conversion mw₂) r₂
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm r₂ d
                 (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                               sm₁ se₁ wB)
                      (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl
  with conversion-functional (mw-conversion mw₁) r₁
     | ∋:=-det (name-fn (mw-conversion-wf mw₂)) dY d
preserve-CancelR {Δ = Δ} {Δᵢ = Δᵢ} {Δ₁ᶜ = Δ₁ᶜ} {Δ⋉ᶜ = Δ⋉ᶜ} {Δᶜ = Δᶜ}
                 {V = V} {Θ₁ = Θ₁} {Θ₂ = Θ₂} {X = X} {Y = Y}
                 {A = A} {A′ = A′} {Aᵢ = Aᵢ} {C = C}
                 wfΔ v ri r₁ d₁ r⋉ sm r₂ d
                 (env mw₂ (env {Δᵢ = Δ₁ᵢ} {Bᵢ = B₁} mw₁ ⊢V (conv-seal dX)
                               sm₁ se₁ wB)
                      (conv-unseal dY) sm₂ se₂ wE)
  | refl | refl | refl | refl
  with ∋:=-det (name-fn (mw-conversion-wf mw₁)) dX d₁
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
  n : ℕ
  n = numBinds Θ₁

  m : ℕ
  m = numBinds Θ₂

  -- the outer frame: the plain exterior under Θ₂'s bind block
  Δᵣᵢ : Ctxᵗ
  Δᵣᵢ = extendReps (binds Θ₂) Δ

  mwR : MorphWf Δ (rewind Θ₂) Δᵣᵢ Δᶜ
  mwR = mw wfΔ (mw-binds mw₂)
           (rewind-interior ri) (rewind-conversion ri r₂)

  -- THE BINDER Y NAMES, and the exterior type it represents
  αY : ℕ
  αY = proj₁ (sameTy-tgt-var sm₂)

  Rc : Ty
  Rc = proj₁ se₂

  pA : names Δᶜ ⊢ A ~ shiftBy m Rc
  pA = subst (λ T → names Δᶜ ⊢ A ~ T)
             (shiftRep-shiftBy m Rc) (proj₂ (proj₂ se₂))

  pCᵣ : names Δᵣᵢ ⊢ C ~ shiftBy m Rc
  pCᵣ = same-shiftRVars m (proj₁ (proj₂ se₂))

  dYrep : pushRepBinds (binds Θ₂) (reps Δ)
            ∋ʳ αY := bindR (shiftBy m Rc)
  dYrep =
    subst (λ Ξ → Ξ ∋ʳ αY := bindR (shiftBy m Rc))
      (conversion-reps r₂)
      (subst (λ a → reps Δᶜ ∋ʳ a := bindR (shiftBy m Rc))
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

  -- X's representation is Y's, one bind block in: `cancel-name`.
  eqX : αX ≡ n + αY
  eqX =
    ∋ˡ-det (proj₁ (proj₂ (proj₂ dX)))
      (ext-lookup n αY
        (subst (λ T → names Δ₁ᶜ ⊢ ` X ~ shiftRep n T)
               (sym (same-rep-unique (proj₁ (proj₂ (sameTy-tgt-var sm₂)))
                                     (proj₁ (proj₂ se₁))))
               (proj₂ (proj₂ se₁))))

  -- THE SHIFT, RECOVERED.  Reading Y's payload through Θ₁'s bind block
  -- shifts it, so the cancelled seal's source denotes exactly the
  -- representation the inner `env`'s `SameTyExt n` asks for.
  dXrep′ : reps Δ₁ᶜ ∋ʳ αX := bindR (shiftBy n (shiftBy m Rc))
  dXrep′ =
    subst (λ Ξ → Ξ ∋ʳ αX := bindR (shiftBy n (shiftBy m Rc)))
      (sym (trans (conversion-reps r₁)
                  (cong (pushRepBinds (binds Θ₁)) (interior-reps ri))))
      (subst (λ a → pushRepBinds (binds Θ₁)
                      (pushRepBinds (binds Θ₂) (reps Δ))
                      ∋ʳ a := bindR (shiftBy n (shiftBy m Rc)))
             (sym eqX) (∋ʳ-push (binds Θ₁) dYrep))

  eqRB : RB ≡ shiftBy n (shiftBy m Rc)
  eqRB = bindR-inj (∋ʳ-det dXrep dXrep′)

  -- the rule-carried re-spelling, and the representation it transports
  RA′ : Ty
  RA′ = proj₁ sm

  qA′ : names Δ⋉ᶜ ⊢ A′ ~ RA′
  qA′ = proj₁ (proj₂ sm)

  eqA′ : RA′ ≡ RB
  eqA′ = same-rep-unique (proj₂ (proj₂ sm)) pAᵢ

  mw⋉ : MorphWf Δᵣᵢ (Θ₁ ⋉ Θ₂) Δ₁ᵢ Δ⋉ᶜ
  mw⋉ = mw (mw-interior-wf mwR)
           (subst (λ Ξ → Ξ ⊢ᴮ binds Θ₁) (interior-reps ri) (mw-binds mw₁))
           (merged-interior (mw-interior mw₂) (mw-interior mw₁))
           r⋉

  innerᵢ : Δ₁ᵢ ⊢ B₁ ≈ A′ ⊣ Δ⋉ᶜ
  innerᵢ =
    RA′
    , subst (λ T → names Δ₁ᵢ ⊢ B₁ ~ T)
            (same-rep-unique (proj₂ (proj₂ sm₁)) (proj₂ (proj₂ sm)))
            (proj₁ (proj₂ sm₁))
    , qA′

  innerₑ : SameTyExt (numBinds (Θ₁ ⋉ Θ₂)) Δᵣᵢ C Δ⋉ᶜ A′
  innerₑ =
    shiftBy m Rc , pCᵣ
    , subst (λ T → names Δ⋉ᶜ ⊢ A′ ~ T)
            (sym (shiftRep-shiftBy n (shiftBy m Rc)))
            (subst (λ T → names Δ⋉ᶜ ⊢ A′ ~ T) (trans eqA′ eqRB) qA′)

  inner : Δᵣᵢ ∣ [] ⊢ V ⟪ Θ₁ ⋉ Θ₂ , mkId A′ ⟫ ⦂ C
  inner = env mw⋉ ⊢V (mkId-⊢ (same-wf qA′)) innerᵢ innerₑ
              (wf-mono Δ Δᵣᵢ (tvMono-extendReps (binds Θ₂) Δ) wE)

  outerᵢ : Δᵣᵢ ⊢ C ≈ A ⊣ Δᶜ
  outerᵢ = shiftBy m Rc , pCᵣ , pA
