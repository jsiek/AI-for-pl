module strong.proof.MoveScope where

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
-- three readings the contractum needs are theorems of `strong.CtxMorph`
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
--   §3  CANCELR — REFUTED, and why
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
  using (_≡_; refl; sym; cong; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.CtxMorph
open import strong.proof.Preserve
  using (CancelRCase; IdPushCase; same-shiftRVars; shiftRep-shiftBy;
         shiftRep-var; same-wf; wf-mono; tvMono-extendReps)

------------------------------------------------------------------------
-- §1  The small inversions
------------------------------------------------------------------------

-- Two ordinary spellings of ONE representation variable.  Both sides of a
-- `SameTy` between variables are `same-var`s, so the judgement is a pair
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

  innerᵢ : SameTy Δ₁ᵢ B₁ Δ⋉ᶜ (` X′)
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

  outerᵢ : SameTy Δᵣᵢ C Δᶜ A
  outerᵢ = shiftBy m Rc , pCᵣ , pA

------------------------------------------------------------------------
-- §3  CANCELR — REFUTED
------------------------------------------------------------------------

-- `CancelRCase` has NO proof: it is FALSE.  The rule's re-spelling
-- premise `SameTy Δ⋉ᶜ A′ Δᶜ A` reads the inner layer's identity type in
-- the OUTER conversion context, and so omits the `numBinds Θ₁` shift that
-- `env`'s `SameTyExt` demands of the inner layer.  `IdPush` escapes
-- because its minted `unseal X′` takes its type from a LOOKUP, which
-- shifts itself (`∋ʳ-push` above); `CancelR` mints `mkId A′`, whose type
-- is whatever the premise says it is.
--
-- The machine-checked counterexample — a well-typed redex, every premise
-- of the rule satisfied, an actual reduction step, and no typing
-- derivation for the contractum — is `notes/CancelRShiftWall.agda`:
--
--   cancelR-case-false : ¬ CancelRCase
--
-- A repair is a RULE change and therefore Jeremy's call; the shape the
-- other three crossings suggest is recorded in that module.  Until then
-- `CancelRCase` stays a parameter of `strong.proof.Preserve.Impl`, and
-- `strong.Preservation` keeps it in its `Stage1` interface.
