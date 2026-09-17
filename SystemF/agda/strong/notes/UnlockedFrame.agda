module strong.notes.UnlockedFrame where

-- PROTOTYPE of the v8 analogue of main's boundary rule (Jeremy,
-- 2026-09-17).  Main types the conversion on `convCtx` and checks the
-- MORPHISM'S REPRESENTATIONS on `unlockedScope Θ Δ` — the exterior with
-- the reveals added and the CONCEALS SKIPPED:
--
--   mw-reps : unlockedScope Θ Δ ⊢ʳ binds Θ
--
-- v8's analogue of `binds Θ` is the `⇓` premise of `conv-seal` and
-- `conv-unseal`, so those two move to an UNLOCKED FRAME `Ξ`, computed
-- once per boundary and threaded UNCHANGED into `↦` and `∀`
-- components.  Everything else stays: the `∋r` lookup, the `▷` pop and
-- `NotAssigned` are main's `mw-changes`, judged over the real contexts,
-- so THE TERM'S CONTEXT STILL POPS.
--
-- Main's premise (3) is `convCtx Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ`
-- — the source type is LITERALLY the interior type and the target is
-- shifted only past the BINDS.  So a lock does not re-spell a type, and
-- `hide`/`show` lose their `renameᵗ (shiftAtᵗ X)`: the conversion's
-- types all live in `Ξ`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion using
  (Conv; id; _∷ᶜ_; ConvElt; seal; unseal; hide; show; _↦_; all; _⧺_)

------------------------------------------------------------------------
-- The proposed conversion typing
------------------------------------------------------------------------

infix 4 _∣_∣_⊢̂′_∶_⇝_⊣_
infix 4 _∣_∣_⊢′_∶_⇝_⊣_

data _∣_∣_⊢̂′_∶_⇝_⊣_ (Σ : Store) (Ξ : Ctxᵗ)
     : Ctxᵗ → ConvElt → Ty → Ty → Ctxᵗ → Set
data _∣_∣_⊢′_∶_⇝_⊣_ (Σ : Store) (Ξ : Ctxᵗ)
     : Ctxᵗ → Conv → Ty → Ty → Ctxᵗ → Set

data _∣_∣_⊢̂′_∶_⇝_⊣_ Σ Ξ where
  -- THE ONE CHANGE: the read-back is at `Ξ`, not at the element's own
  -- interior.  The lookup and the pop are unmoved.
  seal′ : ∀ {Γᵢ Γₑ X α R A}
    → Σ ∣ Γₑ ∋r α := R → Σ ∣ Ξ ⊢ R ⇓ A → Γₑ ▷ X := α ⇒ Γᵢ
    → Σ ∣ Ξ ∣ Γᵢ ⊢̂′ seal X α ∶ A ⇝ ` X ⊣ Γₑ
  unseal′ : ∀ {Γᵢ Γₑ X α R A}
    → Σ ∣ Γᵢ ∋r α := R → Σ ∣ Ξ ⊢ R ⇓ A → Γᵢ ▷ X := α ⇒ Γₑ
    → NotAssigned Γₑ α
    → Σ ∣ Ξ ∣ Γᵢ ⊢̂′ unseal X α ∶ ` X ⇝ A ⊣ Γₑ
  -- NO RE-SPELLING: `A ⇝ A`, and well-formedness is at `Ξ`.
  hide′ : ∀ {Γᵢ Γₑ X α A}
    → Σ ∣ Γᵢ ∋a α → Ξ ⊢ᵗ A → Γₑ ▷ X := α ⇒ Γᵢ → NotAssigned Γᵢ α
    → Σ ∣ Ξ ∣ Γᵢ ⊢̂′ hide X α ∶ A ⇝ A ⊣ Γₑ
  show′ : ∀ {Γᵢ Γₑ X α A}
    → Σ ∣ Γₑ ∋a α → Ξ ⊢ᵗ A → Γᵢ ▷ X := α ⇒ Γₑ → NotAssigned Γₑ α
    → Σ ∣ Ξ ∣ Γᵢ ⊢̂′ show X α ∶ A ⇝ A ⊣ Γₑ
  fun′ : ∀ {Γᵢ Γₑ s t A B C D}
    → Σ ∣ Ξ ∣ Γₑ ⊢′ s ∶ C ⇝ A ⊣ Γᵢ → Σ ∣ Ξ ∣ Γᵢ ⊢′ t ∶ B ⇝ D ⊣ Γₑ
    → Σ ∣ Ξ ∣ Γᵢ ⊢̂′ (s ↦ t) ∶ A ⇒ B ⇝ C ⇒ D ⊣ Γₑ
  -- a BIND shifts — main's `shiftBy (numBinds Θ)` — so `Ξ` grows too
  all′ : ∀ {Ssᵢ Bsᵢ Ssₑ Bsₑ s A B}
    → Σ ∣ (bind ∷ stk Ξ ∥ bas Ξ) ∣ (bind ∷ Ssᵢ ∥ Bsᵢ) ⊢′ s ∶ A ⇝ B
        ⊣ (bind ∷ Ssₑ ∥ Bsₑ)
    → Σ ∣ Ξ ∣ (Ssᵢ ∥ Bsᵢ) ⊢̂′ all s ∶ `∀ A ⇝ `∀ B ⊣ (Ssₑ ∥ Bsₑ)

data _∣_∣_⊢′_∶_⇝_⊣_ Σ Ξ where
  id′   : ∀ {Γ A} → Ξ ⊢ᵗ A → Σ ∣ Ξ ∣ Γ ⊢′ id A ∶ A ⇝ A ⊣ Γ
  cons′ : ∀ {Γ₁ Γ₂ Γ₃ ĉ c A B C}
    → Σ ∣ Ξ ∣ Γ₁ ⊢̂′ ĉ ∶ A ⇝ B ⊣ Γ₂ → Σ ∣ Ξ ∣ Γ₂ ⊢′ c ∶ B ⇝ C ⊣ Γ₃
    → Σ ∣ Ξ ∣ Γ₁ ⊢′ (ĉ ∷ᶜ c) ∶ A ⇝ C ⊣ Γ₃

------------------------------------------------------------------------
-- M₅'s inner conversion, under the proposed rules
------------------------------------------------------------------------
-- The one that has NO derivation today (`notes/SourceToTyWrapGap.M₅-⊥`,
-- `proof.PreserveTyWrap` §8.1b): the `seal`'s read-back lands at a
-- context with an empty stack and no name for `α`.

Sg : Store
Sg = `𝔹ᴿ ∷ []

R : RepTy
R = `ᵃ (lvl zero)

-- the real contexts — UNCHANGED, still popping
Γ₃ Γ₂ Γ₁ : Ctxᵗ
Γ₃ = asgn (lvl zero) ∷ [] ∥ nuBind R ∷ []      -- the ν's body: X:=α
Γ₂ = [] ∥ nuBind R ∷ []                        -- after the hide: EMPTY stack
Γ₁ = asgn (bse zero) ∷ [] ∥ nuBind R ∷ []      -- after the seal: Y:=β

-- THE UNLOCKED FRAME: the exterior Γ₃ with the spine's reveal added and
-- its conceal skipped.  Y at 0, X at 1 — both nameable, and distinct.
Ξ : Ctxᵗ
Ξ = asgn (bse zero) ∷ asgn (lvl zero) ∷ [] ∥ nuBind R ∷ []

W′ : Conv
W′ = ((seal zero (bse zero) ∷ᶜ id (` zero))
       ↦ (show zero (bse zero) ∷ᶜ id `𝔹))
     ∷ᶜ hide zero (lvl zero) ∷ᶜ id (` suc zero ⇒ `𝔹)

wfΞ : Ξ ⊢ᵗ (` suc zero ⇒ `𝔹)
wfΞ = wf-⇒ (wf-var (t-there t-here)) wf-𝔹

-- the read-back that FAILS today, at `Ξ`: it lands on X, at index 1
readΞ : Sg ∣ Ξ ⊢ R ⇓ ` suc zero
readΞ = read-var (n-skip-asgn n-here-asgn)

⊢W′ : Sg ∣ Ξ ∣ Γ₁ ⊢′ W′ ∶ (` zero ⇒ `𝔹) ⇝ (` suc zero ⇒ `𝔹) ⊣ Γ₃
⊢W′ =
  cons′
    (fun′ (cons′ (seal′ r-here readΞ pop-here) (id′ (wf-var t-here)))
          (cons′ (show′ a-here-nu wf-𝔹 pop-here (λ ())) (id′ wf-𝔹)))
    (cons′ (hide′ (a-lvl l-here) wfΞ pop-here (λ ())) (id′ wfΞ))

-- The body `λx:Y. true` is typed at Γ₁ with `` ` 0 ⇒ `𝔹 ``, and `` ` 0 ``
-- is Y at Γ₁ AND at Ξ — the two frames agree on it, so the boundary's
-- interior endpoint needs no transport.
bodyTy : (` zero ⇒ `𝔹) ≡ (` zero ⇒ `𝔹)
bodyTy = refl

------------------------------------------------------------------------
-- What this costs
------------------------------------------------------------------------
-- (1) MORE THAN THE TWO READ-BACKS MOVED.  `hide′`/`show′`'s `⊢ᵗ`
--     premise and `id′`'s are at `Ξ` too — forced, since the types now
--     live there: at `Γ₂` the stack is empty and `` ` 1 `` is not well
--     formed.  This is faithful to main, whose premise (3) types the
--     WHOLE conversion at `convCtx`, but it is more than "only the `⇓`
--     premises".
--
-- (2) THE ANNOTATIONS CHANGE.  `W′`'s terminator is `id (` 1 ⇒ `𝔹)`
--     where the real `W` has `id (` 0 ⇒ `𝔹)`: the exterior type spelled
--     in `Ξ`'s frame rather than the exterior's.  So `revTy`/`concTy`
--     and `instReveal` must build annotations in `Ξ`, and `substAnn`'s
--     slot/type threading is against `Ξ` rather than the spine.
--
-- (3) `Ξ` MUST BE COMPUTED FROM THE WHOLE SPINE, reveals included —
--     not just the boundary's exterior.  With `Ξ = Γ₃` alone, `X` and
--     `Y` would both be `` ` 0 `` and the seal's source would collide
--     with its target.  `Ξ`'s two assignments are what keeps them apart,
--     exactly as main's `unlockedScope` applies the unlocks.
--
-- NOT YET CHECKED: composition (`⨟`/`fuse` must preserve `Ξ`), `arr`'s
-- dualization, and whether the boundary's EXTERIOR endpoint needs a
-- transport from `Ξ` back to `Δ` (the interior endpoint did not — see
-- `bodyTy`).

------------------------------------------------------------------------
-- Composition, at a SHARED frame
------------------------------------------------------------------------
-- `Ξ` is just along for the ride: the append is the same induction it
-- is today.

⧺′ : ∀ {Ξ Γ₁ Γ₂ Γ₃ c d A B C}
  → Sg ∣ Ξ ∣ Γ₁ ⊢′ c ∶ A ⇝ B ⊣ Γ₂ → Sg ∣ Ξ ∣ Γ₂ ⊢′ d ∶ B ⇝ C ⊣ Γ₃
  → Sg ∣ Ξ ∣ Γ₁ ⊢′ (c ⧺ d) ∶ A ⇝ C ⊣ Γ₃
⧺′ (id′ wf) ⊢d = ⊢d
⧺′ (cons′ hd tl) ⊢d = cons′ hd (⧺′ tl ⊢d)

------------------------------------------------------------------------
-- `arr`'s dualization is now EXACT
------------------------------------------------------------------------
-- `arr⁻ (hide X α) = just (show X α ∷ [])`.  Today the two elements
-- carry opposite `shiftAtᵗ`s and `proof.ArrTyping` has to flip them;
-- under the proposal both are `A ⇝ A`, so the dual is the SAME PREMISES
-- with the constructor swapped — the contexts even land in place,
-- because `hide` and `show` share the pop judgment `Γₑ ▷ X := α ⇒ Γᵢ`.

dual-hide : ∀ {Ξ Γᵢ Γₑ X α A}
  → Sg ∣ Ξ ∣ Γᵢ ⊢̂′ hide X α ∶ A ⇝ A ⊣ Γₑ
  → Sg ∣ Ξ ∣ Γₑ ⊢̂′ show X α ∶ A ⇝ A ⊣ Γᵢ
dual-hide (hide′ sc wf pop na) = show′ sc wf pop na

dual-show : ∀ {Ξ Γᵢ Γₑ X α A}
  → Sg ∣ Ξ ∣ Γᵢ ⊢̂′ show X α ∶ A ⇝ A ⊣ Γₑ
  → Sg ∣ Ξ ∣ Γₑ ⊢̂′ hide X α ∶ A ⇝ A ⊣ Γᵢ
dual-show (show′ sc wf pop na) = hide′ sc wf pop na

------------------------------------------------------------------------
-- The endpoints DO need a transport — and both are WEAKENINGS
------------------------------------------------------------------------
-- Main states both endpoint types OUTSIDE the frame and transports them
-- IN: premise (2) types `M` at `interior Θ Δ` with `Bᵢ`, premise (4)
-- says `Δ ⊢ᵗ Bₑ`, and premise (3)'s target is `shiftBy (numBinds Θ) Bₑ`
-- — the type shifted UP into the conversion's frame.  Never down.
--
-- The same works here, because `Ξ` is the LARGEST of the three:
--
--   Δᵢ = Ξ − conceals     Δ = Ξ − reveals
--
-- so both inclusions go INTO `Ξ`, and both transports are `shiftAtᵗ`
-- composites — TOTAL.  (The direction that would be partial, pushing a
-- type from `Ξ` back out, is never needed.)  For M₅:

ιᵢ ιₑ : Ty → Ty
ιᵢ = renameᵗ (shiftAtᵗ (suc zero))   -- Γ₁ ↪ Ξ: the hide's slot, at 1
ιₑ = renameᵗ (shiftAtᵗ zero)         -- Γ₃ ↪ Ξ: the show's slot, at 0

-- the body's type, stated at Δᵢ = Γ₁, transported in — and it IS the
-- source of `⊢W′`
interior-endpoint : ιᵢ (` zero ⇒ `𝔹) ≡ (` zero ⇒ `𝔹)
interior-endpoint = refl

-- the exterior type, stated at Δ = Γ₃, transported in — and it IS the
-- target of `⊢W′`
exterior-endpoint : ιₑ (` zero ⇒ `𝔹) ≡ (` suc zero ⇒ `𝔹)
exterior-endpoint = refl

-- So the boundary rule is main's `env`, clause for clause:
--
--   Σ ∣ Δᵢ ∣ [] ⊢ M ⦂ A            (2) the term, at the popped context
--   Σ ∣ Ξ ∣ Δᵢ ⊢′ c ∶ ιᵢ A ⇝ ιₑ B ⊣ Δ   (3) the conversion, in the frame
--   Δ ⊢ᵗ B                         (4) the exterior type, outside it
--   ------------------------------------
--   Σ ∣ Δ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B
--
-- and `shiftAtᵗ` has not disappeared from the calculus — it has moved
-- from EVERY `hide`/`show` to the TWO BOUNDARY ENDPOINTS, which is
-- exactly where main puts it (`shiftBy (numBinds Θ)`, once, on premise
-- (3)'s target).

------------------------------------------------------------------------
-- What `Merge` needs — and it is also the TOTAL direction
------------------------------------------------------------------------
-- `⧺′` above shares one `Ξ`.  `Merge` does not supply that: in
-- `(M ⟨ c ⟩) ⟨ d ⟩` the inner boundary's exterior is Γ₂ and the outer's
-- is Γ₃, so
--
--   Ξ_c = Γ₂ + reveals(c)          Ξ_d = Γ₃ + reveals(d)
--
-- and the merged boundary's frame is Ξ = Γ₃ + reveals(d) + reveals(c).
-- Since Γ₂ = Γ₃ + reveals(d) − conceals(d),
--
--   Ξ_d ⊆ Ξ   (insert reveals(c))
--   Ξ_c ⊆ Ξ   (insert conceals(d))
--
-- BOTH INCLUSIONS, so both transports are insertions again — no
-- strengthening anywhere.  The lemma to prove is frame weakening:
--
--   Ξ-weaken : (ρ an insertion Ξ ↪ Ξ′)
--     → Σ ∣ Ξ  ∣ Γᵢ ⊢′ c ∶ A ⇝ B ⊣ Γₑ
--     → Σ ∣ Ξ′ ∣ Γᵢ ⊢′ annRen ρ c ∶ renameᵗ ρ A ⇝ renameᵗ ρ B ⊣ Γₑ
--
-- where `annRen` renames the TERMINATOR ANNOTATIONS only: an element's
-- name X indexes the REAL context Γᵢ/Γₑ, which ρ does not touch, so the
-- pops and `NotAssigned` are carried unchanged.  Its two real
-- obligations are the premises that live at `Ξ`: `⊢ᵗ` under a renaming
-- (have it — `proof.TypeWf`) and `⇓` under a renaming (would be new,
-- but `read-var` is a lookup and insertions preserve lookups).
--
-- Main pays the same bill here and it is not small: `_⋉_` / `rewind`
-- (strong.CtxMorph §4) and `proof/MoveScope` exist for exactly this
-- move, under `IdPush` and `CancelR`.
