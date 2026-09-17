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
open import Data.Bool using (true)
open import Relation.Nullary using (¬_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Terms
open import strong.ConversionReduction using (instReveal)
open import strong.Conversion using
  (Conv; id; _∷ᶜ_; ConvElt; seal; unseal; hide; show; _↦_; all; _⧺_;
   interior; pushAsgn; _∣_⊢_∶_⇝_⊣_; conv-id; conv-cons;
   conv-seal; conv-unseal; conv-hide; conv-show; conv-fun; conv-all)

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
  -- BOTH SIDES COME FROM `Ξ`.  The element's NAME `X` indexes the real
  -- context (it is what the pop consumes); the TYPE `` ` X′ `` is the
  -- name `Ξ` has for the same address.  Conflating them — writing
  -- `` ` X `` for the type, as a first draft did — is unsound as soon
  -- as `Γₑ` and `Ξ` disagree, and `Ξ-weaken` below is what caught it.
  seal′ : ∀ {Γᵢ Γₑ X X′ α R A}
    → Σ ∣ Γₑ ∋r α := R → Σ ∣ Ξ ⊢ R ⇓ A → Ξ ∋n X′ := α
    → Γₑ ▷ X := α ⇒ Γᵢ
    → Σ ∣ Ξ ∣ Γᵢ ⊢̂′ seal X α ∶ A ⇝ ` X′ ⊣ Γₑ
  unseal′ : ∀ {Γᵢ Γₑ X X′ α R A}
    → Σ ∣ Γᵢ ∋r α := R → Σ ∣ Ξ ⊢ R ⇓ A → Ξ ∋n X′ := α
    → Γᵢ ▷ X := α ⇒ Γₑ → NotAssigned Γₑ α
    → Σ ∣ Ξ ∣ Γᵢ ⊢̂′ unseal X α ∶ ` X′ ⇝ A ⊣ Γₑ
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
    (fun′ (cons′ (seal′ r-here readΞ n-here-asgn pop-here)
                 (id′ (wf-var t-here)))
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

------------------------------------------------------------------------
-- FRAME WEAKENING — what `Merge` needs
------------------------------------------------------------------------
-- An INSERTION `Ξ ↪ Ξ′` is a renaming that preserves the three lookups
-- the frame is read through.  Only `asgn` entries are ever inserted (a
-- reveal or a conceal), so the bind skeleton — and hence `∋b`'s rank —
-- is untouched.

record Insert (ρ : Renameᵗ) (Ξ Ξ′ : Ctxᵗ) : Set where
  field
    ins-t : ∀ {X} → stk Ξ ∋ᵗ X → stk Ξ′ ∋ᵗ ρ X
    ins-n : ∀ {X α} → Ξ ∋n X := α → Ξ′ ∋n ρ X := α
    ins-b : ∀ {X i} → stk Ξ ∋b X at i → stk Ξ′ ∋b ρ X at i
open Insert

ins-bind : ∀ {ρ Ξ Ξ′} → Insert ρ Ξ Ξ′
  → Insert (extᵗ ρ) (bind ∷ stk Ξ ∥ bas Ξ) (bind ∷ stk Ξ′ ∥ bas Ξ′)
ins-t (ins-bind i) t-here = t-here
ins-t (ins-bind i) (t-there p) = t-there (ins-t i p)
ins-n (ins-bind i) (n-skip-bind p) = n-skip-bind (ins-n i p)
ins-b (ins-bind i) b-here = b-here
ins-b (ins-bind i) (b-bind p) = b-bind (ins-b i p)

wf-ren : ∀ {ρ Ξ Ξ′ A} → Insert ρ Ξ Ξ′ → Ξ ⊢ᵗ A → Ξ′ ⊢ᵗ renameᵗ ρ A
wf-ren i (wf-var n) = wf-var (ins-t i n)
wf-ren i wf-ℕ = wf-ℕ
wf-ren i wf-𝔹 = wf-𝔹
wf-ren i (wf-⇒ a b) = wf-⇒ (wf-ren i a) (wf-ren i b)
wf-ren i (wf-∀ a) = wf-∀ (wf-ren (ins-bind i) a)

-- the one genuinely NEW obligation: the read-back under a renaming
read-ren : ∀ {ρ Ξ Ξ′ R A} → Insert ρ Ξ Ξ′
  → Sg ∣ Ξ ⊢ R ⇓ A → Sg ∣ Ξ′ ⊢ R ⇓ renameᵗ ρ A
read-ren i (read-var n) = read-var (ins-n i n)
read-ren i (read-bv n) = read-bv (ins-b i n)
read-ren i read-ℕ = read-ℕ
read-ren i read-𝔹 = read-𝔹
read-ren i (read-⇒ a b) = read-⇒ (read-ren i a) (read-ren i b)
read-ren i (read-∀ a) = read-∀ (read-ren (ins-bind i) a)

-- Renaming the TERMINATOR ANNOTATIONS only.  An element's name indexes
-- the real context, which the insertion does not touch, so the atomic
-- elements are carried unchanged.
annRen : Renameᵗ → Conv → Conv
annRenElt : Renameᵗ → ConvElt → ConvElt
annRen ρ (id A)   = id (renameᵗ ρ A)
annRen ρ (ĉ ∷ᶜ c) = annRenElt ρ ĉ ∷ᶜ annRen ρ c
annRenElt ρ (seal X α)   = seal X α
annRenElt ρ (unseal X α) = unseal X α
annRenElt ρ (hide X α)   = hide X α
annRenElt ρ (show X α)   = show X α
annRenElt ρ (s ↦ t)      = annRen ρ s ↦ annRen ρ t
annRenElt ρ (all s)      = all (annRen (extᵗ ρ) s)

Ξ-weakenElt : ∀ {ρ Ξ Ξ′ Γᵢ Γₑ ĉ A B} → Insert ρ Ξ Ξ′
  → Sg ∣ Ξ  ∣ Γᵢ ⊢̂′ ĉ ∶ A ⇝ B ⊣ Γₑ
  → Sg ∣ Ξ′ ∣ Γᵢ ⊢̂′ annRenElt ρ ĉ ∶ renameᵗ ρ A ⇝ renameᵗ ρ B ⊣ Γₑ
Ξ-weaken : ∀ {ρ Ξ Ξ′ Γᵢ Γₑ c A B} → Insert ρ Ξ Ξ′
  → Sg ∣ Ξ  ∣ Γᵢ ⊢′ c ∶ A ⇝ B ⊣ Γₑ
  → Sg ∣ Ξ′ ∣ Γᵢ ⊢′ annRen ρ c ∶ renameᵗ ρ A ⇝ renameᵗ ρ B ⊣ Γₑ

Ξ-weakenElt i (seal′ r rd nm pop) =
  seal′ r (read-ren i rd) (ins-n i nm) pop
Ξ-weakenElt i (unseal′ r rd nm pop na) =
  unseal′ r (read-ren i rd) (ins-n i nm) pop na
Ξ-weakenElt i (hide′ sc wf pop na) = hide′ sc (wf-ren i wf) pop na
Ξ-weakenElt i (show′ sc wf pop na) = show′ sc (wf-ren i wf) pop na
Ξ-weakenElt i (fun′ s t) = fun′ (Ξ-weaken i s) (Ξ-weaken i t)
Ξ-weakenElt i (all′ s) = all′ (Ξ-weaken (ins-bind i) s)

Ξ-weaken i (id′ wf) = id′ (wf-ren i wf)
Ξ-weaken i (cons′ hd tl) = cons′ (Ξ-weakenElt i hd) (Ξ-weaken i tl)

------------------------------------------------------------------------
-- `unlocked` — computing `Ξ` from the syntax
------------------------------------------------------------------------
-- The mirror of `Conversion.interior`: the same walk with the CONCEALS
-- SKIPPED.  `↦` collects the reveals of both components (the element's
-- own crossing is delegated to them), `all` descends under a `bind`.

mutual
  unlockedElt : ConvElt → Ctxᵗ → Maybe Ctxᵗ
  unlockedElt (seal X α)   Γ = just Γ          -- conceal: SKIPPED
  unlockedElt (hide X α)   Γ = just Γ          -- conceal: SKIPPED
  unlockedElt (unseal X α) Γ = pushAsgn X α Γ
  unlockedElt (show X α)   Γ = pushAsgn X α Γ
  unlockedElt (s ↦ t)      Γ with unlocked t Γ
  unlockedElt (s ↦ t)      Γ | just Γ′ = unlocked s Γ′
  unlockedElt (s ↦ t)      Γ | nothing = nothing
  unlockedElt (all s) (Ss ∥ Bs) with unlocked s (bind ∷ Ss ∥ Bs)
  unlockedElt (all s) (Ss ∥ Bs) | just (bind ∷ Ss′ ∥ Bs′) = just (Ss′ ∥ Bs′)
  unlockedElt (all s) (Ss ∥ Bs) | just (asgn β ∷ Ss′ ∥ Bs′) = nothing
  unlockedElt (all s) (Ss ∥ Bs) | just ([] ∥ Bs′) = nothing
  unlockedElt (all s) (Ss ∥ Bs) | nothing = nothing

  unlocked : Conv → Ctxᵗ → Maybe Ctxᵗ
  unlocked (id A) Γ = just Γ
  unlocked (ĉ ∷ᶜ c) Γ with unlocked c Γ
  unlocked (ĉ ∷ᶜ c) Γ | just Γ′ = unlockedElt ĉ Γ′
  unlocked (ĉ ∷ᶜ c) Γ | nothing = nothing

-- and it delivers exactly the frame the derivation was given by hand
computesΞ : unlocked W′ Γ₃ ≡ just Ξ
computesΞ = refl

-- for comparison, the real interior is unchanged
computesΓ₁ : interior W′ Γ₃ ≡ just Γ₁
computesΓ₁ = refl

------------------------------------------------------------------------
-- The whole reduct, under the proposed boundary rule
------------------------------------------------------------------------
-- The rule, as a record of its premises (main's `env`, clause for
-- clause).  `Δᵢ` and `Ξ` are COMPUTED; `ιᵢ`/`ιₑ` are the two insertions
-- of §"endpoints" and would be computed from the spine the same way.

record Boundary (Δ : Ctxᵗ) (M : Term) (c : Conv) (B : Ty) : Set where
  field
    Δᵢ Ξb : Ctxᵗ
    b-int : interior c Δ ≡ just Δᵢ
    b-unl : unlocked c Δ ≡ just Ξb
    jᵢ jₑ : Renameᵗ
    A     : Ty
    b-tm  : Sg ∣ Δᵢ ∣ [] ⊢ M ⦂ A
    b-cv  : Sg ∣ Ξb ∣ Δᵢ ⊢′ c ∶ renameᵗ jᵢ A ⇝ renameᵗ jₑ B ⊣ Δ
    b-wf  : Δ ⊢ᵗ B

-- M₅'s inner boundary, at the type the ν's body must have: the redex's
-- own type `T [ ` 0 ]ᵗ = ` 0 ⇒ 𝔹`.
reduct-ok : Boundary Γ₃ (ƛ (` zero) ∙ (# true)) W′ (` zero ⇒ `𝔹)
reduct-ok = record
  { Δᵢ = Γ₁ ; Ξb = Ξ
  ; b-int = refl ; b-unl = refl
  ; jᵢ = shiftAtᵗ (suc zero) ; jₑ = shiftAtᵗ zero
  ; A = ` zero ⇒ `𝔹
  ; b-tm = ⊢ƛ (wf-var t-here) ⊢#
  ; b-cv = ⊢W′
  ; b-wf = wf-⇒ (wf-var t-here) wf-𝔹
  }

-- So the boundary `V ⟨ W′ ⟩` has type `` ` 0 ⇒ 𝔹 `` at Γ₃, which is
-- exactly what `⊢ν` needs of the ν's body (`⊢ν` moves no type), and
-- `` ` 0 ⇒ 𝔹 `` is `T [ ` 0 ]ᵗ` — the redex's type.  The step that
-- `notes/SourceToTyWrapGap.M₅-⊥` refutes today is TYPE-PRESERVING under
-- the proposed rules.
redex-type : (` zero ⇒ `𝔹) ≡ ((` zero ⇒ `𝔹) [ ` zero ]ᵗ)
redex-type = refl

------------------------------------------------------------------------
-- TWO CONCEALS AT DIFFERENT DEPTHS
------------------------------------------------------------------------
-- The question `unlocked` leaves open: its `pushAsgn X α` inserts at the
-- element's LOCAL name, but by then the frame has skipped conceals the
-- real context popped, so the two disagree about where slot X is.  Main
-- does not have this problem — "a change names an EXTERIOR slot and is
-- unshifted by the morphism's own binds".
--
-- Here is the smallest spine that separates them: a conceal at depth 0
-- and a reveal at depth 1, over a two-assignment exterior.

Sg2 : Store
Sg2 = `𝔹ᴿ ∷ `ℕᴿ ∷ []

Δ2 : Ctxᵗ
Δ2 = asgn (lvl zero) ∷ asgn (lvl (suc zero)) ∷ [] ∥ nuBind `𝔹ᴿ ∷ []

c2 : Conv
c2 = show (suc zero) (bse zero) ∷ᶜ hide zero (lvl zero) ∷ᶜ id `𝔹

-- the real interior pops `lvl 0`, THEN pushes `bse 0` at depth 1
int2 : interior c2 Δ2
     ≡ just (asgn (lvl (suc zero)) ∷ asgn (bse zero) ∷ [] ∥ nuBind `𝔹ᴿ ∷ [])
int2 = refl

-- the frame SKIPS the pop, so its depth-1 slot is a different one
unl2 : unlocked c2 Δ2
     ≡ just (asgn (lvl zero) ∷ asgn (bse zero) ∷ asgn (lvl (suc zero)) ∷ []
             ∥ nuBind `𝔹ᴿ ∷ [])
unl2 = refl

-- and the two DISAGREE on what sits at each index:
--    Δᵢ :  0 ↦ lvl 1   1 ↦ bse 0
--    Ξ  :  0 ↦ lvl 0   1 ↦ bse 0   2 ↦ lvl 1
-- so the embedding is 0 ↦ 2, 1 ↦ 1 — NOT MONOTONE, hence not any
-- composite of `shiftAtᵗ`s.
ρ2 : Renameᵗ
ρ2 zero = suc (suc zero)
ρ2 (suc zero) = suc zero
ρ2 (suc (suc n)) = suc (suc n)

-- It is still an `Insert`, though: `Insert` asks only that the three
-- lookups be preserved, and ρ2 sends each slot to the slot holding the
-- SAME ADDRESS.  So frame weakening and the endpoint transports survive
-- — but they are address-matching renamings, determined by `NameFn`,
-- not shifts.
ins2 : Insert ρ2
         (asgn (lvl (suc zero)) ∷ asgn (bse zero) ∷ [] ∥ nuBind `𝔹ᴿ ∷ [])
         (asgn (lvl zero) ∷ asgn (bse zero) ∷ asgn (lvl (suc zero)) ∷ []
          ∥ nuBind `𝔹ᴿ ∷ [])
ins-t ins2 t-here = t-there (t-there t-here)
ins-t ins2 (t-there t-here) = t-there t-here
ins-t ins2 (t-there (t-there ()))
ins-n ins2 n-here-asgn = n-skip-asgn (n-skip-asgn n-here-asgn)
ins-n ins2 (n-skip-asgn n-here-asgn) = n-skip-asgn n-here-asgn
ins-n ins2 (n-skip-asgn (n-skip-asgn ()))
ins-b ins2 (b-asgn (b-asgn ()))

------------------------------------------------------------------------
-- THE DUPLICATE-ADDRESS HAZARD, and the premise that closes it
------------------------------------------------------------------------
-- Jeremy: "In a given context, there should not be two distinct type
-- names with the same address."  That is `NameFn` — and it is NOT
-- automatic for `Ξ`.  A `hide X α` followed by a `show Y α` with X ≠ Y
-- is well typed TODAY: the show's freshness `NotAssigned Γₑ α` is
-- checked at its own exterior, where the hide has already removed X.
-- `fuse` does not cancel them either, since the names differ.  But `Ξ`
-- SKIPS the hide and KEEPS the show, so it holds two names for α.

Sg3 : Store
Sg3 = `𝔹ᴿ ∷ []

Δ3 : Ctxᵗ                      -- a bind, so the pop can reach depth 1
Δ3 = bind ∷ asgn (lvl zero) ∷ [] ∥ []

c3 : Conv
c3 = show zero (lvl zero) ∷ᶜ hide (suc zero) (lvl zero) ∷ᶜ id `𝔹

-- it is well typed under the CURRENT rules
⊢c3 : Sg3 ∣ (asgn (lvl zero) ∷ bind ∷ [] ∥ []) ⊢ c3 ∶ `𝔹 ⇝ `𝔹 ⊣ Δ3
⊢c3 = conv-cons (conv-show (a-lvl l-here) wf-𝔹 pop-here
                  (λ { (n-skip-bind ()) }))
        (conv-cons (conv-hide (a-lvl l-here) wf-𝔹
                     (pop-bind pop-here) (λ { (n-skip-bind ()) }))
          (conv-id wf-𝔹))

-- and its frame holds `lvl 0` at TWO names, 0 and 2
unl3 : unlocked c3 Δ3
     ≡ just (asgn (lvl zero) ∷ bind ∷ asgn (lvl zero) ∷ [] ∥ [])
unl3 = refl

Ξ3 : Ctxᵗ
Ξ3 = asgn (lvl zero) ∷ bind ∷ asgn (lvl zero) ∷ [] ∥ []

namefn-⊥ : ¬ NameFn Ξ3
namefn-⊥ nf with nf n-here-asgn (n-skip-asgn (n-skip-bind n-here-asgn))
namefn-⊥ nf | ()

-- THE FIX, exactly where Jeremy put it: state a reveal's freshness at
-- the FRAME, not at its local exterior.  `Δ3` already assigns `lvl 0`
-- (at name 1), so the show above is rejected …
rejected : ¬ NotAssigned Δ3 (lvl zero)
rejected na = na (n-skip-bind n-here-asgn)

-- … while M₅'s show, whose address is the ν's `bse 0`, still passes:
-- the frame before it is Γ₃, which assigns only `lvl 0`.
accepted : NotAssigned Γ₃ (bse zero)
accepted (n-skip-asgn ())

-- and the frame M₅ actually gets is name-functional
namefnΞ : NameFn Ξ
namefnΞ n-here-asgn n-here-asgn = refl
namefnΞ n-here-asgn (n-skip-asgn (n-skip-asgn ()))
namefnΞ (n-skip-asgn n-here-asgn) (n-skip-asgn n-here-asgn) = refl
namefnΞ (n-skip-asgn (n-skip-asgn ())) q

------------------------------------------------------------------------
-- THE BUILDERS — what has to change, and the recipe
------------------------------------------------------------------------
-- `instReveal` today produces `W` (notes/SourceToTyWrapGap), which has
-- no typing; the proposal wants `W′`.  They differ in EXACTLY ONE
-- annotation:
--
--   W   = (… ↦ …) ∷ᶜ hide 0 (lvl 0) ∷ᶜ id (` 0 ⇒ 𝔹)
--   W′  = (… ↦ …) ∷ᶜ hide 0 (lvl 0) ∷ᶜ id (` 1 ⇒ 𝔹)
--
-- and NO UNIFORM RENAMING relates them: `annRen (shiftAtᵗ 0) W` also
-- moves the seal's `id (` 0)` to `id (` 1)`, which `⊢W′` does not want.

-- `W` as `instReveal` builds it today (notes/SourceToTyWrapGap.W)
Wnow : Conv
Wnow = ((seal zero (bse zero) ∷ᶜ id (` zero))
         ↦ (show zero (bse zero) ∷ᶜ id `𝔹))
       ∷ᶜ hide zero (lvl zero) ∷ᶜ id (` zero ⇒ `𝔹)

built-today : instReveal Sg (bind ∷ [] ∥ []) zero (bse zero) (` zero)
                (hide (suc zero) (lvl zero) ∷ᶜ id (` zero ⇒ `𝔹))
            ≡ Wnow
built-today = refl

not-uniform : annRen (shiftAtᵗ zero) Wnow ≢ W′
not-uniform ()

-- The reason is that today EACH ANNOTATION IS IN ITS OWN LOCAL FRAME,
-- so the same syntax `` ` 0 `` means Y at one position and X at another.
-- Under the proposal they are all in `Ξ`, where `` ` 0 `` is Y and
-- `` ` 1 `` is X — one frame, no coincidences.  The recipe is therefore
-- POSITION-WISE: transport each terminator along the insertion from ITS
-- OWN local context into `Ξ`.  On `W`'s three terminators:

--   1.  `id (` 0)` sits after the seal, at Γ₁.  `bse 0` is slot 0 in
--       Γ₁ AND in Ξ, so the map is the identity there.
retarget₁ : renameᵗ (λ n → n) (` zero) ≡ ` zero
retarget₁ = refl

--   2.  `id 𝔹` sits after the show, at Γ₁.  No variables.
retarget₂ : renameᵗ (λ n → n) `𝔹 ≡ `𝔹
retarget₂ = refl

--   3.  `id (` 0 ⇒ 𝔹)` is the terminator, at Γ₃.  `lvl 0` is slot 0 in
--       Γ₃ but slot 1 in Ξ, so the map is `shiftAtᵗ 0`.
retarget₃ : renameᵗ (shiftAtᵗ zero) (` zero ⇒ `𝔹) ≡ (` suc zero ⇒ `𝔹)
retarget₃ = refl

-- … and that is `W′` on the nose.
recipe : ((seal zero (bse zero) ∷ᶜ id (renameᵗ (λ n → n) (` zero)))
           ↦ (show zero (bse zero) ∷ᶜ id (renameᵗ (λ n → n) `𝔹)))
         ∷ᶜ hide zero (lvl zero)
         ∷ᶜ id (renameᵗ (shiftAtᵗ zero) (` zero ⇒ `𝔹))
       ≡ W′
recipe = refl

------------------------------------------------------------------------
-- … AND A CORRECTION TO `unlocked` THAT THE BUILDERS WANT
------------------------------------------------------------------------
-- `unlocked` inserts a reveal at its LOCAL name X.  That is what made
-- `ins2`'s map non-monotone, and a non-monotone map is bad news for the
-- builders: each terminator's transport stops being a `shiftAtᵗ`
-- composite and has to be recomputed by address matching.
--
-- The fix is to insert at the FRAME position instead — i.e. to carry
-- the map ρ : Γ → Ξ along the walk and insert at ρ X.  Main has this
-- for free ("a change names an EXTERIOR slot and is unshifted by the
-- morphism's own binds"); v8's names are local, so the walk must track
-- it.  Redoing the two-conceals case that way:
--
--   start            Γ = lvl 0, lvl 1        Ξ = lvl 0, lvl 1     ρ = id
--   hide 0 (lvl 0)   Γ = lvl 1               Ξ unchanged          ρ = shiftAtᵗ 0
--   show 1 (bse 0)   Γ = lvl 1, bse 0        insert at ρ 1 = 2
--                                            Ξ = lvl 0, lvl 1, bse 0
--
-- and now Γ's 0 ↦ Ξ's 1, Γ's 1 ↦ Ξ's 2 — MONOTONE, and exactly
-- `shiftAtᵗ 0`.

Δ2ᵢ Ξ2′ : Ctxᵗ
Δ2ᵢ = asgn (lvl (suc zero)) ∷ asgn (bse zero) ∷ [] ∥ nuBind `𝔹ᴿ ∷ []
Ξ2′ = asgn (lvl zero) ∷ asgn (lvl (suc zero)) ∷ asgn (bse zero) ∷ []
      ∥ nuBind `𝔹ᴿ ∷ []

ins2′ : Insert (shiftAtᵗ zero) Δ2ᵢ Ξ2′
ins-t ins2′ t-here = t-there t-here
ins-t ins2′ (t-there t-here) = t-there (t-there t-here)
ins-t ins2′ (t-there (t-there ()))
ins-n ins2′ n-here-asgn = n-skip-asgn n-here-asgn
ins-n ins2′ (n-skip-asgn n-here-asgn) =
  n-skip-asgn (n-skip-asgn n-here-asgn)
ins-n ins2′ (n-skip-asgn (n-skip-asgn ()))
ins-b ins2′ (b-asgn (b-asgn ()))

-- So the recommendation for the port: `unlocked` returns `(Ξ , ρ)`,
-- inserting each reveal at `ρ X`; every transport in sight — `jᵢ`, `jₑ`
-- and the builders' per-terminator retargeting — is then a `shiftAtᵗ`
-- composite, and `NameFn Ξ` follows from the strengthened freshness
-- premise rather than having to be re-established by address matching.
