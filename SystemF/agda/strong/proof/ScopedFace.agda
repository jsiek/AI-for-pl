module strong.proof.ScopedFace where

-- THE FACE-CONDITIONED CANDIDATE, RUN ON THE EXAMPLES.
--
-- proof/WallGrounding closed the `Bwf` route and pointed at this one: put
-- the scoping condition on the `env` node itself, switched by the FACE's
-- POLARITY, so that ONE rule survives.  The proposal, verbatim:
--
--     ScopedAt : Pol → Ctxᵗ → CtxMorph → Ty → Set
--     ScopedAt ↑ˢ Δ Θ Bₑ = scp Θ Δ ⊢ᵗ Bₑ
--     ScopedAt ↓ˢ Δ Θ Bₑ = ⊤
--
--     env : ∀ {Δ Γ Θ c M Bᵢ Bₑ p}
--         → Bwf Δ Θ
--         → intC Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
--         → fceC Θ Δ ⊢ c ∶ Bᵢ ⇝ liftN (nbind Θ) Bₑ ∙ p
--         → Δ ⊢ᵗ Bₑ
--         → ScopedAt p Δ Θ Bₑ
--           --------------------------------------------
--         → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ
--
-- (`Δ ⊢ᵗ Bₑ` stays: `scp` UNMASKS as well as masks, so the new premise
-- does not subsume it.)
--
-- THE VERDICT, in three parts.
--
--   §2  IT DOES WHAT WALLGROUNDING ASKED.  ⊑-stable, free on every
--       lock-free frame, and it REJECTS the `¬IdPushCase` witness while
--       ADMITTING the reachable `seal`-faced wall wrapper of Examples §12.
--
--   §3  BUT IT DOES NOT DISCHARGE IDPUSH.  The obstruction MOVES: IdPush
--       turns the INNER, id-faced layer into an `unseal`-faced one, so the
--       contractum owes `ScopedAt ↑ˢ` at `Θ₁` — which the redex's own
--       premises never mention, because the redex's inner face is
--       `id (` X)`, whose obligation is about `` ` X `` and not about X's
--       REP.  §3 builds a redex satisfying EVERY proposed premise whose
--       contractum fails the new one.  (It types fine TODAY: this refutes
--       the candidate's SUFFICIENCY, not the current IdPush.)
--
--   §4  THE ↓ˢ-PEEL CROSSING IS FINE.  The obligation WallGrounding §4f
--       flagged — a Peel at p = ↓ˢ puts its crossing wrapper at ↑ˢ, where
--       proof/WallGrounding's `¬Scoped-crossing` shape lives — is
--       DISCHARGEABLE, and §4 proves it.  A `flip p` face's target can
--       never name one of the crossed boundary's OWN owners, because its
--       source is a `liftN (nbind Θ)` and every rep on the face type
--       context is one too.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; m≤m+n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.Ctx
open import strong.Conversion
open import strong.Terms
open import strong.TermSubst using (⊢retag; wkN)
open import strong.Reduction
open import strong.proof.Preserve using (⊢ᵗ-of; CtxWf-[]; ∋tv-tail)
open import strong.proof.PeelDual
  using (intC-dual; prep-++; length-prep; reps-dual; ⊑-app; Δ⊑fscp;
         renᵗ-wkN)
open import strong.proof.WallReach using (wf-liftN-prep)
open import strong.proof.WallGrounding using (Scoped)
open import strong.proof.PreserveObstruct using (Δi; Θi; ⊢Ri)

------------------------------------------------------------------------
-- §1  THE CANDIDATE
------------------------------------------------------------------------

ScopedAt : Pol → Ctxᵗ → CtxMorph → Ty → Set
ScopedAt ↑ˢ Δ Θ Bₑ = scp Θ Δ ⊢ᵗ Bₑ
ScopedAt ↓ˢ Δ Θ Bₑ = ⊤

-- a conceal owes nothing …
ScopedAt-↓ : ∀ {Δ Θ Bₑ} → ScopedAt ↓ˢ Δ Θ Bₑ
ScopedAt-↓ = tt

-- … and at ↑ˢ it IS `Scoped` (proof/WallGrounding §4).
ScopedAt-↑ : ∀ {Δ Θ Bₑ} → Scoped Δ Θ Bₑ → ScopedAt ↑ˢ Δ Θ Bₑ
ScopedAt-↑ w = w

------------------------------------------------------------------------
-- §2  WHAT IT BUYS
------------------------------------------------------------------------

-- ⊑-STABLE at both polarities — the property that killed the `Bwf`
-- route (proof/WallGrounding §3).  So `Bwf-⊑`/`⊢retag` survive.
ScopedAt-⊑ : ∀ {Δ Δ′ Bₑ} (p : Pol) (Θ : CtxMorph)
  → Δ ⊑ Δ′ → ScopedAt p Δ Θ Bₑ → ScopedAt p Δ′ Θ Bₑ
ScopedAt-⊑ ↑ˢ Θ ls w = ⊑-wf (⊑-scp Θ ls) w
ScopedAt-⊑ ↓ˢ Θ ls w = tt

-- FREE on a binds-only frame, which is every frame TyBeta and CancelR
-- mint (`scp` is the identity there).
ScopedAt-bind : ∀ {Δ A Bₑ} (p : Pol)
  → Δ ⊢ᵗ Bₑ → ScopedAt p Δ (bind A ∷ []) Bₑ
ScopedAt-bind ↑ˢ w = w
ScopedAt-bind ↓ˢ w = tt

-- DELIVERS the missing premise: the rep an `unseal` face hands back IS
-- `liftN (nbind Θ) Bₑ`.
ScopedAt→interior : ∀ {Δ Bₑ} (Θ : CtxMorph)
  → ScopedAt ↑ˢ Δ Θ Bₑ → intC Θ Δ ⊢ᵗ liftN (nbind Θ) Bₑ
ScopedAt→interior Θ w = wf-liftN-prep (reps Θ) w

-- REJECTS the `¬IdPushCase` witness (its own frame locks the slot its
-- exterior type names) …
¬ScopedAt-Ri : ¬ ScopedAt ↑ˢ Δi Θi (` 1)
¬ScopedAt-Ri (wf-var (_ , es ez , ()))

-- … and ADMITS the REACHABLE wall wrapper, which is a CONCEAL.
ScopedAt-L₄-wall : ScopedAt ↓ˢ (bind (` 0) ∷ bind `ℕ ∷ []) (lock 1 ∷ []) (` 1)
ScopedAt-L₄-wall = tt

------------------------------------------------------------------------
-- §3  THE GAP — IDPUSH MOVES THE OBSTRUCTION TO Θ₁
------------------------------------------------------------------------

-- IdPush SWAPS THE FACES.  The inner layer's face goes from `id (` X)`
-- (which owes nothing about X's rep) to `unseal X` (which owes
-- everything about it), at an UNCHANGED frame Θ₁.  So the new premise has
-- to hold for Θ₁ AFTER the step while the redex only ever declared it for
-- `` ` X ``.  Any lock in Θ₁ that blocks the REP but not the NAME is the
-- gap — and that configuration is typeable.

-- Δ★ is the chained-rep type context (slot 0's rep NAMES slot 1) — the
-- same one Examples §12 reaches from closed source.
Δ★ : Ctxᵗ
Δ★ = bind (` 0) ∷ bind `ℕ ∷ []

-- Θ₂ is LOCK-FREE, so the outer boundary owes nothing new …
Θ★₂ : CtxMorph
Θ★₂ = bind `ℕ ∷ []

Ξ★ : Ctxᵗ
Ξ★ = bind `ℕ ∷ bind (` 0) ∷ bind `ℕ ∷ []

_ : intC Θ★₂ Δ★ ≡ Ξ★
_ = refl

_ : fceC Θ★₂ Δ★ ≡ Ξ★
_ = refl

-- slot 1 of Ξ★ is the chained owner: its rep is slot 2.
_ : Ξ★ ∋ 1 := ` 2
_ = es ez

-- … and Θ₁ locks slot 2 — the REP of the slot its own id-face names.
Θ★₁ : CtxMorph
Θ★₁ = lock 2 ∷ []

Ψ★ : Ctxᵗ
Ψ★ = bind `ℕ ∷ bind (` 0) ∷ blk (bind `ℕ) ∷ []

_ : intC Θ★₁ Ξ★ ≡ Ψ★
_ = refl

_ : fceC Θ★₁ Ξ★ ≡ Ξ★
_ = refl

-- slot 1 — the id-face's NAME — is still nameable inside Θ★₁ …
ScopedAt-name : ∀ (p : Pol) → ScopedAt p Ξ★ Θ★₁ (` 1)
ScopedAt-name ↑ˢ = wf-var (bind (` 2) , es ez , vis-b)
ScopedAt-name ↓ˢ = tt

-- … while slot 2 — its REP — is not.
¬ScopedAt-rep : ¬ ScopedAt ↑ˢ Ξ★ Θ★₁ (` 2)
¬ScopedAt-rep (wf-var (_ , es (es ez) , ()))

-- ── THE VALUE, and the redex ───────────────────────────────────────────

V★ : Term
V★ = (($ 7) ⟪ [] , seal 2 ⟫) ⟪ unlock 2 ∷ [] , seal 1 ⟫

_ : intC (unlock 2 ∷ []) Ψ★ ≡ Ξ★
_ = refl

⊢V★in : Ξ★ ∣ [] ⊢ ($ 7) ⟪ [] , seal 2 ⟫ ⦂ ` 2
⊢V★in = env {p = ↓ˢ} bw[] ⊢$ (conv-seal (es (es ez)))
            (wf-var (bind `ℕ , es (es ez) , vis-b))

⊢V★ : Ψ★ ∣ [] ⊢ V★ ⦂ ` 1
⊢V★ = env {p = ↓ˢ} (bw-u (es (es ez)) bw[]) ⊢V★in (conv-seal (es ez))
           (wf-var (bind (` 2) , es ez , vis-b))

val-V★ : Value V★
val-V★ = V-⟪⟫ (V-⟪⟫ V-$ I-seal) I-seal

R★ C★ : Term
R★ = (V★ ⟪ Θ★₁ , id (` 1) ⟫) ⟪ Θ★₂ , unseal 1 ⟫
C★ = (V★ ⟪ Θ★₁ , unseal 1 ⟫) ⟪ Θ★₂ , idc (` 2) ⟫

⊢R★in : Ξ★ ∣ [] ⊢ V★ ⟪ Θ★₁ , id (` 1) ⟫ ⦂ ` 1
⊢R★in = env {p = ↑ˢ} (bw-l (bind `ℕ , es (es ez) , vis-b) bw[]) ⊢V★
             (conv-idv (bind (` 2) , es ez , vis-b))
             (wf-var (bind (` 2) , es ez , vis-b))

⊢R★ : Δ★ ∣ [] ⊢ R★ ⦂ ` 1
⊢R★ = env {p = ↑ˢ} (bw-b wf-ℕ bw[]) ⊢R★in (conv-unseal (es ez))
           (wf-var (bind `ℕ , es ez , vis-b))

step★ : Δ★ ⊢ R★ -→ C★
step★ = IdPush val-V★ (es ez)

-- ── EVERY PROPOSED PREMISE HOLDS ON THE REDEX ─────────────────────────

-- outer boundary: ↑ˢ (an `unseal` face), frame lock-free
scoped-R★-outer : ScopedAt ↑ˢ Δ★ Θ★₂ (` 1)
scoped-R★-outer = wf-var (bind `ℕ , es ez , vis-b)

-- inner boundary: `id (` 1)` types at EITHER polarity, and the premise
-- holds at both — so no choice of `p` refuses the redex.
scoped-R★-inner : ∀ (p : Pol) → ScopedAt p Ξ★ Θ★₁ (` 1)
scoped-R★-inner = ScopedAt-name

-- ── AND THE CONTRACTUM'S DOES NOT ─────────────────────────────────────

-- The swapped inner face is `unseal 1`, forced to ↑ˢ, with exterior type
-- the REP ` 2 — and `¬ScopedAt-rep` refuses it.
contractum-owes : ¬ ScopedAt ↑ˢ Ξ★ Θ★₁ (` 2)
contractum-owes = ¬ScopedAt-rep

-- The contractum types under the CURRENT rules (`env`'s existing
-- `Δ ⊢ᵗ Bₑ` premise is `Ξ★ ⊢ᵗ ` 2`, which HOLDS): so §3 refutes the
-- candidate's SUFFICIENCY, not today's IdPush.
⊢C★in : Ξ★ ∣ [] ⊢ V★ ⟪ Θ★₁ , unseal 1 ⟫ ⦂ ` 2
⊢C★in = env {p = ↑ˢ} (bw-l (bind `ℕ , es (es ez) , vis-b) bw[]) ⊢V★
             (conv-unseal (es ez))
             (wf-var (bind `ℕ , es (es ez) , vis-b))

⊢C★ : Δ★ ∣ [] ⊢ C★ ⦂ ` 1
⊢C★ = env {p = ↑ˢ} (bw-b wf-ℕ bw[]) ⊢C★in
           (conv-idv (bind `ℕ , es (es ez) , vis-b))
           (wf-var (bind `ℕ , es ez , vis-b))

-- THE READING.  Under the candidate `env`, `⊢R★` still builds (all five
-- premises: `scoped-R★-outer`, `scoped-R★-inner`) and `⊢C★in` does not
-- (`contractum-owes`).  IdPush therefore does NOT become a theorem.  What
-- the premise would have to say at an `id (` X)` face is not about the
-- exterior type at all but about X's REP — i.e. `RepWf (intC Θ Δ)` at
-- every id- and unseal-faced boundary, which is the narrowed reading
-- proof/WallReach §6 already isolates.  Whether THAT survives TyBeta's
-- retag is the next question: proof/WallGrounding's counterexample is a
-- `seal` face, which the narrowed reading also exempts.

------------------------------------------------------------------------
-- §4  THE ↓ˢ-PEEL CROSSING — DISCHARGEABLE
------------------------------------------------------------------------

-- proof/WallGrounding §4e exhibits a crossing wrapper that VIOLATES the
-- premise (`¬Scoped-crossing`), and §4f observes it sits at ↓ˢ, where
-- nothing is owed.  The obligation left open was the other polarity: a
-- Peel at p = ↓ˢ puts its crossing at ↑ˢ, so the crossing then OWES
--
--     scp (dual Θ) (intC Θ Δ) ⊢ᵗ Aᵈ
--
-- where Aᵈ is V's domain read INSIDE — a type that may name Θ's owners,
-- which is exactly what `dual Θ` locks.  §4 DISCHARGES it.
--
-- THE ARGUMENT.  The crossing's face `s` runs `liftN (nbind Θ) Aarg ⇝ Aᵈ`
-- on `fceC Θ Δ`.  Its SOURCE is a lift, so it names no slot below
-- `nbind Θ`; every REP on `fceC Θ Δ` is a lift too (`prep` stores each rep
-- over the PLAIN exterior — SIMULTANEITY); and a conversion only ever
-- replaces a name by its rep or a rep by its name.  So the TARGET names no
-- slot below `nbind Θ` either — and `Aᵈ`, which is well formed inside, is
-- therefore still well formed with the owner prefix blocked.

-- `Lo k n A`: no free variable of A lies in the WINDOW [k, k+n).  A
-- window, not a threshold: under a `∀ the bound slot must stay legal, so
-- the window's floor rises with the binder depth k.
Lo : ℕ → ℕ → Ty → Set
Lo k n (` X)   = (suc X ≤ k) ⊎ (k + n ≤ X)
Lo k n `ℕ      = ⊤
Lo k n `𝔹      = ⊤
Lo k n (A ⇒ B) = Lo k n A × Lo k n B
Lo k n (`∀ A)  = Lo (suc k) n A

LoRen : ℕ → ℕ → ℕ → ℕ → Renameᵗ → Set
LoRen k n k′ n′ ρ = ∀ X → (suc X ≤ k) ⊎ (k + n ≤ X)
                        → (suc (ρ X) ≤ k′) ⊎ (k′ + n′ ≤ ρ X)

LoRen-ext : ∀ {k n k′ n′ ρ} → LoRen k n k′ n′ ρ
          → LoRen (suc k) n (suc k′) n′ (extᵗ ρ)
LoRen-ext h zero    lo = inj₁ (s≤s z≤n)
LoRen-ext h (suc X) (inj₁ (s≤s le)) with h X (inj₁ le)
... | inj₁ le′ = inj₁ (s≤s le′)
... | inj₂ ge′ = inj₂ (s≤s ge′)
LoRen-ext h (suc X) (inj₂ (s≤s ge)) with h X (inj₂ ge)
... | inj₁ le′ = inj₁ (s≤s le′)
... | inj₂ ge′ = inj₂ (s≤s ge′)

Lo-ren : ∀ {k n k′ n′ ρ} (A : Ty)
       → LoRen k n k′ n′ ρ → Lo k n A → Lo k′ n′ (renameᵗ ρ A)
Lo-ren (` X)   h lo          = h X lo
Lo-ren `ℕ      h lo          = tt
Lo-ren `𝔹      h lo          = tt
Lo-ren (A ⇒ B) h (loA , loB) = Lo-ren A h loA , Lo-ren B h loB
Lo-ren (`∀ A)  h lo          = Lo-ren A (LoRen-ext h) lo

low-or-high : (k X : ℕ) → (suc X ≤ k) ⊎ (k ≤ X)
low-or-high zero    X       = inj₂ z≤n
low-or-high (suc k) zero    = inj₁ (s≤s z≤n)
low-or-high (suc k) (suc X) with low-or-high k X
... | inj₁ le = inj₁ (s≤s le)
... | inj₂ ge = inj₂ (s≤s ge)

-- an EMPTY window excludes nothing
Lo-zero : (k : ℕ) (A : Ty) → Lo k 0 A
Lo-zero k (` X) with low-or-high k X
... | inj₁ le = inj₁ le
... | inj₂ ge = inj₂ (subst (_≤ X) (sym (+-identityʳ k)) ge)
Lo-zero k `ℕ      = tt
Lo-zero k `𝔹      = tt
Lo-zero k (A ⇒ B) = Lo-zero k A , Lo-zero k B
Lo-zero k (`∀ A)  = Lo-zero (suc k) A

-- A LIFT NAMES NOTHING IT LIFTS PAST.  This is the whole reason the
-- crossing is safe, and the reason `prep`'s simultaneity matters.
Lo-liftN : (n : ℕ) (A : Ty) → Lo 0 n (liftN n A)
Lo-liftN n A =
  subst (Lo 0 n) (renᵗ-wkN n A) (Lo-ren A h (Lo-zero 0 A))
  where
  h : LoRen 0 0 0 n (wkN n)
  h X _ = inj₂ (m≤m+n n X)

-- shifting one binder outwards widens the window by one
Lo-⇑ : ∀ {n} (A : Ty) → Lo 0 n A → Lo 0 (suc n) (⇑ᵗ A)
Lo-⇑ {n} A lo = Lo-ren A h lo
  where
  h : LoRen 0 n 0 (suc n) suc
  h X (inj₂ ge) = inj₂ (s≤s ge)

------------------------------------------------------------------------
-- §4a  EVERY REP ON A FACE TYPE CONTEXT IS A LIFT
------------------------------------------------------------------------

RepLo : ℕ → ℕ → Ctxᵗ → Set
RepLo k n F = ∀ {Y A} → F ∋ Y := A → Lo k n A

-- One-step inversion of a lookup past a cons.  It is stated on a
-- GENERAL entry: at the `bind A` index the shift `⇑ᵉ E` is not in
-- constructor form, so `es` cannot be matched there directly.
cons-∋e⁻ : ∀ {F E Y E′} → (E ∷ F) ∋e suc Y , E′
         → ∃[ E₀ ] ((F ∋e Y , E₀) × (E′ ≡ ⇑ᵉ E₀))
cons-∋e⁻ (es d) = _ , d , refl

zero-∋e⁻ : ∀ {F E E′} → (E ∷ F) ∋e zero , E′ → E′ ≡ ⇑ᵉ E
zero-∋e⁻ ez = refl

zero-∋bind⁻ : ∀ {F A B} → (bind B ∷ F) ∋ zero := A → A ≡ ⇑ᵗ B
zero-∋bind⁻ d = bind-inj (zero-∋e⁻ d)

cons-∋bind⁻ : ∀ {F E Y A} → (E ∷ F) ∋ suc Y := A
            → ∃[ A₀ ] ((F ∋ Y := A₀) × (A ≡ ⇑ᵗ A₀))
cons-∋bind⁻ d with cons-∋e⁻ d
... | abst    , d₀ , ()
... | bind A₀ , d₀ , refl = A₀ , d₀ , refl
... | blk E₀  , d₀ , ()

RepLo-abst : ∀ {k n F} → RepLo k n F → RepLo (suc k) n (abst ∷ F)
RepLo-abst h {zero}  ()
RepLo-abst {k} {n} h {suc Y} d with cons-∋bind⁻ d
... | A₀ , d₀ , refl = Lo-ren A₀ hs (h d₀)
  where
  hs : LoRen k n (suc k) n suc
  hs X (inj₁ le) = inj₁ (s≤s le)
  hs X (inj₂ ge) = inj₂ (s≤s ge)

-- `prep` stores each rep as a type over the PLAIN exterior, lifted past
-- the owners bound inside it — so no rep of `prep As Ξ` names an owner.
prep-RepLo : (As : List Ty) (Ξ : Ctxᵗ) → RepLo 0 (length As) (prep As Ξ)
prep-RepLo []       Ξ {_} {A} d = Lo-zero 0 A
prep-RepLo (C ∷ As) Ξ {zero} d =
  subst (Lo 0 (suc (length As))) (sym (zero-∋bind⁻ d))
        (Lo-liftN (suc (length As)) C)
prep-RepLo (C ∷ As) Ξ {suc Y} d with cons-∋bind⁻ d
... | A₀ , d₀ , refl = Lo-⇑ A₀ (prep-RepLo As Ξ d₀)

fceC-RepLo : (Θ : CtxMorph) (Δ : Ctxᵗ) → RepLo 0 (nbind Θ) (fceC Θ Δ)
fceC-RepLo Θ Δ = prep-RepLo (reps Θ) (fscp Θ Δ)

------------------------------------------------------------------------
-- §4b  A CONVERSION CANNOT REACH INTO THE WINDOW
------------------------------------------------------------------------

-- The mutual induction: a REVEAL carries the property forwards (source to
-- target), a CONCEAL backwards.  `conv-unseal`/`conv-seal` are the only
-- clauses with content, and both are discharged by `RepLo`.
mutual
  conv-Lo-↑ : ∀ {F c S T k n} → RepLo k n F
            → F ⊢ c ∶ S ⇝ T ∙ ↑ˢ → Lo k n S → Lo k n T
  conv-Lo-↑ h (conv-id b)      lo = lo
  conv-Lo-↑ h (conv-idv tv)    lo = lo
  conv-Lo-↑ h (conv-unseal d)  lo = h d
  conv-Lo-↑ h (conv-fun ⊢s ⊢t) (loA , loB) =
    conv-Lo-↓ h ⊢s loA , conv-Lo-↑ h ⊢t loB
  conv-Lo-↑ h (conv-all ⊢s)    lo = conv-Lo-↑ (RepLo-abst h) ⊢s lo

  conv-Lo-↓ : ∀ {F c S T k n} → RepLo k n F
            → F ⊢ c ∶ S ⇝ T ∙ ↓ˢ → Lo k n T → Lo k n S
  conv-Lo-↓ h (conv-id b)      lo = lo
  conv-Lo-↓ h (conv-idv tv)    lo = lo
  conv-Lo-↓ h (conv-seal d)    lo = h d
  conv-Lo-↓ h (conv-fun ⊢s ⊢t) (loA′ , loB′) =
    conv-Lo-↑ h ⊢s loA′ , conv-Lo-↓ h ⊢t loB′
  conv-Lo-↓ h (conv-all ⊢s)    lo = conv-Lo-↓ (RepLo-abst h) ⊢s lo

------------------------------------------------------------------------
-- §4c  BLOCKING A PREFIX THE TYPE DOES NOT NAME
------------------------------------------------------------------------

∋tv-cons : ∀ {Δ X E} → Δ ∋tv X → (E ∷ Δ) ∋tv suc X
∋tv-cons (E₀ , d , v) = _ , es d , renᵉ-Vis v

∋tv-low : ∀ {Ψ Ψ′ X} (Q : Ctxᵗ) → suc X ≤ length Q
        → (Q ++ Ψ) ∋tv X → (Q ++ Ψ′) ∋tv X
∋tv-low {X = zero}  (E ∷ Q) le (E₀ , ez , v) = _ , ez , v
∋tv-low {X = suc X} (E ∷ Q) (s≤s le) tv =
  ∋tv-cons (∋tv-low Q le (∋tv-tail tv))

∋tv-high⁻ : ∀ {Ψ j} (P : Ctxᵗ) → (P ++ Ψ) ∋tv (length P + j) → Ψ ∋tv j
∋tv-high⁻ []      tv = tv
∋tv-high⁻ (E ∷ P) tv = ∋tv-high⁻ P (∋tv-tail tv)

∋tv-high⁺ : ∀ {Ψ j} (P : Ctxᵗ) → Ψ ∋tv j → (P ++ Ψ) ∋tv (length P + j)
∋tv-high⁺ []      tv = tv
∋tv-high⁺ (E ∷ P) tv = ∋tv-cons (∋tv-high⁺ P tv)

≤-split : ∀ {m n} → m ≤ n → ∃[ j ] (n ≡ m + j)
≤-split {m = zero} {n = n} z≤n = n , refl
≤-split (s≤s le) with ≤-split le
... | j , refl = j , refl

-- The combination: a type that is well formed AND names nothing in the
-- window stays well formed when the window is blocked.
Lo-blk : ∀ {Ξ A} (Q Ow : Ctxᵗ)
       → Lo (length Q) (length Ow) A
       → (Q ++ Ow ++ Ξ) ⊢ᵗ A
       → (Q ++ map blk Ow ++ Ξ) ⊢ᵗ A
Lo-blk {Ξ = Ξ} Q Ow lo (wf-var {X = X} tv) with lo
... | inj₁ le = wf-var (∋tv-low Q le tv)
... | inj₂ ge with ≤-split ge
...   | j , refl = wf-var final
  where
  t1 : (Q ++ Ow ++ Ξ) ∋tv (length Q + (length Ow + j))
  t1 = subst (λ Z → (Q ++ Ow ++ Ξ) ∋tv Z)
             (+-assoc (length Q) (length Ow) j) tv
  t2 : Ξ ∋tv j
  t2 = ∋tv-high⁻ Ow (∋tv-high⁻ Q t1)
  t3 : (map blk Ow ++ Ξ) ∋tv (length Ow + j)
  t3 = subst (λ m → (map blk Ow ++ Ξ) ∋tv (m + j))
             (map-length blk Ow) (∋tv-high⁺ (map blk Ow) t2)
  final : (Q ++ map blk Ow ++ Ξ) ∋tv (length Q + length Ow + j)
  final = subst (λ Z → (Q ++ map blk Ow ++ Ξ) ∋tv Z)
                (sym (+-assoc (length Q) (length Ow) j))
                (∋tv-high⁺ Q t3)
Lo-blk Q Ow lo wf-ℕ = wf-ℕ
Lo-blk Q Ow lo wf-𝔹 = wf-𝔹
Lo-blk Q Ow (loA , loB) (wf-⇒ wA wB) =
  wf-⇒ (Lo-blk Q Ow loA wA) (Lo-blk Q Ow loB wB)
Lo-blk Q Ow lo (wf-∀ wA) = wf-∀ (Lo-blk (abst ∷ Q) Ow lo wA)

------------------------------------------------------------------------
-- §4d  THE VERDICT
------------------------------------------------------------------------

peel-crossing-scoped : (Θ : CtxMorph) (Δ : Ctxᵗ) {Aarg Aᵈ : Ty} {s : Conv}
  → fceC Θ Δ ⊢ s ∶ liftN (nbind Θ) Aarg ⇝ Aᵈ ∙ ↑ˢ
  → intC Θ Δ ⊢ᵗ Aᵈ
    ---------------------------------------------
  → ScopedAt ↑ˢ (intC Θ Δ) (dual Θ) Aᵈ
peel-crossing-scoped Θ Δ {Aarg = Aarg} {Aᵈ = Aᵈ} ⊢s wAᵈ =
  subst (λ Ξ → Ξ ⊢ᵗ Aᵈ) scp≡intC
        (subst (λ Ξ → Ξ ⊢ᵗ Aᵈ) (sym (intC-dual Θ Δ)) step3)
  where
  Ow : Ctxᵗ
  Ow = prep (reps Θ) []

  loAᵈ : Lo 0 (nbind Θ) Aᵈ
  loAᵈ = conv-Lo-↑ (fceC-RepLo Θ Δ) ⊢s (Lo-liftN (nbind Θ) Aarg)

  loOw : Lo 0 (length Ow) Aᵈ
  loOw = subst (λ m → Lo 0 m Aᵈ) (sym (length-prep (reps Θ))) loAᵈ

  step1 : (Ow ++ scp Θ Δ) ⊢ᵗ Aᵈ
  step1 = subst (λ Ξ → Ξ ⊢ᵗ Aᵈ) (prep-++ (reps Θ) (scp Θ Δ)) wAᵈ

  step2 : (map blk Ow ++ scp Θ Δ) ⊢ᵗ Aᵈ
  step2 = Lo-blk [] Ow loOw step1

  step3 : (map blk Ow ++ fscp Θ Δ) ⊢ᵗ Aᵈ
  step3 = ⊑-wf (⊑-app (map blk Ow) (scp⊑fscp Θ Δ)) step2

  scp≡intC : intC (dual Θ) (intC Θ Δ) ≡ scp (dual Θ) (intC Θ Δ)
  scp≡intC =
    cong (λ rs → prep rs (scp (dual Θ) (intC Θ Δ))) (reps-dual Θ)

-- SO: the shape `¬Scoped-crossing` refutes cannot be reached at ↑ˢ.  A
-- crossing wrapper owes the premise only when the crossed boundary is a
-- CONCEAL, and there the crossed face's own source is a lift, which is
-- exactly what forbids the target from naming an owner.
