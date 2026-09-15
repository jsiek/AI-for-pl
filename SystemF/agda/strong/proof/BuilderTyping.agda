module strong.proof.BuilderTyping where

-- Strong System F v8 — the NORMAL-FORM BUILDER that `TyBeta` produces.
--
--   TyBeta : (Λ V) • B [ A ]  —→  ν R ∙ (V ⟨ revTy 0 (bse 0) A B ⟩)
--
-- Two things have to line up.
--
-- (1) A BASE ENTRY GAINS A REPRESENTATION.  `⊢Λ` types its body under
--     `addr ∷ Bs`; the `ν` the rule produces types it under
--     `nuBind R ∷ Bs`.  Going from `addr` to `nuBind R` only ADDS `∋r`
--     facts (the entry's own `bse zero` gains one) and changes nothing
--     else, so every judgment transports structurally.  `BaseGrow`
--     below names the relation — an entry deep in the base, so that the
--     transport can pass under `Λ` and `ν` — and the transport renames
--     nothing, which is why it is so much shorter than the base
--     RENAMING of `proof.AddrWeaken`.
--
-- (2) THE BUILDER'S TYPING.  `revTy X α S B` reveals the assignment
--     `X := α` and `concTy X α S B` conceals it, so they are typed
--     against the SAME crossing `Δ⁺ ▷ X := α ⇒ Δ⁻`, in opposite
--     directions:
--
--       Sg ∣ Δ⁺ ⊢ revTy  X α S B ∶ B            ⇝ closeAt X S B ⊣ Δ⁻
--       Sg ∣ Δ⁻ ⊢ concTy X α S B ∶ closeAt X S B ⇝ B            ⊣ Δ⁺
--
--     where `Δ⁺` is the context that HAS the assignment.  The induction
--     is on `B`: the `⇒` case dualises into `concTy`, so the two
--     lemmas are mutual, and the `∀` case descends under a `bind`,
--     raising the name, the address and the reading `S` together.
--     The MISS equations are v8's novelty — v7 crossed with a bare
--     `id`, v8 with the identity crossings `show`/`hide`, whose source
--     and target differ by `shiftAtᵗ X`; `close-shift` is the equation
--     that makes the two meet, and it is exactly where `occursᵗ X B ≡
--     false` is spent.
--
--     At `X := 0` and `α := bse zero` the target is `closeAt 0 A B ≡
--     B [ A ]ᵗ`, which is `⊢•[]`'s result type — that is `preserve-TyBeta`.

open import Data.Nat using (ℕ; zero; suc; _<_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (_≟_; _<?_; ≮⇒≥; ≤∧≢⇒<)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.Terms
open import strong.proof.AddrWeaken using
  (Renamesᵇ; ren-wk; ren-stk; read-ren; conv-base; convElt-base;
   renᴿ-comm)
open Renamesᵇ
open import strong.proof.Flat using (Flat; flat-closed)

------------------------------------------------------------------------
-- 1.  A BASE ENTRY GAINING A REPRESENTATION
------------------------------------------------------------------------

-- `BaseGrow Bs Bs′`: one `addr` entry of the base has become a
-- `nuBind R`.  The entry may sit at any depth, because the transport
-- passes under `Λ` and `ν`, each of which pushes one base entry.
data BaseGrow : List BaseEnt → List BaseEnt → Set where
  bg-here : ∀ {R Bs} → BaseGrow (addr ∷ Bs) (nuBind R ∷ Bs)
  bg-skip : ∀ {e Bs Bs′} → BaseGrow Bs Bs′ → BaseGrow (e ∷ Bs) (e ∷ Bs′)

-- An address in scope stays in scope: `addr` and `nuBind` are both
-- address binders, so only the CONSTRUCTOR of the lookup changes.
∋a-grow : ∀ {Sg Ss Bs Bs′ α} → BaseGrow Bs Bs′
  → Sg ∣ (Ss ∥ Bs) ∋a α → Sg ∣ (Ss ∥ Bs′) ∋a α
∋a-grow bg (a-lvl l) = a-lvl l
∋a-grow bg a-here-bind = a-here-bind
∋a-grow bg (a-skip-bind q) = a-skip-bind (∋a-grow bg q)
∋a-grow bg (a-skip-asgn q) = a-skip-asgn (∋a-grow bg q)
∋a-grow bg-here a-here-addr = a-here-nu
∋a-grow (bg-skip bg) a-here-addr = a-here-addr
∋a-grow (bg-skip bg) a-here-nu = a-here-nu
∋a-grow bg-here (a-skip-addr q) = a-skip-nu q
∋a-grow (bg-skip bg) (a-skip-addr q) = a-skip-addr (∋a-grow bg q)
∋a-grow (bg-skip bg) (a-skip-nu q) = a-skip-nu (∋a-grow bg q)

-- A represented address keeps its representation.  The grown entry's
-- own `bse zero` GAINS a lookup (`r-here`), which no premise can miss:
-- `∋r` occurs only positively.
∋r-grow : ∀ {Sg Ss Bs Bs′ α T} → BaseGrow Bs Bs′
  → Sg ∣ (Ss ∥ Bs) ∋r α := T → Sg ∣ (Ss ∥ Bs′) ∋r α := T
∋r-grow bg (r-lvl l) = r-lvl l
∋r-grow bg (r-skip-bind q) = r-skip-bind (∋r-grow bg q)
∋r-grow bg (r-skip-asgn q) = r-skip-asgn (∋r-grow bg q)
∋r-grow (bg-skip bg) r-here = r-here
∋r-grow bg-here (r-skip-addr q) = r-skip-nu q
∋r-grow (bg-skip bg) (r-skip-addr q) = r-skip-addr (∋r-grow bg q)
∋r-grow (bg-skip bg) (r-skip-nu q) = r-skip-nu (∋r-grow bg q)

wfᴿ-grow : ∀ {Sg Ss Bs Bs′ T} → BaseGrow Bs Bs′
  → Sg ∣ (Ss ∥ Bs) ⊢ᴿ T → Sg ∣ (Ss ∥ Bs′) ⊢ᴿ T
wfᴿ-grow bg (wfᴿ-var a) = wfᴿ-var (∋a-grow bg a)
wfᴿ-grow bg wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-grow bg wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-grow bg (wfᴿ-⇒ a b) = wfᴿ-⇒ (wfᴿ-grow bg a) (wfᴿ-grow bg b)
wfᴿ-grow bg (wfᴿ-∀ a) = wfᴿ-∀ (wfᴿ-grow bg a)

-- The read-back, the pop judgment and the freshness condition see the
-- STACK alone, so they do not even mention the growth.
read-rebase : ∀ {Sg Ss Bs Bs′ T A}
  → Sg ∣ (Ss ∥ Bs) ⊢ T ⇓ A → Sg ∣ (Ss ∥ Bs′) ⊢ T ⇓ A
read-rebase (read-var n) = read-var (∋n-rebase n)
read-rebase read-ℕ = read-ℕ
read-rebase read-𝔹 = read-𝔹
read-rebase (read-⇒ a b) = read-⇒ (read-rebase a) (read-rebase b)
read-rebase (read-∀ a) = read-∀ (read-rebase a)

pop-rebase : ∀ {Ss Ss′ Bs Bs′ X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → (Ss ∥ Bs′) ▷ X := α ⇒ (Ss′ ∥ Bs′)
pop-rebase pop-here = pop-here
pop-rebase (pop-bind-b q) = pop-bind-b (pop-rebase q)
pop-rebase (pop-bind-l q) = pop-bind-l (pop-rebase q)
pop-rebase (pop-bind-e q) = pop-bind-e (pop-rebase q)

notasgn-rebase : ∀ {Ss Bs Bs′ α}
  → NotAssigned (Ss ∥ Bs) α → NotAssigned (Ss ∥ Bs′) α
notasgn-rebase na q = na (∋n-rebase q)

mutual
  convElt-grow : ∀ {Sg Ssᵢ Ssₑ Bs Bs′ ĉ A B} → BaseGrow Bs Bs′
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Sg ∣ (Ssᵢ ∥ Bs′) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs′)
  convElt-grow bg (conv-seal rep rd q) =
    conv-seal (∋r-grow bg rep) (read-rebase rd) (pop-rebase q)
  convElt-grow bg (conv-unseal rep rd q na) =
    conv-unseal (∋r-grow bg rep) (read-rebase rd) (pop-rebase q)
                (notasgn-rebase na)
  convElt-grow bg (conv-hide wf q na) =
    conv-hide (wf-rebase wf) (pop-rebase q) (notasgn-rebase na)
  convElt-grow bg (conv-show wf q na) =
    conv-show (wf-rebase wf) (pop-rebase q) (notasgn-rebase na)
  convElt-grow bg (conv-fun s t) = conv-fun (conv-grow bg s) (conv-grow bg t)
  convElt-grow bg (conv-all s) = conv-all (conv-grow bg s)

  conv-grow : ∀ {Sg Ssᵢ Ssₑ Bs Bs′ c A B} → BaseGrow Bs Bs′
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Sg ∣ (Ssᵢ ∥ Bs′) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs′)
  conv-grow bg (conv-id wf) = conv-id (wf-rebase wf)
  conv-grow bg (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) with convElt-base hd
  conv-grow bg (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl =
    conv-cons (convElt-grow bg hd) (conv-grow bg tl)

-- `Λ` and `ν` are the base's binders, so they are where the growth
-- descends; every other rule reads the stack alone.
⊢-grow : ∀ {Sg Ss Bs Bs′ Γ M A} → BaseGrow Bs Bs′
  → Sg ∣ (Ss ∥ Bs) ∣ Γ ⊢ M ⦂ A → Sg ∣ (Ss ∥ Bs′) ∣ Γ ⊢ M ⦂ A
⊢-grow bg (⊢` x) = ⊢` x
⊢-grow bg ⊢$ = ⊢$
⊢-grow bg ⊢# = ⊢#
⊢-grow bg (⊢⊕ m n) = ⊢⊕ (⊢-grow bg m) (⊢-grow bg n)
⊢-grow bg (⊢ƛ wf n) = ⊢ƛ (wf-rebase wf) (⊢-grow bg n)
⊢-grow bg (⊢· l m) = ⊢· (⊢-grow bg l) (⊢-grow bg m)
⊢-grow bg (⊢Λ v ⊢V) = ⊢Λ v (⊢-grow (bg-skip bg) ⊢V)
⊢-grow bg (⊢•[] l wf) = ⊢•[] (⊢-grow bg l) (wf-rebase wf)
⊢-grow bg (⊢ν wf ⊢M) = ⊢ν (wfᴿ-grow bg wf) (⊢-grow (bg-skip bg) ⊢M)
⊢-grow bg (⊢⟨⟩ {Δᵢ = Ssᵢ ∥ Bsᵢ} nf ⊢M ⊢c) with conv-base ⊢c
⊢-grow bg (⊢⟨⟩ {Δᵢ = Ssᵢ ∥ Bsᵢ} nf ⊢M ⊢c) | refl =
  ⊢⟨⟩ nf (⊢-grow bg ⊢M) (conv-grow bg ⊢c)

------------------------------------------------------------------------
-- 2.  THE INDEX ARITHMETIC OF `closeAt`
------------------------------------------------------------------------
-- `closeEnv` decides with `_≟_` and `_<?_`; `closeIdx` is the same
-- function on the `X ≢ Y` branch, structurally, and is what the typing
-- proofs case on.

infix 4 _≢ᴺ_
_≢ᴺ_ : ℕ → ℕ → Set
X ≢ᴺ Y = ¬ (X ≡ Y)

closeIdx : ℕ → ℕ → ℕ
closeIdx zero    zero    = zero
closeIdx zero    (suc Y) = Y
closeIdx (suc X) zero    = zero
closeIdx (suc X) (suc Y) = suc (closeIdx X Y)

closeIdx-gt : ∀ X Y → X < Y → closeIdx X Y ≡ Y ∸ 1
closeIdx-gt zero (suc Y) lt = refl
closeIdx-gt (suc X) (suc (suc Y)) (s≤s lt) =
  cong suc (closeIdx-gt X (suc Y) lt)

closeIdx-lt : ∀ X Y → Y < X → closeIdx X Y ≡ Y
closeIdx-lt (suc X) zero lt = refl
closeIdx-lt (suc X) (suc Y) (s≤s lt) = cong suc (closeIdx-lt X Y lt)

closeEnv-hit : ∀ X S → closeEnv X S X ≡ S
closeEnv-hit X S with X ≟ X
closeEnv-hit X S | yes _ = refl
closeEnv-hit X S | no ne = ⊥-elim (ne refl)

closeEnv-miss : ∀ X S Y → X ≢ᴺ Y → closeEnv X S Y ≡ ` (closeIdx X Y)
closeEnv-miss X S Y ne with X ≟ Y
closeEnv-miss X S Y ne | yes eq = ⊥-elim (ne eq)
closeEnv-miss X S Y ne | no _ with X <? Y
closeEnv-miss X S Y ne | no _ | yes lt = cong `_ (sym (closeIdx-gt X Y lt))
closeEnv-miss X S Y ne | no _ | no ¬lt =
  cong `_ (sym (closeIdx-lt X Y (≤∧≢⇒< (≮⇒≥ ¬lt) (λ eq → ne (sym eq)))))

-- Going under a binder.  The decision is taken OUTSIDE the goal: a
-- `with` here would abstract `closeEnv`'s own internal `with`, and
-- `closeEnv-miss` would no longer apply to the abstracted form.
closeEnv-ext : ∀ X S Y → extsᵗ (closeEnv X S) Y ≡ closeEnv (suc X) (⇑ᵗ S) Y
closeEnv-ext X S zero = sym (closeEnv-miss (suc X) (⇑ᵗ S) zero (λ ()))
closeEnv-ext X S (suc Y) = go (X ≟ Y)
  where
  go : Dec (X ≡ Y)
     → extsᵗ (closeEnv X S) (suc Y) ≡ closeEnv (suc X) (⇑ᵗ S) (suc Y)
  go (yes refl) =
    trans (cong ⇑ᵗ (closeEnv-hit X S)) (sym (closeEnv-hit (suc X) (⇑ᵗ S)))
  go (no ne) =
    trans (cong ⇑ᵗ (closeEnv-miss X S Y ne))
          (sym (closeEnv-miss (suc X) (⇑ᵗ S) (suc Y) (λ { refl → ne refl })))

closeAt-∀ : ∀ X S A → closeAt X S (`∀ A) ≡ `∀ (closeAt (suc X) (⇑ᵗ S) A)
closeAt-∀ X S A = cong `∀ (substᵗ-cong (closeEnv-ext X S) A)

closeAt-hit : ∀ X S → closeAt X S (` X) ≡ S
closeAt-hit = closeEnv-hit

closeAt-miss : ∀ X S Y → X ≢ᴺ Y → closeAt X S (` Y) ≡ ` (closeIdx X Y)
closeAt-miss = closeEnv-miss

-- `closeAt zero` IS the type-level action of a type application: the
-- builder's target at the outermost name is `⊢•[]`'s result type.
closeEnv-single : ∀ S Y → closeEnv zero S Y ≡ singleTyEnv S Y
closeEnv-single S zero = closeEnv-hit zero S
closeEnv-single S (suc Y) = closeEnv-miss zero S (suc Y) (λ ())

closeAt-single : ∀ S A → closeAt zero S A ≡ A [ S ]ᵗ
closeAt-single S A = substᵗ-cong (closeEnv-single S) A

------------------------------------------------------------------------
-- The MISS equation: an identity crossing's two types
------------------------------------------------------------------------
-- `show`/`hide` relate `A` and `renameᵗ (shiftAtᵗ X) A`.  When X does
-- not occur, closing at X and shifting back at X is the identity — and
-- that is the whole content of the miss branches.

true≢false : true ≡ false → ⊥
true≢false ()

∨-false-l : ∀ {a b} → a ∨ b ≡ false → a ≡ false
∨-false-l {false} {b} eq = refl
∨-false-l {true} {b} ()

∨-false-r : ∀ {a b} → a ∨ b ≡ false → b ≡ false
∨-false-r {false} {b} eq = eq
∨-false-r {true} {b} ()

occurs-var-yes : ∀ X → occursᵗ X (` X) ≡ true
occurs-var-yes X with X ≟ X
occurs-var-yes X | yes _ = refl
occurs-var-yes X | no ne = ⊥-elim (ne refl)

occurs-var-no : ∀ X Y → X ≢ᴺ Y → occursᵗ X (` Y) ≡ false
occurs-var-no X Y ne with X ≟ Y
occurs-var-no X Y ne | yes eq = ⊥-elim (ne eq)
occurs-var-no X Y ne | no _ = refl

occurs-var-≢ : ∀ X Y → occursᵗ X (` Y) ≡ false → X ≢ᴺ Y
occurs-var-≢ X Y eq refl = true≢false (trans (sym (occurs-var-yes X)) eq)

shiftAt-closeIdx : ∀ X Y → X ≢ᴺ Y → shiftAtᵗ X (closeIdx X Y) ≡ Y
shiftAt-closeIdx zero zero ne = ⊥-elim (ne refl)
shiftAt-closeIdx zero (suc Y) ne = refl
shiftAt-closeIdx (suc X) zero ne = refl
shiftAt-closeIdx (suc X) (suc Y) ne =
  cong suc (shiftAt-closeIdx X Y (λ eq → ne (cong suc eq)))

close-shift : ∀ X S B → occursᵗ X B ≡ false
  → renameᵗ (shiftAtᵗ X) (closeAt X S B) ≡ B
close-shift X S (` Y) eq
  rewrite closeAt-miss X S Y (occurs-var-≢ X Y eq) =
  cong `_ (shiftAt-closeIdx X Y (occurs-var-≢ X Y eq))
close-shift X S `ℕ eq = refl
close-shift X S `𝔹 eq = refl
close-shift X S (A ⇒ B) eq =
  cong₂ _⇒_ (close-shift X S A (∨-false-l eq))
            (close-shift X S B (∨-false-r eq))
close-shift X S (`∀ A) eq =
  trans (cong (renameᵗ (shiftAtᵗ X)) (closeAt-∀ X S A))
        (cong `∀ (close-shift (suc X) (⇑ᵗ S) A eq))

------------------------------------------------------------------------
-- 3.  THE CROSSING'S CONTEXT ALGEBRA
------------------------------------------------------------------------
-- Everything the builders need in order to descend under a `bind`: the
-- pop, the freshness, the representation, the reading and the
-- well-formedness all rise together, the name by `suc` and the address
-- by `⇑ᵃ`.

pop-∋n : ∀ {Γ Γ′ X α} → Γ ▷ X := α ⇒ Γ′ → Γ ∋n X := α
pop-∋n pop-here = n-here-asgn
pop-∋n (pop-bind-b q) = n-skip-bind-b (pop-∋n q)
pop-∋n (pop-bind-l q) = n-skip-bind-l (pop-∋n q)
pop-∋n (pop-bind-e q) = n-skip-bind-e (pop-∋n q)

pop-⇑ : ∀ {Ss Ss′ Bs X α} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → (bind ∷ Ss ∥ Bs) ▷ suc X := ⇑ᵃ α ⇒ (bind ∷ Ss′ ∥ Bs)
pop-⇑ {α = lvl ℓ} q = pop-bind-l q
pop-⇑ {α = bnd i} q = pop-bind-b q
pop-⇑ {α = bse j} q = pop-bind-e q

-- The name lookups rise by (suc , ⇑ᵃ): the binder is a name entry AND
-- an address binder, so both indices move.
∋n-⇑ : ∀ {Ss Bs X α} → (Ss ∥ Bs) ∋n X := α
  → (bind ∷ Ss ∥ Bs) ∋n suc X := ⇑ᵃ α
∋n-⇑ {α = lvl ℓ} q = n-skip-bind-l q
∋n-⇑ {α = bnd i} q = n-skip-bind-b q
∋n-⇑ {α = bse j} q = n-skip-bind-e q

notasgn-⇑ : ∀ {Ss Bs α} → NotAssigned (Ss ∥ Bs) α
  → NotAssigned (bind ∷ Ss ∥ Bs) (⇑ᵃ α)
notasgn-⇑ {α = lvl ℓ} na (n-skip-bind-l q) = na q
notasgn-⇑ {α = bnd i} na (n-skip-bind-b q) = na q
notasgn-⇑ {α = bse j} na (n-skip-bind-e q) = na q

-- The representation does NOT move, provided it is closed for the
-- stack — which is what `StoreOk` and `Flat` deliver at the redex.
∋r-⇑ : ∀ {Sg Ss Bs α R} → (∀ η → renameᴿ η R ≡ R)
  → Sg ∣ (Ss ∥ Bs) ∋r α := R → Sg ∣ (bind ∷ Ss ∥ Bs) ∋r ⇑ᵃ α := R
∋r-⇑ fix (r-lvl l) = r-lvl l
∋r-⇑ fix h@r-here = ∋r-restk h
∋r-⇑ fix h@(r-skip-addr q) = ∋r-restk h
∋r-⇑ fix h@(r-skip-nu q) = ∋r-restk h
∋r-⇑ {Sg} {Ss} {Bs} {α} {R} fix (r-skip-bind q) =
  subst (λ T → Sg ∣ (bind ∷ Ss ∥ Bs) ∋r ⇑ᵃ α := T) (fix suc)
        (r-skip-bind (r-skip-bind q))
∋r-⇑ {Sg} {Ss} {Bs} {α} {R} fix (r-skip-asgn q) =
  subst (λ T → Sg ∣ (bind ∷ Ss ∥ Bs) ∋r ⇑ᵃ α := T) (fix suc)
        (r-skip-bind (r-skip-asgn q))

-- The name-renaming algebra the read-back travels along: names by `ρ`,
-- addresses by the STACK renaming `η`, both extending under a `bind`.
Ren∋ : Renameᵗ → Renameᵇ → Ctxᵗ → Ctxᵗ → Set
Ren∋ ρ η Γ Γ′ = ∀ {X α} → Γ ∋n X := α → Γ′ ∋n ρ X := renᵃ η α

ren∋-ext : ∀ {ρ η Γ Γ′} → Ren∋ ρ η Γ Γ′
  → Ren∋ (extᵗ ρ) (extᵇ η) (bind ∷ stk Γ ∥ bas Γ) (bind ∷ stk Γ′ ∥ bas Γ′)
ren∋-ext r n-here-bind = n-here-bind
ren∋-ext r (n-skip-bind-b q) = n-skip-bind-b (r q)
ren∋-ext r (n-skip-bind-l q) = n-skip-bind-l (r q)
ren∋-ext r (n-skip-bind-e q) = n-skip-bind-e (r q)

read-ren∋ : ∀ {Sg ρ η Γ Γ′ T A} → Ren∋ ρ η Γ Γ′
  → Sg ∣ Γ ⊢ T ⇓ A → Sg ∣ Γ′ ⊢ renameᴿ η T ⇓ renameᵗ ρ A
read-ren∋ r (read-var n) = read-var (r n)
read-ren∋ r read-ℕ = read-ℕ
read-ren∋ r read-𝔹 = read-𝔹
read-ren∋ r (read-⇒ a b) = read-⇒ (read-ren∋ r a) (read-ren∋ r b)
read-ren∋ r (read-∀ a) = read-∀ (read-ren∋ (ren∋-ext r) a)

wf-renN : ∀ {ρ η Γ Γ′ A} → Ren∋ ρ η Γ Γ′ → Γ ⊢ᵗ A → Γ′ ⊢ᵗ renameᵗ ρ A
wf-renN r (wf-var n) = wf-var (r n)
wf-renN r wf-ℕ = wf-ℕ
wf-renN r wf-𝔹 = wf-𝔹
wf-renN r (wf-⇒ a b) = wf-⇒ (wf-renN r a) (wf-renN r b)
wf-renN r (wf-∀ a) = wf-∀ (wf-renN (ren∋-ext r) a)

wf-⇑ : ∀ {Ss Bs A} → (Ss ∥ Bs) ⊢ᵗ A → (bind ∷ Ss ∥ Bs) ⊢ᵗ ⇑ᵗ A
wf-⇑ = wf-renN ∋n-⇑

rd-⇑ : ∀ {Sg Ss Bs R S} → (∀ η → renameᴿ η R ≡ R)
  → Sg ∣ (Ss ∥ Bs) ⊢ R ⇓ S → Sg ∣ (bind ∷ Ss ∥ Bs) ⊢ R ⇓ ⇑ᵗ S
rd-⇑ {Sg} {Ss} {Bs} {R} {S} fix rd =
  subst (λ T → Sg ∣ (bind ∷ Ss ∥ Bs) ⊢ T ⇓ ⇑ᵗ S) (fix suc)
        (read-ren∋ ∋n-⇑ rd)

read-wf : ∀ {Sg Γ T A} → Sg ∣ Γ ⊢ T ⇓ A → Γ ⊢ᵗ A
read-wf (read-var n) = wf-var n
read-wf read-ℕ = wf-ℕ
read-wf read-𝔹 = wf-𝔹
read-wf (read-⇒ a b) = wf-⇒ (read-wf a) (read-wf b)
read-wf (read-∀ a) = wf-∀ (read-wf a)

wf-domain : ∀ {Γ A B} → Γ ⊢ᵗ A ⇒ B → Γ ⊢ᵗ A
wf-domain (wf-⇒ a b) = a

wf-codomain : ∀ {Γ A B} → Γ ⊢ᵗ A ⇒ B → Γ ⊢ᵗ B
wf-codomain (wf-⇒ a b) = b

wf-∀-inv : ∀ {Ss Bs A} → (Ss ∥ Bs) ⊢ᵗ `∀ A → (bind ∷ Ss ∥ Bs) ⊢ᵗ A
wf-∀-inv (wf-∀ a) = a

------------------------------------------------------------------------
-- Closing a well-formed type across the crossing
------------------------------------------------------------------------
-- Every name OTHER than the crossed one survives the pop, its index
-- closing up over the slot that leaves.  Only the EXISTENCE of the
-- surviving name matters, so the address it lands on is existential.

∋n-close : ∀ {Ss Ss′ Bs X α Y β} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → X ≢ᴺ Y → (Ss ∥ Bs) ∋n Y := β
  → Σ[ γ ∈ Addr ] ((Ss′ ∥ Bs) ∋n closeIdx X Y := γ)
∋n-close pop-here ne n-here-asgn = ⊥-elim (ne refl)
∋n-close pop-here ne (n-skip-asgn q) = _ , q
∋n-close (pop-bind-b p) ne n-here-bind = _ , n-here-bind
∋n-close (pop-bind-l p) ne n-here-bind = _ , n-here-bind
∋n-close (pop-bind-e p) ne n-here-bind = _ , n-here-bind
∋n-close (pop-bind-b p) ne (n-skip-bind-b q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-b p) ne (n-skip-bind-b q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-b p) ne (n-skip-bind-l q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-b p) ne (n-skip-bind-l q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-b p) ne (n-skip-bind-e q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-b p) ne (n-skip-bind-e q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-l p) ne (n-skip-bind-b q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-l p) ne (n-skip-bind-b q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-l p) ne (n-skip-bind-l q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-l p) ne (n-skip-bind-l q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-l p) ne (n-skip-bind-e q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-l p) ne (n-skip-bind-e q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-e p) ne (n-skip-bind-b q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-e p) ne (n-skip-bind-b q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-e p) ne (n-skip-bind-l q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-e p) ne (n-skip-bind-l q) | γ , r = _ , ∋n-⇑ r
∋n-close (pop-bind-e p) ne (n-skip-bind-e q)
  with ∋n-close p (λ e → ne (cong suc e)) q
∋n-close (pop-bind-e p) ne (n-skip-bind-e q) | γ , r = _ , ∋n-⇑ r

closeAt-wf : ∀ {Ssᵢ Ssₑ Bs X α S B} → (Ssᵢ ∥ Bs) ▷ X := α ⇒ (Ssₑ ∥ Bs)
  → (Ssₑ ∥ Bs) ⊢ᵗ S → (Ssᵢ ∥ Bs) ⊢ᵗ B → (Ssₑ ∥ Bs) ⊢ᵗ closeAt X S B
closeAt-wf {Ssᵢ} {Ssₑ} {Bs} {X} {α} {S} p wfS (wf-var {X = Y} n) = go (X ≟ Y)
  where
  go : Dec (X ≡ Y) → (Ssₑ ∥ Bs) ⊢ᵗ closeAt X S (` Y)
  go (yes refl) rewrite closeAt-hit X S = wfS
  go (no ne) with ∋n-close p ne n
  go (no ne) | γ , q rewrite closeAt-miss X S Y ne = wf-var q
closeAt-wf p wfS wf-ℕ = wf-ℕ
closeAt-wf p wfS wf-𝔹 = wf-𝔹
closeAt-wf p wfS (wf-⇒ a b) =
  wf-⇒ (closeAt-wf p wfS a) (closeAt-wf p wfS b)
closeAt-wf {X = X} {S = S} p wfS (wf-∀ {A = A} a)
  rewrite closeAt-∀ X S A =
  wf-∀ (closeAt-wf (pop-⇑ p) (wf-⇑ wfS) a)

------------------------------------------------------------------------
-- 4.  THE BUILDERS, EQUATION BY EQUATION
------------------------------------------------------------------------
-- The decisions are read off OUTSIDE the goal: a bare `with` on
-- `X ≟ Y` or on `occursᵗ X B` abstracts the builder's own internal
-- `with`, and the `closeAt` lemmas would no longer apply to the
-- abstracted form.  These equations are what the typing proofs
-- `rewrite` by.

revTy-var-hit : ∀ X α S → revTy X α S (` X) ≡ unseal X α ∷ᶜ id S
revTy-var-hit X α S with X ≟ X
revTy-var-hit X α S | yes _ = refl
revTy-var-hit X α S | no ne = ⊥-elim (ne refl)

-- The `closeAt` in the miss clause carries its OWN `X ≟ Y`, which the
-- proof's `with` cannot reach (it lies under the builder's own with-
-- function).  So the equation is stated at `closeIdx` — which decides
-- nothing — and put back into `closeAt` form afterwards.
revTy-var-miss-idx : ∀ X α S Y → X ≢ᴺ Y
  → revTy X α S (` Y) ≡ show X α ∷ᶜ id (` (closeIdx X Y))
revTy-var-miss-idx X α S Y ne with X ≟ Y
revTy-var-miss-idx X α S Y ne | yes eq = ⊥-elim (ne eq)
revTy-var-miss-idx X α S Y ne | no _ =
  cong (λ T → show X α ∷ᶜ id T) (closeEnv-miss X S Y ne)

revTy-var-miss : ∀ X α S Y → X ≢ᴺ Y
  → revTy X α S (` Y) ≡ show X α ∷ᶜ id (closeAt X S (` Y))
revTy-var-miss X α S Y ne =
  trans (revTy-var-miss-idx X α S Y ne)
        (cong (λ T → show X α ∷ᶜ id T) (sym (closeAt-miss X S Y ne)))

revTy-⇒-miss : ∀ X α S A B → occursᵗ X (A ⇒ B) ≡ false
  → revTy X α S (A ⇒ B) ≡ show X α ∷ᶜ id (closeAt X S (A ⇒ B))
revTy-⇒-miss X α S A B eq rewrite eq = refl

revTy-⇒-hit : ∀ X α S A B → occursᵗ X (A ⇒ B) ≡ true
  → revTy X α S (A ⇒ B)
      ≡ (concTy X α S A ↦ revTy X α S B) ∷ᶜ id (closeAt X S (A ⇒ B))
revTy-⇒-hit X α S A B eq rewrite eq = refl

revTy-∀-miss : ∀ X α S A → occursᵗ (suc X) A ≡ false
  → revTy X α S (`∀ A) ≡ show X α ∷ᶜ id (closeAt X S (`∀ A))
revTy-∀-miss X α S A eq rewrite eq = refl

revTy-∀-hit : ∀ X α S A → occursᵗ (suc X) A ≡ true
  → revTy X α S (`∀ A)
      ≡ all (revTy (suc X) (⇑ᵃ α) (⇑ᵗ S) A) ∷ᶜ id (closeAt X S (`∀ A))
revTy-∀-hit X α S A eq rewrite eq = refl

concTy-var-hit : ∀ X α S → concTy X α S (` X) ≡ seal X α ∷ᶜ id (` X)
concTy-var-hit X α S with X ≟ X
concTy-var-hit X α S | yes _ = refl
concTy-var-hit X α S | no ne = ⊥-elim (ne refl)

concTy-var-miss : ∀ X α S Y → X ≢ᴺ Y
  → concTy X α S (` Y) ≡ hide X α ∷ᶜ id (` Y)
concTy-var-miss X α S Y ne with X ≟ Y
concTy-var-miss X α S Y ne | yes eq = ⊥-elim (ne eq)
concTy-var-miss X α S Y ne | no _ = refl

concTy-⇒-miss : ∀ X α S A B → occursᵗ X (A ⇒ B) ≡ false
  → concTy X α S (A ⇒ B) ≡ hide X α ∷ᶜ id (A ⇒ B)
concTy-⇒-miss X α S A B eq rewrite eq = refl

concTy-⇒-hit : ∀ X α S A B → occursᵗ X (A ⇒ B) ≡ true
  → concTy X α S (A ⇒ B)
      ≡ (revTy X α S A ↦ concTy X α S B) ∷ᶜ id (A ⇒ B)
concTy-⇒-hit X α S A B eq rewrite eq = refl

concTy-∀-miss : ∀ X α S A → occursᵗ (suc X) A ≡ false
  → concTy X α S (`∀ A) ≡ hide X α ∷ᶜ id (`∀ A)
concTy-∀-miss X α S A eq rewrite eq = refl

concTy-∀-hit : ∀ X α S A → occursᵗ (suc X) A ≡ true
  → concTy X α S (`∀ A)
      ≡ all (concTy (suc X) (⇑ᵃ α) (⇑ᵗ S) A) ∷ᶜ id (`∀ A)
concTy-∀-hit X α S A eq rewrite eq = refl

------------------------------------------------------------------------
-- 5.  THE BUILDERS ARE IN NORMAL FORM
------------------------------------------------------------------------
-- Every equation is one element on a terminator, so `irr-id` discharges
-- irreducibility everywhere and only the element needs a witness.

mutual
  revTy-NF : ∀ X α S B → NF (revTy X α S B)
  revTy-NF X α S (` Y) with X ≟ Y
  revTy-NF X α S (` Y) | yes _ = nf-cons nf-unseal nf-id irr-id
  revTy-NF X α S (` Y) | no _ = nf-cons nf-show nf-id irr-id
  revTy-NF X α S `ℕ = nf-cons nf-show nf-id irr-id
  revTy-NF X α S `𝔹 = nf-cons nf-show nf-id irr-id
  revTy-NF X α S (A ⇒ B) with occursᵗ X (A ⇒ B)
  revTy-NF X α S (A ⇒ B) | false = nf-cons nf-show nf-id irr-id
  revTy-NF X α S (A ⇒ B) | true =
    nf-cons (nf-fun (concTy-NF X α S A) (revTy-NF X α S B)) nf-id irr-id
  revTy-NF X α S (`∀ A) with occursᵗ (suc X) A
  revTy-NF X α S (`∀ A) | false = nf-cons nf-show nf-id irr-id
  revTy-NF X α S (`∀ A) | true =
    nf-cons (nf-all (revTy-NF (suc X) (⇑ᵃ α) (⇑ᵗ S) A)) nf-id irr-id

  concTy-NF : ∀ X α S B → NF (concTy X α S B)
  concTy-NF X α S (` Y) with X ≟ Y
  concTy-NF X α S (` Y) | yes _ = nf-cons nf-seal nf-id irr-id
  concTy-NF X α S (` Y) | no _ = nf-cons nf-hide nf-id irr-id
  concTy-NF X α S `ℕ = nf-cons nf-hide nf-id irr-id
  concTy-NF X α S `𝔹 = nf-cons nf-hide nf-id irr-id
  concTy-NF X α S (A ⇒ B) with occursᵗ X (A ⇒ B)
  concTy-NF X α S (A ⇒ B) | false = nf-cons nf-hide nf-id irr-id
  concTy-NF X α S (A ⇒ B) | true =
    nf-cons (nf-fun (revTy-NF X α S A) (concTy-NF X α S B)) nf-id irr-id
  concTy-NF X α S (`∀ A) with occursᵗ (suc X) A
  concTy-NF X α S (`∀ A) | false = nf-cons nf-hide nf-id irr-id
  concTy-NF X α S (`∀ A) | true =
    nf-cons (nf-all (concTy-NF (suc X) (⇑ᵃ α) (⇑ᵗ S) A)) nf-id irr-id

------------------------------------------------------------------------
-- 6.  THE BUILDER TYPING
------------------------------------------------------------------------
-- The two MISS shapes, once and for all.  `close-shift` is what makes
-- the identity crossing's two types meet: `show`/`hide` relate `C` and
-- `renameᵗ (shiftAtᵗ X) C`, and at `C = closeAt X S B` with X absent
-- from B that shift is B itself.

revTy-miss-typing : ∀ {Sg Ssᵢ Ssₑ Bs X α} (S B : Ty)
  → (Ssᵢ ∥ Bs) ▷ X := α ⇒ (Ssₑ ∥ Bs)
  → NotAssigned (Ssₑ ∥ Bs) α
  → occursᵗ X B ≡ false
  → (Ssₑ ∥ Bs) ⊢ᵗ closeAt X S B
  → Sg ∣ (Ssᵢ ∥ Bs) ⊢ show X α ∷ᶜ id (closeAt X S B) ∶ B ⇝ closeAt X S B
      ⊣ (Ssₑ ∥ Bs)
revTy-miss-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} {X} {α} S B p na eq wfC =
  subst (λ C → Sg ∣ (Ssᵢ ∥ Bs) ⊢ show X α ∷ᶜ id (closeAt X S B)
                  ∶ C ⇝ closeAt X S B ⊣ (Ssₑ ∥ Bs))
        (close-shift X S B eq)
        (conv-cons (conv-show wfC p na) (conv-id wfC))

concTy-miss-typing : ∀ {Sg Ssᵢ Ssₑ Bs X α} (S B : Ty)
  → (Ssᵢ ∥ Bs) ▷ X := α ⇒ (Ssₑ ∥ Bs)
  → NotAssigned (Ssₑ ∥ Bs) α
  → occursᵗ X B ≡ false
  → (Ssₑ ∥ Bs) ⊢ᵗ closeAt X S B
  → (Ssᵢ ∥ Bs) ⊢ᵗ B
  → Sg ∣ (Ssₑ ∥ Bs) ⊢ hide X α ∷ᶜ id B ∶ closeAt X S B ⇝ B ⊣ (Ssᵢ ∥ Bs)
concTy-miss-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} {X} {α} S B p na eq wfC wfB =
  conv-cons
    (subst (λ C → Sg ∣ (Ssₑ ∥ Bs) ⊢̂ hide X α ∶ closeAt X S B ⇝ C
                     ⊣ (Ssᵢ ∥ Bs))
           (close-shift X S B eq)
           (conv-hide wfC p na))
    (conv-id wfB)

-- THE STATEMENT.  `Δ⁺ = Ssᵢ ∥ Bs` is the context that HAS the
-- assignment `X := α`; `Δ⁻ = Ssₑ ∥ Bs` is the one without.  `R` is α's
-- representation, `S` its read-back on the unassigned side, and `fix`
-- says `R` mentions no bound STACK address — which is what lets the
-- `∀` case descend under a `bind` without shifting it.
mutual
  revTy-typing : ∀ {Sg Ssᵢ Ssₑ Bs R} (X : ℕ) (α : Addr) (S B : Ty)
    → (Ssᵢ ∥ Bs) ▷ X := α ⇒ (Ssₑ ∥ Bs)
    → NotAssigned (Ssₑ ∥ Bs) α
    → Sg ∣ (Ssᵢ ∥ Bs) ∋r α := R
    → Sg ∣ (Ssₑ ∥ Bs) ⊢ R ⇓ S
    → (∀ η → renameᴿ η R ≡ R)
    → (Ssᵢ ∥ Bs) ⊢ᵗ B
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢ revTy X α S B ∶ B ⇝ closeAt X S B ⊣ (Ssₑ ∥ Bs)

  revTy-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} X α S (` Y) p na rep rd fix wf =
    go (X ≟ Y)
    where
    go : Dec (X ≡ Y)
       → Sg ∣ (Ssᵢ ∥ Bs) ⊢ revTy X α S (` Y) ∶ ` Y ⇝ closeAt X S (` Y)
           ⊣ (Ssₑ ∥ Bs)
    go (yes refl) rewrite revTy-var-hit X α S | closeAt-hit X S =
      conv-cons (conv-unseal rep rd p na) (conv-id (read-wf rd))
    go (no ne) rewrite revTy-var-miss X α S Y ne =
      revTy-miss-typing S (` Y) p na (occurs-var-no X Y ne)
        (closeAt-wf p (read-wf rd) wf)

  revTy-typing X α S `ℕ p na rep rd fix wf =
    revTy-miss-typing S `ℕ p na refl wf-ℕ

  revTy-typing X α S `𝔹 p na rep rd fix wf =
    revTy-miss-typing S `𝔹 p na refl wf-𝔹

  revTy-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} X α S (A ⇒ B) p na rep rd fix wf =
    go (occursᵗ X (A ⇒ B)) refl
    where
    go : (b : Bool) → occursᵗ X (A ⇒ B) ≡ b
       → Sg ∣ (Ssᵢ ∥ Bs) ⊢ revTy X α S (A ⇒ B) ∶ (A ⇒ B)
           ⇝ closeAt X S (A ⇒ B) ⊣ (Ssₑ ∥ Bs)
    go false eq rewrite revTy-⇒-miss X α S A B eq =
      revTy-miss-typing S (A ⇒ B) p na eq (closeAt-wf p (read-wf rd) wf)
    go true eq rewrite revTy-⇒-hit X α S A B eq =
      conv-cons
        (conv-fun (concTy-typing X α S A p na rep rd fix (wf-domain wf))
                  (revTy-typing X α S B p na rep rd fix (wf-codomain wf)))
        (conv-id (closeAt-wf p (read-wf rd) wf))

  revTy-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} X α S (`∀ A) p na rep rd fix wf =
    go (occursᵗ (suc X) A) refl
    where
    go : (b : Bool) → occursᵗ (suc X) A ≡ b
       → Sg ∣ (Ssᵢ ∥ Bs) ⊢ revTy X α S (`∀ A) ∶ (`∀ A)
           ⇝ closeAt X S (`∀ A) ⊣ (Ssₑ ∥ Bs)
    go false eq rewrite revTy-∀-miss X α S A eq =
      revTy-miss-typing S (`∀ A) p na eq (closeAt-wf p (read-wf rd) wf)
    go true eq rewrite revTy-∀-hit X α S A eq =
      subst (λ C → Sg ∣ (Ssᵢ ∥ Bs)
                      ⊢ all (revTy (suc X) (⇑ᵃ α) (⇑ᵗ S) A) ∷ᶜ id C
                      ∶ (`∀ A) ⇝ C ⊣ (Ssₑ ∥ Bs))
            (sym (closeAt-∀ X S A))
            (conv-cons
              (conv-all (revTy-typing (suc X) (⇑ᵃ α) (⇑ᵗ S) A
                          (pop-⇑ p) (notasgn-⇑ na) (∋r-⇑ fix rep)
                          (rd-⇑ fix rd) fix (wf-∀-inv wf)))
              (conv-id (wf-∀ (closeAt-wf (pop-⇑ p) (wf-⇑ (read-wf rd))
                                         (wf-∀-inv wf)))))

  concTy-typing : ∀ {Sg Ssᵢ Ssₑ Bs R} (X : ℕ) (α : Addr) (S B : Ty)
    → (Ssᵢ ∥ Bs) ▷ X := α ⇒ (Ssₑ ∥ Bs)
    → NotAssigned (Ssₑ ∥ Bs) α
    → Sg ∣ (Ssᵢ ∥ Bs) ∋r α := R
    → Sg ∣ (Ssₑ ∥ Bs) ⊢ R ⇓ S
    → (∀ η → renameᴿ η R ≡ R)
    → (Ssᵢ ∥ Bs) ⊢ᵗ B
    → Sg ∣ (Ssₑ ∥ Bs) ⊢ concTy X α S B ∶ closeAt X S B ⇝ B ⊣ (Ssᵢ ∥ Bs)

  concTy-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} X α S (` Y) p na rep rd fix wf =
    go (X ≟ Y)
    where
    go : Dec (X ≡ Y)
       → Sg ∣ (Ssₑ ∥ Bs) ⊢ concTy X α S (` Y) ∶ closeAt X S (` Y) ⇝ ` Y
           ⊣ (Ssᵢ ∥ Bs)
    go (yes refl) rewrite concTy-var-hit X α S | closeAt-hit X S =
      conv-cons (conv-seal rep rd p) (conv-id wf)
    go (no ne) rewrite concTy-var-miss X α S Y ne =
      concTy-miss-typing S (` Y) p na (occurs-var-no X Y ne)
        (closeAt-wf p (read-wf rd) wf) wf

  concTy-typing X α S `ℕ p na rep rd fix wf =
    concTy-miss-typing S `ℕ p na refl wf-ℕ wf-ℕ

  concTy-typing X α S `𝔹 p na rep rd fix wf =
    concTy-miss-typing S `𝔹 p na refl wf-𝔹 wf-𝔹

  concTy-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} X α S (A ⇒ B) p na rep rd fix wf =
    go (occursᵗ X (A ⇒ B)) refl
    where
    go : (b : Bool) → occursᵗ X (A ⇒ B) ≡ b
       → Sg ∣ (Ssₑ ∥ Bs) ⊢ concTy X α S (A ⇒ B) ∶ closeAt X S (A ⇒ B)
           ⇝ (A ⇒ B) ⊣ (Ssᵢ ∥ Bs)
    go false eq rewrite concTy-⇒-miss X α S A B eq =
      concTy-miss-typing S (A ⇒ B) p na eq
        (closeAt-wf p (read-wf rd) wf) wf
    go true eq rewrite concTy-⇒-hit X α S A B eq =
      conv-cons
        (conv-fun (revTy-typing X α S A p na rep rd fix (wf-domain wf))
                  (concTy-typing X α S B p na rep rd fix (wf-codomain wf)))
        (conv-id wf)

  concTy-typing {Sg} {Ssᵢ} {Ssₑ} {Bs} X α S (`∀ A) p na rep rd fix wf =
    go (occursᵗ (suc X) A) refl
    where
    go : (b : Bool) → occursᵗ (suc X) A ≡ b
       → Sg ∣ (Ssₑ ∥ Bs) ⊢ concTy X α S (`∀ A) ∶ closeAt X S (`∀ A)
           ⇝ (`∀ A) ⊣ (Ssᵢ ∥ Bs)
    go false eq rewrite concTy-∀-miss X α S A eq =
      concTy-miss-typing S (`∀ A) p na eq (closeAt-wf p (read-wf rd) wf) wf
    go true eq rewrite concTy-∀-hit X α S A eq =
      subst (λ C → Sg ∣ (Ssₑ ∥ Bs)
                      ⊢ all (concTy (suc X) (⇑ᵃ α) (⇑ᵗ S) A) ∷ᶜ id (`∀ A)
                      ∶ C ⇝ (`∀ A) ⊣ (Ssᵢ ∥ Bs))
            (sym (closeAt-∀ X S A))
            (conv-cons
              (conv-all (concTy-typing (suc X) (⇑ᵃ α) (⇑ᵗ S) A
                          (pop-⇑ p) (notasgn-⇑ na) (∋r-⇑ fix rep)
                          (rd-⇑ fix rd) fix (wf-∀-inv wf)))
              (conv-id wf))

------------------------------------------------------------------------
-- 7.  PRESERVATION FOR `TyBeta`
------------------------------------------------------------------------

-- What `⌊_⌋` writes down, the same context reads back.
quote-read : ∀ {Sg Γ A T} → Sg ∣ Γ ⊢⌊ A ⌋ T → Sg ∣ Γ ⊢ T ⇓ A
quote-read (quote-var n) = read-var n
quote-read quote-ℕ = read-ℕ
quote-read quote-𝔹 = read-𝔹
quote-read (quote-⇒ a b) = read-⇒ (quote-read a) (quote-read b)
quote-read (quote-∀ a) = read-∀ (quote-read a)

-- A representation well-formed over an EMPTY stack mentions no free
-- bound address, so a stack renaming fixes it — the `fix` premise of
-- the builder lemma, discharged by `Flat` at a redex.
wfᴿ-fixed : ∀ {Sg Ts Bs T} (η : Renameᵇ)
  → (∀ {i} → Sg ∣ (Ts ∥ Bs) ∋a bnd i → η i ≡ i)
  → Sg ∣ (Ts ∥ Bs) ⊢ᴿ T → renameᴿ η T ≡ T
wfᴿ-fixed η h (wfᴿ-var {α = lvl ℓ} a) = refl
wfᴿ-fixed η h (wfᴿ-var {α = bnd i} a) = cong (λ j → `ᵃ bnd j) (h a)
wfᴿ-fixed η h (wfᴿ-var {α = bse j} a) = refl
wfᴿ-fixed η h wfᴿ-ℕ = refl
wfᴿ-fixed η h wfᴿ-𝔹 = refl
wfᴿ-fixed η h (wfᴿ-⇒ a b) = cong₂ _⇒ᴿ_ (wfᴿ-fixed η h a) (wfᴿ-fixed η h b)
wfᴿ-fixed η h (wfᴿ-∀ a) =
  cong `∀ᴿ (wfᴿ-fixed (extᵇ η)
    (λ { a-here-bind → refl ; (a-skip-bind r) → cong suc (h r) }) a)

repFixed : ∀ {Sg Bs T} → Sg ∣ ([] ∥ Bs) ⊢ᴿ T → ∀ η → renameᴿ η T ≡ T
repFixed wf η = wfᴿ-fixed η (λ ()) wf

-- `⤒ Ss` renames every base address by `suc`, so `bse zero` is the
-- fresh one: the freshness premise of `unseal`/`show` at the redex.
notasgn-⤒ : ∀ {Bs} (Ss : List StackEnt) → NotAssigned (⤒ Ss ∥ Bs) (bse zero)
notasgn-⤒ [] ()
notasgn-⤒ (bind ∷ Ss) (n-skip-bind-e q) = notasgn-⤒ Ss q
notasgn-⤒ (asgn (lvl ℓ) ∷ Ss) (n-skip-asgn q) = notasgn-⤒ Ss q
notasgn-⤒ (asgn (bnd i) ∷ Ss) (n-skip-asgn q) = notasgn-⤒ Ss q
notasgn-⤒ (asgn (bse j) ∷ Ss) (n-skip-asgn q) = notasgn-⤒ Ss q

-- Moving a type from the `∀`'s binder assignment to the `Λ`'s crossing
-- assignment: the NAME structure is the same, only the addresses move,
-- and `⊢ᵗ` never reads an address.
NameExt : Ctxᵗ → Ctxᵗ → Set
NameExt Γ Γ′ = ∀ {X α} → Γ ∋n X := α → Σ[ β ∈ Addr ] (Γ′ ∋n X := β)

ne-bind : ∀ {Ss Bs Ss′ Bs′} → NameExt (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → NameExt (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
ne-bind f n-here-bind = bnd zero , n-here-bind
ne-bind f (n-skip-bind-b q) with f q
ne-bind f (n-skip-bind-b q) | β , r = _ , ∋n-⇑ r
ne-bind f (n-skip-bind-l q) with f q
ne-bind f (n-skip-bind-l q) | β , r = _ , ∋n-⇑ r
ne-bind f (n-skip-bind-e q) with f q
ne-bind f (n-skip-bind-e q) | β , r = _ , ∋n-⇑ r

wf-ext : ∀ {Γ Γ′ A} → NameExt Γ Γ′ → Γ ⊢ᵗ A → Γ′ ⊢ᵗ A
wf-ext f (wf-var n) with f n
wf-ext f (wf-var n) | β , q = wf-var q
wf-ext f wf-ℕ = wf-ℕ
wf-ext f wf-𝔹 = wf-𝔹
wf-ext f (wf-⇒ a b) = wf-⇒ (wf-ext f a) (wf-ext f b)
wf-ext f (wf-∀ a) = wf-∀ (wf-ext (ne-bind f) a)

Λ-nameext : ∀ {Sg Ss Bs e} → StoreOk Sg
  → NameExt (bind ∷ Ss ∥ Bs) (asgn (bse zero) ∷ ⤒ Ss ∥ e ∷ Bs)
Λ-nameext sok n-here-bind = bse zero , n-here-asgn
Λ-nameext sok (n-skip-bind-b q) =
  _ , n-skip-asgn (ren-n (ren-stk (ren-wk sok)) q)
Λ-nameext sok (n-skip-bind-l q) =
  _ , n-skip-asgn (ren-n (ren-stk (ren-wk sok)) q)
Λ-nameext sok (n-skip-bind-e q) =
  _ , n-skip-asgn (ren-n (ren-stk (ren-wk sok)) q)

-- TYBETA.
--
--   (Λ V) • B [ A ]  —→  ν R ∙ (V ⟨ revTy 0 (bse 0) A B ⟩)
--
-- `⊢Λ`'s body lives under `asgn (bse zero) ∷ ⤒ Ss ∥ addr ∷ Bs`; the
-- `ν` re-binds that very address WITH its representation, which is
-- `⊢-grow bg-here`, and the boundary's conversion is the builder at
-- `X := 0`, `α := bse zero`, whose target `closeAt 0 A B` is `⊢•[]`'s
-- result type `B [ A ]ᵗ`.
--
-- TWO SIDE PREMISES, both of which a `typing-wf` / `ctx-ok` lemma
-- would discharge and neither of which exists in v8 yet:
--   * `Sg ∣ Δ ⊢ᴿ R` — `⊢ν`'s own first premise.  It is NOT derivable
--     from `⊢⌊ A ⌋ R` alone: `quote-var` names an address that no
--     judgment says is in scope.
--   * `Δ ⊢ᵗ `∀ B` — the builder's source well-formedness.  Neither
--     `⊢Λ` nor `⊢•[]` carries it.
preserve-TyBeta : ∀ {Sg Ss Bs V A B R}
  → StoreOk Sg
  → Flat (Ss ∥ Bs)
  → Sg ∣ (Ss ∥ Bs) ⊢ᴿ R
  → Sg ∣ (Ss ∥ Bs) ⊢⌊ A ⌋ R
  → (Ss ∥ Bs) ⊢ᵗ `∀ B
  → Sg ∣ (Ss ∥ Bs) ∣ [] ⊢ (Λ V) • B [ A ] ⦂ B [ A ]ᵗ
  → Sg ∣ (Ss ∥ Bs) ∣ [] ⊢ ν R ∙ (V ⟨ revTy zero (bse zero) A B ⟩) ⦂ B [ A ]ᵗ
preserve-TyBeta {Sg} {Ss} {Bs} {V} {A} {B} {R} sok fl wfR q wf∀
  (⊢•[] (⊢Λ v ⊢V) wfA) =
  ⊢ν wfR
    (⊢⟨⟩ (revTy-NF zero (bse zero) A B) (⊢-grow bg-here ⊢V)
         (subst (λ C → Sg ∣ (asgn (bse zero) ∷ ⤒ Ss ∥ nuBind R ∷ Bs)
                          ⊢ revTy zero (bse zero) A B ∶ B ⇝ C
                          ⊣ (⤒ Ss ∥ nuBind R ∷ Bs))
                (closeAt-single A B)
                (revTy-typing zero (bse zero) A B pop-here
                  (notasgn-⤒ Ss) r-here rdA fixR wfB)))
  where
  rdA : Sg ∣ (⤒ Ss ∥ nuBind R ∷ Bs) ⊢ ⇑ᴿᵉ R ⇓ A
  rdA = read-ren (ren-stk (ren-wk {e = nuBind R} sok)) (quote-read q)

  fixR : ∀ η → renameᴿ η (⇑ᴿᵉ R) ≡ ⇑ᴿᵉ R
  fixR η = trans (sym (renᴿ-comm suc η R))
                 (cong (renameᴿᵉ suc) (repFixed (flat-closed fl wfR) η))

  wfB : (asgn (bse zero) ∷ ⤒ Ss ∥ nuBind R ∷ Bs) ⊢ᵗ B
  wfB = wf-ext (Λ-nameext sok) (wf-∀-inv wf∀)

------------------------------------------------------------------------
-- 8.  THE DESIGN DOCUMENT'S INSTANCES
------------------------------------------------------------------------
-- `strong.Examples` checks the CONVERSIONS the builders produce
-- (`§6.builder-agrees`, `K.builder-agrees`, `§14.miss-agrees`) against
-- the words of notes/notes-v8.md.  Here the same three words are given
-- their TYPING, written out so that the endpoints and the two contexts
-- are checked as well — each instance is `revTy-typing` at the
-- redex-shaped frame `Δ⁺ = asgn (bse 0) ∷ [] ∥ nuBind R ∷ []`.

private
  Δ⁺ℕ : Ctxᵗ
  Δ⁺ℕ = asgn (bse zero) ∷ [] ∥ nuBind `ℕᴿ ∷ []

  Δ⁻ℕ : Ctxᵗ
  Δ⁻ℕ = [] ∥ nuBind `ℕᴿ ∷ []

  -- §6  ((Λα,X. λx:X.x) •(X→X)[ℕ]) : the HIT equation at both ends
  §6-builder :
    [] ∣ Δ⁺ℕ ⊢ ((seal 0 (bse 0) ∷ᶜ id (` 0)) ↦ (unseal 0 (bse 0) ∷ᶜ id `ℕ))
                 ∷ᶜ id (`ℕ ⇒ `ℕ)
      ∶ (` 0 ⇒ ` 0) ⇝ (`ℕ ⇒ `ℕ) ⊣ Δ⁻ℕ
  §6-builder =
    revTy-typing zero (bse zero) `ℕ (` 0 ⇒ ` 0) pop-here (notasgn-⤒ [])
      r-here read-ℕ (λ η → refl)
      (wf-⇒ (wf-var n-here-asgn) (wf-var n-here-asgn))

  -- K  g = Λα,X. λx:X. Λγ,Z. λz:Z. x : the crossing descends under a
  -- `∀`, raising the name to 1 and dualising into `hide`
  K-builder :
    [] ∣ Δ⁺ℕ ⊢ ((seal 0 (bse 0) ∷ᶜ id (` 0))
                   ↦ (all (((hide 1 (bse 0) ∷ᶜ id (` 0))
                              ↦ (unseal 1 (bse 0) ∷ᶜ id `ℕ))
                             ∷ᶜ id (` 0 ⇒ `ℕ))
                        ∷ᶜ id (`∀ (` 0 ⇒ `ℕ))))
                 ∷ᶜ id (`ℕ ⇒ `∀ (` 0 ⇒ `ℕ))
      ∶ (` 0 ⇒ `∀ (` 0 ⇒ ` 1)) ⇝ (`ℕ ⇒ `∀ (` 0 ⇒ `ℕ)) ⊣ Δ⁻ℕ
  K-builder =
    revTy-typing zero (bse zero) `ℕ (` 0 ⇒ `∀ (` 0 ⇒ ` 1)) pop-here
      (notasgn-⤒ []) r-here read-ℕ (λ η → refl)
      (wf-⇒ (wf-var n-here-asgn)
            (wf-∀ (wf-⇒ (wf-var n-here-bind)
                        (wf-var (n-skip-bind-e n-here-asgn)))))

  -- §14  X ∉ B: the MISS equation, one identity crossing
  §14-builder :
    [] ∣ Δ⁺ℕ ⊢ show 0 (bse 0) ∷ᶜ id (`∀ (` 0 ⇒ ` 0) ⇒ `∀ (` 0 ⇒ ` 0))
      ∶ (`∀ (` 0 ⇒ ` 0) ⇒ `∀ (` 0 ⇒ ` 0))
      ⇝ (`∀ (` 0 ⇒ ` 0) ⇒ `∀ (` 0 ⇒ ` 0)) ⊣ Δ⁻ℕ
  §14-builder =
    revTy-typing zero (bse zero) `ℕ (`∀ (` 0 ⇒ ` 0) ⇒ `∀ (` 0 ⇒ ` 0))
      pop-here (notasgn-⤒ []) r-here read-ℕ (λ η → refl)
      (wf-⇒ (wf-∀ (wf-⇒ (wf-var n-here-bind) (wf-var n-here-bind)))
            (wf-∀ (wf-⇒ (wf-var n-here-bind) (wf-var n-here-bind))))
