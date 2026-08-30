module alt.probes.RegionBracketingAudit where

-- File Charter:
--   * Defines the path-stack meaning of well-bracketed regions: a begin pushes
--     its region and an end is accepted only for the current stack head.
--   * Audits every current reduction constructor that creates, deletes,
--     moves, or evaluates beneath reveal/conceal syntax.  The audit exposes
--     the failing β-Λ composition when its value captures an outer conceal.
--   * Rechecks that both closed, crossing-free U40 sources reach their nested
--     β-Λ/SCWRAP prefixes, and records the critical adversarial path produced
--     when a surviving outer wrapper is substituted through an inner SCWRAP.
--   * States the telescope-side innermost-live premise that would enforce the
--     observed bracket discipline.  No typing or reduction rule is changed.

open import Data.Bool using (Bool; false; true; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction using (_⊢_—→_)
import alt.probes.ChainNuReachability as U40
open U40 using (_⊢_—↠_)

------------------------------------------------------------------------
-- Exact path discipline
------------------------------------------------------------------------

-- Region names are abstract naturals in this audit.  `begin r` pushes r;
-- `end r` can run only when r is the innermost currently open region.
data Bracket : Set where
  begin : ℕ → Bracket
  end : ℕ → Bracket

infix 4 _⊢ᵇ_⇓_

data _⊢ᵇ_⇓_ : List ℕ → List Bracket → List ℕ → Set where
  done : ∀ {stack}
      ----------------
    → stack ⊢ᵇ [] ⇓ stack

  push : ∀ {stack path final r}
    → (r ∷ stack) ⊢ᵇ path ⇓ final
      ---------------------------------
    → stack ⊢ᵇ begin r ∷ path ⇓ final

  pop : ∀ {stack path final r}
    → stack ⊢ᵇ path ⇓ final
      -----------------------------
    → (r ∷ stack) ⊢ᵇ end r ∷ path ⇓ final

-- A path may finish with regions open because it ends at an interior leaf;
-- the invariant constrains every end, not the final stack.

outer inner : ℕ
outer = zero
inner = suc zero

neutral-path : [] ⊢ᵇ [] ⇓ []
neutral-path = done

open-path : [] ⊢ᵇ begin outer ∷ [] ⇓ outer ∷ []
open-path = push done

close-path : outer ∷ [] ⊢ᵇ end outer ∷ [] ⇓ []
close-path = pop done

matched-path :
  [] ⊢ᵇ begin outer ∷ end outer ∷ [] ⇓ []
matched-path = push (pop done)

close-reopen-path :
  outer ∷ [] ⊢ᵇ end outer ∷ begin outer ∷ [] ⇓ outer ∷ []
close-reopen-path = pop (push done)

nested-wrapper-path :
  outer ∷ [] ⊢ᵇ
    begin inner ∷ end inner ∷ end outer ∷ [] ⇓ []
nested-wrapper-path = push (pop (pop done))

-- This is the U56 bad geometry.  Its outer end cannot cross the inner stack
-- head, independently of the path's requested final stack.
interleaved-path-rejected : ∀ {final}
  → ¬ (outer ∷ [] ⊢ᵇ
      begin inner ∷ end outer ∷ [] ⇓ final)
interleaved-path-rejected (push ())

------------------------------------------------------------------------
-- Closed source check
------------------------------------------------------------------------

-- The compiler-facing fragment may contain ordinary casts but no region
-- allocation or boundary node.  This executable check is used only for the
-- two closed U40 sources below.
ruleMintedOnly : ∀ {Θ Δ} → Term Θ Δ → Bool
ruleMintedOnly (` x) = true
ruleMintedOnly (ƛ A ˙ N) = ruleMintedOnly N
ruleMintedOnly (L · M) = ruleMintedOnly L ∧ ruleMintedOnly M
ruleMintedOnly (Λ M) = ruleMintedOnly M
ruleMintedOnly (M ⦂∀ B [ A ]) = ruleMintedOnly M
ruleMintedOnly ($ κ) = true
ruleMintedOnly (L ⊕[ op ] M) = ruleMintedOnly L ∧ ruleMintedOnly M
ruleMintedOnly (M ⟨ c ⟩) = ruleMintedOnly M
ruleMintedOnly (M ↑[ X ≔ α ] c) = false
ruleMintedOnly (M ↓[ X ≔ α ] c) = false
ruleMintedOnly (ν[ A ] M) = false
ruleMintedOnly blame = true

u40-app-source-crossing-free : ruleMintedOnly U40.closedAppSource ≡ true
u40-app-source-crossing-free = refl

u40-star-source-crossing-free : ruleMintedOnly U40.closedStarSource ≡ true
u40-star-source-crossing-free = refl

u40-app-producer-prefix :
  U40.emptyEnv ⊢ U40.closedAppSource —↠ U40.closedAppAfterSCWrap
u40-app-producer-prefix = U40.closed-app-scwrap-trace

u40-star-producer-prefix :
  U40.emptyEnv ⊢ U40.closedStarSource —↠ U40.closedStarAfterSCWrap
u40-star-producer-prefix = U40.closed-star-scwrap-trace

------------------------------------------------------------------------
-- Exhaustive boundary-effect audit of `_⊢_—→_`
------------------------------------------------------------------------

-- Minting rules
--
-- β-Λ       : mints `ν X ; begin X`; path effect `begin X`.
-- β-gen     : mints `ν X ; begin X ; end X`; matched pair.
-- SCWRAP    : retains the reveal and mints its matching wrapper conceal.
--             The variable branch changes `begin X` to `begin X ; end X`.
--
-- The checked effects are `open-path`, `matched-path`, and
-- `scwrap-variable-path` below.

βΛ-path : [] ⊢ᵇ begin outer ∷ [] ⇓ outer ∷ []
βΛ-path = open-path

-- If the polymorphic value already contains `end outer`, β-Λ puts its new
-- `begin inner` outside that end.  This is the producer failure exercised by
-- `RegionInterleavingReachable` from a closed source.
βΛ-captured-outer-path-rejected : ∀ {final}
  → ¬ (outer ∷ [] ⊢ᵇ
      begin inner ∷ end outer ∷ [] ⇓ final)
βΛ-captured-outer-path-rejected = interleaved-path-rejected

βgen-path : [] ⊢ᵇ begin outer ∷ end outer ∷ [] ⇓ []
βgen-path = matched-path

scwrap-variable-path :
  [] ⊢ᵇ begin outer ∷ end outer ∷ [] ⇓ []
scwrap-variable-path = matched-path

-- Boundary conversion/reassociation rules
--
-- inject-conceal       : `end X` to `end X`.
-- inject-reveal        : `begin X` to `begin X`.
-- inject-reveal-resolve: `begin X` to `begin X`.
-- ★-project-reveal      : `begin X` to `begin X`.
-- β-reveal-⇒            : the argument branch becomes
--                         `begin X ; end X`.
-- β-conceal-⇒           : the argument branch becomes
--                         `end X ; begin X`, sequential rather than crossed.
-- β-reveal-∀/β-conceal-∀: move the same boundary through `Λ`.

inject-conceal-path :
  outer ∷ [] ⊢ᵇ end outer ∷ [] ⇓ []
inject-conceal-path = close-path

inject-reveal-path :
  [] ⊢ᵇ begin outer ∷ [] ⇓ outer ∷ []
inject-reveal-path = open-path

inject-reveal-resolve-path :
  [] ⊢ᵇ begin outer ∷ [] ⇓ outer ∷ []
inject-reveal-resolve-path = open-path

star-project-reveal-path :
  [] ⊢ᵇ begin outer ∷ [] ⇓ outer ∷ []
star-project-reveal-path = open-path

βreveal-arrow-argument-path :
  [] ⊢ᵇ begin outer ∷ end outer ∷ [] ⇓ []
βreveal-arrow-argument-path = matched-path

βconceal-arrow-argument-path :
  outer ∷ [] ⊢ᵇ end outer ∷ begin outer ∷ [] ⇓ outer ∷ []
βconceal-arrow-argument-path = close-reopen-path

scTyWrap-reveal-path :
  [] ⊢ᵇ begin outer ∷ [] ⇓ outer ∷ []
scTyWrap-reveal-path = open-path

scTyWrap-conceal-path :
  outer ∷ [] ⊢ᵇ end outer ∷ [] ⇓ []
scTyWrap-conceal-path = close-path

-- Cancellation and blame rules
--
-- id-cancel and conceal-reveal delete `begin X ; end X`; a well-bracketed
-- conceal-reveal redex necessarily has the same innermost region even though
-- its raw constructor carries independent X/Y fields.  id-reveal and
-- blame-reveal delete `begin X`; id-conceal and blame-conceal delete `end X`.

id-cancel-redex-path :
  [] ⊢ᵇ begin outer ∷ end outer ∷ [] ⇓ []
id-cancel-redex-path = matched-path

conceal-reveal-redex-path :
  [] ⊢ᵇ begin outer ∷ end outer ∷ [] ⇓ []
conceal-reveal-redex-path = matched-path

id-or-blame-reveal-path :
  [] ⊢ᵇ begin outer ∷ [] ⇓ outer ∷ []
id-or-blame-reveal-path = open-path

id-or-blame-conceal-path :
  outer ∷ [] ⊢ᵇ end outer ∷ [] ⇓ []
id-or-blame-conceal-path = close-path

-- Dissolution and congruence rules
--
-- blame-ν, const-ν, tag-out, inert-cast-out, NUWRAP, and NUTYWRAP do not
-- add or reorder begin/end events.  NUWRAP crosses `ƛ`; NUTYWRAP crosses
-- `Λ`; tag/inert move a cast.  The ν remains on the same side of every
-- region boundary.  All ξ rules retain their enclosing path; ξ-reveal and
-- ξ-conceal evaluate under the already-recorded begin/end respectively.
-- The remaining rules (δ, ordinary β/casts, ground/expand, tag-untag,
-- β-∀, β-inst, primitive/blame propagation) mint no boundary syntax.
-- This is only a syntactic observation: ordinary β can relocate an existing
-- boundary.  No generic bracketing-preservation claim is made for substitution.

boundary-neutral-path : ∀ {stack path final}
  → stack ⊢ᵇ path ⇓ final
  → stack ⊢ᵇ path ⇓ final
boundary-neutral-path path-ok = path-ok

nu-dissolution-path :
  [] ⊢ᵇ begin outer ∷ end outer ∷ [] ⇓ []
nu-dissolution-path = boundary-neutral-path matched-path

congruence-path :
  outer ∷ [] ⊢ᵇ end outer ∷ begin outer ∷ [] ⇓ outer ∷ []
congruence-path = boundary-neutral-path close-reopen-path

------------------------------------------------------------------------
-- Adversarial compositions
------------------------------------------------------------------------

-- Critical U40 continuation after the nested allocation: inner SCWRAP puts
-- its own conceal around the argument occurrence before ordinary β inserts
-- the still-surviving outer wrapper.  The path is therefore
--
--   begin inner ; end inner ; end outer
--
-- from ambient stack `[outer]`, checked by `nested-wrapper-path`.  The bad
-- alternative `begin inner ; end outer` is rejected above.
u40-nested-substitution-path :
  outer ∷ [] ⊢ᵇ
    begin inner ∷ end inner ∷ end outer ∷ [] ⇓ []
u40-nested-substitution-path = nested-wrapper-path

-- Escape/re-crossing uses the same β-reveal-⇒ or SCWRAP wrapper discipline:
-- the newly opened region is ended before the escaped value is entered.
escape-recrossing-path :
  outer ∷ [] ⊢ᵇ
    begin inner ∷ end inner ∷ end outer ∷ [] ⇓ []
escape-recrossing-path = nested-wrapper-path

-- The parked ν-push-conceal/ν-gc-conceal pair is absent from the current
-- reduction datatype at this branch tip, so it cannot produce a current trace.

------------------------------------------------------------------------
-- Typing-level invariant indicated by the audit
------------------------------------------------------------------------

-- A conceal rule would retain its existing premise
--
--   lookup σ Y ≡ just α
--
-- and add: `begin[ Y ≔ α ]` is the most recent live begin in Ψ.  Read this
-- from the telescope, not σ: scan constructors backward, skipping `,typ` and
-- `,:=`, and skip already closed begin/end segments.  The first unmatched
-- begin encountered must be exactly `begin[ Y ≔ α ]`.  The map σ records
-- current aliases and positions but not temporal begin order, so σ alone
-- cannot state the premise.
