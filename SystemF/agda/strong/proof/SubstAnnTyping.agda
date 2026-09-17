module strong.proof.SubstAnnTyping where

-- Strong System F v8 — the typing of `substAnn`, the type substitution
-- that `instReveal`/`instConceal` perform on a conversion's
-- ANNOTATIONS when a `∀` is instantiated.
--
-- `substAnn X S c` REMOVES the name slot X from the context: the
-- annotations are closed over X by `closeAt X S`, and every crossing's
-- NAME is decremented by `nameSub X` exactly when it lies above the
-- slot.  So the lemma transports a typing derivation from a context
-- that still has the slot to the one that has lost it.
--
-- THE SLOT MOVES.  A conversion's spine runs INTERIOR → EXTERIOR, and
-- every crossing changes the context: `seal`/`hide` make the exterior
-- GAIN a name at Y, `unseal`/`show` make it LOSE the one at Y.  So the
-- slot sits at a different index at every element, and `S` — which
-- lives in the coordinates of the context with the slot ALREADY
-- REMOVED — has to be re-expressed as well.  `substAnn` threads both
-- along the spine with `slotOutElt`/`tyOutElt` (strong.Conversion);
-- this proof threads the DROP with them (§9), which is what removed
-- v7's `SlotFree`.
--
-- THE SHAPE OF THE RELATION.  `DropBindS` is an inductive relation in
-- constructor form, not an equation on lists, because every judgment
-- this proof lifts (`∋n`, `∋ᵗ`, `∋b`, `⊢ᵗ`, `⇓`, `▷ := ⇒`) is itself
-- defined by recursion down the stack: a `here`/`there` relation
-- unifies with those derivations one constructor at a time, while `Δ ≡
-- Ss ++ bind ∷ Ss′` would leave every case blocked on an append.
--
-- `drop-there` steps past ANY stack entry, not just a `bind`.  In v7 it
-- stepped past `bind`s only, and that is exactly what made `SlotFree`
-- necessary: a `seal 0 α` or `hide 0 α` puts an `asgn` ABOVE the slot,
-- so the exterior drop does not exist at all in the bind-only form.
-- The `X < Y` premises of `SlotFree` were the assumption that this
-- never happens.  With the general form the exterior drop is CONSTRUCT-
-- IBLE (`drop-pop`), and with it the slot index the crossing moves to.
--
-- WHAT IS LEFT OF THE SIDE CONDITIONS.  Two, and each is smaller than
-- its v7 ancestor:
--
--   * `RepsWf` (§6) — a representation reached by `∋r` has its `` `ᵛ ``s
--     bound by its own `∀ᴿ`s.  All that is left of v7's `NoBndReps`.
--
--   * `SAvoids` (§6) — the weakening of `Closedᵗ S`.  Going outward,
--     `S` is renamed; the rename is faithful only where `S` does not
--     mention the name the crossing moves.  One `Avoidᵗ` per atomic
--     element (two for `unseal`/`show`), plus a well-formedness premise
--     on `S` that is threaded along the spine.
--
-- `StepFix` — the last residue of `SlotFree` — IS GONE.  It said that
-- the slot index comes back to where it started across an `↦`'s
-- components and across an `all`'s body, which is what the OLD
--   substAnnElt X S (s ↦ t) = substAnn X S s ↦ substAnn X S t
-- assumed by handing the same index to two components running in
-- OPPOSITE directions.  `substAnnElt` now steps the index into the
-- contravariant component (`substAnn (slotOut t X) (tyOut t S) s`),
-- and §8b DERIVES what is left: a conversion never changes the BIND
-- SKELETON of its context, so the slot — a `bind` — keeps its rank
-- among the binds along the whole spine, and `↦`'s two components,
-- running between the SAME two contexts, return it to itself.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using
  (_≟_; _<?_; ≤-refl; ≤-trans; suc-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.TypeSubst using
  (rename-subst-commute; rename-subst; rename-cong; rename-rename-commute)
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.proof.AddrWeaken using (conv-base)

private
  variable
    Sg : Store
    Bs Bs′ : List BaseEnt
    Ss Ss′ Ss″ Ssᵢ Ssᵢ′ Ssₑ Ssₑ′ : List StackEnt
    Γ Γ′ : Ctxᵗ
    A B S T : Ty
    R : RepTy
    X Y Z P W n i : ℕ
    α : Addr
    c s t : Conv
    ĉ : ConvElt

------------------------------------------------------------------------
-- §0  Arithmetic, kept local and minimal
------------------------------------------------------------------------

¬<-¬≡-> : ¬ (X < Z) → ¬ (X ≡ Z) → Z < X
¬<-¬≡-> {zero} {zero} nlt ne = ⊥-elim (ne refl)
¬<-¬≡-> {zero} {suc Z} nlt ne = ⊥-elim (nlt (s≤s z≤n))
¬<-¬≡-> {suc X} {zero} nlt ne = s≤s z≤n
¬<-¬≡-> {suc X} {suc Z} nlt ne =
  s≤s (¬<-¬≡-> (λ lt → nlt (s≤s lt)) (λ eq → ne (cong suc eq)))

<-irr : X < X → ⊥
<-irr (s≤s lt) = <-irr lt

<-asym : X < Z → Z < X → ⊥
<-asym (s≤s p) (s≤s q) = <-asym q p

>-≢ : Z < X → ¬ (X ≡ Z)
>-≢ lt refl = <-irr lt

pos-of : X < Z → zero < Z
pos-of {Z = suc Z} lt = s≤s z≤n

suc-pred : zero < Z → suc (Z ∸ 1) ≡ Z
suc-pred {Z = suc Z} lt = refl

pred≤ : suc Z ≤ suc Y → Z ≤ Y
pred≤ (s≤s le) = le

------------------------------------------------------------------------
-- §1  `nameSub`, `shiftAtᵗ` and `closeEnv`, pointwise
------------------------------------------------------------------------

nameSub-gt : ∀ X Y → X < Y → nameSub X Y ≡ (Y ∸ 1)
nameSub-gt X Y lt with X <? Y
nameSub-gt X Y lt | yes _ = refl
nameSub-gt X Y lt | no nlt = ⊥-elim (nlt lt)

nameSub-le : ∀ X Y → ¬ (X < Y) → nameSub X Y ≡ Y
nameSub-le X Y nlt with X <? Y
nameSub-le X Y nlt | yes lt = ⊥-elim (nlt lt)
nameSub-le X Y nlt | no _ = refl

-- the one fact every `there`/`all` step needs: the slot and the name
-- it reindexes move up together
nameSub-suc : ∀ X Y → nameSub (suc X) (suc Y) ≡ suc (nameSub X Y)
nameSub-suc X Y with X <? Y
nameSub-suc X Y | yes lt
  rewrite nameSub-gt (suc X) (suc Y) (s≤s lt) =
  sym (suc-pred (pos-of lt))
nameSub-suc X Y | no nlt =
  nameSub-le (suc X) (suc Y) (λ lt → nlt (pred≤ lt))

nameSub-pred : ∀ Z → nameSub zero (suc Z) ≡ Z
nameSub-pred Z = nameSub-gt zero (suc Z) (s≤s z≤n)

-- A removed name is either the crossing's own name, or one below it —
-- the two cases `nameSub` decides between.  Stated as a sum so the
-- lemmas that need it never have to re-run the decision.
nameSub-cases : ∀ X Y → (nameSub X Y ≡ Y) ⊎ (Y ≡ suc (nameSub X Y))
nameSub-cases X Y with X <? Y
nameSub-cases X Y | no nlt = inj₁ refl
nameSub-cases X Y | yes lt = inj₂ (sym (suc-pred (pos-of lt)))

shiftAt-inj : ∀ Y {Z₁ Z₂} → shiftAtᵗ Y Z₁ ≡ shiftAtᵗ Y Z₂ → Z₁ ≡ Z₂
shiftAt-inj zero refl = refl
shiftAt-inj (suc Y) {zero} {zero} eq = refl
shiftAt-inj (suc Y) {zero} {suc Z₂} ()
shiftAt-inj (suc Y) {suc Z₁} {zero} ()
shiftAt-inj (suc Y) {suc Z₁} {suc Z₂} eq =
  cong suc (shiftAt-inj Y (suc-injective eq))

-- Shifting at W and at suc W agree everywhere but at W itself.
shiftAt-suc-agree : ∀ W V → ¬ (V ≡ W)
  → shiftAtᵗ (suc W) V ≡ shiftAtᵗ W V
shiftAt-suc-agree zero zero ne = ⊥-elim (ne refl)
shiftAt-suc-agree zero (suc V) ne = refl
shiftAt-suc-agree (suc W) zero ne = refl
shiftAt-suc-agree (suc W) (suc V) ne =
  cong suc (shiftAt-suc-agree W V (λ eq → ne (cong suc eq)))

-- Removing the name Y and putting it back is the identity off Y.
sub-shift-id : ∀ Y V → ¬ (V ≡ Y) → shiftAtᵗ Y (nameSub Y V) ≡ V
sub-shift-id zero zero ne = ⊥-elim (ne refl)
sub-shift-id zero (suc V) ne = refl
sub-shift-id (suc Y) zero ne = refl
sub-shift-id (suc Y) (suc V) ne
  rewrite nameSub-suc Y V =
  cong suc (sub-shift-id Y V (λ eq → ne (cong suc eq)))

-- ... and putting it back ONE LOWER is the identity off both names.
sub-shift-id-suc : ∀ W V → ¬ (V ≡ W) → ¬ (V ≡ suc W)
  → shiftAtᵗ W (nameSub (suc W) V) ≡ V
sub-shift-id-suc zero zero ne₁ ne₂ = ⊥-elim (ne₁ refl)
sub-shift-id-suc zero (suc zero) ne₁ ne₂ = ⊥-elim (ne₂ refl)
sub-shift-id-suc zero (suc (suc V)) ne₁ ne₂ = refl
sub-shift-id-suc (suc W) zero ne₁ ne₂ = refl
sub-shift-id-suc (suc W) (suc V) ne₁ ne₂
  rewrite nameSub-suc (suc W) V =
  cong suc (sub-shift-id-suc W V (λ eq → ne₁ (cong suc eq))
                                 (λ eq → ne₂ (cong suc eq)))

-- The crossing's name, read on the side that HAS the assignment, does
-- not depend on which side the slot index is taken from.
nameSub-shift : ∀ X Y → nameSub (shiftAtᵗ Y X) Y ≡ nameSub X Y
nameSub-shift X zero = refl
nameSub-shift zero (suc Y) = refl
nameSub-shift (suc X) (suc Y) =
  trans (nameSub-suc (shiftAtᵗ Y X) Y)
        (trans (cong suc (nameSub-shift X Y)) (sym (nameSub-suc X Y)))

-- THE index law of this file: inserting a name at Y commutes with
-- removing the slot, the slot sliding up by `shiftAtᵗ Y` and the
-- crossing's own name sliding down by `nameSub P`.
nameSub-shiftAt : ∀ Y P Z → ¬ (P ≡ Z)
  → nameSub (shiftAtᵗ Y P) (shiftAtᵗ Y Z)
    ≡ shiftAtᵗ (nameSub P Y) (nameSub P Z)
nameSub-shiftAt zero P Z ne
  rewrite nameSub-le P zero (λ ()) = nameSub-suc P Z
nameSub-shiftAt (suc Y) zero zero ne = ⊥-elim (ne refl)
nameSub-shiftAt (suc Y) zero (suc Z) ne
  rewrite nameSub-pred (shiftAtᵗ Y Z) | nameSub-pred Y | nameSub-pred Z =
  refl
nameSub-shiftAt (suc Y) (suc P) zero ne
  rewrite nameSub-le (suc (shiftAtᵗ Y P)) zero (λ ())
        | nameSub-suc P Y
        | nameSub-le (suc P) zero (λ ()) = refl
nameSub-shiftAt (suc Y) (suc P) (suc Z) ne
  rewrite nameSub-suc (shiftAtᵗ Y P) (shiftAtᵗ Y Z)
        | nameSub-suc P Y | nameSub-suc P Z =
  cong suc (nameSub-shiftAt Y P Z (λ eq → ne (cong suc eq)))

-- A renaming that is pointwise the identity is the identity; and
-- `nameSub 0` undoes `suc`, which is what `tyOutElt (all s)` needs —
-- it brings the slot's type back out from under the `all`'s binder.
ren-id : ∀ {ρ} → (∀ V → ρ V ≡ V) → ∀ S → renameᵗ ρ S ≡ S
ren-id h (` V) = cong `_ (h V)
ren-id h `ℕ = refl
ren-id h `𝔹 = refl
ren-id h (A ⇒ B) = cong₂ _⇒_ (ren-id h A) (ren-id h B)
ren-id {ρ = ρ} h (`∀ A) = cong `∀ (ren-id h-ext A)
  where
  h-ext : ∀ V → extᵗ ρ V ≡ V
  h-ext zero = refl
  h-ext (suc V) = cong suc (h V)

ren-sub0 : ∀ S → renameᵗ (nameSub zero) (renameᵗ suc S) ≡ S
ren-sub0 S =
  trans (rename-rename-commute suc (nameSub zero) S)
        (ren-id (λ V → nameSub-pred V) S)

closeEnv-eq : ∀ X S → closeEnv X S X ≡ S
closeEnv-eq X S with X ≟ X
closeEnv-eq X S | yes _ = refl
closeEnv-eq X S | no ne = ⊥-elim (ne refl)

closeEnv-gt : ∀ X S Z → X < Z → closeEnv X S Z ≡ ` (Z ∸ 1)
closeEnv-gt X S Z lt with X ≟ Z
closeEnv-gt X S Z lt | yes refl = ⊥-elim (<-irr lt)
closeEnv-gt X S Z lt | no _ with X <? Z
closeEnv-gt X S Z lt | no _ | yes _ = refl
closeEnv-gt X S Z lt | no _ | no nlt = ⊥-elim (nlt lt)

closeEnv-lt : ∀ X S Z → Z < X → closeEnv X S Z ≡ ` Z
closeEnv-lt X S Z lt with X ≟ Z
closeEnv-lt X S Z lt | yes refl = ⊥-elim (<-irr lt)
closeEnv-lt X S Z lt | no _ with X <? Z
closeEnv-lt X S Z lt | no _ | yes gt = ⊥-elim (<-asym gt lt)
closeEnv-lt X S Z lt | no _ | no _ = refl

closeEnv-≢ : ∀ X S Z → ¬ (X ≡ Z) → closeEnv X S Z ≡ ` (nameSub X Z)
closeEnv-≢ X S Z ne with X <? Z
closeEnv-≢ X S Z ne | yes lt = closeEnv-gt X S Z lt
closeEnv-≢ X S Z ne | no nlt = closeEnv-lt X S Z (¬<-¬≡-> nlt ne)

------------------------------------------------------------------------
-- §2  Not mentioning a name: SIDE CONDITION (1) on S
------------------------------------------------------------------------
-- `Avoidᵗ Z S` is `occursᵗ Z S ≡ false` in constructor form, which is
-- what the proofs want: every use is a pointwise statement about S's
-- variables, and the `∀` case has to step the name.
--
-- Where it is spent: going outward across an `unseal`/`show`, `S` is
-- re-expressed by `renameᵗ (nameSub Y)`, and the name that disappears
-- from the frame must not be one S mentions.  Going outward across a
-- `seal`/`hide`, `substAnn` shifts S at the crossing's OWN name Y,
-- while the frame S lives in — the one with the slot removed — gains
-- its entry at `nameSub X Y`; the two renamings agree off that name.

data Avoidᵗ : ℕ → Ty → Set where
  av-var : ∀ {Z V} → ¬ (Z ≡ V) → Avoidᵗ Z (` V)
  av-ℕ   : ∀ {Z} → Avoidᵗ Z `ℕ
  av-𝔹   : ∀ {Z} → Avoidᵗ Z `𝔹
  av-⇒   : ∀ {Z A B} → Avoidᵗ Z A → Avoidᵗ Z B → Avoidᵗ Z (A ⇒ B)
  av-∀   : ∀ {Z A} → Avoidᵗ (suc Z) A → Avoidᵗ Z (`∀ A)

av-ren-cong : ∀ {Z S ρ₁ ρ₂} → Avoidᵗ Z S
  → (∀ V → ¬ (V ≡ Z) → ρ₁ V ≡ ρ₂ V)
  → renameᵗ ρ₁ S ≡ renameᵗ ρ₂ S
av-ren-cong (av-var {V = V} ne) h = cong `_ (h V (λ eq → ne (sym eq)))
av-ren-cong av-ℕ h = refl
av-ren-cong av-𝔹 h = refl
av-ren-cong (av-⇒ a b) h = cong₂ _⇒_ (av-ren-cong a h) (av-ren-cong b h)
av-ren-cong {ρ₁ = ρ₁} {ρ₂ = ρ₂} (av-∀ {Z = Z} a) h =
  cong `∀ (av-ren-cong a h-ext)
  where
  h-ext : ∀ V → ¬ (V ≡ suc Z) → extᵗ ρ₁ V ≡ extᵗ ρ₂ V
  h-ext zero ne = refl
  h-ext (suc V) ne = cong suc (h V (λ eq → ne (cong suc eq)))

av-ren-id : ∀ {Z₁ Z₂ S ρ} → Avoidᵗ Z₁ S → Avoidᵗ Z₂ S
  → (∀ V → ¬ (V ≡ Z₁) → ¬ (V ≡ Z₂) → ρ V ≡ V)
  → renameᵗ ρ S ≡ S
av-ren-id (av-var {V = V} ne₁) (av-var ne₂) h =
  cong `_ (h V (λ eq → ne₁ (sym eq)) (λ eq → ne₂ (sym eq)))
av-ren-id av-ℕ av-ℕ h = refl
av-ren-id av-𝔹 av-𝔹 h = refl
av-ren-id (av-⇒ a₁ b₁) (av-⇒ a₂ b₂) h =
  cong₂ _⇒_ (av-ren-id a₁ a₂ h) (av-ren-id b₁ b₂ h)
av-ren-id {ρ = ρ} (av-∀ {Z = Z₁} a₁) (av-∀ {Z = Z₂} a₂) h =
  cong `∀ (av-ren-id a₁ a₂ h-ext)
  where
  h-ext : ∀ V → ¬ (V ≡ suc Z₁) → ¬ (V ≡ suc Z₂) → extᵗ ρ V ≡ V
  h-ext zero ne₁ ne₂ = refl
  h-ext (suc V) ne₁ ne₂ =
    cong suc (h V (λ eq → ne₁ (cong suc eq)) (λ eq → ne₂ (cong suc eq)))

av-ren-comp : ∀ {Z₁ Z₂ S ρ₁ ρ₂} → Avoidᵗ Z₁ S → Avoidᵗ Z₂ S
  → (∀ V → ¬ (V ≡ Z₁) → ¬ (V ≡ Z₂) → ρ₂ (ρ₁ V) ≡ V)
  → renameᵗ ρ₂ (renameᵗ ρ₁ S) ≡ S
av-ren-comp {S = S} {ρ₁ = ρ₁} {ρ₂ = ρ₂} a b h =
  trans (rename-rename-commute ρ₁ ρ₂ S) (av-ren-id a b h)

-- the `seal`/`hide` equation: `substAnn` shifts S at Y, the frame
-- gains its entry at W, and off W the two agree
shift-avoid : ∀ {S} Y W → Avoidᵗ W S → (W ≡ Y) ⊎ (Y ≡ suc W)
  → renameᵗ (shiftAtᵗ Y) S ≡ renameᵗ (shiftAtᵗ W) S
shift-avoid Y W av (inj₁ refl) = refl
shift-avoid .(suc W) W av (inj₂ refl) =
  av-ren-cong av (λ V ne → shiftAt-suc-agree W V ne)

-- Removing the name Y and removing the name below it agree off Y.
sub-suc-agree : ∀ W V → ¬ (V ≡ suc W)
  → nameSub (suc W) V ≡ nameSub W V
sub-suc-agree zero zero ne = refl
sub-suc-agree zero (suc zero) ne = ⊥-elim (ne refl)
sub-suc-agree zero (suc (suc V)) ne = refl
sub-suc-agree (suc W) zero ne = refl
sub-suc-agree (suc W) (suc V) ne
  rewrite nameSub-suc (suc W) V | nameSub-suc W V =
  cong suc (sub-suc-agree W V (λ eq → ne (cong suc eq)))

-- so `substAnnOut`'s `renameᵗ (nameSub Y)` and the frame's own
-- `renameᵗ (nameSub (nameSub X Y))` do the same thing to S
sub-avoid-cong : ∀ {S} Y W → Avoidᵗ Y S → (W ≡ Y) ⊎ (Y ≡ suc W)
  → renameᵗ (nameSub Y) S ≡ renameᵗ (nameSub W) S
sub-avoid-cong Y .Y av (inj₁ refl) = refl
sub-avoid-cong .(suc W) W av (inj₂ refl) =
  av-ren-cong av (λ V ne → sub-suc-agree W V ne)

-- the `unseal`/`show` equation: removing Y from S and putting a name
-- back at W recovers S
sub-avoid : ∀ {S} Y W → Avoidᵗ Y S → Avoidᵗ W S → (W ≡ Y) ⊎ (Y ≡ suc W)
  → renameᵗ (shiftAtᵗ W) (renameᵗ (nameSub Y) S) ≡ S
sub-avoid Y .Y avY avW (inj₁ refl) =
  av-ren-comp avY avW (λ V ne₁ ne₂ → sub-shift-id Y V ne₁)
sub-avoid .(suc W) W avY avW (inj₂ refl) =
  av-ren-comp avY avW (λ V ne₁ ne₂ → sub-shift-id-suc W V ne₂ ne₁)

------------------------------------------------------------------------
-- §2b  Closed types, and the bridge to §2
------------------------------------------------------------------------
-- A closed type mentions nothing, so it avoids every name and is fixed
-- by every renaming.  This is what callers with a ground type argument
-- — `•B[A]` on ground data, as in `Examples.§14` — supply.

data NoFreeᵗ : ℕ → Ty → Set where
  nf-var : ∀ {n} → X < n → NoFreeᵗ n (` X)
  nf-ℕ   : ∀ {n} → NoFreeᵗ n `ℕ
  nf-𝔹   : ∀ {n} → NoFreeᵗ n `𝔹
  nf-⇒   : ∀ {n} → NoFreeᵗ n A → NoFreeᵗ n B → NoFreeᵗ n (A ⇒ B)
  nf-∀   : ∀ {n} → NoFreeᵗ (suc n) A → NoFreeᵗ n (`∀ A)

Closedᵗ : Ty → Set
Closedᵗ S = NoFreeᵗ zero S

nofree-ren : ∀ {n ρ} → NoFreeᵗ n S → (∀ Y → Y < n → ρ Y ≡ Y)
  → renameᵗ ρ S ≡ S
nofree-ren (nf-var {X = X} lt) h = cong `_ (h X lt)
nofree-ren nf-ℕ h = refl
nofree-ren nf-𝔹 h = refl
nofree-ren (nf-⇒ a b) h = cong₂ _⇒_ (nofree-ren a h) (nofree-ren b h)
nofree-ren {ρ = ρ} (nf-∀ {n = n} a) h = cong `∀ (nofree-ren a h-ext)
  where
  h-ext : ∀ Y → Y < suc n → extᵗ ρ Y ≡ Y
  h-ext zero lt = refl
  h-ext (suc Y) (s≤s lt) = cong suc (h Y lt)

closed-ren : Closedᵗ S → ∀ ρ → renameᵗ ρ S ≡ S
closed-ren cl ρ = nofree-ren cl (λ Y ())

closed-⇑ : Closedᵗ S → Closedᵗ (renameᵗ suc S)
closed-⇑ cl rewrite closed-ren cl suc = cl

nofree-avoid : ∀ {n} → NoFreeᵗ n S → n ≤ Z → Avoidᵗ Z S
nofree-avoid (nf-var {X = V} lt) le = av-var ne
  where
  ne : ¬ (_ ≡ V)
  ne refl = <-irr (≤-trans lt le)
nofree-avoid nf-ℕ le = av-ℕ
nofree-avoid nf-𝔹 le = av-𝔹
nofree-avoid (nf-⇒ a b) le = av-⇒ (nofree-avoid a le) (nofree-avoid b le)
nofree-avoid (nf-∀ a) le = av-∀ (nofree-avoid a (s≤s le))

closed-avoidᵗ : Closedᵗ S → ∀ Z → Avoidᵗ Z S
closed-avoidᵗ cl Z = nofree-avoid cl z≤n

------------------------------------------------------------------------
-- §3  The renaming and substitution algebras on name lookups
------------------------------------------------------------------------
-- The mirror of `proof.ArrTyping`'s `Renamesᵗ`/`ext-renames`/`wf-ren`.
-- Well-formedness of a TYPE reads only WHICH NAMES are in scope, and
-- in v8 `∋ᵗ` is address-free — so the whole algebra is stated on `∋ᵗ`
-- and not a single address is mentioned.

RenNamesᵗ : Renameᵗ → List StackEnt → List StackEnt → Set
RenNamesᵗ ρ Ss Ss′ = ∀ {Y} → Ss ∋ᵗ Y → Ss′ ∋ᵗ ρ Y

ext-rennames : ∀ {ρ} → RenNamesᵗ ρ Ss Ss′
  → RenNamesᵗ (extᵗ ρ) (bind ∷ Ss) (bind ∷ Ss′)
ext-rennames r t-here = t-here
ext-rennames r (t-there p) = t-there (r p)

wf-rn : ∀ {ρ} → RenNamesᵗ ρ Ss Ss′
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ renameᵗ ρ A
wf-rn r (wf-var n) = wf-var (r n)
wf-rn r wf-ℕ = wf-ℕ
wf-rn r wf-𝔹 = wf-𝔹
wf-rn r (wf-⇒ a b) = wf-⇒ (wf-rn r a) (wf-rn r b)
wf-rn r (wf-∀ a) = wf-∀ (wf-rn (ext-rennames r) a)

wf-⇑ : (Ss ∥ Bs) ⊢ᵗ A → (bind ∷ Ss ∥ Bs) ⊢ᵗ renameᵗ suc A
wf-⇑ = wf-rn (λ p → t-there p)

-- the inverse: a renaming that REFLECTS scope strengthens.  The `all`
-- case needs it, since the slot's type comes back shifted from under
-- the binder assignment.
wf-rn⁻ : ∀ {ρ} {Ss Ss′ : List StackEnt} {Bs Bs′} (S : Ty)
  → (∀ {Z} → Ss′ ∋ᵗ ρ Z → Ss ∋ᵗ Z)
  → (Ss′ ∥ Bs′) ⊢ᵗ renameᵗ ρ S → (Ss ∥ Bs) ⊢ᵗ S
wf-rn⁻ (` Z) h (wf-var p) = wf-var (h p)
wf-rn⁻ `ℕ h wf-ℕ = wf-ℕ
wf-rn⁻ `𝔹 h wf-𝔹 = wf-𝔹
wf-rn⁻ (A ⇒ B) h (wf-⇒ a b) = wf-⇒ (wf-rn⁻ A h a) (wf-rn⁻ B h b)
wf-rn⁻ {ρ = ρ} {Ss = Ss} {Ss′ = Ss′} (`∀ A) h (wf-∀ a) =
  wf-∀ (wf-rn⁻ A h-ext a)
  where
  h-ext : ∀ {Z} → (bind ∷ Ss′) ∋ᵗ extᵗ ρ Z → (bind ∷ Ss) ∋ᵗ Z
  h-ext {zero} p = t-here
  h-ext {suc Z} (t-there p) = t-there (h p)

wf-⇓ : ∀ {Ss Bs S} → (bind ∷ Ss ∥ Bs) ⊢ᵗ renameᵗ suc S → (Ss ∥ Bs) ⊢ᵗ S
wf-⇓ {S = S} w = wf-rn⁻ S un w
  where
  un : ∀ {Z} → (bind ∷ _) ∋ᵗ suc Z → _ ∋ᵗ Z
  un (t-there p) = p

-- the SOURCE is just a stack, since that is all a lookup reads
SubstsᵗM : Substᵗ → List StackEnt → Ctxᵗ → Set
SubstsᵗM σ Ss Γ′ = ∀ {Y} → Ss ∋ᵗ Y → Γ′ ⊢ᵗ σ Y

ext-substs : ∀ {σ} → SubstsᵗM σ Ss (Ss′ ∥ Bs′)
  → SubstsᵗM (extsᵗ σ) (bind ∷ Ss) (bind ∷ Ss′ ∥ Bs′)
ext-substs m t-here = wf-var t-here
ext-substs m (t-there p) = wf-⇑ (m p)

wf-substM : ∀ {σ} → SubstsᵗM σ Ss (Ss′ ∥ Bs′)
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ substᵗ σ A
wf-substM m (wf-var n) = m n
wf-substM m wf-ℕ = wf-ℕ
wf-substM m wf-𝔹 = wf-𝔹
wf-substM m (wf-⇒ a b) = wf-⇒ (wf-substM m a) (wf-substM m b)
wf-substM m (wf-∀ a) = wf-∀ (wf-substM (ext-substs m) a)

-- a closed type is well formed anywhere
Names< : ℕ → List StackEnt → Set
Names< n Ss = ∀ {Y} → Y < n → Ss ∋ᵗ Y

ext-names : ∀ {n} → Names< n Ss → Names< (suc n) (bind ∷ Ss)
ext-names h {zero} lt = t-here
ext-names h {suc Y} (s≤s lt) = t-there (h lt)

wf-nofree : ∀ {n} → NoFreeᵗ n S → Names< n Ss → (Ss ∥ Bs) ⊢ᵗ S
wf-nofree (nf-var lt) h = wf-var (h lt)
wf-nofree nf-ℕ h = wf-ℕ
wf-nofree nf-𝔹 h = wf-𝔹
wf-nofree (nf-⇒ a b) h = wf-⇒ (wf-nofree a h) (wf-nofree b h)
wf-nofree (nf-∀ a) h = wf-∀ (wf-nofree a (ext-names h))

wf-closed : Closedᵗ S → (Ss ∥ Bs) ⊢ᵗ S
wf-closed cl = wf-nofree cl (λ ())

-- transporting along an equation, so that no proof below has to run a
-- `rewrite` whose left-hand side occurs in more places than intended
wf-≡ : A ≡ B → Γ ⊢ᵗ A → Γ ⊢ᵗ B
wf-≡ refl w = w

------------------------------------------------------------------------
-- §4  `closeAt` at a `∀` and across a crossing's shift
------------------------------------------------------------------------

extsᵗ-closeEnv : ∀ X S Z
  → extsᵗ (closeEnv X S) Z ≡ closeEnv (suc X) (renameᵗ suc S) Z
extsᵗ-closeEnv X S zero = refl
extsᵗ-closeEnv X S (suc Z) with X ≟ Z
extsᵗ-closeEnv X S (suc Z) | yes eq
  rewrite eq
        | closeEnv-eq (suc Z) (renameᵗ suc S) = refl
extsᵗ-closeEnv X S (suc Z) | no ne with X <? Z
extsᵗ-closeEnv X S (suc Z) | no ne | yes lt
  rewrite closeEnv-gt (suc X) (renameᵗ suc S) (suc Z) (s≤s lt)
        | suc-pred (pos-of lt) = refl
extsᵗ-closeEnv X S (suc Z) | no ne | no nlt
  rewrite closeEnv-lt (suc X) (renameᵗ suc S) (suc Z)
                      (s≤s (¬<-¬≡-> nlt ne)) = refl

closeAt-∀ : ∀ X S A
  → closeAt X S (`∀ A) ≡ `∀ (closeAt (suc X) (renameᵗ suc S) A)
closeAt-∀ X S A = cong `∀ (substᵗ-cong (extsᵗ-closeEnv X S) A)

-- THE crux for `hide`/`show`.  Both rules state one of their two types
-- as a `shiftAtᵗ Y` rename of the other; on the side WITHOUT the
-- assignment the slot sits at P and the type is closed over P, on the
-- side WITH it the slot sits at `shiftAtᵗ Y P` and the crossing's own
-- name has slid down to `nameSub P Y`.  Every variable but the slot
-- itself is §1's index law; the slot needs the hypothesis, which is
-- §2's `shift-avoid`.
closeEnv-shift : ∀ P Y T
  → renameᵗ (shiftAtᵗ Y) T ≡ renameᵗ (shiftAtᵗ (nameSub P Y)) T
  → ∀ Z → closeEnv (shiftAtᵗ Y P) (renameᵗ (shiftAtᵗ Y) T) (shiftAtᵗ Y Z)
          ≡ renameᵗ (shiftAtᵗ (nameSub P Y)) (closeEnv P T Z)
-- as in `drop-substs`, the decision is taken in a helper: a top-level
-- `with P ≟ Z` would abstract the very `P ≟ Z` that `closeEnv P T Z`
-- is waiting on, and no equation about `closeEnv` could then be
-- applied to the goal
closeEnv-shift P Y T inv Z = go (P ≟ Z)
  where
  go : Dec (P ≡ Z)
     → closeEnv (shiftAtᵗ Y P) (renameᵗ (shiftAtᵗ Y) T) (shiftAtᵗ Y Z)
       ≡ renameᵗ (shiftAtᵗ (nameSub P Y)) (closeEnv P T Z)
  go (yes eq)
    rewrite sym eq
          | closeEnv-eq (shiftAtᵗ Y P) (renameᵗ (shiftAtᵗ Y) T)
          | closeEnv-eq P T = inv
  go (no ne)
    rewrite closeEnv-≢ (shiftAtᵗ Y P) (renameᵗ (shiftAtᵗ Y) T)
              (shiftAtᵗ Y Z) (λ eq → ne (shiftAt-inj Y eq))
          | closeEnv-≢ P T Z ne
          | nameSub-shiftAt Y P Z ne = refl

closeAt-shift : ∀ P Y T A
  → renameᵗ (shiftAtᵗ Y) T ≡ renameᵗ (shiftAtᵗ (nameSub P Y)) T
  → closeAt (shiftAtᵗ Y P) (renameᵗ (shiftAtᵗ Y) T) (renameᵗ (shiftAtᵗ Y) A)
    ≡ renameᵗ (shiftAtᵗ (nameSub P Y)) (closeAt P T A)
closeAt-shift P Y T A inv =
  trans (rename-subst-commute (shiftAtᵗ Y)
          (closeEnv (shiftAtᵗ Y P) (renameᵗ (shiftAtᵗ Y) T)) A)
        (trans (substᵗ-cong (closeEnv-shift P Y T inv) A)
               (sym (rename-subst (shiftAtᵗ (nameSub P Y))
                      (closeEnv P T) A)))

-- The same equation read from the `show`/`unseal` side, where it is
-- the SOURCE that is the rename: there the slot index on the small
-- side is `nameSub Y X` and its type is `renameᵗ (nameSub Y) S`.
closeAt-unshift : ∀ X X″ Y W S S″ A
  → shiftAtᵗ Y X″ ≡ X
  → renameᵗ (shiftAtᵗ Y) S″ ≡ S
  → nameSub X″ Y ≡ W
  → renameᵗ (shiftAtᵗ Y) S″ ≡ renameᵗ (shiftAtᵗ (nameSub X″ Y)) S″
  → closeAt X S (renameᵗ (shiftAtᵗ Y) A)
    ≡ renameᵗ (shiftAtᵗ W) (closeAt X″ S″ A)
closeAt-unshift X X″ Y W S S″ A e₁ e₂ e₃ inv
  rewrite sym e₁ | sym e₂ | sym e₃ = closeAt-shift X″ Y S″ A inv

------------------------------------------------------------------------
-- §5  The relation: dropping the slot
------------------------------------------------------------------------
-- `drop-there` steps past ANY entry.  In v7 it stepped past `bind`s
-- only, which made `DropBindS` express "the slot with nothing but
-- binder assignments above it" — true of the `∀`'s own slot, but NOT
-- preserved by a crossing: a `seal 0 α` inserts an `asgn` above it.

data DropBindS : ℕ → List StackEnt → List StackEnt → Set where
  drop-here  : DropBindS zero (bind ∷ Ss) Ss
  drop-there : ∀ {e} → DropBindS X Ss Ss′
             → DropBindS (suc X) (e ∷ Ss) (e ∷ Ss′)

drop-uniqueS : DropBindS X Ss Ss′ → DropBindS X Ss Ss″ → Ss′ ≡ Ss″
drop-uniqueS drop-here drop-here = refl
drop-uniqueS (drop-there {e = e} d₁) (drop-there d₂) =
  cong (e ∷_) (drop-uniqueS d₁ d₂)

drop-≡ : X ≡ Y → DropBindS X Ss Ss′ → DropBindS Y Ss Ss′
drop-≡ refl d = d

-- The read-back recursion enters `∀ᴿ`s, and each one pushes a binder
-- assignment on BOTH sides of the drop: `n` counts them, so a `` `ᵛ ``
-- bound by one of them names a `bind` strictly above the slot.
data DropUnder : ℕ → ℕ → List StackEnt → List StackEnt → Set where
  du-base : DropBindS X Ss Ss′ → DropUnder zero X Ss Ss′
  du-bind : DropUnder n X Ss Ss′
          → DropUnder (suc n) (suc X) (bind ∷ Ss) (bind ∷ Ss′)

du-drop : DropUnder n X Ss Ss′ → DropBindS X Ss Ss′
du-drop (du-base d) = d
du-drop (du-bind du) = drop-there (du-drop du)

du-bv : DropUnder n X Ss Ss′ → Ss ∋b Z at i → i < n → Z < X
du-bv (du-base d) b ()
du-bv (du-bind du) b-here lt = s≤s z≤n
du-bv (du-bind du) (b-bind p) (s≤s lt) = s≤s (du-bv du p lt)

------------------------------------------------------------------------
-- §6  The side conditions
------------------------------------------------------------------------
-- (1) `RepsWf` — every representation a `∋r` reaches has its `` `ᵛ ``s
-- bound by its OWN `∀ᴿ`s.  It is what lets `∋r` and the read-back `⇓`
-- travel across the drop with the SAME `R`: `seal`/`unseal` read their
-- type off a representation the syntax does not carry, so `R` cannot be
-- renamed by `substAnn` — and the drop REMOVES one of the `bind`s that
-- `read-bv` counts, so a `` `ᵛ `` escaping `R`'s own `∀ᴿ`s would have
-- to move.
--
-- INDEXED BY THE BASE.  Quantifying over every context makes this
-- REFUTABLE: `nuBind (`ᵛ 0)` is a legal base entry and `r-here`
-- reaches it, but `⇑ᴿᵉ (`ᵛ 0)` is not `⊢ᴿ[ 0 ]`-well-formed.  A
-- conversion never changes the base (`conv-base`), so one base serves
-- the whole recursion, and at the empty base it is just `StoreOk`.
RepsWf : Store → List BaseEnt → Set
RepsWf Sg Bs =
  ∀ {Ss α R} → Sg ∣ (Ss ∥ Bs) ∋r α := R → Sg ∣ (Ss ∥ Bs) ⊢ᴿ R

-- `slotOutElt`, `tyOutElt`, `slotOut` and `tyOut` — the slot index and
-- the slot's type, stepped one element (one spine) outward — are
-- `substAnn`'s own threading functions and live with it in
-- strong.Conversion.
--
-- (2) `SAvoids`, the weakening of `Closedᵗ S`.  `S` lives in the
-- frame with the slot ALREADY REMOVED, where the crossing's name is
-- not Y but `nameSub X Y` — while `tyOutElt` re-expresses S at Y.
-- The two renamings agree off that one name, which is what each
-- `Avoidᵗ` buys:
--
--   `seal`/`hide`     the frame GAINS an entry at `nameSub X Y`, and
--                     `shiftAtᵗ Y` = `shiftAtᵗ (nameSub X Y)` off it.
--   `unseal`/`show`   the frame LOSES the entry at `nameSub X Y`, and
--                     that rename is faithful only off it; `nameSub Y`
--                     = `nameSub (nameSub X Y)` off Y, whence the
--                     second `Avoidᵗ`.
--
-- Only `hide`, `unseal` and `show` spend theirs on an ANNOTATION:
-- `seal`'s is spent only on carrying `S`'s well-formedness outward,
-- which a monotonicity argument could do instead.  It is stated
-- anyway, so that the two elements `tyOutElt` treats alike ask for
-- the same thing.
--
-- `sa-fun` asks for ONE equation, not two: `t` runs the element's
-- interior → exterior and `s` runs back, so the round trip
-- `tyOut s (tyOut t S)` must land on `S` again.  (The INDEX round trip
-- is the same statement one level down, and §8b derives it — that is
-- the difference between the two conditions.)
mutual
  data SAvoidsElt : ℕ → Ty → ConvElt → Set where
    sa-seal   : ∀ {X S Y α} → Avoidᵗ (nameSub X Y) S
              → SAvoidsElt X S (seal Y α)
    sa-unseal : ∀ {X S Y α} → Avoidᵗ Y S → Avoidᵗ (nameSub X Y) S
              → SAvoidsElt X S (unseal Y α)
    sa-hide   : ∀ {X S Y α} → Avoidᵗ (nameSub X Y) S
              → SAvoidsElt X S (hide Y α)
    sa-show   : ∀ {X S Y α} → Avoidᵗ Y S → Avoidᵗ (nameSub X Y) S
              → SAvoidsElt X S (show Y α)
    sa-fun    : ∀ {X S s t} → SAvoids (slotOut t X) (tyOut t S) s
              → SAvoids X S t
              → tyOut s (tyOut t S) ≡ S
              → SAvoidsElt X S (s ↦ t)
    sa-all    : ∀ {X S s} → SAvoids (suc X) (renameᵗ suc S) s
              → tyOut s (renameᵗ suc S) ≡ renameᵗ suc S
              → SAvoidsElt X S (all s)

  data SAvoids : ℕ → Ty → Conv → Set where
    sa-id   : ∀ {X S A} → SAvoids X S (id A)
    sa-cons : ∀ {X S ĉ c} → SAvoidsElt X S ĉ
            → SAvoids (slotOutElt ĉ X) (tyOutElt ĉ S) c
            → SAvoids X S (ĉ ∷ᶜ c)

-- THE WORD THAT KILLED THE OLD `↦` EQUATION.  Both components of this
-- `↦` are well typed between these two contexts, and the slot does NOT
-- come back across either one: `t` moves it 1 ↦ 0 and `s` moves it
-- back 0 ↦ 1.  The old `substAnnElt X S (s ↦ t) = substAnn X S s ↦
-- substAnn X S t` handed `s` the index 1 all the same, and needed
-- `StepFix`'s `slotOut t X ≡ X` to paper over it; the stepped equation
-- hands `s` the index `slotOut t X = 0`, and §10b checks that
-- `substAnn` then TYPES this word.
private
  Sgₓ : Store
  Sgₓ = `ℕᴿ ∷ []

  Γᵢₓ Γₑₓ : Ctxᵗ
  Γᵢₓ = asgn (lvl zero) ∷ bind ∷ [] ∥ []
  Γₑₓ = bind ∷ [] ∥ []

  scₓ : Sgₓ ∣ Γₑₓ ∋a lvl zero
  scₓ = a-lvl l-here

  naₓ : NotAssigned Γₑₓ (lvl zero)
  naₓ (n-skip-bind ())

  popₓ : Γᵢₓ ▷ zero := lvl zero ⇒ Γₑₓ
  popₓ = pop-here

  -- the slot really is there, with an `asgn` above it
  dropₓ : DropBindS 1 (asgn (lvl zero) ∷ bind ∷ []) (asgn (lvl zero) ∷ [])
  dropₓ = drop-there drop-here

  tₓ sₓ : Conv
  tₓ = show zero (lvl zero) ∷ᶜ id `ℕ
  sₓ = hide zero (lvl zero) ∷ᶜ id `ℕ

  ⊢tₓ : Sgₓ ∣ Γᵢₓ ⊢ tₓ ∶ `ℕ ⇝ `ℕ ⊣ Γₑₓ
  ⊢tₓ = conv-cons (conv-show scₓ wf-ℕ popₓ naₓ) (conv-id wf-ℕ)

  ⊢sₓ : Sgₓ ∣ Γₑₓ ⊢ sₓ ∶ `ℕ ⇝ `ℕ ⊣ Γᵢₓ
  ⊢sₓ = conv-cons (conv-hide scₓ wf-ℕ popₓ naₓ) (conv-id wf-ℕ)

  ⊢funₓ : Sgₓ ∣ Γᵢₓ ⊢̂ (sₓ ↦ tₓ) ∶ `ℕ ⇒ `ℕ ⇝ `ℕ ⇒ `ℕ ⊣ Γₑₓ
  ⊢funₓ = conv-fun ⊢sₓ ⊢tₓ

  slot-movesₓ : ¬ (slotOut tₓ 1 ≡ 1)
  slot-movesₓ ()

-- THE BRIDGE the callers with a closed type argument use.  A closed
-- type avoids every name and is fixed by every renaming, so all of
-- `SAvoids` — the `Avoidᵗ`s and the two `tyOut` equations — is free.
mutual
  closed-avoidsElt : ∀ {X S} ĉ → Closedᵗ S → SAvoidsElt X S ĉ
  closed-avoidsElt (seal Y α) cl = sa-seal (closed-avoidᵗ cl _)
  closed-avoidsElt (unseal Y α) cl =
    sa-unseal (closed-avoidᵗ cl _) (closed-avoidᵗ cl _)
  closed-avoidsElt (hide Y α) cl = sa-hide (closed-avoidᵗ cl _)
  closed-avoidsElt (show Y α) cl =
    sa-show (closed-avoidᵗ cl _) (closed-avoidᵗ cl _)
  closed-avoidsElt (s ↦ t) cl =
    sa-fun (closed-avoids s (closed-tyOutC t cl)) (closed-avoids t cl)
           (trans (cong (tyOut s) (closed-tyOut t cl)) (closed-tyOut s cl))
  closed-avoidsElt {S = S} (all s) cl =
    sa-all (closed-avoids s (closed-⇑ cl)) (closed-tyOut s (closed-⇑ cl))

  closed-avoids : ∀ {X S} c → Closedᵗ S → SAvoids X S c
  closed-avoids (id A) cl = sa-id
  closed-avoids {S = S} (ĉ ∷ᶜ c) cl =
    sa-cons (closed-avoidsElt ĉ cl)
            (closed-avoids c (closed-tyElt ĉ cl))

  closed-tyElt : ∀ {S} ĉ → Closedᵗ S → Closedᵗ (tyOutElt ĉ S)
  closed-tyElt {S = S} (seal Y α) cl
    rewrite closed-ren cl (shiftAtᵗ Y) = cl
  closed-tyElt {S = S} (unseal Y α) cl
    rewrite closed-ren cl (nameSub Y) = cl
  closed-tyElt {S = S} (hide Y α) cl
    rewrite closed-ren cl (shiftAtᵗ Y) = cl
  closed-tyElt {S = S} (show Y α) cl
    rewrite closed-ren cl (nameSub Y) = cl
  closed-tyElt (s ↦ t) cl = closed-tyOutC t cl
  closed-tyElt {S = S} (all s) cl
    rewrite closed-tyOut s (closed-⇑ cl) | ren-sub0 S = cl

  closed-tyEltEq : ∀ {S} ĉ → Closedᵗ S → tyOutElt ĉ S ≡ S
  closed-tyEltEq (seal Y α) cl = closed-ren cl (shiftAtᵗ Y)
  closed-tyEltEq (unseal Y α) cl = closed-ren cl (nameSub Y)
  closed-tyEltEq (hide Y α) cl = closed-ren cl (shiftAtᵗ Y)
  closed-tyEltEq (show Y α) cl = closed-ren cl (nameSub Y)
  closed-tyEltEq (s ↦ t) cl = closed-tyOut t cl
  closed-tyEltEq {S = S} (all s) cl =
    trans (cong (renameᵗ (nameSub zero)) (closed-tyOut s (closed-⇑ cl)))
          (ren-sub0 S)

  closed-tyOut : ∀ {S} c → Closedᵗ S → tyOut c S ≡ S
  closed-tyOut (id A) cl = refl
  closed-tyOut (ĉ ∷ᶜ c) cl =
    trans (closed-tyOut c (closed-tyElt ĉ cl)) (closed-tyEltEq ĉ cl)

  closed-tyOutC : ∀ {S} c → Closedᵗ S → Closedᵗ (tyOut c S)
  closed-tyOutC c cl rewrite closed-tyOut c cl = cl

------------------------------------------------------------------------
-- §7  Transporting the lookups across the drop
------------------------------------------------------------------------

-- The slot is a `bind`, and only an `asgn` assigns an address, so no
-- name lookup lands on the slot.
slot-∌ : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n X := α → ⊥
slot-∌ drop-here ()
slot-∌ (drop-there d) (n-skip-asgn p) = slot-∌ d p
slot-∌ (drop-there d) (n-skip-bind p) = slot-∌ d p

slot-≢ : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n Y := α → ¬ (X ≡ Y)
slot-≢ d n refl = slot-∌ d n

-- A name lookup survives the drop with the SAME address: the drop is a
-- stack operation and v8 renames no address across the stack.
∋n-dropS : DropBindS X Ss Ss′ → (Ss ∥ Bs) ∋n Y := α
  → (Ss′ ∥ Bs) ∋n nameSub X Y := α
∋n-dropS drop-here (n-skip-bind {X = Y} p)
  rewrite nameSub-pred Y = p
∋n-dropS (drop-there d) n-here-asgn = n-here-asgn
∋n-dropS (drop-there {X = X} d) (n-skip-asgn {X = Y} p)
  rewrite nameSub-suc X Y = n-skip-asgn (∋n-dropS d p)
∋n-dropS (drop-there {X = X} d) (n-skip-bind {X = Y} p)
  rewrite nameSub-suc X Y = n-skip-bind (∋n-dropS d p)

-- The same for a variable merely IN SCOPE, which is what `⊢ᵗ` reads.
∋ᵗ-dropS : DropBindS X Ss Ss′ → Ss ∋ᵗ Y → ¬ (X ≡ Y)
  → Ss′ ∋ᵗ nameSub X Y
∋ᵗ-dropS drop-here t-here ne = ⊥-elim (ne refl)
∋ᵗ-dropS drop-here (t-there {X = Y} p) ne
  rewrite nameSub-pred Y = p
∋ᵗ-dropS (drop-there d) t-here ne = t-here
∋ᵗ-dropS (drop-there {X = X} d) (t-there {X = Y} p) ne
  rewrite nameSub-suc X Y =
  t-there (∋ᵗ-dropS d p (λ eq → ne (cong suc eq)))

-- A `∀`-bound variable: the drop removes the X-th entry, so a variable
-- whose name is STRICTLY BELOW the slot keeps both its name and the
-- binder it names.
∋b-dropS : DropBindS X Ss Ss′ → Ss ∋b Z at i → Z < X
  → Ss′ ∋b nameSub X Z at i
∋b-dropS drop-here b ()
∋b-dropS (drop-there d) b-here lt = b-here
∋b-dropS (drop-there {X = X} d) (b-asgn {X = Z} p) (s≤s lt)
  rewrite nameSub-suc X Z = b-asgn (∋b-dropS d p lt)
∋b-dropS (drop-there {X = X} d) (b-bind {X = Z} p) (s≤s lt)
  rewrite nameSub-suc X Z = b-bind (∋b-dropS d p lt)

-- the other direction, for `NotAssigned`: putting the slot back
∋n-undropS : DropBindS X Ss Ss′ → (Ss′ ∥ Bs) ∋n Y := α
  → (Ss ∥ Bs) ∋n shiftAtᵗ X Y := α
∋n-undropS drop-here p = n-skip-bind p
∋n-undropS (drop-there d) n-here-asgn = n-here-asgn
∋n-undropS (drop-there d) (n-skip-asgn p) =
  n-skip-asgn (∋n-undropS d p)
∋n-undropS (drop-there d) (n-skip-bind p) =
  n-skip-bind (∋n-undropS d p)

notasgn-drop : DropBindS X Ss Ss′ → NotAssigned (Ss ∥ Bs) α
  → NotAssigned (Ss′ ∥ Bs) α
notasgn-drop d na q = na (∋n-undropS d q)

-- well-formedness: the substitution algebra instantiated at the drop.
-- `S` is well formed in the context the drop LANDS in — that is the
-- frame it lives in, and the premise the spine threads.
drop-substs : ∀ {Bs} → DropBindS X Ss Ss′ → (Ss′ ∥ Bs) ⊢ᵗ S
  → SubstsᵗM (closeEnv X S) Ss (Ss′ ∥ Bs)
-- the decision is taken in a helper: a `with X ≟ Y` at the top level
-- would abstract the very `X ≟ Y` that `closeEnv X S Y` is waiting on,
-- and no equation about `closeEnv` could then be applied to the goal
drop-substs {X = X} {S = S} d wfS {Y = Y} n = go (X ≟ Y)
  where
  go : Dec (X ≡ Y) → _ ⊢ᵗ closeEnv X S Y
  go (yes eq) rewrite eq | closeEnv-eq Y S = wfS
  go (no ne) rewrite closeEnv-≢ X S Y ne = wf-var (∋ᵗ-dropS d n ne)

wf-drop : DropBindS X Ss Ss′ → (Ss′ ∥ Bs) ⊢ᵗ S → (Ss ∥ Bs) ⊢ᵗ A
  → (Ss′ ∥ Bs) ⊢ᵗ closeAt X S A
wf-drop d wfS = wf-substM (drop-substs d wfS)

-- A represented address reads the STORE or the BASE, and the drop is a
-- pure STACK operation, so it touches neither.
∋r-drop : Sg ∣ (Ss ∥ Bs) ∋r α := R → Sg ∣ (Ss′ ∥ Bs) ∋r α := R
∋r-drop = ∋r-restk

-- The read-back travels with its representation UNCHANGED, provided
-- R's bound variables are its own.
read-drop : ∀ {Sg X S n Γᴿ Ss Ss′ Bs R A}
  → DropUnder n X Ss Ss′
  → Sg ∣ Γᴿ ⊢ᴿ[ n ] R → Sg ∣ (Ss ∥ Bs) ⊢ R ⇓ A
  → Sg ∣ (Ss′ ∥ Bs) ⊢ R ⇓ closeAt X S A
read-drop {X = X} {S = S} du (wfᴿ-var a) (read-var {X = Z} n)
  rewrite closeEnv-≢ X S Z (slot-≢ (du-drop du) n) =
  read-var (∋n-dropS (du-drop du) n)
read-drop {X = X} {S = S} du (wfᴿ-bv i<n) (read-bv {X = Z} b)
  rewrite closeEnv-≢ X S Z (>-≢ (du-bv du b i<n)) =
  read-bv (∋b-dropS (du-drop du) b (du-bv du b i<n))
read-drop du wfᴿ-ℕ read-ℕ = read-ℕ
read-drop du wfᴿ-𝔹 read-𝔹 = read-𝔹
read-drop du (wfᴿ-⇒ wr wt) (read-⇒ r t) =
  read-⇒ (read-drop du wr r) (read-drop du wt t)
read-drop {X = X} {S = S} du (wfᴿ-∀ wr) (read-∀ {A = A} r)
  rewrite closeAt-∀ X S A = read-∀ (read-drop (du-bind du) wr r)

------------------------------------------------------------------------
-- §8  Transporting the pop judgment
------------------------------------------------------------------------
-- Both directions take the INTERIOR drop and produce the exterior one,
-- at the slot index the crossing moves it to — which is exactly
-- `slotOutElt`'s value — together with the pop the crossing performs
-- in the DROPPED frame, whose name has slid to `nameSub X Y`.

pop-∋n : Γ ▷ Y := α ⇒ Γ′ → Γ ∋n Y := α
pop-∋n pop-here = n-here-asgn
pop-∋n (pop-bind p) = n-skip-bind (pop-∋n p)

pop-shift : ∀ {Ss Ss′ Bs} → (Ss ∥ Bs) ▷ W := α ⇒ (Ss′ ∥ Bs)
  → Ss′ ∋ᵗ Z → Ss ∋ᵗ shiftAtᵗ W Z
pop-shift pop-here p = t-there p
pop-shift (pop-bind q) t-here = t-here
pop-shift (pop-bind q) (t-there p) = t-there (pop-shift q p)

pop-sub : ∀ {Ss Ss′ Bs} → (Ss ∥ Bs) ▷ W := α ⇒ (Ss′ ∥ Bs)
  → Ss ∋ᵗ Z → ¬ (W ≡ Z) → Ss′ ∋ᵗ nameSub W Z
pop-sub pop-here t-here ne = ⊥-elim (ne refl)
pop-sub pop-here (t-there {X = Z} p) ne rewrite nameSub-pred Z = p
pop-sub (pop-bind q) t-here ne = t-here
pop-sub (pop-bind {X = W} q) (t-there {X = Z} p) ne
  rewrite nameSub-suc W Z =
  t-there (pop-sub q p (λ eq → ne (cong suc eq)))

ext-nameSub : ∀ W Z → extᵗ (nameSub W) Z ≡ nameSub (suc W) Z
ext-nameSub W zero = refl
ext-nameSub W (suc Z) = sym (nameSub-suc W Z)

wf-pop-shift : ∀ {Ss Ss′ Bs} → (Ss ∥ Bs) ▷ W := α ⇒ (Ss′ ∥ Bs)
  → (Ss′ ∥ Bs) ⊢ᵗ S → (Ss ∥ Bs) ⊢ᵗ renameᵗ (shiftAtᵗ W) S
wf-pop-shift p = wf-rn (pop-shift p)

wf-pop-sub : ∀ {Ss Ss′ Bs} → Avoidᵗ W S
  → (Ss ∥ Bs) ▷ W := α ⇒ (Ss′ ∥ Bs)
  → (Ss ∥ Bs) ⊢ᵗ S → (Ss′ ∥ Bs) ⊢ᵗ renameᵗ (nameSub W) S
wf-pop-sub (av-var ne) p (wf-var q) = wf-var (pop-sub p q ne)
wf-pop-sub av-ℕ p wf-ℕ = wf-ℕ
wf-pop-sub av-𝔹 p wf-𝔹 = wf-𝔹
wf-pop-sub (av-⇒ a b) p (wf-⇒ wa wb) =
  wf-⇒ (wf-pop-sub a p wa) (wf-pop-sub b p wb)
wf-pop-sub {W = W} (av-∀ {A = A} a) p (wf-∀ wa)
  rewrite rename-cong (ext-nameSub W) A =
  wf-∀ (wf-pop-sub a (pop-bind p) wa)

-- POP: the crossing removes its assignment going inward (`seal`,
-- `hide`), so the EXTERIOR has it and the slot slides up past it.
drop-pop : ∀ {Ssᵢ Ssᵢ′ Ssₑ Bs} → DropBindS X Ssᵢ Ssᵢ′
  → (Ssₑ ∥ Bs) ▷ Y := α ⇒ (Ssᵢ ∥ Bs)
  → Σ[ Ssₑ′ ∈ List StackEnt ]
      (DropBindS (shiftAtᵗ Y X) Ssₑ Ssₑ′
       × ((Ssₑ′ ∥ Bs) ▷ nameSub X Y := α ⇒ (Ssᵢ′ ∥ Bs)))
drop-pop d pop-here = _ , drop-there d , pop-here
drop-pop drop-here (pop-bind {X = Y} p)
  rewrite nameSub-pred Y = _ , drop-here , p
drop-pop (drop-there {X = X} d) (pop-bind {X = Y} p) with drop-pop d p
drop-pop (drop-there {X = X} d) (pop-bind {X = Y} p) | Ssₑ′ , d′ , p′
  rewrite nameSub-suc X Y = _ , drop-there d′ , pop-bind p′

-- PUSH: the crossing ADDS its assignment going inward (`unseal`,
-- `show`), so the INTERIOR has it and the slot slides down.  The `X <
-- Y` v7 assumed here is now DERIVED: `pop-here` forces the interior's
-- head to be the `asgn`, which the slot's own `drop-here` cannot be.
drop-push : ∀ {Ssᵢ Ssᵢ′ Ssₑ Bs} → DropBindS X Ssᵢ Ssᵢ′
  → (Ssᵢ ∥ Bs) ▷ Y := α ⇒ (Ssₑ ∥ Bs)
  → Σ[ Ssₑ′ ∈ List StackEnt ]
      (DropBindS (nameSub Y X) Ssₑ Ssₑ′
       × ((Ssᵢ′ ∥ Bs) ▷ nameSub X Y := α ⇒ (Ssₑ′ ∥ Bs)))
drop-push (drop-there {X = X} d) pop-here
  rewrite nameSub-pred X = _ , d , pop-here
drop-push drop-here (pop-bind {X = Y} p)
  rewrite nameSub-pred Y = _ , drop-here , p
drop-push (drop-there {X = X} d) (pop-bind {X = Y} p) with drop-push d p
drop-push (drop-there {X = X} d) (pop-bind {X = Y} p) | Ssₑ′ , d′ , p′
  rewrite nameSub-suc X Y | nameSub-suc Y X =
  _ , drop-there d′ , pop-bind p′

------------------------------------------------------------------------
-- §8b  The slot's BIND RANK — what replaced `StepFix`
------------------------------------------------------------------------
-- An atomic element inserts or removes an `asgn`, a `↦` delegates, and
-- an `all` keeps a `bind` at the head on both sides: no element touches
-- the BIND SKELETON of its two contexts.  So count the binds strictly
-- below the slot — `BRank X Ss n` — and that count is invariant along
-- the whole spine (`brank-conv`), while the rank determines the index
-- back (`brank-inj`).
--
-- That is the whole content of the deleted `StepFix`.  A `↦`'s two
-- components run between the SAME two contexts, so `t` sends the slot
-- to the bind of rank n in Ssₑ and `s` sends THAT back to the bind of
-- rank n in Ssᵢ — the slot itself.  No premise required.

data BRank : ℕ → List StackEnt → ℕ → Set where
  br-here : BRank zero (bind ∷ Ss) zero
  br-asgn : BRank X Ss n → BRank (suc X) (asgn α ∷ Ss) n
  br-bind : BRank X Ss n → BRank (suc X) (bind ∷ Ss) (suc n)

-- the slot is a `bind`, so it HAS a rank
drop-brank : DropBindS X Ss Ss′ → Σ[ n ∈ ℕ ] BRank X Ss n
drop-brank drop-here = zero , br-here
drop-brank (drop-there {e = asgn α} d) with drop-brank d
drop-brank (drop-there {e = asgn α} d) | n , b = n , br-asgn b
drop-brank (drop-there {e = bind} d) with drop-brank d
drop-brank (drop-there {e = bind} d) | n , b = suc n , br-bind b

brank-inj : BRank X Ss n → BRank Z Ss n → X ≡ Z
brank-inj br-here br-here = refl
brank-inj (br-asgn b₁) (br-asgn b₂) = cong suc (brank-inj b₁ b₂)
brank-inj (br-bind b₁) (br-bind b₂) = cong suc (brank-inj b₁ b₂)

-- under an `all`'s binder the rank is a successor, so the index is too
-- — which is what makes `slotOutElt (all s) X = slotOut s (suc X) ∸ 1`
-- the right stepping
brank-bind-inv : BRank W (bind ∷ Ss) (suc n)
  → Σ[ Z ∈ ℕ ] (W ≡ suc Z × BRank Z Ss n)
brank-bind-inv (br-bind b) = _ , refl , b

brank-bind-zero : BRank W (bind ∷ Ss) zero → W ≡ zero
brank-bind-zero br-here = refl

-- a crossing that ADDS its assignment going outward slides the slot up
brank-pop-shift : ∀ {Ss Ss′ Bs} → (Ss ∥ Bs) ▷ Y := α ⇒ (Ss′ ∥ Bs)
  → BRank X Ss′ n → BRank (shiftAtᵗ Y X) Ss n
brank-pop-shift pop-here b = br-asgn b
brank-pop-shift (pop-bind p) br-here = br-here
brank-pop-shift (pop-bind p) (br-bind b) = br-bind (brank-pop-shift p b)

-- ... and one that REMOVES it slides the slot down
brank-pop-sub : ∀ {Ss Ss′ Bs} → (Ss ∥ Bs) ▷ Y := α ⇒ (Ss′ ∥ Bs)
  → BRank X Ss n → BRank (nameSub Y X) Ss′ n
brank-pop-sub pop-here (br-asgn {X = Z} b) rewrite nameSub-pred Z = b
brank-pop-sub (pop-bind {X = Y} p) br-here
  rewrite nameSub-le (suc Y) zero (λ ()) = br-here
brank-pop-sub (pop-bind {X = Y} p) (br-bind {X = Z} b)
  rewrite nameSub-suc Y Z = br-bind (brank-pop-sub p b)

mutual
  brankElt-out : ∀ {Sg Ssᵢ Ssₑ Bs ĉ A B X n}
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → BRank X Ssᵢ n → BRank (slotOutElt ĉ X) Ssₑ n
  brankElt-out (conv-seal rep rd p) b = brank-pop-shift p b
  brankElt-out (conv-unseal rep rd p na) b = brank-pop-sub p b
  brankElt-out (conv-hide sc wf p na) b = brank-pop-shift p b
  brankElt-out (conv-show sc wf p na) b = brank-pop-sub p b
  -- the element spans what its COVARIANT component spans
  brankElt-out (conv-fun ⊢s ⊢t) b = brank-conv ⊢t b
  brankElt-out (conv-all ⊢s) b with brank-conv ⊢s (br-bind b)
  brankElt-out (conv-all ⊢s) b | b′ with brank-bind-inv b′
  brankElt-out (conv-all ⊢s) b | b′ | Z , eq , bZ rewrite eq = bZ

  brank-conv : ∀ {Sg Ssᵢ Ssₑ Bs c A B X n}
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → BRank X Ssᵢ n → BRank (slotOut c X) Ssₑ n
  brank-conv (conv-id wf) b = b
  brank-conv (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) b with conv-base tl
  brank-conv (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) b | refl =
    brank-conv tl (brankElt-out hd b)

-- THE `↦` FACT: the round trip returns the slot index.
slotOut-round : ∀ {Sg Ssᵢ Ssₑ Bs s t A B C D X Ssᵢ′}
  → Sg ∣ (Ssₑ ∥ Bs) ⊢ s ∶ C ⇝ A ⊣ (Ssᵢ ∥ Bs)
  → Sg ∣ (Ssᵢ ∥ Bs) ⊢ t ∶ B ⇝ D ⊣ (Ssₑ ∥ Bs)
  → DropBindS X Ssᵢ Ssᵢ′
  → slotOut s (slotOut t X) ≡ X
slotOut-round ⊢s ⊢t d with drop-brank d
slotOut-round ⊢s ⊢t d | n , b =
  brank-inj (brank-conv ⊢s (brank-conv ⊢t b)) b

-- ... and the `∀`-slot fact the callers use: a conversion between two
-- contexts that both begin with a `bind` fixes the index zero.
slotOut-bind : ∀ {Sg Ssᵢ Ssₑ Bs c A B}
  → Sg ∣ (bind ∷ Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (bind ∷ Ssₑ ∥ Bs)
  → slotOut c zero ≡ zero
slotOut-bind ⊢c = brank-bind-zero (brank-conv ⊢c br-here)

------------------------------------------------------------------------
-- §9  The theorem
------------------------------------------------------------------------
-- Stated so that the INTERIOR drop is given and the EXTERIOR one is
-- produced, at the stepped slot index: that is the direction in which
-- `substAnn` itself threads, so the recursion never has to guess where
-- the slot has got to.  `conv-fun`, whose two components run in
-- opposite directions, closes the circle with `drop-uniqueS` — which
-- is legitimate because §8b's `slotOut-round` DERIVES that the two
-- components return the slot index to itself.

-- transports along the `slotOut`/`SAvoids` equations
conv-≡ : ∀ {Sg Γ Γ′ c A B B′} → B ≡ B′
  → Sg ∣ Γ ⊢ c ∶ A ⇝ B ⊣ Γ′ → Sg ∣ Γ ⊢ c ∶ A ⇝ B′ ⊣ Γ′
conv-≡ refl ty = ty

conv-ctx-≡ : ∀ {Sg Γ Γ′ Γ″ c A B} → Γ′ ≡ Γ″
  → Sg ∣ Γ ⊢ c ∶ A ⇝ B ⊣ Γ′ → Sg ∣ Γ ⊢ c ∶ A ⇝ B ⊣ Γ″
conv-ctx-≡ refl ty = ty

convElt-≡ : ∀ {Sg Γ Γ′ ḑ A A′ B} → A ≡ A′
  → Sg ∣ Γ ⊢̂ ḑ ∶ A ⇝ B ⊣ Γ′ → Sg ∣ Γ ⊢̂ ḑ ∶ A′ ⇝ B ⊣ Γ′
convElt-≡ refl ty = ty

mutual
  substAnnElt-typing : ∀ {Sg X S ĉ A B Ssᵢ Ssᵢ′ Ssₑ Bs}
    → RepsWf Sg Bs → SAvoidsElt X S ĉ
    → (Ssᵢ′ ∥ Bs) ⊢ᵗ S → DropBindS X Ssᵢ Ssᵢ′
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Ssₑ′ ∈ List StackEnt ]
        (DropBindS (slotOutElt ĉ X) Ssₑ Ssₑ′
         × ((Ssₑ′ ∥ Bs) ⊢ᵗ tyOutElt ĉ S)
         × Sg ∣ (Ssᵢ′ ∥ Bs) ⊢̂ substAnnElt X S ĉ
             ∶ closeAt X S A
             ⇝ closeAt (slotOutElt ĉ X) (tyOutElt ĉ S) B
             ⊣ (Ssₑ′ ∥ Bs))

  -- a `seal`: the assignment is the EXTERIOR's, and the element's
  -- target IS its name, which slides down to `nameSub X Y`
  substAnnElt-typing {X = X} {S = S} rw (sa-seal {Y = Y} av) wfS d
    (conv-seal rep rd p) with drop-pop d p
  substAnnElt-typing {X = X} {S = S} rw (sa-seal {Y = Y} av) wfS d
    (conv-seal rep rd p) | Ssₑ′ , dₑ , p′
    rewrite closeEnv-≢ (shiftAtᵗ Y X) (renameᵗ (shiftAtᵗ Y) S) Y
              (slot-≢ dₑ (pop-∋n p))
          | nameSub-shift X Y =
    Ssₑ′ , dₑ
    , wf-≡ (sym (shift-avoid Y (nameSub X Y) av (nameSub-cases X Y)))
        (wf-pop-shift p′ wfS)
    , conv-seal (∋r-drop rep) (read-drop (du-base d) (rw rep) rd) p′

  -- an `unseal`: dual, and its freshness side condition comes back
  substAnnElt-typing {X = X} {S = S} rw
    (sa-unseal {Y = Y} avY avW) wfS d (conv-unseal rep rd p na)
    with drop-push d p
  substAnnElt-typing {X = X} {S = S} rw
    (sa-unseal {Y = Y} avY avW) wfS d (conv-unseal rep rd p na)
    | Ssₑ′ , dₑ , p′
    rewrite closeEnv-≢ X S Y (slot-≢ d (pop-∋n p)) =
    Ssₑ′ , dₑ
    , wf-≡ (sym (sub-avoid-cong Y (nameSub X Y) avY (nameSub-cases X Y)))
        (wf-pop-sub avW p′ wfS)
    , conv-unseal (∋r-drop rep)
        (read-drop (du-base dₑ) (rw rep) rd) p′ (notasgn-drop dₑ na)

  -- a `hide`: its target is a `shiftAtᵗ Y` rename, and `closeAt-shift`
  -- slides the shift's cutoff down with the crossing's name
  substAnnElt-typing {X = X} {S = S} rw (sa-hide {Y = Y} av) wfS d
    (conv-hide {A = A} sc wf p na) with drop-pop d p
  substAnnElt-typing {X = X} {S = S} rw (sa-hide {Y = Y} av) wfS d
    (conv-hide {A = A} sc wf p na) | Ssₑ′ , dₑ , p′
    rewrite closeAt-shift X Y S A
              (shift-avoid Y (nameSub X Y) av (nameSub-cases X Y)) =
    Ssₑ′ , dₑ
    , wf-≡ (sym (shift-avoid Y (nameSub X Y) av (nameSub-cases X Y)))
        (wf-pop-shift p′ wfS)
    , conv-hide (∋a-restk sc) (wf-drop d wfS wf) p′ (notasgn-drop d na)

  -- a `show`: the SOURCE is the rename, so the same equation is used
  -- in the other position, with the slot taken on the small side
  substAnnElt-typing {X = X} {S = S} rw (sa-show {Y = Y} avY avW) wfS
    d (conv-show {A = A} sc wf p na) with drop-push d p
  substAnnElt-typing {X = X} {S = S} rw (sa-show {Y = Y} avY avW) wfS
    d (conv-show {A = A} sc wf p na) | Ssₑ′ , dₑ , p′ =
    Ssₑ′ , dₑ , wfS″
    , convElt-≡ (sym eq)
        (conv-show (∋a-restk sc) (wf-drop dₑ wfS″ wf) p′
          (notasgn-drop dₑ na))
    where
    ne : ¬ (X ≡ Y)
    ne = slot-≢ d (pop-∋n p)
    wfS″ : _ ⊢ᵗ renameᵗ (nameSub Y) S
    wfS″ = wf-≡ (sym (sub-avoid-cong Y (nameSub X Y) avY
                       (nameSub-cases X Y)))
             (wf-pop-sub avW p′ wfS)
    st4 : nameSub (nameSub Y X) Y ≡ nameSub X Y
    st4 = trans (sym (nameSub-shift (nameSub Y X) Y))
                (cong (λ Z → nameSub Z Y) (sub-shift-id Y X ne))
    eq : closeAt X S (renameᵗ (shiftAtᵗ Y) A)
       ≡ renameᵗ (shiftAtᵗ (nameSub X Y))
           (closeAt (nameSub Y X) (renameᵗ (nameSub Y) S) A)
    eq = closeAt-unshift X (nameSub Y X) Y (nameSub X Y) S
           (renameᵗ (nameSub Y) S) A
           (sub-shift-id Y X ne)
           (sub-avoid Y Y avY avY (inj₁ refl))
           st4
           (trans (sub-avoid Y Y avY avY (inj₁ refl))
             (sym (trans
               (cong (λ Z → renameᵗ (shiftAtᵗ Z) (renameᵗ (nameSub Y) S))
                 st4)
               (sub-avoid Y (nameSub X Y) avY avW (nameSub-cases X Y)))))

  -- a `↦`: the components run in opposite directions between the same
  -- two contexts, so `t` is substituted at X and `s` at the index and
  -- type `t` has moved the slot to.  §8b's `slotOut-round` says the
  -- round trip lands on X again — no premise about it is needed.
  substAnnElt-typing {X = X} {S = S} {Ssᵢ′ = Ssᵢ′} {Bs = Bs} rw
    (sa-fun sas sat eT) wfS d
    (conv-fun {C = C} {A = A} {B = B} {D = D} ⊢s ⊢t)
    with substAnn-typing rw sat wfS d ⊢t
  substAnnElt-typing {X = X} {S = S} {Ssᵢ′ = Ssᵢ′} {Bs = Bs} rw
    (sa-fun sas sat eT) wfS d
    (conv-fun {C = C} {A = A} {B = B} {D = D} ⊢s ⊢t) | Ssₑ′ , dₑ , wfₑ , ty-t
    with substAnn-typing rw sas wfₑ dₑ ⊢s | slotOut-round ⊢s ⊢t d
  substAnnElt-typing {X = X} {S = S} {Ssᵢ′ = Ssᵢ′} {Bs = Bs} rw
    (sa-fun sas sat eT) wfS d
    (conv-fun {C = C} {A = A} {B = B} {D = D} ⊢s ⊢t)
    | Ssₑ′ , dₑ , wfₑ , ty-t | Ssᵢ″ , d″ , wf″ , ty-s | eX =
    Ssₑ′ , dₑ , wfₑ
    , conv-fun
        (conv-ctx-≡ (cong (_∥ Bs) (sym (drop-uniqueS d (drop-≡ eX d″))))
          (conv-≡ (cong₂ (λ P T → closeAt P T A) eX eT) ty-s))
        ty-t

  -- an `all`: one more binder assignment on both sides, so the slot
  -- moves up by one and S shifts with it.  Coming back out the slot is
  -- again under a `bind` — §8b's rank says its index is a successor —
  -- and `tyOutElt (all s)` brings the slot's type back with it.
  substAnnElt-typing {X = X} {S = S} rw (sa-all sa eT)
    wfS d (conv-all {A = A} {B = B} ⊢s)
    with substAnn-typing rw sa (wf-⇑ wfS) (drop-there d) ⊢s
       | drop-brank d
  substAnnElt-typing {X = X} {S = S} rw (sa-all sa eT)
    wfS d (conv-all {A = A} {B = B} ⊢s) | Ss₂′ , d₂ , wf₂ , ty | n , bX
    with brank-bind-inv (brank-conv ⊢s (br-bind bX))
  substAnnElt-typing {X = X} {S = S} rw (sa-all sa eT)
    wfS d (conv-all {A = A} {B = B} ⊢s) | Ss₂′ , d₂ , wf₂ , ty | n , bX
    | Z , eX , bZ
    with drop-≡ eX d₂ | wf-≡ eT wf₂
       | conv-≡ (cong₂ (λ P T → closeAt P T B) eX eT) ty
  substAnnElt-typing {X = X} {S = S} rw (sa-all sa eT)
    wfS d (conv-all {A = A} {B = B} ⊢s) | Ss₂′ , d₂ , wf₂ , ty | n , bX
    | Z , eX , bZ | drop-there dₑ | wfₑ | ty′
    rewrite eX | eT | ren-sub0 S | closeAt-∀ X S A | closeAt-∀ Z S B =
    _ , dₑ , wf-⇓ wfₑ , conv-all ty′

  substAnn-typing : ∀ {Sg X S c A B Ssᵢ Ssᵢ′ Ssₑ Bs}
    → RepsWf Sg Bs → SAvoids X S c
    → (Ssᵢ′ ∥ Bs) ⊢ᵗ S → DropBindS X Ssᵢ Ssᵢ′
    → Sg ∣ (Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Ssₑ′ ∈ List StackEnt ]
        (DropBindS (slotOut c X) Ssₑ Ssₑ′
         × ((Ssₑ′ ∥ Bs) ⊢ᵗ tyOut c S)
         × Sg ∣ (Ssᵢ′ ∥ Bs) ⊢ substAnn X S c
             ∶ closeAt X S A ⇝ closeAt (slotOut c X) (tyOut c S) B
             ⊣ (Ssₑ′ ∥ Bs))

  substAnn-typing rw sa-id wfS d (conv-id wf) =
    _ , d , wfS , conv-id (wf-drop d wfS wf)
  substAnn-typing {X = X} {S = S} rw (sa-cons {ĉ = ĉ} {c = c} saĉ sac)
    wfS d (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl)
    with conv-base tl
  substAnn-typing {X = X} {S = S} rw (sa-cons {ĉ = ĉ} {c = c} saĉ sac)
    wfS d (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl
    with substAnnElt-typing rw saĉ wfS d hd
  substAnn-typing {X = X} {S = S} rw (sa-cons {ĉ = ĉ} {c = c} saĉ sac)
    wfS d (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl
    | Ss₂′ , d₂ , wf₂ , ty-hd
    with substAnn-typing rw sac wf₂ d₂ tl
  substAnn-typing {X = X} {S = S} rw (sa-cons {ĉ = ĉ} {c = c} saĉ sac)
    wfS d (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl
    | Ss₂′ , d₂ , wf₂ , ty-hd | Ssₑ′ , dₑ , wfₑ , ty-tl =
    Ssₑ′ , dₑ , wfₑ , conv-cons ty-hd ty-tl

------------------------------------------------------------------------
-- §10  The form the callers ask for: both drops given
------------------------------------------------------------------------
-- The caller knows where the slot is at BOTH ends — for `TyWrap` it is
-- the `∀`'s own binder assignment, at index zero on either side — so
-- it hands over both drops and the two equations that say so.

substAnn-typing′ : ∀ {Sg X S c A B Ssᵢ Ssᵢ′ Ssₑ Ssₑ′ Bs}
  → RepsWf Sg Bs → SAvoids X S c
  → (Ssᵢ′ ∥ Bs) ⊢ᵗ S
  → slotOut c X ≡ X → tyOut c S ≡ S
  → DropBindS X Ssᵢ Ssᵢ′ → DropBindS X Ssₑ Ssₑ′
  → Sg ∣ (Ssᵢ ∥ Bs) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
  → Sg ∣ (Ssᵢ′ ∥ Bs) ⊢ substAnn X S c
      ∶ closeAt X S A ⇝ closeAt X S B ⊣ (Ssₑ′ ∥ Bs)
substAnn-typing′ {Bs = Bs} rw sa wfS eX eT dᵢ dₑ ⊢c
  with substAnn-typing rw sa wfS dᵢ ⊢c
substAnn-typing′ {B = B} {Bs = Bs} rw sa wfS eX eT dᵢ dₑ ⊢c
  | Ssₑ″ , d″ , wf″ , ty =
  conv-ctx-≡ (cong (_∥ Bs) (sym (drop-uniqueS dₑ (drop-≡ eX d″))))
    (conv-≡ (cong₂ (λ P T → closeAt P T B) eX eT) ty)

------------------------------------------------------------------------
-- §10b  The §6 word, now TYPED at the stepped index
------------------------------------------------------------------------
-- `substAnnElt 1 `ℕ (sₓ ↦ tₓ)` substitutes `tₓ` at the slot index 1
-- and `sₓ` at `slotOut tₓ 1 = 0` — the whole point of the change.  The
-- old definition handed `sₓ` the index 1 as well, and `StepFix`'s
-- `slotOut tₓ 1 ≡ 1` — which `slot-movesₓ` REFUTES — was the premise
-- that hid it.  Here the theorem types the word with no premise about
-- the slot at all.

private
  substₓ-steps : substAnnElt 1 `ℕ (sₓ ↦ tₓ)
    ≡ substAnn zero `ℕ sₓ ↦ substAnn 1 `ℕ tₓ
  substₓ-steps = refl

  rwₓ : RepsWf Sgₓ []
  rwₓ (r-lvl l-here) = wfᴿ-ℕ

  ⊢substₓ : Sgₓ ∣ (asgn (lvl zero) ∷ [] ∥ [])
    ⊢̂ substAnnElt 1 `ℕ (sₓ ↦ tₓ)
    ∶ closeAt 1 `ℕ (`ℕ ⇒ `ℕ)
    ⇝ closeAt (slotOutElt (sₓ ↦ tₓ) 1) (tyOutElt (sₓ ↦ tₓ) `ℕ) (`ℕ ⇒ `ℕ)
    ⊣ ([] ∥ [])
  ⊢substₓ with substAnnElt-typing rwₓ (closed-avoidsElt (sₓ ↦ tₓ) nf-ℕ)
                 wf-ℕ dropₓ ⊢funₓ
  ⊢substₓ | [] , drop-here , wfₓ , tyₓ = tyₓ

------------------------------------------------------------------------
-- §11  Sanity check against `Examples.§14`
------------------------------------------------------------------------
-- There `allView c₂` is `d = show 1 (lvl 0) ∷ᶜ id (` 0 ⇒ ` 0)`, typed
-- under the ∀'s binder assignment — slot 0 — and `instReveal zero (bse
-- zero) `𝔹 d` composes the builder with `substAnn zero `𝔹 d`.  The
-- crossing returns the slot to 0 (`nameSub 1 0 ≡ 0`), which is what
-- `slotOut-bind` derives; the type argument is ground, so `SAvoids`
-- holds by `closed-avoids`; and the substituted conversion is the one
-- `inst-agrees` checks.

private
  §14-d : Conv
  §14-d = show 1 (lvl 0) ∷ᶜ id (` 0 ⇒ ` 0)

  §14-subst : substAnn zero `𝔹 §14-d ≡ show 0 (lvl 0) ∷ᶜ id (`𝔹 ⇒ `𝔹)
  §14-subst = refl

  §14-closed : Closedᵗ `𝔹
  §14-closed = nf-𝔹

  §14-slot : slotOut §14-d zero ≡ zero
  §14-slot = refl

  §14-avoids : SAvoids zero `𝔹 §14-d
  §14-avoids = closed-avoids §14-d §14-closed
