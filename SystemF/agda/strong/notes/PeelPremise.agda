module strong.notes.PeelPremise where

-- PROTOTYPE, not installed.  What the premise `Peel` would need looks
-- like (§§1–2), that it is satisfiable on the frame where (P) fails
-- (§3), the rule it would produce (§4), the PROOF of the invariant that
-- replaces (P) (§5), and the consequence that the premise never blocks a
-- reduction (§6).  Nothing here is imported by the rule set;
-- `strong.Reduction` is unchanged.

open import Data.List using (List; []; _∷_; _++_; map; reverse)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Properties using (_≟_)
open import Data.List.Properties using (unfold-reverse; map-++)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; subst)

open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.TypeCheck

private
  variable
    η η′ : TyCtx
    X : ℕ
    α : RVar
    A B R : Ty
    s t s′ t′ r u : Conv
    δ : Change
    χ : List Change
    Δ Δ′ Δᵢ Δᶜ Δᵈ : TyCtx
    Ξ Ξ′ : RepCtx
    β : RVar

------------------------------------------------------------------------
-- 1. Reading a conversion in the representation universe
------------------------------------------------------------------------

-- Exactly `_⊢_~_`, one universe up: the ordinary NAMES a conversion
-- carries are translated through the name map, and everything else is
-- structural.  `id` carries a type, so it defers to `_⊢_~_`.
infix 4 _⊩_~_
data _⊩_~_ (η : TyCtx) : Conv → Conv → Set where
  sameᶜ-id     : η ⊢ A ~ R → η ⊩ id A ~ id R
  sameᶜ-seal   : η ∋ˡ X := α → η ⊩ seal X ~ seal α
  sameᶜ-unseal : η ∋ˡ X := α → η ⊩ unseal X ~ unseal α
  sameᶜ-fun    : η ⊩ s ~ r → η ⊩ t ~ u → η ⊩ s ↦ t ~ r ↦ u
  sameᶜ-all    : (zero ∷ shiftNames η) ⊩ s ~ r → η ⊩ `∀ s ~ `∀ r

-- Two ordinary spellings of ONE representation-universe conversion.
SameConv : Ctxᵗ → Conv → Ctxᵗ → Conv → Set
SameConv Γ s Γ′ s′ = ∃[ r ] ((names Γ ⊩ s ~ r) × (names Γ′ ⊩ s′ ~ r))

------------------------------------------------------------------------
-- 2. It determines the spelling, so a rule carrying it stays a function
------------------------------------------------------------------------

sameᶜ-rep-unique : η ⊩ s ~ r → η ⊩ s ~ u → r ≡ u
sameᶜ-rep-unique (sameᶜ-id a) (sameᶜ-id a′) =
  cong id (same-rep-unique a a′)
sameᶜ-rep-unique (sameᶜ-seal d) (sameᶜ-seal d′) =
  cong seal (∋ˡ-det d d′)
sameᶜ-rep-unique (sameᶜ-unseal d) (sameᶜ-unseal d′) =
  cong unseal (∋ˡ-det d d′)
sameᶜ-rep-unique (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
  cong₂ _↦_ (sameᶜ-rep-unique a a′) (sameᶜ-rep-unique b b′)
sameᶜ-rep-unique (sameᶜ-all a) (sameᶜ-all a′) =
  cong `∀ (sameᶜ-rep-unique a a′)

sameᶜ-target-unique : Unique η → η ⊩ s ~ r → η ⊩ s′ ~ r → s ≡ s′
sameᶜ-target-unique uq (sameᶜ-id a) (sameᶜ-id a′) =
  cong id (same-target-unique uq a a′)
sameᶜ-target-unique uq (sameᶜ-seal d) (sameᶜ-seal d′) =
  cong seal (unique-lookup uq d d′)
sameᶜ-target-unique uq (sameᶜ-unseal d) (sameᶜ-unseal d′) =
  cong unseal (unique-lookup uq d d′)
sameᶜ-target-unique uq (sameᶜ-fun a b) (sameᶜ-fun a′ b′) =
  cong₂ _↦_ (sameᶜ-target-unique uq a a′)
            (sameᶜ-target-unique uq b b′)
sameᶜ-target-unique uq (sameᶜ-all a) (sameᶜ-all a′) =
  cong `∀ (sameᶜ-target-unique
             (unique∷ fresh-zero-shift (unique-shift uq)) a a′)

sameConv-src-unique : Unique η
  → ∃[ r ] ((η ⊩ s ~ r) × (η′ ⊩ t ~ r))
  → ∃[ r ] ((η ⊩ s′ ~ r) × (η′ ⊩ t ~ r))
  → s ≡ s′
sameConv-src-unique uq (r , p , q) (r′ , p′ , q′)
  with sameᶜ-rep-unique q q′
... | refl = sameᶜ-target-unique uq p p′

------------------------------------------------------------------------
-- 3. It is SATISFIABLE exactly where (P) fails
------------------------------------------------------------------------

-- A premise that blocked the rule whenever (P) failed would be no repair
-- at all — it would trade unsoundness for a stuck term.  What makes this
-- one a re-spelling rather than a restriction is that the two contexts
-- hold THE SAME REPRESENTATION VARIABLES.  Both are Δ with the unlocked
-- names inserted: the conversion reading skips the locks, and the dual's
-- reading puts the locked names back.  Only the ORDER differs.
--
-- On the mixed frame of notes/CrossingAudit §5 — `lock 0 0` then
-- `unlock 0 2` over Δ₃ — that is visible directly.  (Values recomputed
-- here rather than cited.)  §5 proves it in general.
reps₃ : RepCtx
reps₃ = bindR `ℕ ∷ bindR `𝔹 ∷ bindR `ℕ ∷ []

Δ₃ : Ctxᵗ
Δ₃ = reps₃ ∣ (0 ∷ 1 ∷ [])

Mixed : CtxMorph
Mixed = morph [] (unlock 0 2 ∷ lock 0 0 ∷ [])

nmC : Ctxᵗ → CtxMorph → Maybe TyCtx
nmC Γ Θ with conversion? Γ Θ
nmC Γ Θ | just (Γᶜ , _) = just (names Γᶜ)
nmC Γ Θ | nothing = nothing

Γᶜ Γᵈ : Ctxᵗ
Γᶜ = reps₃ ∣ (2 ∷ 0 ∷ 1 ∷ [])
Γᵈ = reps₃ ∣ (0 ∷ 2 ∷ 1 ∷ [])

-- where `s` is read
is-Γᶜ : nmC Δ₃ Mixed ≡ just (names Γᶜ)
is-Γᶜ = refl

-- where `s` would be used — a PERMUTATION of it, not a smaller context
is-Γᵈ : nmC (reps₃ ∣ (2 ∷ 1 ∷ [])) (dualMorph Mixed) ≡ just (names Γᵈ)
is-Γᵈ = refl

-- so the conversion that `Peel` carries has a spelling on both sides:
-- representation variable 2 sits at ordinary index 0 in one and 1 in the
-- other, and the premise is exactly that renaming.
respelled : SameConv Γᵈ (unseal 1) Γᶜ (unseal 0)
respelled = unseal 2 , sameᶜ-unseal (there here) , sameᶜ-unseal here

------------------------------------------------------------------------
-- 4. The rule it would produce, and the invariant it rests on
------------------------------------------------------------------------

-- `Peel` would read, in the shape the other three repairs already have —
-- name the target spelling, carry a `Same…` relating it to the source,
-- and a `Unique` to keep the rule a function:
--
--   Peel : ∀ {Δ Δᵢ Δᶜ Δᵈ V W Θ s s′ t} → Value V → Value W
--     → Δ ⊢ᶜ Θ ⇒ Δᶜ                     -- where `s` is read
--     → Δ ⊢ⁱ Θ ⇒ Δᵢ
--     → Δᵢ ⊢ᶜ dualMorph Θ ⇒ Δᵈ           -- where `s′` is used
--     → Unique (names Δᵈ)
--     → SameConv Δᵈ s′ Δᶜ s
--     → Δ ⊢ (V ⟪ Θ , s ↦ t ⟫) · W
--         -→ (V · (renᴹ² (ren² idᵗ (wkN (numBinds Θ))) W
--                     ⟪ dualMorph Θ , s′ ⟫)) ⟪ Θ , t ⟫
--
-- `det` closes with `conversion-functional`, `interior-functional` and
-- `sameConv-src-unique`, as the other three do.  `t` needs no premise:
-- it stays on the same boundary, at Δᶜ, where it was read.
--
-- WHAT REPLACES (P) is §3 in general, not on one frame:
--
--   (Q)  conv(dualMorph Θ, int(Θ, Δ)) and conv(Θ, Δ) name the SAME
--        representation variables
--
-- both being Δ with the unlocked names added.  (P) said the two are the
-- same LIST; (Q) says only that they are the same SET, and the premise is
-- what absorbs the difference.  (Q) matters because without it the
-- premise could be UNSATISFIABLE, and then `Peel` would be stuck rather
-- than unsound — progress, not preservation, is what would fail.
--
-- (Q) IS PROVED, in §5, for every well-formed morphism, with no
-- restriction on the change list and no `Unique`: exactly where (P) is
-- false.  §6 then closes the loop — the premise always has a witness, so
-- installing it costs no reduction.

------------------------------------------------------------------------
-- 5. (Q), PROVED
------------------------------------------------------------------------

-- The claim is about NAME MAPS alone: no conversion, no type, no term.
-- Write `Live α Δ` for "α has an ordinary name in Δ".  Then the two
-- conversion contexts `Peel` straddles hold THE SAME representation
-- variables — with `Unique` on both, which the rule already carries, that
-- is a permutation.
Live : RVar → TyCtx → Set
Live α Δ = ∃[ X ] Δ ∋ˡ X := α

-- Insert and delete, against `Live`.
ins-live : α ⊢+ Δ at X ⇒ Δ′ → Live α Δ′
ins-live ins-here = zero , here
ins-live (ins-there i) with ins-live i
ins-live (ins-there i) | X , d = suc X , there d

ins-mono : α ⊢+ Δ at X ⇒ Δ′ → Live β Δ → Live β Δ′
ins-mono ins-here (X , d) = suc X , there d
ins-mono (ins-there i) (zero , here) = zero , here
ins-mono (ins-there i) (suc X , there d) with ins-mono i (X , d)
ins-mono (ins-there i) (suc X , there d) | Y , d′ = suc Y , there d′

ins-inv : α ⊢+ Δ at X ⇒ Δ′ → Live β Δ′ → (β ≡ α) ⊎ Live β Δ
ins-inv ins-here (zero , here) = inj₁ refl
ins-inv ins-here (suc X , there d) = inj₂ (X , d)
ins-inv (ins-there i) (zero , here) = inj₂ (zero , here)
ins-inv (ins-there i) (suc X , there d) with ins-inv i (X , d)
ins-inv (ins-there i) (suc X , there d) | inj₁ eq = inj₁ eq
ins-inv (ins-there i) (suc X , there d) | inj₂ (Y , d′) =
  inj₂ (suc Y , there d′)

del-live : α ⊢- Δ at X ⇒ Δ′ → Live α Δ
del-live del-here = zero , here
del-live (del-there dl) with del-live dl
del-live (del-there dl) | X , d = suc X , there d

del-mono : α ⊢- Δ at X ⇒ Δ′ → β ≢ α → Live β Δ → Live β Δ′
del-mono del-here ne (zero , here) = ⊥-elim (ne refl)
del-mono del-here ne (suc X , there d) = X , d
del-mono (del-there dl) ne (zero , here) = zero , here
del-mono (del-there dl) ne (suc X , there d) with del-mono dl ne (X , d)
del-mono (del-there dl) ne (suc X , there d) | Y , d′ = suc Y , there d′

del-inv : α ⊢- Δ at X ⇒ Δ′ → Live β Δ′ → Live β Δ
del-inv del-here (X , d) = suc X , there d
del-inv (del-there dl) (zero , here) = zero , here
del-inv (del-there dl) (suc X , there d) with del-inv dl (X , d)
del-inv (del-there dl) (suc X , there d) | Y , d′ = suc Y , there d′

------------------------------------------------------------------------
-- 5a. Which names a change list mentions
------------------------------------------------------------------------

data InLocks (α : RVar) : List Change → Set where
  il-here  : ∀ {X χ} → InLocks α (lock X α ∷ χ)
  il-there : ∀ {δ χ} → InLocks α χ → InLocks α (δ ∷ χ)

data InUnlocks (α : RVar) : List Change → Set where
  iu-here  : ∀ {X χ} → InUnlocks α (unlock X α ∷ χ)
  iu-there : ∀ {δ χ} → InUnlocks α χ → InUnlocks α (δ ∷ χ)

inLocks? : (α : RVar) (χ : List Change) → Dec (InLocks α χ)
inLocks? α [] = no (λ ())
inLocks? α (unlock X β ∷ χ) with inLocks? α χ
inLocks? α (unlock X β ∷ χ) | yes il = yes (il-there il)
inLocks? α (unlock X β ∷ χ) | no nl =
  no (λ where (il-there il) → nl il)
inLocks? α (lock X β ∷ χ) with α ≟ β
inLocks? α (lock X β ∷ χ) | yes refl = yes il-here
inLocks? α (lock X β ∷ χ) | no ne with inLocks? α χ
inLocks? α (lock X β ∷ χ) | no ne | yes il = yes (il-there il)
inLocks? α (lock X β ∷ χ) | no ne | no nl =
  no (λ where il-here → ne refl
              (il-there il) → nl il)

------------------------------------------------------------------------
-- 5b. What each reading of a change list does to `Live`
------------------------------------------------------------------------

-- THE CONVERSION CONTEXT ONLY GROWS: it skips every lock, and an unlock
-- either inserts or (already live) does nothing.
conv-mono : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Live α Δ → Live α Δ′
conv-mono conv[] lv = lv
conv-mono (conv-lock v cs) lv = conv-mono cs lv
conv-mono (conv-unlock v cs fr i) lv = ins-mono i (conv-mono cs lv)
conv-mono (conv-unlock-live v cs d) lv = conv-mono cs lv

-- … and it contains every name the list unlocks.
conv-unlocks : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → InUnlocks α χ → Live α Δ′
conv-unlocks (conv-lock v cs) (iu-there iu) = conv-unlocks cs iu
conv-unlocks (conv-unlock v cs fr i) iu-here = ins-live i
conv-unlocks (conv-unlock v cs fr i) (iu-there iu) =
  ins-mono i (conv-unlocks cs iu)
conv-unlocks (conv-unlock-live v cs d) iu-here = _ , d
conv-unlocks (conv-unlock-live v cs d) (iu-there iu) = conv-unlocks cs iu

-- … and nothing else: it is exactly Δ plus the unlocked names.
conv-inv : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ′ → Live α Δ′ → Live α Δ ⊎ InUnlocks α χ
conv-inv conv[] lv = inj₁ lv
conv-inv (conv-lock v cs) lv with conv-inv cs lv
conv-inv (conv-lock v cs) lv | inj₁ l = inj₁ l
conv-inv (conv-lock v cs) lv | inj₂ iu = inj₂ (iu-there iu)
conv-inv (conv-unlock v cs fr i) lv with ins-inv i lv
conv-inv (conv-unlock v cs fr i) lv | inj₁ refl = inj₂ iu-here
conv-inv (conv-unlock v cs fr i) lv | inj₂ lv′ with conv-inv cs lv′
conv-inv (conv-unlock v cs fr i) lv | inj₂ lv′ | inj₁ l = inj₁ l
conv-inv (conv-unlock v cs fr i) lv | inj₂ lv′ | inj₂ iu =
  inj₂ (iu-there iu)
conv-inv (conv-unlock-live v cs d) lv with conv-inv cs lv
conv-inv (conv-unlock-live v cs d) lv | inj₁ l = inj₁ l
conv-inv (conv-unlock-live v cs d) lv | inj₂ iu = inj₂ (iu-there iu)

-- THE INTERIOR keeps every name the list does not lock …
int-keep : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → ¬ InLocks α χ → Live α Δ → Live α Δᵢ
int-keep changes[] nl lv = lv
int-keep (changes∷ cs (step-lock v dl fr)) nl lv =
  del-mono dl (λ where refl → nl il-here)
           (int-keep cs (λ il → nl (il-there il)) lv)
int-keep (changes∷ cs (step-unlock v fr i)) nl lv =
  ins-mono i (int-keep cs (λ il → nl (il-there il)) lv)

-- … including the ones it unlocked along the way.
int-unlocked : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → ¬ InLocks α χ → InUnlocks α χ → Live α Δᵢ
int-unlocked (changes∷ cs (step-lock v dl fr)) nl (iu-there iu) =
  del-mono dl (λ where refl → nl il-here)
           (int-unlocked cs (λ il → nl (il-there il)) iu)
int-unlocked (changes∷ cs (step-unlock v fr i)) nl iu-here = ins-live i
int-unlocked (changes∷ cs (step-unlock v fr i)) nl (iu-there iu) =
  ins-mono i (int-unlocked cs (λ il → nl (il-there il)) iu)

-- Conversely it invents nothing …
int-inv : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → Live α Δᵢ → Live α Δ ⊎ InUnlocks α χ
int-inv changes[] lv = inj₁ lv
int-inv (changes∷ cs (step-lock v dl fr)) lv
  with int-inv cs (del-inv dl lv)
int-inv (changes∷ cs (step-lock v dl fr)) lv | inj₁ l = inj₁ l
int-inv (changes∷ cs (step-lock v dl fr)) lv | inj₂ iu = inj₂ (iu-there iu)
int-inv (changes∷ cs (step-unlock v fr i)) lv with ins-inv i lv
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₁ refl = inj₂ iu-here
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₂ lv′ with int-inv cs lv′
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₂ lv′ | inj₁ l = inj₁ l
int-inv (changes∷ cs (step-unlock v fr i)) lv | inj₂ lv′ | inj₂ iu =
  inj₂ (iu-there iu)

-- … and a name can only be locked if it was there to lock.
int-locked : Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ → InLocks α χ → Live α Δ ⊎ InUnlocks α χ
int-locked (changes∷ cs (step-lock v dl fr)) il-here
  with int-inv cs (del-live dl)
int-locked (changes∷ cs (step-lock v dl fr)) il-here | inj₁ l = inj₁ l
int-locked (changes∷ cs (step-lock v dl fr)) il-here | inj₂ iu =
  inj₂ (iu-there iu)
int-locked (changes∷ cs (step-lock v dl fr)) (il-there il)
  with int-locked cs il
int-locked (changes∷ cs (step-lock v dl fr)) (il-there il) | inj₁ l = inj₁ l
int-locked (changes∷ cs (step-lock v dl fr)) (il-there il) | inj₂ iu =
  inj₂ (iu-there iu)
int-locked (changes∷ cs (step-unlock v fr i)) (il-there il)
  with int-locked cs il
int-locked (changes∷ cs (step-unlock v fr i)) (il-there il) | inj₁ l = inj₁ l
int-locked (changes∷ cs (step-unlock v fr i)) (il-there il) | inj₂ iu =
  inj₂ (iu-there iu)

------------------------------------------------------------------------
-- 5c. The dual unlocks exactly what the list locks
------------------------------------------------------------------------

in-unlocks-++ˡ : ∀ {χ₂} → InUnlocks α χ → InUnlocks α (χ ++ χ₂)
in-unlocks-++ˡ iu-here = iu-here
in-unlocks-++ˡ (iu-there iu) = iu-there (in-unlocks-++ˡ iu)

in-unlocks-++ʳ : ∀ {χ₂} (χ₁ : List Change)
  → InUnlocks α χ₂ → InUnlocks α (χ₁ ++ χ₂)
in-unlocks-++ʳ [] iu = iu
in-unlocks-++ʳ (δ ∷ χ₁) iu = iu-there (in-unlocks-++ʳ χ₁ iu)

in-unlocks-++-inv : ∀ {χ₂} (χ₁ : List Change)
  → InUnlocks α (χ₁ ++ χ₂) → InUnlocks α χ₁ ⊎ InUnlocks α χ₂
in-unlocks-++-inv [] iu = inj₂ iu
in-unlocks-++-inv (unlock X β ∷ χ₁) iu-here = inj₁ iu-here
in-unlocks-++-inv (unlock X β ∷ χ₁) (iu-there iu)
  with in-unlocks-++-inv χ₁ iu
in-unlocks-++-inv (unlock X β ∷ χ₁) (iu-there iu) | inj₁ a =
  inj₁ (iu-there a)
in-unlocks-++-inv (unlock X β ∷ χ₁) (iu-there iu) | inj₂ b = inj₂ b
in-unlocks-++-inv (lock X β ∷ χ₁) (iu-there iu)
  with in-unlocks-++-inv χ₁ iu
in-unlocks-++-inv (lock X β ∷ χ₁) (iu-there iu) | inj₁ a = inj₁ (iu-there a)
in-unlocks-++-inv (lock X β ∷ χ₁) (iu-there iu) | inj₂ b = inj₂ b

locks→dual : (χ : List Change) → InLocks α χ → InUnlocks α (dual χ)
locks→dual (lock X β ∷ χ) il-here
  rewrite unfold-reverse (lock X β) χ
        | map-++ dualChange (reverse χ) (lock X β ∷ []) =
  in-unlocks-++ʳ (dual χ) iu-here
locks→dual (lock X β ∷ χ) (il-there il)
  rewrite unfold-reverse (lock X β) χ
        | map-++ dualChange (reverse χ) (lock X β ∷ []) =
  in-unlocks-++ˡ (locks→dual χ il)
locks→dual (unlock X β ∷ χ) (il-there il)
  rewrite unfold-reverse (unlock X β) χ
        | map-++ dualChange (reverse χ) (unlock X β ∷ []) =
  in-unlocks-++ˡ (locks→dual χ il)

dual→locks : (χ : List Change) → InUnlocks α (dual χ) → InLocks α χ
dual→locks [] ()
dual→locks (lock X β ∷ χ) iu
  rewrite unfold-reverse (lock X β) χ
        | map-++ dualChange (reverse χ) (lock X β ∷ [])
  with in-unlocks-++-inv (dual χ) iu
dual→locks (lock X β ∷ χ) iu | inj₁ a = il-there (dual→locks χ a)
dual→locks (lock X β ∷ χ) iu | inj₂ iu-here = il-here
dual→locks (unlock X β ∷ χ) iu
  rewrite unfold-reverse (unlock X β) χ
        | map-++ dualChange (reverse χ) (unlock X β ∷ [])
  with in-unlocks-++-inv (dual χ) iu
dual→locks (unlock X β ∷ χ) iu | inj₁ a = il-there (dual→locks χ a)
dual→locks (unlock X β ∷ χ) iu | inj₂ (iu-there ())

------------------------------------------------------------------------
-- 5d. (Q) for a change list
------------------------------------------------------------------------

-- Both contexts are Δ with the unlocked names added: the conversion
-- reading skips the locks, and the dual's reading unlocks exactly them.
Q-changes : (χ : List Change)
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Ξ′ ∣ Δᵢ ⊢χᶜ dual χ ⇒ Δᵈ
  → Live α Δᶜ → Live α Δᵈ
Q-changes {α = α} χ int conv dconv lv with inLocks? α χ
Q-changes {α = α} χ int conv dconv lv | yes il =
  conv-unlocks dconv (locks→dual χ il)
Q-changes {α = α} χ int conv dconv lv | no nl with conv-inv conv lv
Q-changes {α = α} χ int conv dconv lv | no nl | inj₁ l =
  conv-mono dconv (int-keep int nl l)
Q-changes {α = α} χ int conv dconv lv | no nl | inj₂ iu =
  conv-mono dconv (int-unlocked int nl iu)

Q-changes-conv : (χ : List Change)
  → Ξ ∣ Δ ⊢χ χ ⇒ Δᵢ
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δᶜ
  → Ξ′ ∣ Δᵢ ⊢χᶜ dual χ ⇒ Δᵈ
  → Live α Δᵈ → Live α Δᶜ
Q-changes-conv χ int conv dconv lv with conv-inv dconv lv
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ with int-inv int lvᵢ
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ | inj₁ l = conv-mono conv l
Q-changes-conv χ int conv dconv lv | inj₁ lvᵢ | inj₂ iu =
  conv-unlocks conv iu
Q-changes-conv χ int conv dconv lv | inj₂ iud
  with int-locked int (dual→locks χ iud)
Q-changes-conv χ int conv dconv lv | inj₂ iud | inj₁ l = conv-mono conv l
Q-changes-conv χ int conv dconv lv | inj₂ iud | inj₂ iu =
  conv-unlocks conv iu

------------------------------------------------------------------------
-- 5e. (Q) for a morphism — the form `Peel`'s premises have
------------------------------------------------------------------------

-- `dualMorph Θ` binds nothing, so its reading starts at the interior
-- unshifted.
shiftRVars-0 : (Δ : TyCtx) → shiftRVars 0 Δ ≡ Δ
shiftRVars-0 [] = refl
shiftRVars-0 (α ∷ Δ) = cong (α ∷_) (shiftRVars-0 Δ)

-- (Q).  The two conversion contexts `Peel` straddles NAME THE SAME
-- REPRESENTATION VARIABLES.  Neither `Unique` nor any premise about the
-- shape of Θ is needed: it holds for every well-formed morphism, mixed
-- change lists included — which is exactly what (P) did not.
Q : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dualMorph Θ ⇒ Γᵈ
  → Live α (names Γᶜ) → Live α (names Γᵈ)
Q {Θ = Θ} (interior cs) (conversion cc) (conversion dc) lv =
  Q-changes (changes Θ) cs cc
    (subst (λ D → _ ∣ D ⊢χᶜ dual (changes Θ) ⇒ _) (shiftRVars-0 _) dc)
    lv

Q-inv : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dualMorph Θ ⇒ Γᵈ
  → Live α (names Γᵈ) → Live α (names Γᶜ)
Q-inv {Θ = Θ} (interior cs) (conversion cc) (conversion dc) lv =
  Q-changes-conv (changes Θ) cs cc
    (subst (λ D → _ ∣ D ⊢χᶜ dual (changes Θ) ⇒ _) (shiftRVars-0 _) dc)
    lv

------------------------------------------------------------------------
-- 6. WHAT (Q) BUYS: the premise never blocks a reduction
------------------------------------------------------------------------

-- Transporting a spelling needs the name map only through `Live`, so (Q)
-- is exactly the right interface.  First, `Live` under a `∀`.
live-cons : Live α η → Live α (β ∷ η)
live-cons (X , d) = suc X , there d

live-shift : Live α η → Live (suc α) (shiftNames η)
live-shift (zero , here) = zero , here
live-shift (suc X , there d) with live-shift (X , d)
live-shift (suc X , there d) | Y , d′ = suc Y , there d′

live-shift-inv : (η : TyCtx) → Live α (shiftNames η)
  → ∃[ β ] (Live β η × (α ≡ suc β))
live-shift-inv (γ ∷ η) (zero , here) = γ , (zero , here) , refl
live-shift-inv (γ ∷ η) (suc X , there d) with live-shift-inv η (X , d)
live-shift-inv (γ ∷ η) (suc X , there d) | β , lv , eq =
  β , live-cons lv , eq

-- A name-preserving map lifts through a binder.
Keeps : TyCtx → TyCtx → Set
Keeps η η′ = ∀ {α} → Live α η → Live α η′

keeps-underΛ : Keeps η η′ → Keeps (zero ∷ shiftNames η) (zero ∷ shiftNames η′)
keeps-underΛ f (zero , here) = zero , here
keeps-underΛ {η = η} f (suc X , there d) with live-shift-inv η (X , d)
keeps-underΛ {η = η} f (suc X , there d) | β , lv , refl =
  live-cons (live-shift (f lv))

-- RE-SPELLING.  A type, and then a conversion, can be rewritten for any
-- context that names everything this one names.
respell-ty : Keeps η η′ → η ⊢ A ~ R → ∃[ A′ ] (η′ ⊢ A′ ~ R)
respell-ty f (same-var d) with f (_ , d)
respell-ty f (same-var d) | X , d′ = ` X , same-var d′
respell-ty f same-ℕ = `ℕ , same-ℕ
respell-ty f same-𝔹 = `𝔹 , same-𝔹
respell-ty f (same-⇒ a b) with respell-ty f a
respell-ty f (same-⇒ a b) | A′ , a′ with respell-ty f b
respell-ty f (same-⇒ a b) | A′ , a′ | B′ , b′ = A′ ⇒ B′ , same-⇒ a′ b′
respell-ty f (same-∀ a) with respell-ty (keeps-underΛ f) a
respell-ty f (same-∀ a) | A′ , a′ = `∀ A′ , same-∀ a′

respell : Keeps η η′ → η ⊩ s ~ r → ∃[ s′ ] (η′ ⊩ s′ ~ r)
respell f (sameᶜ-id a) with respell-ty f a
respell f (sameᶜ-id a) | A′ , a′ = id A′ , sameᶜ-id a′
respell f (sameᶜ-seal d) with f (_ , d)
respell f (sameᶜ-seal d) | X , d′ = seal X , sameᶜ-seal d′
respell f (sameᶜ-unseal d) with f (_ , d)
respell f (sameᶜ-unseal d) | X , d′ = unseal X , sameᶜ-unseal d′
respell f (sameᶜ-fun a b) with respell f a
respell f (sameᶜ-fun a b) | s₁ , a′ with respell f b
respell f (sameᶜ-fun a b) | s₁ , a′ | s₂ , b′ = s₁ ↦ s₂ , sameᶜ-fun a′ b′
respell f (sameᶜ-all a) with respell (keeps-underΛ f) a
respell f (sameᶜ-all a) | s₁ , a′ = `∀ s₁ , sameᶜ-all a′

-- READABILITY.  A well-typed conversion always HAS a representation-
-- universe reading: `id` is restricted to a base type or a live variable,
-- and `seal`/`unseal` cite the lookup square, whose first component is
-- the name map entry.
readable : ∀ {Γ : Ctxᵗ} {c} → Γ ⊢ c ∶ A ⇝ B → ∃[ r ] (names Γ ⊩ c ~ r)
readable (conv-id base-ℕ) = id `ℕ , sameᶜ-id same-ℕ
readable (conv-id base-𝔹) = id `𝔹 , sameᶜ-id same-𝔹
readable (conv-idv (α , d)) = id (` α) , sameᶜ-id (same-var d)
readable (conv-unseal (α , R , d , rd , sm)) = unseal α , sameᶜ-unseal d
readable (conv-seal (α , R , d , rd , sm)) = seal α , sameᶜ-seal d
readable (conv-fun a b) with readable a
readable (conv-fun a b) | r₁ , a′ with readable b
readable (conv-fun a b) | r₁ , a′ | r₂ , b′ = r₁ ↦ r₂ , sameᶜ-fun a′ b′
readable (conv-all a) with readable a
readable (conv-all a) | r₁ , a′ = `∀ r₁ , sameᶜ-all a′

-- THE PAYOFF.  Whatever conversion the redex carries, the premise has a
-- witness.  So installing it costs no reduction: `Peel` fires wherever it
-- fires today, with `s` re-spelled instead of reused verbatim.
premise-exists : ∀ {Γ Γᵢ Γᶜ Γᵈ : Ctxᵗ} {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ
  → Γ ⊢ᶜ Θ ⇒ Γᶜ
  → Γᵢ ⊢ᶜ dualMorph Θ ⇒ Γᵈ
  → Γᶜ ⊢ s ∶ A ⇝ B
  → ∃[ s′ ] SameConv Γᵈ s′ Γᶜ s
premise-exists int conv dconv ⊢s with readable ⊢s
premise-exists int conv dconv ⊢s | r , rd
  with respell (Q int conv dconv) rd
premise-exists int conv dconv ⊢s | r , rd | s′ , rd′ = s′ , (r , rd′ , rd)
