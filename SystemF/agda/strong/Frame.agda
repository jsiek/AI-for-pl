module strong.Frame where

-- Strong System F v8 — THE UNLOCKED FRAME of a conversion.
--
-- A conversion's element list moves the type context by one name at a
-- time, and `Conversion.interior` walks it.  But the context the
-- ELEMENTS' TYPES should be read in is not that walk's result: a
-- CONCEAL (`hide`/`seal`) removes the very name a later element's
-- read-back needs, and the read-back then has nothing to land on.
-- `notes/SourceToTyWrapGap` is a closed source program that reaches
-- exactly that state.
--
-- THE FRAME is the same walk with the conceals SKIPPED — the analogue
-- of main's `unlockedScope Θ Δ`, where the boundary's representations
-- are checked (`mw-reps`, strong.CtxMorph on `main`).  Two rules:
--
--   a CONCEAL  leaves the frame alone and pops the real context;
--   a REVEAL   pushes on both, into the frame AT THE FRAME'S OWN SLOT.
--
-- That second point is what `insMap` is for.  A crossing's name is an
-- index into the REAL context, and by the time a reveal is reached the
-- frame has kept entries the real context dropped, so the two disagree
-- about where slot X is.  Main has no such drift — "a change names an
-- EXTERIOR slot and is unshifted by the morphism's own binds" — so the
-- walk here carries the map `ρ : Γ → Ξ` and inserts at `ρ X`.  With
-- that, every transport in sight is a `shiftAtᵗ` composite.
--
-- A DOMAIN COMPONENT CONTRIBUTES NOTHING (Jeremy, 2026-09-17): "the
-- domain position of an arrow conversion doesn't apply to the current
-- enclosed term and its context, but instead to the argument term after
-- `Wrap` fires, at which point the domain conversion is no longer under
-- an arrow."  So `frameElt (s ↦ t) = frameConv t`, which is
-- `interiorElt`'s own clause, and the two walks differ ONLY at the four
-- atomic elements.  What the domain side still needs of the frame it
-- gets anyway: every clause of `revTy` leaves a reveal at its address
-- in a frame-visited position (see `notes/UnlockedFrame2`).

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion using
  (Conv; id; _∷ᶜ_; ConvElt; seal; unseal; hide; show; _↦_; all;
   pushAsgn; popAsgn; nameSub)

------------------------------------------------------------------------
-- 1.  The walk
------------------------------------------------------------------------
-- A `Frame` is the real context, the frame, and the map between them.

Frame : Set
Frame = Ctxᵗ × Ctxᵗ × Renameᵗ

start : Ctxᵗ → Frame
start Δ = (Δ , Δ , λ n → n)

-- a REVEAL at local name X lands at `ρ X`; the frame's slots from there
-- up move out, and the real context's slots from X up move out
insMap : ℕ → Renameᵗ → Renameᵗ
insMap X ρ Y with X ≟ Y
insMap X ρ Y | yes _ = ρ X
insMap X ρ Y | no  _ = shiftAtᵗ (ρ X) (ρ (nameSub X Y))

-- a CONCEAL drops slot X from the real context and nothing from the
-- frame, so the map reads past the hole
delMap : ℕ → Renameᵗ → Renameᵗ
delMap X ρ Y = ρ (shiftAtᵗ X Y)

mutual
  frameElt : ConvElt → Frame → Maybe Frame
  frameElt (seal X α) (Γ , Ξ , ρ) with popAsgn X α Γ
  ... | just Γ′ = just (Γ′ , Ξ , delMap X ρ)
  ... | nothing = nothing
  frameElt (hide X α) (Γ , Ξ , ρ) with popAsgn X α Γ
  ... | just Γ′ = just (Γ′ , Ξ , delMap X ρ)
  ... | nothing = nothing
  frameElt (unseal X α) (Γ , Ξ , ρ) with pushAsgn X α Γ | pushAsgn (ρ X) α Ξ
  ... | just Γ′ | just Ξ′ = just (Γ′ , Ξ′ , insMap X ρ)
  ... | _ | _ = nothing
  frameElt (show X α) (Γ , Ξ , ρ) with pushAsgn X α Γ | pushAsgn (ρ X) α Ξ
  ... | just Γ′ | just Ξ′ = just (Γ′ , Ξ′ , insMap X ρ)
  ... | _ | _ = nothing
  frameElt (s ↦ t) f = frameConv t f
  frameElt (all s) ((Ss ∥ Bs) , Ξ , ρ)
    with frameConv s ((bind ∷ Ss ∥ Bs) , (bind ∷ stk Ξ ∥ bas Ξ) , extᵗ ρ)
  ... | just ((bind ∷ Ss′ ∥ Bs′) , (bind ∷ Ts ∥ Cs) , ρ′) =
        just ((Ss′ ∥ Bs′) , (Ts ∥ Cs) , λ Y → ρ′ (suc Y) ∸ 1)
  ... | _ = nothing

  frameConv : Conv → Frame → Maybe Frame
  frameConv (id A) f = just f
  frameConv (ĉ ∷ᶜ c) f with frameConv c f
  ... | just f′ = frameElt ĉ f′
  ... | nothing = nothing

getΓ getΞ : Maybe Frame → Maybe Ctxᵗ
getΓ (just (Γ , _ , _)) = just Γ
getΓ nothing = nothing
getΞ (just (_ , Ξ , _)) = just Ξ
getΞ nothing = nothing

getρ : Maybe Frame → Renameᵗ
getρ (just (_ , _ , ρ)) = ρ
getρ nothing = λ n → n

-- the frame of a conversion over its exterior
unlocked : Conv → Ctxᵗ → Maybe Ctxᵗ
unlocked c Δ = getΞ (frameConv c (start Δ))

------------------------------------------------------------------------
-- 2.  Insertions
------------------------------------------------------------------------
-- What relates the real context to the frame, and one frame to a larger
-- one: a renaming preserving the three lookups the frame is read
-- through.  Only `asgn` entries are ever inserted, so the bind skeleton
-- — and `∋b`'s rank — is untouched.

record Insert (ρ : Renameᵗ) (Ξ Ξ′ : Ctxᵗ) : Set where
  field
    ins-t : ∀ {X} → stk Ξ ∋ᵗ X → stk Ξ′ ∋ᵗ ρ X
    ins-n : ∀ {X α} → Ξ ∋n X := α → Ξ′ ∋n ρ X := α
    ins-b : ∀ {X i} → stk Ξ ∋b X at i → stk Ξ′ ∋b ρ X at i
open Insert public

ins-id : ∀ {Ξ} → Insert (λ n → n) Ξ Ξ
ins-t ins-id p = p
ins-n ins-id p = p
ins-b ins-id p = p

ins-bind : ∀ {ρ Ξ Ξ′} → Insert ρ Ξ Ξ′
  → Insert (extᵗ ρ) (bind ∷ stk Ξ ∥ bas Ξ) (bind ∷ stk Ξ′ ∥ bas Ξ′)
ins-t (ins-bind i) t-here = t-here
ins-t (ins-bind i) (t-there p) = t-there (ins-t i p)
ins-n (ins-bind i) (n-skip-bind p) = n-skip-bind (ins-n i p)
ins-b (ins-bind i) b-here = b-here
ins-b (ins-bind i) (b-bind p) = b-bind (ins-b i p)

------------------------------------------------------------------------
-- 3.  What travels along an insertion
------------------------------------------------------------------------

wf-ins : ∀ {ρ Ξ Ξ′ A} → Insert ρ Ξ Ξ′ → Ξ ⊢ᵗ A → Ξ′ ⊢ᵗ renameᵗ ρ A
wf-ins i (wf-var n) = wf-var (ins-t i n)
wf-ins i wf-ℕ = wf-ℕ
wf-ins i wf-𝔹 = wf-𝔹
wf-ins i (wf-⇒ a b) = wf-⇒ (wf-ins i a) (wf-ins i b)
wf-ins i (wf-∀ a) = wf-∀ (wf-ins (ins-bind i) a)

-- the read-back under an insertion: `read-var` is a lookup, and an
-- insertion preserves lookups
read-ins : ∀ {Σ ρ Ξ Ξ′ R A} → Insert ρ Ξ Ξ′
  → Σ ∣ Ξ ⊢ R ⇓ A → Σ ∣ Ξ′ ⊢ R ⇓ renameᵗ ρ A
read-ins i (read-var n) = read-var (ins-n i n)
read-ins i (read-bv n) = read-bv (ins-b i n)
read-ins i read-ℕ = read-ℕ
read-ins i read-𝔹 = read-𝔹
read-ins i (read-⇒ a b) = read-⇒ (read-ins i a) (read-ins i b)
read-ins i (read-∀ a) = read-∀ (read-ins (ins-bind i) a)

------------------------------------------------------------------------
-- 4.  Renaming a conversion's ANNOTATIONS
------------------------------------------------------------------------
-- A crossing's name indexes the real context, which an insertion never
-- touches, so the atomic elements ride unchanged; only the terminators
-- carry types.

mutual
  annRenElt : Renameᵗ → ConvElt → ConvElt
  annRenElt ρ (seal X α)   = seal X α
  annRenElt ρ (unseal X α) = unseal X α
  annRenElt ρ (hide X α)   = hide X α
  annRenElt ρ (show X α)   = show X α
  annRenElt ρ (s ↦ t)      = annRen ρ s ↦ annRen ρ t
  annRenElt ρ (all s)      = all (annRen (extᵗ ρ) s)

  annRen : Renameᵗ → Conv → Conv
  annRen ρ (id A)   = id (renameᵗ ρ A)
  annRen ρ (ĉ ∷ᶜ c) = annRenElt ρ ĉ ∷ᶜ annRen ρ c

------------------------------------------------------------------------
-- 5.  RETARGETING — each terminator by the map at ITS OWN position
------------------------------------------------------------------------
-- `annRen` is the uniform rename an insertion induces.  Retargeting is
-- different and is what the BUILDERS need: today each terminator is
-- written in its own local frame, so the same syntax means different
-- things at different positions, and no uniform rename can fix it.

mutual
  retElt : ConvElt → Frame → Maybe (ConvElt × Frame)
  retElt (seal X α) f with frameElt (seal X α) f
  ... | just f′ = just (seal X α , f′)
  ... | nothing = nothing
  retElt (unseal X α) f with frameElt (unseal X α) f
  ... | just f′ = just (unseal X α , f′)
  ... | nothing = nothing
  retElt (hide X α) f with frameElt (hide X α) f
  ... | just f′ = just (hide X α , f′)
  ... | nothing = nothing
  retElt (show X α) f with frameElt (show X α) f
  ... | just f′ = just (show X α , f′)
  ... | nothing = nothing
  retElt (s ↦ t) f with retarget t f
  ... | nothing = nothing
  ... | just (t′ , f′) with retarget s f′
  ...   | just (s′ , _) = just (s′ ↦ t′ , f′)
  ...   | nothing = nothing
  retElt (all s) f with frameElt (all s) f
  ... | nothing = nothing
  ... | just f′ with retarget s f
  ...   | just (s′ , _) = just (all s′ , f′)
  ...   | nothing = nothing

  retarget : Conv → Frame → Maybe (Conv × Frame)
  retarget (id A) (Γ , Ξ , ρ) = just (id (renameᵗ ρ A) , (Γ , Ξ , ρ))
  retarget (ĉ ∷ᶜ c) f with retarget c f
  ... | nothing = nothing
  ... | just (c′ , f′) with retElt ĉ f′
  ...   | just (ĉ′ , f″) = just (ĉ′ ∷ᶜ c′ , f″)
  ...   | nothing = nothing

retargetAt : Conv → Ctxᵗ → Maybe Conv
retargetAt c Δ with retarget c (start Δ)
... | just (c′ , _) = just c′
... | nothing = nothing

------------------------------------------------------------------------
-- 6.  Regression: the `TyWrap` gap
------------------------------------------------------------------------
-- `notes/SourceToTyWrapGap` is a closed source program whose five-step
-- run ends at a term with no typing, and the conversion it ends at is
-- `Wnow` below.  These pin the frame and the retargeting that repair
-- it (`notes/UnlockedFrame2` carries the derivations).

private
  Rν : RepTy
  Rν = `ᵃ (lvl zero)

  Γₑ Γᵢ : Ctxᵗ
  Γₑ = asgn (lvl zero) ∷ [] ∥ nuBind Rν ∷ []      -- the ν's body
  Γᵢ = asgn (bse zero) ∷ [] ∥ nuBind Rν ∷ []      -- the boundary's

  Wnow : Conv                                      -- what `instReveal` builds
  Wnow = ((seal zero (bse zero) ∷ᶜ id (` zero))
           ↦ (show zero (bse zero) ∷ᶜ id `𝔹))
         ∷ᶜ hide zero (lvl zero) ∷ᶜ id (` zero ⇒ `𝔹)

  Wfix : Conv                                      -- what typechecks
  Wfix = ((seal zero (bse zero) ∷ᶜ id (` suc zero))
           ↦ (show zero (bse zero) ∷ᶜ id `𝔹))
         ∷ᶜ hide zero (lvl zero) ∷ᶜ id (` zero ⇒ `𝔹)

  -- the frame keeps the name the `hide` takes away, one slot out
  frame-Ξ : unlocked Wnow Γₑ
          ≡ just (asgn (lvl zero) ∷ asgn (bse zero) ∷ [] ∥ nuBind Rν ∷ [])
  frame-Ξ = refl

  -- the real interior is untouched
  frame-Γ : getΓ (frameConv Wnow (start Γₑ)) ≡ just Γᵢ
  frame-Γ = refl

  -- and the map is the interior endpoint's transport
  frame-ρ : getρ (frameConv Wnow (start Γₑ)) zero ≡ suc zero
  frame-ρ = refl

  -- ONE annotation moves, and no uniform rename would do it
  retarget-ok : retargetAt Wnow Γₑ ≡ just Wfix
  retarget-ok = refl
