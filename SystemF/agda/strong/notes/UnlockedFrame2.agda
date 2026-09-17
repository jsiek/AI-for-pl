module strong.notes.UnlockedFrame2 where

-- The CORRECTED `unlocked`, and the builders.
--
-- `notes/UnlockedFrame`'s `unlocked` inserts a reveal at its LOCAL name,
-- which makes the map from the real context into the frame non-monotone
-- (`ins2` there).  Here the walk carries that map `ρ` and inserts at
-- `ρ X` instead, which is what main gets for free from changes that name
-- EXTERIOR slots.  Everything then transports by `shiftAtᵗ` composites.

open import Data.Nat using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties using (_≟_)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Terms
open import strong.Conversion using
  (Conv; id; _∷ᶜ_; ConvElt; seal; unseal; hide; show; _↦_; all;
   interior; pushAsgn; popAsgn; nameSub)
open import strong.notes.UnlockedFrame using
  (_∣_∣_⊢′_∶_⇝_⊣_; _∣_∣_⊢̂′_∶_⇝_⊣_;
   seal′; unseal′; hide′; show′; fun′; all′; id′; cons′;
   Sg; R; Γ₃; Γ₂; Γ₁; Wnow)

------------------------------------------------------------------------
-- The walk: real context, frame, and the map between them
------------------------------------------------------------------------

Frame : Set
Frame = Ctxᵗ × Ctxᵗ × Renameᵗ

-- a REVEAL at local name X lands at ρ X in the frame; everything at or
-- above it in the frame moves up
insMap : ℕ → Renameᵗ → Renameᵗ
insMap X ρ Y with X ≟ Y
insMap X ρ Y | yes _ = ρ X
insMap X ρ Y | no  _ = shiftAtᵗ (ρ X) (ρ (nameSub X Y))

-- a CONCEAL removes slot X from the real context and nothing from the
-- frame, so the map just reads past the hole
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
  -- The element's REAL interior is `t`'s alone (`interiorElt (s ↦ t) Γ
  -- = interior t Γ`); `s` runs backward and returns to the exterior.
  -- But its reveals still belong to the frame, so `s` is walked for its
  -- FRAME effect only and the real context is taken from `t`.
  frameElt (s ↦ t) f with frameConv t f
  ... | nothing = nothing
  ... | just (Γᵢ , Ξ₁ , ρ₁) with frameConv s (Γᵢ , Ξ₁ , ρ₁)
  ...   | just (_ , Ξ₂ , _) = just (Γᵢ , Ξ₂ , ρ₁)
  ...   | nothing = nothing
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

start : Ctxᵗ → Frame
start Δ = (Δ , Δ , λ n → n)

getΓ getΞ : Maybe Frame → Maybe Ctxᵗ
getΓ (just (Γ , _ , _)) = just Γ
getΓ nothing = nothing
getΞ (just (_ , Ξ , _)) = just Ξ
getΞ nothing = nothing

getρ : Maybe Frame → Renameᵗ
getρ (just (_ , _ , ρ)) = ρ
getρ nothing = λ n → n

------------------------------------------------------------------------
-- On M₅'s conversion
------------------------------------------------------------------------
-- Same walk, different answer: the reveal now lands at `ρ 0 = 1`, so
-- the frame is `X:=α` THEN `Y:=β` — the exterior's own order, extended.

Ξ″ : Ctxᵗ
Ξ″ = asgn (lvl zero) ∷ asgn (bse zero) ∷ [] ∥ nuBind R ∷ []

frΞ : getΞ (frameConv Wnow (start Γ₃)) ≡ just Ξ″
frΞ = refl

frΓ : getΓ (frameConv Wnow (start Γ₃)) ≡ just Γ₁
frΓ = refl

-- and the map from the real interior Γ₁ into Ξ″ is a SHIFT: Y sits at
-- 0 in Γ₁ and at 1 in Ξ″.
frρ : getρ (frameConv Wnow (start Γ₃)) zero ≡ suc zero
frρ = refl

-- which is `shiftAtᵗ 0`, the interior endpoint transport
ιᵢ″ : Renameᵗ
ιᵢ″ = shiftAtᵗ zero

-- the exterior transport is the IDENTITY here: X sits at 0 in both
ιₑ″ : Renameᵗ
ιₑ″ = λ n → n

------------------------------------------------------------------------
-- THE BUILDER CHANGE: retarget each terminator by the map at ITS OWN
-- position
------------------------------------------------------------------------
-- The atomic elements are untouched — their names index the real
-- contexts.  Only the `id A` terminators move, each by the ρ in force
-- where it sits.

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
  retElt (s ↦ t) f with ret t f
  ... | nothing = nothing
  ... | just (t′ , (Γᵢ , Ξ₁ , ρ₁)) with ret s (Γᵢ , Ξ₁ , ρ₁)
  ...   | just (s′ , (_ , Ξ₂ , _)) = just (s′ ↦ t′ , (Γᵢ , Ξ₂ , ρ₁))
  ...   | nothing = nothing
  retElt (all s) f with frameElt (all s) f
  ... | nothing = nothing
  ... | just f′ with ret s f
  ...   | just (s′ , _) = just (all s′ , f′)
  ...   | nothing = nothing

  ret : Conv → Frame → Maybe (Conv × Frame)
  ret (id A) (Γ , Ξ , ρ) = just (id (renameᵗ ρ A) , (Γ , Ξ , ρ))
  ret (ĉ ∷ᶜ c) f with ret c f
  ... | nothing = nothing
  ... | just (c′ , f′) with retElt ĉ f′
  ...   | just (ĉ′ , f″) = just (ĉ′ ∷ᶜ c′ , f″)
  ...   | nothing = nothing

getC : Maybe (Conv × Frame) → Maybe Conv
getC (just (c , _)) = just c
getC nothing = nothing

-- the conversion the builders should emit
W″ : Conv
W″ = ((seal zero (bse zero) ∷ᶜ id (` suc zero))
       ↦ (show zero (bse zero) ∷ᶜ id `𝔹))
     ∷ᶜ hide zero (lvl zero) ∷ᶜ id (` zero ⇒ `𝔹)

-- and retargeting today's output produces it, ON THE NOSE
builder : getC (ret Wnow (start Γ₃)) ≡ just W″
builder = refl

------------------------------------------------------------------------
-- … and W″ typechecks at Ξ″
------------------------------------------------------------------------

⊢W″ : Sg ∣ Ξ″ ∣ Γ₁ ⊢′ W″ ∶ (` suc zero ⇒ `𝔹) ⇝ (` zero ⇒ `𝔹) ⊣ Γ₃
⊢W″ =
  cons′
    (fun′ (cons′ (seal′ r-here (read-var n-here-asgn)
                   (n-skip-asgn n-here-asgn) pop-here)
                 (id′ (wf-var (t-there t-here))))
          (cons′ (show′ a-here-nu wf-𝔹 pop-here (λ ())) (id′ wf-𝔹)))
    (cons′ (hide′ (a-lvl l-here) (wf-⇒ (wf-var t-here) wf-𝔹)
             pop-here (λ ()))
      (id′ (wf-⇒ (wf-var t-here) wf-𝔹)))

-- THE ENDPOINTS ARE THE WALK'S OWN MAP.  `ιᵢ″` is `getρ … `, the map
-- the frame walk already carries, and `ιₑ″` is the identity because the
-- walk starts there.  So nothing extra has to be computed for them.
endpoint-in : renameᵗ ιᵢ″ (` zero ⇒ `𝔹) ≡ (` suc zero ⇒ `𝔹)
endpoint-in = refl

endpoint-out : renameᵗ ιₑ″ (` zero ⇒ `𝔹) ≡ (` zero ⇒ `𝔹)
endpoint-out = refl

ιᵢ-is-ρ : getρ (frameConv Wnow (start Γ₃)) zero ≡ ιᵢ″ zero
ιᵢ-is-ρ = refl

-- The body is typed at Γ₁ with `` ` 0 ⇒ 𝔹 ``, the redex's type is
-- `` ` 0 ⇒ 𝔹 `` at Γ₃, and both land on `⊢W″`'s endpoints.  So the
-- whole TyWrap step is type preserving with the corrected frame, the
-- builders' only change being `ret`.
body : Sg ∣ Γ₁ ∣ [] ⊢ (ƛ (` zero) ∙ (# true)) ⦂ (` zero ⇒ `𝔹)
body = ⊢ƛ (wf-var t-here) ⊢#

-- STILL OPEN: `retElt (s ↦ t)` keeps `ρ₁` while letting `s` grow the
-- frame.  `s` contributes no reveal here (`concTy` emits `seal`/`hide`
-- at the top), but `-X(A → B) = (+X(A) → -X(B)) ∷ …` puts a `+X` one
-- level down, so a contravariant component CAN reveal.  Whether such a
-- reveal belongs in the boundary's frame at all — main has no analogue,
-- since its `Θ` is separate from the conversion — is the next question.
