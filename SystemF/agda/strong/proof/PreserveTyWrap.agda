module strong.proof.PreserveTyWrap where

-- Strong System F v8 — preservation for `TyWrap`.
--
--   ((Λ V) ⟨ c ⟩) • B [ A ]  —→  ν R ∙ (V ⟨ instReveal 0 (bse 0) A d ⟩)
--                                          if allView c ≡ just d
--
-- This module discharges `proof.PreserveTyDef.TyWrapOk` up to the side
-- conditions the INGREDIENTS require but the redex does not supply.
-- See §7 for the exact statement proved (`tyWrapOk′`), §8 for what is
-- still open, and §9 for the probes that show why each extra premise is
-- there.
--
-- WHAT THE v8 ADDRESS SPLIT COLLAPSED.  Two whole sections of the v7
-- version are gone:
--
--   * §1 used to prove that a typed crossing never names a `bnd`, so
--     that the `NotBnd` half of `SlotFree` was free.  There is no
--     `bnd`: a `∀` binds a type VARIABLE (`RepTy`'s `` `ᵛ ``), so
--     `NotBnd` is vacuous and `proof.SubstAnnTyping` has deleted it.
--     With it goes `DeepNames`, which existed only to name the NAME
--     half of `SlotFree` — and that half is gone too, now that
--     `substAnn` threads the slot along the spine: what is left is
--     `StepFix`, whose atomic constructors carry nothing at all.
--
--   * §3 used to re-prove `substAnn`'s typing against a repaired side
--     condition, because v7's `NoBndReps` was refutable.  Its v8
--     successor `RepsWf` — "every representation a `∋r` reaches has its
--     `` `ᵛ ``s bound by its own `∀ᴿ`s" — is STRUCTURAL, and §2 gets it
--     from `StoreOk` alone.  It is refutable in one respect only, and
--     that is a defect of its STATEMENT, not of the condition: see §2.
--
-- Nothing here is postulated and nothing is left as a hole.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms

open import strong.proof.Flat using
  (Flat; Flatn; flat; conv-flat; fu-nobinds; wfᴿ-restk)
open Flatn
open import strong.proof.Scoped using
  (Scoped; quote-wfᴿ; flat-bindsBelow)
open import strong.proof.Interior using (pop-base)
open import strong.proof.AddrWeaken using
  (Renamesᵇ; ren-wk; ren-stk; read-ren; conv-ren; conv-base; wfᴿ-ren)
open Renamesᵇ
open import strong.proof.BuilderTyping using
  (BaseGrow; bg-here; ⊢-grow; revTy-typing; closeAt-single; notasgn-⤒)
open import strong.proof.SubstAnnTyping using
  (NoFreeᵗ; nf-var; nf-ℕ; nf-𝔹; nf-⇒; nf-∀; Closedᵗ; wf-closed;
   RepsWf; substAnn-typing′;
   SAvoids; closed-avoids; closed-tyOut;
   StepFix; fx-id; fx-cons; fx-hide; fx-show; fx-fun;
   slotOut; drop-here)
open import strong.proof.CompositionTyping using (⨟-typing)
open import strong.proof.AllTyping using (⇑ᶜ; allView-typing)
open import strong.proof.SrcTyping using (srcᶜ-sound)
open import strong.proof.TypeWf using (typing-wf; ctxOk-[])

------------------------------------------------------------------------
-- §1  THE SIDE CONDITION ON REPRESENTATIONS, AND THE ONE FLAW IN ITS
--     STATEMENT
------------------------------------------------------------------------
-- `proof.SubstAnnTyping.substAnn-typing′` asks for
--
-- `RepsWf` is indexed by the BASE at its source, and a conversion
-- never changes the base, so one instance serves a whole spine; at the
-- empty base it is just `StoreOk`.

-- `StoreOk` grades each entry by the STRICTLY EARLIER prefix, so the
-- representation it hands back is well formed over `take ℓ Sg`; the
-- prefix is a genuine sublist of the store, and neither `∋a` nor `⊢ᴿ`
-- reads the stack, so the grading transports.
∋ˡ-take : ∀ {Sg ℓ m R} → take ℓ Sg ∋ˡ m := R → Sg ∋ˡ m := R
∋ˡ-take {ℓ = zero} ()
∋ˡ-take {Sg = []} {ℓ = suc ℓ} ()
∋ˡ-take {Sg = S ∷ Sg} {ℓ = suc ℓ} l-here = l-here
∋ˡ-take {Sg = S ∷ Sg} {ℓ = suc ℓ} (l-there p) = l-there (∋ˡ-take p)

∋a-prefix : ∀ {Sg ℓ Γ α} → take ℓ Sg ∣ ([] ∥ []) ∋a α → Sg ∣ Γ ∋a α
∋a-prefix (a-lvl l) = a-lvl (∋ˡ-take l)

wfᴿ-prefix : ∀ {Sg ℓ Γ n R} → take ℓ Sg ∣ ([] ∥ []) ⊢ᴿ[ n ] R
  → Sg ∣ Γ ⊢ᴿ[ n ] R
wfᴿ-prefix (wfᴿ-var a) = wfᴿ-var (∋a-prefix a)
wfᴿ-prefix (wfᴿ-bv lt) = wfᴿ-bv lt
wfᴿ-prefix wfᴿ-ℕ = wfᴿ-ℕ
wfᴿ-prefix wfᴿ-𝔹 = wfᴿ-𝔹
wfᴿ-prefix (wfᴿ-⇒ a b) = wfᴿ-⇒ (wfᴿ-prefix a) (wfᴿ-prefix b)
wfᴿ-prefix (wfᴿ-∀ a) = wfᴿ-∀ (wfᴿ-prefix a)

-- Over an EMPTY base only the store is reachable.
storeOk-RepsWf : ∀ {Sg} → StoreOk Sg → RepsWf Sg []
storeOk-RepsWf sok (r-lvl l) = wfᴿ-prefix (sok l)

------------------------------------------------------------------------
-- §3  A CONVERSION OVER AN EMPTY BASE IS FIXED BY A BASE RENAMING
------------------------------------------------------------------------
-- The reduction rule writes `d` itself into the `ν`'s body, and the
-- `ν` pushes a base entry — so the base weakening must leave `d`
-- alone.  It does: over an empty base no `bse` address is in scope, and
-- `renᵃᵉ` moves nothing else.  In v8 "nothing else" means a store
-- level, since a `∀` binds no address at all.

∋a-bse-[] : ∀ {Sg Ss j} → Sg ∣ (Ss ∥ []) ∋a bse j → ⊥
∋a-bse-[] ()

∋r-bse-[] : ∀ {Sg Ss j R} → Sg ∣ (Ss ∥ []) ∋r bse j := R → ⊥
∋r-bse-[] ()

addr-fix : ∀ {Sg Ss α} → Sg ∣ (Ss ∥ []) ∋a α → ∀ ρ → renᵃᵉ ρ α ≡ α
addr-fix {α = lvl ℓ} a ρ = refl
addr-fix {α = bse j} a ρ = ⊥-elim (∋a-bse-[] a)

rep-addr-fix : ∀ {Sg Ss α R} → Sg ∣ (Ss ∥ []) ∋r α := R
  → ∀ ρ → renᵃᵉ ρ α ≡ α
rep-addr-fix {α = lvl ℓ} p ρ = refl
rep-addr-fix {α = bse j} p ρ = ⊥-elim (∋r-bse-[] p)

mutual
  convElt-fixᵉ : ∀ {Sg Ssᵢ Ssₑ ĉ A B} (ρ : Renameᵇ)
    → Sg ∣ (Ssᵢ ∥ []) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ []) → renEltᵉ ρ ĉ ≡ ĉ
  convElt-fixᵉ ρ (conv-seal {X = Y} rep rd p) =
    cong (seal Y) (rep-addr-fix rep ρ)
  convElt-fixᵉ ρ (conv-unseal {X = Y} rep rd p na) =
    cong (unseal Y) (rep-addr-fix rep ρ)
  convElt-fixᵉ ρ (conv-hide {X = Y} sc wf p na) =
    cong (hide Y) (addr-fix sc ρ)
  convElt-fixᵉ ρ (conv-show {X = Y} sc wf p na) =
    cong (show Y) (addr-fix sc ρ)
  convElt-fixᵉ ρ (conv-fun ⊢s ⊢t) =
    cong₂ _↦_ (conv-fixᵉ ρ ⊢s) (conv-fixᵉ ρ ⊢t)
  convElt-fixᵉ ρ (conv-all ⊢s) = cong all (conv-fixᵉ ρ ⊢s)

  conv-fixᵉ : ∀ {Sg Ssᵢ Ssₑ c A B} (ρ : Renameᵇ)
    → Sg ∣ (Ssᵢ ∥ []) ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ []) → renConvᵉ ρ c ≡ c
  conv-fixᵉ ρ (conv-id wf) = refl
  conv-fixᵉ ρ (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) with conv-base tl
  conv-fixᵉ ρ (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl =
    cong₂ _∷ᶜ_ (convElt-fixᵉ ρ hd) (conv-fixᵉ ρ tl)

------------------------------------------------------------------------
-- §4  A BASE RENAMING CARRIES `NameFn`
------------------------------------------------------------------------

namefn-ren : ∀ {Sg ρ Γ Γ′} → Renamesᵇ Sg ρ Γ Γ′ → NameFn Γ → NameFn Γ′
namefn-ren r nf p q with ren-n⁻ r p | ren-n⁻ r q
namefn-ren r nf p q | β , p′ , e₁ | γ , q′ , e₂
  with ren-inj r (trans (sym e₁) e₂)
namefn-ren r nf p q | β , p′ , e₁ | γ , q′ , e₂ | refl = nf p′ q′

------------------------------------------------------------------------
-- §5  A CLOSED TYPE'S REPRESENTATION READS BACK ANYWHERE
------------------------------------------------------------------------
-- `TyBeta` quotes and reads back in the SAME context.  `TyWrap` does
-- not: `A` is well formed at the redex's Δ, while the builder's
-- read-back is demanded at the conversion's INTERIOR Δᵢ, whose name
-- assignments are different ones.  With `A` closed the two agree — the
-- only names the reading mentions are the `∀`-binders inside `A`
-- itself.  This is the FIRST place `Closedᵗ A` is spent.
--
-- In v7 those binders were ADDRESSES, so this section had to identify
-- the address a name below the prefix denotes (`binds-addr`).  In v8
-- they are type variables: a name below the prefix is not assigned to
-- anything, it is `∀`-BOUND, and `quote-bv`/`read-bv` carry it across
-- with no address in sight.

binds : ℕ → List StackEnt
binds zero = []
binds (suc n) = bind ∷ binds n

-- nothing below a prefix of `n` binders is assigned an address
binds-∌ : ∀ {n Ss Bs Z α} → Z < n → (binds n ++ Ss ∥ Bs) ∋n Z := α → ⊥
binds-∌ {n = zero} ()
binds-∌ {n = suc n} {Z = zero} lt ()
binds-∌ {n = suc n} {Z = suc Z} (s≤s lt) (n-skip-bind p) = binds-∌ lt p

-- and which binder it names depends on the prefix alone
binds-b : ∀ {n Ss Ss′ Z i} → Z < n → (binds n ++ Ss) ∋b Z at i
  → (binds n ++ Ss′) ∋b Z at i
binds-b {n = zero} ()
binds-b {n = suc n} lt b-here = b-here
binds-b {n = suc n} (s≤s lt) (b-bind p) = b-bind (binds-b lt p)

quote-read-closed : ∀ {Sg n Ss Ss′ Bs Bs′ A R}
  → NoFreeᵗ n A
  → Sg ∣ (binds n ++ Ss ∥ Bs) ⊢⌊ A ⌋ R
  → Sg ∣ (binds n ++ Ss′ ∥ Bs′) ⊢ R ⇓ A
quote-read-closed (nf-var lt) (quote-var n) = ⊥-elim (binds-∌ lt n)
quote-read-closed (nf-var lt) (quote-bv b) = read-bv (binds-b lt b)
quote-read-closed nf-ℕ quote-ℕ = read-ℕ
quote-read-closed nf-𝔹 quote-𝔹 = read-𝔹
quote-read-closed (nf-⇒ a b) (quote-⇒ p q) =
  read-⇒ (quote-read-closed a p) (quote-read-closed b q)
quote-read-closed {n = n} (nf-∀ a) (quote-∀ p) =
  read-∀ (quote-read-closed {n = suc n} a p)

quote-read-anywhere : ∀ {Sg Γ Γ′ A R} → Closedᵗ A → Sg ∣ Γ ⊢⌊ A ⌋ R
  → Sg ∣ Γ′ ⊢ R ⇓ A
quote-read-anywhere cl q = quote-read-closed {n = zero} cl q

------------------------------------------------------------------------
-- §6  PRESERVATION FOR `TyWrap`
------------------------------------------------------------------------
-- The shape, side by side with `preserve-TyBeta`:
--
--   (Λ V) ⟨ c ⟩ • B [ A ]  —→  ν R ∙ (V ⟨ instReveal 0 (bse 0) A d ⟩)
--
-- `⊢⟨⟩` splits the value into `⊢Λ`'s body `V ⦂ A₀` at the conversion's
-- INTERIOR Δᵢ and `c ∶ ∀ A₀ ⇝ ∀ B ⊣ Δ`.  `allView-typing` takes `c` to
-- `d ∶ A₀ ⇝ B` under one more binder assignment; `instReveal` then
-- composes the builder with the annotation substitution,
--
--   +0(d) = revTy 0 (bse 0) A A₀  ⨟  d[0 := A]
--
-- and the two halves meet at `closeAt 0 A A₀`.  The `ν` re-binds the
-- `Λ`'s own `bse zero` WITH its representation (`⊢-grow bg-here`), the
-- builder crosses it by `pop-here`, and `substAnn` drops the `∀`'s
-- binder slot, landing at the `ν`'s own context.  `closeAt-single`
-- turns the target `closeAt 0 A B` into `⊢•[]`'s result type `B [ A ]ᵗ`.
--
-- THE EXTRA PREMISES, and nothing else:
--
--   * `Closedᵗ A`  — the KNOWN GAP, spent THREE times: §5's read-back,
--     `wf-closed` for `substAnn`'s well-formedness premise on the slot's
--     type, and `closed-avoids`/`closed-tyOut` for its `SAvoids`
--     premise.  See §8.1: a NON-closed A really does break the
--     annotation equation at a crossing whose name it mentions.
--   * `StepFix zero d` and `slotOut d zero ≡ zero` — see §8.2.  These
--     are what is left of v7's `SlotFree zero d`, and they are much
--     weaker: the atomic constructors of `StepFix` carry nothing at
--     all, so the probe of §8.2 — which REFUTED `SlotFree` — satisfies
--     both (`stepfixₚ`, `slotₚ`).  What is left says only that the slot
--     index comes back to itself across an `↦`'s components, across an
--     `all`'s body, and across `d` as a whole, which is what
--     `substAnnElt`'s own equations for those three assume.
--   * `srcᶜ d ≢ nothing` — `instReveal`'s OTHER branch, `show X α ∷ᶜ d`,
--     is ill-typed at a `TyWrap` redex; see §9.3.
--
-- The representation side condition `RepsWf` is NOT a premise: §1
-- derives it from `StoreOk Sg`, which the theorem already carries.

tyWrapOk′ : ∀ {Sg Δ V c d A B R C}
  → StoreOk Sg → Flat Δ → NameFn Δ → Scoped Sg Δ
  → Closedᵗ A
  → StepFix zero d
  → slotOut d zero ≡ zero
  → ¬ (srcᶜ d ≡ nothing)
  → allView c ≡ just d
  → Sg ∣ Δ ⊢⌊ A ⌋ R
  → Sg ∣ Δ ∣ [] ⊢ ((Λ V) ⟨ c ⟩) • B [ A ] ⦂ C
  → Sg ∣ Δ ∣ [] ⊢ ν R ∙ (V ⟨ instReveal zero (bse zero) A d ⟩) ⦂ C
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA sf slotOk
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  with flat-bas fl | flat-bas (conv-flat ⊢c fl)
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA sf slotOk
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl with allView-typing nfΔ ⊢c eq
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA sf slotOk
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd with srcᶜ d | srcᶜ-sound ⊢d | srcOk

tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA sf slotOk
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | just A₁ | inj₂ () | _
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA sf slotOk
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | nothing | inj₁ () | _
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA sf slotOk
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | nothing | inj₂ refl | nj = ⊥-elim (nj refl)

tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA sf slotOk
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | just A₁ | inj₁ refl | _ =
  ⊢ν wfR
    (⊢⟨⟩ (⨟-NF (revTy zero (bse zero) A A₁) (substAnn zero A d))
         (⊢-grow bg-here ⊢V) ⊢conv)
  where
  Sh : Renamesᵇ Sg suc ([] ∥ []) ([] ∥ nuBind R ∷ [])
  Sh = ren-wk {e = nuBind R} sok

  wfR : Sg ∣ (Ssₑ ∥ []) ⊢ᴿ R
  wfR = quote-wfᴿ scp (flat-bindsBelow (fu-nobinds (flat-stk fl))) q

  -- the builder's read-back, demanded at the CONVERSION's interior
  rdA : Sg ∣ (⤒ Ssᵢ ∥ nuBind R ∷ []) ⊢ ⇑ᴿᵉ R ⇓ A
  rdA = read-ren (ren-stk {Ss = Ssᵢ} Sh) (quote-read-anywhere clA q)

  -- the builder's `wfR` slot: v7 asked that `R` be fixed by every
  -- address renaming, v8 that it have no free `` `ᵛ ``
  wfR′ : Sg ∣ (⤒ Ssᵢ ∥ nuBind R ∷ []) ⊢ᴿ ⇑ᴿᵉ R
  wfR′ = wfᴿ-ren (ren-stk {Ss = Ssᵢ} Sh) (wfᴿ-restk wfR)

  wfA₀ : (asgn (bse zero) ∷ ⤒ Ssᵢ ∥ nuBind R ∷ []) ⊢ᵗ A₁
  wfA₀ = wf-rebase (typing-wf ctxOk-[] ⊢V)

  ⊢rev : Sg ∣ (asgn (bse zero) ∷ ⤒ Ssᵢ ∥ nuBind R ∷ [])
           ⊢ revTy zero (bse zero) A A₁ ∶ A₁ ⇝ closeAt zero A A₁
           ⊣ (⤒ Ssᵢ ∥ nuBind R ∷ [])
  ⊢rev = revTy-typing zero (bse zero) A A₁ pop-here (notasgn-⤒ Ssᵢ)
           r-here rdA wfR′ wfA₀

  ⊢sub₀ : Sg ∣ (Ssᵢ ∥ []) ⊢ substAnn zero A d
            ∶ closeAt zero A A₁ ⇝ closeAt zero A B ⊣ (Ssₑ ∥ [])
  -- the slot is the `∀`'s own binder assignment, at index zero on
  -- BOTH sides, and `slotOk` says `d` puts it back where it was
  ⊢sub₀ = substAnn-typing′ (storeOk-RepsWf sok) (closed-avoids d clA) sf
            (wf-closed clA) slotOk (closed-tyOut d clA)
            drop-here drop-here ⊢d

  -- the `ν` pushes a base entry; §3 says it leaves the conversion alone
  ⊢subν : Sg ∣ (⤒ Ssᵢ ∥ nuBind R ∷ []) ⊢ substAnn zero A d
            ∶ closeAt zero A A₁ ⇝ closeAt zero A B
            ⊣ (⤒ Ssₑ ∥ nuBind R ∷ [])
  ⊢subν = subst (λ z → Sg ∣ (⤒ Ssᵢ ∥ nuBind R ∷ []) ⊢ z
                          ∶ closeAt zero A A₁ ⇝ closeAt zero A B
                          ⊣ (⤒ Ssₑ ∥ nuBind R ∷ []))
            (conv-fixᵉ suc ⊢sub₀) (conv-ren Sh ⊢sub₀)

  ⊢conv : Sg ∣ (asgn (bse zero) ∷ ⤒ Ssᵢ ∥ nuBind R ∷ [])
            ⊢ (revTy zero (bse zero) A A₁ ⨟ substAnn zero A d)
            ∶ A₁ ⇝ B [ A ]ᵗ ⊣ (⤒ Ssₑ ∥ nuBind R ∷ [])
  ⊢conv = subst (λ T → Sg ∣ (asgn (bse zero) ∷ ⤒ Ssᵢ ∥ nuBind R ∷ [])
                          ⊢ (revTy zero (bse zero) A A₁ ⨟ substAnn zero A d)
                          ∶ A₁ ⇝ T ⊣ (⤒ Ssₑ ∥ nuBind R ∷ []))
            (closeAt-single A B)
            (⨟-typing (namefn-ren (ren-stk Sh) nfΔ) ⊢rev ⊢subν)

------------------------------------------------------------------------
-- §7  WHAT IS NOT CLOSED: `TyWrapOk` ITSELF
------------------------------------------------------------------------
-- `proof.PreserveTyDef.TyWrapOk` is `tyWrapOk′` MINUS the four extra
-- premises, so the wrapper
--
--   tyWrapOk : TyWrapOk
--   tyWrapOk sok fl nf scp eq q ⊢M =
--     tyWrapOk′ sok fl nf scp {- Closedᵗ A -} {- StepFix zero d -}
--                             {- slotOut d zero ≡ zero -}
--                             {- srcᶜ d ≢ nothing -} eq q ⊢M
--
-- cannot be written: none of them is derivable from the redex.  §8
-- gives a probe for each.  The repairs they call for live in files
-- this module may not touch:
--
--   (1) `substAnn` now THREADS the slot and `S` along the spine
--       (`substAnnOut`), which is what removed v7's `SlotFree` — the
--       §8.2 probe below, which REFUTED it, satisfies what took its
--       place.  What `Closedᵗ A` still buys is §5's read-back plus
--       `SubstAnnTyping.SAvoids`: going outward across an `unseal`/
--       `show`, `S` must not mention the name the crossing removes,
--       and across a `seal`/`hide` it must not mention the one the
--       frame gains — see §8.1, where a NON-closed `A` breaks the
--       annotation equation outright.  (strong/Conversion.agda)
--
--   (2) `allView`'s `all⁺` must not let a NESTED `all s` contribute
--       `elts s` unshifted: those elements keep their own names, and
--       a name 0 among them sits AT the slot `substAnn` is removing.
--       That no longer makes the redex ILL TYPED — §8.2 now goes
--       through — but it is still what puts an `asgn` above the slot.
--       (strong/Conversion.agda, `all⁺ (all s) = just (elts s)`)
--
--   (3) `instReveal`'s `nothing` branch, `show X α ∷ᶜ c`, crosses ONE
--       assignment where the redex needs the `∀`'s binder slot to
--       DISAPPEAR.  (strong/ConversionReduction.agda)
--
--   (4) `slotOut d zero ≡ zero` — and the `↦`/`all` equations inside
--       `StepFix` — say the slot index returns to itself.  They are
--       NOT derivable: `substAnnElt` hands an `↦`'s two components the
--       SAME slot index although they run in opposite directions, and
--       with Γᵢ = asgn α ∷ bind ∷ Ss, Γₑ = bind ∷ Ss the components
--       `show 0 α ∷ᶜ id` and `hide 0 α ∷ᶜ id` move the slot 1 ↦ 0.
--       The repair would be for `substAnnElt` to step the index into
--       the contravariant component too.  (strong/Conversion.agda)

------------------------------------------------------------------------
-- §8  THE PROBES
------------------------------------------------------------------------

-- 8.1  `Closedᵗ A` — `S` may not mention a name the spine moves.
--
-- Take the §14-shaped word `d = show 1 (lvl 0) ∷ᶜ id (` 0)` under the
-- slot X = 0, and instantiate at the type argument `S = ` 0` — a
-- variable that IS in scope at the redex (a sealed name), so a
-- perfectly legal `•B[A]`, but not closed.  Going outward the `show`
-- REMOVES the name 1, so `substAnn` re-expresses S by
-- `renameᵗ (nameSub 1)`, and the slot moves to `nameSub 1 0 = 0`.
-- `conv-show` states its source as `renameᵗ (shiftAtᵗ (nameSub 0 1))`
-- of its target, so the equation `substAnn-typing` must discharge at
-- this element (`closeAt-unshift`, with A = ` 0) has the two sides:
--
--   closeAt 0 (` 0) (renameᵗ (shiftAtᵗ 1) (` 0))              =  ` 0
--   renameᵗ (shiftAtᵗ (nameSub 0 1))
--     (closeAt (nameSub 1 0) (renameᵗ (nameSub 1) (` 0)) (` 0)) =  ` 1
--
-- The interior demands `` ` 0 `` (the slot's own variable, read under
-- the crossing) and the substituted annotation supplies `` ` 1 ``.
-- `SAvoids`' premise for a `show` at name Y is exactly what fails:
-- `Avoidᵗ 0 (` 0)` is false, and 0 is `nameSub 0 1`, the name the
-- dropped frame loses here.
avoid-needed :
  ¬ (closeAt zero (` zero) (renameᵗ (shiftAtᵗ 1) (` zero))
      ≡ renameᵗ (shiftAtᵗ (nameSub zero 1))
          (closeAt (nameSub 1 zero) (renameᵗ (nameSub 1) (` zero))
            (` zero)))
avoid-needed ()

-- 8.2  THE PROBE THAT BOUGHT THE THREADING: a REDEX whose `d` has a
-- crossing at name 0.
--
-- `all⁺` does shift the name of every `hide`/`show` it lifts, so those
-- land at `suc X > 0`.  But `all⁺ (all s) = just (elts s)` passes a
-- nested conversion's elements through UNSHIFTED, and those keep their
-- own names — `conv-all` only insists that s's two contexts both begin
-- with a `bind`, not that s's crossings stay below it.  Here is a
-- well-typed, normal, INERT value at a flat scoped context whose
-- `allView` has crossings at name 0 in both directions.
--
-- In v7 this REFUTED `SlotFree zero sₚ`: its `sf-hide` demanded
-- `0 < 0`.  With the slot threaded the conditions that took its place
-- HOLD of exactly this word (`stepfixₚ`, `slotₚ` below) — the hide
-- moves the slot 0 ↦ 1, the `↦` keeps it at 1, the show moves it back
-- 1 ↦ 0 — which is the whole point of the change.  What is left to ask
-- of the `↦` is only that its two components agree about where the
-- slot is, and here they do, both being identities.

private
  Sgₚ : Store
  Sgₚ = `ℕᴿ ∷ []

  sokₚ : StoreOk Sgₚ
  sokₚ l-here = wfᴿ-ℕ

  -- `lvl 0` carries no name in `bind ∷ [] ∥ []`
  naₚ : NotAssigned (bind ∷ [] ∥ []) (lvl zero)
  naₚ (n-skip-bind ())

  scₚ : Sgₚ ∣ (bind ∷ [] ∥ []) ∋a lvl zero
  scₚ = a-lvl l-here

  wfℕℕ : ∀ {Ss Bs} → (Ss ∥ Bs) ⊢ᵗ (`ℕ ⇒ `ℕ)
  wfℕℕ = wf-⇒ wf-ℕ wf-ℕ

  -- the `↦` between the two crossings is what keeps them from fusing
  sₚ : Conv
  sₚ = hide zero (lvl zero) ∷ᶜ (id `ℕ ↦ id `ℕ) ∷ᶜ show zero (lvl zero)
         ∷ᶜ id (`ℕ ⇒ `ℕ)

  cₚ : Conv
  cₚ = all sₚ ∷ᶜ id (`∀ (`ℕ ⇒ `ℕ))

  ⊢sₚ : Sgₚ ∣ (bind ∷ [] ∥ []) ⊢ sₚ ∶ (`ℕ ⇒ `ℕ) ⇝ (`ℕ ⇒ `ℕ)
          ⊣ (bind ∷ [] ∥ [])
  ⊢sₚ = conv-cons (conv-hide scₚ wfℕℕ pop-here naₚ)
          (conv-cons (conv-fun (conv-id wf-ℕ) (conv-id wf-ℕ))
            (conv-cons (conv-show scₚ wfℕℕ pop-here naₚ)
              (conv-id wfℕℕ)))

  ⊢cₚ : Sgₚ ∣ ([] ∥ []) ⊢ cₚ ∶ `∀ (`ℕ ⇒ `ℕ) ⇝ `∀ (`ℕ ⇒ `ℕ) ⊣ ([] ∥ [])
  ⊢cₚ = conv-cons (conv-all ⊢sₚ) (conv-id (wf-∀ wfℕℕ))

  nfsₚ : NF sₚ
  nfsₚ = nf-cons nf-hide
           (nf-cons (nf-fun nf-id nf-id)
             (nf-cons nf-show nf-id irr-id) (irr-cons refl))
           (irr-cons refl)

  nfcₚ : NF cₚ
  nfcₚ = nf-cons (nf-all nfsₚ) nf-id irr-id

  -- the view answers, and it answers with `sₚ` itself
  allViewₚ : allView cₚ ≡ just sₚ
  allViewₚ = refl

  Vₚ : Term
  Vₚ = ƛ `ℕ ∙ ` zero

  ⊢Vₚ : Sgₚ ∣ (asgn (bse zero) ∷ [] ∥ addr ∷ []) ∣ [] ⊢ Vₚ ⦂ (`ℕ ⇒ `ℕ)
  ⊢Vₚ = ⊢ƛ wf-ℕ (⊢` here)

  valueₚ : Value ((Λ Vₚ) ⟨ cₚ ⟩)
  valueₚ = V⟨⟩ (SΛ (Vs Sƛ)) nfcₚ (inert-all allViewₚ)

  -- ... and this really is a `TyWrap` redex, at a flat scoped context
  redexₚ : Sgₚ ∣ ([] ∥ []) ∣ [] ⊢ ((Λ Vₚ) ⟨ cₚ ⟩) • (`ℕ ⇒ `ℕ) [ `ℕ ]
             ⦂ ((`ℕ ⇒ `ℕ) [ `ℕ ]ᵗ)
  redexₚ = ⊢•[] (⊢⟨⟩ nfcₚ (⊢Λ (Vs Sƛ) ⊢Vₚ) ⊢cₚ) wf-ℕ

  -- ... and the conditions that replaced `SlotFree` hold of it: the
  -- slot travels 0 ↦ 1 ↦ 1 ↦ 0 along the spine
  slotₚ : slotOut sₚ zero ≡ zero
  slotₚ = refl

  stepfixₚ : StepFix zero sₚ
  stepfixₚ = fx-cons fx-hide
               (fx-cons (fx-fun fx-id fx-id refl refl)
                 (fx-cons fx-show fx-id))

  -- the type argument is ground, so the `S`-condition is free too
  avoidsₚ : SAvoids zero `ℕ sₚ
  avoidsₚ = closed-avoids sₚ nf-ℕ

-- 8.3  `srcᶜ d ≢ nothing` — `instReveal`'s other branch is ill-typed.
--
-- When `srcᶜ d` is undefined — `d` seal-headed, which `allView` can
-- certainly produce, since `all⁺ (all s) = just (elts s)` passes a
-- `seal` straight through — `instReveal X α S d` is `show X α ∷ᶜ d`.
-- At the redex the whole conversion must run from the `ν`'s interior
-- `asgn (bse 0) ∷ ⤒ Ssᵢ ∥ nuBind R ∷ []` to its exterior, while
-- `allView-typing` hands `d` a context whose stack is `bind ∷ ⤒ Ssᵢ`.
-- The head `show 0 (bse 0)` is typed by `pop-here` — the only pop at
-- name 0 — so the context it hands the tail is `⤒ Ssᵢ`, and
--
--     ⤒ Ssᵢ  ≢  bind ∷ ⤒ Ssᵢ
--
-- for the reason below.  The branch crosses ONE assignment where the
-- rule needs the `∀`'s binder slot to be REMOVED, which is what
-- `substAnn` does and a bare identity crossing does not.
∷-≢ : ∀ {A : Set} (x : A) (xs : List A) → ¬ (xs ≡ x ∷ xs)
∷-≢ x [] ()
∷-≢ x (y ∷ xs) ()
