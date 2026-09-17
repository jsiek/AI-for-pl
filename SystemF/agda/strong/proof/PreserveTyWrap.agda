module strong.proof.PreserveTyWrap where

-- Strong System F v8 — preservation for `TyWrap`.
--
--   ((Λ V) ⟨ c ⟩) • B [ A ]
--     —→  ν R ∙ (V ⟨ instReveal Σ (bind ∷ Δᵢ) 0 (bse 0) A d ⟩)
--            if allView c ≡ just d and interior c Δ ≡ just Δᵢ
--
-- This module discharges `proof.PreserveTyDef.TyWrapOk` up to ONE side
-- condition the INGREDIENTS require but the redex does not supply.  See
-- §7 for the exact statement proved (`tyWrapOk′`) and §8 for the probes.
--
-- ONE PREMISE WHERE THERE WERE TWO (2026-09-17).  `¬ (srcᶜ d ≡ nothing)`
-- is gone, because `srcᶜ` is gone as a partial function: it takes the
-- store and the conversion's INTERIOR CONTEXT and reads a seal's source
-- off α's representation there — which is where `conv-seal` gets it —
-- so it is total on typed conversions (`proof.SrcTyping.srcᶜ-sound`)
-- and `instReveal` has a single branch.  §8.3, which used to REFUTE
-- `TyWrapOk` on a spine `srcᶜ` could not read, is now a positive check:
-- the same redex reduces to a term this module types.
--
-- `Closedᵗ A` IS NOT REMOVABLE, and the reason is not a gap in this
-- proof: §8.1b REFUTES `TyWrapOk` itself, with a well-typed `TyWrap`
-- redex whose reduct has no typing derivation at all.
-- `tyWrapOk-refuted` states the consequence: `TyWrap` does not preserve
-- typing as the rule stands, and `proof.Preservation.Main` cannot be
-- instantiated until the way `A` crosses into the conversion's interior
-- is changed.
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
--     `substAnn` threads the slot along the spine.  Its last residue,
--     `StepFix`, is gone as well: `substAnn` steps the index into an
--     `↦`'s contravariant component, and `slotOut-bind` derives the
--     rest from the bind skeleton (`proof.SubstAnnTyping` §8b).
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
open import Data.Bool using (true)
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
open import strong.TermSubst
open import strong.Reduction

open import strong.proof.PreserveTyDef using (TyWrapOk)
open import strong.proof.Flat using
  (Flat; Flatn; flat; conv-flat; fu-nobinds; wfᴿ-restk; fu-[]; fu-asgn)
open Flatn
open import strong.proof.Scoped using
  (Scoped; quote-wfᴿ; flat-bindsBelow)
open import strong.proof.Interior using (pop-base; conv-interior)
open import strong.proof.AddrWeaken using
  (Renamesᵇ; ren-wk; ren-stk; read-ren; conv-ren; conv-base; wfᴿ-ren)
open Renamesᵇ
open import strong.proof.BuilderTyping using
  (BaseGrow; bg-here; ⊢-grow; revTy-typing; closeAt-single; notasgn-⤒)
open import strong.proof.SubstAnnTyping using
  (NoFreeᵗ; nf-var; nf-ℕ; nf-𝔹; nf-⇒; nf-∀; Closedᵗ; wf-closed;
   RepsWf; substAnn-typing′;
   SAvoids; closed-avoids; closed-tyOut;
   slotOut-bind; drop-here)
open import strong.proof.CompositionTyping using
  (⨟-typing; conv-namefn; namefn-bind)
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
-- THE ONE EXTRA PREMISE, and nothing else:
--
--   * `Closedᵗ A`  — the KNOWN GAP, spent THREE times: §5's read-back,
--     `wf-closed` for `substAnn`'s well-formedness premise on the slot's
--     type, and `closed-avoids`/`closed-tyOut` for its `SAvoids`
--     premise.  See §8.1: a NON-closed A really does break the
--     annotation equation at a crossing whose name it mentions.
--
-- `srcᶜ d ≢ nothing` IS GONE (2026-09-17).  `srcᶜ` is now total: it
-- takes the store and the conversion's interior context and reads a
-- seal's source off α's representation there, which is where
-- `conv-seal` already gets it.  `proof.SrcTyping.srcᶜ-sound` says the
-- answer IS the source, so `instReveal` has one branch and the premise
-- has nothing left to exclude.  §8.3 is now a positive check on the
-- very redex that used to refute it.
--
-- AND NOTHING ABOUT THE SLOT.  v7's `SlotFree zero d` became `StepFix
-- zero d` and `slotOut d zero ≡ zero`; both are GONE.  `substAnn` now
-- steps the slot index into an `↦`'s contravariant component and under
-- an `all`'s binder, and `proof.SubstAnnTyping.slotOut-bind` DERIVES
-- the last of it from the typing: `d` runs between two contexts that
-- both begin with the `∀`'s binder assignment, so it cannot move the
-- slot off index zero.  The §8.2 probe — which REFUTED `SlotFree` —
-- now needs no side condition at all.
--
-- The representation side condition `RepsWf` is NOT a premise: §1
-- derives it from `StoreOk Sg`, which the theorem already carries.
--
-- The interior equation is not a side condition either: it is part of
-- the RULE (the same walk `ξ-⟨⟩` performs), and `conv-interior` pins
-- it to the context `⊢c` names.

tyWrapOk′ : ∀ {Sg Δ Δᵢ V c d A B R C}
  → StoreOk Sg → Flat Δ → NameFn Δ → Scoped Sg Δ
  → Closedᵗ A
  → allView c ≡ just d
  → interior c Δ ≡ just Δᵢ
  → Sg ∣ Δ ⊢⌊ A ⌋ R
  → Sg ∣ Δ ∣ [] ⊢ ((Λ V) ⟨ c ⟩) • B [ A ] ⦂ C
  → Sg ∣ Δ ∣ [] ⊢ ν R ∙ (V ⟨ instReveal Sg (bind ∷ stk Δᵢ ∥ bas Δᵢ)
                               zero (bse zero) A d ⟩) ⦂ C
tyWrapOk′ {Sg = Sg} {Δ = Ssₑ ∥ Bsₑ} {V = V} {c = c} {d = d} {A = A}
  {B = B} {R = R} sok fl nfΔ scp clA
  eq ieq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  with trans (sym ieq) (conv-interior ⊢c)
tyWrapOk′ {Sg = Sg} {Δ = Ssₑ ∥ Bsₑ} {V = V} {c = c} {d = d} {A = A}
  {B = B} {R = R} sok fl nfΔ scp clA
  eq ieq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl with flat-bas fl | flat-bas (conv-flat ⊢c fl)
tyWrapOk′ {Sg = Sg} {Δ = Ssₑ ∥ Bsₑ} {V = V} {c = c} {d = d} {A = A}
  {B = B} {R = R} sok fl nfΔ scp clA
  eq ieq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | refl with allView-typing nfΔ ⊢c eq
tyWrapOk′ {Sg = Sg} {Δ = Ssₑ ∥ Bsₑ} {V = V} {c = c} {d = d} {A = A}
  {B = B} {R = R} sok fl nfΔ scp clA
  eq ieq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | refl | ⊢d , nfd
  with srcᶜ Sg (bind ∷ Ssᵢ ∥ []) d
     | srcᶜ-sound (namefn-bind (conv-namefn ⊢c nfΔ)) ⊢d
tyWrapOk′ {Sg = Sg} {Δ = Ssₑ ∥ Bsₑ} {V = V} {c = c} {d = d} {A = A}
  {B = B} {R = R} sok fl nfΔ scp clA
  eq ieq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | refl | ⊢d , nfd | A₁ | refl =
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
  -- BOTH sides, and `slotOut-bind` — the bind-rank argument — says `d`
  -- puts it back where it was
  ⊢sub₀ = substAnn-typing′ (storeOk-RepsWf sok) (closed-avoids d clA)
            (wf-closed clA) (slotOut-bind ⊢d) (closed-tyOut d clA)
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
-- §7  WHAT IS NOT CLOSED: `TyWrapOk` IS FALSE
------------------------------------------------------------------------
-- `proof.PreserveTyDef.TyWrapOk` is `tyWrapOk′` MINUS `Closedᵗ A`, so
-- the wrapper
--
--   tyWrapOk : TyWrapOk
--   tyWrapOk sok fl nf scp eq q ieq ⊢M =
--     tyWrapOk′ sok fl nf scp {- Closedᵗ A -} eq ieq q ⊢M
--
-- cannot be written — and NOT because the premise is merely underived.
-- §8.1b exhibits a well-typed `TyWrap` redex whose reduct is not
-- typable at any type: `TyWrapOk` is REFUTED (`tyWrapOk-refuted`), so
-- what is wrong is the rule, not the proof.  What the probes pin down:
--
--   (1) `Closedᵗ A` — §8.1.  `A` is a type of the redex's EXTERIOR Δ,
--       and the rule writes it into a conversion whose INTERIOR is a
--       different context: the spine's crossings create and destroy
--       exactly the assignments A may name.  §8.1a is the pointwise
--       failure of `substAnn`'s annotation equation; §8.1b is the
--       redex.  There `d = hide 1 (lvl 0) ∷ᶜ id (` 0 ⇒ `𝔹)` and
--       `A = ` 0` — legal at Δ, since the `hide` is what PUT the
--       assignment there — and the `seal` that `revTy` emits for A has
--       to read its representation back at the interior, where the
--       stack is empty and there is no name to read it to.  `Closedᵗ A`
--       is exactly the condition that A means the same thing at both
--       ends.  (strong/Conversion.agda, strong/Reduction.agda)
--
--   (2) `allView`'s `all⁺` must not let a NESTED `all s` contribute
--       `elts s` unshifted: those elements keep their own names, and
--       a name 0 among them sits AT the slot `substAnn` is removing.
--       That no longer makes the redex ILL TYPED — §8.2 now goes
--       through — but it is still what puts an `asgn` above the slot.
--       (strong/Conversion.agda, `all⁺ (all s) = just (elts s)`)
--
--   (3) §8.3 is no longer a probe against the rule: it is the redex
--       that `srcᶜ`'s partiality used to break, and `srcᶜ` reading the
--       CONTEXT is what fixed it.  It is kept as a regression, with the
--       two context lookups the answer comes from spelled out.
--       (strong/Ctx.agda, strong/ConversionReduction.agda)

------------------------------------------------------------------------
-- §8  THE PROBES
------------------------------------------------------------------------

-- 8.1a  `Closedᵗ A` — `S` may not mention a name the spine moves.
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

-- 8.1b  ... AND THE REDEX ITSELF.  8.1a is an equation; here is a
-- well-typed `TyWrap` redex with an OPEN type argument whose reduct
-- has no typing derivation at all — so `Closedᵗ A` is not an artefact
-- of how `substAnn-typing` is stated.
--
-- The spine is one `hide`, which going OUTWARD adds the assignment
-- `1 := lvl 0`; the redex's Δ therefore HAS that assignment, and
-- `A = ` 0` names it — `⊢•[]`'s `Δ ⊢ᵗ A` is satisfied and `⌊·⌋` quotes
-- it to `` `ᵃ (lvl 0) ``.  Going inward the assignment is gone.  So
-- `revTy 0 (bse 0) (` 0) (` 0 ⇒ `𝔹)` hits, emits
-- `concTy 0 (bse 0) (` 0) (` 0) = seal 0 (bse 0) ∷ᶜ id (` 0)` for the
-- domain, and `conv-seal` must read `` `ᵃ (lvl 0) `` back at the
-- element's own interior — which the `hide` in the tail pins down to a
-- context with an EMPTY stack (`tail-openₘ`).  `read-var` has no name
-- to land on.
private
  Sgₘ : Store
  Sgₘ = `𝔹ᴿ ∷ []

  sokₘ : StoreOk Sgₘ
  sokₘ l-here = wfᴿ-𝔹

  Γᵢₘ Γₑₘ Δₘ : Ctxᵗ
  Γᵢₘ = bind ∷ [] ∥ []
  Γₑₘ = bind ∷ asgn (lvl zero) ∷ [] ∥ []
  Δₘ = asgn (lvl zero) ∷ [] ∥ []

  naₘ : NotAssigned Γᵢₘ (lvl zero)
  naₘ (n-skip-bind ())

  Tₘ : Ty
  Tₘ = ` zero ⇒ `𝔹

  dₘ : Conv
  dₘ = hide 1 (lvl zero) ∷ᶜ id Tₘ

  ⊢dₘ : Sgₘ ∣ Γᵢₘ ⊢ dₘ ∶ Tₘ ⇝ Tₘ ⊣ Γₑₘ
  ⊢dₘ = conv-cons
          (conv-hide (a-lvl l-here) (wf-⇒ (wf-var t-here) wf-𝔹)
            (pop-bind pop-here) naₘ)
          (conv-id (wf-⇒ (wf-var t-here) wf-𝔹))

  -- `srcᶜ` answers here with no help from the context beyond what the
  -- syntax already gave: the spine is a crossing, not a seal
  srcₘ : srcᶜ Sgₘ Γᵢₘ dₘ ≡ Tₘ
  srcₘ = refl

  nfdₘ : NF dₘ
  nfdₘ = nf-cons nf-hide nf-id irr-id

  cₘ : Conv
  cₘ = all dₘ ∷ᶜ id (`∀ Tₘ)

  ⊢cₘ : Sgₘ ∣ ([] ∥ []) ⊢ cₘ ∶ `∀ Tₘ ⇝ `∀ Tₘ ⊣ Δₘ
  ⊢cₘ = conv-cons (conv-all ⊢dₘ)
          (conv-id (wf-∀ (wf-⇒ (wf-var t-here) wf-𝔹)))

  nfcₘ : NF cₘ
  nfcₘ = nf-cons (nf-all nfdₘ) nf-id irr-id

  viewₘ : allView cₘ ≡ just dₘ
  viewₘ = refl

  Vₘ : Term
  Vₘ = ƛ (` zero) ∙ (# true)

  ⊢Vₘ : Sgₘ ∣ (asgn (bse zero) ∷ [] ∥ addr ∷ []) ∣ [] ⊢ Vₘ ⦂ Tₘ
  ⊢Vₘ = ⊢ƛ (wf-var t-here) ⊢#

  Rₘ : RepTy
  Rₘ = `ᵃ (lvl zero)

  qₘ : Sgₘ ∣ Δₘ ⊢⌊ ` zero ⌋ Rₘ
  qₘ = quote-var n-here-asgn

  -- the redex, at a flat scoped context with a name function
  redexₘ : Sgₘ ∣ Δₘ ∣ []
         ⊢ ((Λ Vₘ) ⟨ cₘ ⟩) • Tₘ [ ` zero ] ⦂ (Tₘ [ ` zero ]ᵗ)
  redexₘ = ⊢•[] (⊢⟨⟩ nfcₘ (⊢Λ (Vs Sƛ) ⊢Vₘ) ⊢cₘ) (wf-var t-here)

  valueₘ : Value ((Λ Vₘ) ⟨ cₘ ⟩)
  valueₘ = V⟨⟩ (SΛ (Vs Sƛ)) nfcₘ (inert-all viewₘ)

  -- the `all` element pops the assignment the `hide` carries, so the
  -- conversion's interior is the EMPTY context and `dₘ`'s is `Γᵢₘ`
  intₘ : interior cₘ Δₘ ≡ just ([] ∥ [])
  intₘ = refl

  stepₘ : Sgₘ ∣ Δₘ
        ⊢ ((Λ Vₘ) ⟨ cₘ ⟩) • Tₘ [ ` zero ]
        —→ ν Rₘ ∙ (Vₘ ⟨ instReveal Sgₘ Γᵢₘ zero (bse zero) (` zero) dₘ ⟩)
        ⊣ Sgₘ
  stepₘ = TyWrap valueₘ viewₘ qₘ intₘ

  flₘ : Flat Δₘ
  flₘ = flat (fu-asgn fu-[]) refl

  nfnₘ : NameFn Δₘ
  nfnₘ n-here-asgn n-here-asgn = refl
  nfnₘ n-here-asgn (n-skip-asgn ())
  nfnₘ (n-skip-asgn ()) q

  scpₘ : Scoped Sgₘ Δₘ
  scpₘ n-here-asgn = a-lvl l-here
  scpₘ (n-skip-asgn ())

  Wₘ : Conv
  Wₘ = ((seal zero (bse zero) ∷ᶜ id (` zero))
        ↦ (show zero (bse zero) ∷ᶜ id `𝔹))
       ∷ᶜ hide zero (lvl zero) ∷ᶜ id Tₘ

  builtₘ : instReveal Sgₘ Γᵢₘ zero (bse zero) (` zero) dₘ ≡ Wₘ
  builtₘ = refl

  id-ctxₘ : ∀ {Γ Γ′ A B C} → Sgₘ ∣ Γ ⊢ id A ∶ B ⇝ C ⊣ Γ′ → Γ ≡ Γ′
  id-ctxₘ (conv-id wf) = refl

  -- the `hide` tail pins the `↦`'s exterior to a context with an EMPTY
  -- stack: the crossing that carried the assignment is spent there
  tail-openₘ : ∀ {Γ₁ B C}
    → Sgₘ ∣ Γ₁ ⊢ hide zero (lvl zero) ∷ᶜ id Tₘ ∶ B ⇝ C
        ⊣ (asgn (lvl zero) ∷ [] ∥ nuBind Rₘ ∷ [])
    → Γ₁ ≡ ([] ∥ nuBind Rₘ ∷ [])
  tail-openₘ (conv-cons (conv-hide sc wf pop-here na) tl) with id-ctxₘ tl
  tail-openₘ (conv-cons (conv-hide sc wf pop-here na) tl) | refl = refl

  -- ... and there the `seal`'s read-back has no name to land on
  seal-⊥ₘ : ∀ {Γ′ A C}
    → ¬ (Sgₘ ∣ ([] ∥ nuBind Rₘ ∷ [])
           ⊢ seal zero (bse zero) ∷ᶜ id (` zero) ∶ A ⇝ C ⊣ Γ′)
  seal-⊥ₘ (conv-cons (conv-seal r-here (read-var ()) pop-here) tl)

  reduct-⊥ₘ : ∀ {C} → ¬ (Sgₘ ∣ Δₘ ∣ [] ⊢ ν Rₘ ∙ (Vₘ ⟨ Wₘ ⟩) ⦂ C)
  reduct-⊥ₘ (⊢ν wfR (⊢⟨⟩ nf (⊢ƛ wf ⊢#) (conv-cons (conv-fun ⊢s ⊢t) tl)))
    with tail-openₘ tl
  reduct-⊥ₘ (⊢ν wfR (⊢⟨⟩ nf (⊢ƛ wf ⊢#) (conv-cons (conv-fun ⊢s ⊢t) tl)))
    | refl = seal-⊥ₘ ⊢s

  -- so `TyWrapOk` fails already at a redex whose `srcᶜ d` answers
  closed-neededₘ : ¬ TyWrapOk
  closed-neededₘ ok =
    reduct-⊥ₘ (ok sokₘ flₘ nfnₘ scpₘ viewₘ qₘ intₘ redexₘ)

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
-- `0 < 0`.  With the slot threaded there is nothing left to ask of the
-- word at all — the hide moves the slot 0 ↦ 1, the `↦` keeps it at 1,
-- the show moves it back 1 ↦ 0, and `slotₚ` below just records the
-- round trip that `slotOut-bind` now derives.

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

  -- ... and the slot travels 0 ↦ 1 ↦ 1 ↦ 0 along the spine, which is
  -- what `slotOut-bind` reads off `⊢sₚ` with no premise
  slotₚ : slotOut sₚ zero ≡ zero
  slotₚ = refl

  slot-derivedₚ : slotOut sₚ zero ≡ zero
  slot-derivedₚ = slotOut-bind ⊢sₚ

  -- the type argument is ground, so the `S`-condition is free too
  avoidsₚ : SAvoids zero `ℕ sₚ
  avoidsₚ = closed-avoids sₚ nf-ℕ

-- 8.3  THE REDEX THAT USED TO REFUTE `TyWrapOk`, NOW A POSITIVE CHECK.
--
-- Until 2026-09-17 `srcᶜ` was partial and `instReveal` had a second
-- branch, `show X α ∷ᶜ substAnn X S c`.  That branch is `revTy`'s MISS
-- equation, so it is right precisely when X misses the spine's SOURCE.
-- For a SEAL-HEADED `d` the miss is free — the seal's source is the
-- read-back of a store entry, hence closed — which is why
-- `notes/SrcGap`'s word came out coherent.  It is NOT free when `srcᶜ`
-- gave out through a `↦`:
--
--     srcᶜ ((s ↦ t) ∷ᶜ c) | nothing = nothing     when srcᶜ t ≡ nothing
--
-- because the true source there is `target s ⇒ src t` and only the
-- RIGHT half is forced closed.  The redex below is exactly that shape:
-- `d = (s ↦ t) ∷ᶜ id (` 0 ⇒ ` 1)` with `t` seal-headed and
-- `s = show 1 (lvl 0) ∷ᶜ id (` 0)` running the other way, so the source
-- is `` ` 0 ⇒ `𝔹 `` — which no `show 0` can have, since `conv-show`
-- states its source as `renameᵗ (shiftAtᵗ 0) = renameᵗ suc` and that
-- never produces the name 0.  The reduct had no typing derivation at
-- any type, and `TyWrapOk` was refuted here.
--
-- `srcᶜ` ANSWERS on `dₖ` now, and it answers `` ` 0 ⇒ `𝔹 ``: the seal's
-- source is read off `lvl 0`'s representation at the element's own
-- interior (`repOf Sgₖ Γᵢₖ (lvl 0) ≡ just `𝔹ᴿ`, which `readOf` sends to
-- `` `𝔹 ``), and the `↦` puts `target s` on the left.  So `instReveal`
-- applies `revTy` at the REAL source: it SEALS the domain instead of
-- crossing past it, and `tyWrapOk′` types the reduct (`reduct-okₖ`).
-- The type argument is `ℕ — CLOSED, so §8.1's gap is not in the way.
private
  Sgₖ : Store
  Sgₖ = `𝔹ᴿ ∷ []

  sokₖ : StoreOk Sgₖ
  sokₖ l-here = wfᴿ-𝔹

  Γᵢₖ Γₑₖ Δₖ : Ctxᵗ
  Γᵢₖ = bind ∷ [] ∥ []
  Γₑₖ = bind ∷ asgn (lvl zero) ∷ [] ∥ []
  Δₖ = asgn (lvl zero) ∷ [] ∥ []

  naₖ : NotAssigned Γᵢₖ (lvl zero)
  naₖ (n-skip-bind ())

  sₖ tₖ dₖ : Conv
  sₖ = show 1 (lvl zero) ∷ᶜ id (` zero)
  tₖ = seal 1 (lvl zero) ∷ᶜ id (` 1)
  dₖ = (sₖ ↦ tₖ) ∷ᶜ id (` zero ⇒ ` 1)

  ⊢sₖ : Sgₖ ∣ Γₑₖ ⊢ sₖ ∶ ` zero ⇝ ` zero ⊣ Γᵢₖ
  ⊢sₖ = conv-cons
          (conv-show (a-lvl l-here) (wf-var t-here) (pop-bind pop-here) naₖ)
          (conv-id (wf-var t-here))

  ⊢tₖ : Sgₖ ∣ Γᵢₖ ⊢ tₖ ∶ `𝔹 ⇝ ` 1 ⊣ Γₑₖ
  ⊢tₖ = conv-cons
          (conv-seal (r-lvl l-here) read-𝔹 (pop-bind pop-here))
          (conv-id (wf-var (t-there t-here)))

  ⊢dₖ : Sgₖ ∣ Γᵢₖ ⊢ dₖ ∶ (` zero ⇒ `𝔹) ⇝ (` zero ⇒ ` 1) ⊣ Γₑₖ
  ⊢dₖ = conv-cons (conv-fun ⊢sₖ ⊢tₖ)
          (conv-id (wf-⇒ (wf-var t-here) (wf-var (t-there t-here))))

  -- WHERE THE SOURCE COMES FROM.  The syntax of `dₖ` does not carry it;
  -- the context does, and these are the two steps `conv-seal` takes.
  repₖ : repOf Sgₖ Γᵢₖ (lvl zero) ≡ just `𝔹ᴿ
  repₖ = refl

  readₖ : readOf Γᵢₖ `𝔹ᴿ ≡ just `𝔹
  readₖ = refl

  srcₖ : srcᶜ Sgₖ Γᵢₖ dₖ ≡ (` zero ⇒ `𝔹)
  srcₖ = refl

  nfdₖ : NF dₖ
  nfdₖ = nf-cons
           (nf-fun (nf-cons nf-show nf-id irr-id)
                   (nf-cons nf-seal nf-id irr-id))
           nf-id irr-id

  cₖ : Conv
  cₖ = all dₖ ∷ᶜ id (`∀ (` zero ⇒ ` 1))

  ⊢cₖ : Sgₖ ∣ ([] ∥ []) ⊢ cₖ ∶ `∀ (` zero ⇒ `𝔹) ⇝ `∀ (` zero ⇒ ` 1) ⊣ Δₖ
  ⊢cₖ = conv-cons (conv-all ⊢dₖ)
          (conv-id (wf-∀ (wf-⇒ (wf-var t-here) (wf-var (t-there t-here)))))

  nfcₖ : NF cₖ
  nfcₖ = nf-cons (nf-all nfdₖ) nf-id irr-id

  viewₖ : allView cₖ ≡ just dₖ
  viewₖ = refl

  Vₖ : Term
  Vₖ = ƛ (` zero) ∙ (# true)

  ⊢Vₖ : Sgₖ ∣ (asgn (bse zero) ∷ [] ∥ addr ∷ []) ∣ []
          ⊢ Vₖ ⦂ (` zero ⇒ `𝔹)
  ⊢Vₖ = ⊢ƛ (wf-var t-here) ⊢#

  redexₖ : Sgₖ ∣ Δₖ ∣ []
         ⊢ ((Λ Vₖ) ⟨ cₖ ⟩) • (` zero ⇒ ` 1) [ `ℕ ]
         ⦂ ((` zero ⇒ ` 1) [ `ℕ ]ᵗ)
  redexₖ = ⊢•[] (⊢⟨⟩ nfcₖ (⊢Λ (Vs Sƛ) ⊢Vₖ) ⊢cₖ) wf-ℕ

  qₖ : Sgₖ ∣ Δₖ ⊢⌊ `ℕ ⌋ `ℕᴿ
  qₖ = quote-ℕ

  clₖ : Closedᵗ `ℕ
  clₖ = nf-ℕ

  valueₖ : Value ((Λ Vₖ) ⟨ cₖ ⟩)
  valueₖ = V⟨⟩ (SΛ (Vs Sƛ)) nfcₖ (inert-all viewₖ)

  flₖ : Flat Δₖ
  flₖ = flat (fu-asgn fu-[]) refl

  nfnₖ : NameFn Δₖ
  nfnₖ n-here-asgn n-here-asgn = refl
  nfnₖ n-here-asgn (n-skip-asgn ())
  nfnₖ (n-skip-asgn ()) q

  scpₖ : Scoped Sgₖ Δₖ
  scpₖ n-here-asgn = a-lvl l-here
  scpₖ (n-skip-asgn ())

  -- the conversion's interior is the empty context, so `dₖ` is typed
  -- at `Γᵢₖ` — the context `TyWrap` hands to `instReveal`
  intₖ : interior cₖ Δₖ ≡ just ([] ∥ [])
  intₖ = refl

  stepₖ : Sgₖ ∣ Δₖ
        ⊢ ((Λ Vₖ) ⟨ cₖ ⟩) • (` zero ⇒ ` 1) [ `ℕ ]
        —→ ν `ℕᴿ ∙ (Vₖ ⟨ instReveal Sgₖ Γᵢₖ zero (bse zero) `ℕ dₖ ⟩)
        ⊣ Sgₖ
  stepₖ = TyWrap valueₖ viewₖ qₖ intₖ

  -- THE WORD.  `revTy` at `` ` 0 ⇒ `𝔹 `` HITS in the domain, so the
  -- contravariant component gets a `seal 0 (bse 0)` — the fresh
  -- binder's own crossing — which the `↦` fusion carries inside the
  -- component that `substAnn` produced.  The old branch's bare
  -- `show 0 (bse 0)` on top is gone.
  builtₖ : instReveal Sgₖ Γᵢₖ zero (bse zero) `ℕ dₖ
         ≡ ((show zero (lvl zero) ∷ᶜ seal zero (bse zero) ∷ᶜ id (` zero))
            ↦ (show zero (bse zero) ∷ᶜ seal zero (lvl zero) ∷ᶜ id (` zero)))
           ∷ᶜ id (`ℕ ⇒ ` zero)
  builtₖ = refl

  -- ... and the reduct that had NO typing derivation now has one, from
  -- the theorem itself
  reduct-okₖ : Sgₖ ∣ Δₖ ∣ []
             ⊢ ν `ℕᴿ ∙ (Vₖ ⟨ instReveal Sgₖ Γᵢₖ zero (bse zero) `ℕ dₖ ⟩)
             ⦂ ((` zero ⇒ ` 1) [ `ℕ ]ᵗ)
  reduct-okₖ = tyWrapOk′ sokₖ flₖ nfnₖ scpₖ clₖ viewₖ intₖ qₖ redexₖ

-- THE CONSEQUENCE.  `TyWrapOk` is still not merely unproved: §8.1b
-- REFUTES it, at a redex whose `srcᶜ d` answers and whose only defect
-- is an OPEN type argument.  So `Closedᵗ A` is load-bearing and
-- `proof.Preservation.Main` stays uninstantiated until `TyWrap` (or
-- the way `A` crosses into the conversion's interior) is changed.  The
-- SECOND refutation is gone: §8.3's redex, which used to have no
-- typing derivation at all, now reduces to a typable term.
tyWrapOk-refuted : ¬ TyWrapOk
tyWrapOk-refuted = closed-neededₘ
