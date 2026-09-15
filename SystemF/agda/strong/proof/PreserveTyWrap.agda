module strong.proof.PreserveTyWrap where

-- Strong System F v8 — preservation for `TyWrap`.
--
--   ((Λ V) ⟨ c ⟩) • B [ A ]  —→  ν R ∙ (V ⟨ instReveal 0 (bse 0) A d ⟩)
--                                          if allView c ≡ just d
--
-- This module discharges `proof.PreserveTyDef.TyWrapOk` up to the side
-- conditions the INGREDIENTS require but the redex does not supply.
-- See §8 for the exact statement proved (`tyWrapOk′`) and §9 for the
-- three probes that show why each extra premise is there.
--
-- Nothing here is postulated and nothing is left as a hole.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using (List; []; _∷_; _++_)
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
  (Flat; Flatn; flat; flat-closed; conv-flat)
open Flatn
open import strong.proof.Scoped using (Scoped; quote-wfᴿ)
open import strong.proof.Interior using (pop-base)
open import strong.proof.AddrWeaken using
  (Renamesᵇ; ren-wk; ren-stk; read-ren; conv-ren; conv-base; renᴿ-comm)
open Renamesᵇ
open import strong.proof.BuilderTyping using
  (BaseGrow; bg-here; ⊢-grow; revTy-typing; closeAt-single; notasgn-⤒;
   repFixed)
open import strong.proof.SubstAnnTyping using
  (NoFreeᵗ; nf-var; nf-ℕ; nf-𝔹; nf-⇒; nf-∀; Closedᵗ; closed-⇑;
   NotBnd; nb-lvl; nb-bse; NoBndᴿ; nbr-var; NoBndReps;
   SlotFree; sf-id; sf-cons; SlotFreeElt; sf-seal; sf-unseal; sf-hide;
   sf-show; sf-fun; sf-all;
   DropBindS; drop-here; drop-there; DropBind; drop-ctx; drop-unique;
   drop-uniqueS; slot-addrS;
   ∋a-drop; ∋r-drop; notasgn-drop; wf-drop; drop-pop; drop-push;
   closeAt-∀; closeAt-shift; closeEnv-≢; <-≢; <-irr; pred≤;
   nameSub-gt; nameSub-le; nameSub-suc)
open import strong.proof.CompositionTyping using (⨟-typing)
open import strong.proof.AllTyping using (⇑ᶜ; allView-typing)
open import strong.proof.SrcTyping using (srcᶜ-sound)
open import strong.proof.TypeWf using (typing-wf; ctxOk-[])

------------------------------------------------------------------------
-- §1  THE ADDRESS SIDE CONDITIONS ARE FREE — from TYPING alone
------------------------------------------------------------------------
-- `SlotFree X c` asks two things of every atomic element `κ Y α`:
-- (a) X < Y, and (b) `NotBnd α`.  (b) costs NOTHING: it is already a
-- consequence of the element being TYPED at all, with no appeal to
-- `Flat` or `Scoped`.
--
--   * `seal`/`unseal` scope their address with `∋r`, and `∋r` can never
--     reach a `bnd`: `r-skip-bind` is the only rule whose conclusion
--     names one, and it has no base case (`r-lvl` names a level,
--     `r-here`/`r-skip-addr`/`r-skip-nu` a base entry).
--   * `hide`/`show` scope their address with `∋a` AND declare it
--     unassigned.  Every `bnd` in scope is assigned a name — the
--     binder that binds it IS a name entry (`n-here-bind`) — so the
--     two premises together exclude a `bnd`.
--
-- This is stronger than the note in the task, which derived (b) from
-- `Flat` + `Scoped`: no context hypothesis is needed.

∋r-nobnd : ∀ {Sg Γ i R} → Sg ∣ Γ ∋r bnd i := R → ⊥
∋r-nobnd (r-skip-bind p) = ∋r-nobnd p
∋r-nobnd (r-skip-asgn p) = ∋r-nobnd p

∋r-notbnd : ∀ {Sg Γ α R} → Sg ∣ Γ ∋r α := R → NotBnd α
∋r-notbnd {α = lvl ℓ} p = nb-lvl
∋r-notbnd {α = bnd i} p = ⊥-elim (∋r-nobnd p)
∋r-notbnd {α = bse j} p = nb-bse

∋a-bnd-named : ∀ {Sg Ss Bs i} → Sg ∣ (Ss ∥ Bs) ∋a bnd i
  → Σ[ X ∈ ℕ ] ((Ss ∥ Bs) ∋n X := bnd i)
∋a-bnd-named a-here-bind = zero , n-here-bind
∋a-bnd-named (a-skip-bind p) with ∋a-bnd-named p
∋a-bnd-named (a-skip-bind p) | X , n = suc X , n-skip-bind-b n
∋a-bnd-named (a-skip-asgn p) with ∋a-bnd-named p
∋a-bnd-named (a-skip-asgn p) | X , n = suc X , n-skip-asgn n

∋a-notbnd : ∀ {Sg Ss Bs α} → Sg ∣ (Ss ∥ Bs) ∋a α
  → NotAssigned (Ss ∥ Bs) α → NotBnd α
∋a-notbnd {α = lvl ℓ} a na = nb-lvl
∋a-notbnd {α = bnd i} a na with ∋a-bnd-named a
∋a-notbnd {α = bnd i} a na | X , n = ⊥-elim (na n)
∋a-notbnd {α = bse j} a na = nb-bse

-- So the only content left in `SlotFree` is the NAME condition, which
-- is what `DeepNames` isolates.
mutual
  data DeepNamesElt (X : ℕ) : ConvElt → Set where
    dn-seal   : ∀ {Y α} → X < Y → DeepNamesElt X (seal Y α)
    dn-unseal : ∀ {Y α} → X < Y → DeepNamesElt X (unseal Y α)
    dn-hide   : ∀ {Y α} → X < Y → DeepNamesElt X (hide Y α)
    dn-show   : ∀ {Y α} → X < Y → DeepNamesElt X (show Y α)
    dn-fun    : ∀ {s t} → DeepNames X s → DeepNames X t
              → DeepNamesElt X (s ↦ t)
    dn-all    : ∀ {s} → DeepNames (suc X) s → DeepNamesElt X (all s)

  data DeepNames (X : ℕ) : Conv → Set where
    dn-id   : ∀ {A} → DeepNames X (id A)
    dn-cons : ∀ {ĉ c} → DeepNamesElt X ĉ → DeepNames X c
            → DeepNames X (ĉ ∷ᶜ c)

mutual
  slotFreeElt-of : ∀ {Sg Γᵢ Γₑ ĉ A B X} → Sg ∣ Γᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Γₑ
    → DeepNamesElt X ĉ → SlotFreeElt X ĉ
  slotFreeElt-of (conv-seal rep rd p) (dn-seal lt) =
    sf-seal lt (∋r-notbnd rep)
  slotFreeElt-of (conv-unseal rep rd p na) (dn-unseal lt) =
    sf-unseal lt (∋r-notbnd rep)
  slotFreeElt-of (conv-hide sc wf p na) (dn-hide lt) =
    sf-hide lt (∋a-notbnd sc na)
  slotFreeElt-of (conv-show sc wf p na) (dn-show lt) =
    sf-show lt (∋a-notbnd sc na)
  slotFreeElt-of (conv-fun ⊢s ⊢t) (dn-fun ds dt) =
    sf-fun (slotFree-of ⊢s ds) (slotFree-of ⊢t dt)
  slotFreeElt-of (conv-all ⊢s) (dn-all ds) = sf-all (slotFree-of ⊢s ds)

  slotFree-of : ∀ {Sg Γᵢ Γₑ c A B X} → Sg ∣ Γᵢ ⊢ c ∶ A ⇝ B ⊣ Γₑ
    → DeepNames X c → SlotFree X c
  slotFree-of (conv-id wf) dn-id = sf-id
  slotFree-of (conv-cons hd tl) (dn-cons dh dt) =
    sf-cons (slotFreeElt-of hd dh) (slotFree-of tl dt)

------------------------------------------------------------------------
-- §2  `NoBndReps` IS REFUTABLE — the repaired condition
------------------------------------------------------------------------
-- `proof.SubstAnnTyping`'s side condition (3) reads
--
--   NoBndReps Sg = ∀ {Γ α R} → NotBnd α → Sg ∣ Γ ∋r α := R → NoBndᴿ R
--
-- and it holds for NO store: the context Γ is universally quantified,
-- so a base entry `nuBind (`ᵃ bnd 0)` supplies a counterexample
-- (`r-here`, and `⇑ᴿᵉ` fixes `bnd`).  Even restricted to the contexts
-- this proof visits it would fail, because `NoBndᴿ` forbids a `bnd`
-- UNDER a `∀ᴿ` as well — and `⌊ ∀X.X ⌋ = `∀ᴿ (`ᵃ bnd 0)` is a
-- perfectly good stored representation.
--
-- The condition `read-drop` actually needs is LOCAL CLOSURE: every
-- `bnd` a representation mentions is bound by one of its own `∀ᴿ`s.
-- That is `LCᴿ` below, and it IS what `StoreOk` delivers.  §3 re-proves
-- the `substAnn` typing against it; the re-proof is a transcription of
-- `proof.SubstAnnTyping` §7/§9 with `NoBndᴿ` replaced by `LCᴿ` — every
-- other lemma is imported unchanged.

noBndReps-refuted : ∀ {Sg} → NoBndReps Sg → ⊥
noBndReps-refuted nbr with nbr {Γ = [] ∥ nuBind (`ᵃ bnd zero) ∷ []}
                                {α = bse zero} nb-bse r-here
noBndReps-refuted nbr | nbr-var ()

data OkAddr (X : ℕ) : Addr → Set where
  ok-lvl : ∀ {ℓ} → OkAddr X (lvl ℓ)
  ok-bse : ∀ {j} → OkAddr X (bse j)
  ok-bnd : ∀ {i} → i < X → OkAddr X (bnd i)

data LCᴿ : ℕ → RepTy → Set where
  lc-var : ∀ {n α} → OkAddr n α → LCᴿ n (`ᵃ α)
  lc-ℕ   : ∀ {n} → LCᴿ n `ℕᴿ
  lc-𝔹   : ∀ {n} → LCᴿ n `𝔹ᴿ
  lc-⇒   : ∀ {n R T} → LCᴿ n R → LCᴿ n T → LCᴿ n (R ⇒ᴿ T)
  lc-∀   : ∀ {n R} → LCᴿ (suc n) R → LCᴿ n (`∀ᴿ R)

ok-mono : ∀ {m n α} → m ≤ n → OkAddr m α → OkAddr n α
ok-mono le ok-lvl = ok-lvl
ok-mono le ok-bse = ok-bse
ok-mono le (ok-bnd lt) = ok-bnd (≤-trans lt le)

lc-mono : ∀ {m n R} → m ≤ n → LCᴿ m R → LCᴿ n R
lc-mono le (lc-var ok) = lc-var (ok-mono le ok)
lc-mono le lc-ℕ = lc-ℕ
lc-mono le lc-𝔹 = lc-𝔹
lc-mono le (lc-⇒ a b) = lc-⇒ (lc-mono le a) (lc-mono le b)
lc-mono le (lc-∀ a) = lc-∀ (lc-mono (s≤s le) a)

binds : ℕ → List StackEnt
binds zero = []
binds (suc n) = bind ∷ binds n

∋a-binds : ∀ {Sg n Bs i} → Sg ∣ (binds n ∥ Bs) ∋a bnd i → i < n
∋a-binds {n = zero} ()
∋a-binds {n = suc n} a-here-bind = s≤s z≤n
∋a-binds {n = suc n} (a-skip-bind p) = s≤s (∋a-binds p)

-- A representation well formed over a stack of `n` binders mentions no
-- `bnd` beyond those `n`.
wfᴿ-LC : ∀ {Sg n Bs R} → Sg ∣ (binds n ∥ Bs) ⊢ᴿ R → LCᴿ n R
wfᴿ-LC {R = `ᵃ lvl ℓ} (wfᴿ-var a) = lc-var ok-lvl
wfᴿ-LC {R = `ᵃ bnd i} (wfᴿ-var a) = lc-var (ok-bnd (∋a-binds a))
wfᴿ-LC {R = `ᵃ bse j} (wfᴿ-var a) = lc-var ok-bse
wfᴿ-LC wfᴿ-ℕ = lc-ℕ
wfᴿ-LC wfᴿ-𝔹 = lc-𝔹
wfᴿ-LC (wfᴿ-⇒ a b) = lc-⇒ (wfᴿ-LC a) (wfᴿ-LC b)
wfᴿ-LC {n = n} (wfᴿ-∀ a) = lc-∀ (wfᴿ-LC {n = suc n} a)

-- The repaired side condition, at a FIXED base — which is all the
-- theorem needs, since a typed conversion never changes the base.
LCReps : Store → List BaseEnt → Set
LCReps Sg Bs = ∀ {Ss α R} → NotBnd α → Sg ∣ (Ss ∥ Bs) ∋r α := R → LCᴿ zero R

∋r-lvl-inv : ∀ {Sg Γ ℓ R} → Sg ∣ Γ ∋r lvl ℓ := R → Sg ∋ˡ ℓ := R
∋r-lvl-inv (r-lvl l) = l

∋r-bse-[] : ∀ {Sg Ss j R} → Sg ∣ (Ss ∥ []) ∋r bse j := R → ⊥
∋r-bse-[] ()

∋a-bse-[] : ∀ {Sg Ss j} → Sg ∣ (Ss ∥ []) ∋a bse j → ⊥
∋a-bse-[] ()

-- Over an EMPTY base only the store is reachable, and a stored
-- representation is well formed over the empty stack.
storeOk-LCReps : ∀ {Sg} → StoreOk Sg → LCReps Sg []
storeOk-LCReps sok nb-lvl p = wfᴿ-LC {n = zero} (sok (∋r-lvl-inv p))
storeOk-LCReps sok nb-bse p = ⊥-elim (∋r-bse-[] p)

------------------------------------------------------------------------
-- §3  `substAnn` TYPING, AGAINST `LCᴿ`
------------------------------------------------------------------------

ok-≢ : ∀ {X Ss Ss′ Bs Z α} → DropBindS X Ss Ss′ → OkAddr X α
  → (Ss ∥ Bs) ∋n Z := α → ¬ (X ≡ Z)
ok-≢ d ok-lvl n refl with slot-addrS d n
ok-≢ d ok-lvl n refl | ()
ok-≢ d ok-bse n refl with slot-addrS d n
ok-≢ d ok-bse n refl | ()
ok-≢ d (ok-bnd lt) n refl with slot-addrS d n
ok-≢ d (ok-bnd lt) n refl | refl = <-irr lt

-- The slot's own address is `bnd X`; an address strictly above it is
-- `bnd i` with i < X, and dropping the slot leaves it alone.
∋n-dropOk : ∀ {X Ss Ss′ Bs Z α} → DropBindS X Ss Ss′ → OkAddr X α
  → (Ss ∥ Bs) ∋n Z := α → (Ss′ ∥ Bs) ∋n nameSub X Z := α
∋n-dropOk drop-here (ok-bnd ()) n
∋n-dropOk drop-here ok-lvl (n-skip-bind-l {X = Z} p)
  rewrite nameSub-gt zero (suc Z) (s≤s z≤n) = p
∋n-dropOk drop-here ok-bse (n-skip-bind-e {X = Z} p)
  rewrite nameSub-gt zero (suc Z) (s≤s z≤n) = p
∋n-dropOk (drop-there {X = X} d) (ok-bnd lt) n-here-bind
  rewrite nameSub-le (suc X) zero (λ ()) = n-here-bind
∋n-dropOk (drop-there {X = X} d) (ok-bnd lt) (n-skip-bind-b {X = Z} p)
  rewrite nameSub-suc X Z =
  n-skip-bind-b (∋n-dropOk d (ok-bnd (pred≤ lt)) p)
∋n-dropOk (drop-there {X = X} d) ok-lvl (n-skip-bind-l {X = Z} p)
  rewrite nameSub-suc X Z = n-skip-bind-l (∋n-dropOk d ok-lvl p)
∋n-dropOk (drop-there {X = X} d) ok-bse (n-skip-bind-e {X = Z} p)
  rewrite nameSub-suc X Z = n-skip-bind-e (∋n-dropOk d ok-bse p)

read-drop-lc : ∀ {Sg Ss Ss′ Bs X S R A} → DropBindS X Ss Ss′ → LCᴿ X R
  → Sg ∣ (Ss ∥ Bs) ⊢ R ⇓ A → Sg ∣ (Ss′ ∥ Bs) ⊢ R ⇓ closeAt X S A
read-drop-lc {X = X} {S = S} d (lc-var ok) (read-var {X = Z} n)
  rewrite closeEnv-≢ X S Z (ok-≢ d ok n) = read-var (∋n-dropOk d ok n)
read-drop-lc d lc-ℕ read-ℕ = read-ℕ
read-drop-lc d lc-𝔹 read-𝔹 = read-𝔹
read-drop-lc d (lc-⇒ nr nt) (read-⇒ r t) =
  read-⇒ (read-drop-lc d nr r) (read-drop-lc d nt t)
read-drop-lc {X = X} {S = S} d (lc-∀ nr) (read-∀ {A = A} r)
  rewrite closeAt-∀ X S A = read-∀ (read-drop-lc (drop-there d) nr r)

mutual
  substAnnElt-lc : ∀ {Sg X S ĉ A B Ssₑ Ss′ Bs Ssᵢ Bsᵢ}
    → LCReps Sg Bs → Closedᵗ S → SlotFreeElt X ĉ
    → DropBindS X Ssₑ Ss′
    → Sg ∣ (Ssᵢ ∥ Bsᵢ) ⊢̂ ĉ ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Γᵢ′ ∈ Ctxᵗ ]
        (DropBind X (Ssᵢ ∥ Bsᵢ) Γᵢ′
         × Sg ∣ Γᵢ′ ⊢̂ substAnnElt X S ĉ
             ∶ closeAt X S A ⇝ closeAt X S B ⊣ (Ss′ ∥ Bs))

  substAnnElt-lc {X = X} {S = S} lcr cl (sf-seal {Y = Y} lt nb) d
    (conv-seal rep rd p) with drop-pop d nb p
  substAnnElt-lc {X = X} {S = S} lcr cl (sf-seal {Y = Y} lt nb) d
    (conv-seal rep rd p) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeEnv-≢ X S Y (<-≢ lt) =
    Γᵢ′ , drop-ctx dᵢ
    , conv-seal (∋r-drop nb rep)
        (read-drop-lc dᵢ (lc-mono z≤n (lcr nb rep)) rd) p′

  substAnnElt-lc {X = X} {S = S} lcr cl (sf-unseal {Y = Y} lt nb) d
    (conv-unseal rep rd p na) with pop-base p
  substAnnElt-lc {X = X} {S = S} lcr cl (sf-unseal {Y = Y} lt nb) d
    (conv-unseal rep rd p na) | refl with drop-push d nb lt p
  substAnnElt-lc {X = X} {S = S} lcr cl (sf-unseal {Y = Y} lt nb) d
    (conv-unseal rep rd p na) | refl | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeEnv-≢ X S Y (<-≢ lt) =
    _ , drop-ctx dᵢ
    , conv-unseal (∋r-drop nb rep)
        (read-drop-lc d (lc-mono z≤n (lcr nb rep)) rd) p′
        (notasgn-drop d nb na)

  substAnnElt-lc {X = X} {S = S} lcr cl (sf-hide {Y = Y} lt nb) d
    (conv-hide {A = A} sc wf p na) with drop-pop d nb p
  substAnnElt-lc {X = X} {S = S} lcr cl (sf-hide {Y = Y} lt nb) d
    (conv-hide {A = A} sc wf p na) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeAt-shift X Y S A lt cl =
    _ , drop-ctx dᵢ
    , conv-hide (∋a-drop nb sc) (wf-drop dᵢ cl wf) p′
        (notasgn-drop dᵢ nb na)

  substAnnElt-lc {X = X} {S = S} lcr cl (sf-show {Y = Y} lt nb) d
    (conv-show {A = A} sc wf p na) with drop-push d nb lt p
  substAnnElt-lc {X = X} {S = S} lcr cl (sf-show {Y = Y} lt nb) d
    (conv-show {A = A} sc wf p na) | Γᵢ′ , drop-ctx dᵢ , p′
    rewrite closeAt-shift X Y S A lt cl =
    _ , drop-ctx dᵢ
    , conv-show (∋a-drop nb sc) (wf-drop d cl wf) p′
        (notasgn-drop d nb na)

  substAnnElt-lc lcr cl (sf-fun sfs sft) d (conv-fun ⊢s ⊢t)
    with conv-base ⊢t
  substAnnElt-lc lcr cl (sf-fun sfs sft) d (conv-fun ⊢s ⊢t) | refl
    with substAnn-lc lcr cl sft d ⊢t
  substAnnElt-lc lcr cl (sf-fun sfs sft) d (conv-fun ⊢s ⊢t) | refl
    | Γᵢ′ , drop-ctx dᵢ , ty-t with substAnn-lc lcr cl sfs dᵢ ⊢s
  substAnnElt-lc lcr cl (sf-fun sfs sft) d (conv-fun ⊢s ⊢t) | refl
    | Γᵢ′ , drop-ctx dᵢ , ty-t | Γₑ″ , drop-ctx dₑ″ , ty-s
    rewrite drop-uniqueS d dₑ″ =
    _ , drop-ctx dᵢ , conv-fun ty-s ty-t

  substAnnElt-lc {X = X} {S = S} lcr cl (sf-all sfs) d
    (conv-all {A = A} {B = B} ⊢s)
    with substAnn-lc lcr (closed-⇑ cl) sfs (drop-there d) ⊢s
  substAnnElt-lc {X = X} {S = S} lcr cl (sf-all sfs) d
    (conv-all {A = A} {B = B} ⊢s) | Γ″ , drop-ctx (drop-there dᵢ) , ty
    rewrite closeAt-∀ X S A | closeAt-∀ X S B =
    _ , drop-ctx dᵢ , conv-all ty

  substAnn-lc : ∀ {Sg X S c A B Ssₑ Ss′ Bs Γᵢ}
    → LCReps Sg Bs → Closedᵗ S → SlotFree X c
    → DropBindS X Ssₑ Ss′
    → Sg ∣ Γᵢ ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
    → Σ[ Γᵢ′ ∈ Ctxᵗ ]
        (DropBind X Γᵢ Γᵢ′
         × Sg ∣ Γᵢ′ ⊢ substAnn X S c ∶ closeAt X S A ⇝ closeAt X S B
             ⊣ (Ss′ ∥ Bs))

  substAnn-lc lcr cl sf-id d (conv-id wf) =
    _ , drop-ctx d , conv-id (wf-drop d cl wf)
  substAnn-lc lcr cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) with conv-base tl
  substAnn-lc lcr cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl
    with substAnn-lc lcr cl sfc d tl
  substAnn-lc lcr cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl | Γ₂′ , drop-ctx d₂ , ty-tl
    with substAnnElt-lc lcr cl sfĉ d₂ hd
  substAnn-lc lcr cl (sf-cons sfĉ sfc) d
    (conv-cons {Γ₂ = Ss₂ ∥ Bs₂} hd tl) | refl | Γ₂′ , drop-ctx d₂ , ty-tl
    | Γ₁′ , dr₁ , ty-hd = _ , dr₁ , conv-cons ty-hd ty-tl

substAnn-lc′ : ∀ {Sg X S c A B Δᵢ Δᵢ′ Ssₑ Ss′ Bs}
  → LCReps Sg Bs → Closedᵗ S → SlotFree X c
  → DropBind X Δᵢ Δᵢ′ → DropBindS X Ssₑ Ss′
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ (Ssₑ ∥ Bs)
  → Sg ∣ Δᵢ′ ⊢ substAnn X S c ∶ closeAt X S A ⇝ closeAt X S B ⊣ (Ss′ ∥ Bs)
substAnn-lc′ lcr cl sf drᵢ d ⊢c with substAnn-lc lcr cl sf d ⊢c
substAnn-lc′ lcr cl sf drᵢ d ⊢c | Δᵢ″ , drᵢ″ , ty
  rewrite drop-unique drᵢ drᵢ″ = ty

------------------------------------------------------------------------
-- §4  A CONVERSION OVER AN EMPTY BASE IS FIXED BY A BASE RENAMING
------------------------------------------------------------------------
-- The reduction rule writes `d` itself into the `ν`'s body, and the
-- `ν` pushes a base entry — so the base weakening must leave `d`
-- alone.  It does: over an empty base no `bse` address is in scope, and
-- `renᵃᵉ` moves nothing else.  (This is the second half of the task's
-- observation (b).)

addr-fix : ∀ {Sg Ss α} → Sg ∣ (Ss ∥ []) ∋a α → ∀ ρ → renᵃᵉ ρ α ≡ α
addr-fix {α = lvl ℓ} a ρ = refl
addr-fix {α = bnd i} a ρ = refl
addr-fix {α = bse j} a ρ = ⊥-elim (∋a-bse-[] a)

rep-addr-fix : ∀ {Sg Ss α R} → Sg ∣ (Ss ∥ []) ∋r α := R
  → ∀ ρ → renᵃᵉ ρ α ≡ α
rep-addr-fix {α = lvl ℓ} p ρ = refl
rep-addr-fix {α = bnd i} p ρ = refl
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
-- §5  A BASE RENAMING CARRIES `NameFn`
------------------------------------------------------------------------

namefn-ren : ∀ {Sg ρ Γ Γ′} → Renamesᵇ Sg ρ Γ Γ′ → NameFn Γ → NameFn Γ′
namefn-ren r nf p q with ren-n⁻ r p | ren-n⁻ r q
namefn-ren r nf p q | β , p′ , e₁ | γ , q′ , e₂
  with ren-inj r (trans (sym e₁) e₂)
namefn-ren r nf p q | β , p′ , e₁ | γ , q′ , e₂ | refl = nf p′ q′

------------------------------------------------------------------------
-- §6  A CLOSED TYPE'S REPRESENTATION READS BACK ANYWHERE
------------------------------------------------------------------------
-- `TyBeta` quotes and reads back in the SAME context.  `TyWrap` does
-- not: `A` is well formed at the redex's Δ, while the builder's
-- read-back is demanded at the conversion's INTERIOR Δᵢ, whose name
-- assignments are different ones.  With `A` closed the two agree — the
-- only names the reading mentions are the `∀`-binders inside `A`
-- itself.  This is the FIRST place `Closedᵗ A` is spent.

-- a name below the binder prefix is the prefix's own `bnd`
binds-here : ∀ {n Ss Bs Z} → Z < n → (binds n ++ Ss ∥ Bs) ∋n Z := bnd Z
binds-here {n = suc n} {Z = zero} lt = n-here-bind
binds-here {n = suc n} {Z = suc Z} (s≤s lt) = n-skip-bind-b (binds-here lt)

binds-addr : ∀ {n Ss Bs Z α} → Z < n
  → (binds n ++ Ss ∥ Bs) ∋n Z := α → α ≡ bnd Z
binds-addr {n = zero} () n
binds-addr {n = suc n} lt n-here-bind = refl
binds-addr {n = suc n} (s≤s lt) (n-skip-bind-b p) =
  cong ⇑ᵃ (binds-addr lt p)
binds-addr {n = suc n} (s≤s lt) (n-skip-bind-l p) with binds-addr lt p
binds-addr {n = suc n} (s≤s lt) (n-skip-bind-l p) | ()
binds-addr {n = suc n} (s≤s lt) (n-skip-bind-e p) with binds-addr lt p
binds-addr {n = suc n} (s≤s lt) (n-skip-bind-e p) | ()

quote-read-closed : ∀ {Sg n Ss Ss′ Bs Bs′ A R}
  → NoFreeᵗ n A
  → Sg ∣ (binds n ++ Ss ∥ Bs) ⊢⌊ A ⌋ R
  → Sg ∣ (binds n ++ Ss′ ∥ Bs′) ⊢ R ⇓ A
quote-read-closed (nf-var lt) (quote-var n)
  rewrite binds-addr lt n = read-var (binds-here lt)
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
-- §7  PRESERVATION FOR `TyWrap`
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
--   * `Closedᵗ A`  — the KNOWN GAP, spent TWICE (§6 and §3); see §9.1.
--   * `DeepNames zero d` — the NAME half of `SlotFree zero d`; the
--     ADDRESS half is free (§1) but this half is not, see §9.2.
--   * `srcᶜ d ≢ nothing` — `instReveal`'s OTHER branch, `show X α ∷ᶜ d`,
--     is ill-typed at a `TyWrap` redex; see §9.3.
--
-- and `LCReps Sg []`, which §2 derives from `StoreOk Sg` outright.

tyWrapOk′ : ∀ {Sg Δ V c d A B R C}
  → StoreOk Sg → Flat Δ → NameFn Δ → Scoped Sg Δ
  → Closedᵗ A
  → DeepNames zero d
  → ¬ (srcᶜ d ≡ nothing)
  → allView c ≡ just d
  → Sg ∣ Δ ⊢⌊ A ⌋ R
  → Sg ∣ Δ ∣ [] ⊢ ((Λ V) ⟨ c ⟩) • B [ A ] ⦂ C
  → Sg ∣ Δ ∣ [] ⊢ ν R ∙ (V ⟨ instReveal zero (bse zero) A d ⟩) ⦂ C
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA dn
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  with flat-bas fl | flat-bas (conv-flat ⊢c fl)
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA dn
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl with allView-typing nfΔ ⊢c eq
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA dn
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd with srcᶜ d | srcᶜ-sound ⊢d | srcOk

tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA dn
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | just A₁ | inj₂ () | _
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA dn
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | nothing | inj₁ () | _
tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA dn
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | nothing | inj₂ refl | nj = ⊥-elim (nj refl)

tyWrapOk′ {Sg} {Ssₑ ∥ Bsₑ} {V} {c} {d} {A} {B} {R} sok fl nfΔ scp clA dn
  srcOk eq q (⊢•[] (⊢⟨⟩ nfc (⊢Λ {Ss = Ssᵢ} {Bs = Bsᵢ} val ⊢V) ⊢c) wfA)
  | refl | refl | ⊢d , nfd | just A₁ | inj₁ refl | _ =
  ⊢ν wfR
    (⊢⟨⟩ (⨟-NF (revTy zero (bse zero) A A₁) (substAnn zero A d))
         (⊢-grow bg-here ⊢V) ⊢conv)
  where
  Sh : Renamesᵇ Sg suc ([] ∥ []) ([] ∥ nuBind R ∷ [])
  Sh = ren-wk {e = nuBind R} sok

  wfR : Sg ∣ (Ssₑ ∥ []) ⊢ᴿ R
  wfR = quote-wfᴿ scp q

  -- the builder's read-back, demanded at the CONVERSION's interior
  rdA : Sg ∣ (⤒ Ssᵢ ∥ nuBind R ∷ []) ⊢ ⇑ᴿᵉ R ⇓ A
  rdA = read-ren (ren-stk Sh) (quote-read-anywhere clA q)

  fixR : ∀ η → renameᴿ η (⇑ᴿᵉ R) ≡ ⇑ᴿᵉ R
  fixR η = trans (sym (renᴿ-comm suc η R))
                 (cong (renameᴿᵉ suc) (repFixed (flat-closed fl wfR) η))

  wfA₀ : (asgn (bse zero) ∷ ⤒ Ssᵢ ∥ nuBind R ∷ []) ⊢ᵗ A₁
  wfA₀ = wf-rebase (typing-wf ctxOk-[] ⊢V)

  ⊢rev : Sg ∣ (asgn (bse zero) ∷ ⤒ Ssᵢ ∥ nuBind R ∷ [])
           ⊢ revTy zero (bse zero) A A₁ ∶ A₁ ⇝ closeAt zero A A₁
           ⊣ (⤒ Ssᵢ ∥ nuBind R ∷ [])
  ⊢rev = revTy-typing zero (bse zero) A A₁ pop-here (notasgn-⤒ Ssᵢ)
           r-here rdA fixR wfA₀

  ⊢sub₀ : Sg ∣ (Ssᵢ ∥ []) ⊢ substAnn zero A d
            ∶ closeAt zero A A₁ ⇝ closeAt zero A B ⊣ (Ssₑ ∥ [])
  ⊢sub₀ = substAnn-lc′ (storeOk-LCReps sok) clA (slotFree-of ⊢d dn)
            (drop-ctx drop-here) drop-here ⊢d

  -- the `ν` pushes a base entry; §4 says it leaves the conversion alone
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
-- §8  WHAT IS NOT CLOSED: `TyWrapOk` ITSELF
------------------------------------------------------------------------
-- `proof.PreserveTyDef.TyWrapOk` is `tyWrapOk′` MINUS the three extra
-- premises, so the wrapper
--
--   tyWrapOk : TyWrapOk
--   tyWrapOk sok fl nf scp eq q ⊢M =
--     tyWrapOk′ sok fl nf scp {- Closedᵗ A -} {- DeepNames zero d -}
--                             {- srcᶜ d ≢ nothing -} eq q ⊢M
--
-- cannot be written: none of the three is derivable from the redex.
-- §9 gives a probe for each.  The repairs they call for all live in
-- files this module may not touch:
--
--   (1) `substAnn` should SHIFT `S` at every crossing, exactly as its
--       own `all` equation already does
--       (`substAnnElt X S (all s) = all (substAnn (suc X) (⇑ᵗ S) s)`);
--       then `closeEnv-shift`'s slot branch would not need
--       `renameᵗ (shiftAtᵗ W) S ≡ S`, and `Closedᵗ S` would go.
--       Equally, `revTy`'s read-back premise would then be stated at
--       the interior's own coordinates.  (strong/Conversion.agda)
--
--   (2) `allView`'s `all⁺` must not let a NESTED `all s` contribute
--       `elts s` unshifted: those elements keep their own names, and
--       a name 0 among them sits AT the slot `substAnn` is removing.
--       (strong/Conversion.agda, `all⁺ (all s) = just (elts s)`)
--
--   (3) `instReveal`'s `nothing` branch, `show X α ∷ᶜ c`, crosses ONE
--       assignment where the redex needs the `∀`'s binder slot to
--       DISAPPEAR.  (strong/ConversionReduction.agda)
--
-- Independently, `proof.SubstAnnTyping`'s side condition (3) is
-- refuted outright by §2's `noBndReps-refuted`; the `LCᴿ` version
-- proved in §2/§3 is the repair, and it is what `tyWrapOk′` uses.

------------------------------------------------------------------------
-- §9  THE PROBES
------------------------------------------------------------------------

-- 9.1  `Closedᵗ A` — `substAnn` carries S past a crossing UNSHIFTED.
--
-- Take the §14-shaped word `d = show 1 (lvl 0) ∷ᶜ id (` 0)` under the
-- slot X = 0, and instantiate at the type argument `S = ` 0` — a
-- variable that IS in scope at the redex (a sealed name), so a
-- perfectly legal `•B[A]`, but not closed.  Then
--
--   substAnn 0 (` 0) d  =  show 0 (lvl 0) ∷ᶜ id (` 0)
--
-- and `conv-show` states its source as `renameᵗ (shiftAtᵗ 0)` of its
-- target.  The equation `substAnn-typing` must discharge there is
-- `closeAt-shift 0 1 S A`, whose two sides are:
--
--   closeAt 0 (` 0) (renameᵗ (shiftAtᵗ 1) (` 0))            =  ` 0
--   renameᵗ (shiftAtᵗ (nameSub 0 1)) (closeAt 0 (` 0) (` 0))  =  ` 1
--
-- The interior demands `` ` 0 `` (the slot's own variable, read under
-- the crossing) and the substituted annotation supplies `` ` 1 ``: the
-- crossing inserted a name entry that `S` was never shifted past.
closed-needed :
  ¬ (closeAt zero (` zero) (renameᵗ (shiftAtᵗ 1) (` zero))
      ≡ renameᵗ (shiftAtᵗ (nameSub zero 1)) (closeAt zero (` zero) (` zero)))
closed-needed ()

-- 9.2  `DeepNames zero d` — a REDEX whose `d` has a crossing at name 0.
--
-- `all⁺` does shift the name of every `hide`/`show` it lifts, so those
-- land at `suc X > 0`.  But `all⁺ (all s) = just (elts s)` passes a
-- nested conversion's elements through UNSHIFTED, and those keep their
-- own names — `conv-all` only insists that s's two contexts both begin
-- with a `bind`, not that s's crossings stay below it.  Here is a
-- well-typed, normal, INERT value at a flat scoped context whose
-- `allView` has crossings at name 0 in both directions.

private
  Sgₚ : Store
  Sgₚ = `ℕᴿ ∷ []

  sokₚ : StoreOk Sgₚ
  sokₚ l-here = wfᴿ-ℕ

  -- `lvl 0` carries no name in `bind ∷ [] ∥ []`
  naₚ : NotAssigned (bind ∷ [] ∥ []) (lvl zero)
  naₚ (n-skip-bind-l ())

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

  -- yet the name condition fails on the very first element
  deep-refutedₚ : ¬ (DeepNames zero sₚ)
  deep-refutedₚ (dn-cons (dn-hide ()) _)

  slotfree-refutedₚ : ¬ (SlotFree zero sₚ)
  slotfree-refutedₚ (sf-cons (sf-hide () nb) _)

-- 9.3  `srcᶜ d ≢ nothing` — `instReveal`'s other branch is ill-typed.
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
