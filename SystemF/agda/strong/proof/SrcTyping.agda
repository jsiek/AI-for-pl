module strong.proof.SrcTyping where

-- Strong System F v8 — `srcᶜ` reads a conversion's SOURCE type, and
-- this module says it reads it correctly — EVERYWHERE.
--
-- `instReveal` needs it: it is specified as
--
--     +X(c) ≡ +X(src c) ⨟ c[X:=S]
--
-- so the builder is applied to the source type that `srcᶜ` computed,
-- and the composition only typechecks if that really is the source.
--
-- `srcᶜ` used to be PARTIAL, undefined on a seal-headed conversion
-- "because its source is a read-back the syntax does not carry".  The
-- read-back is carried by the CONTEXT: `conv-seal` reads α's
-- representation back at the element's own interior, and `repOf` and
-- `readOf` (strong.Ctx) are the functional forms of the `∋r` and `⇓`
-- that rule uses.  §2 proves them adequate in both directions; §3 then
-- says `srcᶜ` is TOTAL on typed conversions — it is the source, not
-- merely the source-where-defined — which is what deletes
-- `instReveal`'s second branch.
--
-- The two crossing cases are still where the work is: a `hide` states
-- its types as a `shiftAtᵗ` rename, so reading back through it needs
-- `closeAt-shiftAt`, that closing over a slot undoes shifting past it.

open import Data.Nat using
  (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s; _<?_; _≤?_; _≟_; _∸_)
open import Data.Nat.Properties using (n≮n; ≤-refl; ≰⇒>; <⇒≤)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.proof.Canonical using (conv-target)
open import strong.proof.Interior using (pop-base; pop-sound; push-sound)
open import strong.proof.CompositionTyping using
  (namefn-bind; namefn-push; namefn-pop)

------------------------------------------------------------------------
-- Closing a slot undoes shifting past it
------------------------------------------------------------------------

substᵗ-renameᵗ : ∀ σ ρ A
  → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
substᵗ-renameᵗ σ ρ (` X) = refl
substᵗ-renameᵗ σ ρ `ℕ = refl
substᵗ-renameᵗ σ ρ `𝔹 = refl
substᵗ-renameᵗ σ ρ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-renameᵗ σ ρ A) (substᵗ-renameᵗ σ ρ B)
substᵗ-renameᵗ σ ρ (`∀ A) =
  cong `∀ (trans (substᵗ-renameᵗ (extsᵗ σ) (extᵗ ρ) A)
                 (substᵗ-cong h A))
  where
  h : ∀ X → extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
  h zero = refl
  h (suc X) = refl

substᵗ-id : ∀ A → substᵗ `_ A ≡ A
substᵗ-id (` X) = refl
substᵗ-id `ℕ = refl
substᵗ-id `𝔹 = refl
substᵗ-id (A ⇒ B) = cong₂ _⇒_ (substᵗ-id A) (substᵗ-id B)
substᵗ-id (`∀ A) = cong `∀ (trans (substᵗ-cong h A) (substᵗ-id A))
  where
  h : ∀ X → extsᵗ `_ X ≡ ` X
  h zero = refl
  h (suc X) = refl

-- `shiftAtᵗ X` is the identity below the slot and `suc` at or above it
shiftAt-below : ∀ X Y → Y < X → shiftAtᵗ X Y ≡ Y
shiftAt-below (suc X) zero lt = refl
shiftAt-below (suc X) (suc Y) (s≤s lt) = cong suc (shiftAt-below X Y lt)

shiftAt-above : ∀ X Y → X ≤ Y → shiftAtᵗ X Y ≡ suc Y
shiftAt-above zero Y le = refl
shiftAt-above (suc X) (suc Y) (s≤s le) = cong suc (shiftAt-above X Y le)

closeEnv-shiftAt : ∀ X S Y → closeEnv X S (shiftAtᵗ X Y) ≡ ` Y
closeEnv-shiftAt X S Y with X ≤? Y
closeEnv-shiftAt X S Y | yes le
  rewrite shiftAt-above X Y le = above
  where
  above : closeEnv X S (suc Y) ≡ ` Y
  above with X ≟ suc Y
  above | yes refl = ⊥-elim (n≮n Y le)
  above | no _ with X <? suc Y
  above | no _ | yes _ = refl
  above | no _ | no ¬lt = ⊥-elim (¬lt (s≤s le))
closeEnv-shiftAt X S Y | no ¬le
  rewrite shiftAt-below X Y (≰⇒> ¬le) = below
  where
  below : closeEnv X S Y ≡ ` Y
  below with X ≟ Y
  below | yes refl = ⊥-elim (¬le ≤-refl)
  below | no _ with X <? Y
  below | no _ | yes lt = ⊥-elim (¬le (<⇒≤ lt))
  below | no _ | no _ = refl

closeAt-shiftAt : ∀ X S A → closeAt X S (renameᵗ (shiftAtᵗ X) A) ≡ A
closeAt-shiftAt X S A =
  trans (substᵗ-renameᵗ (closeEnv X S) (shiftAtᵗ X) A)
        (trans (substᵗ-cong (closeEnv-shiftAt X S) A) (substᵗ-id A))

------------------------------------------------------------------------
-- §2  THE LOOKUPS ARE ADEQUATE
------------------------------------------------------------------------
-- `repOf`, `nameOf`/`bindOf` and `readOf` compute what `∋r`, `∋n`/`∋b`
-- and `⇓` relate, in BOTH directions.  Only the two NAME lookups need
-- anything of the context, and it is what `read-unique` needs too: with
-- two names for one address a read-back is not single-valued, so
-- `NameFn` is what makes `readOf` agree with the derivation one HAS
-- rather than with some other derivation of the same representation.

-- the `Maybe` plumbing, inverted
sucᴹ-inv : ∀ {m X} → sucᴹ m ≡ just X
  → Σ[ Y ∈ ℕ ] ((m ≡ just Y) × (X ≡ suc Y))
sucᴹ-inv {m = just Y} refl = Y , refl , refl
sucᴹ-inv {m = nothing} ()

⇑ᴹ-inv : ∀ {m R} → ⇑ᴹ m ≡ just R
  → Σ[ T ∈ RepTy ] ((m ≡ just T) × (R ≡ ⇑ᴿᵉ T))
⇑ᴹ-inv {m = just T} refl = T , refl , refl
⇑ᴹ-inv {m = nothing} ()

readVar-inv : ∀ {m A} → readVar m ≡ just A
  → Σ[ X ∈ ℕ ] ((m ≡ just X) × (A ≡ ` X))
readVar-inv {m = just X} refl = X , refl , refl
readVar-inv {m = nothing} ()

readFun-inv : ∀ {m n A} → readFun m n ≡ just A
  → Σ[ B ∈ Ty ] Σ[ C ∈ Ty ]
      ((m ≡ just B) × (n ≡ just C) × (A ≡ B ⇒ C))
readFun-inv {m = just B} {n = just C} refl = B , C , refl , refl , refl
readFun-inv {m = just B} {n = nothing} ()
readFun-inv {m = nothing} {n = n} ()

readAll-inv : ∀ {m A} → readAll m ≡ just A
  → Σ[ B ∈ Ty ] ((m ≡ just B) × (A ≡ `∀ B))
readAll-inv {m = just B} refl = B , refl , refl
readAll-inv {m = nothing} ()

-- the store
lvlOf-sound : ∀ {Sg ℓ R} → lvlOf Sg ℓ ≡ just R → Sg ∋ˡ ℓ := R
lvlOf-sound {Sg = []} {ℓ = zero} ()
lvlOf-sound {Sg = []} {ℓ = suc ℓ} ()
lvlOf-sound {Sg = S ∷ Sg} {ℓ = zero} refl = l-here
lvlOf-sound {Sg = S ∷ Sg} {ℓ = suc ℓ} eq = l-there (lvlOf-sound eq)

lvlOf-complete : ∀ {Sg ℓ R} → Sg ∋ˡ ℓ := R → lvlOf Sg ℓ ≡ just R
lvlOf-complete l-here = refl
lvlOf-complete (l-there p) = lvlOf-complete p

-- α's representation: the base's `nuBind`s, shifted at each entry
bseOf-sound : ∀ {Sg Ss Bs j R} → bseOf Bs j ≡ just R
  → Sg ∣ (Ss ∥ Bs) ∋r bse j := R
bseOf-sound {Bs = []} {j = zero} ()
bseOf-sound {Bs = []} {j = suc j} ()
bseOf-sound {Bs = addr ∷ Bs} {j = zero} ()
bseOf-sound {Bs = nuBind T ∷ Bs} {j = zero} refl = r-here
bseOf-sound {Bs = addr ∷ Bs} {j = suc j} eq with ⇑ᴹ-inv eq
bseOf-sound {Bs = addr ∷ Bs} {j = suc j} eq | T , e , refl =
  r-skip-addr (bseOf-sound e)
bseOf-sound {Bs = nuBind T ∷ Bs} {j = suc j} eq with ⇑ᴹ-inv eq
bseOf-sound {Bs = nuBind T ∷ Bs} {j = suc j} eq | S , e , refl =
  r-skip-nu (bseOf-sound e)

repOf-sound : ∀ {Sg Γ α R} → repOf Sg Γ α ≡ just R → Sg ∣ Γ ∋r α := R
repOf-sound {Γ = Ss ∥ Bs} {α = lvl ℓ} eq = r-lvl (lvlOf-sound eq)
repOf-sound {Γ = Ss ∥ Bs} {α = bse j} eq = bseOf-sound eq

repOf-complete : ∀ {Sg Γ α R} → Sg ∣ Γ ∋r α := R → repOf Sg Γ α ≡ just R
repOf-complete (r-lvl l) = lvlOf-complete l
repOf-complete r-here = refl
repOf-complete (r-skip-addr p) rewrite repOf-complete p = refl
repOf-complete (r-skip-nu p) rewrite repOf-complete p = refl

-- the name assigned to an address
nameOf-sound : ∀ {Ss Bs α X} → nameOf Ss α ≡ just X → (Ss ∥ Bs) ∋n X := α
nameOf-sound {Ss = []} ()
nameOf-sound {Ss = bind ∷ Ss} eq with sucᴹ-inv eq
nameOf-sound {Ss = bind ∷ Ss} eq | Y , e , refl =
  n-skip-bind (nameOf-sound e)
nameOf-sound {Ss = asgn β ∷ Ss} {α = α} eq with α ≟ᵃ β | eq
nameOf-sound {Ss = asgn β ∷ Ss} {α = α} eq | yes refl | refl = n-here-asgn
nameOf-sound {Ss = asgn β ∷ Ss} {α = α} eq | no ne | eq′ with sucᴹ-inv eq′
nameOf-sound {Ss = asgn β ∷ Ss} {α = α} eq | no ne | eq′ | Y , e , refl =
  n-skip-asgn (nameOf-sound e)

-- an assigned address HAS a name, whichever one the walk finds first
nameOf-total : ∀ {Ss Bs α X} → (Ss ∥ Bs) ∋n X := α
  → Σ[ Y ∈ ℕ ] (nameOf Ss α ≡ just Y)
nameOf-total {α = α} n-here-asgn with α ≟ᵃ α
nameOf-total {α = α} n-here-asgn | yes _ = zero , refl
nameOf-total {α = α} n-here-asgn | no ne = ⊥-elim (ne refl)
nameOf-total {Ss = asgn β ∷ Ss} {α = α} (n-skip-asgn p) with α ≟ᵃ β
nameOf-total {Ss = asgn β ∷ Ss} {α = α} (n-skip-asgn p) | yes _ =
  zero , refl
nameOf-total {Ss = asgn β ∷ Ss} {α = α} (n-skip-asgn p) | no ne
  with nameOf-total p
nameOf-total {Ss = asgn β ∷ Ss} {α = α} (n-skip-asgn p) | no ne | Y , e
  rewrite e = suc Y , refl
nameOf-total {Ss = bind ∷ Ss} (n-skip-bind p) with nameOf-total p
nameOf-total {Ss = bind ∷ Ss} (n-skip-bind p) | Y , e rewrite e =
  suc Y , refl

-- ... and with names unique, the one it finds is the one asked for
nameOf-complete : ∀ {Γ α X} → NameFn Γ → Γ ∋n X := α
  → nameOf (stk Γ) α ≡ just X
nameOf-complete {Γ = Ss ∥ Bs} nf p with nameOf-total p
nameOf-complete {Γ = Ss ∥ Bs} nf p | Y , e
  rewrite nf p (nameOf-sound {Bs = Bs} e) = e

-- the name of the i-th `bind`: a function outright
bindOf-sound : ∀ {Ss i X} → bindOf Ss i ≡ just X → Ss ∋b X at i
bindOf-sound {Ss = []} ()
bindOf-sound {Ss = asgn β ∷ Ss} eq with sucᴹ-inv eq
bindOf-sound {Ss = asgn β ∷ Ss} eq | Y , e , refl =
  b-asgn (bindOf-sound e)
bindOf-sound {Ss = bind ∷ Ss} {i = zero} refl = b-here
bindOf-sound {Ss = bind ∷ Ss} {i = suc i} eq with sucᴹ-inv eq
bindOf-sound {Ss = bind ∷ Ss} {i = suc i} eq | Y , e , refl =
  b-bind (bindOf-sound e)

bindOf-complete : ∀ {Ss i X} → Ss ∋b X at i → bindOf Ss i ≡ just X
bindOf-complete b-here = refl
bindOf-complete (b-asgn p) rewrite bindOf-complete p = refl
bindOf-complete (b-bind p) rewrite bindOf-complete p = refl

-- the read-back
readOf-sound : ∀ {Sg Γ R A} → readOf Γ R ≡ just A → Sg ∣ Γ ⊢ R ⇓ A
readOf-sound {Γ = Ss ∥ Bs} {R = `ᵃ α} eq with readVar-inv eq
readOf-sound {Γ = Ss ∥ Bs} {R = `ᵃ α} eq | X , e , refl =
  read-var (nameOf-sound e)
readOf-sound {Γ = Ss ∥ Bs} {R = `ᵛ i} eq with readVar-inv eq
readOf-sound {Γ = Ss ∥ Bs} {R = `ᵛ i} eq | X , e , refl =
  read-bv (bindOf-sound e)
readOf-sound {Γ = Ss ∥ Bs} {R = `ℕᴿ} refl = read-ℕ
readOf-sound {Γ = Ss ∥ Bs} {R = `𝔹ᴿ} refl = read-𝔹
readOf-sound {Γ = Ss ∥ Bs} {R = R ⇒ᴿ T} eq with readFun-inv eq
readOf-sound {Γ = Ss ∥ Bs} {R = R ⇒ᴿ T} eq | B , C , e₁ , e₂ , refl =
  read-⇒ (readOf-sound e₁) (readOf-sound e₂)
readOf-sound {Γ = Ss ∥ Bs} {R = `∀ᴿ R} eq with readAll-inv eq
readOf-sound {Γ = Ss ∥ Bs} {R = `∀ᴿ R} eq | B , e , refl =
  read-∀ (readOf-sound e)

readOf-complete : ∀ {Sg Γ R A} → NameFn Γ → Sg ∣ Γ ⊢ R ⇓ A
  → readOf Γ R ≡ just A
readOf-complete nf (read-var n) rewrite nameOf-complete nf n = refl
readOf-complete nf (read-bv b) rewrite bindOf-complete b = refl
readOf-complete nf read-ℕ = refl
readOf-complete nf read-𝔹 = refl
readOf-complete nf (read-⇒ p q)
  rewrite readOf-complete nf p | readOf-complete nf q = refl
readOf-complete nf (read-∀ p)
  rewrite readOf-complete (namefn-bind nf) p = refl

------------------------------------------------------------------------
-- §3  `srcᶜ` IS TOTAL, AND IT IS THE SOURCE
------------------------------------------------------------------------
-- The recursion follows the syntax, not the derivation's spine: a
-- crossing reads its tail's source and undoes its own reindexing, a `↦`
-- or `all` reads the source out of a COMPONENT — and a SEAL reads it
-- out of the CONTEXT.  Each recursive call is given the context the
-- typing rule gives that subterm: `pushAsgn` for a `hide`'s tail,
-- `popAsgn` for a `show`'s, one more `bind` for an `all`'s component.
-- `pop-sound`/`push-sound` say those computed moves are the ones the
-- pop judgment made, which is what rules out every `nothing`.

-- `∋r` reads the BASE only, and a pop leaves the base alone
∋r-pop : ∀ {Sg Γ Γ′ X α R} → Γ ▷ X := α ⇒ Γ′ → Sg ∣ Γ ∋r α := R
  → Sg ∣ Γ′ ∋r α := R
∋r-pop {Γ = Ss ∥ Bs} {Γ′ = Ss′ ∥ Bs′} p q with pop-base p
∋r-pop {Γ = Ss ∥ Bs} {Γ′ = Ss′ ∥ Bs′} p q | refl = ∋r-restk q

srcᶜ-sound : ∀ {Sg Δᵢ Δ c A B} → NameFn Δᵢ
  → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δ → srcᶜ Sg Δᵢ c ≡ A
srcᶜ-sound nf (conv-id wf) = refl

-- the case that used to be `nothing`: the seal's `∋r` lives one
-- crossing out, and `∋r-pop` brings it back to the element's interior,
-- where `readOf` performs the very read-back `conv-seal` demands
srcᶜ-sound nf (conv-cons (conv-seal rep rd p) tl)
  rewrite repOf-complete (∋r-pop p rep) | readOf-complete nf rd = refl

-- an unseal's source IS its name
srcᶜ-sound nf (conv-cons (conv-unseal rep rd p na) tl) = refl

-- a `hide` shifts its target, so reading back closes over the slot
srcᶜ-sound nf (conv-cons (conv-hide {A = A} {X = X} sc wf p na) tl)
  rewrite push-sound p | srcᶜ-sound (namefn-push nf na p) tl =
  closeAt-shiftAt X `ℕ A

-- a `show` shifts its source, which is exactly what `srcᶜ` re-applies
srcᶜ-sound nf (conv-cons (conv-show sc wf p na) tl)
  rewrite pop-sound p | srcᶜ-sound (namefn-pop p nf) tl = refl

-- a `↦` reads the covariant component's source; the contravariant
-- one's TARGET is the domain, which `conv-target` supplies
srcᶜ-sound nf (conv-cons (conv-fun ⊢s ⊢t) tl)
  rewrite conv-target ⊢s | srcᶜ-sound nf ⊢t = refl

-- an `all` reads its component's source under the binder
srcᶜ-sound nf (conv-cons (conv-all ⊢s) tl)
  rewrite srcᶜ-sound (namefn-bind nf) ⊢s = refl
