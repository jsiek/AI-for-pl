module strong.proof.InertRenaming where

-- Strong System F v8 — INERTNESS and VALUEHOOD survive a base renaming.
--
-- A base renaming `renConvᵉ ρ` touches nothing but the `bse` component
-- of the addresses carried by the four atomic elements: it leaves every
-- NAME alone, leaves every `Ty` alone (`renConvᵉ ρ (id A) = id A`), and
-- passes through `all` UNEXTENDED, because an `all` binds a STACK
-- address.  So everything the views `arr` and `allView` decide by
-- looking at a type — the target's shape, the terminators they attach —
-- is literally unchanged, and everything they decide by looking at the
-- element shapes commutes with the renaming.  That gives
--
--   inert-renᵉ : Inert c → Inert (renConvᵉ ρ c)
--
-- with NO side condition: `Inert` asks only that a view SUCCEED, and
-- success is a matter of shape.
--
-- `Value` is different.  A value's conversion must also be a NORMAL
-- FORM, and normality is a DISEQUALITY of addresses — `fuse` cancels
-- `hide X α` against `show X β` exactly when α ≡ β.  A renaming that
-- identifies two addresses therefore creates a redex where there was
-- none, and valuehood genuinely fails; `value-renᵉ-not-unconditional`
-- below exhibits the counterexample.  So `value-renᵉ` carries the
-- injectivity hypothesis `Injᵉ ρ`, which every call site has (the base
-- binders are crossed by `suc` and `extᵇ`).

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_; suc-injective)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion
open import strong.ConversionReduction
open import strong.Terms
open import strong.TermSubst

------------------------------------------------------------------------
-- A base renaming leaves the annotations alone
------------------------------------------------------------------------

target-renᵉ : ∀ ρ c → target (renConvᵉ ρ c) ≡ target c
target-renᵉ ρ (id A)    = refl
target-renᵉ ρ (ĉ ∷ᶜ c) = target-renᵉ ρ c

elts-renᵉ : ∀ ρ c → elts (renConvᵉ ρ c) ≡ map (renEltᵉ ρ) (elts c)
elts-renᵉ ρ (id A)    = refl
elts-renᵉ ρ (ĉ ∷ᶜ c) = cong (renEltᵉ ρ ĉ ∷_) (elts-renᵉ ρ c)


------------------------------------------------------------------------
-- The elementwise views commute with the renaming
------------------------------------------------------------------------
-- The renaming is pushed under a `Maybe (List ConvElt)` by `mapEls`
-- and under a `Maybe (List ConvElt × List ConvElt)` by `mapPr`.

mapEls : Renameᵇ → Maybe (List ConvElt) → Maybe (List ConvElt)
mapEls ρ (just es) = just (map (renEltᵉ ρ) es)
mapEls ρ nothing   = nothing

mapPr : Renameᵇ → Maybe (List ConvElt × List ConvElt)
  → Maybe (List ConvElt × List ConvElt)
mapPr ρ (just (Ls , Rs)) = just (map (renEltᵉ ρ) Ls , map (renEltᵉ ρ) Rs)
mapPr ρ nothing          = nothing

arr⁻-renᵉ : ∀ ρ ĉ → arr⁻ (renEltᵉ ρ ĉ) ≡ mapEls ρ (arr⁻ ĉ)
arr⁻-renᵉ ρ (seal X α)   = refl
arr⁻-renᵉ ρ (unseal X α) = refl
arr⁻-renᵉ ρ (hide X α)   = refl
arr⁻-renᵉ ρ (show X α)   = refl
arr⁻-renᵉ ρ (s ↦ t)      = cong just (elts-renᵉ ρ s)
arr⁻-renᵉ ρ (all s)      = refl

arr⁺-renᵉ : ∀ ρ ĉ → arr⁺ (renEltᵉ ρ ĉ) ≡ mapEls ρ (arr⁺ ĉ)
arr⁺-renᵉ ρ (seal X α)   = refl
arr⁺-renᵉ ρ (unseal X α) = refl
arr⁺-renᵉ ρ (hide X α)   = refl
arr⁺-renᵉ ρ (show X α)   = refl
arr⁺-renᵉ ρ (s ↦ t)      = cong just (elts-renᵉ ρ t)
arr⁺-renᵉ ρ (all s)      = refl

-- `all⁺` hoists an identity crossing under the ∀ element's binder, so
-- its address shifts; that shift is exactly what `renᵃᵉ-⇑ᵃ` commutes.
all⁺-renᵉ : ∀ ρ ĉ → all⁺ (renEltᵉ ρ ĉ) ≡ mapEls ρ (all⁺ ĉ)
all⁺-renᵉ ρ (seal X α)   = refl
all⁺-renᵉ ρ (unseal X α) = refl
all⁺-renᵉ ρ (hide X α)   = refl
all⁺-renᵉ ρ (show X α)   = refl
all⁺-renᵉ ρ (s ↦ t)      = refl
all⁺-renᵉ ρ (all s)      = cong just (elts-renᵉ ρ s)

------------------------------------------------------------------------
-- The folds commute with the renaming
------------------------------------------------------------------------

consArr-renᵉ : ∀ ρ l r q
  → consArr (mapEls ρ l) (mapEls ρ r) (mapPr ρ q)
  ≡ mapPr ρ (consArr l r q)
consArr-renᵉ ρ (just ls) (just rs) (just (Ls , Rs)) =
  cong₂ (λ x y → just (x , y))
    (sym (map-++ (renEltᵉ ρ) Ls ls))
    (sym (map-++ (renEltᵉ ρ) rs Rs))
consArr-renᵉ ρ (just ls) (just rs) nothing = refl
consArr-renᵉ ρ (just ls) nothing q = refl
consArr-renᵉ ρ nothing r q = refl

arrElts-renᵉ : ∀ ρ Es
  → arrElts (map (renEltᵉ ρ) Es) ≡ mapPr ρ (arrElts Es)
arrElts-renᵉ ρ [] = refl
arrElts-renᵉ ρ (ĉ ∷ Es)
  rewrite arr⁻-renᵉ ρ ĉ | arr⁺-renᵉ ρ ĉ | arrElts-renᵉ ρ Es =
  consArr-renᵉ ρ (arr⁻ ĉ) (arr⁺ ĉ) (arrElts Es)

consAllE-renᵉ : ∀ ρ e E
  → consAllE (mapEls ρ e) (mapEls ρ E) ≡ mapEls ρ (consAllE e E)
consAllE-renᵉ ρ (just es) (just Es) =
  cong just (sym (map-++ (renEltᵉ ρ) es Es))
consAllE-renᵉ ρ (just es) nothing = refl
consAllE-renᵉ ρ nothing E = refl

allElts-renᵉ : ∀ ρ Es
  → allElts (map (renEltᵉ ρ) Es) ≡ mapEls ρ (allElts Es)
allElts-renᵉ ρ [] = refl
allElts-renᵉ ρ (ĉ ∷ Es)
  rewrite all⁺-renᵉ ρ ĉ | allElts-renᵉ ρ Es =
  consAllE-renᵉ ρ (all⁺ ĉ) (allElts Es)

------------------------------------------------------------------------
-- The views themselves: SUCCESS is preserved
------------------------------------------------------------------------
-- The components `arrFrom` and `allFrom` build are NORMALIZED appends,
-- and a renaming does not commute with `normalize` on the nose — but
-- `Inert` asks only that the view succeed, so the Σ-form suffices.

arrFrom-ren : ∀ ρ A₀ q T {c₁ c₂} → arrFrom A₀ q T ≡ just (c₁ , c₂)
  → Σ[ d₁ ∈ Conv ] Σ[ d₂ ∈ Conv ]
      arrFrom A₀ (mapPr ρ q) T ≡ just (d₁ , d₂)
arrFrom-ren ρ A₀ (just (Ls , Rs)) (C ⇒ D) eq =
    normalize (attach (map (renEltᵉ ρ) Ls) A₀)
  , normalize (attach (map (renEltᵉ ρ) Rs) D)
  , refl
arrFrom-ren ρ A₀ (just p) (` X) ()
arrFrom-ren ρ A₀ (just p) `ℕ ()
arrFrom-ren ρ A₀ (just p) `𝔹 ()
arrFrom-ren ρ A₀ (just p) (`∀ B) ()
arrFrom-ren ρ A₀ nothing T ()

arr-renᵉ : ∀ ρ A₀ c {c₁ c₂} → arr A₀ c ≡ just (c₁ , c₂)
  → Σ[ d₁ ∈ Conv ] Σ[ d₂ ∈ Conv ]
      arr A₀ (renConvᵉ ρ c) ≡ just (d₁ , d₂)
arr-renᵉ ρ A₀ c eq
  with arrFrom-ren ρ A₀ (arrElts (elts c)) (target c) eq
arr-renᵉ ρ A₀ c eq | d₁ , d₂ , eq′ = d₁ , d₂ , unfolded
  where
  unfolded :
      arrFrom A₀ (arrElts (elts (renConvᵉ ρ c))) (target (renConvᵉ ρ c))
    ≡ just (d₁ , d₂)
  unfolded
    rewrite elts-renᵉ ρ c | arrElts-renᵉ ρ (elts c) | target-renᵉ ρ c =
    eq′

allFrom-ren : ∀ ρ Es T {d} → allFrom Es T ≡ just d
  → Σ[ e ∈ Conv ] allFrom (mapEls ρ Es) T ≡ just e
allFrom-ren ρ (just es) (`∀ B) eq =
  normalize (attach (map (renEltᵉ ρ) es) B) , refl
allFrom-ren ρ (just es) (` X) ()
allFrom-ren ρ (just es) `ℕ ()
allFrom-ren ρ (just es) `𝔹 ()
allFrom-ren ρ (just es) (C ⇒ D) ()
allFrom-ren ρ nothing T ()

allView-renᵉ : ∀ ρ c {d} → allView c ≡ just d
  → Σ[ e ∈ Conv ] allView (renConvᵉ ρ c) ≡ just e
allView-renᵉ ρ c eq
  with allFrom-ren ρ (allElts (elts c)) (target c) eq
allView-renᵉ ρ c eq | e , eq′ = e , unfolded
  where
  unfolded :
      allFrom (allElts (elts (renConvᵉ ρ c))) (target (renConvᵉ ρ c))
    ≡ just e
  unfolded
    rewrite elts-renᵉ ρ c | allElts-renᵉ ρ (elts c) | target-renᵉ ρ c =
    eq′

------------------------------------------------------------------------
-- Inertness survives a base renaming — unconditionally
------------------------------------------------------------------------

inert-renᵉ : ∀ {ρ c} → Inert c → Inert (renConvᵉ ρ c)
inert-renᵉ {ρ} {c} (inert-arr A₀ eq) with arr-renᵉ ρ A₀ c eq
inert-renᵉ {ρ} {c} (inert-arr A₀ eq) | d₁ , d₂ , eq′ = inert-arr A₀ eq′
inert-renᵉ {ρ} {c} (inert-all eq) with allView-renᵉ ρ c eq
inert-renᵉ {ρ} {c} (inert-all eq) | e , eq′ = inert-all eq′
inert-renᵉ {ρ} {c} (inert-var eq) = inert-var (trans (target-renᵉ ρ c) eq)

------------------------------------------------------------------------
-- Injective base renamings
------------------------------------------------------------------------

Injᵉ : Renameᵇ → Set
Injᵉ ρ = ∀ {α β} → renᵃᵉ ρ α ≡ renᵃᵉ ρ β → α ≡ β

-- Injectivity on addresses and injectivity on base indices are the same
-- thing: `renᵃᵉ` is the identity on the other two address forms.
injᵇ-of : ∀ {ρ} → Injᵉ ρ → ∀ {i j} → ρ i ≡ ρ j → i ≡ j
injᵇ-of inj e = bse-inj (inj (cong bse e))

injᵇ-to : ∀ {ρ} → (∀ {i j} → ρ i ≡ ρ j → i ≡ j) → Injᵉ ρ
injᵇ-to f {lvl ℓ} {lvl m} e = e
injᵇ-to f {lvl ℓ} {bse j} ()
injᵇ-to f {bse i} {lvl m} ()
injᵇ-to f {bse i} {bse j} e = cong bse (f (bse-inj e))

extᵇ-injᵇ : ∀ {ρ} → (∀ {i j} → ρ i ≡ ρ j → i ≡ j)
  → ∀ {i j} → extᵇ ρ i ≡ extᵇ ρ j → i ≡ j
extᵇ-injᵇ f {zero} {zero} e = refl
extᵇ-injᵇ f {zero} {suc j} ()
extᵇ-injᵇ f {suc i} {zero} ()
extᵇ-injᵇ f {suc i} {suc j} e = cong suc (f (suc-injective e))

extᵇ-injᵉ : ∀ {ρ} → Injᵉ ρ → Injᵉ (extᵇ ρ)
extᵇ-injᵉ inj = injᵇ-to (extᵇ-injᵇ (injᵇ-of inj))

suc-injᵉ : Injᵉ suc
suc-injᵉ = injᵇ-to suc-injective

------------------------------------------------------------------------
-- Normal forms survive an injective base renaming
------------------------------------------------------------------------
-- The four cancelling rows of `fuse` compare a NAME and an ADDRESS; a
-- base renaming leaves the name alone and moves the address
-- injectively, so a pair that did not cancel still does not.  Every
-- other row is decided by the element shapes, which renaming preserves.

fuse-renᵉ : ∀ {ρ} → Injᵉ ρ → ∀ ĉ ḓ → fuse ĉ ḓ ≡ nothing
  → fuse (renEltᵉ ρ ĉ) (renEltᵉ ρ ḓ) ≡ nothing
fuse-renᵉ inj (seal X α) (seal Y β) eq = refl
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq
  with X ≟ Y | α ≟ᵃ β | renᵃᵉ ρ α ≟ᵃ renᵃᵉ ρ β
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) () | yes _ | yes _ | _
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq | yes _ | no ne | yes e =
  ⊥-elim (ne (inj e))
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq | yes _ | no _ | no _ = refl
fuse-renᵉ {ρ = ρ} inj (seal X α) (unseal Y β) eq | no _ | _ | _ = refl
fuse-renᵉ inj (seal X α) (hide Y β) eq = refl
fuse-renᵉ inj (seal X α) (show Y β) eq = refl
fuse-renᵉ inj (seal X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (seal X α) (all s₂) eq = refl
fuse-renᵉ inj (unseal X α) (seal Y β) eq = refl
fuse-renᵉ inj (unseal X α) (unseal Y β) eq = refl
fuse-renᵉ inj (unseal X α) (hide Y β) eq = refl
fuse-renᵉ inj (unseal X α) (show Y β) eq = refl
fuse-renᵉ inj (unseal X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (unseal X α) (all s₂) eq = refl
fuse-renᵉ inj (hide X α) (seal Y β) eq = refl
fuse-renᵉ inj (hide X α) (unseal Y β) eq = refl
fuse-renᵉ inj (hide X α) (hide Y β) eq = refl
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq
  with X ≟ Y | α ≟ᵃ β | renᵃᵉ ρ α ≟ᵃ renᵃᵉ ρ β
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) () | yes _ | yes _ | _
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq | yes _ | no ne | yes e =
  ⊥-elim (ne (inj e))
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq | yes _ | no _ | no _ = refl
fuse-renᵉ {ρ = ρ} inj (hide X α) (show Y β) eq | no _ | _ | _ = refl
fuse-renᵉ inj (hide X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (hide X α) (all s₂) eq = refl
fuse-renᵉ inj (show X α) (seal Y β) eq = refl
fuse-renᵉ inj (show X α) (unseal Y β) eq = refl
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq
  with X ≟ Y | α ≟ᵃ β | renᵃᵉ ρ α ≟ᵃ renᵃᵉ ρ β
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) () | yes _ | yes _ | _
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq | yes _ | no ne | yes e =
  ⊥-elim (ne (inj e))
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq | yes _ | no _ | no _ = refl
fuse-renᵉ {ρ = ρ} inj (show X α) (hide Y β) eq | no _ | _ | _ = refl
fuse-renᵉ inj (show X α) (show Y β) eq = refl
fuse-renᵉ inj (show X α) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (show X α) (all s₂) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (seal Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (unseal Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (hide Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (show Y β) eq = refl
fuse-renᵉ inj (s₁ ↦ t₁) (s₂ ↦ t₂) ()
fuse-renᵉ inj (s₁ ↦ t₁) (all s₂) eq = refl
fuse-renᵉ inj (all s₁) (seal Y β) eq = refl
fuse-renᵉ inj (all s₁) (unseal Y β) eq = refl
fuse-renᵉ inj (all s₁) (hide Y β) eq = refl
fuse-renᵉ inj (all s₁) (show Y β) eq = refl
fuse-renᵉ inj (all s₁) (s₂ ↦ t₂) eq = refl
fuse-renᵉ inj (all s₁) (all s₂) ()

mutual
  nfElt-renᵉ : ∀ {ρ ĉ} → Injᵉ ρ → NFElt ĉ → NFElt (renEltᵉ ρ ĉ)
  nfElt-renᵉ inj nf-seal = nf-seal
  nfElt-renᵉ inj nf-unseal = nf-unseal
  nfElt-renᵉ inj nf-hide = nf-hide
  nfElt-renᵉ inj nf-show = nf-show
  nfElt-renᵉ inj (nf-fun s t) = nf-fun (nf-renᵉ inj s) (nf-renᵉ inj t)
  nfElt-renᵉ inj (nf-all s) = nf-all (nf-renᵉ inj s)

  irr-renᵉ : ∀ {ρ ĉ c} → Injᵉ ρ → IrreducibleAfter ĉ c
    → IrreducibleAfter (renEltᵉ ρ ĉ) (renConvᵉ ρ c)
  irr-renᵉ inj irr-id = irr-id
  irr-renᵉ {ĉ = ĉ} inj (irr-cons {ḓ = ḓ} e) = irr-cons (fuse-renᵉ inj ĉ ḓ e)

  nf-renᵉ : ∀ {ρ c} → Injᵉ ρ → NF c → NF (renConvᵉ ρ c)
  nf-renᵉ inj nf-id = nf-id
  nf-renᵉ inj (nf-cons hd tl irr) =
    nf-cons (nfElt-renᵉ inj hd) (nf-renᵉ inj tl) (irr-renᵉ inj irr)

------------------------------------------------------------------------
-- Valuehood survives an injective base renaming
------------------------------------------------------------------------
-- `Λ` is a base binder, so the renaming extends there — and `extᵇ`
-- preserves injectivity.

mutual
  simple-renᵉ : ∀ {ρ V} → Injᵉ ρ → Simple V → Simple (renBseᴹ ρ V)
  simple-renᵉ inj S$ = S$
  simple-renᵉ inj S# = S#
  simple-renᵉ inj Sƛ = Sƛ
  simple-renᵉ inj (SΛ v) = SΛ (value-renᵉ (extᵇ-injᵉ inj) v)

  value-renᵉ : ∀ {ρ V} → Injᵉ ρ → Value V → Value (renBseᴹ ρ V)
  value-renᵉ inj (Vs s) = Vs (simple-renᵉ inj s)
  value-renᵉ inj (V⟨⟩ s nf inrt) =
    V⟨⟩ (simple-renᵉ inj s) (nf-renᵉ inj nf) (inert-renᵉ inrt)

------------------------------------------------------------------------
-- Why the injectivity hypothesis cannot be dropped
------------------------------------------------------------------------
-- `$ 0 ⟨ hide 0 (bse 0) ∷ᶜ show 0 (bse 1) ∷ᶜ id (` 0) ⟩` is a value:
-- the conversion is a normal form (the pair does not cancel, the two
-- addresses differ) and it is inert (its target is a type variable).
-- The constant renaming `λ i → 0` identifies `bse 0` with `bse 1`, so
-- the pair cancels and the renamed conversion is no longer a normal
-- form — hence the renamed term is no longer a value.

private
  ce-conv : Conv
  ce-conv = hide zero (bse zero) ∷ᶜ show zero (bse (suc zero)) ∷ᶜ id (` zero)

  ce-nf : NF ce-conv
  ce-nf = nf-cons nf-hide (nf-cons nf-show nf-id irr-id) (irr-cons refl)

  ce-inert : Inert ce-conv
  ce-inert = inert-var refl

  ce-term : Term
  ce-term = ($ zero) ⟨ ce-conv ⟩

  ce-value : Value ce-term
  ce-value = V⟨⟩ S$ ce-nf ce-inert

  ce-ρ : Renameᵇ
  ce-ρ i = zero

  ce-¬value : ¬ Value (renBseᴹ ce-ρ ce-term)
  ce-¬value (Vs ())
  ce-¬value (V⟨⟩ s (nf-cons hd tl (irr-cons ())) inrt)

value-renᵉ-not-unconditional :
  ¬ (∀ {ρ V} → Value V → Value (renBseᴹ ρ V))
value-renᵉ-not-unconditional f = ce-¬value (f {ce-ρ} {ce-term} ce-value)
