module proof.ReductionProperties where

-- File Charter:
--   * Proof-only metatheory for Nu GTSF reduction.
--   * Multi-step composition, store-change action composition, and reduction
--     congruence lemmas for contexts that do not involve narrowing/widening.
--   * Narrowing/widening-specific reduction arguments belong in their
--     corresponding proof modules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; _≤_; zero; suc)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; suc-injective)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≢_; cong; cong₂; subst; sym; trans)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import proof.CoercionProperties
  using
    ( renameᶜ-dual-normal
    ; renameᶜ-ext-suc-suc
    ; renameᶜ-open-commute
    ; renameᶜ-preserves-Inert
    )
open import proof.NuTermProperties
  using
    ( renameᵗᵐ-ext-suc-comm
    ; renameᵗᵐ-open-commute
    ; renameᵗᵐ-preserves-Value
    ; renameᵗᵐ-preserves-No•
    ; renameᵗᵐ-pred-suc
    ; renameᵗᵐ-single-subst
    )
open import proof.TypeProperties using (predᵗ; renameᵗ-ext-suc-comm)

------------------------------------------------------------------------
-- Source shapes that can catch up to values
------------------------------------------------------------------------

-- A value-target narrowing source is never an active elimination form at its
-- reducible spine.  Values are leaves: applications and type applications
-- under lambda bodies are not inspected by reduction until the value itself is
-- eliminated by a surrounding context.
data CatchupSafe : Term → Set where
  safe-value :
    ∀ {V} →
    Value V →
    CatchupSafe V

  safe-ν :
    ∀ {A L c} →
    CatchupSafe L →
    CatchupSafe (ν A L c)

  safe-cast :
    ∀ {M c} →
    CatchupSafe M →
    CatchupSafe (M ⟨ c ⟩)

TermShiftImage : Term → Set
TermShiftImage M = ∃[ N ] (M ≡ ⇑ᵗᵐ N)

TyShiftImage : Ty → Set
TyShiftImage A = ∃[ B ] (A ≡ ⇑ᵗ B)

CoercionShiftImage : Coercion → Set
CoercionShiftImage c = ∃[ d ] (c ≡ renameᶜ suc d)

CoercionUnderShiftImage : Coercion → Set
CoercionUnderShiftImage c = ∃[ d ] (c ≡ renameᶜ (extᵗ suc) d)

shift-image-from-pre :
  ∀ {M N} →
  M ≡ ⇑ᵗᵐ N →
  M ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ M)
shift-image-from-pre {N = N} refl =
  sym (cong ⇑ᵗᵐ (renameᵗᵐ-pred-suc N))

term-shift-image-final :
  ∀ {M} →
  TermShiftImage M →
  M ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ M)
term-shift-image-final (N , M≡⇑N) =
  shift-image-from-pre M≡⇑N

cast-term-injective-left :
  ∀ {M N : Term} {c d : Coercion} →
  M ⟨ c ⟩ ≡ N ⟨ d ⟩ →
  M ≡ N
cast-term-injective-left refl = refl

cast-term-injective-right :
  ∀ {M N : Term} {c d : Coercion} →
  M ⟨ c ⟩ ≡ N ⟨ d ⟩ →
  c ≡ d
cast-term-injective-right refl = refl

ν-injective-ty :
  ∀ {A B : Ty} {M N : Term} {c d : Coercion} →
  ν A M c ≡ ν B N d →
  A ≡ B
ν-injective-ty refl = refl

ν-injective-term :
  ∀ {A B : Ty} {M N : Term} {c d : Coercion} →
  ν A M c ≡ ν B N d →
  M ≡ N
ν-injective-term refl = refl

ν-injective-coercion :
  ∀ {A B : Ty} {M N : Term} {c d : Coercion} →
  ν A M c ≡ ν B N d →
  c ≡ d
ν-injective-coercion refl = refl

seq-injective-left :
  ∀ {c d p q : Coercion} →
  c ︔ d ≡ p ︔ q →
  c ≡ p
seq-injective-left refl = refl

seq-injective-right :
  ∀ {c d p q : Coercion} →
  c ︔ d ≡ p ︔ q →
  d ≡ q
seq-injective-right refl = refl

inst-injective-ty :
  ∀ {A B : Ty} {c d : Coercion} →
  inst A c ≡ inst B d →
  A ≡ B
inst-injective-ty refl = refl

inst-injective-coercion :
  ∀ {A B : Ty} {c d : Coercion} →
  inst A c ≡ inst B d →
  c ≡ d
inst-injective-coercion refl = refl

cast-term-image-left :
  ∀ {M c} →
  TermShiftImage (M ⟨ c ⟩) →
  TermShiftImage M
cast-term-image-left (` x , ())
cast-term-image-left (ƛ P , ())
cast-term-image-left (P · Q , ())
cast-term-image-left (Λ P , ())
cast-term-image-left (P • , ())
cast-term-image-left (ν A P d , ())
cast-term-image-left ($ κ , ())
cast-term-image-left (P ⊕[ op ] Q , ())
cast-term-image-left (P ⟨ d ⟩ , eq) =
  P , cast-term-injective-left eq
cast-term-image-left (blame , ())

cast-coercion-image-right :
  ∀ {M c} →
  TermShiftImage (M ⟨ c ⟩) →
  CoercionShiftImage c
cast-coercion-image-right (` x , ())
cast-coercion-image-right (ƛ P , ())
cast-coercion-image-right (P · Q , ())
cast-coercion-image-right (Λ P , ())
cast-coercion-image-right (P • , ())
cast-coercion-image-right (ν A P d , ())
cast-coercion-image-right ($ κ , ())
cast-coercion-image-right (P ⊕[ op ] Q , ())
cast-coercion-image-right (P ⟨ d ⟩ , eq) =
  d , cast-term-injective-right eq
cast-coercion-image-right (blame , ())

ν-ty-image :
  ∀ {A M c} →
  TermShiftImage (ν A M c) →
  TyShiftImage A
ν-ty-image (` x , ())
ν-ty-image (ƛ P , ())
ν-ty-image (P · Q , ())
ν-ty-image (Λ P , ())
ν-ty-image (P • , ())
ν-ty-image (ν B P d , eq) =
  B , ν-injective-ty eq
ν-ty-image ($ κ , ())
ν-ty-image (P ⊕[ op ] Q , ())
ν-ty-image (P ⟨ d ⟩ , ())
ν-ty-image (blame , ())

ν-term-image :
  ∀ {A M c} →
  TermShiftImage (ν A M c) →
  TermShiftImage M
ν-term-image (` x , ())
ν-term-image (ƛ P , ())
ν-term-image (P · Q , ())
ν-term-image (Λ P , ())
ν-term-image (P • , ())
ν-term-image (ν B P d , eq) =
  P , ν-injective-term eq
ν-term-image ($ κ , ())
ν-term-image (P ⊕[ op ] Q , ())
ν-term-image (P ⟨ d ⟩ , ())
ν-term-image (blame , ())

ν-coercion-under-image :
  ∀ {A M c} →
  TermShiftImage (ν A M c) →
  CoercionUnderShiftImage c
ν-coercion-under-image (` x , ())
ν-coercion-under-image (ƛ P , ())
ν-coercion-under-image (P · Q , ())
ν-coercion-under-image (Λ P , ())
ν-coercion-under-image (P • , ())
ν-coercion-under-image (ν B P d , eq) =
  d , ν-injective-coercion eq
ν-coercion-under-image ($ κ , ())
ν-coercion-under-image (P ⊕[ op ] Q , ())
ν-coercion-under-image (P ⟨ d ⟩ , ())
ν-coercion-under-image (blame , ())

term-image-cast :
  ∀ {M c} →
  TermShiftImage M →
  CoercionShiftImage c →
  TermShiftImage (M ⟨ c ⟩)
term-image-cast (P , refl) (d , refl) =
  P ⟨ d ⟩ , refl

term-image-ν :
  ∀ {A M c} →
  TyShiftImage A →
  TermShiftImage M →
  CoercionUnderShiftImage c →
  TermShiftImage (ν A M c)
term-image-ν (B , refl) (P , refl) (d , refl) =
  ν B P d , refl

seq-coercion-image-left :
  ∀ {c d} →
  CoercionShiftImage (c ︔ d) →
  CoercionShiftImage c
seq-coercion-image-left (id A , ())
seq-coercion-image-left (p ︔ q , eq) =
  p , seq-injective-left eq
seq-coercion-image-left (p ↦ q , ())
seq-coercion-image-left (`∀ p , ())
seq-coercion-image-left (A ! , ())
seq-coercion-image-left (A ？ , ())
seq-coercion-image-left (seal A α , ())
seq-coercion-image-left (unseal α A , ())
seq-coercion-image-left (gen A p , ())
seq-coercion-image-left (inst A p , ())

seq-coercion-image-right :
  ∀ {c d} →
  CoercionShiftImage (c ︔ d) →
  CoercionShiftImage d
seq-coercion-image-right (id A , ())
seq-coercion-image-right (p ︔ q , eq) =
  q , seq-injective-right eq
seq-coercion-image-right (p ↦ q , ())
seq-coercion-image-right (`∀ p , ())
seq-coercion-image-right (A ! , ())
seq-coercion-image-right (A ？ , ())
seq-coercion-image-right (seal A α , ())
seq-coercion-image-right (unseal α A , ())
seq-coercion-image-right (gen A p , ())
seq-coercion-image-right (inst A p , ())

inst-ty-image :
  ∀ {A c} →
  CoercionShiftImage (inst A c) →
  TyShiftImage A
inst-ty-image (id B , ())
inst-ty-image (p ︔ q , ())
inst-ty-image (p ↦ q , ())
inst-ty-image (`∀ p , ())
inst-ty-image (B ! , ())
inst-ty-image (B ？ , ())
inst-ty-image (seal B α , ())
inst-ty-image (unseal α B , ())
inst-ty-image (gen B p , ())
inst-ty-image (inst B p , eq) =
  B , inst-injective-ty eq

inst-coercion-under-image :
  ∀ {A c} →
  CoercionShiftImage (inst A c) →
  CoercionUnderShiftImage c
inst-coercion-under-image (id B , ())
inst-coercion-under-image (p ︔ q , ())
inst-coercion-under-image (p ↦ q , ())
inst-coercion-under-image (`∀ p , ())
inst-coercion-under-image (B ! , ())
inst-coercion-under-image (B ？ , ())
inst-coercion-under-image (seal B α , ())
inst-coercion-under-image (unseal α B , ())
inst-coercion-under-image (gen B p , ())
inst-coercion-under-image (inst B p , eq) =
  p , inst-injective-coercion eq

------------------------------------------------------------------------
-- Store-change list views
------------------------------------------------------------------------

-- A plain snoc view was tried first for emitted store-change prefixes, but it
-- loses the information catchup needs: whether the last non-keep change is a
-- binder.  The surviving proofs use `StoreChangesLastBind` instead.

data AllKeep : StoreChanges → Set where
  all-[] :
    AllKeep []
  all-keep : ∀ {χs} →
    AllKeep χs →
    AllKeep (keep ∷ χs)

data StoreChangesLastBind : StoreChanges → Set where
  no-bind : ∀ {χs} →
    AllKeep χs →
    StoreChangesLastBind χs
  last-bind : ∀ χs A keeps →
    AllKeep keeps →
    StoreChangesLastBind (χs ++ bind A ∷ keeps)

storeChangesLastBind : ∀ χs → StoreChangesLastBind χs
storeChangesLastBind [] = no-bind all-[]
storeChangesLastBind (keep ∷ χs)
    with storeChangesLastBind χs
storeChangesLastBind (keep ∷ χs) | no-bind keeps =
  no-bind (all-keep keeps)
storeChangesLastBind (keep ∷ .(χs ++ bind A ∷ keeps))
    | last-bind χs A keeps keeps-ok =
  last-bind (keep ∷ χs) A keeps keeps-ok
storeChangesLastBind (bind A ∷ χs)
    with storeChangesLastBind χs
storeChangesLastBind (bind A ∷ χs) | no-bind keeps =
  last-bind [] A χs keeps
storeChangesLastBind (bind A ∷ .(χs ++ bind B ∷ keeps))
    | last-bind χs B keeps keeps-ok =
  last-bind (bind A ∷ χs) B keeps keeps-ok

------------------------------------------------------------------------
-- Finality facts
------------------------------------------------------------------------

value-no-pure-step :
  ∀ {V N} →
  Value V →
  V —→ N →
  ⊥
value-no-pure-step (ƛ N) ()
value-no-pure-step (Λ vV) ()
value-no-pure-step ($ κ) ()
value-no-pure-step (() ⟨ G ! ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ seal A α ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ c ↦ d ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ `∀ c ⟩) blame-⟨⟩
value-no-pure-step (() ⟨ gen A c ⟩) blame-⟨⟩

value-no-step :
  ∀ {χ V N} →
  Value V →
  V —→[ χ ] N →
  ⊥
value-no-step vV (pure-step red) =
  value-no-pure-step vV red
value-no-step (vV ⟨ i ⟩) (ξ-⟨⟩ red) =
  value-no-step vV red

blame-not-value :
  Value blame →
  ⊥
blame-not-value ()

blame-no-pure-step :
  ∀ {N} →
  blame —→ N →
  ⊥
blame-no-pure-step ()

blame-no-step :
  ∀ {χ N} →
  blame —→[ χ ] N →
  ⊥
blame-no-step (pure-step red) =
  blame-no-pure-step red

NoValueReachable : Term → Set
NoValueReachable M = ∀ {χs V} → M —↠[ χs ] V → Value V → ⊥

blame-no-↠-value :
  NoValueReachable blame
blame-no-↠-value ↠-refl vV =
  blame-not-value vV
blame-no-↠-value (↠-step red reds) vV =
  blame-no-step red

noValue-·₁ :
  ∀ {L M} →
  NoValueReachable L →
  NoValueReachable (L · M)
noValue-·₁ noL ↠-refl ()
noValue-·₁ noL (↠-step (pure-step (β vV)) reds) vW =
  noL ↠-refl (ƛ _)
noValue-·₁ noL
    (↠-step (pure-step (β-↦ {p = p} {q = q} vV vW)) reds) vP =
  noL ↠-refl (vV ⟨ p ↦ q ⟩)
noValue-·₁ noL (↠-step (pure-step blame-·₁) reds) vW =
  blame-no-↠-value reds vW
noValue-·₁ noL (↠-step (pure-step (blame-·₂ vV)) reds) vW =
  noL ↠-refl vV
noValue-·₁ noL (↠-step (ξ-·₁ red shiftM) reds) vW =
  noValue-·₁ (λ redsL vL → noL (↠-step red redsL) vL) reds vW
noValue-·₁ noL (↠-step (ξ-·₂ vV shiftV red) reds) vW =
  noL ↠-refl vV

noValue-·₂ :
  ∀ {V M} →
  Value V →
  NoValueReachable M →
  NoValueReachable (V · M)
noValue-·₂ vV noM ↠-refl ()
noValue-·₂ vV noM (↠-step (pure-step (β vM)) reds) vW =
  noM ↠-refl vM
noValue-·₂ vV noM (↠-step (pure-step (β-↦ vF vM)) reds) vW =
  noM ↠-refl vM
noValue-·₂ vV noM (↠-step (pure-step (blame-·₂ vF)) reds) vW =
  blame-no-↠-value reds vW
noValue-·₂ vV noM (↠-step (ξ-·₁ red shiftM) reds) vW =
  value-no-step vV red
noValue-·₂ vV noM (↠-step (ξ-·₂ {χ = keep} vF shiftV red) reds) vW =
  noValue-·₂ vV
    (λ redsM vM → noM (↠-step red redsM) vM)
    reds
    vW
noValue-·₂ vV noM
    (↠-step (ξ-·₂ {χ = bind A} vF shiftV red) reds) vW =
  noValue-·₂ (renameᵗᵐ-preserves-Value suc vV)
    (λ redsM vM → noM (↠-step red redsM) vM)
    reds
    vW

noValue-cast :
  ∀ {M c} →
  NoValueReachable M →
  NoValueReachable (M ⟨ c ⟩)
noValue-cast noM ↠-refl (vM ⟨ i ⟩) =
  noM ↠-refl vM
noValue-cast noM (↠-step (pure-step (β-id vV)) reds) vW =
  noM ↠-refl vV
noValue-cast noM (↠-step (pure-step (β-seq vV)) reds) vW =
  noM ↠-refl vV
noValue-cast noM (↠-step (pure-step (β-inst vV)) reds) vW =
  noM ↠-refl vV
noValue-cast noM
    (↠-step (pure-step (tag-untag-ok {G = G} vV)) reds) vW =
  noM ↠-refl (vV ⟨ G ! ⟩)
noValue-cast noM
    (↠-step (pure-step (tag-untag-bad {G = G} vV G≢H)) reds) vW =
  noM ↠-refl (vV ⟨ G ! ⟩)
noValue-cast noM
    (↠-step (pure-step (seal-unseal {α = α} vV)) reds) vW =
  noM ↠-refl (vV ⟨ seal _ α ⟩)
noValue-cast noM (↠-step (pure-step blame-⟨⟩) reds) vW =
  blame-no-↠-value reds vW
noValue-cast noM (↠-step (ξ-⟨⟩ red) reds) vW =
  noValue-cast (λ redsM vM → noM (↠-step red redsM) vM) reds vW

tag-untag-bad-noValue :
  ∀ {V G H} →
  Value V →
  G ≢ H →
  NoValueReachable (V ⟨ G ! ⟩ ⟨ H ？ ⟩)
tag-untag-bad-noValue vV G≢H ↠-refl (vVG ⟨ () ⟩)
tag-untag-bad-noValue vV G≢H
    (↠-step (pure-step (tag-untag-ok vV′)) reds) vW =
  G≢H refl
tag-untag-bad-noValue vV G≢H
    (↠-step (pure-step (tag-untag-bad vV′ G≢H′)) reds) vW =
  blame-no-↠-value reds vW
tag-untag-bad-noValue vV G≢H (↠-step (ξ-⟨⟩ red) reds) vW =
  value-no-step (vV ⟨ _ ! ⟩) red

noValue-ν :
  ∀ {A M c} →
  NoValueReachable M →
  NoValueReachable (ν A M c)
noValue-ν noM ↠-refl ()
noValue-ν noM (↠-step (ν-step vM no•M) reds) vW =
  noM ↠-refl vM
noValue-ν noM (↠-step (ξ-ν red) reds) vW =
  noValue-ν (λ redsM vM → noM (↠-step red redsM) vM) reds vW
noValue-ν noM (↠-step blame-ν reds) vW =
  blame-no-↠-value reds vW

data ImageStepView (N : Term) : Set where
  image-step :
    CatchupSafe N →
    TermShiftImage N →
    ImageStepView N
  image-doomed :
    NoValueReachable N →
    ImageStepView N

safe-pure-step-image-view :
  ∀ {M N} →
  CatchupSafe M →
  TermShiftImage M →
  M —→ N →
  ImageStepView N
safe-pure-step-image-view (safe-value vM) img red =
  ⊥-elim (value-no-pure-step vM red)
safe-pure-step-image-view (safe-cast safeM) img (β-id vV) =
  image-step (safe-value vV) (cast-term-image-left img)
safe-pure-step-image-view (safe-cast safeM) img (β-seq vV) =
  image-step (safe-cast (safe-cast (safe-value vV)))
    (term-image-cast
      (term-image-cast (cast-term-image-left img)
      (seq-coercion-image-left (cast-coercion-image-right img)))
      (seq-coercion-image-right (cast-coercion-image-right img)))
safe-pure-step-image-view (safe-cast safeM) img (β-inst vV) =
  image-step (safe-ν (safe-value vV))
    (term-image-ν (★ , refl) (cast-term-image-left img)
      (inst-coercion-under-image (cast-coercion-image-right img)))
safe-pure-step-image-view (safe-cast safeM) img (tag-untag-ok vV) =
  image-step (safe-value vV)
    (cast-term-image-left (cast-term-image-left img))
safe-pure-step-image-view (safe-cast safeM) img (tag-untag-bad vV G≢H) =
  image-doomed blame-no-↠-value
safe-pure-step-image-view (safe-cast safeM) img (seal-unseal vV) =
  image-step (safe-value vV)
    (cast-term-image-left (cast-term-image-left img))
safe-pure-step-image-view (safe-cast (safe-value vB)) img blame-⟨⟩ =
  ⊥-elim (blame-not-value vB)

safe-keep-step-image-view :
  ∀ {M N} →
  CatchupSafe M →
  TermShiftImage M →
  M —→[ keep ] N →
  ImageStepView N
safe-keep-step-image-view (safe-value vM) img red =
  ⊥-elim (value-no-step vM red)
safe-keep-step-image-view safeM img (pure-step red) =
  safe-pure-step-image-view safeM img red
safe-keep-step-image-view (safe-cast safeM) img (ξ-⟨⟩ red)
    with safe-keep-step-image-view safeM (cast-term-image-left img) red
safe-keep-step-image-view (safe-cast safeM) img (ξ-⟨⟩ red)
    | image-step safeN imgN =
  image-step (safe-cast safeN)
    (term-image-cast imgN (cast-coercion-image-right img))
safe-keep-step-image-view (safe-cast safeM) img (ξ-⟨⟩ red)
    | image-doomed noN =
  image-doomed (noValue-cast noN)
safe-keep-step-image-view (safe-ν safeL) img (ξ-ν red)
    with safe-keep-step-image-view safeL (ν-term-image img) red
safe-keep-step-image-view (safe-ν safeL) img (ξ-ν red)
    | image-step safeL′ imgL′ =
  image-step (safe-ν safeL′)
    (term-image-ν (ν-ty-image img) imgL′ (ν-coercion-under-image img))
safe-keep-step-image-view (safe-ν safeL) img (ξ-ν red)
    | image-doomed noL =
  image-doomed (noValue-ν noL)
safe-keep-step-image-view (safe-ν (safe-value vB)) img blame-ν =
  ⊥-elim (blame-not-value vB)

safe-allKeep-value-image :
  ∀ {M W χs} →
  CatchupSafe M →
  TermShiftImage M →
  AllKeep χs →
  M —↠[ χs ] W →
  Value W →
  W ≡ ⇑ᵗᵐ (renameᵗᵐ predᵗ W)
safe-allKeep-value-image safeM img all-[] ↠-refl vW =
  term-shift-image-final img
safe-allKeep-value-image safeM img (all-keep keeps) (↠-step red reds) vW
    with safe-keep-step-image-view safeM img red
safe-allKeep-value-image safeM img (all-keep keeps) (↠-step red reds) vW
    | image-step safeN imgN =
  safe-allKeep-value-image safeN imgN keeps reds vW
safe-allKeep-value-image safeM img (all-keep keeps) (↠-step red reds) vW
    | image-doomed noN =
  ⊥-elim (noN reds vW)

noValue-⊕₁ :
  ∀ {L M op} →
  NoValueReachable L →
  NoValueReachable (L ⊕[ op ] M)
noValue-⊕₁ noL ↠-refl ()
noValue-⊕₁ noL (↠-step (pure-step δ-⊕) reds) vW =
  noL ↠-refl ($ _)
noValue-⊕₁ noL (↠-step (pure-step blame-⊕₁) reds) vW =
  blame-no-↠-value reds vW
noValue-⊕₁ noL (↠-step (pure-step (blame-⊕₂ vL)) reds) vW =
  noL ↠-refl vL
noValue-⊕₁ noL (↠-step (ξ-⊕₁ red shiftM) reds) vW =
  noValue-⊕₁ (λ redsL vL → noL (↠-step red redsL) vL) reds vW
noValue-⊕₁ noL (↠-step (ξ-⊕₂ vL shiftL red) reds) vW =
  noL ↠-refl vL

noValue-⊕₂ :
  ∀ {L M op} →
  Value L →
  NoValueReachable M →
  NoValueReachable (L ⊕[ op ] M)
noValue-⊕₂ vL noM ↠-refl ()
noValue-⊕₂ vL noM (↠-step (pure-step δ-⊕) reds) vW =
  noM ↠-refl ($ _)
noValue-⊕₂ vL noM (↠-step (pure-step (blame-⊕₂ vL′)) reds) vW =
  blame-no-↠-value reds vW
noValue-⊕₂ vL noM (↠-step (ξ-⊕₁ red shiftM) reds) vW =
  value-no-step vL red
noValue-⊕₂ vL noM
    (↠-step (ξ-⊕₂ {χ = keep} vL′ shiftL red) reds) vW =
  noValue-⊕₂ vL
    (λ redsM vM → noM (↠-step red redsM) vM)
    reds
    vW
noValue-⊕₂ vL noM
    (↠-step (ξ-⊕₂ {χ = bind A} vL′ shiftL red) reds) vW =
  noValue-⊕₂ (renameᵗᵐ-preserves-Value suc vL)
    (λ redsM vM → noM (↠-step red redsM) vM)
    reds
    vW

applyTyCtx-≤ :
  ∀ χ Δ →
  Δ ≤ applyTyCtx χ Δ
applyTyCtx-≤ keep Δ = ≤-refl
applyTyCtx-≤ (bind A) Δ = n≤1+n Δ

applyTyCtxs-≤ :
  ∀ χs Δ →
  Δ ≤ applyTyCtxs χs Δ
applyTyCtxs-≤ [] Δ = ≤-refl
applyTyCtxs-≤ (χ ∷ χs) Δ =
  ≤-trans (applyTyCtx-≤ χ Δ) (applyTyCtxs-≤ χs (applyTyCtx χ Δ))

------------------------------------------------------------------------
-- Store-change composition
------------------------------------------------------------------------

storeTail : Store → Store
storeTail [] = []
storeTail (_ ∷ Σ) = Σ

storeHead-∷≡ :
  ∀ {x y : TyVar × Ty}{Σ Σ′} →
  x ∷ Σ ≡ y ∷ Σ′ →
  x ≡ y
storeHead-∷≡ refl = refl

storeTail-∷≡ :
  ∀ {x y : TyVar × Ty}{Σ Σ′} →
  x ∷ Σ ≡ y ∷ Σ′ →
  Σ ≡ Σ′
storeTail-∷≡ eq = cong storeTail eq

shiftVar : ℕ → TyVar → TyVar
shiftVar zero X = X
shiftVar (suc n) X = suc (shiftVar n X)

shiftTy : ℕ → Ty → Ty
shiftTy zero A = A
shiftTy (suc n) A = ⇑ᵗ (shiftTy n A)

shiftStore : ℕ → Store → Store
shiftStore zero Σ = Σ
shiftStore (suc n) Σ = ⟰ᵗ (shiftStore n Σ)

shiftStore-empty :
  ∀ n →
  shiftStore n [] ≡ []
shiftStore-empty zero = refl
shiftStore-empty (suc n) rewrite shiftStore-empty n = refl

shiftStore-cons :
  ∀ n α A Σ →
  shiftStore n ((α , A) ∷ Σ) ≡
    (shiftVar n α , shiftTy n A) ∷ shiftStore n Σ
shiftStore-cons zero α A Σ = refl
shiftStore-cons (suc n) α A Σ
    rewrite shiftStore-cons n α A Σ =
  refl

shiftStore-⟰ᵗ :
  ∀ n Σ →
  shiftStore n (⟰ᵗ Σ) ≡ ⟰ᵗ (shiftStore n Σ)
shiftStore-⟰ᵗ zero Σ = refl
shiftStore-⟰ᵗ (suc n) Σ =
  cong ⟰ᵗ (shiftStore-⟰ᵗ n Σ)

renameStoreᵗ-empty-inv :
  ∀ ρ {Σ} →
  renameStoreᵗ ρ Σ ≡ [] →
  Σ ≡ []
renameStoreᵗ-empty-inv ρ {[]} eq = refl
renameStoreᵗ-empty-inv ρ {_ ∷ Σ} ()

⟰ᵗ-empty-inv :
  ∀ {Σ} →
  ⟰ᵗ Σ ≡ [] →
  Σ ≡ []
⟰ᵗ-empty-inv = renameStoreᵗ-empty-inv suc

shiftStore-empty-inv :
  ∀ n {Σ} →
  shiftStore n Σ ≡ [] →
  Σ ≡ []
shiftStore-empty-inv zero eq = eq
shiftStore-empty-inv (suc n) eq =
  shiftStore-empty-inv n (⟰ᵗ-empty-inv eq)

applyStores-++ :
  ∀ χs χs′ Σ →
  applyStores (χs ++ χs′) Σ ≡ applyStores χs′ (applyStores χs Σ)
applyStores-++ [] χs′ Σ = refl
applyStores-++ (χ ∷ χs) χs′ Σ =
  applyStores-++ χs χs′ (applyStore χ Σ)

allKeep-applyStores-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ Σ → applyStores χs Σ ≡ Σ
allKeep-applyStores-id all-[] Σ = refl
allKeep-applyStores-id (all-keep keeps) Σ =
  allKeep-applyStores-id keeps Σ

applyStores-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ Σ →
  applyStores (χs ++ bind A ∷ keeps) Σ ≡
    applyStore (bind A) (applyStores χs Σ)
applyStores-last-bind χs A keeps keeps-ok Σ =
  trans
    (applyStores-++ χs (bind A ∷ keeps) Σ)
    (allKeep-applyStores-id keeps-ok
      (applyStore (bind A) (applyStores χs Σ)))

applyStores-last-bind-tail :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ Σ →
  storeTail (applyStores (χs ++ bind A ∷ keeps) Σ) ≡
    ⟰ᵗ (applyStores χs Σ)
applyStores-last-bind-tail χs A keeps keeps-ok Σ =
  cong storeTail (applyStores-last-bind χs A keeps keeps-ok Σ)

applyStores-cons≢[] :
  ∀ χs {α A Σ} →
  applyStores χs ((α , A) ∷ Σ) ≢ []
applyStores-cons≢[] [] ()
applyStores-cons≢[] (keep ∷ χs) eq =
  applyStores-cons≢[] χs eq
applyStores-cons≢[] (bind A ∷ χs) eq =
  applyStores-cons≢[] χs eq

applyStores-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ Σ → applyStores χs Σ ≡ Σ
applyStores-empty-id [] eq Σ = refl
applyStores-empty-id (keep ∷ χs) eq Σ =
  applyStores-empty-id χs eq Σ
applyStores-empty-id (bind A ∷ χs) eq Σ =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTyCtxs-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ Δ → applyTyCtxs χs Δ ≡ Δ
applyTyCtxs-empty-id [] eq Δ = refl
applyTyCtxs-empty-id (keep ∷ χs) eq Δ =
  applyTyCtxs-empty-id χs eq Δ
applyTyCtxs-empty-id (bind A ∷ χs) eq Δ =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTys-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ A → applyTys χs A ≡ A
applyTys-empty-id [] eq A = refl
applyTys-empty-id (keep ∷ χs) eq A =
  applyTys-empty-id χs eq A
applyTys-empty-id (bind A ∷ χs) eq B =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTy-★ :
  ∀ χ →
  applyTy χ ★ ≡ ★
applyTy-★ keep = refl
applyTy-★ (bind A) = refl

applyTys-★ :
  ∀ χs →
  applyTys χs ★ ≡ ★
applyTys-★ [] = refl
applyTys-★ (χ ∷ χs) rewrite applyTy-★ χ = applyTys-★ χs

applyTerms-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ M → applyTerms χs M ≡ M
applyTerms-empty-id [] eq M = refl
applyTerms-empty-id (keep ∷ χs) eq M =
  applyTerms-empty-id χs eq M
applyTerms-empty-id (bind A ∷ χs) eq M =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyTyCtxs-++ :
  ∀ χs χs′ Δ →
  applyTyCtxs (χs ++ χs′) Δ ≡ applyTyCtxs χs′ (applyTyCtxs χs Δ)
applyTyCtxs-++ [] χs′ Δ = refl
applyTyCtxs-++ (χ ∷ χs) χs′ Δ =
  applyTyCtxs-++ χs χs′ (applyTyCtx χ Δ)

allKeep-applyTyCtxs-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ Δ → applyTyCtxs χs Δ ≡ Δ
allKeep-applyTyCtxs-id all-[] Δ = refl
allKeep-applyTyCtxs-id (all-keep keeps) Δ =
  allKeep-applyTyCtxs-id keeps Δ

applyTyCtxs-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ Δ →
  applyTyCtxs (χs ++ bind A ∷ keeps) Δ ≡ suc (applyTyCtxs χs Δ)
applyTyCtxs-last-bind χs A keeps keeps-ok Δ =
  trans
    (applyTyCtxs-++ χs (bind A ∷ keeps) Δ)
    (allKeep-applyTyCtxs-id keeps-ok (suc (applyTyCtxs χs Δ)))

applyTyCtxs-suc :
  ∀ χs Δ →
  applyTyCtxs χs (suc Δ) ≡ suc (applyTyCtxs χs Δ)
applyTyCtxs-suc [] Δ = refl
applyTyCtxs-suc (keep ∷ χs) Δ = applyTyCtxs-suc χs Δ
applyTyCtxs-suc (bind A ∷ χs) Δ = applyTyCtxs-suc χs (suc Δ)

applyTyCtxs-last-bind-suc :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ Δ →
  applyTyCtxs (χs ++ bind A ∷ keeps) (suc Δ) ≡
    suc (suc (applyTyCtxs χs Δ))
applyTyCtxs-last-bind-suc χs A keeps keeps-ok Δ =
  trans
    (applyTyCtxs-last-bind χs A keeps keeps-ok (suc Δ))
    (cong suc (applyTyCtxs-suc χs Δ))

applyTys-++ :
  ∀ χs χs′ A →
  applyTys (χs ++ χs′) A ≡ applyTys χs′ (applyTys χs A)
applyTys-++ [] χs′ A = refl
applyTys-++ (χ ∷ χs) χs′ A =
  applyTys-++ χs χs′ (applyTy χ A)

allKeep-applyTys-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ A → applyTys χs A ≡ A
allKeep-applyTys-id all-[] A = refl
allKeep-applyTys-id (all-keep keeps) A =
  allKeep-applyTys-id keeps A

applyTys-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ B →
  applyTys (χs ++ bind A ∷ keeps) B ≡ ⇑ᵗ (applyTys χs B)
applyTys-last-bind χs A keeps keeps-ok B =
  trans
    (applyTys-++ χs (bind A ∷ keeps) B)
    (allKeep-applyTys-id keeps-ok (⇑ᵗ (applyTys χs B)))

applyTys-⇑ᵗ :
  ∀ χs A →
  applyTys χs (⇑ᵗ A) ≡ ⇑ᵗ (applyTys χs A)
applyTys-⇑ᵗ [] A = refl
applyTys-⇑ᵗ (keep ∷ χs) A = applyTys-⇑ᵗ χs A
applyTys-⇑ᵗ (bind B ∷ χs) A = applyTys-⇑ᵗ χs (⇑ᵗ A)

applyTyUnderTyBinder : StoreChange → Ty → Ty
applyTyUnderTyBinder keep A = A
applyTyUnderTyBinder (bind B) A = renameᵗ (extᵗ suc) A

applyTysUnderTyBinders : StoreChanges → Ty → Ty
applyTysUnderTyBinders [] A = A
applyTysUnderTyBinders (χ ∷ χs) A =
  applyTysUnderTyBinders χs (applyTyUnderTyBinder χ A)

applyTysUnderTyBinders-⇑ᵗ :
  ∀ χs A →
  applyTysUnderTyBinders χs (⇑ᵗ A) ≡ ⇑ᵗ (applyTys χs A)
applyTysUnderTyBinders-⇑ᵗ [] A = refl
applyTysUnderTyBinders-⇑ᵗ (keep ∷ χs) A =
  applyTysUnderTyBinders-⇑ᵗ χs A
applyTysUnderTyBinders-⇑ᵗ (bind B ∷ χs) A =
  trans
    (cong (applyTysUnderTyBinders χs) (renameᵗ-ext-suc-comm suc A))
    (applyTysUnderTyBinders-⇑ᵗ χs (⇑ᵗ A))

applyTys-∀ :
  ∀ χs A →
  applyTys χs (`∀ A) ≡ `∀ (applyTysUnderTyBinders χs A)
applyTys-∀ [] A = refl
applyTys-∀ (keep ∷ χs) A = applyTys-∀ χs A
applyTys-∀ (bind B ∷ χs) A =
  applyTys-∀ χs (renameᵗ (extᵗ suc) A)

applyTyVar : StoreChange → TyVar → TyVar
applyTyVar keep α = α
applyTyVar (bind A) α = suc α

applyTyVars : StoreChanges → TyVar → TyVar
applyTyVars [] α = α
applyTyVars (χ ∷ χs) α = applyTyVars χs (applyTyVar χ α)

applyTyVars-++ :
  ∀ χs χs′ α →
  applyTyVars (χs ++ χs′) α ≡ applyTyVars χs′ (applyTyVars χs α)
applyTyVars-++ [] χs′ α = refl
applyTyVars-++ (χ ∷ χs) χs′ α =
  applyTyVars-++ χs χs′ (applyTyVar χ α)

applyTerms-++ :
  ∀ χs χs′ M →
  applyTerms (χs ++ χs′) M ≡ applyTerms χs′ (applyTerms χs M)
applyTerms-++ [] χs′ M = refl
applyTerms-++ (χ ∷ χs) χs′ M =
  applyTerms-++ χs χs′ (applyTerm χ M)

allKeep-applyTerms-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ M → applyTerms χs M ≡ M
allKeep-applyTerms-id all-[] M = refl
allKeep-applyTerms-id (all-keep keeps) M =
  allKeep-applyTerms-id keeps M

applyTerms-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ M →
  applyTerms (χs ++ bind A ∷ keeps) M ≡ ⇑ᵗᵐ (applyTerms χs M)
applyTerms-last-bind χs A keeps keeps-ok M =
  trans
    (applyTerms-++ χs (bind A ∷ keeps) M)
    (allKeep-applyTerms-id keeps-ok (⇑ᵗᵐ (applyTerms χs M)))

applyTerms-⇑ᵗᵐ :
  ∀ χs M →
  applyTerms χs (⇑ᵗᵐ M) ≡ ⇑ᵗᵐ (applyTerms χs M)
applyTerms-⇑ᵗᵐ [] M = refl
applyTerms-⇑ᵗᵐ (keep ∷ χs) M = applyTerms-⇑ᵗᵐ χs M
applyTerms-⇑ᵗᵐ (bind A ∷ χs) M = applyTerms-⇑ᵗᵐ χs (⇑ᵗᵐ M)

applyTerm-preserves-Value :
  ∀ χ {V} →
  Value V →
  Value (applyTerm χ V)
applyTerm-preserves-Value keep vV = vV
applyTerm-preserves-Value (bind A) vV = renameᵗᵐ-preserves-Value suc vV

applyTerms-preserves-Value :
  ∀ χs {V} →
  Value V →
  Value (applyTerms χs V)
applyTerms-preserves-Value [] vV = vV
applyTerms-preserves-Value (χ ∷ χs) vV =
  applyTerms-preserves-Value χs (applyTerm-preserves-Value χ vV)

applyTerm-preserves-No• :
  ∀ χ {M} →
  No• M →
  No• (applyTerm χ M)
applyTerm-preserves-No• keep noM = noM
applyTerm-preserves-No• (bind A) noM = renameᵗᵐ-preserves-No• suc noM

applyTerms-preserves-No• :
  ∀ χs {M} →
  No• M →
  No• (applyTerms χs M)
applyTerms-preserves-No• [] noM = noM
applyTerms-preserves-No• (χ ∷ χs) noM =
  applyTerms-preserves-No• χs (applyTerm-preserves-No• χ noM)

applyTermUnderTyBinder : StoreChange → Term → Term
applyTermUnderTyBinder keep M = M
applyTermUnderTyBinder (bind A) M = renameᵗᵐ (extᵗ suc) M

applyTermsUnderTyBinders : StoreChanges → Term → Term
applyTermsUnderTyBinders [] M = M
applyTermsUnderTyBinders (χ ∷ χs) M =
  applyTermsUnderTyBinders χs (applyTermUnderTyBinder χ M)

applyTermsUnderTyBinders-⇑ᵗᵐ :
  ∀ χs M →
  applyTermsUnderTyBinders χs (⇑ᵗᵐ M) ≡ ⇑ᵗᵐ (applyTerms χs M)
applyTermsUnderTyBinders-⇑ᵗᵐ [] M = refl
applyTermsUnderTyBinders-⇑ᵗᵐ (keep ∷ χs) M =
  applyTermsUnderTyBinders-⇑ᵗᵐ χs M
applyTermsUnderTyBinders-⇑ᵗᵐ (bind B ∷ χs) M =
  trans
    (cong (applyTermsUnderTyBinders χs) (renameᵗᵐ-ext-suc-comm suc M))
    (applyTermsUnderTyBinders-⇑ᵗᵐ χs (⇑ᵗᵐ M))

applyTermsUnderTyBinders-++ :
  ∀ χs χs′ M →
  applyTermsUnderTyBinders (χs ++ χs′) M ≡
    applyTermsUnderTyBinders χs′ (applyTermsUnderTyBinders χs M)
applyTermsUnderTyBinders-++ [] χs′ M = refl
applyTermsUnderTyBinders-++ (χ ∷ χs) χs′ M =
  applyTermsUnderTyBinders-++ χs χs′ (applyTermUnderTyBinder χ M)

allKeep-applyTermsUnderTyBinders-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ M → applyTermsUnderTyBinders χs M ≡ M
allKeep-applyTermsUnderTyBinders-id all-[] M = refl
allKeep-applyTermsUnderTyBinders-id (all-keep keeps) M =
  allKeep-applyTermsUnderTyBinders-id keeps M

applyTermUnderTyBinder-preserves-Value :
  ∀ χ {V} →
  Value V →
  Value (applyTermUnderTyBinder χ V)
applyTermUnderTyBinder-preserves-Value keep vV = vV
applyTermUnderTyBinder-preserves-Value (bind A) vV =
  renameᵗᵐ-preserves-Value (extᵗ suc) vV

applyTermsUnderTyBinders-preserves-Value :
  ∀ χs {V} →
  Value V →
  Value (applyTermsUnderTyBinders χs V)
applyTermsUnderTyBinders-preserves-Value [] vV = vV
applyTermsUnderTyBinders-preserves-Value (χ ∷ χs) vV =
  applyTermsUnderTyBinders-preserves-Value χs
    (applyTermUnderTyBinder-preserves-Value χ vV)

applyTermUnderTyBinder-preserves-No• :
  ∀ χ {M} →
  No• M →
  No• (applyTermUnderTyBinder χ M)
applyTermUnderTyBinder-preserves-No• keep noM = noM
applyTermUnderTyBinder-preserves-No• (bind A) noM =
  renameᵗᵐ-preserves-No• (extᵗ suc) noM

applyTermsUnderTyBinders-preserves-No• :
  ∀ χs {M} →
  No• M →
  No• (applyTermsUnderTyBinders χs M)
applyTermsUnderTyBinders-preserves-No• [] noM = noM
applyTermsUnderTyBinders-preserves-No• (χ ∷ χs) noM =
  applyTermsUnderTyBinders-preserves-No• χs
    (applyTermUnderTyBinder-preserves-No• χ noM)

applyTerms-open :
  ∀ χs M α →
  applyTerms χs (M [ α ]ᵀ) ≡
    applyTermsUnderTyBinders χs M [ applyTyVars χs α ]ᵀ
applyTerms-open [] M α = refl
applyTerms-open (keep ∷ χs) M α = applyTerms-open χs M α
applyTerms-open (bind A ∷ χs) M α =
  trans
    (cong (applyTerms χs) (renameᵗᵐ-open-commute suc M α))
    (applyTerms-open χs (renameᵗᵐ (extᵗ suc) M) (suc α))

applyTerms-last-bind-open :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ M α →
  applyTerms (χs ++ bind A ∷ keeps) (M [ α ]ᵀ) ≡
    applyTerms χs (renameᵗᵐ (extᵗ suc) M [ suc α ]ᵀ)
applyTerms-last-bind-open χs A keeps keeps-ok M α =
  trans
    (applyTerms-last-bind χs A keeps keeps-ok (M [ α ]ᵀ))
    (trans
      (sym (applyTerms-⇑ᵗᵐ χs (M [ α ]ᵀ)))
      (cong (applyTerms χs) (renameᵗᵐ-open-commute suc M α)))

applyTerms-Λ :
  ∀ χs M →
  applyTerms χs (Λ M) ≡ Λ (applyTermsUnderTyBinders χs M)
applyTerms-Λ [] M = refl
applyTerms-Λ (keep ∷ χs) M = applyTerms-Λ χs M
applyTerms-Λ (bind A ∷ χs) M =
  applyTerms-Λ χs (renameᵗᵐ (extᵗ suc) M)

applyTerms-• :
  ∀ χs M →
  applyTerms χs (M •) ≡ applyTerms χs M •
applyTerms-• [] M = refl
applyTerms-• (keep ∷ χs) M = applyTerms-• χs M
applyTerms-• (bind A ∷ χs) M = applyTerms-• χs (⇑ᵗᵐ M)

applyCoercions : StoreChanges → Coercion → Coercion
applyCoercions [] c = c
applyCoercions (χ ∷ χs) c = applyCoercions χs (applyCoercion χ c)

applyCoercions-empty-id :
  ∀ χs →
  applyStores χs [] ≡ [] →
  ∀ c → applyCoercions χs c ≡ c
applyCoercions-empty-id [] eq c = refl
applyCoercions-empty-id (keep ∷ χs) eq c =
  applyCoercions-empty-id χs eq c
applyCoercions-empty-id (bind A ∷ χs) eq c =
  ⊥-elim (applyStores-cons≢[] χs eq)

applyCoercions-++ :
  ∀ χs χs′ c →
  applyCoercions (χs ++ χs′) c ≡
    applyCoercions χs′ (applyCoercions χs c)
applyCoercions-++ [] χs′ c = refl
applyCoercions-++ (χ ∷ χs) χs′ c =
  applyCoercions-++ χs χs′ (applyCoercion χ c)

allKeep-applyCoercions-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ c → applyCoercions χs c ≡ c
allKeep-applyCoercions-id all-[] c = refl
allKeep-applyCoercions-id (all-keep keeps) c =
  allKeep-applyCoercions-id keeps c

applyCoercions-last-bind :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ c →
  applyCoercions (χs ++ bind A ∷ keeps) c ≡ ⇑ᶜ (applyCoercions χs c)
applyCoercions-last-bind χs A keeps keeps-ok c =
  trans
    (applyCoercions-++ χs (bind A ∷ keeps) c)
    (allKeep-applyCoercions-id keeps-ok (⇑ᶜ (applyCoercions χs c)))

applyCoercions-⇑ᶜ :
  ∀ χs c →
  applyCoercions χs (⇑ᶜ c) ≡ ⇑ᶜ (applyCoercions χs c)
applyCoercions-⇑ᶜ [] c = refl
applyCoercions-⇑ᶜ (keep ∷ χs) c = applyCoercions-⇑ᶜ χs c
applyCoercions-⇑ᶜ (bind A ∷ χs) c = applyCoercions-⇑ᶜ χs (⇑ᶜ c)

applyCoercion-preserves-Inert :
  ∀ χ {c} →
  Inert c →
  Inert (applyCoercion χ c)
applyCoercion-preserves-Inert keep i = i
applyCoercion-preserves-Inert (bind A) i = renameᶜ-preserves-Inert suc i

applyCoercions-preserves-Inert :
  ∀ χs {c} →
  Inert c →
  Inert (applyCoercions χs c)
applyCoercions-preserves-Inert [] i = i
applyCoercions-preserves-Inert (χ ∷ χs) i =
  applyCoercions-preserves-Inert χs (applyCoercion-preserves-Inert χ i)

applyCoercion-dual :
  ∀ χ c →
  applyCoercion χ (- c) ≡ - applyCoercion χ c
applyCoercion-dual keep c = refl
applyCoercion-dual (bind A) c = renameᶜ-dual-normal suc c

applyCoercions-dual :
  ∀ χs c →
  applyCoercions χs (- c) ≡ - applyCoercions χs c
applyCoercions-dual [] c = refl
applyCoercions-dual (keep ∷ χs) c = applyCoercions-dual χs c
applyCoercions-dual (bind A ∷ χs) c
    rewrite renameᶜ-dual-normal suc c =
  applyCoercions-dual χs (⇑ᶜ c)

applyCoercionUnderTyBinders : StoreChanges → Coercion → Coercion
applyCoercionUnderTyBinders [] c = c
applyCoercionUnderTyBinders (χ ∷ χs) c =
  applyCoercionUnderTyBinders χs (applyCoercionUnderTyBinder χ c)

applyCoercionUnderTyBinder-⇑ᶜ :
  ∀ χ c →
  applyCoercionUnderTyBinder χ (⇑ᶜ c) ≡ ⇑ᶜ (applyCoercion χ c)
applyCoercionUnderTyBinder-⇑ᶜ keep c = refl
applyCoercionUnderTyBinder-⇑ᶜ (bind A) c = renameᶜ-ext-suc-suc c

applyCoercionUnderTyBinder-preserves-Inert :
  ∀ χ {c} →
  Inert c →
  Inert (applyCoercionUnderTyBinder χ c)
applyCoercionUnderTyBinder-preserves-Inert keep i = i
applyCoercionUnderTyBinder-preserves-Inert (bind A) i =
  renameᶜ-preserves-Inert (extᵗ suc) i

applyCoercionUnderTyBinders-preserves-Inert :
  ∀ χs {c} →
  Inert c →
  Inert (applyCoercionUnderTyBinders χs c)
applyCoercionUnderTyBinders-preserves-Inert [] i = i
applyCoercionUnderTyBinders-preserves-Inert (χ ∷ χs) i =
  applyCoercionUnderTyBinders-preserves-Inert χs
    (applyCoercionUnderTyBinder-preserves-Inert χ i)

applyCoercionUnderTyBinders-⇑ᶜ :
  ∀ χs c →
  applyCoercionUnderTyBinders χs (⇑ᶜ c) ≡ ⇑ᶜ (applyCoercions χs c)
applyCoercionUnderTyBinders-⇑ᶜ [] c = refl
applyCoercionUnderTyBinders-⇑ᶜ (χ ∷ χs) c =
  trans
    (cong (applyCoercionUnderTyBinders χs)
      (applyCoercionUnderTyBinder-⇑ᶜ χ c))
    (applyCoercionUnderTyBinders-⇑ᶜ χs (applyCoercion χ c))

applyCoercionUnderTyBinders-++ :
  ∀ χs χs′ c →
  applyCoercionUnderTyBinders (χs ++ χs′) c ≡
    applyCoercionUnderTyBinders χs′ (applyCoercionUnderTyBinders χs c)
applyCoercionUnderTyBinders-++ [] χs′ c = refl
applyCoercionUnderTyBinders-++ (χ ∷ χs) χs′ c =
  applyCoercionUnderTyBinders-++ χs χs′
    (applyCoercionUnderTyBinder χ c)

allKeep-applyCoercionUnderTyBinders-id :
  ∀ {χs} →
  AllKeep χs →
  ∀ c → applyCoercionUnderTyBinders χs c ≡ c
allKeep-applyCoercionUnderTyBinders-id all-[] c = refl
allKeep-applyCoercionUnderTyBinders-id (all-keep keeps) c =
  allKeep-applyCoercionUnderTyBinders-id keeps c

applyTerms-ν :
  ∀ χs A M c →
  applyTerms χs (ν A M c) ≡
    ν (applyTys χs A) (applyTerms χs M)
      (applyCoercionUnderTyBinders χs c)
applyTerms-ν [] A M c = refl
applyTerms-ν (keep ∷ χs) A M c = applyTerms-ν χs A M c
applyTerms-ν (bind B ∷ χs) A M c =
  applyTerms-ν χs (⇑ᵗ A) (⇑ᵗᵐ M) (renameᶜ (extᵗ suc) c)

applyCoercions-open :
  ∀ χs c α →
  applyCoercions χs (c [ α ]ᶜ) ≡
    applyCoercionUnderTyBinders χs c [ applyTyVars χs α ]ᶜ
applyCoercions-open [] c α = refl
applyCoercions-open (keep ∷ χs) c α = applyCoercions-open χs c α
applyCoercions-open (bind A ∷ χs) c α =
  trans
    (cong (applyCoercions χs) (renameᶜ-open-commute suc c α))
    (applyCoercions-open χs (renameᶜ (extᵗ suc) c) (suc α))

applyCoercions-last-bind-open :
  ∀ χs A keeps →
  AllKeep keeps →
  ∀ c α →
  applyCoercions (χs ++ bind A ∷ keeps) (c [ α ]ᶜ) ≡
    applyCoercions χs (renameᶜ (extᵗ suc) c [ suc α ]ᶜ)
applyCoercions-last-bind-open χs A keeps keeps-ok c α =
  trans
    (applyCoercions-last-bind χs A keeps keeps-ok (c [ α ]ᶜ))
    (trans
      (sym (applyCoercions-⇑ᶜ χs (c [ α ]ᶜ)))
      (cong (applyCoercions χs) (renameᶜ-open-commute suc c α)))

applyCoercions-∀ :
  ∀ χs c →
  applyCoercions χs (`∀ c) ≡ `∀ (applyCoercionUnderTyBinders χs c)
applyCoercions-∀ [] c = refl
applyCoercions-∀ (keep ∷ χs) c = applyCoercions-∀ χs c
applyCoercions-∀ (bind A ∷ χs) c =
  applyCoercions-∀ χs (renameᶜ (extᵗ suc) c)

applyCoercions-gen :
  ∀ χs A c →
  applyCoercions χs (gen A c) ≡
    gen (applyTys χs A) (applyCoercionUnderTyBinders χs c)
applyCoercions-gen [] A c = refl
applyCoercions-gen (keep ∷ χs) A c = applyCoercions-gen χs A c
applyCoercions-gen (bind B ∷ χs) A c =
  applyCoercions-gen χs (⇑ᵗ A) (renameᶜ (extᵗ suc) c)

applyCoercions-inst :
  ∀ χs A c →
  applyCoercions χs (inst A c) ≡
    inst (applyTys χs A) (applyCoercionUnderTyBinders χs c)
applyCoercions-inst [] A c = refl
applyCoercions-inst (keep ∷ χs) A c = applyCoercions-inst χs A c
applyCoercions-inst (bind B ∷ χs) A c =
  applyCoercions-inst χs (⇑ᵗ A) (renameᶜ (extᵗ suc) c)

applyTerms-cast :
  ∀ χs M c →
  applyTerms χs (M ⟨ c ⟩) ≡ applyTerms χs M ⟨ applyCoercions χs c ⟩
applyTerms-cast [] M c = refl
applyTerms-cast (keep ∷ χs) M c = applyTerms-cast χs M c
applyTerms-cast (bind A ∷ χs) M c =
  applyTerms-cast χs (⇑ᵗᵐ M) (⇑ᶜ c)

applyTerms-cast-dual :
  ∀ χs M c →
  applyTerms χs (M ⟨ - c ⟩) ≡
    applyTerms χs M ⟨ - applyCoercions χs c ⟩
applyTerms-cast-dual χs M c =
  trans (applyTerms-cast χs M (- c))
    (cong (λ d → applyTerms χs M ⟨ d ⟩) (applyCoercions-dual χs c))

------------------------------------------------------------------------
-- Multi-step reduction
------------------------------------------------------------------------

shiftStoreChange : StoreChange → StoreChange
shiftStoreChange keep = keep
shiftStoreChange (bind A) = bind (⇑ᵗ A)

shiftable-⇑ᵗᵐ :
  ∀ {χ M} →
  Shiftable χ M →
  Shiftable (shiftStoreChange χ) (⇑ᵗᵐ M)
shiftable-⇑ᵗᵐ shift-keep = shift-keep
shiftable-⇑ᵗᵐ (shift-bind noM) =
  shift-bind (renameᵗᵐ-preserves-No• suc noM)

＇-injective :
  ∀ {X Y : TyVar} →
  _≡_ {A = Ty} (＇ X) (＇ Y) →
  X ≡ Y
＇-injective refl = refl

‵-injective :
  ∀ {ι ι′ : Base} →
  _≡_ {A = Ty} (‵ ι) (‵ ι′) →
  ι ≡ ι′
‵-injective refl = refl

⇒-injective-left :
  ∀ {A B C D} →
  A ⇒ B ≡ C ⇒ D →
  A ≡ C
⇒-injective-left refl = refl

⇒-injective-right :
  ∀ {A B C D} →
  A ⇒ B ≡ C ⇒ D →
  B ≡ D
⇒-injective-right refl = refl

∀-injective :
  ∀ {A B : Ty} →
  `∀ A ≡ `∀ B →
  A ≡ B
∀-injective refl = refl

RenameInjective : Renameᵗ → Set
RenameInjective ρ = ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y

extᵗ-injective :
  ∀ {ρ} →
  RenameInjective ρ →
  RenameInjective (extᵗ ρ)
extᵗ-injective inj {zero} {zero} eq = refl
extᵗ-injective inj {zero} {suc Y} ()
extᵗ-injective inj {suc X} {zero} ()
extᵗ-injective inj {suc X} {suc Y} eq =
  cong suc (inj (suc-injective eq))

pred-β-step :
  ∀ {N V} →
  Value V →
  renameᵗᵐ predᵗ ((ƛ N) · V) —→ renameᵗᵐ predᵗ (N [ V ])
pred-β-step {N = N} {V = V} vV =
  subst
    (λ T → (ƛ renameᵗᵐ predᵗ N) · renameᵗᵐ predᵗ V —→ T)
    (sym (renameᵗᵐ-single-subst predᵗ N V))
    (β (renameᵗᵐ-preserves-Value predᵗ vV))

pred-β-Λ•-step :
  ∀ {V} →
  Value V →
  renameᵗᵐ predᵗ ((Λ V) •) —→ renameᵗᵐ predᵗ (V [ zero ]ᵀ)
pred-β-Λ•-step {V = V} vV =
  subst
    (λ T → (Λ renameᵗᵐ (extᵗ predᵗ) V) • —→ T)
    (sym (renameᵗᵐ-open-commute predᵗ V zero))
    (β-Λ• (renameᵗᵐ-preserves-Value (extᵗ predᵗ) vV))

pred-β-∀•-step :
  ∀ {V c} →
  Value V →
  renameᵗᵐ predᵗ ((V ⟨ `∀ c ⟩) •) —→
    renameᵗᵐ predᵗ ((V •) ⟨ c [ zero ]ᶜ ⟩)
pred-β-∀•-step {V = V} {c = c} vV =
  subst
    (λ d →
      (renameᵗᵐ predᵗ V ⟨ `∀ (renameᶜ (extᵗ predᵗ) c) ⟩) •
      —→ (renameᵗᵐ predᵗ V •) ⟨ d ⟩)
    (sym (renameᶜ-open-commute predᵗ c zero))
    (β-∀• (renameᵗᵐ-preserves-Value predᵗ vV))

pred-β-gen•-step :
  ∀ {A V c} →
  Value V →
  renameᵗᵐ predᵗ ((V ⟨ gen A c ⟩) •) —→
    renameᵗᵐ predᵗ (V ⟨ c [ zero ]ᶜ ⟩)
pred-β-gen•-step {A = A} {V = V} {c = c} vV =
  subst
    (λ d → (renameᵗᵐ predᵗ V
      ⟨ gen (renameᵗ predᵗ A) (renameᶜ (extᵗ predᵗ) c) ⟩) •
      —→ renameᵗᵐ predᵗ V ⟨ d ⟩)
    (sym (renameᶜ-open-commute predᵗ c zero))
    (β-gen• (renameᵗᵐ-preserves-Value predᵗ vV))

data PredPureStepView (M N : Term) : Set where
  pred-pure-step :
    renameᵗᵐ predᵗ M —→ renameᵗᵐ predᵗ N →
    PredPureStepView M N
  pred-pure-doomed :
    NoValueReachable (renameᵗᵐ predᵗ N) →
    PredPureStepView M N

pure-pred-step-view :
  ∀ {M N} →
  M —→ N →
  PredPureStepView M N
pure-pred-step-view δ-⊕ =
  pred-pure-step δ-⊕
pure-pred-step-view (β vV) =
  pred-pure-step (pred-β-step vV)
pure-pred-step-view (β-Λ• vV) =
  pred-pure-step (pred-β-Λ•-step vV)
pure-pred-step-view (β-∀• vV) =
  pred-pure-step (pred-β-∀•-step vV)
pure-pred-step-view (β-gen• vV) =
  pred-pure-step (pred-β-gen•-step vV)
pure-pred-step-view (β-id vV) =
  pred-pure-step (β-id (renameᵗᵐ-preserves-Value predᵗ vV))
pure-pred-step-view (β-seq vV) =
  pred-pure-step (β-seq (renameᵗᵐ-preserves-Value predᵗ vV))
pure-pred-step-view (β-↦ vV vW) =
  pred-pure-step
    (β-↦ (renameᵗᵐ-preserves-Value predᵗ vV)
          (renameᵗᵐ-preserves-Value predᵗ vW))
pure-pred-step-view (β-inst vV) =
  pred-pure-step (β-inst (renameᵗᵐ-preserves-Value predᵗ vV))
pure-pred-step-view (tag-untag-ok vV) =
  pred-pure-step (tag-untag-ok (renameᵗᵐ-preserves-Value predᵗ vV))
pure-pred-step-view (tag-untag-bad vV G≢H) =
  pred-pure-doomed blame-no-↠-value
pure-pred-step-view (seal-unseal vV) =
  pred-pure-step (seal-unseal (renameᵗᵐ-preserves-Value predᵗ vV))
pure-pred-step-view blame-·₁ =
  pred-pure-step blame-·₁
pure-pred-step-view (blame-·₂ vV) =
  pred-pure-step (blame-·₂ (renameᵗᵐ-preserves-Value predᵗ vV))
pure-pred-step-view blame-• =
  pred-pure-step blame-•
pure-pred-step-view blame-⟨⟩ =
  pred-pure-step blame-⟨⟩
pure-pred-step-view blame-⊕₁ =
  pred-pure-step blame-⊕₁
pure-pred-step-view (blame-⊕₂ vV) =
  pred-pure-step (blame-⊕₂ (renameᵗᵐ-preserves-Value predᵗ vV))

data PredKeepStepView (M N : Term) : Set where
  pred-keep-step :
    renameᵗᵐ predᵗ M —→[ keep ] renameᵗᵐ predᵗ N →
    PredKeepStepView M N
  pred-keep-doomed :
    NoValueReachable (renameᵗᵐ predᵗ N) →
    PredKeepStepView M N

keep-pred-step-view :
  ∀ {M N} →
  M —→[ keep ] N →
  PredKeepStepView M N
keep-pred-step-view (pure-step red)
    with pure-pred-step-view red
keep-pred-step-view (pure-step red) | pred-pure-step red′ =
  pred-keep-step (pure-step red′)
keep-pred-step-view (pure-step red) | pred-pure-doomed noN =
  pred-keep-doomed noN
keep-pred-step-view (ξ-·₁ red shiftM)
    with keep-pred-step-view red
keep-pred-step-view (ξ-·₁ red shiftM) | pred-keep-step red′ =
  pred-keep-step (ξ-·₁ red′ shift-keep)
keep-pred-step-view (ξ-·₁ red shiftM) | pred-keep-doomed noL =
  pred-keep-doomed (noValue-·₁ noL)
keep-pred-step-view (ξ-·₂ vV shiftV red)
    with keep-pred-step-view red
keep-pred-step-view (ξ-·₂ vV shiftV red) | pred-keep-step red′ =
  pred-keep-step
    (ξ-·₂ (renameᵗᵐ-preserves-Value predᵗ vV) shift-keep red′)
keep-pred-step-view (ξ-·₂ vV shiftV red) | pred-keep-doomed noM =
  pred-keep-doomed
    (noValue-·₂ (renameᵗᵐ-preserves-Value predᵗ vV) noM)
keep-pred-step-view (ξ-⟨⟩ red)
    with keep-pred-step-view red
keep-pred-step-view (ξ-⟨⟩ red) | pred-keep-step red′ =
  pred-keep-step (ξ-⟨⟩ red′)
keep-pred-step-view (ξ-⟨⟩ red) | pred-keep-doomed noM =
  pred-keep-doomed (noValue-cast noM)
keep-pred-step-view (ξ-ν red)
    with keep-pred-step-view red
keep-pred-step-view (ξ-ν red) | pred-keep-step red′ =
  pred-keep-step (ξ-ν red′)
keep-pred-step-view (ξ-ν red) | pred-keep-doomed noM =
  pred-keep-doomed (noValue-ν noM)
keep-pred-step-view blame-ν =
  pred-keep-step blame-ν
keep-pred-step-view (ξ-⊕₁ red shiftM)
    with keep-pred-step-view red
keep-pred-step-view (ξ-⊕₁ red shiftM) | pred-keep-step red′ =
  pred-keep-step (ξ-⊕₁ red′ shift-keep)
keep-pred-step-view (ξ-⊕₁ red shiftM) | pred-keep-doomed noL =
  pred-keep-doomed (noValue-⊕₁ noL)
keep-pred-step-view (ξ-⊕₂ vV shiftV red)
    with keep-pred-step-view red
keep-pred-step-view (ξ-⊕₂ vV shiftV red) | pred-keep-step red′ =
  pred-keep-step
    (ξ-⊕₂ (renameᵗᵐ-preserves-Value predᵗ vV) shift-keep red′)
keep-pred-step-view (ξ-⊕₂ vV shiftV red) | pred-keep-doomed noM =
  pred-keep-doomed
    (noValue-⊕₂ (renameᵗᵐ-preserves-Value predᵗ vV) noM)

pure-pred-↠-value :
  ∀ {M V χs} →
  AllKeep χs →
  M —↠[ χs ] V →
  Value V →
  renameᵗᵐ predᵗ M —↠[ χs ] renameᵗᵐ predᵗ V
pure-pred-↠-value all-[] ↠-refl vV =
  ↠-refl
pure-pred-↠-value (all-keep keeps) (↠-step red reds) vV
    with keep-pred-step-view red
pure-pred-↠-value (all-keep keeps) (↠-step red reds) vV
    | pred-keep-step red′ =
  ↠-step red′ (pure-pred-↠-value keeps reds vV)
pure-pred-↠-value (all-keep keeps) (↠-step red reds) vV
    | pred-keep-doomed noN =
  ⊥-elim
    (noN (pure-pred-↠-value keeps reds vV)
      (renameᵗᵐ-preserves-Value predᵗ vV))

pure-pred-↠-shifted-value :
  ∀ {M V χs} →
  AllKeep χs →
  ⇑ᵗᵐ M —↠[ χs ] V →
  Value V →
  M —↠[ χs ] renameᵗᵐ predᵗ V
pure-pred-↠-shifted-value {M = M} {V = V} {χs = χs} keeps reds vV =
  subst
    (λ L → L —↠[ χs ] renameᵗᵐ predᵗ V)
    (renameᵗᵐ-pred-suc M)
    (pure-pred-↠-value keeps reds vV)

allKeep-ν-no-value :
  ∀ {A M c χs V} →
  AllKeep χs →
  ν A M c —↠[ χs ] V →
  Value V →
  ⊥
allKeep-ν-no-value all-[] ↠-refl ()
allKeep-ν-no-value (all-keep keeps) (↠-step (ξ-ν red) reds) vV =
  allKeep-ν-no-value keeps reds vV
allKeep-ν-no-value (all-keep keeps) (↠-step blame-ν reds) vV =
  blame-no-↠-value reds vV

ν-bind-step-value-tail-inv :
  ∀ {A B L c Q keeps W} →
  ν A L c —→[ bind B ] Q →
  AllKeep keeps →
  Q —↠[ keeps ] W →
  Value W →
  Value L × No• L × B ≡ A
ν-bind-step-value-tail-inv (ν-step vL noL) keeps Q↠W vW =
  vL , noL , refl
ν-bind-step-value-tail-inv (ξ-ν red) keeps Q↠W vW =
  ⊥-elim (allKeep-ν-no-value keeps Q↠W vW)

renameᵗ-injective :
  ∀ {ρ A B} →
  RenameInjective ρ →
  renameᵗ ρ A ≡ renameᵗ ρ B →
  A ≡ B
renameᵗ-injective {A = ＇ X} {B = ＇ Y} inj eq =
  cong ＇_ (inj (＇-injective eq))
renameᵗ-injective {A = ＇ X} {B = ‵ ι} inj ()
renameᵗ-injective {A = ＇ X} {B = ★} inj ()
renameᵗ-injective {A = ＇ X} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ＇ X} {B = `∀ B} inj ()
renameᵗ-injective {A = ‵ ι} {B = ＇ X} inj ()
renameᵗ-injective {A = ‵ ι} {B = ‵ ι′} inj eq =
  cong ‵_ (‵-injective eq)
renameᵗ-injective {A = ‵ ι} {B = ★} inj ()
renameᵗ-injective {A = ‵ ι} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ‵ ι} {B = `∀ B} inj ()
renameᵗ-injective {A = ★} {B = ＇ X} inj ()
renameᵗ-injective {A = ★} {B = ‵ ι} inj ()
renameᵗ-injective {A = ★} {B = ★} inj eq = refl
renameᵗ-injective {A = ★} {B = B ⇒ C} inj ()
renameᵗ-injective {A = ★} {B = `∀ B} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ＇ X} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ‵ ι} inj ()
renameᵗ-injective {A = A ⇒ B} {B = ★} inj ()
renameᵗ-injective {A = A ⇒ B} {B = C ⇒ D} inj eq =
  cong₂ _⇒_
    (renameᵗ-injective inj (⇒-injective-left eq))
    (renameᵗ-injective inj (⇒-injective-right eq))
renameᵗ-injective {A = A ⇒ B} {B = `∀ C} inj ()
renameᵗ-injective {A = `∀ A} {B = ＇ X} inj ()
renameᵗ-injective {A = `∀ A} {B = ‵ ι} inj ()
renameᵗ-injective {A = `∀ A} {B = ★} inj ()
renameᵗ-injective {A = `∀ A} {B = B ⇒ C} inj ()
renameᵗ-injective {A = `∀ A} {B = `∀ B} inj eq =
  cong `∀ (renameᵗ-injective (extᵗ-injective inj) (∀-injective eq))

pure-rename-step-⇑ᵗᵐ :
  ∀ {M N} →
  M —→ N →
  ∃[ N′ ] (⇑ᵗᵐ M —→ N′)
pure-rename-step-⇑ᵗᵐ δ-⊕ =
  _ , δ-⊕
pure-rename-step-⇑ᵗᵐ (β vV) =
  _ , β (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-Λ• vV) =
  _ , β-Λ• (renameᵗᵐ-preserves-Value (extᵗ suc) vV)
pure-rename-step-⇑ᵗᵐ (β-∀• vV) =
  _ , β-∀• (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-gen• vV) =
  _ , β-gen• (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-id vV) =
  _ , β-id (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-seq vV) =
  _ , β-seq (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (β-↦ vV vW) =
  _ , β-↦ (renameᵗᵐ-preserves-Value suc vV)
           (renameᵗᵐ-preserves-Value suc vW)
pure-rename-step-⇑ᵗᵐ (β-inst vV) =
  _ , β-inst (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (tag-untag-ok vV) =
  _ , tag-untag-ok (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ (tag-untag-bad vV G≢H) =
  _ , tag-untag-bad (renameᵗᵐ-preserves-Value suc vV)
                    (λ eq → G≢H (renameᵗ-injective suc-injective eq))
pure-rename-step-⇑ᵗᵐ (seal-unseal vV) =
  _ , seal-unseal (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ blame-·₁ =
  _ , blame-·₁
pure-rename-step-⇑ᵗᵐ (blame-·₂ vV) =
  _ , blame-·₂ (renameᵗᵐ-preserves-Value suc vV)
pure-rename-step-⇑ᵗᵐ blame-• =
  _ , blame-•
pure-rename-step-⇑ᵗᵐ blame-⟨⟩ =
  _ , blame-⟨⟩
pure-rename-step-⇑ᵗᵐ blame-⊕₁ =
  _ , blame-⊕₁
pure-rename-step-⇑ᵗᵐ (blame-⊕₂ vV) =
  _ , blame-⊕₂ (renameᵗᵐ-preserves-Value suc vV)

type-rename-step-⇑ᵗᵐ-exact :
  ∀ {M N χ} →
  M —→[ χ ] N →
  ∃[ N′ ] (⇑ᵗᵐ M —→[ shiftStoreChange χ ] N′)
type-rename-step-⇑ᵗᵐ-exact (pure-step red)
    with pure-rename-step-⇑ᵗᵐ red
type-rename-step-⇑ᵗᵐ-exact (pure-step red)
    | N′ , red′ =
  N′ , pure-step red′
type-rename-step-⇑ᵗᵐ-exact (ν-step vV noV) =
  _ , ν-step (renameᵗᵐ-preserves-Value suc vV)
             (renameᵗᵐ-preserves-No• suc noV)
type-rename-step-⇑ᵗᵐ-exact (ξ-·₁ red shiftM)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-·₁ red shiftM)
    | L′ , red′ =
  _ , ξ-·₁ red′ (shiftable-⇑ᵗᵐ shiftM)
type-rename-step-⇑ᵗᵐ-exact (ξ-·₂ vV shiftV red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-·₂ vV shiftV red)
    | M′ , red′ =
  _ , ξ-·₂ (renameᵗᵐ-preserves-Value suc vV)
             (shiftable-⇑ᵗᵐ shiftV)
             red′
type-rename-step-⇑ᵗᵐ-exact (ξ-⟨⟩ red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-⟨⟩ red)
    | M′ , red′ =
  _ , ξ-⟨⟩ red′
type-rename-step-⇑ᵗᵐ-exact (ξ-ν red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-ν red)
    | L′ , red′ =
  _ , ξ-ν red′
type-rename-step-⇑ᵗᵐ-exact blame-ν =
  _ , blame-ν
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₁ red shiftM)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₁ red shiftM)
    | L′ , red′ =
  _ , ξ-⊕₁ red′ (shiftable-⇑ᵗᵐ shiftM)
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₂ vV shiftV red)
    with type-rename-step-⇑ᵗᵐ-exact red
type-rename-step-⇑ᵗᵐ-exact (ξ-⊕₂ vV shiftV red)
    | M′ , red′ =
  _ , ξ-⊕₂ (renameᵗᵐ-preserves-Value suc vV)
             (shiftable-⇑ᵗᵐ shiftV)
             red′

type-rename-step-⇑ᵗᵐ :
  ∀ {M N χ} →
  M —→[ χ ] N →
  ∃[ χ′ ] ∃[ N′ ] (⇑ᵗᵐ M —→[ χ′ ] N′)
type-rename-step-⇑ᵗᵐ red =
  shiftStoreChange _ , type-rename-step-⇑ᵗᵐ-exact red

↠-trans :
  ∀ {M N P χs χs′} →
  M —↠[ χs ] N →
  N —↠[ χs′ ] P →
  M —↠[ χs ++ χs′ ] P
↠-trans ↠-refl N↠P = N↠P
↠-trans (↠-step M→N N↠P) P↠Q = ↠-step M→N (↠-trans N↠P P↠Q)

↠-split-++ :
  ∀ {M W χs χs′} →
  M —↠[ χs ++ χs′ ] W →
  ∃[ P ] ((M —↠[ χs ] P) × (P —↠[ χs′ ] W))
↠-split-++ {χs = []} M↠W =
  _ , ↠-refl , M↠W
↠-split-++ {χs = χ ∷ χs} (↠-step M→N N↠W)
    with ↠-split-++ {χs = χs} N↠W
↠-split-++ {χs = χ ∷ χs} (↠-step M→N N↠W)
    | P , N↠P , P↠W =
  P , ↠-step M→N N↠P , P↠W

↠-split-last-bind :
  ∀ {M W χs A keeps} →
  M —↠[ χs ++ bind A ∷ keeps ] W →
  ∃[ P ] ∃[ Q ]
    ((M —↠[ χs ] P) × (P —→[ bind A ] Q) × (Q —↠[ keeps ] W))
↠-split-last-bind {χs = χs} M↠W
    with ↠-split-++ {χs = χs} M↠W
↠-split-last-bind {χs = χs} M↠W
    | P , M↠P , ↠-step P→Q Q↠W =
  P , _ , M↠P , P→Q , Q↠W

cast-↠ :
  ∀ {M N c χs} →
  M —↠[ χs ] N →
  M ⟨ c ⟩ —↠[ χs ] N ⟨ applyCoercions χs c ⟩
cast-↠ {c = c} ↠-refl = ↠-refl
cast-↠ {c = c} (↠-step {χ = χ} red reds) =
  ↠-step (ξ-⟨⟩ red) (cast-↠ {c = applyCoercion χ c} reds)

cast-dual-↠ :
  ∀ {M N c χs} →
  M —↠[ χs ] N →
  M ⟨ - c ⟩ —↠[ χs ] N ⟨ - applyCoercions χs c ⟩
cast-dual-↠ {M = M} {N = N} {c = c} {χs = χs} M↠N =
  subst (λ d → M ⟨ - c ⟩ —↠[ χs ] N ⟨ d ⟩)
        (applyCoercions-dual χs c)
        (cast-↠ {c = - c} M↠N)

ν-↠ :
  ∀ {M N A c χs} →
  M —↠[ χs ] N →
  ν A M c —↠[ χs ]
    ν (applyTys χs A) N (applyCoercionUnderTyBinders χs c)
ν-↠ {A = A} {c = c} ↠-refl = ↠-refl
ν-↠ {A = A} {c = c} (↠-step {χ = χ} red reds) =
  ↠-step (ξ-ν red)
    (ν-↠ {A = applyTy χ A} {c = applyCoercionUnderTyBinder χ c} reds)
