module strong.proof.ArrTyping where

-- Strong System F v8 — `arr` splits a typed conversion into two typed
-- conversions, one contravariant and one covariant.
--
-- The split is ELEMENTWISE, so the proof walks the conversion: a `↦`
-- element contributes its own two components, and an identity crossing
-- contributes ITSELF to the covariant side and its DUAL to the
-- contravariant one — which is why the two crossing rules were made
-- exact duals.  The components are appends, and `⧺-typing` types them;
-- `arr` then normalizes, and `preserve-↠` carries the typing along.

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.ConversionReduction
open import strong.proof.CompositionTyping using
  (⧺-typing; preserve-↠; conv-namefn)
open import strong.proof.Canonical using (conv-target)

private
  variable
    Sg : Store
    Ξ : Ctxᵗ
    Δ Δᵢ Δ₂ : Ctxᵗ
    A B A₀ B₀ A′ B′ : Ty
    c : Conv

-- `attach` splits along an append: the first block keeps its elements
-- and gives up its terminator.
attach-++ : ∀ (Ls es : List ConvElt) (T A : Ty)
  → attach (Ls ++ es) A ≡ (attach Ls T ⧺ attach es A)
attach-++ [] es T A = refl
attach-++ (ĉ ∷ Ls) es T A = cong (ĉ ∷ᶜ_) (attach-++ Ls es T A)

-- A rename cannot turn a non-arrow into an arrow.
shift-⇒-inv : ∀ X A {A₀ B₀} → renameᵗ (shiftAtᵗ X) A ≡ (A₀ ⇒ B₀)
  → Σ[ A₁ ∈ Ty ] Σ[ B₁ ∈ Ty ]
      ((A ≡ A₁ ⇒ B₁) × (renameᵗ (shiftAtᵗ X) A₁ ≡ A₀)
       × (renameᵗ (shiftAtᵗ X) B₁ ≡ B₀))
shift-⇒-inv X (A ⇒ B) refl = A , B , refl , refl , refl
shift-⇒-inv X (` Y) ()
shift-⇒-inv X `ℕ ()
shift-⇒-inv X `𝔹 ()
shift-⇒-inv X (`∀ A) ()

wf-⇒-inv : ∀ {Γ A B} → Γ ⊢ᵗ (A ⇒ B) → (Γ ⊢ᵗ A) × (Γ ⊢ᵗ B)
wf-⇒-inv (wf-⇒ a b) = a , b

------------------------------------------------------------------------
-- The renaming algebra for name assignments
------------------------------------------------------------------------
-- A crossing SHIFTS the names at and above its own, and the standard
-- renaming algebra carries well-formedness along: a map of lookups
-- extends under a binder, and `⊢ᵗ` follows it.

-- Two versions, because the two things a renaming can carry are now
-- genuinely different: an ASSIGNMENT (address and all), and mere
-- SCOPE, which is all `⊢ᵗ` reads.

Renamesᵗ : Renameᵗ → Ctxᵗ → Ctxᵗ → Set
Renamesᵗ ρ Γ Γ′ = ∀ {X α} → Γ ∋n X := α → Γ′ ∋n ρ X := α

Renamesˢ : Renameᵗ → List StackEnt → List StackEnt → Set
Renamesˢ ρ Ss Ss′ = ∀ {X} → Ss ∋ᵗ X → Ss′ ∋ᵗ ρ X

ext-renames : ∀ {ρ Γ Γ′} → Renamesᵗ ρ Γ Γ′
  → Renamesᵗ (extᵗ ρ) (bind ∷ stk Γ ∥ bas Γ) (bind ∷ stk Γ′ ∥ bas Γ′)
ext-renames r (n-skip-bind p) = n-skip-bind (r p)

ext-renamesˢ : ∀ {ρ Ss Ss′} → Renamesˢ ρ Ss Ss′
  → Renamesˢ (extᵗ ρ) (bind ∷ Ss) (bind ∷ Ss′)
ext-renamesˢ r t-here = t-here
ext-renamesˢ r (t-there p) = t-there (r p)

wf-ren : ∀ {ρ Ss Ss′ Bs Bs′ A} → Renamesˢ ρ Ss Ss′
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ renameᵗ ρ A
wf-ren r (wf-var n) = wf-var (r n)
wf-ren r wf-ℕ = wf-ℕ
wf-ren r wf-𝔹 = wf-𝔹
wf-ren r (wf-⇒ a b) = wf-⇒ (wf-ren r a) (wf-ren r b)
wf-ren r (wf-∀ a) = wf-∀ (wf-ren (ext-renamesˢ r) a)

-- Inserting the assignment a crossing introduces IS that shift.
pop-renames : ∀ {Γₑ Γᵢ X α} → Γₑ ▷ X := α ⇒ Γᵢ
  → Renamesᵗ (shiftAtᵗ X) Γᵢ Γₑ
pop-renames pop-here p = n-skip-asgn p
pop-renames (pop-bind q) = ext-renames (pop-renames q)

-- only the STACKS matter, so this needs no relation between the bases
pop-renamesˢ : ∀ {Γₑ Γᵢ X α} → Γₑ ▷ X := α ⇒ Γᵢ
  → Renamesˢ (shiftAtᵗ X) (stk Γᵢ) (stk Γₑ)
pop-renamesˢ pop-here p = t-there p
pop-renamesˢ (pop-bind q) = ext-renamesˢ (pop-renamesˢ q)

wf-shift : ∀ {Γₑ Γᵢ X α A} → Γₑ ▷ X := α ⇒ Γᵢ → Γᵢ ⊢ᵗ A
  → Γₑ ⊢ᵗ renameᵗ (shiftAtᵗ X) A
wf-shift q wf = wf-ren (pop-renamesˢ q) wf

------------------------------------------------------------------------
-- Reading the folds back
------------------------------------------------------------------------

attach-elts : ∀ c → attach (elts c) (target c) ≡ c
attach-elts (id A) = refl
attach-elts (ĉ ∷ᶜ c) = cong (ĉ ∷ᶜ_) (attach-elts c)

attach-elts-at : ∀ {c A} → target c ≡ A → attach (elts c) A ≡ c
attach-elts-at {c = c} refl = attach-elts c

-- the two shapes the `↦` case needs, each as ONE equation (a chain of
-- rewrites would abstract the subterm the next step wants)
attach-++ʳ : ∀ Ls (c : Conv) T {A} → target c ≡ A
  → attach (Ls ++ elts c) A ≡ (attach Ls T ⧺ c)
attach-++ʳ Ls c T {A} teq =
  trans (attach-++ Ls (elts c) T A) (cong (attach Ls T ⧺_) (attach-elts-at teq))

attach-++ˡ : ∀ (c : Conv) Rs B
  → attach (elts c ++ Rs) B ≡ (c ⧺ attach Rs B)
attach-++ˡ c Rs B =
  trans (attach-++ (elts c) Rs (target c) B)
        (cong (_⧺ attach Rs B) (attach-elts c))

consArr-inv : ∀ {ls rs q Ls Rs}
  → consArr (just ls) (just rs) q ≡ just (Ls , Rs)
  → Σ[ Ls′ ∈ List ConvElt ] Σ[ Rs′ ∈ List ConvElt ]
      ((q ≡ just (Ls′ , Rs′)) × (Ls ≡ Ls′ ++ ls) × (Rs ≡ rs ++ Rs′))
consArr-inv {q = just (Ls′ , Rs′)} refl = Ls′ , Rs′ , refl , refl , refl
consArr-inv {q = nothing} ()

------------------------------------------------------------------------
-- The elementwise split, before normalization
------------------------------------------------------------------------
-- The SOURCE is carried as an equation: the crossing rules state their
-- types as renames, which the unifier cannot match against an arrow.

arrElts-typing : ∀ {Sg Δᵢ Δ c S A₀ B₀ A′ B′ Ls Rs}
  → Sg ∣ Ξ ∣ Δᵢ ⊢ c ∶ S ⇝ (A′ ⇒ B′) ⊣ Δ
  → S ≡ (A₀ ⇒ B₀)
  → arrElts (elts c) ≡ just (Ls , Rs)
  → (Sg ∣ Ξ ∣ Δ ⊢ attach Ls A₀ ∶ A′ ⇝ A₀ ⊣ Δᵢ)
    × (Sg ∣ Ξ ∣ Δᵢ ⊢ attach Rs B′ ∶ B₀ ⇝ B′ ⊣ Δ)

arrElts-typing (conv-id wf) refl refl with wf-⇒-inv wf
arrElts-typing (conv-id wf) refl refl | wfA , wfB = conv-id wfA , conv-id wfB

-- a `↦` element contributes its own two components
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-fun {s = s} {C = C} {t = t} {D = D} ⊢s ⊢t) tl) refl eq
  with consArr-inv eq
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-fun {s = s} {C = C} {t = t} {D = D} ⊢s ⊢t) tl) refl eq
  | Ls′ , Rs′ , eq′ , refl , refl with arrElts-typing tl refl eq′
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-fun {s = s} {C = C} {t = t} {D = D} ⊢s ⊢t) tl) refl eq
  | Ls′ , Rs′ , eq′ , refl , refl | ih₁ , ih₂
  rewrite attach-++ʳ Ls′ s C (conv-target ⊢s)
        | attach-++ˡ t Rs′ B′ =
  ⧺-typing ih₁ ⊢s , ⧺-typing ⊢t ih₂

-- a `hide`: its DUAL joins the contravariant side, itself the covariant
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-hide {α = α} {A = A} {X = X} sc wf p na) tl) refl eq
  with wf-⇒-inv wf | consArr-inv eq
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-hide {α = α} {A = A} {X = X} sc wf p na) tl) refl eq
  | wfA , wfB | Ls′ , Rs′ , eq′ , refl , refl
  with arrElts-typing tl refl eq′
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-hide {α = α} {A = A} {X = X} sc wf p na) tl) refl eq
  | wfA , wfB | Ls′ , Rs′ , eq′ , refl , refl | ih₁ , ih₂
  rewrite attach-++ Ls′ (show X α ∷ []) A₀ A₀ =
  ⧺-typing ih₁ (conv-cons (conv-show sc wfA p na) (conv-id wfA))
  , conv-cons (conv-hide sc wfB p na) ih₂

-- a `show`: its DUAL joins the contravariant side.  The source is a
-- SHIFT, so the arrow is recovered by inversion.
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  with shift-⇒-inv X A seq
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  | A₁ , B₁ , refl , refl , refl
  with wf-⇒-inv wf | consArr-inv eq
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  | A₁ , B₁ , refl , refl , refl | wfA , wfB | Ls′ , Rs′ , eq′ , refl , refl
  with arrElts-typing tl refl eq′
arrElts-typing {A₀ = A₀} {B′ = B′}
  (conv-cons (conv-show {α = α} {A = A} {X = X} sc wf p na) tl) seq eq
  | A₁ , B₁ , refl , refl , refl | wfA , wfB | Ls′ , Rs′ , eq′ , refl , refl
  | ih₁ , ih₂
  rewrite attach-++ Ls′ (hide X α ∷ []) A₁ A₁ =
  ⧺-typing ih₁ (conv-cons (conv-hide sc wfA p na) (conv-id wfA))
  , conv-cons (conv-show sc wfB p na) ih₂

-- the renaming elements and `all` are not view-accepted
arrElts-typing (conv-cons (conv-seal rep rd nm p) tl) refl ()
arrElts-typing (conv-cons (conv-unseal rep rd nm p na) tl) () eq
arrElts-typing (conv-cons (conv-all s′) tl) () eq

------------------------------------------------------------------------
-- `arr` itself: the components are normalized, so the typing travels
-- along the normalization trace
------------------------------------------------------------------------

arr-inv : ∀ {A₀ c c₁ c₂} → arr A₀ c ≡ just (c₁ , c₂)
  → Σ[ Ls ∈ List ConvElt ] Σ[ Rs ∈ List ConvElt ] Σ[ C ∈ Ty ] Σ[ D ∈ Ty ]
      ((arrElts (elts c) ≡ just (Ls , Rs)) × (target c ≡ C ⇒ D)
       × (c₁ ≡ normalize (attach Ls A₀)) × (c₂ ≡ normalize (attach Rs D)))
arr-inv {A₀ = A₀} {c = c} eq with arrElts (elts c) | target c
arr-inv {A₀ = A₀} {c = c} refl | just (Ls , Rs) | C ⇒ D =
  Ls , Rs , C , D , refl , refl , refl , refl
arr-inv {A₀ = A₀} {c = c} () | just p | ` X
arr-inv {A₀ = A₀} {c = c} () | just p | `ℕ
arr-inv {A₀ = A₀} {c = c} () | just p | `𝔹
arr-inv {A₀ = A₀} {c = c} () | just p | `∀ B
arr-inv {A₀ = A₀} {c = c} () | nothing | _

arr-typing : ∀ {Sg Δᵢ Δ c A₀ B₀ A′ B′ c₁ c₂}
  → NameFn Δ
  → Sg ∣ Ξ ∣ Δᵢ ⊢ c ∶ (A₀ ⇒ B₀) ⇝ (A′ ⇒ B′) ⊣ Δ
  → arr A₀ c ≡ just (c₁ , c₂)
  → (Sg ∣ Ξ ∣ Δ ⊢ c₁ ∶ A′ ⇝ A₀ ⊣ Δᵢ) × (Sg ∣ Ξ ∣ Δᵢ ⊢ c₂ ∶ B₀ ⇝ B′ ⊣ Δ)
    × NF c₁ × NF c₂
arr-typing {c = c} nf conv eq with arr-inv {c = c} eq
arr-typing {c = c} nf conv eq | Ls , Rs , C , D , eqE , teq , refl , refl
  with trans (sym teq) (conv-target conv)
arr-typing {c = c} nf conv eq | Ls , Rs , C , D , eqE , teq , refl , refl | refl
  with arrElts-typing conv refl eqE
arr-typing {c = c} {A₀ = A₀} {B′ = B′} nf conv eq
  | Ls , Rs , C , D , eqE , teq , refl , refl | refl | ty₁ , ty₂ =
    preserve-↠ (conv-namefn conv nf) ty₁ (normalize-↠ (attach Ls A₀))
  , preserve-↠ nf ty₂ (normalize-↠ (attach Rs B′))
  , normalize-NF (attach Ls A₀)
  , normalize-NF (attach Rs B′)
