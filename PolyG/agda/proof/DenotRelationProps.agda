module proof.DenotRelationProps where

-- File Charter:
--   * Basic facts about the joint-list relations of
--     proof/DenotRelation.agda (reflection ▹, the left program more
--     precise; preservation ◃):
--       - membership characterizations of the list extractors (untagᴸ,
--         unsealᴸ, argsAt, resultsAt, bodiesAt, valuesAt), their sizes,
--         and selection of a sublist from membership proofs (select);
--       - closure under subsets of the list (▹-⊆, ◃-⊆; in the notation
--         ▹-sub⊆, ◃-sub⊆), which gives fuel irrelevance (▹-fuel, ◃-fuel)
--         and closure under sublists (▹-sublist, ◃-sublist);
--       - monotonicity in the set side (▹-mono, ◃-mono) and Kripke
--         monotonicity in the world (▹-kripke, ◃-kripke);
--       - a related nonempty list forces its set to be nonempty (▹-conv,
--         ◃-conv, ▹ᶜ-conv, ◃ᶜ-conv), and uniformity against a consistent
--         set (▹-bool, ◃-bool: one boolean; ▹-tag, ◃-tag: one tag);
--       - the substitution and closing lemmas (▹-subst, ◃-subst, with
--         ▹-substᵖ, ◃-substᵖ, ▹-close, ◃-close, gp-▹, gp-◃);
--       - compatibility with bind and application (bind▹, bind◃, app▹,
--         app◃), reducing sets to finite lists by finite support.
--   * The relations are defined at a fuel k; the notation
--     W ∣ θ ⊢ p ⊢ L ▹ D′ uses fuel suc (sizeᴸ L).  The subset lemma is
--     stated for arbitrary fuels and proved by induction on a bound on
--     the sizes of the elements.
--   * Facts about casts and the model operators:
--     proof/DenotCastProps.agda.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Sublist.Propositional
  using ([]; _∷_; _∷ʳ_) renaming (_⊆_ to _⊑ˢ_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; <-≤-trans; ≤-<-trans; m≤m+n; m≤n+m; +-mono-≤;
         +-mono-<-≤; n≤1+n; <⇒≤)
  renaming (_≟_ to _≟ℕ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to tt₁)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Types
open import Terms using (Dir; up; down; flip)
open import GraphModel
open import Denotation
open import proof.DenotRelation
open import proof.DenotCastProps

open Equivalence using (to; from)

------------------------------------------------------------------------
-- Sizes
------------------------------------------------------------------------

sizeᵛ-pos : ∀ v → 0 < sizeᵛ v
sizeᵛ-pos vtrue = s≤s z≤n
sizeᵛ-pos vfalse = s≤s z≤n
sizeᵛ-pos (sealᵛ σ u) = s≤s z≤n
sizeᵛ-pos (injᵛ G u) = s≤s z≤n
sizeᵛ-pos (U ⟼ r at m) = s≤s z≤n
sizeᵛ-pos (σ ⟼∀ r) = s≤s z≤n
sizeᵛ-pos νλ = s≤s z≤n
sizeᵛ-pos ν∀ = s≤s z≤n

∈-size : ∀ {v L} → v ⋵ L → sizeᵛ v ≤ sizeᴸ L
∈-size {v} {x ∷ L} (here refl) = m≤m+n (sizeᵛ v) (sizeᴸ L)
∈-size {v} {x ∷ L} (there v∈) =
  ≤-trans (∈-size v∈) (m≤n+m (sizeᴸ L) (sizeᵛ x))

∈-sizeᴿ : ∀ {r Rs} → r ⋵ Rs → sizeᴿ r ≤ sizeᴿᴸ Rs
∈-sizeᴿ {r} {x ∷ Rs} (here refl) = m≤m+n (sizeᴿ r) (sizeᴿᴸ Rs)
∈-sizeᴿ {r} {x ∷ Rs} (there r∈) =
  ≤-trans (∈-sizeᴿ r∈) (m≤n+m (sizeᴿᴸ Rs) (sizeᴿ x))

sub-size : ∀ {L₀ L} → L₀ ⊑ˢ L → sizeᴸ L₀ ≤ sizeᴸ L
sub-size [] = z≤n
sub-size (_∷ʳ_ {xs = L₀} {ys = L} y s) =
  ≤-trans (sub-size s) (m≤n+m (sizeᴸ L) (sizeᵛ y))
sub-size (_∷_ {x = x} refl s) = +-mono-≤ (≤-refl {sizeᵛ x}) (sub-size s)

sub-mem : ∀ {L₀ L} → L₀ ⊑ˢ L → mem L₀ ⊆ mem L
sub-mem (y ∷ʳ s) v v∈ = there (sub-mem s v v∈)
sub-mem (refl ∷ s) v (here refl) = here refl
sub-mem (refl ∷ s) v (there v∈) = there (sub-mem s v v∈)

-- a head that contributes c to the extracted size, with c < sizeᵛ v
head-< : ∀ {c a b x} → c < x → a ≤ b → c + a < x + b
head-< = +-mono-<-≤

-- the sizes of the extractors
untag-< : ∀ G v L → sizeᴸ (untagᴸ G (v ∷ L)) < sizeᴸ (v ∷ L)
untag-≤ : ∀ G L → sizeᴸ (untagᴸ G L) ≤ sizeᴸ L
untag-< G (injᵛ H u) L with G ≟G H
untag-< G (injᵛ H u) L | yes _ =
  head-< {x = suc (sizeᵛ u)} ≤-refl (untag-≤ G L)
untag-< G (injᵛ H u) L | no _ =
  head-< {c = 0} {x = suc (sizeᵛ u)} (s≤s z≤n) (untag-≤ G L)
untag-< G vtrue L = head-< {c = 0} (s≤s z≤n) (untag-≤ G L)
untag-< G vfalse L = head-< {c = 0} (s≤s z≤n) (untag-≤ G L)
untag-< G (sealᵛ σ u) L = head-< {c = 0} (s≤s z≤n) (untag-≤ G L)
untag-< G (U ⟼ r at m) L = head-< {c = 0} (s≤s z≤n) (untag-≤ G L)
untag-< G (σ ⟼∀ r) L = head-< {c = 0} (s≤s z≤n) (untag-≤ G L)
untag-< G νλ L = head-< {c = 0} (s≤s z≤n) (untag-≤ G L)
untag-< G ν∀ L = head-< {c = 0} (s≤s z≤n) (untag-≤ G L)
untag-≤ G [] = z≤n
untag-≤ G (v ∷ L) = <⇒≤ (untag-< G v L)

unseal-< : ∀ σ v L → sizeᴸ (unsealᴸ σ (v ∷ L)) < sizeᴸ (v ∷ L)
unseal-≤ : ∀ σ L → sizeᴸ (unsealᴸ σ L) ≤ sizeᴸ L
unseal-< σ (sealᵛ σ′ u) L with σ ≟ℕ σ′
unseal-< σ (sealᵛ σ′ u) L | yes _ =
  head-< {x = suc (sizeᵛ u)} ≤-refl (unseal-≤ σ L)
unseal-< σ (sealᵛ σ′ u) L | no _ =
  head-< {c = 0} {x = suc (sizeᵛ u)} (s≤s z≤n) (unseal-≤ σ L)
unseal-< σ vtrue L = head-< {c = 0} (s≤s z≤n) (unseal-≤ σ L)
unseal-< σ vfalse L = head-< {c = 0} (s≤s z≤n) (unseal-≤ σ L)
unseal-< σ (injᵛ G u) L = head-< {c = 0} (s≤s z≤n) (unseal-≤ σ L)
unseal-< σ (U ⟼ r at m) L = head-< {c = 0} (s≤s z≤n) (unseal-≤ σ L)
unseal-< σ (σ′ ⟼∀ r) L = head-< {c = 0} (s≤s z≤n) (unseal-≤ σ L)
unseal-< σ νλ L = head-< {c = 0} (s≤s z≤n) (unseal-≤ σ L)
unseal-< σ ν∀ L = head-< {c = 0} (s≤s z≤n) (unseal-≤ σ L)
unseal-≤ σ [] = z≤n
unseal-≤ σ (v ∷ L) = <⇒≤ (unseal-< σ v L)

sizeᴸ-++ : ∀ U V → sizeᴸ (U ++ V) ≡ sizeᴸ U + sizeᴸ V
sizeᴸ-++ [] V = refl
sizeᴸ-++ (u ∷ U) V rewrite sizeᴸ-++ U V = sym (+-assoc′ (sizeᵛ u))
  where
  +-assoc′ : ∀ a {b c} → (a + b) + c ≡ a + (b + c)
  +-assoc′ zero = refl
  +-assoc′ (suc a) = cong suc (+-assoc′ a)

args-< : ∀ m v L → sizeᴸ (argsAt m (v ∷ L)) < sizeᴸ (v ∷ L)
args-≤ : ∀ m L → sizeᴸ (argsAt m L) ≤ sizeᴸ L
args-< m (U ⟼ r at m′) L with m ≟ℕ m′
args-< m (U ⟼ r at m′) L | yes _
  rewrite sizeᴸ-++ U (argsAt m L) =
  head-< {x = suc (sizeᴸ U + sizeᴿ r)} (s≤s (m≤m+n (sizeᴸ U) (sizeᴿ r)))
    (args-≤ m L)
args-< m (U ⟼ r at m′) L | no _ =
  head-< {c = 0} {x = suc (sizeᴸ U + sizeᴿ r)} (s≤s z≤n) (args-≤ m L)
args-< m vtrue L = head-< {c = 0} (s≤s z≤n) (args-≤ m L)
args-< m vfalse L = head-< {c = 0} (s≤s z≤n) (args-≤ m L)
args-< m (sealᵛ σ u) L = head-< {c = 0} (s≤s z≤n) (args-≤ m L)
args-< m (injᵛ G u) L = head-< {c = 0} (s≤s z≤n) (args-≤ m L)
args-< m (σ ⟼∀ r) L = head-< {c = 0} (s≤s z≤n) (args-≤ m L)
args-< m νλ L = head-< {c = 0} (s≤s z≤n) (args-≤ m L)
args-< m ν∀ L = head-< {c = 0} (s≤s z≤n) (args-≤ m L)
args-≤ m [] = z≤n
args-≤ m (v ∷ L) = <⇒≤ (args-< m v L)

results-< : ∀ m v L → sizeᴿᴸ (resultsAt m (v ∷ L)) < sizeᴸ (v ∷ L)
results-≤ : ∀ m L → sizeᴿᴸ (resultsAt m L) ≤ sizeᴸ L
results-< m (U ⟼ r at m′) L with m ≟ℕ m′
results-< m (U ⟼ r at m′) L | yes _ =
  head-< {x = suc (sizeᴸ U + sizeᴿ r)} (s≤s (m≤n+m (sizeᴿ r) (sizeᴸ U)))
    (results-≤ m L)
results-< m (U ⟼ r at m′) L | no _ =
  head-< {c = 0} {x = suc (sizeᴸ U + sizeᴿ r)} (s≤s z≤n) (results-≤ m L)
results-< m vtrue L = head-< {c = 0} (s≤s z≤n) (results-≤ m L)
results-< m vfalse L = head-< {c = 0} (s≤s z≤n) (results-≤ m L)
results-< m (sealᵛ σ u) L = head-< {c = 0} (s≤s z≤n) (results-≤ m L)
results-< m (injᵛ G u) L = head-< {c = 0} (s≤s z≤n) (results-≤ m L)
results-< m (σ ⟼∀ r) L = head-< {c = 0} (s≤s z≤n) (results-≤ m L)
results-< m νλ L = head-< {c = 0} (s≤s z≤n) (results-≤ m L)
results-< m ν∀ L = head-< {c = 0} (s≤s z≤n) (results-≤ m L)
results-≤ m [] = z≤n
results-≤ m (v ∷ L) = <⇒≤ (results-< m v L)

bodies-< : ∀ σ v L → sizeᴿᴸ (bodiesAt σ (v ∷ L)) < sizeᴸ (v ∷ L)
bodies-≤ : ∀ σ L → sizeᴿᴸ (bodiesAt σ L) ≤ sizeᴸ L
bodies-< σ (σ′ ⟼∀ r) L with σ ≟ℕ σ′
bodies-< σ (σ′ ⟼∀ r) L | yes _ =
  head-< {x = suc (sizeᴿ r)} ≤-refl (bodies-≤ σ L)
bodies-< σ (σ′ ⟼∀ r) L | no _ =
  head-< {c = 0} {x = suc (sizeᴿ r)} (s≤s z≤n) (bodies-≤ σ L)
bodies-< σ vtrue L = head-< {c = 0} (s≤s z≤n) (bodies-≤ σ L)
bodies-< σ vfalse L = head-< {c = 0} (s≤s z≤n) (bodies-≤ σ L)
bodies-< σ (sealᵛ σ′ u) L = head-< {c = 0} (s≤s z≤n) (bodies-≤ σ L)
bodies-< σ (injᵛ G u) L = head-< {c = 0} (s≤s z≤n) (bodies-≤ σ L)
bodies-< σ (U ⟼ r at m) L = head-< {c = 0} (s≤s z≤n) (bodies-≤ σ L)
bodies-< σ νλ L = head-< {c = 0} (s≤s z≤n) (bodies-≤ σ L)
bodies-< σ ν∀ L = head-< {c = 0} (s≤s z≤n) (bodies-≤ σ L)
bodies-≤ σ [] = z≤n
bodies-≤ σ (v ∷ L) = <⇒≤ (bodies-< σ v L)

values-≤ : ∀ m Rs → sizeᴸ (valuesAt m Rs) ≤ sizeᴿᴸ Rs
values-≤ m [] = z≤n
values-≤ m (ret v m′ ∷ Rs) with m ≟ℕ m′
values-≤ m (ret v m′ ∷ Rs) | yes _ =
  +-mono-≤ (≤-refl {sizeᵛ v}) (values-≤ m Rs)
values-≤ m (ret v m′ ∷ Rs) | no _ =
  ≤-trans (values-≤ m Rs) (m≤n+m (sizeᴿᴸ Rs) (sizeᵛ v))
values-≤ m (err ∷ Rs) = ≤-trans (values-≤ m Rs) (n≤1+n (sizeᴿᴸ Rs))

-- the arguments and results of a sublist of a nonempty list are smaller
args-sub-< : ∀ m {L₀} v L → L₀ ⊑ˢ (v ∷ L)
  → sizeᴸ (argsAt m L₀) < sizeᴸ (v ∷ L)
args-sub-< m {[]} v L s = +-mono-<-≤ (sizeᵛ-pos v) z≤n
args-sub-< m {w ∷ L₀} v L s = <-≤-trans (args-< m w L₀) (sub-size s)

results-sub-< : ∀ m {L₀} v L → L₀ ⊑ˢ (v ∷ L)
  → sizeᴿᴸ (resultsAt m L₀) < sizeᴸ (v ∷ L)
results-sub-< m {[]} v L s = +-mono-<-≤ (sizeᵛ-pos v) z≤n
results-sub-< m {w ∷ L₀} v L s =
  <-≤-trans (results-< m w L₀) (sub-size s)

------------------------------------------------------------------------
-- Membership in the extracted lists
------------------------------------------------------------------------

untag-∈⁺ : ∀ {G u L} → injᵛ G u ⋵ L → u ⋵ untagᴸ G L
untag-∈⁺ {G} {u} {injᵛ H w ∷ L} p with G ≟G H
untag-∈⁺ {G} {u} {injᵛ H w ∷ L} (here refl) | yes _ = here refl
untag-∈⁺ {G} {u} {injᵛ H w ∷ L} (there p) | yes _ = there (untag-∈⁺ p)
untag-∈⁺ {G} {u} {injᵛ H w ∷ L} (here refl) | no G≢ = ⊥-elim (G≢ refl)
untag-∈⁺ {G} {u} {injᵛ H w ∷ L} (there p) | no _ = untag-∈⁺ p
untag-∈⁺ {L = vtrue ∷ L} (there p) = untag-∈⁺ p
untag-∈⁺ {L = vfalse ∷ L} (there p) = untag-∈⁺ p
untag-∈⁺ {L = sealᵛ σ w ∷ L} (there p) = untag-∈⁺ p
untag-∈⁺ {L = (U ⟼ r at m) ∷ L} (there p) = untag-∈⁺ p
untag-∈⁺ {L = (σ ⟼∀ r) ∷ L} (there p) = untag-∈⁺ p
untag-∈⁺ {L = νλ ∷ L} (there p) = untag-∈⁺ p
untag-∈⁺ {L = ν∀ ∷ L} (there p) = untag-∈⁺ p

untag-∈⁻ : ∀ {G u} L → u ⋵ untagᴸ G L → injᵛ G u ⋵ L
untag-∈⁻ {G} (injᵛ H w ∷ L) p with G ≟G H
untag-∈⁻ {G} (injᵛ H w ∷ L) (here refl) | yes refl = here refl
untag-∈⁻ {G} (injᵛ H w ∷ L) (there p) | yes refl = there (untag-∈⁻ L p)
untag-∈⁻ {G} (injᵛ H w ∷ L) p | no _ = there (untag-∈⁻ L p)
untag-∈⁻ (vtrue ∷ L) p = there (untag-∈⁻ L p)
untag-∈⁻ (vfalse ∷ L) p = there (untag-∈⁻ L p)
untag-∈⁻ (sealᵛ σ w ∷ L) p = there (untag-∈⁻ L p)
untag-∈⁻ ((U ⟼ r at m) ∷ L) p = there (untag-∈⁻ L p)
untag-∈⁻ ((σ ⟼∀ r) ∷ L) p = there (untag-∈⁻ L p)
untag-∈⁻ (νλ ∷ L) p = there (untag-∈⁻ L p)
untag-∈⁻ (ν∀ ∷ L) p = there (untag-∈⁻ L p)

unseal-∈⁺ : ∀ {σ u L} → sealᵛ σ u ⋵ L → u ⋵ unsealᴸ σ L
unseal-∈⁺ {σ} {u} {sealᵛ σ′ w ∷ L} p with σ ≟ℕ σ′
unseal-∈⁺ {σ} {u} {sealᵛ σ′ w ∷ L} (here refl) | yes _ = here refl
unseal-∈⁺ {σ} {u} {sealᵛ σ′ w ∷ L} (there p) | yes _ = there (unseal-∈⁺ p)
unseal-∈⁺ {σ} {u} {sealᵛ σ′ w ∷ L} (here refl) | no σ≢ = ⊥-elim (σ≢ refl)
unseal-∈⁺ {σ} {u} {sealᵛ σ′ w ∷ L} (there p) | no _ = unseal-∈⁺ p
unseal-∈⁺ {L = vtrue ∷ L} (there p) = unseal-∈⁺ p
unseal-∈⁺ {L = vfalse ∷ L} (there p) = unseal-∈⁺ p
unseal-∈⁺ {L = injᵛ G w ∷ L} (there p) = unseal-∈⁺ p
unseal-∈⁺ {L = (U ⟼ r at m) ∷ L} (there p) = unseal-∈⁺ p
unseal-∈⁺ {L = (σ′ ⟼∀ r) ∷ L} (there p) = unseal-∈⁺ p
unseal-∈⁺ {L = νλ ∷ L} (there p) = unseal-∈⁺ p
unseal-∈⁺ {L = ν∀ ∷ L} (there p) = unseal-∈⁺ p

unseal-∈⁻ : ∀ {σ u} L → u ⋵ unsealᴸ σ L → sealᵛ σ u ⋵ L
unseal-∈⁻ {σ} (sealᵛ σ′ w ∷ L) p with σ ≟ℕ σ′
unseal-∈⁻ {σ} (sealᵛ σ′ w ∷ L) (here refl) | yes refl = here refl
unseal-∈⁻ {σ} (sealᵛ σ′ w ∷ L) (there p) | yes refl =
  there (unseal-∈⁻ L p)
unseal-∈⁻ {σ} (sealᵛ σ′ w ∷ L) p | no _ = there (unseal-∈⁻ L p)
unseal-∈⁻ (vtrue ∷ L) p = there (unseal-∈⁻ L p)
unseal-∈⁻ (vfalse ∷ L) p = there (unseal-∈⁻ L p)
unseal-∈⁻ (injᵛ G w ∷ L) p = there (unseal-∈⁻ L p)
unseal-∈⁻ ((U ⟼ r at m) ∷ L) p = there (unseal-∈⁻ L p)
unseal-∈⁻ ((σ′ ⟼∀ r) ∷ L) p = there (unseal-∈⁻ L p)
unseal-∈⁻ (νλ ∷ L) p = there (unseal-∈⁻ L p)
unseal-∈⁻ (ν∀ ∷ L) p = there (unseal-∈⁻ L p)

args-∈⁺ : ∀ {m U r u L} → (U ⟼ r at m) ⋵ L → u ⋵ U → u ⋵ argsAt m L
args-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} p u∈ with m ≟ℕ m′
args-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (here refl) u∈ | yes _ = ∈-++⁺ˡ u∈
args-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (there p) u∈ | yes _ =
  ∈-++⁺ʳ V (args-∈⁺ p u∈)
args-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (here refl) u∈ | no m≢ =
  ⊥-elim (m≢ refl)
args-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (there p) u∈ | no _ = args-∈⁺ p u∈
args-∈⁺ {L = vtrue ∷ L} (there p) u∈ = args-∈⁺ p u∈
args-∈⁺ {L = vfalse ∷ L} (there p) u∈ = args-∈⁺ p u∈
args-∈⁺ {L = sealᵛ σ w ∷ L} (there p) u∈ = args-∈⁺ p u∈
args-∈⁺ {L = injᵛ G w ∷ L} (there p) u∈ = args-∈⁺ p u∈
args-∈⁺ {L = (σ ⟼∀ s) ∷ L} (there p) u∈ = args-∈⁺ p u∈
args-∈⁺ {L = νλ ∷ L} (there p) u∈ = args-∈⁺ p u∈
args-∈⁺ {L = ν∀ ∷ L} (there p) u∈ = args-∈⁺ p u∈

args-∈⁻ : ∀ {m u} L → u ⋵ argsAt m L
  → Σ[ U ∈ List Val ] Σ[ r ∈ Res ] ((U ⟼ r at m) ⋵ L × u ⋵ U)
args-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p with m ≟ℕ m′
args-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | yes refl with ∈-++⁻ V p
args-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | yes refl | inj₁ u∈ =
  V , s , here refl , u∈
args-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | yes refl | inj₂ p′
  with args-∈⁻ L p′
args-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | yes refl | inj₂ p′
  | U , r , e∈ , u∈ = U , r , there e∈ , u∈
args-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | no _ with args-∈⁻ L p
args-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | no _ | U , r , e∈ , u∈ =
  U , r , there e∈ , u∈
args-∈⁻ (vtrue ∷ L) p with args-∈⁻ L p
args-∈⁻ (vtrue ∷ L) p | U , r , e∈ , u∈ = U , r , there e∈ , u∈
args-∈⁻ (vfalse ∷ L) p with args-∈⁻ L p
args-∈⁻ (vfalse ∷ L) p | U , r , e∈ , u∈ = U , r , there e∈ , u∈
args-∈⁻ (sealᵛ σ w ∷ L) p with args-∈⁻ L p
args-∈⁻ (sealᵛ σ w ∷ L) p | U , r , e∈ , u∈ = U , r , there e∈ , u∈
args-∈⁻ (injᵛ G w ∷ L) p with args-∈⁻ L p
args-∈⁻ (injᵛ G w ∷ L) p | U , r , e∈ , u∈ = U , r , there e∈ , u∈
args-∈⁻ ((σ ⟼∀ s) ∷ L) p with args-∈⁻ L p
args-∈⁻ ((σ ⟼∀ s) ∷ L) p | U , r , e∈ , u∈ = U , r , there e∈ , u∈
args-∈⁻ (νλ ∷ L) p with args-∈⁻ L p
args-∈⁻ (νλ ∷ L) p | U , r , e∈ , u∈ = U , r , there e∈ , u∈
args-∈⁻ (ν∀ ∷ L) p with args-∈⁻ L p
args-∈⁻ (ν∀ ∷ L) p | U , r , e∈ , u∈ = U , r , there e∈ , u∈

results-∈⁺ : ∀ {m U r L} → (U ⟼ r at m) ⋵ L → r ⋵ resultsAt m L
results-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} p with m ≟ℕ m′
results-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (here refl) | yes _ = here refl
results-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (there p) | yes _ =
  there (results-∈⁺ p)
results-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (here refl) | no m≢ =
  ⊥-elim (m≢ refl)
results-∈⁺ {m} {L = (V ⟼ s at m′) ∷ L} (there p) | no _ = results-∈⁺ p
results-∈⁺ {L = vtrue ∷ L} (there p) = results-∈⁺ p
results-∈⁺ {L = vfalse ∷ L} (there p) = results-∈⁺ p
results-∈⁺ {L = sealᵛ σ w ∷ L} (there p) = results-∈⁺ p
results-∈⁺ {L = injᵛ G w ∷ L} (there p) = results-∈⁺ p
results-∈⁺ {L = (σ ⟼∀ s) ∷ L} (there p) = results-∈⁺ p
results-∈⁺ {L = νλ ∷ L} (there p) = results-∈⁺ p
results-∈⁺ {L = ν∀ ∷ L} (there p) = results-∈⁺ p

results-∈⁻ : ∀ {m r} L → r ⋵ resultsAt m L
  → Σ[ U ∈ List Val ] ((U ⟼ r at m) ⋵ L)
results-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p with m ≟ℕ m′
results-∈⁻ {m} ((V ⟼ s at m′) ∷ L) (here refl) | yes refl = V , here refl
results-∈⁻ {m} ((V ⟼ s at m′) ∷ L) (there p) | yes refl
  with results-∈⁻ L p
results-∈⁻ {m} ((V ⟼ s at m′) ∷ L) (there p) | yes refl | U , e∈ =
  U , there e∈
results-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | no _ with results-∈⁻ L p
results-∈⁻ {m} ((V ⟼ s at m′) ∷ L) p | no _ | U , e∈ = U , there e∈
results-∈⁻ (vtrue ∷ L) p with results-∈⁻ L p
results-∈⁻ (vtrue ∷ L) p | U , e∈ = U , there e∈
results-∈⁻ (vfalse ∷ L) p with results-∈⁻ L p
results-∈⁻ (vfalse ∷ L) p | U , e∈ = U , there e∈
results-∈⁻ (sealᵛ σ w ∷ L) p with results-∈⁻ L p
results-∈⁻ (sealᵛ σ w ∷ L) p | U , e∈ = U , there e∈
results-∈⁻ (injᵛ G w ∷ L) p with results-∈⁻ L p
results-∈⁻ (injᵛ G w ∷ L) p | U , e∈ = U , there e∈
results-∈⁻ ((σ ⟼∀ s) ∷ L) p with results-∈⁻ L p
results-∈⁻ ((σ ⟼∀ s) ∷ L) p | U , e∈ = U , there e∈
results-∈⁻ (νλ ∷ L) p with results-∈⁻ L p
results-∈⁻ (νλ ∷ L) p | U , e∈ = U , there e∈
results-∈⁻ (ν∀ ∷ L) p with results-∈⁻ L p
results-∈⁻ (ν∀ ∷ L) p | U , e∈ = U , there e∈

bodies-∈⁺ : ∀ {σ r L} → (σ ⟼∀ r) ⋵ L → r ⋵ bodiesAt σ L
bodies-∈⁺ {σ} {L = (σ′ ⟼∀ s) ∷ L} p with σ ≟ℕ σ′
bodies-∈⁺ {σ} {L = (σ′ ⟼∀ s) ∷ L} (here refl) | yes _ = here refl
bodies-∈⁺ {σ} {L = (σ′ ⟼∀ s) ∷ L} (there p) | yes _ =
  there (bodies-∈⁺ p)
bodies-∈⁺ {σ} {L = (σ′ ⟼∀ s) ∷ L} (here refl) | no σ≢ =
  ⊥-elim (σ≢ refl)
bodies-∈⁺ {σ} {L = (σ′ ⟼∀ s) ∷ L} (there p) | no _ = bodies-∈⁺ p
bodies-∈⁺ {L = vtrue ∷ L} (there p) = bodies-∈⁺ p
bodies-∈⁺ {L = vfalse ∷ L} (there p) = bodies-∈⁺ p
bodies-∈⁺ {L = sealᵛ σ′ w ∷ L} (there p) = bodies-∈⁺ p
bodies-∈⁺ {L = injᵛ G w ∷ L} (there p) = bodies-∈⁺ p
bodies-∈⁺ {L = (V ⟼ s at m) ∷ L} (there p) = bodies-∈⁺ p
bodies-∈⁺ {L = νλ ∷ L} (there p) = bodies-∈⁺ p
bodies-∈⁺ {L = ν∀ ∷ L} (there p) = bodies-∈⁺ p

bodies-∈⁻ : ∀ {σ r} L → r ⋵ bodiesAt σ L → (σ ⟼∀ r) ⋵ L
bodies-∈⁻ {σ} ((σ′ ⟼∀ s) ∷ L) p with σ ≟ℕ σ′
bodies-∈⁻ {σ} ((σ′ ⟼∀ s) ∷ L) (here refl) | yes refl = here refl
bodies-∈⁻ {σ} ((σ′ ⟼∀ s) ∷ L) (there p) | yes refl =
  there (bodies-∈⁻ L p)
bodies-∈⁻ {σ} ((σ′ ⟼∀ s) ∷ L) p | no _ = there (bodies-∈⁻ L p)
bodies-∈⁻ (vtrue ∷ L) p = there (bodies-∈⁻ L p)
bodies-∈⁻ (vfalse ∷ L) p = there (bodies-∈⁻ L p)
bodies-∈⁻ (sealᵛ σ′ w ∷ L) p = there (bodies-∈⁻ L p)
bodies-∈⁻ (injᵛ G w ∷ L) p = there (bodies-∈⁻ L p)
bodies-∈⁻ ((V ⟼ s at m) ∷ L) p = there (bodies-∈⁻ L p)
bodies-∈⁻ (νλ ∷ L) p = there (bodies-∈⁻ L p)
bodies-∈⁻ (ν∀ ∷ L) p = there (bodies-∈⁻ L p)

values-∈⁺ : ∀ {m v Rs} → ret v m ⋵ Rs → v ⋵ valuesAt m Rs
values-∈⁺ {m} {Rs = ret w m′ ∷ Rs} p with m ≟ℕ m′
values-∈⁺ {m} {Rs = ret w m′ ∷ Rs} (here refl) | yes _ = here refl
values-∈⁺ {m} {Rs = ret w m′ ∷ Rs} (there p) | yes _ =
  there (values-∈⁺ p)
values-∈⁺ {m} {Rs = ret w m′ ∷ Rs} (here refl) | no m≢ = ⊥-elim (m≢ refl)
values-∈⁺ {m} {Rs = ret w m′ ∷ Rs} (there p) | no _ = values-∈⁺ p
values-∈⁺ {Rs = err ∷ Rs} (there p) = values-∈⁺ p

values-∈⁻ : ∀ {m v} Rs → v ⋵ valuesAt m Rs → ret v m ⋵ Rs
values-∈⁻ {m} (ret w m′ ∷ Rs) p with m ≟ℕ m′
values-∈⁻ {m} (ret w m′ ∷ Rs) (here refl) | yes refl = here refl
values-∈⁻ {m} (ret w m′ ∷ Rs) (there p) | yes refl =
  there (values-∈⁻ Rs p)
values-∈⁻ {m} (ret w m′ ∷ Rs) p | no _ = there (values-∈⁻ Rs p)
values-∈⁻ (err ∷ Rs) p = there (values-∈⁻ Rs p)

-- the extractors are monotone with respect to membership
untag-⊆ : ∀ {G} L L₂ → mem L₂ ⊆ mem L
  → mem (untagᴸ G L₂) ⊆ mem (untagᴸ G L)
untag-⊆ L L₂ L⊆ u u∈ = untag-∈⁺ (L⊆ _ (untag-∈⁻ L₂ u∈))

unseal-⊆ : ∀ {σ} L L₂ → mem L₂ ⊆ mem L
  → mem (unsealᴸ σ L₂) ⊆ mem (unsealᴸ σ L)
unseal-⊆ L L₂ L⊆ u u∈ = unseal-∈⁺ (L⊆ _ (unseal-∈⁻ L₂ u∈))

args-⊆ : ∀ {m} L L₂ → mem L₂ ⊆ mem L
  → mem (argsAt m L₂) ⊆ mem (argsAt m L)
args-⊆ L L₂ L⊆ u u∈ with args-∈⁻ L₂ u∈
args-⊆ L L₂ L⊆ u u∈ | U , r , e∈ , u∈U = args-∈⁺ (L⊆ _ e∈) u∈U

results-⊆ : ∀ {m} L L₂ → mem L₂ ⊆ mem L
  → ∀ r → r ⋵ resultsAt m L₂ → r ⋵ resultsAt m L
results-⊆ L L₂ L⊆ r r∈ with results-∈⁻ L₂ r∈
results-⊆ L L₂ L⊆ r r∈ | U , e∈ = results-∈⁺ (L⊆ _ e∈)

bodies-⊆ : ∀ {σ} L L₂ → mem L₂ ⊆ mem L
  → ∀ r → r ⋵ bodiesAt σ L₂ → r ⋵ bodiesAt σ L
bodies-⊆ L L₂ L⊆ r r∈ = bodies-∈⁺ (L⊆ _ (bodies-∈⁻ L₂ r∈))

values-⊆ : ∀ {m} Rs Rs₂ → (∀ r → r ⋵ Rs₂ → r ⋵ Rs)
  → mem (valuesAt m Rs₂) ⊆ mem (valuesAt m Rs)
values-⊆ Rs Rs₂ R⊆ v v∈ = values-∈⁺ (R⊆ _ (values-∈⁻ Rs₂ v∈))

-- the members of a list
nonempty : ∀ {A : Set} {L : List A} {x} → x ⋵ L → L ≢ []
nonempty (here refl) ()
nonempty (there p) ()

head∈ : ∀ {A : Set} {x : A} {L} → x ⋵ (x ∷ L)
head∈ = here refl

------------------------------------------------------------------------
-- Selecting a sublist from membership proofs
------------------------------------------------------------------------

-- split P by whether each element is the head y
split : ∀ y L′ P → mem P ⊆ mem (y ∷ L′)
  → Σ[ P′ ∈ List Val ]
      (mem P′ ⊆ mem L′ × mem P′ ⊆ mem P
       × ((y ⋵ P × (∀ x → x ⋵ P → x ⋵ P′ ⊎ x ≡ y))
          ⊎ (∀ x → x ⋵ P → x ⋵ P′)))
split y L′ [] h = [] , c-[]-⊆ , c-[]-⊆ , inj₂ (λ x ())
split y L′ (x ∷ P) h with h x (here refl)
  | split y L′ P (λ z z∈ → h z (there z∈))
split y L′ (x ∷ P) h | here refl | P′ , P′⊆L′ , P′⊆P , cov =
  P′ , P′⊆L′ , (λ z z∈ → there (P′⊆P z z∈)) ,
  inj₁ (here refl , cov′ (weaken cov))
  where
  weaken : ((x ⋵ P × (∀ z → z ⋵ P → z ⋵ P′ ⊎ z ≡ x))
            ⊎ (∀ z → z ⋵ P → z ⋵ P′))
    → ∀ z → z ⋵ P → z ⋵ P′ ⊎ z ≡ x
  weaken (inj₁ (x∈ , c)) = c
  weaken (inj₂ c) z z∈ = inj₁ (c z z∈)
  cov′ : (∀ z → z ⋵ P → z ⋵ P′ ⊎ z ≡ x)
    → ∀ z → z ⋵ (x ∷ P) → z ⋵ P′ ⊎ z ≡ x
  cov′ c z (here refl) = inj₂ refl
  cov′ c z (there z∈) = c z z∈
split y L′ (x ∷ P) h | there x∈ | P′ , P′⊆L′ , P′⊆P , cov =
  x ∷ P′ , c-∷-⊆ x∈ P′⊆L′ , c-∷-⊆ (here refl) (λ z z∈ → there (P′⊆P z z∈)) ,
  cov′ cov
  where
  cov′ : ((y ⋵ P × (∀ z → z ⋵ P → z ⋵ P′ ⊎ z ≡ y))
          ⊎ (∀ z → z ⋵ P → z ⋵ P′))
    → ((y ⋵ (x ∷ P) × (∀ z → z ⋵ (x ∷ P) → z ⋵ (x ∷ P′) ⊎ z ≡ y))
       ⊎ (∀ z → z ⋵ (x ∷ P) → z ⋵ (x ∷ P′)))
  cov′ (inj₁ (y∈ , c)) = inj₁ (there y∈ , c′)
    where
    c′ : ∀ z → z ⋵ (x ∷ P) → z ⋵ (x ∷ P′) ⊎ z ≡ y
    c′ z (here refl) = inj₁ (here refl)
    c′ z (there z∈) with c z z∈
    c′ z (there z∈) | inj₁ z∈′ = inj₁ (there z∈′)
    c′ z (there z∈) | inj₂ eq = inj₂ eq
  cov′ (inj₂ c) = inj₂ c′
    where
    c′ : ∀ z → z ⋵ (x ∷ P) → z ⋵ (x ∷ P′)
    c′ z (here refl) = here refl
    c′ z (there z∈) = there (c z z∈)

-- a sublist of L with the same members as P
select : ∀ L P → mem P ⊆ mem L
  → Σ[ L₀ ∈ List Val ] (L₀ ⊑ˢ L × mem L₀ ⊆ mem P × mem P ⊆ mem L₀)
select [] P h = [] , [] , c-[]-⊆ , (λ x x∈ → h x x∈)
select (y ∷ L′) P h with split y L′ P h
select (y ∷ L′) P h | P′ , P′⊆L′ , P′⊆P , cov
  with select L′ P′ P′⊆L′
select (y ∷ L′) P h | P′ , P′⊆L′ , P′⊆P , inj₁ (y∈ , c)
  | L₀ , s , L₀⊆P′ , P′⊆L₀ =
  y ∷ L₀ , refl ∷ s , c-∷-⊆ y∈ (λ z z∈ → P′⊆P z (L₀⊆P′ z z∈)) , cov′
  where
  cov′ : mem P ⊆ mem (y ∷ L₀)
  cov′ z z∈ with c z z∈
  cov′ z z∈ | inj₁ z∈′ = there (P′⊆L₀ z z∈′)
  cov′ z z∈ | inj₂ refl = here refl
select (y ∷ L′) P h | P′ , P′⊆L′ , P′⊆P , inj₂ c
  | L₀ , s , L₀⊆P′ , P′⊆L₀ =
  L₀ , y ∷ʳ s , (λ z z∈ → P′⊆P z (L₀⊆P′ z z∈)) ,
  (λ z z∈ → P′⊆L₀ z (c z z∈))


------------------------------------------------------------------------
-- Closure under subsets of the list; fuel irrelevance
------------------------------------------------------------------------

All-lookup : ∀ {P : Val → Set} {L y} → All P L → y ⋵ L → P y
All-lookup (px ∷ all) (here refl) = px
All-lookup (px ∷ all) (there y∈) = All-lookup all y∈

All-⊆ : ∀ {P : Val → Set} {L L₂} → All P L → mem L₂ ⊆ mem L → All P L₂
All-⊆ {L₂ = []} all L⊆ = []
All-⊆ {L₂ = x ∷ L₂} all L⊆ =
  All-lookup all (L⊆ x (here refl)) ∷ All-⊆ all (λ y y∈ → L⊆ y (there y∈))

ne-⊆ : ∀ {A : Set} (X Y : List A) → (∀ x → x ⋵ X → x ⋵ Y)
  → X ≢ [] → Y ≢ []
ne-⊆ [] Y X⊆ ne = ⊥-elim (ne refl)
ne-⊆ (x ∷ X) Y X⊆ ne = nonempty (X⊆ x (here refl))

HasErr→∈ : ∀ {Rs} → HasErr Rs → err ⋵ Rs
HasErr→∈ (here refl) = here refl
HasErr→∈ (there h) = there (HasErr→∈ h)

∈→HasErr : ∀ {Rs} → err ⋵ Rs → HasErr Rs
∈→HasErr (here refl) = here refl
∈→HasErr (there h) = there (∈→HasErr h)

noerr-⊆ : ∀ Rs Rs₂ → (∀ r → r ⋵ Rs₂ → r ⋵ Rs) → ¬ HasErr Rs
  → ¬ HasErr Rs₂
noerr-⊆ Rs Rs₂ R⊆ ne h = ne (∈→HasErr (R⊆ err (HasErr→∈ h)))

-- size bounds for the parts of the elements
pred-< : ∀ {a d} → suc a < suc d → a < d
pred-< (s≤s a<d) = a<d

untag-bound : ∀ {G d} L → (∀ v → v ⋵ L → sizeᵛ v < suc d)
  → ∀ u → u ⋵ untagᴸ G L → sizeᵛ u < d
untag-bound L b u u∈ = pred-< (b _ (untag-∈⁻ L u∈))

unseal-bound : ∀ {σ d} L → (∀ v → v ⋵ L → sizeᵛ v < suc d)
  → ∀ u → u ⋵ unsealᴸ σ L → sizeᵛ u < d
unseal-bound L b u u∈ = pred-< (b _ (unseal-∈⁻ L u∈))

args-bound : ∀ {m d} L → (∀ v → v ⋵ L → sizeᵛ v < suc d)
  → ∀ u → u ⋵ argsAt m L → sizeᵛ u < d
args-bound L b u u∈ with args-∈⁻ L u∈
args-bound L b u u∈ | U , r , e∈ , u∈U =
  pred-< (≤-<-trans (s≤s (≤-trans (∈-size u∈U) (m≤m+n _ _))) (b _ e∈))

results-bound : ∀ {m d} L → (∀ v → v ⋵ L → sizeᵛ v < suc d)
  → ∀ r → r ⋵ resultsAt m L → sizeᴿ r < d
results-bound L b r r∈ with results-∈⁻ L r∈
results-bound L b r r∈ | U , e∈ =
  pred-< (≤-<-trans (s≤s (m≤n+m (sizeᴿ r) (sizeᴸ U))) (b _ e∈))

bodies-bound : ∀ {σ d} L → (∀ v → v ⋵ L → sizeᵛ v < suc d)
  → ∀ r → r ⋵ bodiesAt σ L → sizeᴿ r < d
bodies-bound L b r r∈ = pred-< (b _ (bodies-∈⁻ L r∈))

values-bound : ∀ {m d} Rs → (∀ r → r ⋵ Rs → sizeᴿ r < d)
  → ∀ v → v ⋵ valuesAt m Rs → sizeᵛ v < d
values-bound Rs b v v∈ = b _ (values-∈⁻ Rs v∈)

-- the fuel needed by the parts of a nonempty list
<-pred : ∀ {a b k} → a < b → b < suc k → a < k
<-pred a<b (s≤s b≤k) = <-≤-trans a<b b≤k

∉[] : ∀ {A : Set} {x : A} → x ⋵ [] → ⊥
∉[] ()

mutual
  ▹-⊆ : ∀ d k k₂ {W θ p L L₂ D′}
    → (∀ v → v ⋵ L → sizeᵛ v < d) → sizeᴸ L < k → sizeᴸ L₂ < k₂
    → mem L₂ ⊆ mem L
    → Rel▹ k W θ p L D′ → Rel▹ k₂ W θ p L₂ D′
  ▹-⊆ d k k₂ {L₂ = []} b sL sL₂ L⊆ rel = tt₁
  ▹-⊆ d k k₂ {L = []} {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ rel =
    ⊥-elim (∉[] (L⊆ v₂ (here refl)))
  ▹-⊆ zero k k₂ {L = v ∷ L} {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ rel
    with b v (here refl)
  ... | ()
  ▹-⊆ (suc d) zero k₂ {L = v ∷ L} {L₂ = v₂ ∷ L₂} b () sL₂ L⊆ rel
  ▹-⊆ (suc d) (suc k) zero {L = v ∷ L} {L₂ = v₂ ∷ L₂} b sL () L⊆ rel
  ▹-⊆ (suc d) (suc k) (suc k₂) {p = ★⊑} {L = v ∷ L} {L₂ = v₂ ∷ L₂}
      b sL sL₂ L⊆ (lift all , f) =
    lift (All-⊆ all L⊆) ,
    λ G → ▹-⊆ d k k₂ (untag-bound (v ∷ L) b)
            (<-pred (untag-< G v L) sL) (<-pred (untag-< G v₂ L₂) sL₂)
            (untag-⊆ (v ∷ L) (v₂ ∷ L₂) L⊆) (f G)
  ▹-⊆ (suc d) (suc k) (suc k₂) {p = tag G p} {L = v ∷ L} {L₂ = v₂ ∷ L₂}
      b sL sL₂ L⊆ rel =
    ▹-⊆ (suc d) (suc k) (suc k₂) {p = p} b sL sL₂ L⊆ rel
  ▹-⊆ (suc d) (suc k) (suc k₂) {θ = θ} {p = ‵⊑ α} {L = v ∷ L}
      {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ (lift all , q , w∋ , rel) =
    lift (All-⊆ all L⊆) , q , w∋ ,
    ▹-⊆ d k k₂ (unseal-bound (v ∷ L) b)
      (<-pred (unseal-< (⟦ α ⟧ₙ θ) v L) sL)
      (<-pred (unseal-< (⟦ α ⟧ₙ θ) v₂ L₂) sL₂)
      (unseal-⊆ (v ∷ L) (v₂ ∷ L₂) L⊆) rel
  ▹-⊆ (suc d) (suc k) (suc k₂) {p = 𝔹⊑} {L = v ∷ L} {L₂ = v₂ ∷ L₂}
      b sL sL₂ L⊆ (lift all) = lift (All-⊆ all L⊆)
  ▹-⊆ (suc d) (suc k) (suc k₂) {W} {θ} {p ⇒⊑ q} {v ∷ L} {v₂ ∷ L₂} {D′}
      b sL sL₂ L⊆ (lift all , lift ν∈ , f) =
    lift (All-⊆ all L⊆) , lift ν∈ , g
    where
    g : ∀ L₂₀ → L₂₀ ⊑ˢ (v₂ ∷ L₂) → ∀ m W′ → W ⊑ʷ W′ → length W′ ≡ m
      → ∀ E′ → Consistent E′
      → Rel▹ k₂ W′ θ p (argsAt m L₂₀) E′
      → Rel▹ᶜ k₂ W′ θ q (resultsAt m L₂₀) (D′ ●[ m ] E′)
    g L₂₀ s m W′ ext len E′ CE′ rel₂
      with select (v ∷ L) L₂₀ (λ x x∈ → L⊆ x (sub-mem s x x∈))
    g L₂₀ s m W′ ext len E′ CE′ rel₂ | L₀ , s₀ , L₀⊆ , ⊆L₀ =
      ▹ᶜ-⊆ d k k₂ {R′ = D′ ●[ m ] E′}
        (results-bound L₀ (λ x x∈ → b x (sub-mem s₀ x x∈)))
        (<-pred (results-sub-< m v L s₀) sL)
        (<-pred (results-sub-< m v₂ L₂ s) sL₂)
        (results-⊆ L₀ L₂₀ ⊆L₀)
        (f L₀ s₀ m W′ ext len E′ CE′
          (▹-⊆ d k₂ k
             (args-bound L₂₀
                (λ x x∈ → b x (L⊆ x (sub-mem s x x∈))))
             (<-pred (args-sub-< m v₂ L₂ s) sL₂)
             (<-pred (args-sub-< m v L s₀) sL)
             (args-⊆ L₂₀ L₀ L₀⊆) rel₂))
  ▹-⊆ (suc d) (suc k) (suc k₂) {p = ∀⊑ p} {L = v ∷ L} {L₂ = v₂ ∷ L₂}
      {D′} b sL sL₂ L⊆ (lift all , lift ν∈ , f) =
    lift (All-⊆ all L⊆) , lift ν∈ ,
    λ σ W′ q′ ext len →
      ▹ᶜ-⊆ d k k₂ {R′ = D′ ◆ σ} (bodies-bound (v ∷ L) b)
        (<-pred (bodies-< σ v L) sL) (<-pred (bodies-< σ v₂ L₂) sL₂)
        (bodies-⊆ (v ∷ L) (v₂ ∷ L₂) L⊆) (f σ W′ q′ ext len)

  ▹ᶜ-⊆ : ∀ d k k₂ {W θ p Rs Rs₂ R′}
    → (∀ r → r ⋵ Rs → sizeᴿ r < d) → sizeᴿᴸ Rs < k → sizeᴿᴸ Rs₂ < k₂
    → (∀ r → r ⋵ Rs₂ → r ⋵ Rs)
    → Rel▹ᶜ k W θ p Rs R′ → Rel▹ᶜ k₂ W θ p Rs₂ R′
  ▹ᶜ-⊆ d k k₂ {Rs = Rs} {Rs₂} {R′} b sR sR₂ R⊆ h m ne
    with h m (ne-⊆ (valuesAt m Rs₂) (valuesAt m Rs) (values-⊆ Rs Rs₂ R⊆) ne)
  ... | W′ , ext , len , rel =
    W′ , ext , len ,
    ▹-⊆ d k k₂ {D′ = ⌊ R′ ⌋ m} (values-bound Rs b)
      (≤-<-trans (values-≤ m Rs) sR) (≤-<-trans (values-≤ m Rs₂) sR₂)
      (values-⊆ Rs Rs₂ R⊆) rel

mutual
  ◃-⊆ : ∀ d k k₂ {W θ p D L L₂}
    → (∀ v → v ⋵ L → sizeᵛ v < d) → sizeᴸ L < k → sizeᴸ L₂ < k₂
    → mem L₂ ⊆ mem L
    → Rel◃ k W θ p D L → Rel◃ k₂ W θ p D L₂
  ◃-⊆ d k k₂ {L₂ = []} b sL sL₂ L⊆ rel = tt₁
  ◃-⊆ d k k₂ {L = []} {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ rel =
    ⊥-elim (∉[] (L⊆ v₂ (here refl)))
  ◃-⊆ zero k k₂ {L = v ∷ L} {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ rel
    with b v (here refl)
  ... | ()
  ◃-⊆ (suc d) zero k₂ {L = v ∷ L} {L₂ = v₂ ∷ L₂} b () sL₂ L⊆ rel
  ◃-⊆ (suc d) (suc k) zero {L = v ∷ L} {L₂ = v₂ ∷ L₂} b sL () L⊆ rel
  ◃-⊆ (suc d) (suc k) (suc k₂) {p = ★⊑} {L = v ∷ L} {L₂ = v₂ ∷ L₂}
      b sL sL₂ L⊆ (lift all , f) =
    lift (All-⊆ all L⊆) ,
    λ G → ◃-⊆ d k k₂ (untag-bound (v ∷ L) b)
            (<-pred (untag-< G v L) sL) (<-pred (untag-< G v₂ L₂) sL₂)
            (untag-⊆ (v ∷ L) (v₂ ∷ L₂) L⊆) (f G)
  ◃-⊆ (suc d) (suc k) (suc k₂) {θ = θ} {p = tag G p} {L = v ∷ L}
      {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ (lift all , rel) =
    lift (All-⊆ all L⊆) ,
    ◃-⊆ d k k₂ (untag-bound (v ∷ L) b)
      (<-pred (untag-< (⟦ G ⟧ᴳ θ) v L) sL)
      (<-pred (untag-< (⟦ G ⟧ᴳ θ) v₂ L₂) sL₂)
      (untag-⊆ (v ∷ L) (v₂ ∷ L₂) L⊆) rel
  ◃-⊆ (suc d) (suc k) (suc k₂) {θ = θ} {p = ‵⊑ α} {L = v ∷ L}
      {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ (lift all , q , w∋ , rel) =
    lift (All-⊆ all L⊆) , q , w∋ ,
    ◃-⊆ d k k₂ (unseal-bound (v ∷ L) b)
      (<-pred (unseal-< (⟦ α ⟧ₙ θ) v L) sL)
      (<-pred (unseal-< (⟦ α ⟧ₙ θ) v₂ L₂) sL₂)
      (unseal-⊆ (v ∷ L) (v₂ ∷ L₂) L⊆) rel
  ◃-⊆ (suc d) (suc k) (suc k₂) {p = 𝔹⊑} {L = v ∷ L} {L₂ = v₂ ∷ L₂}
      b sL sL₂ L⊆ (lift all) = lift (All-⊆ all L⊆)
  ◃-⊆ (suc d) (suc k) (suc k₂) {W} {θ} {p ⇒⊑ q} {D} {v ∷ L} {v₂ ∷ L₂}
      b sL sL₂ L⊆ (lift all , lift ν∈ , f) =
    lift (All-⊆ all L⊆) , lift ν∈ , g
    where
    g : ∀ L₂₀ → L₂₀ ⊑ˢ (v₂ ∷ L₂) → ∀ m W′ → W ⊑ʷ W′ → length W′ ≡ m
      → ∀ E → Consistent E
      → Rel◃ k₂ W′ θ p E (argsAt m L₂₀)
      → Rel◃ᶜ k₂ W′ θ q (D ●[ m ] E) (resultsAt m L₂₀)
    g L₂₀ s m W′ ext len E CE rel₂
      with select (v ∷ L) L₂₀ (λ x x∈ → L⊆ x (sub-mem s x x∈))
    g L₂₀ s m W′ ext len E CE rel₂ | L₀ , s₀ , L₀⊆ , ⊆L₀ =
      ◃ᶜ-⊆ d k k₂ {R = D ●[ m ] E}
        (results-bound L₀ (λ x x∈ → b x (sub-mem s₀ x x∈)))
        (<-pred (results-sub-< m v L s₀) sL)
        (<-pred (results-sub-< m v₂ L₂ s) sL₂)
        (results-⊆ L₀ L₂₀ ⊆L₀)
        (f L₀ s₀ m W′ ext len E CE
          (◃-⊆ d k₂ k
             (args-bound L₂₀
                (λ x x∈ → b x (L⊆ x (sub-mem s x x∈))))
             (<-pred (args-sub-< m v₂ L₂ s) sL₂)
             (<-pred (args-sub-< m v L s₀) sL)
             (args-⊆ L₂₀ L₀ L₀⊆) rel₂))
  ◃-⊆ (suc d) (suc k) (suc k₂) {p = ∀⊑ p} {D = D} {L = v ∷ L}
      {L₂ = v₂ ∷ L₂} b sL sL₂ L⊆ (lift all , lift ν∈ , f) =
    lift (All-⊆ all L⊆) , lift ν∈ ,
    λ σ W′ q′ ext len →
      ◃ᶜ-⊆ d k k₂ {R = D ◆ σ} (bodies-bound (v ∷ L) b)
        (<-pred (bodies-< σ v L) sL) (<-pred (bodies-< σ v₂ L₂) sL₂)
        (bodies-⊆ (v ∷ L) (v₂ ∷ L₂) L⊆) (f σ W′ q′ ext len)

  ◃ᶜ-⊆ : ∀ d k k₂ {W θ p R Rs Rs₂}
    → (∀ r → r ⋵ Rs → sizeᴿ r < d) → sizeᴿᴸ Rs < k → sizeᴿᴸ Rs₂ < k₂
    → (∀ r → r ⋵ Rs₂ → r ⋵ Rs)
    → Rel◃ᶜ k W θ p R Rs → Rel◃ᶜ k₂ W θ p R Rs₂
  ◃ᶜ-⊆ d k k₂ b sR sR₂ R⊆ (inj₁ e) = inj₁ e
  ◃ᶜ-⊆ d k k₂ {W} {θ} {p} {R} {Rs} {Rs₂} b sR sR₂ R⊆
      (inj₂ (lift ne , h)) =
    inj₂ (lift (noerr-⊆ Rs Rs₂ R⊆ ne) , h′)
    where
    h′ : ∀ m → valuesAt m Rs₂ ≢ []
      → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m)
          × Rel◃ k₂ W′ θ p (⌊ R ⌋ m) (valuesAt m Rs₂))
    h′ m ne₂
      with h m (ne-⊆ (valuesAt m Rs₂) (valuesAt m Rs)
                  (values-⊆ Rs Rs₂ R⊆) ne₂)
    ... | W′ , ext , len , rel =
      W′ , ext , len ,
      ◃-⊆ d k k₂ {D = ⌊ R ⌋ m} (values-bound Rs b)
        (≤-<-trans (values-≤ m Rs) sR) (≤-<-trans (values-≤ m Rs₂) sR₂)
        (values-⊆ Rs Rs₂ R⊆) rel

-- every element of a list is no larger than the list
size-bound : ∀ L → ∀ v → v ⋵ L → sizeᵛ v < suc (sizeᴸ L)
size-bound L v v∈ = s≤s (∈-size v∈)

size-boundᴿ : ∀ Rs → ∀ r → r ⋵ Rs → sizeᴿ r < suc (sizeᴿᴸ Rs)
size-boundᴿ Rs r r∈ = s≤s (∈-sizeᴿ r∈)

-- fuel irrelevance
▹-fuel : ∀ k k₂ {W θ p L D′} → sizeᴸ L < k → sizeᴸ L < k₂
  → Rel▹ k W θ p L D′ → Rel▹ k₂ W θ p L D′
▹-fuel k k₂ {L = L} sk sk₂ =
  ▹-⊆ (suc (sizeᴸ L)) k k₂ (size-bound L) sk sk₂ (λ x x∈ → x∈)

▹ᶜ-fuel : ∀ k k₂ {W θ p Rs R′} → sizeᴿᴸ Rs < k → sizeᴿᴸ Rs < k₂
  → Rel▹ᶜ k W θ p Rs R′ → Rel▹ᶜ k₂ W θ p Rs R′
▹ᶜ-fuel k k₂ {Rs = Rs} {R′} sk sk₂ =
  ▹ᶜ-⊆ (suc (sizeᴿᴸ Rs)) k k₂ {R′ = R′} (size-boundᴿ Rs) sk sk₂ (λ x x∈ → x∈)

◃-fuel : ∀ k k₂ {W θ p D L} → sizeᴸ L < k → sizeᴸ L < k₂
  → Rel◃ k W θ p D L → Rel◃ k₂ W θ p D L
◃-fuel k k₂ {L = L} sk sk₂ =
  ◃-⊆ (suc (sizeᴸ L)) k k₂ (size-bound L) sk sk₂ (λ x x∈ → x∈)

◃ᶜ-fuel : ∀ k k₂ {W θ p R Rs} → sizeᴿᴸ Rs < k → sizeᴿᴸ Rs < k₂
  → Rel◃ᶜ k W θ p R Rs → Rel◃ᶜ k₂ W θ p R Rs
◃ᶜ-fuel k k₂ {R = R} {Rs} sk sk₂ =
  ◃ᶜ-⊆ (suc (sizeᴿᴸ Rs)) k k₂ {R = R} (size-boundᴿ Rs) sk sk₂ (λ x x∈ → x∈)

-- closure under subsets and sublists, in the notation
▹-sub⊆ : ∀ {W θ p L L₂ D′} → mem L₂ ⊆ mem L
  → W ∣ θ ⊢ p ⊢ L ▹ D′ → W ∣ θ ⊢ p ⊢ L₂ ▹ D′
▹-sub⊆ {L = L} {L₂} L⊆ =
  ▹-⊆ (suc (sizeᴸ L)) (suc (sizeᴸ L)) (suc (sizeᴸ L₂)) (size-bound L)
    ≤-refl ≤-refl L⊆

◃-sub⊆ : ∀ {W θ p D L L₂} → mem L₂ ⊆ mem L
  → W ∣ θ ⊢ p ⊢ D ◃ L → W ∣ θ ⊢ p ⊢ D ◃ L₂
◃-sub⊆ {L = L} {L₂} L⊆ =
  ◃-⊆ (suc (sizeᴸ L)) (suc (sizeᴸ L)) (suc (sizeᴸ L₂)) (size-bound L)
    ≤-refl ≤-refl L⊆

▹-sublist : ∀ {W θ p L L₀ D′} → L₀ ⊑ˢ L
  → W ∣ θ ⊢ p ⊢ L ▹ D′ → W ∣ θ ⊢ p ⊢ L₀ ▹ D′
▹-sublist s = ▹-sub⊆ (sub-mem s)

◃-sublist : ∀ {W θ p D L L₀} → L₀ ⊑ˢ L
  → W ∣ θ ⊢ p ⊢ D ◃ L → W ∣ θ ⊢ p ⊢ D ◃ L₀
◃-sublist s = ◃-sub⊆ (sub-mem s)

▹ᶜ-sub⊆ : ∀ {W θ p Rs Rs₂ R′} → (∀ r → r ⋵ Rs₂ → r ⋵ Rs)
  → W ∣ θ ⊢ p ⊢ Rs ▹ᶜ R′ → W ∣ θ ⊢ p ⊢ Rs₂ ▹ᶜ R′
▹ᶜ-sub⊆ {Rs = Rs} {Rs₂} {R′} R⊆ =
  ▹ᶜ-⊆ (suc (sizeᴿᴸ Rs)) (suc (sizeᴿᴸ Rs)) (suc (sizeᴿᴸ Rs₂)) {R′ = R′}
    (size-boundᴿ Rs) ≤-refl ≤-refl R⊆

◃ᶜ-sub⊆ : ∀ {W θ p R Rs Rs₂} → (∀ r → r ⋵ Rs₂ → r ⋵ Rs)
  → W ∣ θ ⊢ p ⊢ R ◃ᶜ Rs → W ∣ θ ⊢ p ⊢ R ◃ᶜ Rs₂
◃ᶜ-sub⊆ {R = R} {Rs} {Rs₂} R⊆ =
  ◃ᶜ-⊆ (suc (sizeᴿᴸ Rs)) (suc (sizeᴿᴸ Rs)) (suc (sizeᴿᴸ Rs₂)) {R = R}
    (size-boundᴿ Rs) ≤-refl ≤-refl R⊆


------------------------------------------------------------------------
-- Monotonicity in the set side
------------------------------------------------------------------------

All-map : ∀ {P Q : Val → Set} {L} → (∀ x → P x → Q x) → All P L → All Q L
All-map f [] = []
All-map f (px ∷ all) = f _ px ∷ All-map f all

IsBool-mono : ∀ {D D′} → D ⊆ D′ → ∀ x → IsBool D x → IsBool D′ x
IsBool-mono D⊆ vtrue t∈ = D⊆ vtrue t∈
IsBool-mono D⊆ vfalse f∈ = D⊆ vfalse f∈
IsBool-mono D⊆ (sealᵛ σ u) ()
IsBool-mono D⊆ (injᵛ G u) ()
IsBool-mono D⊆ (U ⟼ r at m) ()
IsBool-mono D⊆ (σ ⟼∀ r) ()
IsBool-mono D⊆ νλ ()
IsBool-mono D⊆ ν∀ ()

mutual
  ▹-mono : ∀ k {W θ p L D′ D″} → D′ ⊆ D″
    → Rel▹ k W θ p L D′ → Rel▹ k W θ p L D″
  ▹-mono k {L = []} D⊆ rel = tt₁
  ▹-mono zero {L = v ∷ L} D⊆ (lift ())
  ▹-mono (suc k) {W} {p = ★⊑} {L = v ∷ L} {D′} {D″} D⊆ (all , f) =
    all , λ G → ▹-mono k {W} {θ₀} {gp G} {untagᴸ G (v ∷ L)} {untag G D′}
                  {untag G D″} (λ x x∈ → D⊆ (injᵛ G x) x∈) (f G)
  ▹-mono (suc k) {W} {θ} {tag G p} {v ∷ L} {D′} {D″} D⊆ rel =
    ▹-mono (suc k) {W} {θ} {p} {v ∷ L} {untag (⟦ G ⟧ᴳ θ) D′}
      {untag (⟦ G ⟧ᴳ θ) D″} (λ x x∈ → D⊆ (injᵛ (⟦ G ⟧ᴳ θ) x) x∈) rel
  ▹-mono (suc k) {W} {θ} {‵⊑ α} {v ∷ L} {D′} {D″} D⊆
      (all , q , w∋ , rel) =
    all , q , w∋ ,
    ▹-mono k {W} {θ₀} {q} {unsealᴸ (⟦ α ⟧ₙ θ) (v ∷ L)}
      {unsealᴾ (⟦ α ⟧ₙ θ) D′} {unsealᴾ (⟦ α ⟧ₙ θ) D″}
      (λ x x∈ → D⊆ (sealᵛ (⟦ α ⟧ₙ θ) x) x∈) rel
  ▹-mono (suc k) {p = 𝔹⊑} {L = v ∷ L} D⊆ (lift all) =
    lift (All-map (IsBool-mono D⊆) all)
  ▹-mono (suc k) {W} {θ} {p ⇒⊑ q} {v ∷ L} {D′} {D″} D⊆
      (all , lift ν∈ , f) =
    all , lift (D⊆ νλ ν∈) ,
    λ L₀ s m W′ ext len E′ CE′ rel →
      ▹ᶜ-mono k {W′} {θ} {q} {resultsAt m L₀} {D′ ●[ m ] E′}
        {D″ ●[ m ] E′} (c-●-mono D⊆ (λ x x∈ → x∈))
        (f L₀ s m W′ ext len E′ CE′ rel)
  ▹-mono (suc k) {W} {θ} {∀⊑ p} {v ∷ L} {D′} {D″} D⊆
      (all , lift ν∈ , f) =
    all , lift (D⊆ ν∀ ν∈) ,
    λ σ W′ q′ ext len →
      ▹ᶜ-mono k {W′ ++ (q′ ∷ [])} {σ •ᵗ θ} {p} {bodiesAt σ (v ∷ L)}
        {D′ ◆ σ} {D″ ◆ σ} (λ r r∈ → D⊆ (σ ⟼∀ r) r∈) (f σ W′ q′ ext len)

  ▹ᶜ-mono : ∀ k {W θ p Rs R′ R″} → R′ ⊆ᴿ R″
    → Rel▹ᶜ k W θ p Rs R′ → Rel▹ᶜ k W θ p Rs R″
  ▹ᶜ-mono k {W} {θ} {p} {Rs} {R′} {R″} R⊆ h m ne with h m ne
  ... | W′ , ext , len , rel =
    W′ , ext , len ,
    ▹-mono k {W′} {θ} {p} {valuesAt m Rs} {⌊ R′ ⌋ m} {⌊ R″ ⌋ m}
      (c-⌊⌋-mono R⊆) rel

mutual
  ◃-mono : ∀ k {W θ p D D″ L} → D ⊆ D″
    → Rel◃ k W θ p D L → Rel◃ k W θ p D″ L
  ◃-mono k {L = []} D⊆ rel = tt₁
  ◃-mono zero {L = v ∷ L} D⊆ (lift ())
  ◃-mono (suc k) {W} {p = ★⊑} {D} {D″} {v ∷ L} D⊆ (all , f) =
    all , λ G → ◃-mono k {W} {θ₀} {gp G} {untag G D} {untag G D″}
                  {untagᴸ G (v ∷ L)} (λ x x∈ → D⊆ (injᵛ G x) x∈) (f G)
  ◃-mono (suc k) {W} {θ} {tag G p} {D} {D″} {v ∷ L} D⊆ (all , rel) =
    all , ◃-mono k {W} {θ} {p} {D} {D″} {untagᴸ (⟦ G ⟧ᴳ θ) (v ∷ L)} D⊆ rel
  ◃-mono (suc k) {W} {θ} {‵⊑ α} {D} {D″} {v ∷ L} D⊆
      (all , q , w∋ , rel) =
    all , q , w∋ ,
    ◃-mono k {W} {θ₀} {q} {unsealᴾ (⟦ α ⟧ₙ θ) D} {unsealᴾ (⟦ α ⟧ₙ θ) D″}
      {unsealᴸ (⟦ α ⟧ₙ θ) (v ∷ L)}
      (λ x x∈ → D⊆ (sealᵛ (⟦ α ⟧ₙ θ) x) x∈) rel
  ◃-mono (suc k) {p = 𝔹⊑} {L = v ∷ L} D⊆ (lift all) =
    lift (All-map (IsBool-mono D⊆) all)
  ◃-mono (suc k) {W} {θ} {p ⇒⊑ q} {D} {D″} {v ∷ L} D⊆
      (all , lift ν∈ , f) =
    all , lift (D⊆ νλ ν∈) ,
    λ L₀ s m W′ ext len E CE rel →
      ◃ᶜ-mono k {W′} {θ} {q} {D ●[ m ] E} {D″ ●[ m ] E} {resultsAt m L₀}
        (c-●-mono D⊆ (λ x x∈ → x∈)) (f L₀ s m W′ ext len E CE rel)
  ◃-mono (suc k) {W} {θ} {∀⊑ p} {D} {D″} {v ∷ L} D⊆
      (all , lift ν∈ , f) =
    all , lift (D⊆ ν∀ ν∈) ,
    λ σ W′ q′ ext len →
      ◃ᶜ-mono k {W′ ++ (q′ ∷ [])} {σ •ᵗ θ} {p} {D ◆ σ} {D″ ◆ σ}
        {bodiesAt σ (v ∷ L)} (λ r r∈ → D⊆ (σ ⟼∀ r) r∈) (f σ W′ q′ ext len)

  ◃ᶜ-mono : ∀ k {W θ p R R″ Rs} → R ⊆ᴿ R″
    → Rel◃ᶜ k W θ p R Rs → Rel◃ᶜ k W θ p R″ Rs
  ◃ᶜ-mono k R⊆ (inj₁ (lift e∈)) = inj₁ (lift (R⊆ err e∈))
  ◃ᶜ-mono k {W} {θ} {p} {R} {R″} {Rs} R⊆ (inj₂ (ne , h)) = inj₂ (ne , h′)
    where
    h′ : ∀ m → valuesAt m Rs ≢ []
      → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m)
          × Rel◃ k W′ θ p (⌊ R″ ⌋ m) (valuesAt m Rs))
    h′ m ne′ with h m ne′
    ... | W′ , ext , len , rel =
      W′ , ext , len ,
      ◃-mono k {W′} {θ} {p} {⌊ R ⌋ m} {⌊ R″ ⌋ m} {valuesAt m Rs}
        (c-⌊⌋-mono R⊆) rel

------------------------------------------------------------------------
-- Worlds
------------------------------------------------------------------------

++-assoc′ : ∀ (W X Y : World) → (W ++ X) ++ Y ≡ W ++ (X ++ Y)
++-assoc′ [] X Y = refl
++-assoc′ (q ∷ W) X Y = cong (q ∷_) (++-assoc′ W X Y)

++-[] : ∀ (W : World) → W ≡ W ++ []
++-[] [] = refl
++-[] (q ∷ W) = cong (q ∷_) (++-[] W)

⊑ʷ-refl : ∀ {W} → W ⊑ʷ W
⊑ʷ-refl {W} = [] , ++-[] W

⊑ʷ-trans : ∀ {W W′ W″} → W ⊑ʷ W′ → W′ ⊑ʷ W″ → W ⊑ʷ W″
⊑ʷ-trans {W} (X , refl) (Y , refl) = X ++ Y , ++-assoc′ W X Y

∋ʷ-++ : ∀ {W σ q} X → W ∋ʷ σ ⦂ q → (W ++ X) ∋ʷ σ ⦂ q
∋ʷ-++ X Zʷ = Zʷ
∋ʷ-++ X (Sʷ w∋) = Sʷ (∋ʷ-++ X w∋)

∋ʷ-ext : ∀ {W W′ σ q} → W ⊑ʷ W′ → W ∋ʷ σ ⦂ q → W′ ∋ʷ σ ⦂ q
∋ʷ-ext (X , refl) w∋ = ∋ʷ-++ X w∋

▹-kripke : ∀ k {W W″ θ p L D′} → W ⊑ʷ W″
  → Rel▹ k W θ p L D′ → Rel▹ k W″ θ p L D′
▹-kripke k {L = []} ext rel = tt₁
▹-kripke zero {L = v ∷ L} ext (lift ())
▹-kripke (suc k) {W} {W″} {p = ★⊑} {v ∷ L} {D′} ext (all , f) =
  all , λ G → ▹-kripke k {W} {W″} {θ₀} {gp G} {untagᴸ G (v ∷ L)}
                {untag G D′} ext (f G)
▹-kripke (suc k) {W} {W″} {θ} {tag G p} {v ∷ L} {D′} ext rel =
  ▹-kripke (suc k) {W} {W″} {θ} {p} {v ∷ L} {untag (⟦ G ⟧ᴳ θ) D′} ext rel
▹-kripke (suc k) {W} {W″} {θ} {‵⊑ α} {v ∷ L} {D′} ext
    (all , q , lift w∋ , rel) =
  all , q , lift (∋ʷ-ext ext w∋) ,
  ▹-kripke k {W} {W″} {θ₀} {q} {unsealᴸ (⟦ α ⟧ₙ θ) (v ∷ L)}
    {unsealᴾ (⟦ α ⟧ₙ θ) D′} ext rel
▹-kripke (suc k) {p = 𝔹⊑} {L = v ∷ L} ext rel = rel
▹-kripke (suc k) {p = p ⇒⊑ q} {L = v ∷ L} ext (all , ν∈ , f) =
  all , ν∈ ,
  λ L₀ s m W′ ext′ len → f L₀ s m W′ (⊑ʷ-trans ext ext′) len
▹-kripke (suc k) {p = ∀⊑ p} {L = v ∷ L} ext (all , ν∈ , f) =
  all , ν∈ , λ σ W′ q′ ext′ len → f σ W′ q′ (⊑ʷ-trans ext ext′) len

◃-kripke : ∀ k {W W″ θ p D L} → W ⊑ʷ W″
  → Rel◃ k W θ p D L → Rel◃ k W″ θ p D L
◃-kripke k {L = []} ext rel = tt₁
◃-kripke zero {L = v ∷ L} ext (lift ())
◃-kripke (suc k) {W} {W″} {p = ★⊑} {D} {v ∷ L} ext (all , f) =
  all , λ G → ◃-kripke k {W} {W″} {θ₀} {gp G} {untag G D}
                {untagᴸ G (v ∷ L)} ext (f G)
◃-kripke (suc k) {W} {W″} {θ} {tag G p} {D} {v ∷ L} ext (all , rel) =
  all , ◃-kripke k {W} {W″} {θ} {p} {D} {untagᴸ (⟦ G ⟧ᴳ θ) (v ∷ L)} ext rel
◃-kripke (suc k) {W} {W″} {θ} {‵⊑ α} {D} {v ∷ L} ext
    (all , q , lift w∋ , rel) =
  all , q , lift (∋ʷ-ext ext w∋) ,
  ◃-kripke k {W} {W″} {θ₀} {q} {unsealᴾ (⟦ α ⟧ₙ θ) D}
    {unsealᴸ (⟦ α ⟧ₙ θ) (v ∷ L)} ext rel
◃-kripke (suc k) {p = 𝔹⊑} {L = v ∷ L} ext rel = rel
◃-kripke (suc k) {p = p ⇒⊑ q} {L = v ∷ L} ext (all , ν∈ , f) =
  all , ν∈ ,
  λ L₀ s m W′ ext′ len → f L₀ s m W′ (⊑ʷ-trans ext ext′) len
◃-kripke (suc k) {p = ∀⊑ p} {L = v ∷ L} ext (all , ν∈ , f) =
  all , ν∈ , λ σ W′ q′ ext′ len → f σ W′ q′ (⊑ʷ-trans ext ext′) len

------------------------------------------------------------------------
-- A related nonempty list forces its set to be nonempty
------------------------------------------------------------------------

conv-pre : ∀ {D : 𝒱} (f : Val → Val) → Conv (λ x → f x ∈ D) → Conv D
conv-pre f (x , x∈) = f x , x∈

IsBool-conv : ∀ {D} x → IsBool D x → Conv D
IsBool-conv vtrue t∈ = vtrue , t∈
IsBool-conv vfalse f∈ = vfalse , f∈
IsBool-conv (sealᵛ σ u) ()
IsBool-conv (injᵛ G u) ()
IsBool-conv (U ⟼ r at m) ()
IsBool-conv (σ ⟼∀ r) ()
IsBool-conv νλ ()
IsBool-conv ν∀ ()

▹-conv : ∀ k {W θ p L D′ u} → u ⋵ L → Rel▹ k W θ p L D′ → Conv D′
▹-conv k {L = []} () rel
▹-conv zero {L = x ∷ L} u∈ (lift ())
▹-conv (suc k) {p = ★⊑} {L = injᵛ G w ∷ L} u∈
    (lift (is-inj ∷ all) , f) =
  conv-pre (injᵛ G) (▹-conv k (untag-∈⁺ {L = injᵛ G w ∷ L} (here refl))
                       (f G))
▹-conv (suc k) {θ = θ} {p = tag G p} {L = x ∷ L} u∈ rel =
  conv-pre (injᵛ (⟦ G ⟧ᴳ θ)) (▹-conv (suc k) {p = p} u∈ rel)
▹-conv (suc k) {p = ‵⊑ α} {L = sealᵛ σ w ∷ L} u∈
    (lift (is-seal-at ∷ all) , q , w∋ , rel) =
  conv-pre (sealᵛ σ)
    (▹-conv k (unseal-∈⁺ {L = sealᵛ σ w ∷ L} (here refl)) rel)
▹-conv (suc k) {p = 𝔹⊑} {L = x ∷ L} u∈ (lift (ib ∷ all)) =
  IsBool-conv x ib
▹-conv (suc k) {p = p ⇒⊑ q} {L = x ∷ L} u∈ (all , lift ν∈ , f) = νλ , ν∈
▹-conv (suc k) {p = ∀⊑ p} {L = x ∷ L} u∈ (all , lift ν∈ , f) = ν∀ , ν∈

◃-conv : ∀ k {W θ p D L u} → u ⋵ L → Rel◃ k W θ p D L → Conv D
◃-conv k {L = []} () rel
◃-conv zero {L = x ∷ L} u∈ (lift ())
◃-conv (suc k) {p = ★⊑} {L = injᵛ G w ∷ L} u∈
    (lift (is-inj ∷ all) , f) =
  conv-pre (injᵛ G) (◃-conv k (untag-∈⁺ {L = injᵛ G w ∷ L} (here refl))
                       (f G))
◃-conv (suc k) {p = tag G p} {L = injᵛ H w ∷ L} u∈
    (lift (is-inj-at ∷ all) , rel) =
  ◃-conv k (untag-∈⁺ {L = injᵛ H w ∷ L} (here refl)) rel
◃-conv (suc k) {p = ‵⊑ α} {L = sealᵛ σ w ∷ L} u∈
    (lift (is-seal-at ∷ all) , q , w∋ , rel) =
  conv-pre (sealᵛ σ)
    (◃-conv k (unseal-∈⁺ {L = sealᵛ σ w ∷ L} (here refl)) rel)
◃-conv (suc k) {p = 𝔹⊑} {L = x ∷ L} u∈ (lift (ib ∷ all)) =
  IsBool-conv x ib
◃-conv (suc k) {p = p ⇒⊑ q} {L = x ∷ L} u∈ (all , lift ν∈ , f) = νλ , ν∈
◃-conv (suc k) {p = ∀⊑ p} {L = x ∷ L} u∈ (all , lift ν∈ , f) = ν∀ , ν∈

-- a list of results with values at m forces the right set to have
-- values at m
▹ᶜ-conv : ∀ k {W θ p Rs R′ v m} → ret v m ⋵ Rs
  → Rel▹ᶜ k W θ p Rs R′ → Conv (⌊ R′ ⌋ m)
▹ᶜ-conv k {Rs = Rs} {v = v} {m} r∈ h
  with h m (nonempty (values-∈⁺ {Rs = Rs} r∈))
... | W′ , ext , len , rel = ▹-conv k (values-∈⁺ {Rs = Rs} r∈) rel

◃ᶜ-conv : ∀ k {W θ p R Rs v m} → ret v m ⋵ Rs
  → Rel◃ᶜ k W θ p R Rs → Lift₁ (err ∈ᴿ R) ⊎ Conv (⌊ R ⌋ m)
◃ᶜ-conv k r∈ (inj₁ e) = inj₁ e
◃ᶜ-conv k {Rs = Rs} {v = v} {m} r∈ (inj₂ (ne , h))
  with h m (nonempty (values-∈⁺ {Rs = Rs} r∈))
... | W′ , ext , len , rel = inj₂ (◃-conv k (values-∈⁺ {Rs = Rs} r∈) rel)

------------------------------------------------------------------------
-- Uniformity against a consistent set
------------------------------------------------------------------------

IsBool-split : ∀ {D} x → IsBool D x
  → (x ≡ vtrue × vtrue ∈ D) ⊎ (x ≡ vfalse × vfalse ∈ D)
IsBool-split vtrue t∈ = inj₁ (refl , t∈)
IsBool-split vfalse f∈ = inj₂ (refl , f∈)
IsBool-split (sealᵛ σ u) ()
IsBool-split (injᵛ G u) ()
IsBool-split (U ⟼ r at m) ()
IsBool-split (σ ⟼∀ r) ()
IsBool-split νλ ()
IsBool-split ν∀ ()

all-true : ∀ {D} → Consistent D → vtrue ∈ D → ∀ L → All (IsBool D) L
  → All (_≡ vtrue) L
all-true CD t∈ [] [] = []
all-true CD t∈ (x ∷ L) (ib ∷ all) with IsBool-split x ib
all-true CD t∈ (x ∷ L) (ib ∷ all) | inj₁ (refl , _) =
  refl ∷ all-true CD t∈ L all
all-true CD t∈ (x ∷ L) (ib ∷ all) | inj₂ (refl , f∈) =
  ⊥-elim (CD vtrue vfalse t∈ f∈)

all-false : ∀ {D} → Consistent D → vfalse ∈ D → ∀ L → All (IsBool D) L
  → All (_≡ vfalse) L
all-false CD f∈ [] [] = []
all-false CD f∈ (x ∷ L) (ib ∷ all) with IsBool-split x ib
all-false CD f∈ (x ∷ L) (ib ∷ all) | inj₁ (refl , t∈) =
  ⊥-elim (CD vfalse vtrue f∈ t∈)
all-false CD f∈ (x ∷ L) (ib ∷ all) | inj₂ (refl , _) =
  refl ∷ all-false CD f∈ L all

bool-uniform : ∀ {D} → Consistent D → ∀ L → All (IsBool D) L
  → All (_≡ vtrue) L ⊎ All (_≡ vfalse) L
bool-uniform CD [] [] = inj₁ []
bool-uniform CD (x ∷ L) (ib ∷ all) with IsBool-split x ib
bool-uniform CD (x ∷ L) (ib ∷ all) | inj₁ (refl , t∈) =
  inj₁ (all-true CD t∈ (x ∷ L) (ib ∷ all))
bool-uniform CD (x ∷ L) (ib ∷ all) | inj₂ (refl , f∈) =
  inj₂ (all-false CD f∈ (x ∷ L) (ib ∷ all))

-- a list of booleans related to a consistent set is uniform
▹-bool : ∀ k {W θ L D′} → Consistent D′ → Rel▹ k W θ 𝔹⊑ L D′
  → All (_≡ vtrue) L ⊎ All (_≡ vfalse) L
▹-bool k {L = []} CD rel = inj₁ []
▹-bool zero {L = x ∷ L} CD (lift ())
▹-bool (suc k) {L = x ∷ L} CD (lift all) = bool-uniform CD (x ∷ L) all

◃-bool : ∀ k {W θ D L} → Consistent D → Rel◃ k W θ 𝔹⊑ D L
  → All (_≡ vtrue) L ⊎ All (_≡ vfalse) L
◃-bool k {L = []} CD rel = inj₁ []
◃-bool zero {L = x ∷ L} CD (lift ())
◃-bool (suc k) {L = x ∷ L} CD (lift all) = bool-uniform CD (x ∷ L) all

-- the tags of a list of injections, given that the payloads of each
-- tag present have a counterpart
tag-uniform : ∀ {D} → Consistent D → ∀ G w L
  → (∀ H u → injᵛ H u ⋵ (injᵛ G w ∷ L) → Conv (untag H D))
  → All IsInj L → All (IsInjAt G) (injᵛ G w ∷ L)
tag-uniform {D} CD G w L h all = is-inj-at ∷ go L all (λ y y∈ → there y∈)
  where
  cG : Conv (untag G D)
  cG = h G w (here refl)
  go : ∀ L′ → All IsInj L′ → mem L′ ⊆ mem (injᵛ G w ∷ L)
    → All (IsInjAt G) L′
  go [] [] L⊆ = []
  go (injᵛ H u ∷ L′) (is-inj ∷ all′) L⊆
    with h H u (L⊆ _ (here refl))
  go (injᵛ H u ∷ L′) (is-inj ∷ all′) L⊆ | b , b∈
    with CD (injᵛ G (proj₁ cG)) (injᵛ H b) (proj₂ cG) b∈
  go (injᵛ H u ∷ L′) (is-inj ∷ all′) L⊆ | b , b∈ | refl , _ =
    is-inj-at ∷ go L′ all′ (λ y y∈ → L⊆ y (there y∈))

▹-tag : ∀ k {W θ L D′} → Consistent D′ → Rel▹ k W θ ★⊑ L D′
  → Σ[ G ∈ Ground ] All (IsInjAt G) L
▹-tag k {L = []} CD rel = G𝔹 , []
▹-tag zero {L = x ∷ L} CD (lift ())
▹-tag (suc k) {L = injᵛ G w ∷ L} CD (lift (is-inj ∷ all) , f) =
  G , tag-uniform CD G w L
        (λ H u u∈ → ▹-conv k (untag-∈⁺ u∈) (f H)) all

◃-tag : ∀ k {W θ D L} → Consistent D → Rel◃ k W θ ★⊑ D L
  → Σ[ G ∈ Ground ] All (IsInjAt G) L
◃-tag k {L = []} CD rel = G𝔹 , []
◃-tag zero {L = x ∷ L} CD (lift ())
◃-tag (suc k) {L = injᵛ G w ∷ L} CD (lift (is-inj ∷ all) , f) =
  G , tag-uniform CD G w L
        (λ H u u∈ → ◃-conv k (untag-∈⁺ u∈) (f H)) all


------------------------------------------------------------------------
-- Substitution and closing
------------------------------------------------------------------------

⇔-id : ∀ {A : Set₁} → A ⇔ A
⇔-id = mk⇔ (λ x → x) (λ x → x)

⇔-∘ : ∀ {A B C : Set₁} → A ⇔ B → B ⇔ C → A ⇔ C
⇔-∘ e₁ e₂ = mk⇔ (λ x → to e₂ (to e₁ x)) (λ z → from e₁ (from e₂ z))

⇔-≡ : ∀ {A B : Set₁} → A ≡ B → A ⇔ B
⇔-≡ refl = ⇔-id

⟦substₙ⟧ₙ : ∀ {θ θ′ s} → (∀ i → θ i ≡ ⟦ s i ⟧ₙ θ′)
  → ∀ α → ⟦ substₙ s α ⟧ₙ θ′ ≡ ⟦ α ⟧ₙ θ
⟦substₙ⟧ₙ h (tvar i) = sym (h i)
⟦substₙ⟧ₙ h (tseal σ) = refl

⟦substG⟧ᴳ : ∀ {θ θ′ s} → (∀ i → θ i ≡ ⟦ s i ⟧ₙ θ′)
  → ∀ G → ⟦ substG s G ⟧ᴳ θ′ ≡ ⟦ G ⟧ᴳ θ
⟦substG⟧ᴳ h (G‵ α) = cong (λ σ → G‵ (tseal σ)) (⟦substₙ⟧ₙ h α)
⟦substG⟧ᴳ h G𝔹 = refl
⟦substG⟧ᴳ h G⇒ = refl
⟦substG⟧ᴳ h G∀ = refl

⟦⇑ₙ⟧ₙ : ∀ {θ′ σ} α → ⟦ α ⟧ₙ θ′ ≡ ⟦ ⇑ₙ α ⟧ₙ (σ •ᵗ θ′)
⟦⇑ₙ⟧ₙ (tvar i) = refl
⟦⇑ₙ⟧ₙ (tseal s) = refl

ext-agree : ∀ {θ θ′ s σ} → (∀ i → θ i ≡ ⟦ s i ⟧ₙ θ′)
  → ∀ i → (σ •ᵗ θ) i ≡ ⟦ extₙ s i ⟧ₙ (σ •ᵗ θ′)
ext-agree h zero = refl
ext-agree {s = s} h (suc i) = trans (h i) (⟦⇑ₙ⟧ₙ (s i))

mutual
  ▹-subst : ∀ k {θ θ′ s W p L D′} → (∀ i → θ i ≡ ⟦ s i ⟧ₙ θ′)
    → Rel▹ k W θ′ (substᵖ s p) L D′ ⇔ Rel▹ k W θ p L D′
  ▹-subst k {L = []} h = ⇔-id
  ▹-subst zero {L = v ∷ L} h = ⇔-id
  ▹-subst (suc k) {p = ★⊑} {L = v ∷ L} h = ⇔-id
  ▹-subst (suc k) {θ} {θ′} {s} {W} {tag G p} {v ∷ L} {D′} h =
    ⇔-∘ (▹-subst (suc k) {θ} {θ′} {s} {W} {p} {v ∷ L}
           {untag (⟦ substG s G ⟧ᴳ θ′) D′} h)
        (⇔-≡ (cong (λ H → Rel▹ (suc k) W θ p (v ∷ L) (untag H D′))
                   (⟦substG⟧ᴳ h G)))
  ▹-subst (suc k) {θ} {θ′} {s} {W} {‵⊑ α} {v ∷ L} {D′} h =
    ⇔-≡ (cong (λ σ → Lift₁ (All (IsSealAt σ) (v ∷ L))
                      × Σ[ q ∈ Prec ] (Lift₁ (W ∋ʷ σ ⦂ q)
                          × Rel▹ k W θ₀ q (unsealᴸ σ (v ∷ L))
                                          (unsealᴾ σ D′)))
              (⟦substₙ⟧ₙ h α))
  ▹-subst (suc k) {p = 𝔹⊑} {L = v ∷ L} h = ⇔-id
  ▹-subst (suc k) {θ} {θ′} {s} {W} {p ⇒⊑ q} {v ∷ L} {D′} h =
    mk⇔ (λ { (all , ν∈ , f) → all , ν∈ ,
               λ L₀ s₀ m W′ ext len E′ CE′ rel →
                 to (▹ᶜ-subst k {θ} {θ′} {s} {W′} {q} {resultsAt m L₀}
                       {D′ ●[ m ] E′} h)
                   (f L₀ s₀ m W′ ext len E′ CE′
                      (from (▹-subst k {θ} {θ′} {s} {W′} {p}
                               {argsAt m L₀} {E′} h) rel)) })
        (λ { (all , ν∈ , f) → all , ν∈ ,
               λ L₀ s₀ m W′ ext len E′ CE′ rel →
                 from (▹ᶜ-subst k {θ} {θ′} {s} {W′} {q} {resultsAt m L₀}
                         {D′ ●[ m ] E′} h)
                   (f L₀ s₀ m W′ ext len E′ CE′
                      (to (▹-subst k {θ} {θ′} {s} {W′} {p}
                             {argsAt m L₀} {E′} h) rel)) })
  ▹-subst (suc k) {θ} {θ′} {s} {W} {∀⊑ p} {v ∷ L} {D′} h =
    mk⇔ (λ { (all , ν∈ , f) → all , ν∈ ,
               λ σ W′ q′ ext len →
                 to (▹ᶜ-subst k {σ •ᵗ θ} {σ •ᵗ θ′} {extₙ s}
                       {W′ ++ (q′ ∷ [])} {p} {bodiesAt σ (v ∷ L)}
                       {D′ ◆ σ} (ext-agree {θ} {θ′} {s} {σ} h))
                   (f σ W′ q′ ext len) })
        (λ { (all , ν∈ , f) → all , ν∈ ,
               λ σ W′ q′ ext len →
                 from (▹ᶜ-subst k {σ •ᵗ θ} {σ •ᵗ θ′} {extₙ s}
                         {W′ ++ (q′ ∷ [])} {p} {bodiesAt σ (v ∷ L)}
                         {D′ ◆ σ} (ext-agree {θ} {θ′} {s} {σ} h))
                   (f σ W′ q′ ext len) })

  ▹ᶜ-subst : ∀ k {θ θ′ s W p Rs R′} → (∀ i → θ i ≡ ⟦ s i ⟧ₙ θ′)
    → Rel▹ᶜ k W θ′ (substᵖ s p) Rs R′ ⇔ Rel▹ᶜ k W θ p Rs R′
  ▹ᶜ-subst k {θ} {θ′} {s} {W} {p} {Rs} {R′} h =
    mk⇔ (λ g m ne → map-rel (λ {W′} → to (▹-subst k {θ} {θ′} {s} {W′} {p}
                                          {valuesAt m Rs} {⌊ R′ ⌋ m} h))
                      (g m ne))
        (λ g m ne → map-rel (λ {W′} → from (▹-subst k {θ} {θ′} {s} {W′} {p}
                                            {valuesAt m Rs} {⌊ R′ ⌋ m} h))
                      (g m ne))
    where
    map-rel : ∀ {m} {A B : World → Set₁} → (∀ {W′} → A W′ → B W′)
      → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m) × A W′)
      → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m) × B W′)
    map-rel f (W′ , ext , len , a) = W′ , ext , len , f a

mutual
  ◃-subst : ∀ k {θ θ′ s W p D L} → (∀ i → θ i ≡ ⟦ s i ⟧ₙ θ′)
    → Rel◃ k W θ′ (substᵖ s p) D L ⇔ Rel◃ k W θ p D L
  ◃-subst k {L = []} h = ⇔-id
  ◃-subst zero {L = v ∷ L} h = ⇔-id
  ◃-subst (suc k) {p = ★⊑} {L = v ∷ L} h = ⇔-id
  ◃-subst (suc k) {θ} {θ′} {s} {W} {tag G p} {D} {v ∷ L} h =
    ⇔-∘ (⇔-≡ (cong (λ H → Lift₁ (All (IsInjAt H) (v ∷ L))
                           × Rel◃ k W θ′ (substᵖ s p) D (untagᴸ H (v ∷ L)))
                   (⟦substG⟧ᴳ h G)))
        (mk⇔ (λ { (all , rel) →
                    all , to (◃-subst k {θ} {θ′} {s} {W} {p} {D}
                                {untagᴸ (⟦ G ⟧ᴳ θ) (v ∷ L)} h) rel })
             (λ { (all , rel) →
                    all , from (◃-subst k {θ} {θ′} {s} {W} {p} {D}
                                  {untagᴸ (⟦ G ⟧ᴳ θ) (v ∷ L)} h) rel }))
  ◃-subst (suc k) {θ} {θ′} {s} {W} {‵⊑ α} {D} {v ∷ L} h =
    ⇔-≡ (cong (λ σ → Lift₁ (All (IsSealAt σ) (v ∷ L))
                      × Σ[ q ∈ Prec ] (Lift₁ (W ∋ʷ σ ⦂ q)
                          × Rel◃ k W θ₀ q (unsealᴾ σ D)
                                          (unsealᴸ σ (v ∷ L))))
              (⟦substₙ⟧ₙ h α))
  ◃-subst (suc k) {p = 𝔹⊑} {L = v ∷ L} h = ⇔-id
  ◃-subst (suc k) {θ} {θ′} {s} {W} {p ⇒⊑ q} {D} {v ∷ L} h =
    mk⇔ (λ { (all , ν∈ , f) → all , ν∈ ,
               λ L₀ s₀ m W′ ext len E CE rel →
                 to (◃ᶜ-subst k {θ} {θ′} {s} {W′} {q} {D ●[ m ] E}
                       {resultsAt m L₀} h)
                   (f L₀ s₀ m W′ ext len E CE
                      (from (◃-subst k {θ} {θ′} {s} {W′} {p} {E}
                               {argsAt m L₀} h) rel)) })
        (λ { (all , ν∈ , f) → all , ν∈ ,
               λ L₀ s₀ m W′ ext len E CE rel →
                 from (◃ᶜ-subst k {θ} {θ′} {s} {W′} {q} {D ●[ m ] E}
                         {resultsAt m L₀} h)
                   (f L₀ s₀ m W′ ext len E CE
                      (to (◃-subst k {θ} {θ′} {s} {W′} {p} {E}
                             {argsAt m L₀} h) rel)) })
  ◃-subst (suc k) {θ} {θ′} {s} {W} {∀⊑ p} {D} {v ∷ L} h =
    mk⇔ (λ { (all , ν∈ , f) → all , ν∈ ,
               λ σ W′ q′ ext len →
                 to (◃ᶜ-subst k {σ •ᵗ θ} {σ •ᵗ θ′} {extₙ s}
                       {W′ ++ (q′ ∷ [])} {p} {D ◆ σ} {bodiesAt σ (v ∷ L)}
                       (ext-agree {θ} {θ′} {s} {σ} h))
                   (f σ W′ q′ ext len) })
        (λ { (all , ν∈ , f) → all , ν∈ ,
               λ σ W′ q′ ext len →
                 from (◃ᶜ-subst k {σ •ᵗ θ} {σ •ᵗ θ′} {extₙ s}
                         {W′ ++ (q′ ∷ [])} {p} {D ◆ σ} {bodiesAt σ (v ∷ L)}
                         (ext-agree {θ} {θ′} {s} {σ} h))
                   (f σ W′ q′ ext len) })

  ◃ᶜ-subst : ∀ k {θ θ′ s W p R Rs} → (∀ i → θ i ≡ ⟦ s i ⟧ₙ θ′)
    → Rel◃ᶜ k W θ′ (substᵖ s p) R Rs ⇔ Rel◃ᶜ k W θ p R Rs
  ◃ᶜ-subst k {θ} {θ′} {s} {W} {p} {R} {Rs} h =
    mk⇔ (λ { (inj₁ e) → inj₁ e
           ; (inj₂ (ne , g)) → inj₂ (ne , λ m ne′ →
               map-rel (λ {W′} → to (◃-subst k {θ} {θ′} {s} {W′} {p}
                                       {⌊ R ⌋ m} {valuesAt m Rs} h))
                 (g m ne′)) })
        (λ { (inj₁ e) → inj₁ e
           ; (inj₂ (ne , g)) → inj₂ (ne , λ m ne′ →
               map-rel (λ {W′} → from (◃-subst k {θ} {θ′} {s} {W′} {p}
                                         {⌊ R ⌋ m} {valuesAt m Rs} h))
                 (g m ne′)) })
    where
    map-rel : ∀ {m} {A B : World → Set₁} → (∀ {W′} → A W′ → B W′)
      → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m) × A W′)
      → Σ[ W′ ∈ World ] (Lift₁ (W ⊑ʷ W′) × Lift₁ (length W′ ≡ m) × B W′)
    map-rel f (W′ , ext , len , a) = W′ , ext , len , f a

-- the substitution lemma in the form θ′ ⊢ p[s] ⇔ ⟦ s ⟧ θ′ ⊢ p
▹-substᵖ : ∀ θ′ s {W p L D′}
  → (W ∣ θ′ ⊢ substᵖ s p ⊢ L ▹ D′)
    ⇔ (W ∣ (λ i → ⟦ s i ⟧ₙ θ′) ⊢ p ⊢ L ▹ D′)
▹-substᵖ θ′ s {W} {p} {L} {D′} =
  ▹-subst (suc (sizeᴸ L)) {λ i → ⟦ s i ⟧ₙ θ′} {θ′} {s} {W} {p} {L} {D′}
    (λ i → refl)

◃-substᵖ : ∀ θ′ s {W p D L}
  → (W ∣ θ′ ⊢ substᵖ s p ⊢ D ◃ L)
    ⇔ (W ∣ (λ i → ⟦ s i ⟧ₙ θ′) ⊢ p ⊢ D ◃ L)
◃-substᵖ θ′ s {W} {p} {D} {L} =
  ◃-subst (suc (sizeᴸ L)) {λ i → ⟦ s i ⟧ₙ θ′} {θ′} {s} {W} {p} {D} {L}
    (λ i → refl)

-- closing: a derivation under θ is its closed form under any θ′
▹-close : ∀ k θ θ′ {W p L D′}
  → Rel▹ k W θ′ (⟦ p ⟧ᵖ θ) L D′ ⇔ Rel▹ k W θ p L D′
▹-close k θ θ′ {W} {p} {L} {D′} =
  ▹-subst k {θ} {θ′} {λ i → tseal (θ i)} {W} {p} {L} {D′} (λ i → refl)

◃-close : ∀ k θ θ′ {W p D L}
  → Rel◃ k W θ′ (⟦ p ⟧ᵖ θ) D L ⇔ Rel◃ k W θ p D L
◃-close k θ θ′ {W} {p} {D} {L} =
  ◃-subst k {θ} {θ′} {λ i → tseal (θ i)} {W} {p} {D} {L} (λ i → refl)

▹ᶜ-close : ∀ k θ θ′ {W p Rs R′}
  → Rel▹ᶜ k W θ′ (⟦ p ⟧ᵖ θ) Rs R′ ⇔ Rel▹ᶜ k W θ p Rs R′
▹ᶜ-close k θ θ′ {W} {p} {Rs} {R′} =
  ▹ᶜ-subst k {θ} {θ′} {λ i → tseal (θ i)} {W} {p} {Rs} {R′} (λ i → refl)

◃ᶜ-close : ∀ k θ θ′ {W p R Rs}
  → Rel◃ᶜ k W θ′ (⟦ p ⟧ᵖ θ) R Rs ⇔ Rel◃ᶜ k W θ p R Rs
◃ᶜ-close k θ θ′ {W} {p} {R} {Rs} =
  ◃ᶜ-subst k {θ} {θ′} {λ i → tseal (θ i)} {W} {p} {R} {Rs} (λ i → refl)

-- the payloads of injections tagged ⟦ G ⟧ᴳ θ are related as at G
gp-▹ : ∀ k θ G {W L D}
  → Rel▹ k W θ₀ (gp (⟦ G ⟧ᴳ θ)) L D ⇔ Rel▹ k W θ (idᵖ (groundTy G)) L D
gp-▹ k θ (G‵ (tvar i)) {W} {L} {D} =
  ▹-close k θ θ₀ {W} {idᵖ (groundTy (G‵ (tvar i)))} {L} {D}
gp-▹ k θ (G‵ (tseal σ)) {W} {L} {D} =
  ▹-close k θ θ₀ {W} {idᵖ (groundTy (G‵ (tseal σ)))} {L} {D}
gp-▹ k θ G𝔹 {W} {L} {D} = ▹-close k θ θ₀ {W} {idᵖ (groundTy G𝔹)} {L} {D}
gp-▹ k θ G⇒ {W} {L} {D} = ▹-close k θ θ₀ {W} {idᵖ (groundTy G⇒)} {L} {D}
gp-▹ k θ G∀ {W} {L} {D} = ▹-close k θ θ₀ {W} {idᵖ (groundTy G∀)} {L} {D}

gp-◃ : ∀ k θ G {W D L}
  → Rel◃ k W θ₀ (gp (⟦ G ⟧ᴳ θ)) D L ⇔ Rel◃ k W θ (idᵖ (groundTy G)) D L
gp-◃ k θ (G‵ (tvar i)) {W} {D} {L} =
  ◃-close k θ θ₀ {W} {idᵖ (groundTy (G‵ (tvar i)))} {D} {L}
gp-◃ k θ (G‵ (tseal σ)) {W} {D} {L} =
  ◃-close k θ θ₀ {W} {idᵖ (groundTy (G‵ (tseal σ)))} {D} {L}
gp-◃ k θ G𝔹 {W} {D} {L} = ◃-close k θ θ₀ {W} {idᵖ (groundTy G𝔹)} {D} {L}
gp-◃ k θ G⇒ {W} {D} {L} = ◃-close k θ θ₀ {W} {idᵖ (groundTy G⇒)} {D} {L}
gp-◃ k θ G∀ {W} {D} {L} = ◃-close k θ θ₀ {W} {idᵖ (groundTy G∀)} {D} {L}


------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------

entry-args-⊆ : ∀ {U V r s m m′ E} → (U ⟼ r at m) ≡ (V ⟼ s at m′)
  → mem V ⊆ E → mem U ⊆ E
entry-args-⊆ refl V⊆ = V⊆

-- the entries of Lf used by a finite list of results of mem Lf ●[ m ] E
used : ∀ {Lf E m} Rs → (∀ r → r ⋵ Rs → r ∈ᴿ (mem Lf ●[ m ] E))
  → Σ[ P ∈ List Val ]
      (mem P ⊆ mem Lf
       × (∀ e → e ⋵ P → Σ[ U ∈ List Val ] Σ[ r ∈ Res ]
            (e ≡ (U ⟼ r at m) × mem U ⊆ E))
       × (∀ r → r ⋵ Rs → Σ[ U ∈ List Val ] ((U ⟼ r at m) ⋵ P)))
used [] h = [] , (λ e ()) , (λ e ()) , (λ r ())
used {m = m} (r ∷ Rs) h with h r (here refl)
  | used Rs (λ r′ r′∈ → h r′ (there r′∈))
used {m = m} (r ∷ Rs) h | U , e∈ , U⊆ , U≢ | P , P⊆ , Pg , Pc =
  (U ⟼ r at m) ∷ P , c-∷-⊆ e∈ P⊆ , good , cov
  where
  good : ∀ e → e ⋵ ((U ⟼ r at m) ∷ P)
    → Σ[ U′ ∈ List Val ] Σ[ r′ ∈ Res ] (e ≡ (U′ ⟼ r′ at m) × mem U′ ⊆ _)
  good e (here refl) = U , r , refl , U⊆
  good e (there e∈′) = Pg e e∈′
  cov : ∀ r′ → r′ ⋵ (r ∷ Rs)
    → Σ[ U′ ∈ List Val ] ((U′ ⟼ r′ at m) ⋵ ((U ⟼ r at m) ∷ P))
  cov r′ (here refl) = U , here refl
  cov r′ (there r′∈) with Pc r′ r′∈
  cov r′ (there r′∈) | U′ , e∈′ = U′ , there e∈′

app▹ : ∀ {θ W p q Lf F′ E E′ m}
  → W ∣ θ ⊢ p ⇒⊑ q ⊢ Lf ▹ F′ → length W ≡ m → Consistent E′
  → (∀ La → mem La ⊆ E → W ∣ θ ⊢ p ⊢ La ▹ E′)
  → ∀ Rs → (∀ r → r ⋵ Rs → r ∈ᴿ (mem Lf ●[ m ] E))
  → W ∣ θ ⊢ q ⊢ Rs ▹ᶜ (F′ ●[ m ] E′)
app▹ {Lf = []} rel len CE′ hA [] Rs⊆ m₃ ne₃ = ⊥-elim (ne₃ refl)
app▹ {Lf = []} rel len CE′ hA (r ∷ Rs) Rs⊆ m₃ ne₃
  with Rs⊆ r (here refl)
... | U , () , U⊆ , U≢
app▹ {θ} {W} {p} {q} {v ∷ Lf} {F′} {E} {E′} {m}
    (all , ν∈ , f) len CE′ hA Rs Rs⊆ =
  ▹ᶜ-⊆ (sizeᴸ (v ∷ Lf)) (sizeᴸ (v ∷ Lf)) (suc (sizeᴿᴸ Rs))
    {W} {θ} {q} {resultsAt m L₀} {Rs} {F′ ●[ m ] E′}
    (results-bound L₀ (λ x x∈ → size-bound (v ∷ Lf) x (sub-mem s₀ x x∈)))
    (results-sub-< m v Lf s₀) ≤-refl Rs⊆R
    (f L₀ s₀ m W ⊑ʷ-refl len E′ CE′
       (▹-⊆ (suc (sizeᴸ (argsAt m L₀))) (suc (sizeᴸ (argsAt m L₀)))
          (sizeᴸ (v ∷ Lf)) {W} {θ} {p} {argsAt m L₀} {argsAt m L₀} {E′}
          (size-bound (argsAt m L₀)) ≤-refl (args-sub-< m v Lf s₀)
          (λ x x∈ → x∈) (hA (argsAt m L₀) argsOK)))
  where
  U = used {v ∷ Lf} {E} {m} Rs Rs⊆
  P = proj₁ U
  sel = select (v ∷ Lf) P (proj₁ (proj₂ U))
  L₀ = proj₁ sel
  s₀ = proj₁ (proj₂ sel)
  argsOK : mem (argsAt m L₀) ⊆ E
  argsOK u u∈ with args-∈⁻ L₀ u∈
  argsOK u u∈ | U′ , r , e∈ , u∈U
    with proj₁ (proj₂ (proj₂ U)) _ (proj₁ (proj₂ (proj₂ sel)) _ e∈)
  argsOK u u∈ | U′ , r , e∈ , u∈U | V , r′ , eq , V⊆ =
    entry-args-⊆ eq V⊆ u u∈U
  Rs⊆R : ∀ r → r ⋵ Rs → r ⋵ resultsAt m L₀
  Rs⊆R r r∈ with proj₂ (proj₂ (proj₂ U)) r r∈
  Rs⊆R r r∈ | V , e∈P = results-∈⁺ (proj₂ (proj₂ (proj₂ sel)) _ e∈P)

app◃ : ∀ {θ W p q F Lf′ E E′ m}
  → W ∣ θ ⊢ p ⇒⊑ q ⊢ F ◃ Lf′ → length W ≡ m → Consistent E
  → (∀ La′ → mem La′ ⊆ E′ → W ∣ θ ⊢ p ⊢ E ◃ La′)
  → ∀ Rs′ → (∀ r → r ⋵ Rs′ → r ∈ᴿ (mem Lf′ ●[ m ] E′))
  → W ∣ θ ⊢ q ⊢ (F ●[ m ] E) ◃ᶜ Rs′
app◃ {Lf′ = []} rel len CE hA [] Rs⊆ =
  inj₂ (lift (λ ()) , λ m₃ ne₃ → ⊥-elim (ne₃ refl))
app◃ {Lf′ = []} rel len CE hA (r ∷ Rs) Rs⊆ with Rs⊆ r (here refl)
... | U , () , U⊆ , U≢
app◃ {θ} {W} {p} {q} {F} {v ∷ Lf} {E} {E′} {m}
    (all , ν∈ , f) len CE hA Rs Rs⊆ =
  ◃ᶜ-⊆ (sizeᴸ (v ∷ Lf)) (sizeᴸ (v ∷ Lf)) (suc (sizeᴿᴸ Rs))
    {W} {θ} {q} {F ●[ m ] E} {resultsAt m L₀} {Rs}
    (results-bound L₀ (λ x x∈ → size-bound (v ∷ Lf) x (sub-mem s₀ x x∈)))
    (results-sub-< m v Lf s₀) ≤-refl Rs⊆R
    (f L₀ s₀ m W ⊑ʷ-refl len E CE
       (◃-⊆ (suc (sizeᴸ (argsAt m L₀))) (suc (sizeᴸ (argsAt m L₀)))
          (sizeᴸ (v ∷ Lf)) {W} {θ} {p} {E} {argsAt m L₀} {argsAt m L₀}
          (size-bound (argsAt m L₀)) ≤-refl (args-sub-< m v Lf s₀)
          (λ x x∈ → x∈) (hA (argsAt m L₀) argsOK)))
  where
  U = used {v ∷ Lf} {E′} {m} Rs Rs⊆
  P = proj₁ U
  sel = select (v ∷ Lf) P (proj₁ (proj₂ U))
  L₀ = proj₁ sel
  s₀ = proj₁ (proj₂ sel)
  argsOK : mem (argsAt m L₀) ⊆ E′
  argsOK u u∈ with args-∈⁻ L₀ u∈
  argsOK u u∈ | U′ , r , e∈ , u∈U
    with proj₁ (proj₂ (proj₂ U)) _ (proj₁ (proj₂ (proj₂ sel)) _ e∈)
  argsOK u u∈ | U′ , r , e∈ , u∈U | V , r′ , eq , V⊆ =
    entry-args-⊆ eq V⊆ u u∈U
  Rs⊆R : ∀ r → r ⋵ Rs → r ⋵ resultsAt m L₀
  Rs⊆R r r∈ with proj₂ (proj₂ (proj₂ U)) r r∈
  Rs⊆R r r∈ | V , e∈P = results-∈⁺ (proj₂ (proj₂ (proj₂ sel)) _ e∈P)


------------------------------------------------------------------------
-- Bind
------------------------------------------------------------------------

ne-head : ∀ {A : Set} (X : List A) → X ≢ [] → Σ[ x ∈ A ] (x ⋵ X)
ne-head [] ne = ⊥-elim (ne refl)
ne-head (x ∷ X) ne = x , here refl

mapRet : ℕ → List Val → List Res
mapRet m [] = []
mapRet m (x ∷ L) = ret x m ∷ mapRet m L

mapRet-∈ : ∀ {x m L} → x ⋵ L → ret x m ⋵ mapRet m L
mapRet-∈ (here refl) = here refl
mapRet-∈ (there x∈) = there (mapRet-∈ x∈)

mapRet-∈⁻ : ∀ {r m} L → r ⋵ mapRet m L → Σ[ x ∈ Val ] (r ≡ ret x m × x ⋵ L)
mapRet-∈⁻ (x ∷ L) (here refl) = x , refl , here refl
mapRet-∈⁻ (x ∷ L) (there r∈) with mapRet-∈⁻ L r∈
mapRet-∈⁻ (x ∷ L) (there r∈) | y , eq , y∈ = y , eq , there y∈

-- the inputs from S that a result of a group of S ≫= Kc uses
SupG : (𝒱 → ℕ → ℛ) → Res → List Res → Set
SupG Kc r Qs =
  Σ[ m₁ ∈ ℕ ] Σ[ c ∈ Val ] Σ[ Lr ∈ List Val ]
    (ret c m₁ ⋵ Qs × (∀ x → x ⋵ Lr → ret x m₁ ⋵ Qs)
     × r ∈ᴿ Kc (mem Lr) m₁)

SupG-mono : ∀ {Kc r Qs Qs′} → (∀ q → q ⋵ Qs → q ⋵ Qs′)
  → SupG Kc r Qs → SupG Kc r Qs′
SupG-mono Q⊆ (m₁ , c , Lr , c∈ , L∈ , r∈) =
  m₁ , c , Lr , Q⊆ _ c∈ , (λ x x∈ → Q⊆ _ (L∈ x x∈)) , r∈

gatherG : ∀ {S : ℛ} {Kc : 𝒱 → ℕ → ℛ} → (∀ m → c-FinR (λ X → Kc X m))
  → ∀ Rs
  → (∀ r → r ⋵ Rs
       → Σ[ m₁ ∈ ℕ ] (Conv (⌊ S ⌋ m₁) × r ∈ᴿ Kc (⌊ S ⌋ m₁) m₁))
  → Σ[ Qs ∈ List Res ] ((∀ q → q ⋵ Qs → q ∈ᴿ S)
                        × (∀ r → r ⋵ Rs → SupG Kc r Qs))
gatherG finK [] h = [] , (λ q ()) , (λ r ())
gatherG {S} {Kc} finK (r ∷ Rs) h
  with h r (here refl) | gatherG {S} {Kc} finK Rs (λ r′ r′∈ → h r′ (there r′∈))
gatherG {S} {Kc} finK (r ∷ Rs) h | m₁ , (c , c∈) , r∈ | Q₂ , Q₂⊆ , S₂
  with finK m₁ (⌊ S ⌋ m₁) r r∈
gatherG {S} {Kc} finK (r ∷ Rs) h | m₁ , (c , c∈) , r∈ | Q₂ , Q₂⊆ , S₂
  | Lr , Lr⊆ , r∈′ =
  Q₁ ++ Q₂ , Q⊆ , sup
  where
  Q₁ = ret c m₁ ∷ mapRet m₁ Lr
  Q₁⊆ : ∀ q → q ⋵ Q₁ → q ∈ᴿ S
  Q₁⊆ q (here refl) = c∈
  Q₁⊆ q (there q∈) with mapRet-∈⁻ Lr q∈
  Q₁⊆ q (there q∈) | x , refl , x∈ = Lr⊆ x x∈
  Q⊆ : ∀ q → q ⋵ (Q₁ ++ Q₂) → q ∈ᴿ S
  Q⊆ q q∈ with ∈-++⁻ Q₁ q∈
  Q⊆ q q∈ | inj₁ q∈₁ = Q₁⊆ q q∈₁
  Q⊆ q q∈ | inj₂ q∈₂ = Q₂⊆ q q∈₂
  sup : ∀ r′ → r′ ⋵ (r ∷ Rs) → SupG Kc r′ (Q₁ ++ Q₂)
  sup r′ (here refl) =
    m₁ , c , Lr , ∈-++⁺ˡ {xs = Q₁} {ys = Q₂} (here refl) ,
    (λ x x∈ → ∈-++⁺ˡ {xs = Q₁} {ys = Q₂} (there (mapRet-∈ x∈))) , r∈′
  sup r′ (there r′∈) =
    SupG-mono {Kc} {r′} {Q₂} {Q₁ ++ Q₂} (λ q q∈ → ∈-++⁺ʳ Q₁ q∈) (S₂ r′ r′∈)

bind▹ : ∀ {θ θ′ W p q R R′ K K′}
  → (∀ m → c-FinR (λ X → K X m)) → (∀ m → c-MonoR (λ X → K X m))
  → Consistentᴿ R′
  → (∀ Rs → (∀ r → r ⋵ Rs → r ∈ᴿ R) → W ∣ θ ⊢ p ⊢ Rs ▹ᶜ R′)
  → (∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
       → ∀ L → W₁ ∣ θ ⊢ p ⊢ L ▹ ⌊ R′ ⌋ m₁
       → ∀ Rs → (∀ r → r ⋵ Rs → r ∈ᴿ K (mem L) m₁)
       → W₁ ∣ θ′ ⊢ q ⊢ Rs ▹ᶜ K′ (⌊ R′ ⌋ m₁) m₁)
  → ∀ Rs → (∀ r → r ⋵ Rs → r ∈ᴿ (R ≫= K))
  → W ∣ θ′ ⊢ q ⊢ Rs ▹ᶜ (R′ ≫= K′)
bind▹ {θ} {θ′} {W} {p} {q} {R} {R′} {K} {K′} finK monoK CR hR hK Rs Rs⊆
    m ne = result
  where
  Ys = valuesAt m Rs
  Rs₁ = mapRet m Ys
  grp : ∀ r → r ⋵ Rs₁
    → Σ[ m₁ ∈ ℕ ] (Conv (⌊ R ⌋ m₁) × r ∈ᴿ K (⌊ R ⌋ m₁) m₁)
  grp r r∈ with mapRet-∈⁻ Ys r∈
  grp r r∈ | y , refl , y∈ with Rs⊆ _ (values-∈⁻ Rs y∈)
  grp r r∈ | y , refl , y∈ | inj₁ (() , e)
  grp r r∈ | y , refl , y∈ | inj₂ g = g
  gat = gatherG {R} {K} finK Rs₁ grp
  Qs = proj₁ gat
  H : W ∣ θ ⊢ p ⊢ Qs ▹ᶜ R′
  H = hR Qs (proj₁ (proj₂ gat))
  SQ = proj₂ (proj₂ gat)
  y₀ = proj₁ (ne-head Ys ne)
  y₀∈ = proj₂ (ne-head Ys ne)
  S₀ = SQ (ret y₀ m) (mapRet-∈ y₀∈)
  m₁ = proj₁ S₀
  c₀ = proj₁ (proj₂ S₀)
  c₀∈ = proj₁ (proj₂ (proj₂ (proj₂ S₀)))
  convAt : ∀ k c → ret c k ⋵ Qs → Conv (⌊ R′ ⌋ k)
  convAt k c c∈ = ▹ᶜ-conv (suc (sizeᴿᴸ Qs)) {W} {θ} {p} {Qs} {R′} c∈ H
  sameCtr : ∀ k c → ret c k ⋵ Qs → k ≡ m₁
  sameCtr k c c∈ =
    proj₁ (CR (ret (proj₁ (convAt k c c∈)) k)
              (ret (proj₁ (convAt m₁ c₀ c₀∈)) m₁)
              (proj₂ (convAt k c c∈)) (proj₂ (convAt m₁ c₀ c₀∈)))
  L = valuesAt m₁ Qs
  Rs₁⊆ : ∀ r → r ⋵ Rs₁ → r ∈ᴿ K (mem L) m₁
  Rs₁⊆ r r∈ with SQ r r∈
  Rs₁⊆ r r∈ | k , c , Lr , c∈ , L∈ , r∈′ with sameCtr k c c∈
  Rs₁⊆ r r∈ | k , c , Lr , c∈ , L∈ , r∈′ | refl =
    monoK m₁ (λ x x∈ → values-∈⁺ (L∈ x x∈)) r r∈′
  result : Σ[ W₂ ∈ World ] (Lift₁ (W ⊑ʷ W₂) × Lift₁ (length W₂ ≡ m)
             × Rel▹ (suc (sizeᴿᴸ Rs)) W₂ θ′ q Ys (⌊ R′ ≫= K′ ⌋ m))
  result with H m₁ (nonempty (values-∈⁺ {Rs = Qs} c₀∈))
  result | W₁ , lift ext₁ , lift len₁ , rel₁
    with hK m₁ W₁ ext₁ len₁ L
           (▹-fuel (suc (sizeᴿᴸ Qs)) (suc (sizeᴸ L))
              {W₁} {θ} {p} {L} {⌊ R′ ⌋ m₁}
              (s≤s (values-≤ m₁ Qs)) ≤-refl rel₁)
           Rs₁ Rs₁⊆ m (nonempty (values-∈⁺ {Rs = Rs₁} (mapRet-∈ y₀∈)))
  result | W₁ , lift ext₁ , lift len₁ , rel₁ | W₂ , lift ext₂ , len₂ , rel₂ =
    W₂ , lift (⊑ʷ-trans ext₁ ext₂) , len₂ ,
    ▹-mono (suc (sizeᴿᴸ Rs)) {W₂} {θ′} {q} {Ys}
      {⌊ K′ (⌊ R′ ⌋ m₁) m₁ ⌋ m} {⌊ R′ ≫= K′ ⌋ m}
      (λ x x∈ → inj₂ (m₁ , convAt m₁ c₀ c₀∈ , x∈))
      (▹-⊆ (suc (sizeᴿᴸ Rs₁)) (suc (sizeᴿᴸ Rs₁)) (suc (sizeᴿᴸ Rs))
         {W₂} {θ′} {q} {valuesAt m Rs₁} {Ys} {⌊ K′ (⌊ R′ ⌋ m₁) m₁ ⌋ m}
         (values-bound Rs₁ (size-boundᴿ Rs₁))
         (s≤s (values-≤ m Rs₁)) (s≤s (values-≤ m Rs))
         (λ y y∈ → values-∈⁺ (mapRet-∈ y∈)) rel₂)

-- either some result comes from an error of the first computation, or
-- each comes from a group
split-err : ∀ {R′ : ℛ} {K′ : 𝒱 → ℕ → ℛ} Rs
  → (∀ r → r ⋵ Rs → r ∈ᴿ (R′ ≫= K′))
  → err ∈ᴿ R′
    ⊎ (∀ r → r ⋵ Rs
         → Σ[ m₁ ∈ ℕ ] (Conv (⌊ R′ ⌋ m₁) × r ∈ᴿ K′ (⌊ R′ ⌋ m₁) m₁))
split-err [] h = inj₂ (λ r ())
split-err (r ∷ Rs) h with h r (here refl)
split-err (r ∷ Rs) h | inj₁ (eq , e) = inj₁ e
split-err {R′} {K′} (r ∷ Rs) h | inj₂ g
  with split-err {R′} {K′} Rs (λ r′ r′∈ → h r′ (there r′∈))
split-err (r ∷ Rs) h | inj₂ g | inj₁ e = inj₁ e
split-err {R′} {K′} (r ∷ Rs) h | inj₂ g | inj₂ G = inj₂ all
  where
  all : ∀ r′ → r′ ⋵ (r ∷ Rs)
    → Σ[ m₁ ∈ ℕ ] (Conv (⌊ R′ ⌋ m₁) × r′ ∈ᴿ K′ (⌊ R′ ⌋ m₁) m₁)
  all r′ (here refl) = g
  all r′ (there r′∈) = G r′ r′∈

bind◃ : ∀ {θ θ′ W p q R R′ K K′}
  → (∀ m → c-FinR (λ X → K′ X m)) → (∀ m → c-MonoR (λ X → K′ X m))
  → Consistentᴿ R
  → (∀ Rs′ → (∀ r → r ⋵ Rs′ → r ∈ᴿ R′) → W ∣ θ ⊢ p ⊢ R ◃ᶜ Rs′)
  → (∀ m₁ W₁ → W ⊑ʷ W₁ → length W₁ ≡ m₁
       → ∀ L′ → W₁ ∣ θ ⊢ p ⊢ ⌊ R ⌋ m₁ ◃ L′
       → ∀ Rs′ → (∀ r → r ⋵ Rs′ → r ∈ᴿ K′ (mem L′) m₁)
       → W₁ ∣ θ′ ⊢ q ⊢ K (⌊ R ⌋ m₁) m₁ ◃ᶜ Rs′)
  → ∀ Rs′ → (∀ r → r ⋵ Rs′ → r ∈ᴿ (R′ ≫= K′))
  → W ∣ θ′ ⊢ q ⊢ (R ≫= K) ◃ᶜ Rs′
bind◃ finK monoK CR hR hK [] Rs⊆ =
  inj₂ (lift (λ ()) , λ m ne → ⊥-elim (ne refl))
bind◃ {θ} {θ′} {W} {p} {q} {R} {R′} {K} {K′} finK monoK CR hR hK
    (r₀ ∷ Rs′) Rs⊆ with split-err {R′} {K′} (r₀ ∷ Rs′) Rs⊆
bind◃ {θ} {θ′} {W} {p} {q} {R} {R′} {K} {K′} finK monoK CR hR hK
    (r₀ ∷ Rs′) Rs⊆ | inj₁ e =
  fromErr (hR (err ∷ []) (λ { r (here refl) → e }))
  where
  fromErr : W ∣ θ ⊢ p ⊢ R ◃ᶜ (err ∷ [])
    → W ∣ θ′ ⊢ q ⊢ (R ≫= K) ◃ᶜ (r₀ ∷ Rs′)
  fromErr (inj₁ (lift e′)) = inj₁ (lift (c-≫=-err {R} {K} e′))
  fromErr (inj₂ (lift ne , h)) = ⊥-elim (ne (here refl))
bind◃ {θ} {θ′} {W} {p} {q} {R} {R′} {K} {K′} finK monoK CR hR hK
    (r₀ ∷ Rs′) Rs⊆ | inj₂ grp = body
  where
  Rs = r₀ ∷ Rs′
  gat = gatherG {R′} {K′} finK Rs grp
  Qs = proj₁ gat
  SQ = proj₂ (proj₂ gat)
  S₀ = SQ r₀ (here refl)
  m₁ = proj₁ S₀
  c₀ = proj₁ (proj₂ S₀)
  c₀∈ = proj₁ (proj₂ (proj₂ (proj₂ S₀)))
  L′ = valuesAt m₁ Qs
  body : W ∣ θ′ ⊢ q ⊢ (R ≫= K) ◃ᶜ Rs
  body with hR Qs (proj₁ (proj₂ gat))
  body | inj₁ (lift e) = inj₁ (lift (c-≫=-err {R} {K} e))
  body | inj₂ (lift neQ , HQ) = rest
    where
    convAt : ∀ k c → ret c k ⋵ Qs → Conv (⌊ R ⌋ k)
    convAt k c c∈ with HQ k (nonempty (values-∈⁺ {Rs = Qs} c∈))
    convAt k c c∈ | W₁ , ext₁ , len₁ , rel₁ =
      ◃-conv (suc (sizeᴿᴸ Qs)) (values-∈⁺ {Rs = Qs} c∈) rel₁
    sameCtr : ∀ k c → ret c k ⋵ Qs → k ≡ m₁
    sameCtr k c c∈ =
      proj₁ (CR (ret (proj₁ (convAt k c c∈)) k)
                (ret (proj₁ (convAt m₁ c₀ c₀∈)) m₁)
                (proj₂ (convAt k c c∈)) (proj₂ (convAt m₁ c₀ c₀∈)))
    Rs⊆′ : ∀ r → r ⋵ Rs → r ∈ᴿ K′ (mem L′) m₁
    Rs⊆′ r r∈ with SQ r r∈
    Rs⊆′ r r∈ | k , c , Lr , c∈ , L∈ , r∈′ with sameCtr k c c∈
    Rs⊆′ r r∈ | k , c , Lr , c∈ , L∈ , r∈′ | refl =
      monoK m₁ (λ x x∈ → values-∈⁺ (L∈ x x∈)) r r∈′
    incl : K (⌊ R ⌋ m₁) m₁ ⊆ᴿ (R ≫= K)
    incl = c-≫=-group {R} {K} {m₁} (convAt m₁ c₀ c₀∈)
    rest : W ∣ θ′ ⊢ q ⊢ (R ≫= K) ◃ᶜ Rs
    rest with HQ m₁ (nonempty (values-∈⁺ {Rs = Qs} c₀∈))
    rest | W₁ , lift ext₁ , lift len₁ , rel₁
      with hK m₁ W₁ ext₁ len₁ L′
             (◃-fuel (suc (sizeᴿᴸ Qs)) (suc (sizeᴸ L′))
                {W₁} {θ} {p} {⌊ R ⌋ m₁} {L′}
                (s≤s (values-≤ m₁ Qs)) ≤-refl rel₁)
             Rs Rs⊆′
    rest | W₁ , lift ext₁ , lift len₁ , rel₁ | inj₁ (lift e) =
      inj₁ (lift (incl err e))
    rest | W₁ , lift ext₁ , lift len₁ , rel₁ | inj₂ (ne , h) =
      inj₂ (ne , h′)
      where
      h′ : ∀ m → valuesAt m Rs ≢ []
        → Σ[ W₂ ∈ World ] (Lift₁ (W ⊑ʷ W₂) × Lift₁ (length W₂ ≡ m)
            × Rel◃ (suc (sizeᴿᴸ Rs)) W₂ θ′ q (⌊ R ≫= K ⌋ m)
                (valuesAt m Rs))
      h′ m ne₃ with h m ne₃
      h′ m ne₃ | W₂ , lift ext₂ , len₂ , rel₂ =
        W₂ , lift (⊑ʷ-trans ext₁ ext₂) , len₂ ,
        ◃-mono (suc (sizeᴿᴸ Rs)) {W₂} {θ′} {q}
          {⌊ K (⌊ R ⌋ m₁) m₁ ⌋ m} {⌊ R ≫= K ⌋ m} {valuesAt m Rs}
          (c-⌊⌋-mono incl) rel₂
