module proof.NarrowWidenIsomorphism where

-- File Charter:
--   * Establishes derivation isomorphisms from GTSFImp type imprecision to
--     polarized widening and narrowing.
--   * Proves both round trips for each direction, not merely equivalence of
--     inhabitation or equality of endpoints.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
import Imprecision as I
open I using (ImpEnv)
open import NarrowWiden
open import DerivationIso

mutual
  imprecision→widening : ∀ {Δ μ} {A B : Ty Δ}
    → I._⊢_⊑_ μ A B
    → Widening μ A B
  imprecision→widening I.★⊑★ = w-id★
  imprecision→widening I.ι⊑ι = w-idι
  imprecision→widening I.X⊑X = w-idˣ
  imprecision→widening (I.⇒⊑⇒ p q) =
    w-⇒ (imprecision→narrowing p) (imprecision→widening q)
  imprecision→widening (I.∀⊑∀ p) = w-∀ (imprecision→widening p)
  imprecision→widening (I.⇒⊑★ p q) =
    w-⇒★ (imprecision→narrowing p) (imprecision→widening q)
  imprecision→widening I.ι⊑★ = w-ι★
  imprecision→widening (I.X⊑★ eq) = w-X★ eq
  imprecision→widening (I.∀⊑ nonvar occurs p) =
    w-∀-elim nonvar occurs (imprecision→widening p)
  imprecision→widening I.∀★⊑★ = w-∀★-elim
  imprecision→widening (I.∀⊑★ nonstar p) =
    w-∀★ nonstar (imprecision→widening p)
  imprecision→widening I.bot-elim = w-bot-elim
  imprecision→widening I.bot⊑★ = w-bot★

  imprecision→narrowing : ∀ {Δ μ} {A B : Ty Δ}
    → I._⊢_⊑_ μ A B
    → Narrowing μ B A
  imprecision→narrowing I.★⊑★ = n-id★
  imprecision→narrowing I.ι⊑ι = n-idι
  imprecision→narrowing I.X⊑X = n-idˣ
  imprecision→narrowing (I.⇒⊑⇒ p q) =
    n-⇒ (imprecision→widening p) (imprecision→narrowing q)
  imprecision→narrowing (I.∀⊑∀ p) = n-∀ (imprecision→narrowing p)
  imprecision→narrowing (I.⇒⊑★ p q) =
    n-★⇒ (imprecision→widening p) (imprecision→narrowing q)
  imprecision→narrowing I.ι⊑★ = n-★ι
  imprecision→narrowing (I.X⊑★ eq) = n-★X eq
  imprecision→narrowing (I.∀⊑ nonvar occurs p) =
    n-∀-intro nonvar occurs (imprecision→narrowing p)
  imprecision→narrowing I.∀★⊑★ = n-∀★-intro
  imprecision→narrowing (I.∀⊑★ nonstar p) =
    n-★∀ nonstar (imprecision→narrowing p)
  imprecision→narrowing I.bot-elim = n-bot-intro
  imprecision→narrowing I.bot⊑★ = n-★bot

mutual
  widening→imprecision : ∀ {Δ μ} {A B : Ty Δ}
    → Widening μ A B
    → I._⊢_⊑_ μ A B
  widening→imprecision w-id★ = I.★⊑★
  widening→imprecision w-idι = I.ι⊑ι
  widening→imprecision w-idˣ = I.X⊑X
  widening→imprecision (w-⇒ p q) =
    I.⇒⊑⇒ (narrowing→imprecision p) (widening→imprecision q)
  widening→imprecision (w-∀ p) = I.∀⊑∀ (widening→imprecision p)
  widening→imprecision (w-⇒★ p q) =
    I.⇒⊑★ (narrowing→imprecision p) (widening→imprecision q)
  widening→imprecision w-ι★ = I.ι⊑★
  widening→imprecision (w-X★ eq) = I.X⊑★ eq
  widening→imprecision (w-∀-elim nonvar occurs p) =
    I.∀⊑ nonvar occurs (widening→imprecision p)
  widening→imprecision w-∀★-elim = I.∀★⊑★
  widening→imprecision (w-∀★ nonstar p) =
    I.∀⊑★ nonstar (widening→imprecision p)
  widening→imprecision w-bot-elim = I.bot-elim
  widening→imprecision w-bot★ = I.bot⊑★

  narrowing→imprecision : ∀ {Δ μ} {A B : Ty Δ}
    → Narrowing μ B A
    → I._⊢_⊑_ μ A B
  narrowing→imprecision n-id★ = I.★⊑★
  narrowing→imprecision n-idι = I.ι⊑ι
  narrowing→imprecision n-idˣ = I.X⊑X
  narrowing→imprecision (n-⇒ p q) =
    I.⇒⊑⇒ (widening→imprecision p) (narrowing→imprecision q)
  narrowing→imprecision (n-∀ p) = I.∀⊑∀ (narrowing→imprecision p)
  narrowing→imprecision (n-★⇒ p q) =
    I.⇒⊑★ (widening→imprecision p) (narrowing→imprecision q)
  narrowing→imprecision n-★ι = I.ι⊑★
  narrowing→imprecision (n-★X eq) = I.X⊑★ eq
  narrowing→imprecision (n-∀-intro nonvar occurs p) =
    I.∀⊑ nonvar occurs (narrowing→imprecision p)
  narrowing→imprecision n-∀★-intro = I.∀★⊑★
  narrowing→imprecision (n-★∀ nonstar p) =
    I.∀⊑★ nonstar (narrowing→imprecision p)
  narrowing→imprecision n-bot-intro = I.bot-elim
  narrowing→imprecision n-★bot = I.bot⊑★

mutual
  widening-after-imprecision : ∀ {Δ μ} {A B : Ty Δ}
    → (p : I._⊢_⊑_ μ A B)
    → widening→imprecision (imprecision→widening p) ≡ p
  widening-after-imprecision I.★⊑★ = refl
  widening-after-imprecision I.ι⊑ι = refl
  widening-after-imprecision I.X⊑X = refl
  widening-after-imprecision (I.⇒⊑⇒ p q)
    rewrite narrowing-after-imprecision p
          | widening-after-imprecision q = refl
  widening-after-imprecision (I.∀⊑∀ p)
    rewrite widening-after-imprecision p = refl
  widening-after-imprecision (I.⇒⊑★ p q)
    rewrite narrowing-after-imprecision p
          | widening-after-imprecision q = refl
  widening-after-imprecision I.ι⊑★ = refl
  widening-after-imprecision (I.X⊑★ eq) = refl
  widening-after-imprecision (I.∀⊑ nonvar occurs p)
    rewrite widening-after-imprecision p = refl
  widening-after-imprecision I.∀★⊑★ = refl
  widening-after-imprecision (I.∀⊑★ nonstar p)
    rewrite widening-after-imprecision p = refl
  widening-after-imprecision I.bot-elim = refl
  widening-after-imprecision I.bot⊑★ = refl

  narrowing-after-imprecision : ∀ {Δ μ} {A B : Ty Δ}
    → (p : I._⊢_⊑_ μ A B)
    → narrowing→imprecision (imprecision→narrowing p) ≡ p
  narrowing-after-imprecision I.★⊑★ = refl
  narrowing-after-imprecision I.ι⊑ι = refl
  narrowing-after-imprecision I.X⊑X = refl
  narrowing-after-imprecision (I.⇒⊑⇒ p q)
    rewrite widening-after-imprecision p
          | narrowing-after-imprecision q = refl
  narrowing-after-imprecision (I.∀⊑∀ p)
    rewrite narrowing-after-imprecision p = refl
  narrowing-after-imprecision (I.⇒⊑★ p q)
    rewrite widening-after-imprecision p
          | narrowing-after-imprecision q = refl
  narrowing-after-imprecision I.ι⊑★ = refl
  narrowing-after-imprecision (I.X⊑★ eq) = refl
  narrowing-after-imprecision (I.∀⊑ nonvar occurs p)
    rewrite narrowing-after-imprecision p = refl
  narrowing-after-imprecision I.∀★⊑★ = refl
  narrowing-after-imprecision (I.∀⊑★ nonstar p)
    rewrite narrowing-after-imprecision p = refl
  narrowing-after-imprecision I.bot-elim = refl
  narrowing-after-imprecision I.bot⊑★ = refl

mutual
  imprecision-after-widening : ∀ {Δ μ} {A B : Ty Δ}
    → (w : Widening μ A B)
    → imprecision→widening (widening→imprecision w) ≡ w
  imprecision-after-widening w-id★ = refl
  imprecision-after-widening w-idι = refl
  imprecision-after-widening w-idˣ = refl
  imprecision-after-widening (w-⇒ p q)
    rewrite imprecision-after-narrowing p
          | imprecision-after-widening q = refl
  imprecision-after-widening (w-∀ p)
    rewrite imprecision-after-widening p = refl
  imprecision-after-widening (w-⇒★ p q)
    rewrite imprecision-after-narrowing p
          | imprecision-after-widening q = refl
  imprecision-after-widening w-ι★ = refl
  imprecision-after-widening (w-X★ eq) = refl
  imprecision-after-widening (w-∀-elim nonvar occurs p)
    rewrite imprecision-after-widening p = refl
  imprecision-after-widening w-∀★-elim = refl
  imprecision-after-widening (w-∀★ nonstar p)
    rewrite imprecision-after-widening p = refl
  imprecision-after-widening w-bot-elim = refl
  imprecision-after-widening w-bot★ = refl

  imprecision-after-narrowing : ∀ {Δ μ} {A B : Ty Δ}
    → (n : Narrowing μ B A)
    → imprecision→narrowing (narrowing→imprecision n) ≡ n
  imprecision-after-narrowing n-id★ = refl
  imprecision-after-narrowing n-idι = refl
  imprecision-after-narrowing n-idˣ = refl
  imprecision-after-narrowing (n-⇒ p q)
    rewrite imprecision-after-widening p
          | imprecision-after-narrowing q = refl
  imprecision-after-narrowing (n-∀ p)
    rewrite imprecision-after-narrowing p = refl
  imprecision-after-narrowing (n-★⇒ p q)
    rewrite imprecision-after-widening p
          | imprecision-after-narrowing q = refl
  imprecision-after-narrowing n-★ι = refl
  imprecision-after-narrowing (n-★X eq) = refl
  imprecision-after-narrowing (n-∀-intro nonvar occurs p)
    rewrite imprecision-after-narrowing p = refl
  imprecision-after-narrowing n-∀★-intro = refl
  imprecision-after-narrowing (n-★∀ nonstar p)
    rewrite imprecision-after-narrowing p = refl
  imprecision-after-narrowing n-bot-intro = refl
  imprecision-after-narrowing n-★bot = refl

imprecision-widening-iso : ∀ {Δ μ} {A B : Ty Δ}
  → DerivationIso (I._⊢_⊑_ μ A B) (Widening μ A B)
imprecision-widening-iso =
  derivation-iso imprecision→widening widening→imprecision
    widening-after-imprecision imprecision-after-widening

imprecision-narrowing-iso : ∀ {Δ μ} {A B : Ty Δ}
  → DerivationIso (I._⊢_⊑_ μ A B) (Narrowing μ B A)
imprecision-narrowing-iso =
  derivation-iso imprecision→narrowing narrowing→imprecision
    narrowing-after-imprecision imprecision-after-narrowing
