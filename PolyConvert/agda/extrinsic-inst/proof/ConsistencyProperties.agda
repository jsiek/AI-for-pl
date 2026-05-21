module proof.ConsistencyProperties where

-- File Charter:
--   * Properties of the Consistency relation

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Properties using (length-replicate; ++-identityʳ)
open import Data.Nat using (ℕ; _+_; _<_; _≤_; zero; suc; z<s; s<s; z≤n; s≤s)
open import Data.Nat.Properties using (suc-injective; m<n⇒m<1+n)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Consistency
open import Types
open import proof.TypeProperties
  using
    ( raiseVarFrom-injective
    ; raiseVarFrom-<-inv
    ; rename-raise-ext
    ; rename-raise-⇑ᵗ
    ; renameᵗ-ground-id
    )

cong-~ :
  ∀ {Γ A A′ B B′} →
  A ≡ A′ →
  B ≡ B′ →
  Γ ⊢ A ~ B →
  Γ ⊢ A′ ~ B′
cong-~ refl refl h = h

swapMode : CMode → CMode
swapMode X~★ = ★~X
swapMode ★~X = X~★
swapMode X~X = X~X
swapMode neither = neither

swapCCtx : CCtx → CCtx
swapCCtx [] = []
swapCCtx (m ∷ Γ) = swapMode m ∷ swapCCtx Γ

swap∋ᶜ :
  ∀ {Γ X m} →
  Γ ∋ᶜ X ∶ m →
  swapCCtx Γ ∋ᶜ X ∶ swapMode m
swap∋ᶜ here = here
swap∋ᶜ (there x∈) = there (swap∋ᶜ x∈)

length-swapCCtx :
  ∀ Γ →
  length (swapCCtx Γ) ≡ length Γ
length-swapCCtx [] = refl
length-swapCCtx (m ∷ Γ) = cong suc (length-swapCCtx Γ)

renameᵗ-Non★-inv : ∀ {ρ A} → Non★ (renameᵗ ρ A) → Non★ A
renameᵗ-Non★-inv {A = ＇ X} non★-＇ = non★-＇
renameᵗ-Non★-inv {A = ｀ α} non★-｀ = non★-｀
renameᵗ-Non★-inv {A = ‵ ι} non★-‵ = non★-‵
renameᵗ-Non★-inv {A = A ⇒ B} non★-⇒ = non★-⇒
renameᵗ-Non★-inv {A = `∀ A} non★-∀ = non★-∀

renameᵗ-Non∀-inv : ∀ {ρ A} → Non∀ (renameᵗ ρ A) → Non∀ A
renameᵗ-Non∀-inv {A = ＇ X} non∀-＇ = non∀-＇
renameᵗ-Non∀-inv {A = ｀ α} non∀-｀ = non∀-｀
renameᵗ-Non∀-inv {A = ‵ ι} non∀-‵ = non∀-‵
renameᵗ-Non∀-inv {A = ★} non∀-★ = non∀-★
renameᵗ-Non∀-inv {A = A ⇒ B} non∀-⇒ = non∀-⇒

------------------------------------------------------------------------
-- Consistency is Symmetric
------------------------------------------------------------------------

~-sym :
  ∀ {Γ A B} →
  Γ ⊢ A ~ B →
  swapCCtx Γ ⊢ B ~ A
~-sym ★-~-★ = ★-~-★
~-sym (X-~-X x∈) = X-~-X (swap∋ᶜ x∈)
~-sym ι-~-ι = ι-~-ι
~-sym (⇒-~-⇒ A~A′ B~B′) =
  ⇒-~-⇒ (~-sym A~A′) (~-sym B~B′)
~-sym (∀-~-∀ A~B) = ∀-~-∀ (~-sym A~B)
~-sym (A-~-★ n★ n∀ g A~G) = ★-~-B n★ n∀ g (~-sym A~G)
~-sym (★-~-B n★ n∀ h H~B) = A-~-★ n★ n∀ h (~-sym H~B)
~-sym (νX-~-★ x∈) = ★-~-νX (swap∋ᶜ x∈)
~-sym (★-~-νX x∈) = νX-~-★ (swap∋ᶜ x∈)
~-sym {Γ = Γ} (∀-~-B {B = B} wfB A~⇑B) =
  A-~-∀
    (subst (λ n → WfTy n 0 B) (sym (length-swapCCtx Γ)) wfB)
    (~-sym A~⇑B)
~-sym {Γ = Γ} (A-~-∀ {A = A} wfA ⇑A~B) =
  ∀-~-B
    (subst (λ n → WfTy n 0 A) (sym (length-swapCCtx Γ)) wfA)
    (~-sym ⇑A~B)


------------------------------------------------------------------------
-- Consistency Context Helpers
------------------------------------------------------------------------

length-leftICtx : ∀ Γ → length (leftICtx Γ) ≡ length Γ
length-leftICtx [] = refl
length-leftICtx (m ∷ Γ) = cong suc (length-leftICtx Γ)

length-rightICtx : ∀ Γ → length (rightICtx Γ) ≡ length Γ
length-rightICtx [] = refl
length-rightICtx (m ∷ Γ) = cong suc (length-rightICtx Γ)

length-extend-X~X[] : ∀ Δ → length (extend-X~X Δ []) ≡ Δ
length-extend-X~X[] Δ
  rewrite ++-identityʳ (replicate Δ X~X)
        | (length-replicate Δ {X~X}) = refl

lookup-extend-X~X[] :
  ∀ {Δ X} →
  X < Δ →
  extend-X~X Δ [] ∋ᶜ X ∶ X~X
lookup-extend-X~X[] {Δ = zero} ()
lookup-extend-X~X[] {Δ = suc Δ} {X = zero} z<s = here
lookup-extend-X~X[] {Δ = suc Δ} {X = suc X} (s<s X<Δ) =
  there (lookup-extend-X~X[] X<Δ)

extend-X~X-length-split :
  (Φ Γ : CCtx) →
  extend-X~X (length (Φ ++ Γ)) [] ≡ extend-X~X (length Φ) [] ++ extend-X~X (length Γ) []
extend-X~X-length-split [] Γ = refl
extend-X~X-length-split (m ∷ Φ) Γ =
  cong (X~X ∷_) (extend-X~X-length-split Φ Γ)

lookup-insert-extend-X~X :
  ∀ k {Δ X d} →
  X < k + Δ →
  (extend-X~X k [] ++ d ∷ extend-X~X Δ []) ∋ᶜ
    raiseVarFrom k X ∶ X~X
lookup-insert-extend-X~X zero X<Δ =
  there (lookup-extend-X~X[] X<Δ)
lookup-insert-extend-X~X (suc k) {X = zero} z<s = here
lookup-insert-extend-X~X (suc k) {X = suc X} (s<s X<k+Δ) =
  there (lookup-insert-extend-X~X k X<k+Δ)

refl-insert-extend-X~X :
  ∀ k {Δ A d} →
  WfTy (k + Δ) 0 A →
  extend-X~X k [] ++ d ∷ extend-X~X Δ [] ⊢
    renameᵗ (raiseVarFrom k) A ~ renameᵗ (raiseVarFrom k) A
refl-insert-extend-X~X k (wfVar X<k+Δ) =
  X-~-X (lookup-insert-extend-X~X k X<k+Δ)
refl-insert-extend-X~X k (wfSeal ())
refl-insert-extend-X~X k wfBase = ι-~-ι
refl-insert-extend-X~X k wf★ = ★-~-★
refl-insert-extend-X~X k (wf⇒ wfA wfB) =
  ⇒-~-⇒ (refl-insert-extend-X~X k wfA)
         (refl-insert-extend-X~X k wfB)
refl-insert-extend-X~X k {A = `∀ A} (wf∀ wfA) =
  ∀-~-∀
    (cong-~
      (sym (rename-raise-ext k A))
      (sym (rename-raise-ext k A))
      (refl-insert-extend-X~X (suc k) wfA))

non∀-raise-refl-~ :
  ∀ {Δ A} →
  Non∀ A →
  WfTy Δ 0 A →
  ★~X ∷ extend-X~X Δ [] ⊢ ⇑ᵗ A ~ ⇑ᵗ A
non∀-raise-refl-~ non∀A wfA =
  refl-insert-extend-X~X zero wfA

non∀-∀-consistent :
  ∀ {Δ A} →
  Non∀ A →
  WfTy Δ 0 A →
  extend-X~X Δ [] ⊢ A ~ `∀ (⇑ᵗ A)
non∀-∀-consistent non∀A wfA =
  A-~-∀
    (subst (λ n → WfTy n 0 _) (sym (length-extend-X~X[] _)) wfA)
    (non∀-raise-refl-~ non∀A wfA)

length-extend-X~X-split :
  (Φ Γ : CCtx) →
  length (Φ ++ Γ) ≡ length (extend-X~X (length Φ) [] ++ extend-X~X (length Γ) [])
length-extend-X~X-split [] Γ = sym (length-extend-X~X[] (length Γ))
length-extend-X~X-split (m ∷ Φ) Γ = cong suc (length-extend-X~X-split Φ Γ)

rename-raise-length-extend-X~X :
  (Φ : CCtx) (A : Ty) →
  renameᵗ (raiseVarFrom (length Φ)) A ≡
  renameᵗ (raiseVarFrom (length (extend-X~X (length Φ) []))) A
rename-raise-length-extend-X~X Φ A =
  rename-cong
    (λ X → cong (λ n → raiseVarFrom n X)
      (sym (length-extend-X~X[] (length Φ))))
    A


drop∋ᶜ-mode :
  ∀ {d Φ Γ X m} →
  (Φ ++ d ∷ Γ) ∋ᶜ raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ Γ) ∋ᶜ X ∶ m
drop∋ᶜ-mode {Φ = []} (there x∈) = x∈
drop∋ᶜ-mode {Φ = m₀ ∷ Φ} {X = zero} here = here
drop∋ᶜ-mode {Φ = m₀ ∷ Φ} {X = suc X} (there x∈) =
  there (drop∋ᶜ-mode {Φ = Φ} x∈)

drop∋ᶜ-neither :
  ∀ {Φ Γ X m} →
  (Φ ++ neither ∷ Γ) ∋ᶜ raiseVarFrom (length Φ) X ∶ m →
  (Φ ++ Γ) ∋ᶜ X ∶ m
drop∋ᶜ-neither {Φ = Φ} {Γ = Γ} {X = X} x∈ =
  drop∋ᶜ-mode {d = neither} {Φ = Φ} {Γ = Γ} {X = X} x∈

drop<-raise-mode :
  ∀ {d : CMode}{ Φ Γ X} →
  raiseVarFrom (length Φ) X < length (Φ ++ d ∷ Γ) →
  X < length (Φ ++ Γ)
drop<-raise-mode {Φ = []} (s<s X<Γ) = X<Γ
drop<-raise-mode {Φ = m ∷ Φ} {X = zero} z<s = z<s
drop<-raise-mode {Φ = m ∷ Φ} {X = suc X} (s<s X<Γ) =
  s<s (drop<-raise-mode {Φ = Φ} X<Γ)

drop<-raise :
  ∀ {Φ Γ X} →
  raiseVarFrom (length Φ) X < length (Φ ++ neither ∷ Γ) →
  X < length (Φ ++ Γ)
drop<-raise {Φ = Φ} {Γ = Γ} {X = X} X<Γ =
  drop<-raise-mode {d = neither} {Φ = Φ} {Γ = Γ} {X = X} X<Γ

drop-mode-WfTy :
  ∀ {d : CMode} {Φ Γ : CCtx} {A} →
  WfTy (length (Φ ++ d ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) 0 A
drop-mode-WfTy {Φ = Φ} {Γ = Γ} {A = ＇ X} (wfVar X<Γ) =
  wfVar (drop<-raise-mode {Φ = Φ} {Γ = Γ} {X = X} X<Γ)
drop-mode-WfTy {A = ｀ α} (wfSeal α<Ψ) = wfSeal α<Ψ
drop-mode-WfTy {A = ‵ ι} wfBase = wfBase
drop-mode-WfTy {A = ★} wf★ = wf★
drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A ⇒ B} (wf⇒ wfA wfB) =
  wf⇒ (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A} wfA)
       (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = B} wfB)
drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = `∀ A} (wf∀ wfA) =
  wf∀
    (drop-mode-WfTy {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} {A = A}
      (subst (λ B → WfTy (length ((X~X ∷ Φ) ++ d ∷ Γ)) 0 B)
        (rename-raise-ext (length Φ) A)
        wfA))

drop-neither-WfTy :
  ∀ {Φ Γ : CCtx} {A} →
  WfTy (length (Φ ++ neither ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) 0 A
drop-neither-WfTy {Φ = Φ} {Γ = Γ} {A = A} wfA =
  drop-mode-WfTy {d = neither} {Φ = Φ} {Γ = Γ} {A = A} wfA

var-var-~-inj :
  ∀ {Γ X Y} →
  Γ ⊢ ＇ X ~ ＇ Y →
  Σ[ eq ∈ X ≡ Y ] Γ ∋ᶜ X ∶ X~X
var-var-~-inj (X-~-X x∈) = refl , x∈

~-size :
  ∀ {Γ A B} →
  Γ ⊢ A ~ B →
  ℕ
~-size ★-~-★ = zero
~-size (X-~-X x∈) = zero
~-size ι-~-ι = zero
~-size (⇒-~-⇒ h₁ h₂) = suc (~-size h₁ + ~-size h₂)
~-size (∀-~-∀ h) = suc (~-size h)
~-size (A-~-★ n★ n∀ g h) = suc (~-size h)
~-size (★-~-B n★ n∀ hG h) = suc (~-size h)
~-size (νX-~-★ x∈) = zero
~-size (★-~-νX x∈) = zero
~-size (∀-~-B wfB h) = suc (~-size h)
~-size (A-~-∀ wfA h) = suc (~-size h)

≤refl : ∀ {n} → n ≤ n
≤refl {zero} = z≤n
≤refl {suc n} = s≤s ≤refl

≤step : ∀ {m n} → m ≤ n → m ≤ suc n
≤step z≤n = z≤n
≤step (s≤s m≤n) = s≤s (≤step m≤n)

≤trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤trans z≤n q = z≤n
≤trans (s≤s p) (s≤s q) = s≤s (≤trans p q)

≤left+ : ∀ m n → m ≤ m + n
≤left+ zero n = z≤n
≤left+ (suc m) n = s≤s (≤left+ m n)

≤right+ : ∀ m n → n ≤ m + n
≤right+ zero n = ≤refl
≤right+ (suc m) n = ≤step (≤right+ m n)

cong-~-size :
  ∀ {Γ A A′ B B′} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (h : Γ ⊢ A ~ B) →
  ~-size (cong-~ eqA eqB h) ≡ ~-size h
cong-~-size refl refl h = refl

cong-~-≤ :
  ∀ {Γ A A′ B B′ gas} →
  (eqA : A ≡ A′) →
  (eqB : B ≡ B′) →
  (h : Γ ⊢ A ~ B) →
  ~-size h ≤ gas →
  ~-size (cong-~ eqA eqB h) ≤ gas
cong-~-≤ eqA eqB h p =
  subst (λ n → n ≤ _) (sym (cong-~-size eqA eqB h)) p

drop-mode-at-X-suc :
  ∀ {d m Φ Γ X Y} →
  (m ∷ Φ) ++ d ∷ Γ ⊢
    ＇ suc (raiseVarFrom (length Φ) X) ~
    ＇ suc (raiseVarFrom (length Φ) Y) →
  (m ∷ Φ) ++ Γ ⊢ ＇ suc X ~ ＇ suc Y
drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    with var-var-~-inj h
drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    | eq , x∈
    with raiseVarFrom-injective (length Φ) (suc-injective eq)
drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
    | eq , x∈ | refl =
  X-~-X (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
           {X = suc X} x∈)

drop-mode-at-νL-suc :
  ∀ {d m Φ Γ X} →
  (m ∷ Φ) ++ d ∷ Γ ⊢
    ＇ suc (raiseVarFrom (length Φ) X) ~ ★ →
  (m ∷ Φ) ++ Γ ⊢ ＇ suc X ~ ★
drop-mode-at-νL-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X}
    (νX-~-★ x∈) =
  νX-~-★
    (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ} {X = suc X} x∈)
drop-mode-at-νL-suc (A-~-★ n★ n∀ (｀ α) ())
drop-mode-at-νL-suc (A-~-★ n★ n∀ (‵ ι) ())
drop-mode-at-νL-suc (A-~-★ n★ n∀ ★⇒★ ())

drop-mode-at-νR-suc :
  ∀ {d m Φ Γ X} →
  (m ∷ Φ) ++ d ∷ Γ ⊢
    ★ ~ ＇ suc (raiseVarFrom (length Φ) X) →
  (m ∷ Φ) ++ Γ ⊢ ★ ~ ＇ suc X
drop-mode-at-νR-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X}
    (★-~-νX x∈) =
  ★-~-νX
    (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ} {X = suc X} x∈)
drop-mode-at-νR-suc (★-~-B n★ n∀ (｀ α) ())
drop-mode-at-νR-suc (★-~-B n★ n∀ (‵ ι) ())
drop-mode-at-νR-suc (★-~-B n★ n∀ ★⇒★ ())

drop-mode-at-~-gas :
  (gas : ℕ) →
  ∀ {d Φ Γ B C}
    {h : Φ ++ d ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                         ~ renameᵗ (raiseVarFrom (length Φ)) C} →
  ~-size h ≤ gas →
  Φ ++ Γ ⊢ B ~ C
drop-mode-at-~-gas gas {B = ★} {C = ★} {h = ★-~-★} p = ★-~-★
drop-mode-at-~-gas gas {d = d} {Φ = []} {Γ = Γ}
    {B = ＇ X} {C = ＇ .X}
    {h = X-~-X {X = .(suc X)} x∈} p =
  X-~-X (drop∋ᶜ-mode {d = d} {Φ = []} {Γ = Γ} {X = X} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ zero}
    {C = ＇ zero}
    {h = X-~-X {X = zero} x∈} p =
  X-~-X (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
           {X = zero} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ suc X}
    {C = ＇ suc Y} {h = h} p =
  drop-mode-at-X-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ}
    {X = X} {Y = Y} h
drop-mode-at-~-gas gas {B = ‵ ι} {C = ‵ ι′} {h = ι-~-ι} p =
  ι-~-ι
drop-mode-at-~-gas zero {B = A ⇒ B} {C = A′ ⇒ B′}
    {h = ⇒-~-⇒ A~A′ B~B′} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = A ⇒ B}
    {C = A′ ⇒ B′} {h = ⇒-~-⇒ A~A′ B~B′} (s≤s p) =
  ⇒-~-⇒
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = A} {C = A′} {h = A~A′}
      (≤trans (≤left+ (~-size A~A′) (~-size B~B′)) p))
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = B} {C = B′} {h = B~B′}
      (≤trans (≤right+ (~-size A~A′) (~-size B~B′)) p))
drop-mode-at-~-gas zero {B = `∀ A} {C = `∀ B} {h = ∀-~-∀ A~B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = `∀ A}
    {C = `∀ B} {h = ∀-~-∀ A~B} (s≤s p) =
  ∀-~-∀
    (drop-mode-at-~-gas gas
      {d = d} {Φ = X~X ∷ Φ} {Γ = Γ} {B = A} {C = B}
      {h = cong-~ (rename-raise-ext (length Φ) A)
                  (rename-raise-ext (length Φ) B)
                  A~B}
      (cong-~-≤ (rename-raise-ext (length Φ) A)
                (rename-raise-ext (length Φ) B)
                A~B p))
drop-mode-at-~-gas zero {B = A} {C = ★} {h = A-~-★ n★ n∀ g A~G} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = A}
    {C = ★}
    {h = A-~-★ {G = G} n★ n∀ g A~G} (s≤s p) =
  A-~-★ (renameᵗ-Non★-inv n★) (renameᵗ-Non∀-inv n∀) g
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = A} {C = G}
      {h = cong-~ refl (sym (renameᵗ-ground-id g)) A~G}
      (cong-~-≤ refl (sym (renameᵗ-ground-id g)) A~G p))
drop-mode-at-~-gas zero {B = ★} {C = B} {h = ★-~-B n★ n∀ g H~B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = ★}
    {C = B}
    {h = ★-~-B {H = H} n★ n∀ g H~B} (s≤s p) =
  ★-~-B (renameᵗ-Non★-inv n★) (renameᵗ-Non∀-inv n∀) g
    (drop-mode-at-~-gas gas
      {d = d} {Φ = Φ} {Γ = Γ} {B = H} {C = B}
      {h = cong-~ (sym (renameᵗ-ground-id g)) refl H~B}
      (cong-~-≤ (sym (renameᵗ-ground-id g)) refl H~B p))
drop-mode-at-~-gas gas {d = d} {Φ = []} {Γ = Γ} {B = ＇ X}
    {C = ★}
    {h = νX-~-★ {X = .(suc X)} x∈} p =
  νX-~-★ (drop∋ᶜ-mode {d = d} {Φ = []} {Γ = Γ} {X = X} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ zero}
    {C = ★}
    {h = νX-~-★ {X = zero} x∈} p =
  νX-~-★ (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
            {X = zero} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ＇ suc X}
    {C = ★} {h = h} p =
  drop-mode-at-νL-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
drop-mode-at-~-gas gas {d = d} {Φ = []} {Γ = Γ} {B = ★} {C = ＇ X}
    {h = ★-~-νX {X = .(suc X)} x∈} p =
  ★-~-νX (drop∋ᶜ-mode {d = d} {Φ = []} {Γ = Γ} {X = X} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ★}
    {C = ＇ zero}
    {h = ★-~-νX {X = zero} x∈} p =
  ★-~-νX (drop∋ᶜ-mode {d = d} {Φ = m ∷ Φ} {Γ = Γ}
            {X = zero} x∈)
drop-mode-at-~-gas gas {d = d} {Φ = m ∷ Φ} {Γ = Γ} {B = ★}
    {C = ＇ suc X} {h = h} p =
  drop-mode-at-νR-suc {d = d} {m = m} {Φ = Φ} {Γ = Γ} {X = X} h
drop-mode-at-~-gas zero {B = `∀ A} {C = B} {h = ∀-~-B wfB A~⇑B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = `∀ A}
    {C = B}
    {h = ∀-~-B wfB A~⇑B} (s≤s p) =
  ∀-~-B
    (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = B} wfB)
    (drop-mode-at-~-gas gas
      {d = d} {Φ = X~★ ∷ Φ} {Γ = Γ} {B = A} {C = ⇑ᵗ B}
      {h = cong-~ (rename-raise-ext (length Φ) A)
                  (sym (rename-raise-⇑ᵗ (length Φ) B))
                  A~⇑B}
      (cong-~-≤ (rename-raise-ext (length Φ) A)
                (sym (rename-raise-⇑ᵗ (length Φ) B))
                A~⇑B p))
drop-mode-at-~-gas zero {B = A} {C = `∀ B} {h = A-~-∀ wfA ⇑A~B} ()
drop-mode-at-~-gas (suc gas) {d = d} {Φ = Φ} {Γ = Γ} {B = A}
    {C = `∀ B}
    {h = A-~-∀ wfA ⇑A~B} (s≤s p) =
  A-~-∀
    (drop-mode-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A} wfA)
    (drop-mode-at-~-gas gas
      {d = d} {Φ = ★~X ∷ Φ} {Γ = Γ} {B = ⇑ᵗ A} {C = B}
      {h = cong-~ (sym (rename-raise-⇑ᵗ (length Φ) A))
                  (rename-raise-ext (length Φ) B)
                  ⇑A~B}
      (cong-~-≤ (sym (rename-raise-⇑ᵗ (length Φ) A))
                (rename-raise-ext (length Φ) B)
                ⇑A~B p))

drop-mode-at-~ :
  ∀ {d Φ Γ B C} →
  Φ ++ d ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                  ~ renameᵗ (raiseVarFrom (length Φ)) C →
  Φ ++ Γ ⊢ B ~ C
drop-mode-at-~ h = drop-mode-at-~-gas (~-size h) {h = h} ≤refl

drop-neither-at-~ :
  ∀ {Φ Γ B C} →
  Φ ++ neither ∷ Γ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                     ~ renameᵗ (raiseVarFrom (length Φ)) C →
  Φ ++ Γ ⊢ B ~ C
drop-neither-at-~ = drop-mode-at-~ {d = neither}

drop-mode-~ :
  ∀ {d Γ B C} →
  d ∷ Γ ⊢ ⇑ᵗ B ~ ⇑ᵗ C →
  Γ ⊢ B ~ C
drop-mode-~ = drop-mode-at-~ {Φ = []}

drop-both-~ :
  ∀ {Γ B C} →
  X~X ∷ Γ ⊢ ⇑ᵗ B ~ ⇑ᵗ C →
  Γ ⊢ B ~ C
drop-both-~ = drop-mode-~ {d = X~X}

drop-extend-X~X-at-~ :
  ∀ {d Φ Γ B C} →
  extend-X~X (length (Φ ++ d ∷ Γ)) [] ⊢
    renameᵗ (raiseVarFrom (length Φ)) B ~
    renameᵗ (raiseVarFrom (length Φ)) C →
  extend-X~X (length (Φ ++ Γ)) [] ⊢ B ~ C
drop-extend-X~X-at-~ {d = d} {Φ = Φ} {Γ = Γ} {B = B} {C = C} h =
  subst (λ Ξ → Ξ ⊢ B ~ C) (sym (extend-X~X-length-split Φ Γ))
    (drop-mode-at-~ {d = X~X} {Φ = extend-X~X (length Φ) []}
      {Γ = extend-X~X (length Γ) []} {B = B} {C = C}
      (cong-~
        (rename-raise-length-extend-X~X Φ B)
        (rename-raise-length-extend-X~X Φ C)
        (subst
          (λ Ξ → Ξ ⊢ renameᵗ (raiseVarFrom (length Φ)) B
                     ~ renameᵗ (raiseVarFrom (length Φ)) C)
          (extend-X~X-length-split Φ (d ∷ Γ))
          h)))

drop-neither-~ :
  ∀ {Γ B C} →
  neither ∷ Γ ⊢ ⇑ᵗ B ~ ⇑ᵗ C →
  Γ ⊢ B ~ C
drop-neither-~ = drop-mode-~ {d = neither}

drop-extend-X~X-WfTy :
  ∀ {d : CMode} {Φ Γ : CCtx} {A} →
  WfTy (length (Φ ++ d ∷ Γ)) 0
    (renameᵗ (raiseVarFrom (length Φ)) A) →
  WfTy (length (Φ ++ Γ)) 0 A
drop-extend-X~X-WfTy {d = d} {Φ = Φ} {Γ = Γ} {A = A} wfA =
  subst (λ n → WfTy n 0 A) (sym (length-extend-X~X-split Φ Γ))
    (drop-mode-WfTy {d = X~X} {Φ = extend-X~X (length Φ) []}
      {Γ = extend-X~X (length Γ) []} {A = A}
      (subst
        (λ n → WfTy n 0
          (renameᵗ (raiseVarFrom (length (extend-X~X (length Φ) []))) A))
        (length-extend-X~X-split Φ (d ∷ Γ))
        (subst
          (λ B → WfTy (length (Φ ++ d ∷ Γ)) 0 B)
          (rename-raise-length-extend-X~X Φ A)
          wfA)))

drop-⇑ᵗ-WfTy-extend-X⊑X :
  ∀ {Δ A} →
  WfTy (suc Δ) 0 (⇑ᵗ A) →
  WfTy Δ 0 A
drop-⇑ᵗ-WfTy-extend-X⊑X {Δ = Δ} {A = A} wfA =
  subst (λ n → WfTy n 0 A) (length-extend-X~X[] Δ)
    (drop-mode-WfTy {d = X~X} {Φ = []} {Γ = extend-X~X Δ []} {A = A}
      (subst (λ n → WfTy (suc n) 0 (⇑ᵗ A))
        (sym (length-extend-X~X[] Δ))
        wfA))

swap-extend-X~X[] :
  ∀ Δ →
  swapCCtx (extend-X~X Δ []) ≡ extend-X~X Δ []
swap-extend-X~X[] zero = refl
swap-extend-X~X[] (suc Δ) = cong (X~X ∷_) (swap-extend-X~X[] Δ)

extend-X~X-sym :
  ∀ {Δ A B} →
  extend-X~X Δ [] ⊢ A ~ B →
  extend-X~X Δ [] ⊢ B ~ A
extend-X~X-sym {Δ = Δ} {A = A} {B = B} A~B =
  subst (λ Γ → Γ ⊢ B ~ A) (swap-extend-X~X[] Δ) (~-sym A~B)
