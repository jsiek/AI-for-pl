module strong.proof.ColorPreservation where

-- Strong System F v7 — proof that every retained source node keeps its
-- lexical type-variable scope.  The proof factors through a push/pop balance
-- for one-hole contexts; anchor names and representation stores contribute no
-- colors.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using ([]; _∷_; _++_; map; reverse; length)
open import Data.List.Properties using (reverse-++)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open Relation.Binary.PropositionalEquality.≡-Reasoning
import Data.Nat.Solver as NatSolver
open NatSolver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:=_; con)

open import strong.Ctx
open import strong.CtxMorph
open import strong.RepresentationTypes using (extᴿ)
open import strong.Terms
open import strong.TermSubst
open import strong.Residual

reverse-cons : ∀ {A : Set} (x : A) xs
  → reverse (x ∷ xs) ≡ reverse xs ++ (x ∷ [])
reverse-cons x xs = reverse-++ (x ∷ []) xs

reorder₃ : ∀ a b c → (a + b) + c ≡ (a + c) + b
reorder₃ = solve 3
  (λ a b c → (a :+ b) :+ c := (a :+ c) :+ b) refl

chain-balance : ∀ {a b c p q r s}
  → a + p ≡ b + q
  → b + r ≡ c + s
  → a + (p + r) ≡ c + (q + s)
chain-balance {a} {b} {c} {p} {q} {r} {s} eq₁ eq₂ = begin
  a + (p + r) ≡⟨ solve 3
    (λ a p r → a :+ (p :+ r) := (a :+ p) :+ r) refl a p r ⟩
  (a + p) + r ≡⟨ cong (_+ r) eq₁ ⟩
  (b + q) + r ≡⟨ reorder₃ b q r ⟩
  (b + r) + q ≡⟨ cong (_+ q) eq₂ ⟩
  (c + s) + q ≡⟨ solve 3
    (λ c s q → (c :+ s) :+ q := c :+ (q :+ s)) refl c s q ⟩
  c + (q + s) ∎

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective refl = refl

cancel-right : ∀ {m n} k → m + k ≡ n + k → m ≡ n
cancel-right {m} {n} zero eq = begin
  m ≡⟨ solve 1 (λ m → m := m :+ con 0) refl m ⟩
  m + zero ≡⟨ eq ⟩
  n + zero ≡⟨ solve 1 (λ n → n :+ con 0 := n) refl n ⟩
  n ∎
cancel-right {m} {n} (suc k) eq = cancel-right k (suc-injective (begin
  suc (m + k) ≡⟨ solve 2
    (λ m k → con 1 :+ (m :+ k) := m :+ (con 1 :+ k)) refl m k ⟩
  m + suc k ≡⟨ eq ⟩
  n + suc k ≡⟨ solve 2
    (λ n k → n :+ (con 1 :+ k) := con 1 :+ (n :+ k)) refl n k ⟩
  suc (n + k) ∎))

raise-image : ∀ {a b c d k}
  → a + b ≡ c + d + k
  → a + suc b ≡ c + d + suc k
raise-image {a} {b} {c} {d} {k} eq = begin
  a + suc b ≡⟨ solve 2
    (λ a b → a :+ (con 1 :+ b) := con 1 :+ (a :+ b)) refl a b ⟩
  suc (a + b) ≡⟨ cong suc eq ⟩
  suc (c + d + k) ≡⟨ solve 3
    (λ c d k → con 1 :+ ((c :+ d) :+ k)
       := (c :+ d) :+ (con 1 :+ k)) refl c d k ⟩
  c + d + suc k ∎

lower-copy-Λ : ∀ {a b c d k}
  → a + b ≡ c + d + suc k
  → a + b ≡ suc c + d + k
lower-copy-Λ {a} {b} {c} {d} {k} eq = trans eq
  (solve 3 (λ c d k → (c :+ d) :+ (con 1 :+ k)
                    := ((con 1 :+ c) :+ d) :+ k) refl c d k)

lift-effect : ∀ {a b c d} x y
  → a + b ≡ c + d
  → (x + a) + (y + b) ≡ (x + c) + (y + d)
lift-effect {a} {b} {c} {d} x y eq = begin
  (x + a) + (y + b) ≡⟨ solve 4
    (λ x a y b → (x :+ a) :+ (y :+ b)
       := (x :+ y) :+ (a :+ b)) refl x a y b ⟩
  (x + y) + (a + b) ≡⟨ cong ((x + y) +_) eq ⟩
  (x + y) + (c + d) ≡⟨ solve 4
    (λ x y c d → (x :+ y) :+ (c :+ d)
       := (x :+ c) :+ (y :+ d)) refl x y c d ⟩
  (x + c) + (y + d) ∎

effect-trans : ∀ {a b c d e f}
  → a + d ≡ c + b
  → c + f ≡ e + d
  → a + f ≡ e + b
effect-trans {a} {b} {c} {d} {e} {f} one many =
  cancel-right d (begin
    (a + f) + d ≡⟨ reorder₃ a f d ⟩
    (a + d) + f ≡⟨ cong (_+ f) one ⟩
    (c + b) + f ≡⟨ reorder₃ c b f ⟩
    (c + f) + b ≡⟨ cong (_+ b) many ⟩
    (e + d) + b ≡⟨ reorder₃ e d b ⟩
    (e + b) + d ∎)

same-hole-names : ∀ {n a b c d x y}
  → n + a ≡ x + b
  → n + c ≡ y + d
  → a + d ≡ c + b
  → x ≡ y
same-hole-names {n} {a} {b} {c} {d} {x} {y} left right effect =
  cancel-right (b + d) (begin
    x + (b + d) ≡⟨ solve 3
      (λ x b d → x :+ (b :+ d) := (x :+ b) :+ d) refl x b d ⟩
    (x + b) + d ≡⟨ cong (_+ d) (sym left) ⟩
    (n + a) + d ≡⟨ solve 3
      (λ n a d → (n :+ a) :+ d := n :+ (a :+ d)) refl n a d ⟩
    n + (a + d) ≡⟨ cong (n +_) effect ⟩
    n + (c + b) ≡⟨ solve 3
      (λ n c b → n :+ (c :+ b) := (n :+ c) :+ b) refl n c b ⟩
    (n + c) + b ≡⟨ cong (_+ b) right ⟩
    (y + d) + b ≡⟨ reorder₃ y d b ⟩
    (y + b) + d ≡⟨ solve 3
      (λ y b d → (y :+ b) :+ d := y :+ (b :+ d)) refl y b d ⟩
    y + (b + d) ∎)

drop-zero : ∀ p q → p + q + 0 ≡ p + q
drop-zero = solve 2 (λ p q → p :+ q :+ con 0 := p :+ q) refl

wrap-effect : ∀ p q a b
  → a + ((p + q) + b) ≡ (p + a) + ((q + b) + 0)
wrap-effect = solve 4
  (λ p q a b → a :+ ((p :+ q) :+ b)
    := (p :+ a) :+ ((q :+ b) :+ con 0)) refl

wrap-renamed : ∀ {pd qd ar br} p q a b
  → pd ≡ q → qd ≡ p → ar ≡ a → br ≡ b
  → a + (q + (qd + br)) ≡ (p + (pd + ar)) + b
wrap-renamed {pd} {qd} {ar} {br} p q a b ep eq ea eb = begin
  a + (q + (qd + br))
    ≡⟨ cong (λ z → a + (q + z)) (cong₂ _+_ eq eb) ⟩
  a + (q + (p + b))
    ≡⟨ solve 4
      (λ p q a b → a :+ (q :+ (p :+ b))
        := (p :+ (q :+ a)) :+ b) refl p q a b ⟩
  (p + (q + a)) + b
    ≡⟨ cong (λ z → (p + z) + b) (cong₂ _+_ (sym ep) (sym ea)) ⟩
  (p + (pd + ar)) + b ∎

tywrap-effect : ∀ p q a b
  → (p + (1 + a)) + (q + b) ≡ (p + 1 + a) + (q + b)
tywrap-effect = solve 4
  (λ p q a b → (p :+ (con 1 :+ a)) :+ (q :+ b)
    := ((p :+ con 1) :+ a) :+ (q :+ b)) refl

merge-effect : ∀ p₁ p₂ q₁ q₂ a b
  → (p₁ + (p₂ + a)) + (q₁ + (q₂ + b)) ≡
    (p₁ + p₂ + a) + (q₁ + q₂ + b)
merge-effect = solve 6
  (λ p₁ p₂ q₁ q₂ a b →
    (p₁ :+ (p₂ :+ a)) :+ (q₁ :+ (q₂ :+ b))
      := ((p₁ :+ p₂) :+ a) :+ ((q₁ :+ q₂) :+ b)) refl

same-effect : ∀ {a b c d} → a ≡ c → b ≡ d → a + d ≡ c + b
same-effect {a} {b} {c} {d} p q =
  trans (cong (a +_) (sym q)) (cong (_+ b) p)

------------------------------------------------------------------------
-- Colors are determined by the number of source-name entries
------------------------------------------------------------------------

names : Ctxᵗ → ℕ
names []           = zero
names (abst ∷ Δ)   = names Δ
names (bind R ∷ Δ) = names Δ
names (name α ∷ Δ) = suc (names Δ)

colors : ℕ → VarSet
colors zero    = []
colors (suc n) = zero ∷ map suc (colors n)

scope-colors : ∀ Δ → scopeᵗ Δ ≡ colors (names Δ)
scope-colors [] = refl
scope-colors (abst ∷ Δ) rewrite scope-colors Δ = refl
scope-colors (bind R ∷ Δ) rewrite scope-colors Δ = refl
scope-colors (name α ∷ Δ) rewrite scope-colors Δ = refl

scope-names : ∀ {Δ₁ Δ₂}
  → names Δ₁ ≡ names Δ₂
  → scopeᵗ Δ₁ ≡ scopeᵗ Δ₂
scope-names {Δ₁} {Δ₂} eq =
  trans (scope-colors Δ₁) (trans (cong colors eq) (sym (scope-colors Δ₂)))

------------------------------------------------------------------------
-- Push/pop accounting for scope changes and term contexts
------------------------------------------------------------------------

pushChange popChange : Change → ℕ
pushChange (reveal α)  = 1
pushChange (conceal α) = 0
popChange (reveal α)   = 0
popChange (conceal α)  = 1

pushScope popScope : Scope → ℕ
pushScope []       = 0
pushScope (δ ∷ χ)  = pushChange δ + pushScope χ
popScope []        = 0
popScope (δ ∷ χ)   = popChange δ + popScope χ

pushes pops : TermCtx → ℕ
pushes □ = 0
pushes (C ⊕L[ p ] N) = pushes C
pushes (L ⊕R[ p ] C) = pushes C
pushes (ƛC A ∙ C) = pushes C
pushes (C ·L N) = pushes C
pushes (L ·R C) = pushes C
pushes (ΛC C) = suc (pushes C)
pushes (C •C B [ A ]) = pushes C
pushes (νC Θ , χ [ C ∣ c ]) = pushScope χ + pushes C

pops □ = 0
pops (C ⊕L[ p ] N) = pops C
pops (L ⊕R[ p ] C) = pops C
pops (ƛC A ∙ C) = pops C
pops (C ·L N) = pops C
pops (L ·R C) = pops C
pops (ΛC C) = pops C
pops (C •C B [ A ]) = pops C
pops (νC Θ , χ [ C ∣ c ]) = popScope χ + pops C

store-names : ∀ {Δ Θ Δ′}
  → Δ ⊢ˢ Θ ⇒ Δ′
  → names Δ ≡ names Δ′
store-names store[] = refl
store-names (store-abst s) = store-names s
store-names (store-bind q s) = store-names s

pop-names : ∀ {Δ α Δ′}
  → Δ ▷ α ↘ Δ′
  → names Δ ≡ suc (names Δ′)
pop-names pop-here = refl
pop-names (pop-abst p) = pop-names p
pop-names (pop-bind p) = pop-names p

change-balance : ∀ {Δ δ Δ′}
  → Δ ⊢δ δ ⇒ Δ′
  → names Δ + pushChange δ ≡ names Δ′ + popChange δ
change-balance (step-reveal {Δ = Δ} a fresh) = solve 1
  (λ n → n :+ con 1 := (con 1 :+ n) :+ con 0) refl (names Δ)
change-balance (step-conceal {Δ′ = Δ′} p) = trans
  (cong (_+ 0) (pop-names p))
  (solve 1 (λ n → (con 1 :+ n) :+ con 0 := n :+ con 1)
    refl (names Δ′))

scope-balance : ∀ {Δ χ Δ′}
  → Δ ⊢χ χ ⇒ Δ′
  → names Δ + pushScope χ ≡ names Δ′ + popScope χ
scope-balance scope[] = refl
scope-balance (scope∷ {Δ₁ = Δ₁} {Δ₂ = Δ₂} {Δ₃ = Δ₃}
                       {δ = δ} {χ = χ} d s) =
  chain-balance {a = names Δ₁} {b = names Δ₂} {c = names Δ₃}
    {p = pushChange δ} {q = popChange δ}
    {r = pushScope χ} {s = popScope χ}
    (change-balance d) (scope-balance s)

frame-balance : ∀ {Δ C Δ′}
  → Δ ⊢C C ⊣ Δ′
  → names Δ + pushes C ≡ names Δ′ + pops C
frame-balance frame-□ = refl
frame-balance (frame-⊕L f) = frame-balance f
frame-balance (frame-⊕R f) = frame-balance f
frame-balance (frame-ƛ f) = frame-balance f
frame-balance (frame-·L f) = frame-balance f
frame-balance (frame-·R f) = frame-balance f
frame-balance (frame-Λ {Δ = Δ} {C = C} f) = trans
  (solve 2 (λ n p → n :+ (con 1 :+ p) := (con 1 :+ n) :+ p)
    refl (names Δ) (pushes C))
  (frame-balance f)
frame-balance (frame-• f) = frame-balance f
frame-balance
  (frame-ν {ΔΘ = ΔΘ} {Δᵢ = Δᵢ} {Δ′ = Δ′} {χ = χ} {C = C}
    s ch f)
  rewrite store-names s =
  chain-balance {a = names ΔΘ} {b = names Δᵢ} {c = names Δ′}
    {p = pushScope χ} {q = popScope χ}
    {r = pushes C} {s = pops C}
    (scope-balance ch) (frame-balance f)

------------------------------------------------------------------------
-- Context operations preserve push/pop counts
------------------------------------------------------------------------

push-substCtx : ∀ σ C → pushes (substCtx σ C) ≡ pushes C
push-substCtx σ □ = refl
push-substCtx σ (C ⊕L[ p ] N) = push-substCtx σ C
push-substCtx σ (L ⊕R[ p ] C) = push-substCtx σ C
push-substCtx σ (ƛC A ∙ C) = push-substCtx (extImg σ) C
push-substCtx σ (C ·L N) = push-substCtx σ C
push-substCtx σ (L ·R C) = push-substCtx σ C
push-substCtx σ (ΛC C) = cong suc (push-substCtx _ C)
push-substCtx σ (C •C B [ A ]) = push-substCtx σ C
push-substCtx σ (νC Θ , χ [ C ∣ c ]) = refl

pop-substCtx : ∀ σ C → pops (substCtx σ C) ≡ pops C
pop-substCtx σ □ = refl
pop-substCtx σ (C ⊕L[ p ] N) = pop-substCtx σ C
pop-substCtx σ (L ⊕R[ p ] C) = pop-substCtx σ C
pop-substCtx σ (ƛC A ∙ C) = pop-substCtx (extImg σ) C
pop-substCtx σ (C ·L N) = pop-substCtx σ C
pop-substCtx σ (L ·R C) = pop-substCtx σ C
pop-substCtx σ (ΛC C) = pop-substCtx _ C
pop-substCtx σ (C •C B [ A ]) = pop-substCtx σ C
pop-substCtx σ (νC Θ , χ [ C ∣ c ]) = refl

substCtx-balance : ∀ σ C
  → pushes C + pops (substCtx σ C) ≡
    pushes (substCtx σ C) + pops C
substCtx-balance σ C = trans (cong (pushes C +_) (pop-substCtx σ C))
  (cong (_+ pops C) (sym (push-substCtx σ C)))

push-renScope : ∀ ρ χ → pushScope (renScope ρ χ) ≡ pushScope χ
push-renScope ρ [] = refl
push-renScope ρ (reveal α ∷ χ) = cong suc (push-renScope ρ χ)
push-renScope ρ (conceal α ∷ χ) = push-renScope ρ χ

pop-renScope : ∀ ρ χ → popScope (renScope ρ χ) ≡ popScope χ
pop-renScope ρ [] = refl
pop-renScope ρ (reveal α ∷ χ) = pop-renScope ρ χ
pop-renScope ρ (conceal α ∷ χ) = cong suc (pop-renScope ρ χ)

push-renAnchCtx : ∀ ρ C → pushes (renAnchCtx ρ C) ≡ pushes C
push-renAnchCtx ρ □ = refl
push-renAnchCtx ρ (C ⊕L[ p ] N) = push-renAnchCtx ρ C
push-renAnchCtx ρ (L ⊕R[ p ] C) = push-renAnchCtx ρ C
push-renAnchCtx ρ (ƛC A ∙ C) = push-renAnchCtx ρ C
push-renAnchCtx ρ (C ·L N) = push-renAnchCtx ρ C
push-renAnchCtx ρ (L ·R C) = push-renAnchCtx ρ C
push-renAnchCtx ρ (ΛC C) = cong suc (push-renAnchCtx (extᴿ ρ) C)
push-renAnchCtx ρ (C •C B [ A ]) = push-renAnchCtx ρ C
push-renAnchCtx ρ (νC Θ , χ [ C ∣ c ])
  with push-renScope (extendAnchor (length Θ) ρ) χ
     | push-renAnchCtx (extendAnchor (length Θ) ρ) C
push-renAnchCtx ρ (νC Θ , χ [ C ∣ c ]) | χ-eq | C-eq =
  cong₂ _+_ χ-eq C-eq

pop-renAnchCtx : ∀ ρ C → pops (renAnchCtx ρ C) ≡ pops C
pop-renAnchCtx ρ □ = refl
pop-renAnchCtx ρ (C ⊕L[ p ] N) = pop-renAnchCtx ρ C
pop-renAnchCtx ρ (L ⊕R[ p ] C) = pop-renAnchCtx ρ C
pop-renAnchCtx ρ (ƛC A ∙ C) = pop-renAnchCtx ρ C
pop-renAnchCtx ρ (C ·L N) = pop-renAnchCtx ρ C
pop-renAnchCtx ρ (L ·R C) = pop-renAnchCtx ρ C
pop-renAnchCtx ρ (ΛC C) = pop-renAnchCtx (extᴿ ρ) C
pop-renAnchCtx ρ (C •C B [ A ]) = pop-renAnchCtx ρ C
pop-renAnchCtx ρ (νC Θ , χ [ C ∣ c ])
  with pop-renScope (extendAnchor (length Θ) ρ) χ
     | pop-renAnchCtx (extendAnchor (length Θ) ρ) C
pop-renAnchCtx ρ (νC Θ , χ [ C ∣ c ]) | χ-eq | C-eq =
  cong₂ _+_ χ-eq C-eq

push-++ : ∀ χ ψ → pushScope (χ ++ ψ) ≡ pushScope χ + pushScope ψ
push-++ [] ψ = refl
push-++ (reveal α ∷ χ) ψ rewrite push-++ χ ψ = refl
push-++ (conceal α ∷ χ) ψ rewrite push-++ χ ψ = refl

pop-++ : ∀ χ ψ → popScope (χ ++ ψ) ≡ popScope χ + popScope ψ
pop-++ [] ψ = refl
pop-++ (reveal α ∷ χ) ψ rewrite pop-++ χ ψ = refl
pop-++ (conceal α ∷ χ) ψ rewrite pop-++ χ ψ = refl

push-reverse : ∀ χ → pushScope (reverse χ) ≡ pushScope χ
push-reverse [] = refl
push-reverse (reveal α ∷ χ) rewrite reverse-cons (reveal α) χ
                                    | push-++ (reverse χ) (reveal α ∷ [])
                                    | push-reverse χ = solve 1
  (λ n → n :+ con 1 := con 1 :+ n) refl (pushScope χ)
push-reverse (conceal α ∷ χ) rewrite reverse-cons (conceal α) χ
                                     | push-++ (reverse χ) (conceal α ∷ [])
                                     | push-reverse χ = solve 1
  (λ n → n :+ con 0 := n) refl (pushScope χ)

pop-reverse : ∀ χ → popScope (reverse χ) ≡ popScope χ
pop-reverse [] = refl
pop-reverse (reveal α ∷ χ) rewrite reverse-cons (reveal α) χ
                                   | pop-++ (reverse χ) (reveal α ∷ [])
                                   | pop-reverse χ = solve 1
  (λ n → n :+ con 0 := n) refl (popScope χ)
pop-reverse (conceal α ∷ χ) rewrite reverse-cons (conceal α) χ
                                    | pop-++ (reverse χ) (conceal α ∷ [])
                                    | pop-reverse χ = solve 1
  (λ n → n :+ con 1 := con 1 :+ n) refl (popScope χ)

push-dual-map : ∀ χ → pushScope (map dualChange χ) ≡ popScope χ
push-dual-map [] = refl
push-dual-map (reveal α ∷ χ) = push-dual-map χ
push-dual-map (conceal α ∷ χ) = cong suc (push-dual-map χ)

pop-dual-map : ∀ χ → popScope (map dualChange χ) ≡ pushScope χ
pop-dual-map [] = refl
pop-dual-map (reveal α ∷ χ) = cong suc (pop-dual-map χ)
pop-dual-map (conceal α ∷ χ) = pop-dual-map χ

push-dual : ∀ χ → pushScope (dual χ) ≡ popScope χ
push-dual χ = trans (push-dual-map (reverse χ))
                    (pop-reverse χ)

pop-dual : ∀ χ → popScope (dual χ) ≡ pushScope χ
pop-dual χ = trans (pop-dual-map (reverse χ))
                   (push-reverse χ)

push-shiftScope : ∀ n χ → pushScope (shiftScope n χ) ≡ pushScope χ
push-shiftScope n [] = refl
push-shiftScope n (reveal α ∷ χ) = cong suc (push-shiftScope n χ)
push-shiftScope n (conceal α ∷ χ) = push-shiftScope n χ

pop-shiftScope : ∀ n χ → popScope (shiftScope n χ) ≡ popScope χ
pop-shiftScope n [] = refl
pop-shiftScope n (reveal α ∷ χ) = pop-shiftScope n χ
pop-shiftScope n (conceal α ∷ χ) = cong suc (pop-shiftScope n χ)

tywrap-push : ∀ χ C
  → pushScope χ + suc (pushes C) ≡
    pushScope (shiftScope 1 χ ++ (reveal zero ∷ [])) + pushes C
tywrap-push χ C = begin
  pushScope χ + suc (pushes C) ≡⟨ solve 2
    (λ p a → p :+ (con 1 :+ a) := (p :+ con 1) :+ a)
    refl (pushScope χ) (pushes C) ⟩
  (pushScope χ + 1) + pushes C
    ≡⟨ cong (λ z → (z + 1) + pushes C)
             (sym (push-shiftScope 1 χ)) ⟩
  (pushScope (shiftScope 1 χ) + 1) + pushes C
    ≡⟨ cong (_+ pushes C)
             (sym (push-++ (shiftScope 1 χ) (reveal zero ∷ []))) ⟩
  pushScope (shiftScope 1 χ ++ (reveal zero ∷ [])) + pushes C ∎

tywrap-pop : ∀ χ C
  → popScope χ + pops C ≡
    popScope (shiftScope 1 χ ++ (reveal zero ∷ [])) + pops C
tywrap-pop χ C = begin
  popScope χ + pops C
    ≡⟨ cong (_+ pops C) (sym (pop-shiftScope 1 χ)) ⟩
  popScope (shiftScope 1 χ) + pops C ≡⟨ solve 2
    (λ q b → q :+ b := (q :+ con 0) :+ b)
    refl (popScope (shiftScope 1 χ)) (pops C) ⟩
  (popScope (shiftScope 1 χ) + 0) + pops C
    ≡⟨ cong (_+ pops C)
             (sym (pop-++ (shiftScope 1 χ) (reveal zero ∷ []))) ⟩
  popScope (shiftScope 1 χ ++ (reveal zero ∷ [])) + pops C ∎

merge-push : ∀ n χ₁ χ₂ C
  → pushScope χ₁ + (pushScope χ₂ + pushes C) ≡
    pushScope (shiftScope n χ₁ ++ χ₂) + pushes C
merge-push n χ₁ χ₂ C = begin
  pushScope χ₁ + (pushScope χ₂ + pushes C) ≡⟨ solve 3
    (λ p₁ p₂ a → p₁ :+ (p₂ :+ a) := (p₁ :+ p₂) :+ a)
    refl (pushScope χ₁) (pushScope χ₂) (pushes C) ⟩
  (pushScope χ₁ + pushScope χ₂) + pushes C
    ≡⟨ cong (λ z → (z + pushScope χ₂) + pushes C)
             (sym (push-shiftScope n χ₁)) ⟩
  (pushScope (shiftScope n χ₁) + pushScope χ₂) + pushes C
    ≡⟨ cong (_+ pushes C) (sym (push-++ (shiftScope n χ₁) χ₂)) ⟩
  pushScope (shiftScope n χ₁ ++ χ₂) + pushes C ∎

merge-pop : ∀ n χ₁ χ₂ C
  → popScope χ₁ + (popScope χ₂ + pops C) ≡
    popScope (shiftScope n χ₁ ++ χ₂) + pops C
merge-pop n χ₁ χ₂ C = begin
  popScope χ₁ + (popScope χ₂ + pops C) ≡⟨ solve 3
    (λ q₁ q₂ b → q₁ :+ (q₂ :+ b) := (q₁ :+ q₂) :+ b)
    refl (popScope χ₁) (popScope χ₂) (pops C) ⟩
  (popScope χ₁ + popScope χ₂) + pops C
    ≡⟨ cong (λ z → (z + popScope χ₂) + pops C)
             (sym (pop-shiftScope n χ₁)) ⟩
  (popScope (shiftScope n χ₁) + popScope χ₂) + pops C
    ≡⟨ cong (_+ pops C) (sym (pop-++ (shiftScope n χ₁) χ₂)) ⟩
  popScope (shiftScope n χ₁ ++ χ₂) + pops C ∎

------------------------------------------------------------------------
-- A residual context has the same net color effect
------------------------------------------------------------------------

image-balance : ∀ {k I C M D N}
  → ImageResidual k I C M D N
  → pushes C + pops D ≡ pushes D + pops C + k
image-balance (image-here {C = C} node) = solve 2
  (λ p q → p :+ q := (p :+ q) :+ con 0) refl (pushes C) (pops C)
image-balance {k = suc k} (image-Λ {C = C} {D = D} r)
  with image-balance r | push-renAnchCtx suc D | pop-renAnchCtx suc D
image-balance {k = suc k} (image-Λ {C = C} {D = D} r) | ih | p | q =
  trans (cong (λ z → pushes C + suc z) q)
    (trans (raise-image {a = pushes C} {b = pops D}
             {c = pushes D} {d = pops C} {k = k} ih)
      (cong (λ z → z + pops C + suc k) (sym p)))

copy-balance : ∀ {k σ P C M D N}
  → CopyResidual k σ P C M D N
  → pushes C + pops D ≡ pushes D + pops C + k
copy-balance (copy-var r) = image-balance r
copy-balance (copy-⊕L r) = copy-balance r
copy-balance (copy-⊕R r) = copy-balance r
copy-balance (copy-ƛ r) = copy-balance r
copy-balance (copy-·L r) = copy-balance r
copy-balance (copy-·R r) = copy-balance r
copy-balance {k = k} {C = C} {D = ΛC D} (copy-Λ r)
  with copy-balance r
copy-balance {k = k} {C = C} {D = ΛC D} (copy-Λ r) | ih =
  lower-copy-Λ {a = pushes C} {b = pops D} {c = pushes D}
    {d = pops C} {k = k} ih
copy-balance (copy-• r) = copy-balance r

residual-balance : ∀ {Δ L N r C M D P}
  → Residual {Δ = Δ} {L = L} {N = N} r C M D P
  → pushes C + pops D ≡ pushes D + pops C
residual-balance {C = ((ƛC A ∙ C) ·L W)} (residual-β-body v stable) =
  substCtx-balance _ C
residual-balance (residual-β-arg v r) with copy-balance r
residual-balance {C = C} {D = D} (residual-β-arg v r) | ih =
  trans ih (drop-zero (pushes D) (pops C))
residual-balance (residual-TyBeta v q eq node) = refl
residual-balance (residual-Wrap-body vb vw eq refl node) = refl
residual-balance
  (residual-Wrap-arg {Θ = Θ} {χ = χ} {C = C} vb vw eq refl node)
  with push-dual χ | pop-dual χ
     | push-renAnchCtx (shiftAnchor (length Θ)) C
     | pop-renAnchCtx (shiftAnchor (length Θ)) C
residual-balance
  (residual-Wrap-arg {Θ = Θ} {χ = χ} {C = C} vb vw eq refl node)
  | pχ | qχ | pC | qC = wrap-renamed
    (pushScope χ) (popScope χ) (pushes C) (pops C) pχ qχ pC qC
residual-balance (residual-TyWrap {χ = χ} v eq q refl node)
  with push-shiftScope 1 χ | pop-shiftScope 1 χ
     | push-++ (shiftScope 1 χ) (reveal zero ∷ [])
     | pop-++ (shiftScope 1 χ) (reveal zero ∷ [])
residual-balance
  (residual-TyWrap {χ = χ} {C = C} v eq q refl node)
  | ps | qs | pp | qp = same-effect (tywrap-push χ C) (tywrap-pop χ C)
residual-balance
  (residual-Merge {Θ₂ = Θ₂} {χ₁ = χ₁} {χ₂ = χ₂} {C = C}
    v refl node)
  with push-shiftScope (length Θ₂) χ₁
     | pop-shiftScope (length Θ₂) χ₁
     | push-++ (shiftScope (length Θ₂) χ₁) χ₂
     | pop-++ (shiftScope (length Θ₂) χ₁) χ₂
residual-balance
  (residual-Merge {Θ₂ = Θ₂} {χ₁ = χ₁} {χ₂ = χ₂} {C = C}
    v refl node)
  | ps | qs | pp | qp = same-effect
    (merge-push (length Θ₂) χ₁ χ₂ C)
    (merge-pop (length Θ₂) χ₁ χ₂ C)
residual-balance (residual-ξ-⊕L r) = residual-balance r
residual-balance (residual-ξ-⊕R v r) = residual-balance r
residual-balance (residual-ξ-·L r) = residual-balance r
residual-balance (residual-ξ-·R v r) = residual-balance r
residual-balance (residual-ξ-• r) = residual-balance r
residual-balance {C = ΛC C} {D = ΛC D} (residual-ξ-Λ r)
  with residual-balance r
residual-balance {C = ΛC C} {D = ΛC D} (residual-ξ-Λ r) | ih =
  lift-effect {a = pushes C} {b = pops D}
    {c = pushes D} {d = pops C} 1 0 ih
residual-balance {C = νC Θ , χ [ C ∣ c ]}
                 {D = νC Θ , χ [ D ∣ c ]}
                 (residual-ξ-ν {χ = χ} s ch r)
  with residual-balance r
residual-balance {C = νC Θ , χ [ C ∣ c ]}
                 {D = νC Θ , χ [ D ∣ c ]}
                 (residual-ξ-ν {χ = χ} s ch r) | ih =
  lift-effect {a = pushes C} {b = pops D}
    {c = pushes D} {d = pops C}
    (pushScope χ) (popScope χ) ih

residuals-balance : ∀ {Δ L N rs C M D P}
  → Residuals {Δ = Δ} {L = L} {N = N} rs C M D P
  → pushes C + pops D ≡ pushes D + pops C
residuals-balance (residuals-done node) = refl
residuals-balance {C = C} {D = E}
  (residuals-step {D = D} r rs)
  with residual-balance r | residuals-balance rs
residuals-balance {C = C} {D = E}
  (residuals-step {D = D} r rs) | one | many =
  effect-trans {a = pushes C} {b = pops C}
    {c = pushes D} {d = pops D} {e = pushes E} {f = pops E}
    one many

------------------------------------------------------------------------
-- The theorem used by the public wrapper
------------------------------------------------------------------------

color-preservation : ∀ {Δ L N rs C M D P Δ₁ Δ₂}
  → Residuals {Δ = Δ} {L = L} {N = N} rs C M D P
  → Δ ⊢C C ⊣ Δ₁
  → Δ ⊢C D ⊣ Δ₂
  → scopeᵗ Δ₁ ≡ scopeᵗ Δ₂
color-preservation {Δ = Δ} {C = C} {D = D} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
  rs source target
  with frame-balance source | frame-balance target | residuals-balance rs
color-preservation {Δ = Δ} {C = C} {D = D} {Δ₁ = Δ₁} {Δ₂ = Δ₂}
  rs source target | source-eq | target-eq | residual-eq =
  scope-names {Δ₁ = Δ₁} {Δ₂ = Δ₂}
    (same-hole-names {n = names Δ} {a = pushes C}
    {b = pops C} {c = pushes D} {d = pops D}
    {x = names Δ₁} {y = names Δ₂}
    source-eq target-eq residual-eq)
