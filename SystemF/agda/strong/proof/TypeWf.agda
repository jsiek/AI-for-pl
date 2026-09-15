module strong.proof.TypeWf where

-- Strong System F v8 — a well-typed term has a well-formed type.
--
-- Two observations carry it.
--
-- First, `⊢ᵗ` reads ONLY names, and every stack entry is a name entry
-- (`bind` names the binder it introduces, `asgn` names an address
-- bound elsewhere).  So well-formedness of a type depends on nothing
-- but the LENGTH of the stack: `wf-len`.  That is what relates a `Λ`'s
-- body context, whose stack is `asgn (bse zero) ∷ ⤒ Ss`, to the `∀`'s,
-- whose stack is `bind ∷ Ss` — different entries, same length.
--
-- Second, a typed conversion's TARGET is well formed at its exterior,
-- with no hypothesis at all (`conv-wf`): each rule either states its
-- target as a premise, or as a `shiftAtᵗ` of one, or as a name the pop
-- puts in scope, or as a read-back, and a read-back is well formed
-- because `read-var` carries the name lookup.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion
open import strong.Terms
open import strong.proof.ArrTyping using (wf-shift)
open import strong.proof.BuilderTyping using (wf-⇑)

private
  variable
    Sg : Store
    Δ Δᵢ Δₑ : Ctxᵗ
    Ss Ss′ : List StackEnt
    Bs Bs′ : List BaseEnt
    A B : Ty
    R : RepTy
    X : ℕ
    α : Addr

------------------------------------------------------------------------
-- Well-formedness depends only on how many names are in scope
------------------------------------------------------------------------

-- Every stack entry names something, so a lookup exists at every
-- position below the stack's length — whatever the entries are.
∋n-len : length Ss ≡ length Ss′ → (Ss ∥ Bs) ∋n X := α
  → Σ[ β ∈ Addr ] ((Ss′ ∥ Bs′) ∋n X := β)
∋n-len {Ss′ = asgn β ∷ Ss′} eq n-here-asgn = β , n-here-asgn
∋n-len {Ss′ = bind ∷ Ss′} eq n-here-asgn = bnd zero , n-here-bind
∋n-len {Ss′ = asgn β ∷ Ss′} eq n-here-bind = β , n-here-asgn
∋n-len {Ss′ = bind ∷ Ss′} eq n-here-bind = bnd zero , n-here-bind
∋n-len {Ss′ = asgn β ∷ Ss′} eq (n-skip-asgn p) with ∋n-len (suc-inj eq) p
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
∋n-len {Ss′ = asgn β ∷ Ss′} eq (n-skip-asgn p) | γ , q =
  γ , n-skip-asgn q
∋n-len {Ss′ = bind ∷ Ss′} eq (n-skip-asgn p) with ∋n-len (suc-inj eq) p
  where
  suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
  suc-inj refl = refl
∋n-len {Ss′ = bind ∷ Ss′} eq (n-skip-asgn p) | lvl ℓ , q =
  lvl ℓ , n-skip-bind-l q
∋n-len {Ss′ = bind ∷ Ss′} eq (n-skip-asgn p) | bnd i , q =
  bnd (suc i) , n-skip-bind-b q
∋n-len {Ss′ = bind ∷ Ss′} eq (n-skip-asgn p) | bse j , q =
  bse j , n-skip-bind-e q
∋n-len {Ss′ = Ss′} eq (n-skip-bind-b p) = skip eq p
  where
  skip : ∀ {Ss Ss′ Bs Bs′ X i} → length (bind ∷ Ss) ≡ length Ss′
    → (Ss ∥ Bs) ∋n X := bnd i
    → Σ[ β ∈ Addr ] ((Ss′ ∥ Bs′) ∋n suc X := β)
  skip {Ss′ = asgn β ∷ Ss′} eq p with ∋n-len (sucI eq) p
    where
    sucI : ∀ {m n} → suc m ≡ suc n → m ≡ n
    sucI refl = refl
  skip {Ss′ = asgn β ∷ Ss′} eq p | γ , q = γ , n-skip-asgn q
  skip {Ss′ = bind ∷ Ss′} eq p with ∋n-len (sucI eq) p
    where
    sucI : ∀ {m n} → suc m ≡ suc n → m ≡ n
    sucI refl = refl
  skip {Ss′ = bind ∷ Ss′} eq p | lvl ℓ , q = lvl ℓ , n-skip-bind-l q
  skip {Ss′ = bind ∷ Ss′} eq p | bnd i , q = bnd (suc i) , n-skip-bind-b q
  skip {Ss′ = bind ∷ Ss′} eq p | bse j , q = bse j , n-skip-bind-e q
∋n-len {Ss′ = Ss′} eq (n-skip-bind-l p) = skip eq p
  where
  skip : ∀ {Ss Ss′ Bs Bs′ X ℓ} → length (bind ∷ Ss) ≡ length Ss′
    → (Ss ∥ Bs) ∋n X := lvl ℓ
    → Σ[ β ∈ Addr ] ((Ss′ ∥ Bs′) ∋n suc X := β)
  skip {Ss′ = asgn β ∷ Ss′} eq p with ∋n-len (sucI eq) p
    where
    sucI : ∀ {m n} → suc m ≡ suc n → m ≡ n
    sucI refl = refl
  skip {Ss′ = asgn β ∷ Ss′} eq p | γ , q = γ , n-skip-asgn q
  skip {Ss′ = bind ∷ Ss′} eq p with ∋n-len (sucI eq) p
    where
    sucI : ∀ {m n} → suc m ≡ suc n → m ≡ n
    sucI refl = refl
  skip {Ss′ = bind ∷ Ss′} eq p | lvl m , q = lvl m , n-skip-bind-l q
  skip {Ss′ = bind ∷ Ss′} eq p | bnd i , q = bnd (suc i) , n-skip-bind-b q
  skip {Ss′ = bind ∷ Ss′} eq p | bse j , q = bse j , n-skip-bind-e q
∋n-len {Ss′ = Ss′} eq (n-skip-bind-e p) = skip eq p
  where
  skip : ∀ {Ss Ss′ Bs Bs′ X j} → length (bind ∷ Ss) ≡ length Ss′
    → (Ss ∥ Bs) ∋n X := bse j
    → Σ[ β ∈ Addr ] ((Ss′ ∥ Bs′) ∋n suc X := β)
  skip {Ss′ = asgn β ∷ Ss′} eq p with ∋n-len (sucI eq) p
    where
    sucI : ∀ {m n} → suc m ≡ suc n → m ≡ n
    sucI refl = refl
  skip {Ss′ = asgn β ∷ Ss′} eq p | γ , q = γ , n-skip-asgn q
  skip {Ss′ = bind ∷ Ss′} eq p with ∋n-len (sucI eq) p
    where
    sucI : ∀ {m n} → suc m ≡ suc n → m ≡ n
    sucI refl = refl
  skip {Ss′ = bind ∷ Ss′} eq p | lvl m , q = lvl m , n-skip-bind-l q
  skip {Ss′ = bind ∷ Ss′} eq p | bnd i , q = bnd (suc i) , n-skip-bind-b q
  skip {Ss′ = bind ∷ Ss′} eq p | bse j , q = bse j , n-skip-bind-e q

wf-len : ∀ {Ss Ss′ Bs Bs′ A} → length Ss ≡ length Ss′
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ A
wf-len eq (wf-var n) with ∋n-len eq n
wf-len eq (wf-var n) | β , q = wf-var q
wf-len eq wf-ℕ = wf-ℕ
wf-len eq wf-𝔹 = wf-𝔹
wf-len eq (wf-⇒ a b) = wf-⇒ (wf-len eq a) (wf-len eq b)
wf-len eq (wf-∀ a) = wf-∀ (wf-len (cong suc eq) a)

------------------------------------------------------------------------
-- A conversion's source and target are well formed
------------------------------------------------------------------------

read-wf : Sg ∣ Δ ⊢ R ⇓ A → Δ ⊢ᵗ A
read-wf (read-var n) = wf-var n
read-wf read-ℕ = wf-ℕ
read-wf read-𝔹 = wf-𝔹
read-wf (read-⇒ a b) = wf-⇒ (read-wf a) (read-wf b)
read-wf (read-∀ a) = wf-∀ (read-wf a)

-- the popped name is in scope on the side that has the assignment
pop-∋n : Δₑ ▷ X := α ⇒ Δᵢ → Δₑ ∋n X := α
pop-∋n pop-here = n-here-asgn
pop-∋n (pop-bind-b p) = n-skip-bind-b (pop-∋n p)
pop-∋n (pop-bind-l p) = n-skip-bind-l (pop-∋n p)
pop-∋n (pop-bind-e p) = n-skip-bind-e (pop-∋n p)

mutual
  convElt-wf-src : ∀ {ĉ} → Sg ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δₑ → Δᵢ ⊢ᵗ A
  convElt-wf-src (conv-seal rep rd p) = read-wf rd
  convElt-wf-src (conv-unseal rep rd p na) = wf-var (pop-∋n p)
  convElt-wf-src (conv-hide wf p na) = wf
  convElt-wf-src (conv-show wf p na) = wf-shift p wf
  convElt-wf-src (conv-fun ⊢s ⊢t) =
    wf-⇒ (conv-wf-tgt ⊢s) (conv-wf-src ⊢t)
  convElt-wf-src (conv-all ⊢s) = wf-∀ (conv-wf-src ⊢s)

  convElt-wf-tgt : ∀ {ĉ} → Sg ∣ Δᵢ ⊢̂ ĉ ∶ A ⇝ B ⊣ Δₑ → Δₑ ⊢ᵗ B
  convElt-wf-tgt (conv-seal rep rd p) = wf-var (pop-∋n p)
  convElt-wf-tgt (conv-unseal rep rd p na) = read-wf rd
  convElt-wf-tgt (conv-hide wf p na) = wf-shift p wf
  convElt-wf-tgt (conv-show wf p na) = wf
  convElt-wf-tgt (conv-fun ⊢s ⊢t) =
    wf-⇒ (conv-wf-src ⊢s) (conv-wf-tgt ⊢t)
  convElt-wf-tgt (conv-all ⊢s) = wf-∀ (conv-wf-tgt ⊢s)

  conv-wf-src : ∀ {c} → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δₑ → Δᵢ ⊢ᵗ A
  conv-wf-src (conv-id wf) = wf
  conv-wf-src (conv-cons hd tl) = convElt-wf-src hd

  conv-wf-tgt : ∀ {c} → Sg ∣ Δᵢ ⊢ c ∶ A ⇝ B ⊣ Δₑ → Δₑ ⊢ᵗ B
  conv-wf-tgt (conv-id wf) = wf
  conv-wf-tgt (conv-cons hd tl) = conv-wf-tgt tl

------------------------------------------------------------------------
-- Type substitution preserves well-formedness
------------------------------------------------------------------------

Substsᵗ : Substᵗ → Ctxᵗ → Ctxᵗ → Set
Substsᵗ σ Δ Δ′ = ∀ {X α} → Δ ∋n X := α → Δ′ ⊢ᵗ σ X

exts-substs : ∀ {σ Ss Ss′ Bs Bs′} → Substsᵗ σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → Substsᵗ (extsᵗ σ) (bind ∷ Ss ∥ Bs) (bind ∷ Ss′ ∥ Bs′)
exts-substs s n-here-bind = wf-var n-here-bind
exts-substs s (n-skip-bind-b p) = wf-⇑ (s p)
exts-substs s (n-skip-bind-l p) = wf-⇑ (s p)
exts-substs s (n-skip-bind-e p) = wf-⇑ (s p)

wf-subst : ∀ {σ Ss Ss′ Bs Bs′ A} → Substsᵗ σ (Ss ∥ Bs) (Ss′ ∥ Bs′)
  → (Ss ∥ Bs) ⊢ᵗ A → (Ss′ ∥ Bs′) ⊢ᵗ substᵗ σ A
wf-subst s (wf-var n) = s n
wf-subst s wf-ℕ = wf-ℕ
wf-subst s wf-𝔹 = wf-𝔹
wf-subst s (wf-⇒ a b) = wf-⇒ (wf-subst s a) (wf-subst s b)
wf-subst s (wf-∀ a) = wf-∀ (wf-subst (exts-substs s) a)

-- instantiating the outermost binder
wf-inst : ∀ {Ss Bs A B} → (bind ∷ Ss ∥ Bs) ⊢ᵗ B → (Ss ∥ Bs) ⊢ᵗ A
  → (Ss ∥ Bs) ⊢ᵗ B [ A ]ᵗ
wf-inst {Ss = Ss} {Bs = Bs} {A = A} wfB wfA = wf-subst single wfB
  where
  single : Substsᵗ (singleTyEnv A) (bind ∷ Ss ∥ Bs) (Ss ∥ Bs)
  single n-here-bind = wfA
  single (n-skip-bind-b p) = wf-var p
  single (n-skip-bind-l p) = wf-var p
  single (n-skip-bind-e p) = wf-var p

------------------------------------------------------------------------
-- A well-typed term's type is well formed
------------------------------------------------------------------------
-- The term context must be well formed too, which for the empty one
-- it vacuously is.

CtxOk : Ctxᵗ → Ctx → Set
CtxOk Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ⊢ᵗ A

ctxOk-[] : ∀ {Δ} → CtxOk Δ []
ctxOk-[] ()

typing-wf : ∀ {Sg Δ Γ M A} → CtxOk Δ Γ
  → Sg ∣ Δ ∣ Γ ⊢ M ⦂ A → Δ ⊢ᵗ A
typing-wf ok (⊢` x) = ok x
typing-wf ok ⊢$ = wf-ℕ
typing-wf ok ⊢# = wf-𝔹
typing-wf ok (⊢⊕ m n) = wf-ℕ
typing-wf ok (⊢ƛ wf body) = wf-⇒ wf (typing-wf (extend ok wf) body)
  where
  extend : ∀ {Δ Γ A} → CtxOk Δ Γ → Δ ⊢ᵗ A → CtxOk Δ (A ∷ Γ)
  extend ok wf here = wf
  extend ok wf (there p) = ok p
typing-wf ok (⊢· l m) with typing-wf ok l
typing-wf ok (⊢· l m) | wf-⇒ a b = b
-- the `Λ`'s body context has the SAME NUMBER of names as the `∀`'s,
-- though not the same entries: `asgn (bse zero) ∷ ⤒ Ss` against
-- `bind ∷ Ss`
typing-wf {Δ = Ss ∥ Bs} ok (⊢Λ v body) =
  wf-∀ (wf-len (cong suc (renStk-len suc Ss)) (typing-wf (ctxOk-⤊ ok) body))
  where
  renStk-len : ∀ ρ Ss → length (renStk ρ Ss) ≡ length Ss
  renStk-len ρ [] = refl
  renStk-len ρ (bind ∷ Ss) = cong suc (renStk-len ρ Ss)
  renStk-len ρ (asgn α ∷ Ss) = cong suc (renStk-len ρ Ss)
  ctxOk-⤊ : ∀ {Γ} → CtxOk (Ss ∥ Bs) Γ
    → CtxOk (asgn (bse zero) ∷ ⤒ Ss ∥ addr ∷ Bs) (⤊ Γ)
  ctxOk-⤊ {Γ = A ∷ Γ} ok′ here =
    wf-len (cong suc (sym (renStk-len suc Ss))) (wf-⇑ (ok′ here))
  ctxOk-⤊ {Γ = A ∷ Γ} ok′ (there p) = ctxOk-⤊ (λ q → ok′ (there q)) p
typing-wf ok (⊢•[] l wf) with typing-wf ok l
typing-wf ok (⊢•[] l wf) | wf-∀ b = wf-inst b wf
typing-wf {Δ = Ss ∥ Bs} ok (⊢ν wfR body) =
  wf-len (renStk-len suc Ss) (typing-wf (λ p → wf-len (sym (renStk-len suc Ss))
                                                      (ok p)) body)
  where
  renStk-len : ∀ ρ Ss → length (renStk ρ Ss) ≡ length Ss
  renStk-len ρ [] = refl
  renStk-len ρ (bind ∷ Ss) = cong suc (renStk-len ρ Ss)
  renStk-len ρ (asgn α ∷ Ss) = cong suc (renStk-len ρ Ss)
typing-wf ok (⊢⟨⟩ nf body conv) = conv-wf-tgt conv
