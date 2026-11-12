{-

  File Charter:
    * Laws of renaming and substitution by a traversal with a kit
      (Subst/Kit.agda), after the denotational_semantics repository
      (proof/Framework/Syntax/TypedSubst.agda).
    * All equations between substitutions are pointwise, so no function
      extensionality is needed.
    * Two laws are by induction on the language's terms, so each
      language proves them: two traversals fuse into one (`Fuse`, for a
      relation between the two substitutions and the one that is kept
      under a binder and agrees on variables), and substituting
      variables for themselves is the identity (`SubId`).  For kits with
      laws (`Laws`), both hypotheses are closed under a binder
      (`trav-trav-exts`, `trav-id-exts`).  From the two inductions, the
      module `Lemmas` derives the rest:
        - `ren-trav`, `sub-ren`: a renaming then a traversal, a
          substitution then a renaming;
        - `Laws`, `varL`, `tmL`: what both kits satisfy;
        - `trav-trav`: any two traversals fuse, when their kits have
          laws (`ren-ren`, `ren-sub`, `sub-sub` are instances);
        - `trav-cong`, `ren-id`, `trav-id`, `ren-as-sub`;
        - single substitution: `sub-⇑-•`, `⇑-[]`, `exts-[]`, `trav-[]`
          (`ren-[]`, `sub-[]`).

-}

open import Subst.Scope using (Scope)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans;
  cong; module ≡-Reasoning)

module Subst.proof.Kit (𝒮 : Scope) (let open Scope 𝒮)
  (Tm : Sc → Sort → Set) (`_ : ∀ {Γ A} → Var Γ A → Tm Γ A) where

open import Subst.Kit 𝒮 Tm `_ public
open ≡-Reasoning

{- Computation laws of cons and exts ---------------------------------------}

cons-here : ∀ {Γ B} {F : Sort → Set} (a : F B) (f : ∀ {A} → Var Γ A → F A)
  → cons {F = F} a f here ≡ a
cons-here {F = F} a f = var-ind-here (λ {A} _ → F A) a f

cons-there : ∀ {Γ B} {F : Sort → Set} (a : F B) (f : ∀ {A} → Var Γ A → F A)
  → ∀ {A} (x : Var Γ A) → cons {F = F} a f (there x) ≡ f x
cons-there {F = F} a f x = var-ind-there (λ {A} _ → F A) a f x

exts-here : ∀ 𝒦 {Γ Δ B} (σ : Sub 𝒦 Γ Δ)
  → exts 𝒦 {B = B} σ here ≡ Kit.vr 𝒦 here
exts-here 𝒦 σ =
  cons-here {F = Kit.K 𝒦 _} (Kit.vr 𝒦 here) (λ x → Kit.wk 𝒦 (σ x))

exts-there : ∀ 𝒦 {Γ Δ B A} (σ : Sub 𝒦 Γ Δ) (x : Var Γ A)
  → exts 𝒦 {B = B} σ (there x) ≡ Kit.wk 𝒦 (σ x)
exts-there 𝒦 σ x =
  cons-there {F = Kit.K 𝒦 _} (Kit.vr 𝒦 here) (λ y → Kit.wk 𝒦 (σ y)) x

exts-cong : ∀ 𝒦 {Γ Δ B} {σ τ : Sub 𝒦 Γ Δ}
  → (∀ {A} (x : Var Γ A) → σ x ≡ τ x)
  → ∀ {A} (x : Var (Γ ▷ B) A) → exts 𝒦 σ x ≡ exts 𝒦 τ x
exts-cong 𝒦 {σ = σ} {τ} h =
  var-ind (λ x → exts 𝒦 σ x ≡ exts 𝒦 τ x)
    (trans (exts-here 𝒦 σ) (sym (exts-here 𝒦 τ)))
    (λ x → trans (exts-there 𝒦 σ x)
             (trans (cong (Kit.wk 𝒦) (h x)) (sym (exts-there 𝒦 τ x))))

{- The laws, for a language's traversal ------------------------------------}

module Traversal
  (trav : (𝒦 : Kit) → ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A)
  (trav-var : ∀ 𝒦 {Γ Δ A} (σ : Sub 𝒦 Γ Δ) (x : Var Γ A)
    → trav 𝒦 σ (` x) ≡ Kit.tm 𝒦 (σ x)) where

  open Substitution trav public

  {- What a language proves by induction on its terms ---------------------}

  Fuse : Set₁
  Fuse =
    ∀ (𝒦₁ 𝒦₂ 𝒦₃ : Kit)
    (R : ∀ {Γ Δ Θ} → Sub 𝒦₁ Γ Δ → Sub 𝒦₂ Δ Θ → Sub 𝒦₃ Γ Θ → Set)
    → (∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
        → R σ₁ σ₂ σ₃ → R (exts 𝒦₁ {B = B} σ₁) (exts 𝒦₂ σ₂) (exts 𝒦₃ σ₃))
    → (∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
        → R σ₁ σ₂ σ₃ → ∀ {A} (x : Var Γ A)
        → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
    → ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
      → R σ₁ σ₂ σ₃ → ∀ {A} (M : Tm Γ A)
      → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M

  SubId : Set
  SubId =
    ∀ {Γ A} {σ : Sub tmK Γ Γ}
    → (∀ {B} (x : Var Γ B) → σ x ≡ ` x)
    → (M : Tm Γ A)
    → sub σ M ≡ M

  {- what the identity needs under a binder -}
  sub-id-exts : ∀ {Γ C} {σ : Sub tmK Γ Γ}
    → (∀ {B} (x : Var Γ B) → σ x ≡ ` x)
    → ∀ {B} (x : Var (Γ ▷ C) B)
    → exts tmK σ x ≡ ` x
  sub-id-exts {σ = σ} h =
    var-ind (λ x → exts tmK σ x ≡ ` x)
      (exts-here tmK σ)
      (λ x → trans (exts-there tmK σ x)
               (trans (cong ⇑ (h x)) (trav-var varK there x)))

  {- what both kits satisfy -}
  record Laws (𝒦 : Kit) : Set where
    field
      tm-vr : ∀ {Γ A} (x : Var Γ A) → Kit.tm 𝒦 (Kit.vr 𝒦 x) ≡ ` x
      tm-wk : ∀ {Γ A B} (k : Kit.K 𝒦 Γ A)
        → Kit.tm 𝒦 (Kit.wk 𝒦 {B = B} k) ≡ ⇑ (Kit.tm 𝒦 k)
      exts-ren : ∀ {Γ Δ A B} (τ : Sub 𝒦 Γ Δ) (M : Tm Γ A)
        → trav 𝒦 (exts 𝒦 {B = B} τ) (⇑ M) ≡ ⇑ (trav 𝒦 τ M)

  {- a substitution that acts as the identity on variables still does
     under a binder -}
  trav-id-exts : ∀ {𝒦} → Laws 𝒦
    → ∀ {Γ C} {σ : Sub 𝒦 Γ Γ}
    → (∀ {B} (x : Var Γ B) → Kit.tm 𝒦 (σ x) ≡ ` x)
    → ∀ {B} (x : Var (Γ ▷ C) B)
    → Kit.tm 𝒦 (exts 𝒦 σ x) ≡ ` x
  trav-id-exts {𝒦} L {σ = σ} h =
    var-ind (λ x → Kit.tm 𝒦 (exts 𝒦 σ x) ≡ ` x)
      (trans (cong (Kit.tm 𝒦) (exts-here 𝒦 σ)) (Laws.tm-vr L here))
      (λ x → begin
         Kit.tm 𝒦 (exts 𝒦 σ (there x))
       ≡⟨ cong (Kit.tm 𝒦) (exts-there 𝒦 σ x) ⟩
         Kit.tm 𝒦 (Kit.wk 𝒦 (σ x))
       ≡⟨ Laws.tm-wk L (σ x) ⟩
         ⇑ (Kit.tm 𝒦 (σ x))
       ≡⟨ cong ⇑ (h x) ⟩
         ⇑ (` x)
       ≡⟨ trav-var varK there x ⟩
         ` (there x)
       ∎)

  {- two traversals that fuse on variables still do under a binder -}
  trav-trav-exts : ∀ {𝒦₁ 𝒦₂ 𝒦₃} → Laws 𝒦₁ → Laws 𝒦₂ → Laws 𝒦₃
    → ∀ {Γ Δ Θ B} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
    → (∀ {C} (x : Var Γ C)
         → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
    → ∀ {C} (x : Var (Γ ▷ B) C)
    → trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (exts 𝒦₁ σ₁ x))
      ≡ Kit.tm 𝒦₃ (exts 𝒦₃ σ₃ x)
  trav-trav-exts {𝒦₁} {𝒦₂} {𝒦₃} L₁ L₂ L₃ {σ₁ = σ₁} {σ₂} {σ₃} h =
    var-ind
      (λ x → trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (exts 𝒦₁ σ₁ x))
             ≡ Kit.tm 𝒦₃ (exts 𝒦₃ σ₃ x))
      (begin
         trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (exts 𝒦₁ σ₁ here))
       ≡⟨ cong (λ k → trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ k))
            (exts-here 𝒦₁ σ₁) ⟩
         trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (Kit.vr 𝒦₁ here))
       ≡⟨ cong (trav 𝒦₂ (exts 𝒦₂ σ₂)) (Laws.tm-vr L₁ here) ⟩
         trav 𝒦₂ (exts 𝒦₂ σ₂) (` here)
       ≡⟨ trav-var 𝒦₂ (exts 𝒦₂ σ₂) here ⟩
         Kit.tm 𝒦₂ (exts 𝒦₂ σ₂ here)
       ≡⟨ cong (Kit.tm 𝒦₂) (exts-here 𝒦₂ σ₂) ⟩
         Kit.tm 𝒦₂ (Kit.vr 𝒦₂ here)
       ≡⟨ Laws.tm-vr L₂ here ⟩
         ` here
       ≡⟨ sym (Laws.tm-vr L₃ here) ⟩
         Kit.tm 𝒦₃ (Kit.vr 𝒦₃ here)
       ≡⟨ sym (cong (Kit.tm 𝒦₃) (exts-here 𝒦₃ σ₃)) ⟩
         Kit.tm 𝒦₃ (exts 𝒦₃ σ₃ here)
       ∎)
      (λ x → begin
         trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (exts 𝒦₁ σ₁ (there x)))
       ≡⟨ cong (λ k → trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ k))
            (exts-there 𝒦₁ σ₁ x) ⟩
         trav 𝒦₂ (exts 𝒦₂ σ₂) (Kit.tm 𝒦₁ (Kit.wk 𝒦₁ (σ₁ x)))
       ≡⟨ cong (trav 𝒦₂ (exts 𝒦₂ σ₂)) (Laws.tm-wk L₁ (σ₁ x)) ⟩
         trav 𝒦₂ (exts 𝒦₂ σ₂) (⇑ (Kit.tm 𝒦₁ (σ₁ x)))
       ≡⟨ Laws.exts-ren L₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ⟩
         ⇑ (trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)))
       ≡⟨ cong ⇑ (h x) ⟩
         ⇑ (Kit.tm 𝒦₃ (σ₃ x))
       ≡⟨ sym (Laws.tm-wk L₃ (σ₃ x)) ⟩
         Kit.tm 𝒦₃ (Kit.wk 𝒦₃ (σ₃ x))
       ≡⟨ sym (cong (Kit.tm 𝒦₃) (exts-there 𝒦₃ σ₃ x)) ⟩
         Kit.tm 𝒦₃ (exts 𝒦₃ σ₃ (there x))
       ∎)

  {- The consequences -----------------------------------------------------}

  module Lemmas (fuse : Fuse) (sub-id : SubId) where

    {- a renaming, then a traversal -}
    ren-trav : ∀ 𝒦 {Γ Δ Θ} {r : ∀ {B} → Var Γ B → Var Δ B}
      {σ : Sub 𝒦 Δ Θ} {τ : Sub 𝒦 Γ Θ}
      → (∀ {B} (x : Var Γ B) → σ (r x) ≡ τ x)
      → ∀ {A} (M : Tm Γ A)
      → trav 𝒦 σ (ren r M) ≡ trav 𝒦 τ M
    ren-trav 𝒦 =
      fuse varK 𝒦 𝒦 (λ r σ τ → ∀ {B} (x : Var _ B) → σ (r x) ≡ τ x)
        (λ { {σ₁ = r} {σ} {τ} h →
             var-ind (λ x → exts 𝒦 σ (exts varK r x) ≡ exts 𝒦 τ x)
               (trans (cong (λ y → exts 𝒦 σ y) (exts-here varK r))
                  (trans (exts-here 𝒦 σ) (sym (exts-here 𝒦 τ))))
               (λ x → trans (cong (λ y → exts 𝒦 σ y) (exts-there varK r x))
                        (trans (exts-there 𝒦 σ (r x))
                           (trans (cong (Kit.wk 𝒦) (h x))
                              (sym (exts-there 𝒦 τ x))))) })
        (λ { {σ₁ = r} {σ} h x
             → trans (trav-var 𝒦 σ (r x)) (cong (Kit.tm 𝒦) (h x)) })

    {- a substitution, then a renaming -}
    sub-ren : ∀ {Γ Δ Θ} {σ : Sub tmK Γ Δ} {r : ∀ {B} → Var Δ B → Var Θ B}
      {τ : Sub tmK Γ Θ}
      → (∀ {B} (x : Var Γ B) → ren r (σ x) ≡ τ x)
      → ∀ {A} (M : Tm Γ A)
      → ren r (sub σ M) ≡ sub τ M
    sub-ren =
      fuse tmK varK tmK (λ σ r τ → ∀ {B} (x : Var _ B) → ren r (σ x) ≡ τ x)
        (λ { {σ₁ = σ} {r} {τ} h →
             var-ind (λ x → ren (exts varK r) (exts tmK σ x) ≡ exts tmK τ x)
               (begin
                  ren (exts varK r) (exts tmK σ here)
                ≡⟨ cong (ren (exts varK r)) (exts-here tmK σ) ⟩
                  ren (exts varK r) (` here)
                ≡⟨ trav-var varK (exts varK r) here ⟩
                  ` (exts varK r here)
                ≡⟨ cong `_ (exts-here varK r) ⟩
                  ` here
                ≡⟨ sym (exts-here tmK τ) ⟩
                  exts tmK τ here
                ∎)
               (λ x → begin
                  ren (exts varK r) (exts tmK σ (there x))
                ≡⟨ cong (ren (exts varK r)) (exts-there tmK σ x) ⟩
                  ren (exts varK r) (⇑ (σ x))
                ≡⟨ ren-trav varK (λ y → exts-there varK r y) (σ x) ⟩
                  ren (λ y → there (r y)) (σ x)
                ≡⟨ sym (ren-trav varK (λ _ → refl) (σ x)) ⟩
                  ⇑ (ren r (σ x))
                ≡⟨ cong ⇑ (h x) ⟩
                  ⇑ (τ x)
                ≡⟨ sym (exts-there tmK τ x) ⟩
                  exts tmK τ (there x)
                ∎) })
        (λ h x → h x)

    varL : Laws varK
    varL = record
      { tm-vr = λ _ → refl
      ; tm-wk = λ k → sym (trav-var varK there k)
      ; exts-ren = λ τ M →
          trans (ren-trav varK (λ y → exts-there varK τ y) M)
                (sym (ren-trav varK (λ _ → refl) M))
      }

    tmL : Laws tmK
    tmL = record
      { tm-vr = λ _ → refl
      ; tm-wk = λ _ → refl
      ; exts-ren = λ τ M →
          trans (ren-trav tmK (λ y → exts-there tmK τ y) M)
                (sym (sub-ren (λ _ → refl) M))
      }

    {- any two traversals, when their kits have laws -}
    trav-trav : ∀ {𝒦₁ 𝒦₂ 𝒦₃} → Laws 𝒦₁ → Laws 𝒦₂ → Laws 𝒦₃
      → ∀ {Γ Δ Θ} {σ₁ : Sub 𝒦₁ Γ Δ} {σ₂ : Sub 𝒦₂ Δ Θ} {σ₃ : Sub 𝒦₃ Γ Θ}
      → (∀ {B} (x : Var Γ B)
           → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
      → ∀ {A} (M : Tm Γ A)
      → trav 𝒦₂ σ₂ (trav 𝒦₁ σ₁ M) ≡ trav 𝒦₃ σ₃ M
    trav-trav {𝒦₁} {𝒦₂} {𝒦₃} L₁ L₂ L₃ =
      fuse 𝒦₁ 𝒦₂ 𝒦₃
        (λ σ₁ σ₂ σ₃ → ∀ {B} (x : Var _ B)
           → trav 𝒦₂ σ₂ (Kit.tm 𝒦₁ (σ₁ x)) ≡ Kit.tm 𝒦₃ (σ₃ x))
        (trav-trav-exts L₁ L₂ L₃)
        (λ h x → h x)

    {- the instances of fusion with one kit throughout -}
    ren-ren : ∀ {Γ Δ Θ} {r₁ : ∀ {B} → Var Γ B → Var Δ B}
      {r₂ : ∀ {B} → Var Δ B → Var Θ B} {r₃ : ∀ {B} → Var Γ B → Var Θ B}
      → (∀ {B} (x : Var Γ B) → r₂ (r₁ x) ≡ r₃ x)
      → ∀ {A} (M : Tm Γ A)
      → ren r₂ (ren r₁ M) ≡ ren r₃ M
    ren-ren = ren-trav varK

    ren-sub : ∀ {Γ Δ Θ} {r : ∀ {B} → Var Γ B → Var Δ B}
      {σ : Sub tmK Δ Θ} {τ : Sub tmK Γ Θ}
      → (∀ {B} (x : Var Γ B) → σ (r x) ≡ τ x)
      → ∀ {A} (M : Tm Γ A)
      → sub σ (ren r M) ≡ sub τ M
    ren-sub = ren-trav tmK

    sub-sub : ∀ {Γ Δ Θ} {σ : Sub tmK Γ Δ} {τ : Sub tmK Δ Θ}
      {ρ : Sub tmK Γ Θ}
      → (∀ {B} (x : Var Γ B) → sub τ (σ x) ≡ ρ x)
      → ∀ {A} (M : Tm Γ A)
      → sub τ (sub σ M) ≡ sub ρ M
    sub-sub = trav-trav tmL tmL tmL

    {- pointwise equal substitutions act equally -}
    trav-cong : ∀ 𝒦 {Γ Δ} {σ τ : Sub 𝒦 Γ Δ}
      → (∀ {B} (x : Var Γ B) → σ x ≡ τ x)
      → ∀ {A} (M : Tm Γ A)
      → trav 𝒦 σ M ≡ trav 𝒦 τ M
    trav-cong 𝒦 {σ = σ} {τ} h M =
      trans (sym (ren-trav 𝒦 {r = λ x → x} {σ = σ} {τ = σ} (λ _ → refl) M))
            (ren-trav 𝒦 {r = λ x → x} h M)

    ren-cong : ∀ {Γ Δ} {r s : ∀ {B} → Var Γ B → Var Δ B}
      → (∀ {B} (x : Var Γ B) → r x ≡ s x)
      → ∀ {A} (M : Tm Γ A)
      → ren r M ≡ ren s M
    ren-cong = trav-cong varK

    sub-cong : ∀ {Γ Δ} {σ τ : Sub tmK Γ Δ}
      → (∀ {B} (x : Var Γ B) → σ x ≡ τ x)
      → ∀ {A} (M : Tm Γ A)
      → sub σ M ≡ sub τ M
    sub-cong = trav-cong tmK

    {- renaming is substitution by variables -}
    ren-as-sub : ∀ {Γ Δ} (r : ∀ {B} → Var Γ B → Var Δ B)
      → ∀ {A} (M : Tm Γ A)
      → ren r M ≡ sub (λ x → ` (r x)) M
    ren-as-sub r M =
      trans (sym (sub-id (λ _ → refl) (ren r M)))
            (ren-trav tmK (λ _ → refl) M)

    {- the identity -}
    ren-id : ∀ {Γ} {r : ∀ {B} → Var Γ B → Var Γ B}
      → (∀ {B} (x : Var Γ B) → r x ≡ x)
      → ∀ {A} (M : Tm Γ A)
      → ren r M ≡ M
    ren-id {r = r} h M =
      trans (ren-as-sub r M) (sub-id (λ x → cong `_ (h x)) M)

    trav-id : ∀ {𝒦} → Laws 𝒦
      → ∀ {Γ} {σ : Sub 𝒦 Γ Γ}
      → (∀ {B} (x : Var Γ B) → Kit.tm 𝒦 (σ x) ≡ ` x)
      → ∀ {A} (M : Tm Γ A)
      → trav 𝒦 σ M ≡ M
    trav-id {𝒦} L {σ = σ} h M =
      begin
        trav 𝒦 σ M
      ≡⟨ sym (sub-id (λ _ → refl) (trav 𝒦 σ M)) ⟩
        sub ids (trav 𝒦 σ M)
      ≡⟨ trav-trav L tmL tmL
           (λ x → trans (sub-id (λ _ → refl) (Kit.tm 𝒦 (σ x))) (h x)) M ⟩
        sub ids M
      ≡⟨ sub-id (λ _ → refl) M ⟩
        M
      ∎

    {- Single substitution ------------------------------------------------}

    {- substituting into a weakened term skips the cons -}
    sub-⇑-• : ∀ {Γ Δ A B} (W : Tm Δ B) (σ : Sub tmK Γ Δ) (M : Tm Γ A)
      → sub (W • σ) (⇑ M) ≡ sub σ M
    sub-⇑-• {Δ = Δ} W σ M = ren-sub (λ x → cons-there {F = Tm Δ} W σ x) M

    ⇑-[] : ∀ {Γ A B} (M : Tm Γ A) (W : Tm Γ B) → ⇑ M [ W ] ≡ M
    ⇑-[] M W = trans (sub-⇑-• W ids M) (sub-id (λ _ → refl) M)

    {- under a binder, then for the bound variable -}
    exts-[] : ∀ {Γ Δ A B} (σ : Sub tmK Γ Δ) (N : Tm (Γ ▷ B) A) (W : Tm Δ B)
      → sub (exts tmK σ) N [ W ] ≡ sub (W • σ) N
    exts-[] {Γ} {Δ} σ N W =
      sub-sub
        (var-ind (λ x → sub (W • ids) (exts tmK σ x) ≡ (W • σ) x)
          (begin
             sub (W • ids) (exts tmK σ here)
           ≡⟨ cong (sub (W • ids)) (exts-here tmK σ) ⟩
             sub (W • ids) (` here)
           ≡⟨ trav-var tmK (W • ids) here ⟩
             (W • ids) here
           ≡⟨ cons-here {F = Tm Δ} W ids ⟩
             W
           ≡⟨ sym (cons-here {F = Tm Δ} W σ) ⟩
             (W • σ) here
           ∎)
          (λ x → begin
             sub (W • ids) (exts tmK σ (there x))
           ≡⟨ cong (sub (W • ids)) (exts-there tmK σ x) ⟩
             sub (W • ids) (⇑ (σ x))
           ≡⟨ ⇑-[] (σ x) W ⟩
             σ x
           ≡⟨ sym (cons-there {F = Tm Δ} W σ x) ⟩
             (W • σ) (there x)
           ∎))
        N

    {- a traversal commutes with a single substitution -}
    trav-[] : ∀ {𝒦} → Laws 𝒦
      → ∀ {Γ Δ A B} (σ : Sub 𝒦 Γ Δ) (N : Tm (Γ ▷ B) A) (M : Tm Γ B)
      → trav 𝒦 σ (N [ M ]) ≡ trav 𝒦 (exts 𝒦 σ) N [ trav 𝒦 σ M ]
    trav-[] {𝒦} L {Γ} {Δ} σ N M =
      begin
        trav 𝒦 σ (N [ M ])
      ≡⟨ trav-trav tmL L tmL (λ _ → refl) N ⟩
        sub (λ x → trav 𝒦 σ ((M • ids) x)) N
      ≡⟨ sub-cong pt N ⟩
        sub (λ x → sub (W • ids) (Kit.tm 𝒦 (exts 𝒦 σ x))) N
      ≡⟨ sym (trav-trav L tmL tmL (λ _ → refl) N) ⟩
        trav 𝒦 (exts 𝒦 σ) N [ W ]
      ∎
      where
      W = trav 𝒦 σ M
      pt : ∀ {C} (x : Var (Γ ▷ _) C)
        → trav 𝒦 σ ((M • ids) x)
          ≡ sub (W • ids) (Kit.tm 𝒦 (exts 𝒦 σ x))
      pt = var-ind
        (λ x → trav 𝒦 σ ((M • ids) x)
               ≡ sub (W • ids) (Kit.tm 𝒦 (exts 𝒦 σ x)))
        (begin
           trav 𝒦 σ ((M • ids) here)
         ≡⟨ cong (trav 𝒦 σ) (cons-here {F = Tm Γ} M ids) ⟩
           W
         ≡⟨ sym (cons-here {F = Tm Δ} W ids) ⟩
           (W • ids) here
         ≡⟨ sym (trav-var tmK (W • ids) here) ⟩
           sub (W • ids) (` here)
         ≡⟨ cong (sub (W • ids)) (sym (Laws.tm-vr L here)) ⟩
           sub (W • ids) (Kit.tm 𝒦 (Kit.vr 𝒦 here))
         ≡⟨ cong (λ k → sub (W • ids) (Kit.tm 𝒦 k)) (sym (exts-here 𝒦 σ)) ⟩
           sub (W • ids) (Kit.tm 𝒦 (exts 𝒦 σ here))
         ∎)
        (λ x → begin
           trav 𝒦 σ ((M • ids) (there x))
         ≡⟨ cong (trav 𝒦 σ) (cons-there {F = Tm Γ} M ids x) ⟩
           trav 𝒦 σ (` x)
         ≡⟨ trav-var 𝒦 σ x ⟩
           Kit.tm 𝒦 (σ x)
         ≡⟨ sym (⇑-[] (Kit.tm 𝒦 (σ x)) W) ⟩
           sub (W • ids) (⇑ (Kit.tm 𝒦 (σ x)))
         ≡⟨ cong (sub (W • ids)) (sym (Laws.tm-wk L (σ x))) ⟩
           sub (W • ids) (Kit.tm 𝒦 (Kit.wk 𝒦 (σ x)))
         ≡⟨ cong (λ k → sub (W • ids) (Kit.tm 𝒦 k)) (sym (exts-there 𝒦 σ x)) ⟩
           sub (W • ids) (Kit.tm 𝒦 (exts 𝒦 σ (there x)))
         ∎)

    ren-[] : ∀ {Γ Δ A B} (r : ∀ {C} → Var Γ C → Var Δ C)
      (N : Tm (Γ ▷ B) A) (M : Tm Γ B)
      → ren r (N [ M ]) ≡ ren (exts varK r) N [ ren r M ]
    ren-[] = trav-[] varL

    sub-[] : ∀ {Γ Δ A B} (σ : Sub tmK Γ Δ) (N : Tm (Γ ▷ B) A) (M : Tm Γ B)
      → sub σ (N [ M ]) ≡ sub (exts tmK σ) N [ sub σ M ]
    sub-[] = trav-[] tmL
