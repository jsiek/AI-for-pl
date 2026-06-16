-- File Charter:
--   * Type checking and synthesis for well-scoped raw terms.
--   * Primary exports are context compatibility, elaboration evidence, `synth`,
--     and `check`.
--   * Depends on core types, labels, consistency, typed terms, and raw terms.

module TypeCheck where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Subset using (Subset; Side; inside; outside; _∈_)
open import Data.Vec using (_∷_)
open import Data.Product using (∃-syntax; Σ; proj₁; proj₂; _,_; _×_; map)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; inspect; [_])
  renaming (subst to substEq)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (id)

open import Types
open import Label using (Label)
open import Consistency
open import Terms as CT
open import RawTerms as RT

-- compatibility of scope and typing context

data comp-Γ {Δ : TyCtx} : RT.ExCtx → CT.ExCtx Δ → Set where

  comp-∅ : comp-Γ zero ∅

  comp-▷ : ∀ {Γr}{Γc : CT.ExCtx Δ}{T : Ty Δ} → comp-Γ Γr Γc → comp-Γ (suc Γr) (Γc ▷ T)

rename-comp-Γ :
  ∀ {Δ Δ′ Γr}{Γc : CT.ExCtx Δ} →
  (ρ : Renameᵗ Δ Δ′) →
  comp-Γ Γr Γc →
  comp-Γ Γr (renameᵉ ρ Γc)
rename-comp-Γ ρ comp-∅ = comp-∅
rename-comp-Γ ρ (comp-▷ comp) = comp-▷ (rename-comp-Γ ρ comp)

data comp-var {Δ : TyCtx} :
    ∀ {Γr Γc} →
    comp-Γ Γr Γc → (x : RT.ExVar Γr) → {T : Ty Δ} →
    CT.ExVar Γc T → Set where

  comp-Z : ∀ {Γr Γc T}{comp : comp-Γ Γr Γc} →
    comp-var {Γr = suc Γr} {Γc = Γc ▷ T}
             (comp-▷ {T = T} comp) zero Zᵉ

  comp-S : ∀ {Γr Γc T U x}{comp : comp-Γ Γr Γc}{xᵉ : CT.ExVar Γc T} →
    comp-var comp x xᵉ →
    comp-var {Γr = suc Γr} {Γc = Γc ▷ U}
             (comp-▷ {T = U} comp) (suc x) (Sᵉ xᵉ)

-- compatibility of expressions

data comp-E {Δ : TyCtx} {Ψ : Subset Δ} {Γr Γc} (comp :
     comp-Γ Γr Γc) : {T : Ty Δ} → RT.Ex Δ Γr → CT.Ex{Ψ = Ψ} Γc T → Set where

  comp-` : ∀ {T}{x}{xᵉ} →
    comp-var comp x xᵉ →
    comp-E comp {T} (` x) (` xᵉ)

  comp-cst : ∀ {b : Σ Base base-type} → comp-E comp {‵ b .proj₁} (cst b) (CT.cst b )

  comp-λ : ∀ {T U rt ct} →
    comp-E (comp-▷ comp) {U} rt ct →
    comp-E comp {T ⇒ U} (λx: T ⇒ rt) (CT.λx: T ⇒ ct)

  comp-app : ∀ {ℓ S T U V rt rt₁ ct ct₁}
      {S~T⇒U : Ψ ∣ ℓ ⊢ S ~ (T ⇒ U)} {V~T : Ψ ∣ ℓ ⊢ V ~ T} →
    ~-func {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T , U , S~T⇒U) →
    comp-E comp {S} rt ct →
    comp-E comp {V} rt₁ ct₁ →
    comp-E comp {U} (RT.app ℓ rt rt₁) (CT.app ct S~T⇒U ct₁ V~T)

  comp-ΛX : ∀ {T rt ct} →
    comp-E {Ψ = outside ∷ Ψ} (rename-comp-Γ Sᵗ comp) {T} rt ct →
    comp-E comp {`∀ T} (RT.ΛX rt) (CT.ΛX ct)

  comp-tapp : ∀ {ℓ S T U rt ct}{S~∀T : Ψ ∣ ℓ ⊢ S ~ (`∀ T)} →
    ~-poly {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T , S~∀T) →
    comp-E comp {S} rt ct →
    comp-E comp {T [ U ]ᵗ} (RT.tapp ℓ rt U) (CT.tapp ct S~∀T U)

comp-var-type-unique :
  ∀ {Δ Γr Γc}{comp : comp-Γ Γr Γc}{x : RT.ExVar Γr}
    {T U : Ty Δ}{xᵉ : CT.ExVar Γc T}{yᵉ : CT.ExVar Γc U} →
  comp-var comp x xᵉ →
  comp-var comp x yᵉ →
  T ≡ U
comp-var-type-unique comp-Z comp-Z = refl
comp-var-type-unique (comp-S x-comp) (comp-S y-comp) =
  comp-var-type-unique x-comp y-comp

yes-func-result-unique :
  ∀ {Δ Ψ}{ℓ : Label}{S T U T′ U′ : Ty Δ}
    {S~T⇒U : Ψ ∣ ℓ ⊢ S ~ (T ⇒ U)}
    {S~T′⇒U′ : Ψ ∣ ℓ ⊢ S ~ (T′ ⇒ U′)} →
  yes (T , U , S~T⇒U) ≡ yes (T′ , U′ , S~T′⇒U′) →
  U ≡ U′
yes-func-result-unique refl = refl

yes-func-domain-unique :
  ∀ {Δ Ψ}{ℓ : Label}{S T U T′ U′ : Ty Δ}
    {S~T⇒U : Ψ ∣ ℓ ⊢ S ~ (T ⇒ U)}
    {S~T′⇒U′ : Ψ ∣ ℓ ⊢ S ~ (T′ ⇒ U′)} →
  yes (T , U , S~T⇒U) ≡ yes (T′ , U′ , S~T′⇒U′) →
  T ≡ T′
yes-func-domain-unique refl = refl

func-result-unique :
  ∀ {Δ Ψ}{ℓ : Label}{S T U T′ U′ : Ty Δ}
    {S~T⇒U : Ψ ∣ ℓ ⊢ S ~ (T ⇒ U)}
    {S~T′⇒U′ : Ψ ∣ ℓ ⊢ S ~ (T′ ⇒ U′)} →
  ~-func {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T , U , S~T⇒U) →
  ~-func {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T′ , U′ , S~T′⇒U′) →
  U ≡ U′
func-result-unique ok ok′ = yes-func-result-unique (trans (sym ok) ok′)

func-domain-unique :
  ∀ {Δ Ψ}{ℓ : Label}{S T U T′ U′ : Ty Δ}
    {S~T⇒U : Ψ ∣ ℓ ⊢ S ~ (T ⇒ U)}
    {S~T′⇒U′ : Ψ ∣ ℓ ⊢ S ~ (T′ ⇒ U′)} →
  ~-func {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T , U , S~T⇒U) →
  ~-func {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T′ , U′ , S~T′⇒U′) →
  T ≡ T′
func-domain-unique ok ok′ = yes-func-domain-unique (trans (sym ok) ok′)

yes-poly-result-unique :
  ∀ {Δ Ψ}{ℓ : Label}{S : Ty Δ}{T T′ : Ty (suc Δ)}
    {S~∀T : Ψ ∣ ℓ ⊢ S ~ (`∀ T)}
    {S~∀T′ : Ψ ∣ ℓ ⊢ S ~ (`∀ T′)} →
  yes (T , S~∀T) ≡ yes (T′ , S~∀T′) →
  T ≡ T′
yes-poly-result-unique refl = refl

poly-result-unique :
  ∀ {Δ Ψ}{ℓ : Label}{S : Ty Δ}{T T′ : Ty (suc Δ)}
    {S~∀T : Ψ ∣ ℓ ⊢ S ~ (`∀ T)}
    {S~∀T′ : Ψ ∣ ℓ ⊢ S ~ (`∀ T′)} →
  ~-poly {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T , S~∀T) →
  ~-poly {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T′ , S~∀T′) →
  T ≡ T′
poly-result-unique ok ok′ = yes-poly-result-unique (trans (sym ok) ok′)

comp-E-type-unique :
  ∀ {Δ Ψ Γr Γc}{comp : comp-Γ Γr Γc}{rt : RT.Ex Δ Γr}
    {T U : Ty Δ}{ct : CT.Ex {Ψ = Ψ} Γc T}
    {ct′ : CT.Ex {Ψ = Ψ} Γc U} →
  comp-E comp rt ct →
  comp-E comp rt ct′ →
  T ≡ U
comp-E-type-unique (comp-` x-comp) (comp-` y-comp) =
  comp-var-type-unique x-comp y-comp
comp-E-type-unique comp-cst comp-cst = refl
comp-E-type-unique {rt = λx: T ⇒ rt} (comp-λ comp-ct)
                   (comp-λ comp-ct′) =
  cong (λ U → T ⇒ U) (comp-E-type-unique comp-ct comp-ct′)
comp-E-type-unique (comp-app func-ok comp-f comp-a)
                   (comp-app func-ok′ comp-f′ comp-a′)
  with comp-E-type-unique comp-f comp-f′
... | refl = func-result-unique func-ok func-ok′
comp-E-type-unique (comp-ΛX comp-ct) (comp-ΛX comp-ct′) =
  cong `∀ (comp-E-type-unique comp-ct comp-ct′)
comp-E-type-unique {rt = RT.tapp ℓ rt U} (comp-tapp poly-ok comp-ct)
                   (comp-tapp poly-ok′ comp-ct′)
  with comp-E-type-unique comp-ct comp-ct′
... | refl = cong (λ T → T [ U ]ᵗ) (poly-result-unique poly-ok poly-ok′)

app-no-func :
  ∀ {Δ Ψ}{ℓ : Label}{Γr Γc}{comp : comp-Γ Γr Γc}{rt rt₁ : RT.Ex Δ Γr}
    {A S T U : Ty Δ}
    {ct-f : CT.Ex {Ψ = Ψ} Γc A}
    {ct-f′ : CT.Ex {Ψ = Ψ} Γc S}
    {S~T⇒U : Ψ ∣ ℓ ⊢ S ~ (T ⇒ U)} →
  ¬ (Σ (Ty Δ) λ T → Σ (Ty Δ) λ U → Ψ ∣ ℓ ⊢ A ~ (T ⇒ U)) →
  comp-E comp rt ct-f →
  comp-E comp rt ct-f′ →
  ⊥
app-no-func {S~T⇒U = S~T⇒U} A≁⇒ comp-f comp-f′
  with comp-E-type-unique comp-f comp-f′
... | refl = A≁⇒ (_ , _ , S~T⇒U)

app-no-arg :
  ∀ {Δ Ψ}{ℓ : Label}{Γr Γc}{comp : comp-Γ Γr Γc}{rt rt₁ : RT.Ex Δ Γr}
    {A S T U T′ U′ V : Ty Δ}
    {ct-f : CT.Ex {Ψ = Ψ} Γc A}
    {ct-f′ : CT.Ex {Ψ = Ψ} Γc S}
    {ct-a : CT.Ex {Ψ = Ψ} Γc V}
    {A~T⇒U : Ψ ∣ ℓ ⊢ A ~ (T ⇒ U)}
    {S~T′⇒U′ : Ψ ∣ ℓ ⊢ S ~ (T′ ⇒ U′)}
    {V~T′ : Ψ ∣ ℓ ⊢ V ~ T′} →
  ¬ (Σ (Ty Δ) λ V →
     Σ (CT.Ex {Ψ = Ψ} Γc V) λ ct →
     (Ψ ∣ ℓ ⊢ V ~ T) × comp-E comp rt₁ ct) →
  ~-func {Ψ = Ψ} {ℓ = ℓ} A ≡ yes (T , U , A~T⇒U) →
  ~-func {Ψ = Ψ} {ℓ = ℓ} S ≡ yes (T′ , U′ , S~T′⇒U′) →
  comp-E comp rt ct-f →
  comp-E comp rt ct-f′ →
  comp-E comp rt₁ ct-a →
  ⊥
app-no-arg {ℓ = ℓ} {V~T′ = V~T′} arg≁ func-ok func-ok′ comp-f comp-f′ comp-a
  with comp-E-type-unique comp-f comp-f′
... | refl =
  arg≁ (_ , _ ,
        substEq (λ X → _ ∣ ℓ ⊢ _ ~ X)
                (sym (func-domain-unique func-ok func-ok′))
                V~T′ ,
        comp-a)

tapp-no-poly :
  ∀ {Δ Ψ}{ℓ : Label}{Γr Γc}{comp : comp-Γ Γr Γc}{rt : RT.Ex Δ Γr}
    {A S : Ty Δ}{B : Ty (suc Δ)}
    {ct : CT.Ex {Ψ = Ψ} Γc A}
    {ct′ : CT.Ex {Ψ = Ψ} Γc S}
    {S~∀B : Ψ ∣ ℓ ⊢ S ~ (`∀ B)} →
  ¬ (Σ (Ty (suc Δ)) λ B → Ψ ∣ ℓ ⊢ A ~ (`∀ B)) →
  comp-E comp rt ct →
  comp-E comp rt ct′ →
  ⊥
tapp-no-poly {S~∀B = S~∀B} A≁∀ comp-ct comp-ct′
  with comp-E-type-unique comp-ct comp-ct′
... | refl = A≁∀ (_ , S~∀B)

-- translation of variables across compatibility

mk-var : ∀ {Δ : TyCtx} {Γr : RT.ExCtx}
  → (Γc : CT.ExCtx Δ)
  → (comp : comp-Γ Γr Γc)
  → (x : RT.ExVar Γr)
  → Σ (Ty Δ) λ T
    → Σ (CT.ExVar Γc T) λ cx
    → comp-var comp x cx

mk-var (Γc ▷ T) (comp-▷ _) zero = T , Zᵉ , comp-Z
mk-var (Γc ▷ _) (comp-▷ comp) (suc x)
  with mk-var Γc comp x
... | T , cx , cx-comp = T , Sᵉ cx , comp-S cx-comp

-- bidirectional type checking

synth : ∀ {Δ : TyCtx} {Γr : RT.ExCtx}
  → (rt : RT.Ex Δ Γr)
  → (Γc : CT.ExCtx Δ)
  → (Ψ : Subset Δ)
  → (comp : comp-Γ Γr Γc)
  → Dec (Σ (Ty Δ) λ T →
         Σ (CT.Ex {Δ}{Ψ} Γc T) λ ct →
         comp-E comp rt ct )

check : ∀ {Δ : TyCtx} {Γr : RT.ExCtx}
  → (rt : RT.Ex Δ Γr)
  → (Γc : CT.ExCtx Δ)
  → (Ψ : Subset Δ)
  → (comp : comp-Γ Γr Γc)
  → (ℓ : Label)
  → (T : Ty Δ)
  → Dec (Σ (Ty Δ) λ V →
         Σ (CT.Ex {Δ}{Ψ} Γc V) λ ct →
         (Ψ ∣ ℓ ⊢ V ~ T) × comp-E comp rt ct)

synth (` x) Γc Ψ comp
  with mk-var Γc comp x
... | T , cx , cx-comp = yes (T , ` cx , comp-` cx-comp)

synth (cst b) Γc Ψ comp = yes ((‵ b .proj₁) , CT.cst b , comp-cst)

synth {Δ} (λx: T ⇒ rt) Γc Ψ comp
  with synth rt (Γc ▷ T) Ψ (comp-▷ comp)
... | yes (U , ct-body , comp-body) = yes ((T ⇒ U) , (λx: T ⇒ ct-body) , comp-λ comp-body)
... | no ¬ih = no (neg-body ¬ih)
    where
      neg-body :
        ¬ Σ (Ty Δ) (λ U → Σ (CT.Ex{Ψ = Ψ} (Γc ▷ T) U) (comp-E (comp-▷ comp) rt))
        → Σ (Ty Δ) (λ T₁ → Σ (CT.Ex{Ψ = Ψ} Γc T₁) (comp-E comp (λx: T ⇒ rt)))
        → ⊥
      neg-body ¬ih (_ , λx: T ⇒ ct-body , comp-λ comp-body) = ¬ih (_ , ct-body , comp-body)

synth (app ℓ rt rt₁) Γc Ψ comp
  with synth rt Γc Ψ comp
... | no ¬ih-f = no λ
  { (_ , _ , comp-app {S = sTy} {ct = ct-f′} func-ok comp-f′ comp-a) →
    ¬ih-f (sTy , ct-f′ , comp-f′) }
... | yes (A , ct-f , comp-f)
  with ~-func {Ψ = Ψ} {ℓ = ℓ} A
     | inspect (λ A → ~-func {Ψ = Ψ} {ℓ = ℓ} A) A
... | no r | _ = no λ
  { (_ , _ , comp-app {S = sTy} {T = tTy} {U = uTy} {ct = ct-f′}
                       {S~T⇒U = s~t⇒u} func-ok comp-f′ comp-a) →
    app-no-func {Ψ = Ψ} {comp = comp} {rt = rt} {rt₁ = rt₁}
                {A = A} {S = sTy} {T = tTy} {U = uTy}
                {ct-f = ct-f} {ct-f′ = ct-f′} {S~T⇒U = s~t⇒u}
                r comp-f comp-f′ }
... | yes (T , U , A~T⇒U) | [ func-ok ]
  with check rt₁ Γc Ψ comp ℓ T
... | no r = no λ
  { (_ , _ , comp-app {S = sTy} {T = tTy′} {U = uTy′} {V = vTy}
                       {ct = ct-f′} {ct₁ = ct-a}
                       {S~T⇒U = s~t′⇒u′} {V~T = v~t′}
                       func-ok′ comp-f′ comp-a) →
    app-no-arg {A = A} {S = sTy} {T = T} {U = U}
               {T′ = tTy′} {U′ = uTy′} {V = vTy}
               {ct-f = ct-f} {ct-f′ = ct-f′} {ct-a = ct-a}
               {A~T⇒U = A~T⇒U} {S~T′⇒U′ = s~t′⇒u′}
               {V~T′ = v~t′}
               r func-ok func-ok′ comp-f comp-f′ comp-a }
... | yes (V , ct-a , V~T , comp-a) =
  yes (U , app ct-f A~T⇒U ct-a V~T ,
       comp-app {S = A} {T = T} {U = U} {V = V}
                {S~T⇒U = A~T⇒U} {V~T = V~T}
                func-ok comp-f comp-a)

synth (ΛX rt) Γc Ψ comp
  with synth rt (renameᵉ Sᵗ Γc) (outside ∷ Ψ) (rename-comp-Γ Sᵗ comp)
... | no r = no λ
  { (_ , _ , comp-ΛX {ct = ct-body} comp-body) →
    r (_ , ct-body , comp-body) }
... | yes (B , ct-body , comp-body) = yes (`∀ B , ΛX ct-body , comp-ΛX comp-body)

synth (tapp ℓ rt U) Γc Ψ comp
  with synth rt Γc Ψ comp
... | no r = no λ
  { (_ , _ , comp-tapp {S = sTy} {ct = ct-body} poly-ok comp-body) →
    r (sTy , ct-body , comp-body) }
... | yes (A , ct-body , comp-body)
  with ~-poly {Ψ = Ψ} {ℓ = ℓ} A
     | inspect (λ A → ~-poly {Ψ = Ψ} {ℓ = ℓ} A) A
... | no r | _ = no λ
  { (_ , _ , comp-tapp {S = sTy} {T = bTy} {ct = ct-body′}
                         {S~∀T = s~∀b} poly-ok comp-body′) →
    tapp-no-poly {A = A} {S = sTy} {B = bTy}
                 {ct = ct-body} {ct′ = ct-body′} {S~∀B = s~∀b}
                 r comp-body comp-body′ }
... | yes (B , A~∀B) | [ poly-ok ] =
  yes (B [ U ]ᵗ , tapp ct-body A~∀B U , comp-tapp poly-ok comp-body)

check rt Γc Ψ comp ℓ T
  with synth rt Γc Ψ comp
... | no ¬Tct = no λ { (V , ct , V~T , comp-ct) →
  ¬Tct (V , ct , comp-ct) }
... | yes (U , ct , comp-ct)
  with A~B? {Ψ = Ψ} {ℓ = ℓ} U T
... | yes U~T = yes (U , ct , U~T , comp-ct)
... | no ¬U~T = no λ { (V , ct′ , V~T , comp-ct′) →
  ¬U~T (substEq (λ X → Ψ ∣ ℓ ⊢ X ~ T)
                (sym (comp-E-type-unique comp-ct comp-ct′))
                V~T) }
