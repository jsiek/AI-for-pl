module PolyGEval where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool renaming (true to btrue; false to bfalse) using (Bool)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product renaming (_×_ to _×ᵖ_) using (_,_)
open import Relation.Nullary using (Dec; yes; no)

open import PolyC
import PolyCProgress as Prog
open import PolyG

------------------------------------------------------------------------
-- Decidable equality helpers
------------------------------------------------------------------------

sameTyName : TyName → TyName → Bool
sameTyName α α₂ with Prog._≟TyName_ α α₂
... | yes _ = btrue
... | no _  = bfalse

sameGround : Ground → Ground → Bool
sameGround G H with Prog._≟Ground_ G H
... | yes _ = btrue
... | no _  = bfalse

------------------------------------------------------------------------
-- Boolean value test
------------------------------------------------------------------------

isValue : Term → Bool
isValue true = btrue
isValue false = btrue
isValue (seal α M) = isValue M
isValue (pair M N) with isValue M | isValue N
... | btrue | btrue = btrue
... | _     | _     = bfalse
isValue (lam A M) = btrue
isValue (tlam M) = btrue
isValue (inj G M) = isValue M
isValue (cast d (p ⇒⊑ q) M) = isValue M
isValue (cast d (pForall p) M) = isValue M
isValue (pack A cs M) = btrue
isValue _ = bfalse

------------------------------------------------------------------------
-- Deterministic one-step reduction
------------------------------------------------------------------------

cast-step : Store → Dir → Prec → Term → Maybe (Store ×ᵖ Term)
cast-step Σ d pDyn V = just (Σ , V)
cast-step Σ d (pName α) V = just (Σ , V)
cast-step Σ d pBool V = just (Σ , V)
cast-step Σ d (p ×⊑ q) (pair V₁ V₂) with isValue V₁ | isValue V₂
... | btrue | btrue = just (Σ , pair (cast d p V₁) (cast d q V₂))
... | _    | _    = nothing
cast-step Σ d (p ×⊑ q) V = nothing
cast-step Σ d (p ⇒⊑ q) V = nothing
cast-step Σ d (pExists p') (pack A cs M) = just (Σ , pack A (qcast d p' ∷ cs) M)
cast-step Σ d (pExists p') V = nothing
cast-step Σ d (pForall p') V = nothing
cast-step Σ up (pTag G p') V = just (Σ , inj G (cast up p' V))
cast-step Σ down (pTag G p') (inj H W) with isValue W | sameGround G H
... | btrue | btrue = just (Σ , cast down p' W)
... | btrue | bfalse = just (Σ , err)
... | bfalse | _ = nothing
cast-step Σ down (pTag G p') V = nothing

unseal-value-step : Store → TyName → Term → Maybe (Store ×ᵖ Term)
unseal-value-step Σ α (seal α' V) with isValue V | sameTyName α α'
... | btrue | btrue = just (Σ , V)
... | btrue | bfalse = nothing
... | bfalse | _ = nothing
unseal-value-step Σ α V = nothing

is-value-step : Store → Ground → Term → Maybe (Store ×ᵖ Term)
is-value-step Σ G (inj H V) with isValue V | sameGround G H
... | btrue | btrue = just (Σ , true)
... | btrue | bfalse = just (Σ , false)
... | bfalse | _ = nothing
is-value-step Σ G V = nothing

letpair-value-step : Store → Term → Term → Maybe (Store ×ᵖ Term)
letpair-value-step Σ N (pair V W) with isValue V | isValue W
... | btrue | btrue = just (Σ , N [ V ][ W ])
... | _ | _ = nothing
letpair-value-step Σ N M = nothing

app-beta-step : Store → Term → Term → Maybe (Store ×ᵖ Term)
app-beta-step Σ (lam A P) N = just (Σ , P [ N ])
app-beta-step Σ (cast d (p ⇒⊑ q) V) N with isValue V
... | btrue = just (Σ , cast d q (app V (cast (flipDir d) p N)))
... | bfalse = nothing
app-beta-step Σ M N = nothing

tapp-value-step : Store → TyName → Ty → Term → Maybe (Store ×ᵖ Term)
tapp-value-step Σ α A (tlam N) = just (Σ , substᵀ (singleTyEnv (nameTy α)) N)
tapp-value-step Σ α A (cast d (pForall p) V) with isValue V
... | btrue = just (Σ , cast d (substPrec (singleTyEnv (nameTy α)) p) (tapp V α A))
... | bfalse = nothing
tapp-value-step Σ α A M = nothing

stepC : Store → Term → Maybe (Store ×ᵖ Term)
stepC Σ (var x) = nothing
stepC Σ err = nothing
stepC Σ true = nothing
stepC Σ false = nothing
stepC Σ (letv M N) with M
... | err = just (Σ , err)
... | _ with isValue M
...   | btrue = just (Σ , N [ M ])
...   | bfalse with stepC Σ M
...     | nothing = nothing
...     | just (Σ' , M') = just (Σ' , letv M' N)
stepC Σ (seal α M) with M
... | err = just (Σ , err)
... | _ with isValue M
...   | btrue = nothing
...   | bfalse with stepC Σ M
...     | nothing = nothing
...     | just (Σ' , M') = just (Σ' , seal α M')
stepC Σ (unseal α M) with M
... | err = just (Σ , err)
... | _ with isValue M
...   | btrue = unseal-value-step Σ α M
...   | bfalse with stepC Σ M
...     | nothing = nothing
...     | just (Σ' , M') = just (Σ' , unseal α M')
stepC Σ (is G M) with M
... | err = just (Σ , err)
... | _ with isValue M
...   | btrue = is-value-step Σ G M
...   | bfalse with stepC Σ M
...     | nothing = nothing
...     | just (Σ' , M') = just (Σ' , is G M')
stepC Σ (ifte L M N) with L
... | err = just (Σ , err)
... | true = just (Σ , M)
... | false = just (Σ , N)
... | _ with stepC Σ L
...   | nothing = nothing
...   | just (Σ' , L') = just (Σ' , ifte L' M N)
stepC Σ (pair M N) with M | isValue M
... | err | _ = just (Σ , err)
stepC Σ (pair M N) | _ | btrue
    with N
... | err = just (Σ , err)
... | _ with isValue N
...   | btrue = nothing
...   | bfalse with stepC Σ N
...     | nothing = nothing
...     | just (Σ' , N') = just (Σ' , pair M N')
stepC Σ (pair M N) | _ | bfalse with stepC Σ M
...   | nothing = nothing
...   | just (Σ' , M') = just (Σ' , pair M' N)
stepC Σ (letpair M N) with M | isValue M
... | err | _ = just (Σ , err)
... | _ | btrue = letpair-value-step Σ N M
... | _ | bfalse with stepC Σ M
...   | nothing = nothing
...   | just (Σ' , M') = just (Σ' , letpair M' N)
stepC Σ (lam A M) = nothing
stepC Σ (app M N) with M | isValue M
... | err | _ = just (Σ , err)
stepC Σ (app M N) | _ | btrue
    with N | isValue N
... | err | _ = just (Σ , err)
... | _ | btrue = app-beta-step Σ M N
... | _ | bfalse with stepC Σ N
...   | nothing = nothing
...   | just (Σ' , N') = just (Σ' , app M N')
stepC Σ (app M N) | _ | bfalse with stepC Σ M
...   | nothing = nothing
...   | just (Σ' , M') = just (Σ' , app M' N)
stepC Σ (pack A cs M) = nothing
stepC Σ (unpack M N) with M | isValue M
... | err | _ = just (Σ , err)
... | pack A cs P | btrue = just ((Σ ∷ʳ A) , subst (singleEnv (applyCastStack (fresh Σ) cs P)) (substᵀ (singleTyEnv (nameTy (tseal (fresh Σ)))) N))
... | _ | btrue = nothing
... | _ | bfalse with stepC Σ M
...   | nothing = nothing
...   | just (Σ' , M') = just (Σ' , unpack M' N)
stepC Σ (tlam M) = nothing
stepC Σ (tapp M α A) with M | isValue M
... | err | _ = just (Σ , err)
... | _ | btrue = tapp-value-step Σ α A M
... | _ | bfalse with stepC Σ M
...   | nothing = nothing
...   | just (Σ' , M') = just (Σ' , tapp M' α A)
stepC Σ (hide A M) = just ((Σ ∷ʳ A) , substSealTerm (fresh Σ) M)
stepC Σ (inj G M) with M
... | err = just (Σ , err)
... | _ with isValue M
...   | btrue = nothing
...   | bfalse with stepC Σ M
...     | nothing = nothing
...     | just (Σ' , M') = just (Σ' , inj G M')
stepC Σ (cast d p M) with M
... | err = just (Σ , err)
... | _ with isValue M
...   | btrue = cast-step Σ d p M
...   | bfalse with stepC Σ M
...     | nothing = nothing
...     | just (Σ' , M') = just (Σ' , cast d p M')

------------------------------------------------------------------------
-- Fuel-based evaluator
------------------------------------------------------------------------

runC : ℕ → Store → Term → Store ×ᵖ Term
runC zero Σ M = Σ , M
runC (suc n) Σ M with stepC Σ M
... | nothing = Σ , M
... | just (Σ' , M') = runC n Σ' M'

evalPolyG :
  ℕ →
  {Δ : TyEnv} {M : GTerm} {A : Ty} →
  Δ ⊢g [] ⊢ M ⦂ A →
  Store ×ᵖ Term
evalPolyG n h = runC n [] (elab h)
