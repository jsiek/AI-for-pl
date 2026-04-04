module Heq where

open import Level using (Level)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

Hcong₁ :
  ∀ {a b}
    {A : Set a}
    {B : A → Set b}
    {x y}
    (f : (x : A) → B x)
    → x ≅ y
    → f x ≅ f y
Hcong₁ f H.refl = H.refl

Hcong₂ :
  ∀ {a b c}
    {A : Set a}
    {B : A → Set b}
    {C : ∀ x → B x → Set c}
    {x y u v}
    (f : (x : A) (y : B x) → C x y)
    → x ≅ y
    → u ≅ v
    → f x u ≅ f y v
Hcong₂ f H.refl H.refl = H.refl

Hcong₃ :
  ∀ {a b c d}
    {A : Set a}
    {B : A → Set b}
    {C : ∀ x → B x → Set c}
    {D : ∀ x → (y : B x) → C x y → Set d}
    {x y u v i j}
    (f : (x : A) (y : B x) (z : C x y) → D x y z)
    → x ≅ y
    → u ≅ v
    → i ≅ j
    → f x u i ≅ f y v j
Hcong₃ f H.refl H.refl H.refl = H.refl

Hcong₄ :
  ∀ {a b c d e}
    {A : Set a}
    {B : A → Set b}
    {C : ∀ x → B x → Set c}
    {D : ∀ x → (y : B x) → C x y → Set d}
    {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
    {x y u v i j p q}
    (f : (x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w)
    → x ≅ y
    → u ≅ v
    → i ≅ j
    → p ≅ q
    → f x u i p ≅ f y v j q
Hcong₄ f H.refl H.refl H.refl H.refl = H.refl

Hcong₅ :
  ∀ {a b c d e f}
    {A : Set a}
    {B : A → Set b}
    {C : ∀ x → B x → Set c}
    {D : ∀ x → (y : B x) → C x y → Set d}
    {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
    {F : ∀ x → (y : B x) → (z : C x y) → (w : D x y z) → E x y z w → Set f}
    {x y u v i j p q r s}
    (g : (x : A) (y : B x) (z : C x y) (w : D x y z) (t : E x y z w) → F x y z w t)
    → x ≅ y
    → u ≅ v
    → i ≅ j
    → p ≅ q
    → r ≅ s
    → g x u i p r ≅ g y v j q s
Hcong₅ g H.refl H.refl H.refl H.refl H.refl = H.refl
