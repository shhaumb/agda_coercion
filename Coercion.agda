module Coercion where

open import Level

data _≤_ {l m} : (A : Set l) → (B : Set m) → Set (suc (l ⊔ m)) where
  coerce : {A : Set l} → {B : Set m} → (A → B) → (A ≤ B)

getfunc : ∀ {l m} → {A : Set l} → {B : Set m} → (A ≤ B) → (A → B)
getfunc (coerce f) = f

_::_=>_ : ∀ {l m} → Set l  → (n : Level) → Set m → Set ((suc l) ⊔ m ⊔ (suc n))
_::_=>_ x n y = {A : Set n} → (a : A) → {{c : A ≤ x}} → y

coercive : ∀ {l m n} → {A : Set l} → {B : Set m} → (A → B) → (A :: n => B)
coercive f a {{c}} = f ((getfunc c) a)

data _&_ : (A : Set) → (A → Set) → Set1 where
  #_ : {A : Set} → {f : A → Set} →  (a : A) → {{c : f a}} → (A & f)

identityCoercion : ∀ {l} → {A : Set l} → A ≤ A
identityCoercion {_} {A} = coerce (λ(x : A) → x)

refinementCoercionFunc : (A : Set) → (f : A → Set) → (A & f) → A
refinementCoercionFunc A f (# a) = a

refinementCoercion : {A : Set} → {f : A → Set} → ((A & f) ≤ A)
refinementCoercion {A} {f} = coerce (refinementCoercionFunc A f)
