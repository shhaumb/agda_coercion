module CoercionExample where

open import Coercion

-------------------------------------------------------------

-- define natural numbers.
data Nat : Set where
  O : Nat
  S : Nat → Nat

{-# BUILTIN NATURAL Nat    #-}
{-# BUILTIN ZERO    O #-}
{-# BUILTIN SUC     S #-}

-- define coercion instance from Nat to Nat.
natIdentityCoercion : Nat ≤ Nat
natIdentityCoercion = identityCoercion

-------------------------------------------------------------

-- define True and False Sets

data True : Set where
  unit : True

data False : Set where

-------------------------------------------------------------

-- define Parity
data Parity : Set where
  even : Parity
  odd : Parity

changeParity : Parity → Parity
changeParity even = odd
changeParity odd = even

parityOf' : Nat → Parity
parityOf' O = even                          -- parity of 0 is even
parityOf' (S n) = changeParity (parityOf' n)  -- parity of (n+1) is opposite of parity of n

{- parityOf' 5 = odd
   parityOf' 8 = even
-}

{- let's define a parityOf function that can take any subtype of Nat
   for which coercion instance is defined and it returns the
   parity of that number. -}
parityOf : ∀ {n} → Nat :: n => Parity
parityOf = coercive parityOf'

-- define operator `==` on Parity
_==_ : Parity → Parity → Set
even == even = True
odd == odd = True
_ == _ = False  -- otherwise

-------------------------------------------------------------

{- creating a subtype of Nat that also contains the parity of
   the number as information in it's type -}
data NatP : Parity → Set where
  conP : (n : Nat) → NatP (parityOf' n)

{- conP 5 : NatP odd
   conP 8 : NatP even
-}

convertNatPtoNat : {p : Parity} → NatP p → Nat
convertNatPtoNat (conP n) = n

getParity : {p : Parity} → NatP p → Parity
getParity {p} _ = p

{- define coercion instance from (NatP even) to Nat as (NatP even)
   is subtype of Nat.
   coerce takes the function for this job
-}
natPevenCoercion : (NatP even) ≤ Nat
natPevenCoercion = coerce convertNatPtoNat

-- similarly
natPoddCoercion : (NatP odd) ≤ Nat
natPoddCoercion = coerce convertNatPtoNat

{- We had defined a parityOf function that can take
   any subtype of Nat. hence
   parityOf 3 = odd                 -- uses natIdentityCoercion
   parityOf 4 = even                -- uses natIdentityCoercion
   parityOf (conP 5) = odd          -- uses natPoddCoercion
   parityOf (conP 8) = even         -- uses natPevenCoercion
-}

-------------------------------------------------------------

-- type refinement

-- let's define a type similar to (NatP even) using type refinement
EvenNat = Nat & (λ x → parityOf' x == even)

-- define coercion instance from EvenNat to Nat
natEvenCoercion : EvenNat ≤ Nat
natEvenCoercion = refinementCoercion

-- let's declare a term of type EvenNat
m : EvenNat
m = # 6

{-
   parityOf m = even               -- uses natEvenCoercion
-}

-- similarly for odd natural numbers
OddNat = Nat & (λ x → parityOf' x == odd)

natOddCoercion : OddNat ≤ Nat
natOddCoercion = refinementCoercion

-------------------------------------------------------------

-- define a function that takes only even natural number and returns 0.

-- 1st method
f1 : NatP even → Nat
f1 _ = 0

{-
   f1 (conP 6) = 0
   f1 (conP 5) shows type error
-}


-- 2nd method
f2 : (n : Nat) → {{k : (parityOf' n) == even}} → Nat
f2 _ = 0

{-
   f2 6 = 0           -- `k = unit` of type True is found
   f2 5 shows error   -- no variable of type False is found
-}


-- 3rd method
f3 : EvenNat → Nat
f3 _ = 0

{-
   f3 (# 6) = 0
   f3 (# 5) shows error. -- no variable of type False is found
-}
