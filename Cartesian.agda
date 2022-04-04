open import Data.Float renaming (_≤ᵇ_ to _≤F?_ ; _≡ᵇ_ to _≡F?_)


data Bool : Set where
  false true : Bool

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

pred : Nat -> Nat
pred zero = zero
pred (succ n) = n

_+N_ : Nat -> Nat -> Nat
zero +N m = m
succ m +N n = succ (m +N n)

_*N_ : Nat -> Nat -> Nat
zero *N m = zero
succ n *N m = succ (n *N m) +N m

_<N_ : Nat → Nat → Bool
_ <N zero  = false
zero <N succ _ = true
succ n <N succ m = n <N m

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

mapList : {A B : Set} -> (A -> B) -> List A -> List B
mapList f [] = []
mapList f (x :: xs) = f x :: mapList f xs

data _x_ (A B : Set) : Set where
  <_,_> : A -> B -> A x B

fst : {A B : Set} -> A x B -> A
fst < a , b > = a

snd : {A B : Set} -> A x B -> B
snd < a , b > = b

-- The basic stuff is finished. Now the ApproxRatio.agda stuff.

ContFrac : Set
ContFrac = List Nat
