open import Data.Maybe renaming (map to mapMb)
open import Function.Base
open import Data.Unit
open import Data.Maybe.Categorical

data Bool : Set where
  false true : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

pred : ℕ -> ℕ
pred zero = zero
pred (succ n) = n

_+_ : ℕ -> ℕ -> ℕ
zero + m = m
succ m + n = succ (m + n)

_*_ : ℕ -> ℕ -> ℕ
zero * m = zero
succ n * m = succ (n * m) + m

_<_ : ℕ → ℕ → Bool
_ < zero  = false
zero < succ _ = true
succ n < succ m = n < m

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

mapList : {A B : Set} -> (A -> B) -> List A -> List B
mapList f [] = []
mapList f (x :: xs) = f x :: mapList f xs

data _x_ (A B : Set) : Set where
  <_,_> : A -> B -> A x B

fst : {A B : Set} -> A x B -> A
fst < a , b >  = a

snd : {A B : Set} -> A x B -> B
snd < a , b > = b

-- The basic stuff is finished. Now the ApproxRatio.agda stuff.

ContFrac : Set
ContFrac = List ℕ

ℚ : Set
ℚ = ℕ x ℕ

inits : List ℕ ->  List (List ℕ)
inits []       = [] :: []
inits (x :: xs) = [] :: mapList (x ::_) (inits xs)

_⊚_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → A → Maybe C
f ⊚ g = λ x → g x >>= f

toℚ : ContFrac → ℚ
toℚ [] = < succ zero , zero >
toℚ (a₀ :: as) =
  let
    < p' , q' > = toℚ as
  in
    < ((a₀ * p') + q') , p' >

convergents : ContFrac → List ℚ
convergents = (mapList toℚ) ∘ inits
