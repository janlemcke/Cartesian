module Cartesian where

open import Data.Maybe renaming (map to mapMb) hiding (zip)
open import Relation.Binary.PropositionalEquality
open import Function.Base
open import Data.Unit
open import Data.Maybe.Categorical
open ≡-Reasoning


data Bool : Set where
  false true : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

pred : ℕ -> ℕ
pred zero = zero
pred (succ n) = n

_+_ : ℕ -> ℕ -> ℕ
zero + m = m
succ m + n = succ (m + n)

_*_ : ℕ -> ℕ -> ℕ
zero * m = zero
succ n * m = (n * m) + m

_<_ : ℕ → ℕ → Bool
_ < zero  = false
zero < succ _ = true
succ n < succ m = n < m

infixr 20 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

mapList : {A B : Set} -> (A -> B) -> List A -> List B
mapList f [] = []
mapList f (x :: xs) = f x :: mapList f xs

record _x_ (A B : Set) : Set where
  constructor <_,_>
  field
    fst : A
    snd : B


-- The basic stuff is finished. Now the ApproxRatio.agda stuff.

ContFrac : Set
ContFrac = List ℕ

ℚ : Set
ℚ = ℕ x ℕ

inits : List ℕ ->  List (List ℕ)
inits [] = [] :: []
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


-- zip works like a zipper, e.g.
-- zip [1,2,3] [a,b] = [< 1 , a > , < 2 , b >]
-- the length of the result is the length of the
-- shorter input list
zip : {A B : Set} → List A → List B → List (A x B)
zip [] bs = []
zip (a :: as) [] = []
zip (a :: as) (b :: bs) = < a , b > :: zip as bs

scan2l : {A B : Set} ->  B -> B -> (B -> B -> A -> B) -> List A -> List B
scan2l bn-2 bn-1 f [] = []
scan2l bn-2 bn-1 f (a :: as) = f bn-2 bn-1 a :: scan2l bn-1 (f bn-2 bn-1 a) f as

numerators denominators : ContFrac → List ℕ
-- 0 1 startbedingung für p
-- 1 0 startbedingungen für q, wobei n-2 das erste argument ist
numerators cf = scan2l 0 1 (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) cf
denominators cf = scan2l 1 0 (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) cf

convergents' : ContFrac → List ℚ
convergents' cf = zip (numerators cf) (denominators cf)

tail : {A : Set} -> List A -> List A
tail [] = []
tail (x :: xs) = xs

x+0≡x : (x : ℕ) → x + 0 ≡ x
x+0≡x zero = refl
x+0≡x (succ x) = cong succ (x+0≡x x)


proof : (cf : ContFrac) → tail (convergents cf) ≡ convergents' cf
proof [] = refl
proof (a :: as) =
    let
      < p' , q' > = toℚ as  
      f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 )
    in
      tail (convergents (a :: as))
      ≡⟨ refl ⟩
      mapList toℚ (mapList (a ::_) (inits as))
      ≡⟨ cong (λ xs → mapList toℚ (mapList (a ::_) xs)) (inits as) ⟩
      mapList (λ xs → toℚ (a :: xs)) (inits as)
      ≡⟨ cong (λ xs → mapList (λ xs → < ((a * p') + q') , p' >) xs) (inits as) ⟩
      mapList (λ xs → < ((a * p') + q') , p' >) (inits as)
      ≡⟨ cong (λ xs → zip (mapList (λ xs → ((a * p') + q')) xs) (mapList (λ xs → p') xs)) (inits as) ⟩
      zip (mapList (λ xs → ((a * p') + q')) (inits as)) (mapList (λ xs → p') (inits as))
      ≡⟨ cong (λ xs → zip (scan2l 1 ((a * p') + q') f xs) (scan2l 1 p' f xs)) (inits as) ⟩
      zip (scan2l 1 ((a * p') + q') f as) (scan2l 1 p' f as)
       ≡⟨ cong (λ xs → zip (scan2l 1 ((a * p') + q') f xs) (scan2l 1 p' f xs)) (inits as) ⟩
      zip (scan2l 0 1 f (a :: as)) (scan2l 1 0 f (a :: as))
      ≡⟨ refl ⟩
      convergents' (a :: as)


