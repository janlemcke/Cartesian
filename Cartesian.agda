{-# OPTIONS --guardedness #-}

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

infixr 20 _+_

_+_ : ℕ -> ℕ -> ℕ
zero + m = m
succ m + n = succ (m + n)

infixr 30 _*_

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
open _x_ public

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

x+1≡sx : (x : ℕ) → x + 1 ≡ succ x
x+1≡sx zero = refl
x+1≡sx (succ x) = cong (succ) (x+1≡sx x)

x*1≡x : (x : ℕ) → x * 1 ≡ x
x*1≡x zero = refl
x*1≡x (succ x) =
     ((x * 1) + 1)
      ≡⟨ cong (λ a → (a + 1)) (x*1≡x x) ⟩
     (x + 1)
      ≡⟨ x+1≡sx x ⟩
     succ x
      ∎


{-

Idee: Elemtenweise Formulierung für den Beweis der Gleichheit.

proof : (cf : ContFrac) → tail (convergents cf) ≡ convergents' cf
proof [] = refl
proof (a :: as) =
    let
      < p' , q' > = toℚ as
      f = (λ bn-2 → λ bn-1 → λ a → (bn-1 * a) + bn-2 )
    in
      tail (convergents (a :: as))
       ≡⟨ refl ⟩
      mapList toℚ (mapList (a ::_) (inits as))
       ≡⟨ {!!} {- cong (λ xs → mapList toℚ (mapList (a ::_) xs)) (inits as) -} ⟩
      mapList (λ xs → toℚ (a :: xs)) (inits as)
       ≡⟨ {!!} {- cong (λ xs → mapList (λ xs → < ((a * p') + q') , p' >) xs) (inits as) -} ⟩
      mapList (λ xs → < ((a * p') + q') , p' >) (inits as)
       ≡⟨ {!!} {- cong (λ xs → zip (mapList (λ xs → ((a * p') + q')) xs) (mapList (λ xs → p') xs)) (inits as) -} ⟩
      zip (mapList (λ xs → ((a * p') + q')) (inits as)) (mapList (λ xs → p') (inits as))
       ≡⟨ {!!} {- cong (λ xs → zip (scan2l 1 ((a * p') + q') f xs) (scan2l 1 p' f xs)) (inits as) -} ⟩
      zip (scan2l 1 ((a * p') + q') f as) (scan2l 1 p' f as)
       ≡⟨ {!!} {- cong (λ xs → zip (scan2l 1 ((a * p') + q') f xs) (scan2l 1 p' f xs)) (inits as) -} ⟩
      zip (scan2l 0 1 f (a :: as)) (scan2l 1 0 f (a :: as))
       ≡⟨ refl ⟩
      convergents' (a :: as)
      ∎
-}
-- Example computation

initsExmpl : inits (1 :: 2 :: 3 :: []) ≡ [] :: (1 :: []) :: (1 :: 2 :: []) :: (1 :: 2 :: 3 :: []) :: []
initsExmpl =
  inits (1 :: 2 :: 3 :: [])
    ≡⟨ refl
       {- Def. inits, 2nd pattern -} ⟩
  [] :: mapList (1 ::_) (inits (2 :: 3 :: []))
    ≡⟨ cong (λ xxs → [] :: mapList (1 ::_) xxs) refl
       {- Def. inits, 2nd pattern -} ⟩
  [] :: mapList (1 ::_) ([] :: mapList (2 ::_) (inits (3 :: [])))
    ≡⟨ cong ([] ::_) refl
       {- Def. mapList (1 ::_), 2nd pattern -} ⟩
  [] :: (1 :: []) :: mapList (1 ::_) (mapList (2 ::_) (inits (3 :: [])))
    ≡⟨ cong (λ xxs → [] :: (1 :: []) :: mapList (1 ::_) (mapList (2 ::_) xxs)) refl
       {- Def. inits, 2nd pattern -} ⟩
  [] :: (1 :: []) :: mapList (1 ::_) (mapList (2 ::_) ([] :: (mapList (3 ::_) (inits []))))
    ≡⟨ cong (λ xxs → [] :: (1 :: []) :: mapList (1 ::_) xxs) refl
       {- Def. mapList (2 ::_), 2nd pattern -} ⟩
  [] :: (1 :: []) :: mapList (1 ::_) ((2 :: []) :: mapList (2 ::_) ((mapList (3 ::_) (inits []))))
    ≡⟨ cong (λ xxs → [] :: (1 :: []) :: xxs) refl
       {- Def. mapList (1 ::_), 2nd pattern -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: mapList (1 ::_) (mapList (2 ::_) ((mapList (3 ::_) (inits []))))
    ≡⟨ refl
       {- Def. inits, 1st pattern ...
          I leave out the cong stuff from here on, after all, by definition we have
             cong f refl ≡ refl
          for an arbitrary function f ! -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: mapList (1 ::_) (mapList (2 ::_) ((mapList (3 ::_) ([] :: []))))
    ≡⟨ refl
       {- Def. mapList (3 ::_), 2nd pattern -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: mapList (1 ::_) (mapList (2 ::_) ((3 :: []) :: (mapList (3 ::_) [])))
    ≡⟨ refl
       {- Def. mapList (3 ::_), 1st pattern -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: mapList (1 ::_) (mapList (2 ::_) ((3 :: []) :: []))
    ≡⟨ refl
       {- Def. mapList (2 ::_), 2nd pattern -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: mapList (1 ::_) ((2 :: 3 :: []) :: mapList (2 ::_) [])
    ≡⟨ refl
       {- Def. mapList (2 ::_), 1st pattern -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: mapList (1 ::_) ((2 :: 3 :: []) :: [])
    ≡⟨ refl
       {- Def. mapList (1 ::_), 2nd pattern -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: (1 :: 2 :: 3 :: []) :: mapList (1 ::_) []
    ≡⟨ refl
       {- Def. mapList (1 ::_), 1st pattern -} ⟩
  [] :: (1 :: []) :: (1 :: 2 :: []) :: (1 :: 2 :: 3 :: []) :: []
    ∎



convExample : convergents' (1 :: 2 :: 3 :: []) ≡  < 1 , 1 > :: < 3 , 2 > :: < 10 , 7 > :: []
convExample =
  convergents' (1 :: 2 :: 3 :: [])
  ≡⟨ refl ⟩
  zip (numerators (1 :: 2 :: 3 :: [])) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (scan2l 0 1 f (1 :: 2 :: 3 :: []) ) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Def. scan2l, 2nd pattern -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (f 0 1 1 :: scan2l 1 (f 0 1 1) f (2 :: 3 :: [])) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Def. scan2l, 2nd pattern -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (f 0 1 1 :: (f 1 (f 0 1 1) 2 :: scan2l (f 0 1 1) (f 1 (f 0 1 1) 2) f (3 :: []))) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Def. scan2l, 2nd pattern -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (f 0 1 1 :: (f 1 (f 0 1 1) 2 :: (f (f 0 1 1) (f 1 (f 0 1 1) 2) 3 :: scan2l (f 1 (f 0 1 1) 2) (f (f 0 1 1) (f 1 (f 0 1 1) 2) 3) f []))) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Def. scan2l, 1nd pattern -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (f 0 1 1 :: (f 1 (f 0 1 1) 2 :: (f (f 0 1 1) (f 1 (f 0 1 1) 2) 3 :: []))) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Computation -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (1 :: (f 1 1 2 :: (f 1 (f 1 1 2) 3 :: []))) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Computation -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (1 :: (3 :: (f 1 3 3 :: []))) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Computation -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (1 :: (3 :: (10 :: []))) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl {- Def _::_  -}  ⟩
  let f = (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) in
    zip (1 :: 3 :: 10 :: []) (denominators  (1 :: 2 :: 3 :: []))
  ≡⟨ refl ⟩
  < 1 , 1 > :: < 3 , 2 > :: < 10 , 7 > :: []
  ∎


-- towards computing toℚ [1,2,3]

toℚLemma0 : toℚ [] ≡ < 1 , 0 >
toℚLemma0 = refl

toℚLemma1 : (a₀ : ℕ) → toℚ ( a₀ :: []) ≡ < a₀ , 1 >
toℚLemma1 a₀ =
  toℚ (a₀ :: [])
   ≡⟨ refl {- Def toℚ, 2md pattern -} ⟩
  let < p' , q' > = toℚ [] in
  < ((a₀ * p') + q') , p' >
   ≡⟨ cong (λ x → let < p' , q' > = x in < ((a₀ * p') + q') , p' > )  toℚLemma0 ⟩
  let < p' , q' > = < 1 , 0 > in
  < ((a₀ * p') + q') , p' >
   ≡⟨ refl {- Def. let ... -} ⟩
  < ((a₀ * 1) + 0) , 1 >
   ≡⟨ cong (λ x → < x , 1 > ) (x+0≡x (a₀ * 1)) ⟩
  < (a₀ * 1) , 1 >
   ≡⟨ cong (λ x → < x , 1 >) (x*1≡x a₀) ⟩
  < a₀ , 1 >
  ∎

toℚLemma2 : (a₀ a₁ : ℕ) → toℚ ( a₀ :: a₁ :: []) ≡ < (a₀ * a₁) + 1 , a₁ >
toℚLemma2 a₀ a₁ =
  toℚ (a₀ :: a₁ :: [])
    ≡⟨ refl {- Def toℚ, 2nd pattern -} ⟩
     let < p' , q' > = toℚ (a₁ :: []) in
    < ((a₀ * p') + q') , p' >
    ≡⟨ cong (λ x → let < p' , q' > = x in < ((a₀ * p') + q') , p' > )  (toℚLemma1 a₁) ⟩
     < (a₀ * a₁) + 1 , a₁ >
  ∎


-- infinite cf's might be useful

record Stream (A : Set) : Set where
  coinductive
  constructor _∷_     -- type as \::
  field
    first : A
    rest  : Stream A
open Stream public

ContFrac∞ : Set          -- type ∞ as \inf
ContFrac∞ = Stream ℕ

segment : ℕ → ContFrac∞ → ContFrac
segment zero cf = first cf :: []
segment (succ n) cf = first cf :: segment n (rest cf)

-- alternatively, we could encode infinite cf's as
-- functions from ℕ → ℕ

ContFrac∞Fun : Set
ContFrac∞Fun = ℕ → ℕ

segmentFun : ℕ → ContFrac∞Fun → ContFrac
segmentFun zero cf = cf zero :: []
segmentFun (succ n) cf = cf zero :: segmentFun n (cf ∘ succ)

convergentsFun : ContFrac∞Fun → ℕ → ℚ
convergentsFun cf n = toℚ (segmentFun n cf)

numsFun denomsFun : ContFrac∞Fun → ℕ → ℕ
numsFun   cf n = fst (convergentsFun cf n)
denomsFun cf n = snd (convergentsFun cf n)

cfTail : ContFrac∞Fun → ContFrac∞Fun
cfTail cf = cf ∘ succ

segmentFunLemma : (cf : ContFrac∞Fun) → (n : ℕ) → segmentFun (1 + n) cf ≡ cf 0 :: segmentFun n (cfTail cf)
segmentFunLemma cf zero     = refl
segmentFunLemma cf (succ n) = cong (cf 0 ::_) (segmentFunLemma (cfTail cf) n)


numsFunLemma : (cf : ContFrac∞Fun) → (n : ℕ) →
               numsFun cf (1 + n) ≡ cf 0  * numsFun (cfTail cf) n  + denomsFun (cfTail cf) n
numsFunLemma cf n = 
   numsFun cf (1 + n)
     ≡⟨⟩
   fst (toℚ (segmentFun (1 + n) cf))
     ≡⟨ cong (fst ∘ toℚ) (segmentFunLemma cf n) ⟩
   fst (toℚ (cf 0 :: segmentFun n (cfTail cf)))
     ≡⟨⟩ -- by definition of toℚ
   cf 0 * numsFun (cfTail cf) n + denomsFun (cfTail cf) n
     ∎

denomsFunLemma : (cf : ContFrac∞Fun) → (n : ℕ) →
                 denomsFun cf (1 + n) ≡ numsFun (cfTail cf) n
denomsFunLemma cf n = 
   denomsFun cf (1 + n)
     ≡⟨⟩ -- by definitions denomsFun and convergentsFun
   snd (toℚ (segmentFun (1 + n) cf))
     ≡⟨ cong (snd ∘ toℚ) (segmentFunLemma cf n) ⟩
   snd (toℚ (cf 0 :: segmentFun n (cfTail cf)))
     ≡⟨⟩ -- by definition of toℚ
   numsFun (cfTail cf) n
     ∎

numsFun0Lemma : (cf : ContFrac∞Fun) → numsFun cf 0 ≡ cf 0
numsFun0Lemma cf = 
  numsFun cf 0
    ≡⟨⟩
  fst (toℚ (segmentFun 0 cf))
    ≡⟨ cong fst (toℚLemma1 (cf 0)) ⟩
  cf 0
    ∎

denomsFun0Lemma : (cf : ContFrac∞Fun) → denomsFun cf 0 ≡ 1
denomsFun0Lemma cf =
  denomsFun cf 0
    ≡⟨⟩
  1
    ∎

numsFun1Lemma : (cf : ContFrac∞Fun) → numsFun cf 1 ≡ cf 0 * cf 1 + 1
numsFun1Lemma cf =
  numsFun cf 1
    ≡⟨⟩
  fst (toℚ (segmentFun 1 cf))
    ≡⟨ cong fst (toℚLemma2 (cf 0) (cf 1)) ⟩
  cf 0 * cf 1 + 1
    ∎

denomsFun1Lemma : (cf : ContFrac∞Fun) → denomsFun cf 1 ≡ cf 1
denomsFun1Lemma cf =
  denomsFun cf 1
    ≡⟨⟩
  snd (toℚ (segmentFun 1 cf))
    ≡⟨ cong snd (toℚLemma2 (cf 0) (cf 1)) ⟩
  cf 1
    ∎

mutual     -- we need mutual since we call theorem1Denoms in theorem1Nums and vice versa
  theorem1Nums : (cf : ContFrac∞Fun) → (n : ℕ) →
                 numsFun cf (2 + n) ≡ cf (2 + n) * numsFun cf (1 + n) + numsFun cf n
  theorem1Nums cf zero     = 
    let
      cf'  = cfTail cf
      cf'' = cfTail cf'
    in
      numsFun cf 2
        ≡⟨ numsFunLemma cf 1 ⟩
      cf 0 * numsFun cf' 1 + denomsFun cf' 1
        ≡⟨ cong (λ x → cf 0 * x + denomsFun cf' 1) (numsFun1Lemma cf') ⟩
      cf 0 * (cf' 0 * cf' 1 + 1) + denomsFun cf' 1
        ≡⟨ cong (λ x → cf 0 * (cf' 0 * cf' 1 + 1) + x) (denomsFun1Lemma cf') ⟩
      cf 0 * (cf' 0 * cf' 1 + 1) + cf' 1
        ≡⟨⟩  -- definition cfTail 
      cf 0 * (cf 1 * cf 2 + 1) + cf 2
        ≡⟨ {!!} ⟩   -- rest is arithmetic
      cf 2 * (cf 0 * cf 1 + 1)  +  cf 0
        ≡⟨ cong (λ x → cf 2 * x + cf 0) (sym (numsFun1Lemma cf)) ⟩
      cf 2 * numsFun cf 1  +  cf 0
        ≡⟨ cong (λ x → cf 2 * numsFun cf 1 + x) (sym (numsFun0Lemma cf)) ⟩
      cf 2 * numsFun cf 1  +  numsFun cf 0
        ∎
  
  theorem1Nums cf (succ n) =
    let
      cf'  = cfTail cf
      cf'' = cfTail cf'
    in
      numsFun cf (3 + n)
        ≡⟨ numsFunLemma cf (2 + n) ⟩
      cf 0  * numsFun cf' (2 + n) + denomsFun cf' (2 + n)
        ≡⟨ cong (λ x → cf 0 * x + denomsFun cf' (2 + n)) (theorem1Nums cf' n) ⟩
      cf 0  * (cf' (2 + n) * numsFun cf' (1 + n) + numsFun cf' n) + denomsFun cf' (2 + n)
        ≡⟨⟩ -- by def. on cfTail
      cf 0  * (cf (3 + n) * numsFun cf' (1 + n) + numsFun cf' n) + denomsFun cf' (2 + n)
        ≡⟨ cong (λ x → cf 0 * (cf (3 + n) * numsFun cf' (1 + n) + numsFun cf' n) + x) (theorem1Denoms cf' n) ⟩
      cf 0  * (cf (3 + n) * numsFun cf' (1 + n) + numsFun cf' n) + (cf' (2 + n) * denomsFun cf' (1 + n)) + denomsFun cf' n
        ≡⟨⟩
      cf 0  * (cf (3 + n) * numsFun cf' (1 + n) + numsFun cf' n) + (cf (3 + n) * denomsFun cf' (1 + n)) + denomsFun cf' n
        ≡⟨ {!!} ⟩  -- rest is arithmetic
      cf (3 + n) * (cf 0  * numsFun cf' (1 + n) + denomsFun cf' (1 + n)) + cf 0 * numsFun cf' n + denomsFun cf' n  
        ≡⟨ sym (cong (λ x → cf (3 + n) * x + numsFun cf (1 + n)) (numsFunLemma cf (1 + n))) ⟩ 
      cf (3 + n) * (cf 0  * numsFun cf' (1 + n) + denomsFun cf' (1 + n)) + numsFun cf (1 + n)  
        ≡⟨ sym (cong (λ x → cf (3 + n) * x + numsFun cf (1 + n)) (numsFunLemma cf (1 + n))) ⟩ 
      cf (3 + n) * numsFun cf (2 + n) + numsFun cf (1 + n)
        ∎
  
  theorem1Denoms : (cf : ContFrac∞Fun) → (n : ℕ) →
                   denomsFun cf (2 + n) ≡ (cf (2 + n) * denomsFun cf (1 + n)) + denomsFun cf n
  theorem1Denoms = {!!} -- analogous
