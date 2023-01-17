# Cartesian

```
ContFrac : Set
ContFrac = List ℕ

ℚ : Set
ℚ = ℕ x ℕ
```

ContFrac is defined to be a synonym for List ℕ, which means that it is a type consisting of a list of natural numbers.

ℚ is defined to be the Cartesian product of ℕ and ℕ, using the record type x defined earlier. This means that it is a type that consists of a pair of natural numbers, with the first component being accessed via the field `fst` and the second component being accessed via the field `snd` .


```
inits : List ℕ ->  List (List ℕ)
inits [] = [] :: []
inits (x :: xs) = [] :: mapList (x ::_) (inits xs)
```
The function "inits" returns a list of all the possible initial segments of the input list.
For example, if the input list is [1,2,3], inits will return [[], [1], [1,2], [1,2,3]].

##### Example
```
inits [1,2,3]
= mapList (x :: _) (inits [2,3]) [1] :: [inits [2,3]]
= mapList (x :: _) ([2] :: [2,3]) [1] :: [[2], [2,3]]
= mapList (x :: _) ([3] :: [3]) [1] :: [[2], [2,3], [3]]
= [[], [1], [1,2], [1,2,3]]
# output from agda console
= [] :: (1 :: []) :: (1 :: 2 :: []) :: (1 :: 2 :: 3 :: []) :: []
```


```
_⊚_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → A → Maybe C
f ⊚ g = λ x → g x >>= f
```
This operator composes two functions, f and g, such that the output of g is passed as the input to f.

```
toℚ : ContFrac → ℚ
toℚ [] = < succ zero , zero >
toℚ (a₀ :: as) =
  let
    < p' , q' > = toℚ as
  in
    < ((a₀ * p') + q') , p' >
```

##### Example
```
toQ (1 :: 2 :: 3 :: []) != < 10 , 7>
= < ((1 * p') + q') , p' > toℚ [2,3]
= < ((1 * p') + q') , p' > < ((2 * p') + q') , p' > toℚ [3]
= < ((1 * p') + q') , p' > < ((2 * p') + q') , p' > < ((3 * p') + q') , p' > toℚ []
= < ((1 * p') + q') , p' > < ((2 * p') + q') , p' > < ((3 * p') + q') , p' > < succ zero, zero >
= < ((1 * p') + q') , p' > < ((2 * p') + q') , p' > < ((3 * p') + q') , p' > < 1, 0 >
= < ((1 * p') + q') , p' > < ((2 * p') + q') , p' > < ((3 * 1) + 0) , 1 >
= < ((1 * p') + q') , p' > < ((2 * p') + q') , p' > < 3, 1 >
= < ((1 * p') + q') , p' > < ((2 * 3) + 1) , 3 >
= < ((1 * p') + q') , p' > < 7 , 3 >
= < ((1 * 7) + 3) , 7 >
= < 10 , 7 >

```
10/7 = 1.42857142857

## Convergents
The first proposal to calculate the convergents is the following:

```
convergents : ContFrac → List ℚ
convergents = (mapList toℚ) ∘ inits
```

##### Example
```
convergents (1 :: 2 :: 3 :: []) != < 1 , 0 > :: < 1 , 1 > :: < 3 , 2 > :: < 10 , 7 > :: []
```
3/2 = 1.5

10/7 = 1.42857142857


## Convergents'

```
zip : {A B : Set} → List A → List B → List (A x B)
zip [] bs = []
zip (a :: as) [] = []
zip (a :: as) (b :: bs) = < a , b > :: zip as bs
```
The `zip` works like a zipper, for example: zip [1,2,3] [a,b] = [< 1 , a > , < 2 , b >] .The length of the result is the length of the shorter input list.

```
scan2l : {A B : Set} ->  B -> B -> (B -> B -> A -> B) -> List A -> List B
scan2l bn-2 bn-1 f [] = []
scan2l bn-2 bn-1 f (a :: as) = f bn-2 bn-1 a :: scan2l bn-1 (f bn-2 bn-1 a) f as
```

