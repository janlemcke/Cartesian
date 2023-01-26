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
The `toℚ` function TODO??

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
convergents (1 :: 2 :: 3 :: []) == < 1 , 0 > :: < 1 , 1 > :: < 3 , 2 > :: < 10 , 7 > :: []
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

`scan2l` is a function that takes in 5 arguments: two initial values (bn-2 and bn-1) of type B, a binary function (f) that takes in two values of type B and one value of type A, and returns a value of type B, and a list of values of type A ([]). The function returns a list of values of type B.

The function starts by defining the base case, where if the input list is empty, it returns an empty list. Otherwise, it applies the binary function f to the initial values bn-2 and bn-1 and the first value in the input list (a). This result is consed onto the recursive call of the function, where bn-1 becomes the new bn-2 and the result of f becomes the new bn-1. The result is a list of values of type B.

```
numerators denominators : ContFrac → List ℕ
-- 0 1 startbedingung für p
-- 1 0 startbedingungen für q, wobei n-2 das erste argument ist
numerators cf = scan2l 0 1 (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) cf
denominators cf = scan2l 1 0 (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) cf
```

`numerators` and `denominators` are two functions that take in an argument of type `ContFrac` (a continued fraction). Both functions use the `scan2l` function defined earlier with different initial values and binary function.

The numerators function will generate the sequence of numerators of the continued fraction.

The denominators function will generate the sequence of denominators of the continued fraction.

##### Example

```
To proof:
numerators (1 :: 2 :: 3 :: []) == 1 :: 3 :: 10 :: []
denominators (1 :: 2 :: 3 :: []) == 1 :: 2 :: 7 :: []

numerators (1 :: 2 :: 3 :: [])
= scan2l 0 1 (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) (1 :: 2 :: 3 :: [])
= f 0 1 1 :: scan2l 1 (f 0 1 1) f (2 :: 3 :: [])
= f 0 1 1 :: f 1 (f 0 1 1) 2 :: scan2l (f 0 1 1) (f 1 (f 0 1 1) 2) f (3 :: [])
= f 0 1 1 :: f 1 (f 0 1 1) 2 :: f (f 0 1 1) (f 1 (f 0 1 1) 2) 3 :: scan2l (f 1 (f 0 1 1) 2) (f (f 0 1 1) (f 1 (f 0 1 1) 2) 3) f []

// base case reached
= f 0 1 1 :: f 1 (f 0 1 1) 2 :: f (f 0 1 1) (f 1 (f 0 1 1) 2) 3 :: []

// Remember: f(bn-2, bn-1, a) = (bn-1 * a) + bn-2)

// f 0 1 1 = (1 * 1) + 0 = 1
= 1 :: f 1 1 2 :: f 1 (f 1 1 2) 3 :: []

// f 1 1 2 = (1 * 2) + 1 = 3
= 1 :: 3 :: f 1 3 3 :: []

// f 1 3 3 = (3 * 3) + 1 = 10
= 1 :: 3 :: 10 :: []

scan2l bn-2 bn-1 f [] = []
scan2l bn-2 bn-1 f (a :: as) = f bn-2 bn-1 a :: scan2l bn-1 (f bn-2 bn-1 a) f as

denominators (1 :: 2 :: 3 :: [])
= scan2l 1 0 (\bn-2 -> \bn-1 -> \a -> (bn-1 * a) + bn-2 ) (1 :: 2 :: 3 :: [])
= scan2l 1 0 f (1 :: 2 :: 3 :: [])
= f 1 0 1 :: scan2l 0 (f 1 0 1) f (2 :: 3 :: [])
= f 1 0 1 :: f 0 (f 1 0 1) 2 :: scan2l (f 1 0 1) (f 0 (f 1 0 1) 2) f (3 :: [])
= f 1 0 1 :: f 0 (f 1 0 1) 2 :: f (f 1 0 1) (f 0 (f 1 0 1) 2) 3 :: scan2l (f 0 (f 1 0 1) 2) (f (f 1 0 1) (f 0 (f 1 0 1) 2) 3) f []

// base case reached
= f 1 0 1 :: f 0 (f 1 0 1) 2 :: f (f 1 0 1) (f 0 (f 1 0 1) 2) 3 :: []

// Remember: f(bn-2, bn-1, a) = (bn-1 * a) + bn-2)

// f 1 0 1 = (0 * 1) + 1 = 1
= 1 :: f 0 1 2 :: f 1 (f 0 1 2) 3 :: []

// f 0 1 2 = (1 * 2) + 0 = 2
= 1 :: 2 :: f 1 2 3 :: []

// f 1 2 3 = (2 * 3) + 1 = 7
= 1 :: 2 :: 7 :: []

```

After `denominators`and `numerators` , we have two lists and we need to zip them into a continous fraction.

```
convergents' : ContFrac → List ℚ
convergents' cf = zip (numerators cf) (denominators cf)
```

##### Example
```
convergents' (1 :: 2 :: 3 :: []) == < 1 , 1 > :: < 3 , 2 > :: < 10 , 7 > :: []
```

We see that we roughly get the exact same result, but the result of convergents has one tuple to much as a head. That's why we need to show that the tail of the result is the same as the result of convergents'.

-----------------

## Proof that tail(convergents cf) == convergents'cf
```
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
      
```
