{-# OPTIONS --without-K #-}

module Cartesian2 where


{--  new attempt

1. from the start, use infinite continued fractions, encoded as
   functions ℕ → ℕ

2. instead of defining convergents, just define the sequences of numerators
   and denominators by mutual recursion  (nums dens)

3. prove the recursion formulas for numerators and denominators by
   mutual induction, close to Khinchin

-}

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 10 _+_

_+_ : ℕ -> ℕ -> ℕ
zero + m = m
succ m + n = succ (m + n)

infixl 11 _*_

_*_ : ℕ -> ℕ -> ℕ
zero * m = zero
succ n * m = (n * m) + m

infixr 20 _::_
data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A


-- arithmetic lemmata

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

x*0≡0 : (x : ℕ) → x * 0 ≡ 0
x*0≡0 zero = refl
x*0≡0 (succ x) = 
  (x * 0) + 0
    ≡⟨ cong (λ y → y + 0) (x*0≡0 x) ⟩
  0 + 0
    ≡⟨ refl ⟩
  0
    ∎

+assoc : (x y z : ℕ) → x + (y + z) ≡ x + y + z
+assoc zero y z = refl
+assoc (succ x) y z = cong succ ( +assoc x y z )

+assoc' : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+assoc' zero y z = refl
+assoc' (succ x) y z = cong succ (+assoc' x y z)



+comm : (x y : ℕ) → x + y ≡ y + x
+comm zero y = sym (x+0≡x y)
+comm (succ x) y = 
  succ (x + y)
    ≡⟨ cong succ (+comm x y) ⟩
  succ (y + x)
    ≡⟨ sym (x+1≡sx (y + x)) ⟩
  y + x + 1
    ≡⟨ sym (+assoc y x 1) ⟩
  y + (x + 1)
    ≡⟨ cong (y +_) (x+1≡sx x) ⟩
  y + succ x
    ∎

*+dist : (x y z : ℕ) → x * (y + z) ≡ x * y + x * z
*+dist zero y z = refl
*+dist (succ x) y z = 
  x * (y + z) + (y + z)
    ≡⟨ cong (λ w → w + (y + z)) (*+dist x y z) ⟩
  x * y + x * z + (y + z)
    ≡⟨ sym (+assoc (x * y) (x * z) _) ⟩
  x * y + (x * z + (y + z))
    ≡⟨ cong (x * y +_) (+assoc (x * z) y z) ⟩
  x * y + (x * z + y + z)
    ≡⟨ cong (λ w → x * y + (w + z)) (+comm (x * z) y) ⟩
  x * y + (y + x * z + z)
    ≡⟨ cong (x * y +_) (sym (+assoc y (x * z) z)) ⟩
  x * y + (y + (x * z + z))
    ≡⟨ +assoc (x * y) y _ ⟩
  x * y + y + (x * z + z)
    ∎


*comm : (x y : ℕ) → x * y ≡ y * x
*comm zero y = sym (x*0≡0 y)
*comm (succ x) y = 
  x * y + y
    ≡⟨ cong (_+ y) (*comm x y) ⟩
  y * x + y
    ≡⟨ cong (y * x +_) (sym (x*1≡x y)) ⟩
  y * x + y * 1
    ≡⟨ sym (*+dist y x 1) ⟩
  y * (x + 1)
    ≡⟨ cong (y *_) (x+1≡sx x) ⟩
  y * succ x
    ∎

*+dist' : (x y z : ℕ) → (y + z) * x ≡ y * x + z * x
*+dist' x y z =
  (y + z) * x
    ≡⟨ *comm (y + z) x ⟩
  x * (y + z)
    ≡⟨ *+dist x y z ⟩
  x * y + x * z
    ≡⟨ cong (_+ (x * z)) (*comm x y) ⟩
  y * x + x * z
    ≡⟨ cong (y * x +_) (*comm x z) ⟩
  y * x + z * x
    ∎
    
*assoc : (x y z : ℕ) → x * (y * z) ≡ x * y * z
*assoc zero y z = refl
*assoc (succ x) y z = 
  x * (y * z) + y * z
    ≡⟨ cong (_+ y * z) (*assoc x y z) ⟩
  x * y * z + y * z
    ≡⟨ sym (*+dist' z (x * y) y) ⟩
  (x * y + y) * z
    ∎



infix 3 _∘_

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(f ∘ g) a = f (g a) 


CF : Set
CF = ℕ → ℕ

mutual
  nums dens : CF → ℕ → ℕ
  nums cf zero = cf 0
  nums cf (succ n) = 
    let
      a₀ = cf 0
      tail = cf ∘ succ
      p' = nums tail n
      q' = dens tail n
    in
      a₀ * p' + q'
  dens cf zero = 1
  dens cf (succ n) = 
    let
      tail = cf ∘ succ
      p' = nums tail n
    in
      p'

-- helper to show the first values of a function of type ℕ → ℕ

showfirst : (ℕ → ℕ) → ℕ → List ℕ
showfirst f zero = []
showfirst f (succ n) = f zero :: showfirst (f ∘ succ) n


-- example: the continued fraction for the golden ratio
-- check:  nums τ , dens τ   are the Fibonacci sequence (in nums τ without first 1)

τ : CF
τ n = 1

-- we just prove the recursions (numsRec , densRec) mutually
-- compare Khinchin Theorem 1 pp 4 and 5

mutual
  numsRec : ∀ cf n →
            nums cf (succ (succ n)) ≡ cf (succ (succ n)) * nums cf (succ n) + nums cf n
  numsRec cf zero = 
    let
      a₀ = cf 0
      a₁ = cf 1
      a₂ = cf 2
    in
      a₀ * (a₁ * a₂ + 1) + a₂
        ≡⟨ cong (λ xs → xs + a₂) (*comm (a₀) (a₁ * a₂ + 1)) ⟩
       (a₁ * a₂ + 1) * a₀ + a₂
        ≡⟨ cong (λ xs → xs + a₂) (*+dist' (a₀) (a₁ * a₂) 1) ⟩
      (a₁ * a₂ * a₀ + 1 * a₀) + a₂
        ≡⟨ cong (λ xs → (a₁ * a₂ * a₀ + xs) + a₂) (refl)   ⟩
      (a₁ * a₂ * a₀ + a₀) + a₂
        ≡⟨ refl ⟩
      a₁ * a₂ * a₀ + a₀ + a₂
        ≡⟨ +assoc' (a₁ * a₂ * a₀) (a₀) (a₂) ⟩
      a₁ * a₂ * a₀ + (a₀ + a₂)
        ≡⟨ cong (λ xs → a₁ * a₂ * a₀ + xs) (+comm a₀ a₂) ⟩
      a₁ * a₂ * a₀ + (a₂ + a₀)
        ≡⟨ +assoc (a₁ * a₂ * a₀) a₂ a₀ ⟩
      a₁ * a₂ * a₀ + a₂ + a₀
        ≡⟨ cong ( λ xs → a₁ * a₂ * a₀ + xs + a₀) refl ⟩
      a₁ * a₂ * a₀ + 1 * a₂ + a₀
        ≡⟨ cong (λ xs → xs * a₀ + 1 * a₂ + a₀) (*comm a₁ a₂) ⟩
      a₂ * a₁ * a₀ + 1 * a₂ + a₀
        ≡⟨ cong (λ xs → a₂ * a₁ * a₀ + xs + a₀) (*comm 1 a₂) ⟩ 
      a₂ * a₁ * a₀ + a₂ * 1 + a₀
        ≡⟨ cong (λ xs → xs + a₂ * 1 + a₀) (sym (*assoc a₂ a₁ a₀)) ⟩ 
      a₂ * (a₁ * a₀) + a₂ * 1 + a₀
        ≡⟨ cong (_+ a₀) (sym (*+dist a₂ (a₁ * a₀) 1)) {- *+dist a₂ (a₁ * a₀) 1 -}⟩
      a₂ * ((a₁ * a₀) + 1) + a₀
        ≡⟨ cong ((λ xs →  a₂ * (xs + 1) + a₀)) (*comm (a₁) (a₀)) ⟩
      a₂ * ((a₀ * a₁) + 1) + a₀
       ≡⟨ refl ⟩
      a₂ * (a₀ * a₁ + 1) + a₀
      ∎
      
  numsRec cf (succ m) =      -- n = succ (succ (succ m))
    let
      a₀ = cf 0
      aₙ = cf (succ (succ (succ m)))
      pₙ = nums cf (succ (succ (succ m)))
      pₙ₋₁ = nums cf (succ (succ m))
      pₙ₋₂ = nums cf (succ m)
      qₙ = dens cf (succ (succ (succ m)))
      p'ₙ₋₁ = nums (cf ∘ succ) (succ (succ m))
      p'ₙ₋₂ = nums (cf ∘ succ) (succ m)
      p'ₙ₋₃ = nums (cf ∘ succ) m
      q'ₙ₋₁ = dens (cf ∘ succ) (succ (succ m))
      q'ₙ₋₂ = dens (cf ∘ succ) (succ m)
      q'ₙ₋₃ = dens (cf ∘ succ) m
      {- note that
        pₙ ≡ a₀ * p'ₙ₋₁ + q'ₙ₋₁
        qₙ ≡ p'ₙ₋₁
        and similarly for n-1 and n-2
        hold by definition of nums and dens and thus
        can be proved by refl !!
      -}
      IHnums : p'ₙ₋₁ ≡ aₙ * p'ₙ₋₂ + p'ₙ₋₃
      IHnums = numsRec (cf ∘ succ) m
      IHdens : q'ₙ₋₁ ≡ aₙ * q'ₙ₋₂ + q'ₙ₋₃
      IHdens = densRec (cf ∘ succ) m
    in
      pₙ
        ≡⟨ refl {- Def. nums -}⟩
      a₀ * p'ₙ₋₁ + q'ₙ₋₁
        ≡⟨ cong (λ x → a₀ * x + q'ₙ₋₁) IHnums ⟩
      a₀ * (aₙ * p'ₙ₋₂ + p'ₙ₋₃) + q'ₙ₋₁
        ≡⟨ cong (λ x →  a₀ * (aₙ * p'ₙ₋₂ + p'ₙ₋₃) + x) IHdens ⟩
      a₀ * (aₙ * p'ₙ₋₂ + p'ₙ₋₃) + (aₙ * q'ₙ₋₂ + q'ₙ₋₃)
      ≡⟨ cong (λ x → x + (aₙ * q'ₙ₋₂ + q'ₙ₋₃)) (*+dist (a₀) (aₙ * p'ₙ₋₂) (p'ₙ₋₃)) ⟩
      a₀ * (aₙ * p'ₙ₋₂) + a₀ * p'ₙ₋₃ + (aₙ * q'ₙ₋₂ + q'ₙ₋₃)
      ≡⟨ cong (λ x → x + a₀ * p'ₙ₋₃ + (aₙ * q'ₙ₋₂ + q'ₙ₋₃)) (*assoc (a₀) (aₙ) (p'ₙ₋₂)) ⟩
      a₀ * aₙ * p'ₙ₋₂ + a₀ * p'ₙ₋₃ + (aₙ * q'ₙ₋₂ + q'ₙ₋₃)
      ≡⟨ cong (λ xs → xs * p'ₙ₋₂ + a₀ * p'ₙ₋₃ + (aₙ * q'ₙ₋₂ + q'ₙ₋₃) ) (*comm (a₀) (aₙ)) ⟩
      aₙ *  a₀ * p'ₙ₋₂ + a₀ * p'ₙ₋₃ + (aₙ * q'ₙ₋₂ + q'ₙ₋₃)
      ≡⟨ +assoc (aₙ *  a₀ * p'ₙ₋₂ + a₀ * p'ₙ₋₃) (aₙ * q'ₙ₋₂) (q'ₙ₋₃) ⟩
      aₙ *  a₀ * p'ₙ₋₂ + a₀ * p'ₙ₋₃ + aₙ * q'ₙ₋₂ + q'ₙ₋₃
       ≡⟨ cong (λ x → x + q'ₙ₋₃) (+assoc' (aₙ *  a₀ * p'ₙ₋₂) (a₀ * p'ₙ₋₃) (aₙ * q'ₙ₋₂))  ⟩
      aₙ *  a₀ * p'ₙ₋₂ + (a₀ * p'ₙ₋₃ + aₙ * q'ₙ₋₂) + q'ₙ₋₃
      ≡⟨ cong (λ x → aₙ *  a₀ * p'ₙ₋₂ + x + q'ₙ₋₃) (+comm ( a₀ * p'ₙ₋₃)  (aₙ * q'ₙ₋₂)) ⟩
      aₙ *  a₀ * p'ₙ₋₂ + (aₙ * q'ₙ₋₂ + a₀ * p'ₙ₋₃) + q'ₙ₋₃
       ≡⟨ cong (λ x → x + q'ₙ₋₃)  (+assoc ( aₙ *  a₀ * p'ₙ₋₂) (aₙ * q'ₙ₋₂) (a₀ * p'ₙ₋₃)) ⟩
      aₙ *  a₀ * p'ₙ₋₂ + aₙ * q'ₙ₋₂ + a₀ * p'ₙ₋₃ + q'ₙ₋₃
       ≡⟨ +assoc' (aₙ *  a₀ * p'ₙ₋₂ + aₙ * q'ₙ₋₂) (a₀ * p'ₙ₋₃) (q'ₙ₋₃) ⟩
      aₙ *  a₀ * p'ₙ₋₂ + aₙ * q'ₙ₋₂ + (a₀ * p'ₙ₋₃ + q'ₙ₋₃)
        ≡⟨ cong (λ x →  x +  aₙ * q'ₙ₋₂ + (a₀ * p'ₙ₋₃ + q'ₙ₋₃)) (sym (*assoc aₙ a₀ p'ₙ₋₂)) ⟩
      aₙ *  (a₀ * p'ₙ₋₂) + aₙ * q'ₙ₋₂ + (a₀ * p'ₙ₋₃ + q'ₙ₋₃)
        ≡⟨ cong (_+ (a₀ * p'ₙ₋₃ + q'ₙ₋₃)) (sym (*+dist  aₙ (a₀ * p'ₙ₋₂) q'ₙ₋₂))⟩
      aₙ * ((a₀ * p'ₙ₋₂) + q'ₙ₋₂) + (a₀ * p'ₙ₋₃ + q'ₙ₋₃)
        ≡⟨ refl {- Def. nums -}⟩
      aₙ * pₙ₋₁ + pₙ₋₂
        ∎

  densRec : ∀ cf n →
            dens cf (succ (succ n)) ≡ cf (succ (succ n)) * dens cf (succ n) + dens cf n
  densRec cf zero = 
    let
      a₁ = cf 1
      a₂ = cf 2
    in
      a₁ * a₂ + 1
        ≡⟨ cong (λ x → x + 1) (*comm a₁ a₂) ⟩
      a₂ * a₁ + 1
        ∎ 
  densRec cf (succ m) = 
    let
      aₙ = cf (succ (succ (succ m)))
      qₙ = dens cf (succ (succ (succ m)))
      qₙ₋₁ = dens cf (succ (succ m))
      qₙ₋₂ = dens cf (succ m)
      p'ₙ₋₁ = nums (cf ∘ succ) (succ (succ m))
      p'ₙ₋₂ = nums (cf ∘ succ) (succ m)
      p'ₙ₋₃ = nums (cf ∘ succ) m
      {- note that
        pₙ ≡ a₀ * p'ₙ₋₁ + q'ₙ₋₁
        qₙ ≡ p'ₙ₋₁
        and similarly for n-1 and n-2
        hold by definition of nums and dens and thus
        can be proved by refl !!
      -}
      IHnums : p'ₙ₋₁ ≡ aₙ * p'ₙ₋₂ + p'ₙ₋₃
      IHnums = numsRec (cf ∘ succ) m
    in
      qₙ
        ≡⟨ refl {- Def. dens -}⟩
      p'ₙ₋₁
        ≡⟨ IHnums ⟩
      aₙ * p'ₙ₋₂ + p'ₙ₋₃
        ≡⟨ refl {- Def. dens -}⟩
      aₙ * qₙ₋₁ + qₙ₋₂
        ∎
