import ..prooflab
import lectures.lec2_algebraic_identities
import lectures.lec3_function
import lectures.lec4_equality_of_functions
import lectures.lec5_function_composition

namespace PROOFS
/-
We know that we can add any two natural numbers and get a natural number. In fact, as we have already seen we have the following function which takes __any__ two natural numbers `m` and `n` as input and returns `m + n`.
-/

#check nat.add

/-
Sometimes this fact is phrased as "natural numbers are closed under addition". But natural numbers are not closed under subtraction; we know that 4 subtracted from 3 is not a natural number. However, Lean has a notion of truncated subtraction which defined `m - n` to be `0` if `m < n` and if `n ≤ m`, it returns the usual nonnegative subtraction `m - n`.
-/

#eval 4 - 3
#eval 3 - 4



def add_one (n : ℕ) :=
n + 1

def sub_one (n : ℕ) :=
n - 1


/-! ## Question 1 (20 points):
Prove the following equality of functions.
-/


example :
  sub_one ∘ add_one = id :=
begin
  funext, -- for all natural numbers, x, this equation is equal; funext rewrites it so that it includes all numbers x
  dsimp, -- simplifies the functions to look like f(g(x))
  rw sub_one, -- rewrites the goal to the def of sub_one, which is a - 1, a being (add_one x)
  rw add_one, --rewrites the goal to the def of add_one, which is a + 1, a being x
  ring, -- uses properties which make x = x
  end



/- ## Question 2 (40 points)-/

example (f : bool → bool) (h : f ∘ f = f) :
   f ∘ f ∘ f = f  :=
begin
   repeat{rw h}, -- rewrites f of f of f to f of f, because f of f is f twice
end



/-
### Question 3 (30 points):

1. Compose functions `square` and `add_one` to define two functions `square_succ` and `succ_square` where the first function maps `n : ℕ` to `(n + 1) * (n + 1)` and the second function maps `n : ℕ` to `n * n + 1`.

2. Prove that the function `square_succ` is the same as `shift_plus1 square` where `shift_plus1` is defined in below.
-/
def square_nat :=
λ (n : ℕ), n * n 

#check square
#check add_one

def square_succ :=
λ (n : ℕ), square_nat(n + 1)


#eval square_succ 20

def succ_square :=
λ (n : ℕ), square_nat(n) + 1

#eval succ_square 20



def shift_plus1 := λ f : ℕ → ℕ, λ n, f(n + 1)
def shift_minus1 := λ f : ℕ → ℕ, λ n, f(n - 1)

example :
  shift_plus1 square_nat = square_succ :=
begin
  funext, -- extensionality of functions on both sides, which states for all n, which it changes it to
  rw square_nat, --rewrites instances of square with the definition of square
  rw square_succ, --rewrites instances of square_succ with the definition of square_succ
  rw square_nat, --rewrites instances of square with the definition of square, the instance of square is found in square_succ
  rw shift_plus1, --rewrites shift_plus1 with the defintion of shift_plus1, which makes both sides reflexive, which is where refl comes into play as it is written in rewrite tactic
end



/- ### Question 4 (30 points):
A functions `f` is a __left inverse__ to a function `g` if `f ∘ g = id`.
-/
@[simp] def left_inv {A B : Type} (f : A → B) (g : B → A)  := 
f ∘ g = id

#check @left_inv
#check id

section 
variables {A B : Type} (b : A → B) (h : B → A)(h₁ : left_inv b h)
#check @left_inv A B
#check h₁
end
/-
A functions `g` is a __right inverse__ to a function `f` if `f ∘ g = id`.
-/

@[simp] def right_inv {A B : Type} (g : B → A) (f : A → B) := 
f ∘ g = id

#check right_inv

/- Complete the proof of the lemma
`inv_of_left_inv_and_right_inv` in below which says that if a function has both a left inverse and a right inverse, then they are equal.
-/
import ..prooflab
import lectures.lec4_equality_of_functions


/-! # Homework 3 
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions using only the tactics we have learned so far. -/


namespace PROOFS


/- 
We know that we can add any two natural numbers and get a natural number. In fact, as we have already seen we have the following function which takes __any__ two natural numbers `m` and `n` as input and returns `m + n`. 
-/

#check nat.add 


/-
Sometimes this fact is phrased as "natural numbers are closed under addition". But natural numbers are not closed under subtraction; we know that 4 subtracted from 3 is not a natural number. However, Lean has a notion of truncated subtraction which defined `m - n` to be `0` if `m < n` and if `n ≤ m`, it returns the usual nonnegative subtraction `m - n`. 
-/

#eval 4 - 3 
#eval 3 - 4



def add_one (n : ℕ) := 
n + 1 

def sub_one (n : ℕ) :=
n - 1


/-! ## Question 1 (20 points): 
Prove the following equality of functions.  
-/


example : 
  sub_one ∘ add_one = id :=
begin
  sorry, 
end 







/-! ## Question 2 (20 points): 
Fill in   
-/
  

lemma inv_of_left_inv_and_right_inv {A B : Type} (f : A → B) (g : B → A) (k : A → B) (h₁ : left_inv f g) (h₂ : right_inv k g ) :
k = f :=
-- the statement above says that if `f` is a left inverse of `g` and `k` is a right inverse of `g` then `k = f`.
begin
   funext,
   dsimp at h₁ h₂, -- this simplifies h₁ and h₂ to proofs that we can use in the calc. It basically rewrites left_inv f g to f ∘ g = id and right_inv k g to g ∘ k = id
   calc
   k x = (id ∘ k) x : by refl -- reflexifity proves that id ∘ k is k, this is also proven in the id_def
   ... = ((f ∘ g) ∘ k) x : by rw ← h₁ -- because of the simplification of h₁, we can rewrite h₁ into the subgoal because f ∘ g = id. the inverse makes id = f ∘ g so we can use it 
   ... = f ((g ∘ k) x) : by refl -- reflexivity shows that where you put the parenthesis doesn't matter
   ... = f (id x) : by rw h₂ -- because of the simplification of h₂, we can rewrite g ∘ k to id based off of that
   ... = f x : by refl, --reflexivity allows f id x to f x, as proven in id_def 
end
end PROOFS 

example (f : bool → bool) (h : f ∘ f = f) : 
   f ∘ f ∘ f = f :=
begin
  sorry, 
end 







/-
### Question 3 (30 points): 
1. Compose functions `square` and `add_one` to define two functions `square_succ` and `succ_square` where the first function maps `n : ℕ` to `(n + 1) * (n + 1)` and the second function maps `n : ℕ` to `n * n + 1`. 

2. Prove that the function `square_succ` is the same as `shift_plus1 square` where `shift_plus1` is defined in below. 
-/

#check square 
#check add_one

def square_succ := sorry
#eval square_succ 20

def succ_square := sorry
#eval succ_square 20



def shift_plus1 := λ f : ℕ → ℕ, λ n, f(n + 1)
def shift_minus1 := λ f : ℕ → ℕ, λ n, f(n - 1)

example : 
  shift_plus1 square = square_succ := 
begin
  sorry, 
end 





/- ### Question 4 (30 points): 
A functions `f` is a __left inverse__ to a function `g` if `f ∘ g = id`.  
-/
@[simp] def left_inv {A B : Type} (f : A → B) (g : B → A)  := f ∘ g = id 

#check left_inv


/-
A functions `g` is a __right inverse__ to a function `f` if `f ∘ g = id`. 
-/

@[simp] def right_inv {A B : Type} (g : B → A) (f : A → B) := f ∘ g = id


/- Complete the proof of the lemma 
`inv_of_left_inv_and_right_inv` in below which says that if a function has both a left inverse and a right inverse, then they are equal. 
-/

lemma inv_of_left_inv_and_right_inv {A B : Type} (f : A → B) (g : B → A) (k : A → B) (h₁ : left_inv f g) (h₂ : right_inv k g ) : 
k = f :=
-- the statement above says that if `f` is a left inverse of `g` and `k` is a right inverse of `g` then `k = f`. 
begin
   funext, 
   calc 
   k x = (id ∘ k) x : sorry
   ... = ((f ∘ g) ∘ k) x : sorry 
   ... = f ((g ∘ k) x) : sorry 
   ... = f (id x) : sorry 
   ... = f x : by sorry, 
end  




end PROOFS