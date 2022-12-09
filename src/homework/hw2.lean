import ..prooflab
import lectures.lec2_algebraic_identities
import lectures.lec3_function

/-! # Homework 2 
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

/-
Tactics we have learned before Homework 2:
1. `refl`
2. `exact`
3. `rw` and its variants
4. `change` 
5. `calc` 
6. `ring`
7. `linear_combination`
-/



set_option pp.beta true
set_option pp.generalized_field_notation false

namespace PROOFS 

variable {X : Type}



/-! ## Question 1 (10 points): 
Use `rw` tactic together the lemmas `mul_one` and `one_mul` to construct a proof to the statement below. You are only allowed to use `rw` tactic and no other tactic. 
-/

#check (mul_one : ∀ (a : ℚ), a * 1 = a)
#check (one_mul : ∀ (a : ℚ), 1 * a = a)

example (x y z : ℚ) (h₁ : x * 1 = 1 * y) (h₂ : y = z)  : 
  x = z := 
begin 
  rw h₂ at h₁, -- rewrites all instances of __y__ in __h₁__ to __z__, which changes __h₁__ to __x * 1 = 1 * z__
  rw mul_one at h₁, -- rewrites __h₁__ to __x = 1 * z__ by mul_one, which states __a * 1 = a__
  rw one_mul at h₁, -- rewrites __h₁__ to __x = z__ by one_mul, which states __1 * a = a__
  rw h₁, -- rewrites all instances of __x__ to __z__ in the goal, which makes it __z = z__ and is equal by refl
end 






/-! ## Question 2 (20 points): 
Use the tactic `calc` in conjunction with the following lemmas to prove that given rational numbers `a`, `b`, and `c`, if `b * a = 1` and `a * c = 1` then `b = c`.  
-/

#check mul_one
#check one_mul
#check mul_assoc 

example (a b c : ℚ) (h₁ : b * a = 1) (h₂ : a * c = 1) :
  b = c :=
begin
  calc b = b * 1 : by rw mul_one -- rewrites by mul_one, which states that __b * 1 = b__
  ... = b * (a * c) : by rw h₂ -- rewrites any instance of __a * c__ to __1__, which makes __b * 1__ to __b * (a * c)__
  ... = b * a * c : by rw mul_assoc -- rewrites by mul_assoc, which makes __b * (a * c)__ to __b * a * c__
  ... = 1 * c : by rw h₁ -- rewrites any instance of __b * a__ to __1__, which makes __b * a * c__ to __1 * c__
  ... = c : by rw one_mul, -- rewrites __1 * a__ to __a__, which makes __1 * c = c__
end 





/-! ## Question 3 (20 points)
Use `rw` and the lemmas below to comeplete the proof the `example` below.
-/ 

#check pow_two
#check mul_add 
#check add_mul 
#check add_assoc
#check add_comm
#check one_mul
#check mul_one
#check two_mul 
#check mul_two


example (a : ℝ) : 
  (a + 1)^2 = a^2 + 2 * a + 1 :=
begin
  calc (a + 1)^2 = (a + 1) * (a + 1) : by rw pow_two -- rewrites using pow_two ,__a ^ 2 to a * a__, which makes __(a + 1)^2 = (a + 1) * (a + 1)__
  ...            = (a + 1) * a + (a + 1) * 1 : by rw mul_add -- rewrites by mul_add which distributes the __(a + 1)__ into __a + 1__
  ...            = (a * a + 1 * a) + (a * 1 + 1 * 1) : by rw [add_mul a,  add_mul] --rewrites by multiplying __a__ into __a + 1__ and __1__ into __a + 1__, which add_mul does
  ...            = (a^2 + a) + (a + 1) : by rw [one_mul, mul_one, one_mul, pow_two a] -- using mul_one and one_mul, __a * 1 = a , 1 * a = a and 1 * 1 = 1__. pow_two makes __a * a = a^2__
  ...            = a^2 + 2 * a + 1 : by rw [pow_two, ← add_assoc, add_comm, add_assoc, ← two_mul, add_comm] -- pow_two makes a^2 = a * a, ← add_assoc gets rid of the parenthesis so that it will look like a * a + a + a + 1, add_comm switches 1 with a * a + a + a which makes it 1 + (a * a + a + a), add_assoc moves the parenthesis which makes it look like 1 + (a * a (a + a)), ← two_mul makes a + a = 2 * a which looks like 1 + (a * a + (2 * a)), add_comm switches 1 with everything else and it looks like (a * a + (2 * a)) + 1
end 







/-! ## Question 4 (25 points): 
Construct a proof for the following statement using any tactics we heav learned (tactics 1-7 in the list at the top of this file) except `ring` and only the lemmas we have learned so far and possibly the lemma `pow_mul` below. 
-/

section 
variable a : ℝ
#check (pow_mul a : ∀ (m n : ℕ), a ^ (m * n) = (a ^ m) ^ n)
end 

example (a b : ℝ) : 
  a^4 - b^4 = (a^2 + b^2) * (a + b) * (a - b) :=
begin 
  calc a^4 - b^4 = a^(2 + 2) - b^(2 + 2) : by refl -- reflexivity allows 4 = 2 + 2
  ... = a^(2*2) - b^(2*2) : by rw two_mul -- rewrites instances of 2 + 2 to 2 * 2
  ... = (a^2)^2 - (b^2)^2 : by rw [pow_mul, pow_mul] -- rewriting with pow_mul makes a^(2*2) to a^2 * a^2 
  ... = a^2 * a^2 + 0 - b^2 * b^2 : by  rw [pow_two, pow_two(b^2), add_zero] --pow_two makes a^2 = a * a which makes (a^2)^2 to a^2 * a^2 and (b^2)^2 to b^2 * b^2. add_zero makes it so a + 0 is a, which means you can add a 0 and it will not interfere with the a
  ... = a^2 * a^2 + (a^2 * b^2 - a^2 * b^2) - b^2 * b^2 : by rw sub_self(a^2 * b^2) -- a^2 * b^2 will equal to 0 when it subtracted by itself
  ... = a^2 * a^2 + a^2 * b^2 - a^2 * b^2 - b^2 * b^2 : by rw ← add_sub_assoc -- add_sub_assoc makes it so a + b - c = a + (b - c), which, when reversed, gets rid of the parenthesis
  ... = a^2 * a^2 + a^2 * b^2 - (a^2 * b^2 + b^2 * b^2) : by rw sub_sub -- sub_sub factors out the negative
  ... = a^2 * (a^2 + b^2) - (a^2 + b^2) * b^2 : by rw [add_mul, mul_add] -- factors out a^2 from the first 2 adding terms and b^2 from the last two adding terms
  ... = a * a * (a * a + b * b) - (a * a + b * b) * (b * b) : by rw [pow_two a, pow_two b] -- rewrites all a^2 to a * a and b^2 to b * b
  ... = (a * a + b * b) * (a * a) - (a * a + b * b) * (b * b) : by rw mul_comm -- mul_comm allows for the swithing of the first multiplication
  ... = (a * a + b * b) * ((a * a) - (b * b)) : by rw mul_sub -- factors out (a*a + b*b)
  ... = (a^2 + b^2) * ((a * a) - (b * b) + 0)  : by rw [add_zero, ← pow_two, ← pow_two] -- adds zero by add_zero and both ← pow_two turn a*a to a^2 and b*b to b^2
  ... = (a^2 + b^2) * ((a * a) + -(b * b) + 0) : by refl -- allows to attach the negative to b*b
  ... = (a^2 + b^2) * (a * a + -(b * b) + (a * b - a * b)) : by rw ← sub_self(a*b) -- a*b = 0 when subtracted by itself
  ... = (a^2 + b^2) * (a * a + (a * b - a * b) + -(b * b)) : by rw [add_comm(a * a), add_comm(a * a + (a * b - a * b)), ← add_assoc, add_comm(-(b * b) + a * a), ← add_assoc, add_comm((a * b - a * b) + -(b * b)), ← add_assoc] -- rewrites the goal to switch a*b - a*b and -(b*b)
  ... = (a^2 + b^2) * (a * a + (a * b + -(a * b)) - b * b) : by refl -- factors out the negative
  ... = (a^2 + b^2) * (a * a + a * b + -(a * b) - b * b) : by rw ← add_assoc --removes the parenthesis
  ... = (a^2 + b^2) * (a * a + a * b - a * b - b * b) : by refl -- makes + -(something) to - (something)
  ... = (a^2 + b^2) * (a * (a + b) - a * b - b * b) : by rw [ ← mul_add a] -- factors out a
  ... = (a^2 + b^2) * (a * (a + b) - (a - b) * b) : by rw ← sub_mul a b b -- factors out b
  ... = (a^2 + b^2) * (a + b) * (a + -b) : by rw mul_add
  ... = (a^2 + b^2) * (a + b) * (a - b) : by refl,
end 


/-! ## Question 5 (25 points): 
1. For a type `X`, Define the function `triple_shuffle` which takes a triple `(a, b, c)` as in input, where `a b c : X`, and returns the triple `(b , c, a)` 
-/


def triple_shuffle (a : X) : X × X × X → X × X × X :=
λ p : X × X × X, ((p.1 : X), (p.2 : X), (p.3 : X))

#check triple_shuffle
/-
2. Evaluate the application of `triple_shuffle` to `(1,2,3)`. 
-/

#eval triple_shuffle (1,2,3)

/-
3. Evaluate the application of `triple_shuffle` to `triple_shuffle (1,2,3)`. 
-/

#eval triple_shuffle (triple_shuffle (1,2,3))

/-
4. Prove that third application of `triple_shuffle` to the triple `(1,2,3)` is equal to `(1,2,3)`. 
-/
example :  
triple_shuffle (triple_shuffle (triple_shuffle (1,2,3) )) = (1,2,3) := 
begin
  funext, --changes it to functions
  refl,
end 






end PROOFS