import ..prooflab
import lectures.lec6_proposition
import data.real.basic
import data.complex.exponential


/-! # Homework 4: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far.

Pro Tip: Don't forget you know the tactics `linarith` and `ring`!
 -/

namespace PROOFS

variables {P Q R : Prop}

/-! ## Question 1 (20 points):
Give a proof of the proposition `(P ∧ R) → (R → P → Q) → Q`.
-/

example :
  (P ∧ R) → (R → P → Q) → Q :=
begin
  intro hpr, --introduction rule of implication is used to make P ∧ R an assumption
  intro hrpq, --introduction rule of implication is used to make R → P → Q an assumption
  cases hpr with h₁ h₂, --elimination rule of conjugation that make P and R proves from hpr
  have h₃: P → Q, from hrpq h₂, -- assume that P → Q is true by using the assumption hrpq and h₂, which says that because h₂ proves R to be true, R → P → Q will prove P → Q
  exact h₃ h₁, -- assumes that the new goal Q is true by using the assumption h₃ and h₁ which says that P → Q is Q because it is proven by P/h₁
end






/-! ## Question 2 (20 points):
Prove the implication
`m * n - m - n + 1 = 1 → (m = 2) ∧ (n = 2)`
for natural numbers `m` and `n` by filling in `sorry` placeholders below.

You need to use the lemma `mul_eq_one_of_pos_of_pos` in below which says if the multiplication of two positive integers is `1` then both of them must be `1`. Notice that we did not provide the proof of this lemma here, and __you don't need to provide it either__. We will construct a proof of this lemma in the next lecture.
-/

-- no need to solve the following, just use it in the next proof
lemma mul_eq_one_of_pos_of_pos  (m n : ℤ) (h : m * n = 1) :
  (0 < m ∧ 0 < n) → (m = 1 ∧ n = 1) :=
begin
  sorry,
end

-- give a proof of this one using the lemma above.
example (m n : ℤ) :
  m * n - m - n + 1 = 1 → (1 < m ∧ 1 < n) → (m = 2) ∧ (n = 2) :=
begin
  intro h₁, --introduction rule of implication to make m * n - m - n + 1 = 1 an assumption and the new goal to (1 < m ∧ 1 < n) → (m = 2) ∧ (n = 2)
  have h₂ : (m - 1) * (n - 1) = 1, by linarith, --using linarith, we can make h₂ an assumption to prove that (m - 1) * (n - 1) = 1
  intro h₃, --introduction rule of implication to make (1 < m ∧ 1 < n) and assumption and the new goal (m = 2) ∧ (n = 2)
  cases h₃ with h₄ h₅, --introduction rule of conjugation splits h₃ to 2 new assumptions 1 < m and 1 < n
  have h₆ , from mul_eq_one_of_pos_of_pos (m-1) (n-1) h₂, -- can imply h₆ by using the lemma mul_eq_one_of_pos_of_pos (m-1)(n-1) h₂, which we had made h₂ an assumption earlier. This gives us the right side of the lemma mul_eq_one_of_pos_of_pos which we can use later to prove that m-1 = 1 and n-1 = 1
  have h₇: 0 <  m - 1, by linarith, --can prove 0 < m - 1 from assumptions present using linarith
  have h₈: 0 < n - 1, by linarith, -- same as line before except 0 < n - 1
  have hp: 0 < m - 1 ∧ 0 < n - 1, by {split, { assumption}, {assumption},}, -- we can prove hp by proving that the left is true by h₇ and the right is true by h₈. The split tactic of elimination of conjugation is used to split the goals of hp so we can prove that each side is true.
  have h₉: m - 1 = 1 ∧ n - 1 = 1, from h₆ hp, -- the left side of h₆ is proven by hp, which proves h₉ to be true
  cases h₉, -- introduction rule of conjugation splits the goals of h₉ into assumptions that we use later
  split, -- elimination rule of conjugation splits the goal to m = 2 and n = 2
  {
    linarith, -- proves m = 2 with definitions and assumptions
  },
  {
    linarith, -- proves n = 2 with definitions and assumptions
  },
end






/-! ## Question 3 (20 points):
Construct a proof of the proposition `abs (2 * x - 1) < 5 → -2 < x `. You are allowed to use the lemma `abs_lt`.
-/

section
variables a b : ℝ
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)

end
example (x y : ℝ) : abs (2 * x - 1) < 5 → -2 < x :=
begin
  intro h₁, --introduction rule of implication will make abs (2 * x - 1) < 5 and assumption and make -2 < x the new goal
  rw abs_lt at h₁, -- rewrites the abs(2 * x - 1) to -5 < 2 * x - 1 ∧ 2 * x - 1 < 5, the def of absolute value, by abs_lt at h₁
  cases h₁ with h₂ h₃, -- elimination rule of conjugation will separate h₁ to both sides of the conjugation h₂ and h₃
  linarith, -- like ring, will use assumptions and other defenitions to prove the goal
end






/-! ## Question 4 (20 points):
For `x : ℝ`, the term `real.exp x` encodes the exponential e^x.
-/

section
variables a b c : ℝ
#check (real.exp_le_exp.mpr : a ≤ b → real.exp a ≤ real.exp b)
end

example (a b c : ℝ) (h : 1 ≤ a ∧ b ≤ c) :
  2 + a + real.exp b ≤ 3 * a + real.exp c :=
begin
  cases h with h₁ h₂, -- we can split h into 2 assumptions using the intro rule of conjugation "cases", which h₁ = 1 ≤ a and h₂ = b ≤ c
  have h₃, from real.exp_le_exp.mpr h₂, -- using real.exp_le_exp.mpr to h₂, we can prove real.exp b ≤ real.exp c
  have h₄: 2 + a ≤ 3 * a, by linarith, -- so far, we are trying to make an assumption as close to the goal as possible. we need to prove the other parts of the goal in order to then add them to the assumption which we can then prove the goal. linarith proves the other parts of the goal 2 + a ≤ 3 * a
  have h₅, from add_le_add h₄ h₃, -- using add_le_add h₄ h₃, we can prove 2 + a + real.exp b ≤ 3 * a + real.exp c because h₃ is real.exp b ≤ real.exp c and h₄ is 2 + a ≤ 3 * a, which add_le_add proves that we can merge the two together to get the goal, which is 2 + a + real.exp b ≤ 3 * a + real.exp c
  assumption, -- proves the goal by h₅
end






/-! ## Question 5 (20 points):
Prove the following statement. You might like to use  lemmas `abs_mul` and/or `abs_lt`.
- `abs_mul`
- `abs_lt`.
- `abs_nonneg`
- `abs_pos`
- `real_le_of_mul_nonneg_left`
- `real_lt_of_mul_pos_right`
- `real_le_mul_right`
-/

section
variables a b : ℝ
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
#check abs_nonneg
#check abs_pos 
end

lemma real_le_of_mul_nonneg_left {a b c : ℝ} (h₀ : a < b) (h₁ : 0 ≤ c):
  c * a ≤ c * b :=
begin
  apply mul_le_mul_of_nonneg_left,
  {
    apply le_of_lt,
    apply h₀,
  },
  {
     apply h₁,
  },
end


lemma real_lt_of_mul_pos_right {a b c : ℝ} (h₀ : a < b) (h₁ : 0 < c):
  a * c < b * c :=
begin
  rw mul_comm a c,
  rw mul_comm b c,
  apply mul_lt_mul_of_pos_left,
  assumption',
end


lemma real_le_mul_right {a b c : ℝ} (h₀ : a ≤ b) (h₁ : 0 < c):
  a * c ≤ b * c :=
begin
  apply (mul_le_mul_right h₁).mpr,
  assumption,
end

#check abs_nonneg

/-
- `abs_mul`
- `abs_lt`.
- `abs_nonneg`
- `abs_pos`
- `real_le_of_mul_nonneg_left`
- `real_lt_of_mul_pos_right`
- `real_le_mul_right`
-/
import ..prooflab
import lectures.lec6_proposition
import data.real.basic
import data.complex.exponential


/-! # Homework 4: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far. 

Pro Tip: Don't forget you know the tactics `linarith` and `ring`! 
 -/





namespace PROOFS


variables {P Q R : Prop}



/-! ## Question 1 (20 points): 
Give a proof of the proposition `(P ∧ R) → (R → P → Q) → Q`. 
-/

example : 
  (P ∧ R) → (R → P → Q) → Q :=
begin
  sorry, 
end 






/-! ## Question 2 (20 points): 
Prove the implication 
`m * n - m - n + 1 = 1 → (m = 2) ∧ (n = 2)` 
for natural numbers `m` and `n` by filling in `sorry` placeholders below. 

You need to use the lemma `mul_eq_one_of_pos_of_pos` in below which says if the multiplication of two positive integers is `1` then both of them must be `1`. Notice that we did not provide the proof of this lemma here, and __you don't need to provide it either__. We will construct a proof of this lemma in the next lecture. 
-/

-- no need to solve the following, just use it in the next proof 
lemma mul_eq_one_of_pos_of_pos  (m n : ℤ) (h : m * n = 1) : 
  (0 < m ∧ 0 < n) → (m = 1 ∧ n = 1) := 
begin 
  sorry, 
end 

-- give a proof of this one using the lemma above. 
example (m n : ℤ) : 
  m * n - m - n + 1 = 1 → (1 < m ∧ 1 < n) → (m = 2) ∧ (n = 2) := 
begin
  sorry, 
end  

 




/-! ## Question 3 (20 points): 
Construct a proof of the proposition `abs (2 * x - 1) < 5 → -2 < x `. You are allowed to use the lemma `abs_lt`.  
-/

section 
variables a b : ℝ 
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)

end 
example (x y : ℝ) : abs (2 * x - 1) < 5 → -2 < x := 
begin
  sorry, 
end



/-! ## Question 4 (20 points): 
For `x : ℝ`, the term `real.exp x` encodes the exponential e^x. 
-/

section 
variables a b c : ℝ
#check (real.exp_le_exp.mpr : a ≤ b → real.exp a ≤ real.exp b)
end 


example (a b c : ℝ) (h : 1 ≤ a ∧ b ≤ c) :
  2 + a + real.exp b ≤ 3 * a + real.exp c :=
begin
  sorry, 
end 






/-! ## Question 5 (20 points): 
Prove the following statement. You might like to use any of the following lemmas (most likely you need only some of them not all.): 
- `abs_mul` 
- `abs_lt`.
- `abs_nonneg`
- `abs_pos`
- `real_le_of_mul_nonneg_left`
- `real_lt_of_mul_pos_right`
- `real_le_mul_right`
-/

section 
variables a b : ℝ
#check (abs_mul a b : |a * b| = |a| * |b|)
#check (abs_lt : |a| < b ↔ -b < a ∧ a < b)
end 


lemma real_le_of_mul_nonneg_left {a b c : ℝ} (h₀ : a < b) (h₁ : 0 ≤ c): 
  c * a ≤ c * b := 
begin
  apply mul_le_mul_of_nonneg_left, 
  {
    apply le_of_lt,
    apply h₀, 
  },
  {
     apply h₁, 
  },
end   


lemma real_lt_of_mul_pos_right {a b c : ℝ} (h₀ : a < b) (h₁ : 0 < c): 
  a * c < b * c := 
begin
  rw mul_comm a c,
  rw mul_comm b c, 
  apply mul_lt_mul_of_pos_left, 
  assumption',
end 


lemma real_le_mul_right {a b c : ℝ} (h₀ : a ≤ b) (h₁ : 0 < c): 
  a * c ≤ b * c := 
begin
  apply (mul_le_mul_right h₁).mpr,
  assumption,  
end 

#check abs_nonneg
 

example (x y ε : ℝ) :
(0 < ε ∧ ε ≤ 1) → (abs x < ε ∧ abs y < ε) → abs (x * y) < ε :=
begin
intros h₁ h₂,
rw abs_mul,
cases h₁,
cases h₂,
have h₃ : |x| < 1, by linarith,
have h₄ : |x| * ε < 1 * ε, from real_lt_of_mul_pos_right h₃ h₁_left,
have h₅, from abs_nonneg x,
have h₆ : |x| * |y| ≤ |x| * ε, from real_le_of_mul_nonneg_left h₂_right h₅,
linarith,
end 
end PROOFS




example (x y ε : ℝ) : 
  (0 < ε ∧ ε ≤ 1) → (abs x < ε ∧ abs y < ε) → abs (x * y) < ε :=
begin
  sorry,  
end   




end PROOFS