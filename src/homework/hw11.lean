/-
Homeowork 11
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec14_inductive_naturals
import homework.hw10


open PROOFS
open PROOFS.STR



/-
Note that the code below is not wrapped by the namespace `mat`, so if you want to use a definition or lemma/theorem named `xyz` from lec14 you need to append `mat` to its name and use it as `mat.xyz`.
-/



/-! ## Question 1 (20 pts) :
Prove the following results using `cases` or `induction`.
-/


lemma mat.zero_of_add_eq_zero (m n : mat) :
  m + n = 0  → (m = 0) ∧ (n = 0) :=
begin
 intro h, -- intro rule of implication
 split, -- intro rule of conjugation
 {
  
  induction m with m ihm, 
  { -- proving base case `P 0`
    refl,
  },
  { -- the inductive step: assuming `P n` and proving `P succ(n)`
    simp at *, -- simplifies h with mat.add_succ
    tauto
  },
 },
 {
  induction n with n ihn,
  { -- proving base case `P 0`
    refl,
  },
  { -- the inductive step: assuming `P n` and proving `P succ(n)`
    simp at *, -- simplifies h with mat.add_succ
    tauto,
  },
 },
end


lemma mat.zero_of_mul_eq_zero (m n : mat) :
  m * n = 0  → (m = 0) ∨ (n = 0) :=
begin
  intro h, -- intro rule of implication
  cases m, -- like induction
  { -- proving base case `P 0`
    left, -- we want to prove `mat.zero = 0 ∨ n = 0`, use intro rule of disjunction to prove the left side with reflexivity becuase mat.zero is 0
    refl,
  },
  { -- the inductive step: assuming `P n` and proving `P succ(n)`
    right, -- we want to prove `m.succ = 0 ∨ n = 0`, use intro rule of disjunction to prove the right side
    cases n, -- like induction
    { -- proving base case `P 0`
      refl,
    },  
    { -- the inductive step: assuming `P n` and proving `P succ(n)`
      tauto,
    },
  },
end



/-! ## Question 2 (20 pts) :
Prove the following distributivity result and then use them to prove lemma `mat.two_mul` (a proof of `mat.two_mul` which does not use distributivity lemmas is also accepted).
-/

lemma mat.mul_add_distrib (k m n : mat) :
  k * (m + n) = k * m + k * n :=
begin
  induction m with m ihm,
  { -- proving base case `P 0`
    have h: mat.zero = 0, by refl, -- we want to replace mat.zero with 0 so we can use lemmas
    rw h, -- makes the goal `k * (0 + n) = k * 0 + k * n`
    rw mat.mul_zero, -- makes the goal `k * (0 + n) = 0 + k * n` because mat.mul_zero : ∀ (m : mat), m * 0 = 0
    repeat{ rw mat.zero_add,}, -- solves the goal with reflexivity after using the lemma mat.zero_add : ∀ (m : mat), 0 + m = m
  },
  { -- the inductive step: assuming `P n` and proving `P succ(n)`
    rw mat.succ_add, -- we want to prove `k * (m.succ + n) = k * m.succ + k * n`, we can use mat.succ_add, which makes the goal `k * (m + n).succ = k * m.succ + k * n`
    rw mat.mul_succ, -- rewrite mat.mul_succ makes the goal `k * (m + n) + k = k * m.succ + k * n`
    rw ihm, -- rewriting using the inductive hypothesis. the goal is now `k * m + k * n + k = k * m.succ + k * n`
    rw mat.mul_succ, -- rewrite mat.mul_succ makes the goal `k * m + k * n + k = k * m + k + k * n`
    rw mat.add_assoc, -- rewrite mat.add_assoc makes the goal `k * m + (k * n + k) = k * m + k + k * n` so that we can rewrite with add_comm and then get rid of parenthesis using add_assoc. refl will solve which is inside rw.
    nth_rewrite 1 mat.add_comm,
    rw mat.add_assoc,
  },
end
#check nat.left_distrib



lemma mat.add_mul_distrib (m n s : mat) :
  (m + n) * s = m  * s + n * s :=
begin
  induction s with s ihs,
  { -- proving base case `P 0`
    have h: mat.zero = 0, by refl, -- we want to make mat.zero to 0 so we can use lemmas
    rw h,
    repeat{ rw mat.mul_zero, }, -- we want to prove `(m + n) * 0 = m * 0 + n * 0`, we can rewrite mat.mul_zero to make the new goal `0 = 0 + 0`
    rw mat.add_zero, -- rewriting mat.add_zero proves the goal
  },
  { -- the inductive step: assuming `P n` and proving `P succ(n)`
    rw ← mat.add_one, -- we want to prove `(m + n) * s.succ = m * s.succ + n * s.succ`, we can rewrite with `add_one : m + 1 = m.succ` which makes the new goal `(m + n) * (s + 1) = m * (s + 1) + n * (s + 1)`
    repeat{rw mat.mul_add_distrib,}, -- we can use the lemma we just proved to make the new goal `(m + n) * s + (m + n) * 1 = m * s + m * 1 + (n * s + n * 1)`
    rw ihs, -- we can rewrite with the inductive hypothesis, makes the new goal `m * s + n * s + (m + n) * 1 = m * s + m * 1 + (n * s + n * 1)`
    repeat{rw mat.mul_one,}, -- we can rewrite the goal with `mat.mul_one : m * 1 = m`, which makes the goal `m * s + n * s + (m + n) = m * s + m + (n * s + n)`
    repeat{rw ← mat.add_assoc,}, -- we want to get rid of the parenthesis so we can use communative property to prove the goal
    nth_rewrite 1 mat.add_comm,
    rw ← mat.add_assoc,
    nth_rewrite 5 mat.add_comm,
  },
end


lemma mat.two_mul (m : mat) :
  2 * m = m + m :=
begin
  induction m with m ihm,
  { -- proving base case `P 0`
    simp, -- solves the goal by making mat.zero to 0 and using lemmas mat.add_zero and mat.mul_zero
  },  
  { -- the inductive step: assuming `P n` and proving `P succ(n)`
    rw mat.mul_succ, -- we want to prove `2 * m.succ = m.succ + m.succ`, we can use `mul_succ : m * n.succ = m * n + m` which makes the new goal `2 * m + 2 = m.succ + m.succ`
    rw mat.add_succ, -- we can use `add_succ : m + n.succ = (m + n).succ` to make the new goal `2 * m + 2 = (m.succ + m).succ`
    repeat{rw ← mat.one_add,}, -- we can use `one_add : 1 + n = n.succ` to make the new goal `2 * m + 2 = 1 + (1 + m + m)`
    rw ihm, -- we can rewrite with the inductive hypothesis which makes the goal `m + m + 2 = 1 + (1 + m + m)`
    repeat{rw ← mat.add_assoc,}, -- we can use `add_assoc : a + b + c = a + (b + c)` to make the new goal ` + m + 2 = 1 + 1 + m + m`
    rw mat.add_one, -- we can use add_one `n + 1 = n.succ` to make the new goal `m + m + 2 = 1.succ + m + m`
    have h: 2 = (1 : mat).succ, from rfl, -- we want to rewrite 2 with 1.succ so we can make the left side of the equality look more like the right
    rw h,
    rw mat.add_comm, -- we want to prove `m + m + 1.succ = 1.succ + m + m` and we know this is true with communitive and associative properties
    rw ← mat.add_assoc,
  },
end






/-! ## Question 3 (20 pts) :
In this exercise you will prove that for any natural number `n`,
`2 * (1 + ... + n) = n * (n + 1)`
which is allegedly proved by Gauss in the 18th century when he was a primary school student. https://nrich.maths.org/2478
-/

#check mat.sum_up_to --defined in the lecture


/- To prove this statement we need to prove an additional lemma to the repository of lemmas proved about `mat` in lecture 14.  -/


theorem sum_up_to_closed_formula :
  ∀ n : mat, 2 * (mat.sum_up_to n) = n * (n + 1) :=
begin
  intro n, -- we can use intro rule of ∀
  induction n with n ihn,
  { -- proving base case `P 0`
    simp, -- we want to prove `2 * mat.zero.sum_up_to = mat.zero * (mat.zero + 1)`, simp uses mat.zero_add and mat.zero_mul to make the new goal `2 * 0.sum_up_to = 0`
    rw mat.sum_up_to, -- in def of sum_up_to, it has proof of 0.sum_up_to as 0
    rw mat.mul_zero, -- we can use mul_zero : m * 0 = 0
  },
  { -- the inductive step: assuming `P n` and proving `P succ(n)`
    rw mat.sum_up_to, -- we want to prove `2 * n.succ.sum_up_to = n.succ * (n.succ + 1)`, we can rw with sum_up_to because the def has n.succ. the new goal is `2 * (n.sum_up_to + n.succ) = n.succ * (n.succ + 1)`
    rw mat.mul_add_distrib, -- we can use the lemma we created, mul_add_distrib, earlier to make the new goal `2 * n.sum_up_to + 2 * n.succ = n.succ * (n.succ + 1)`
    rw ihn, -- we can use the inductive hypothesis to make the new goal `n * (n + 1) + 2 * n.succ = n.succ * (n.succ + 1)`
    rw mat.mul_succ, -- we can use lemma mul_succ to mulitply 2 with n.succ, the new goal becomes `n * (n + 1) + (2 * n + 2) = n.succ * (n.succ + 1)`
    repeat{rw mat.mul_add_distrib,}, -- we can use lemma mul_add_distrib that we created earlier to multiply n with n+1 and n.succ with n.succ+1
    have h: 2 = (1 : mat).succ, from rfl,-- we want to replace 2 with 1.succ so that we can use one_add lemma later
    rw h,
    repeat{rw ← mat.one_add,},
    simp, -- simp will use add_one and mul_one to simplify the goal
    repeat{rw ← mat.one_add,}, -- one_add will replace 1.succ with 1+1, the new goal is `n * n + n + (1 + 1) * n = (1 + n) * n + n + n`
    repeat{rw mat.add_mul_distrib,}, -- we can distribute the n with 2 cases across the equation to make the new goal `n * n + n + (1 * n + 1 * n) = 1 * n + n * n + n + n`
    rw mat.one_mul, -- we can simplify the goal with `one_mul : 1 * m = m` the goal becomes `n * n + n + (n + n) = n + n * n + n + n` which we can prove with communitivity and associativity
    nth_rewrite 1 mat.add_comm,
    rw ← mat.add_assoc,
  },
end








/-! ## Question 4 (20 pts)-/

variables {X Y : Type}


def has_retract (f : X → Y) : Prop :=
∃ r : Y → X, r ∘ f = id


lemma retract_inj {f : X → Y} :
  has_retract f → is_injective f :=
begin
  sorry,
end

/-
Use the lemma `has_retract` above to prove that the function `mat.succ` is injective.
-/

#check mat.succ

lemma inj_succ :
  is_injective mat.succ :=
begin
 sorry,
end







/-! ## Question 5 (20 pts)
Give a different proof that `mat.succ` is injective by filling in `sorry` placeholder below.
-/

@[simp]
def diagonal : mat → mat → Prop
| (mat.succ m) (mat.succ n) := (m = n)
| _     _     := true



lemma succ_inj (m n : mat) (h₁ : mat.succ m = mat.succ n) :
  m = n :=
begin
  have h₂ : (mat.succ m = mat.succ n) → diagonal (mat.succ m) (mat.succ n), 
  {
    simp, -- simp uses the def of diagonal and the lemma succ_inj to prove the goal `m.succ = n.succ → diagonal m.succ n.succ`
  },
  {
    apply h₂, -- we want to prove `m = n`, we can use the elim rule of implication with `h₂ : m.succ = n.succ → diagonal m.succ n.succ` to make the goal `m.succ = n.succ` which is the same as h₁. diagonal m.succ n.succ is definitionally equal to m = n, which is why it can be applied
    assumption,
  },

  --didn't have to use these because it was proven before?????
  --have h₃ : diagonal (mat.succ m) (mat.succ n), sorry,
  --have h₄ : m = n, by sorry,
  --sorry,
end






/-! ## Question 6 (20 pts)
Equip `mat` with the structure of a preorder by completing the following instance where the `≤` relation is defined as in below:
-/

def mat.le (m n : mat) : Prop := ∃ k, m + k = n

#check mat.le


/-
Prove that ≤ relation
-/
lemma mat.le_antisymm (m n : mat) :
  (mat.le m n) → (mat.le n m) → m = n :=
begin
  intros h₁ h₂,
  obtain ⟨k, hk⟩ := h₁,
  obtain ⟨l, hl⟩ := h₂,
  sorry,
end




/-! ## Question 7 (20 pts)
Equip `mat` with the structure of a preorder by completing the following instance where the `≤` relation is defined as in below:
-/

instance additive_preorder_mat : preorder mat :=
{
  le := mat.le,
  lt := sorry,
  le_refl := sorry,
  le_trans := sorry,
  lt_iff_le_not_le := sorry,
}






/-! ## Question 8 (20 pts)
We define __exponentiation__ for the type `mat`. Then you should prove that all powers of a positive number are positive. 
-/


def mat.power : mat → mat → mat
| m 0        := 1
| m (n + 1)  := (mat.power m n) * m


example : 
  mat.power 4 3 = 64 := 
begin
  refl, 
end 

postfix ` ^^ `:15  := mat.power


example : 0 ^^ 31 = 0 := 
begin
  refl, 
end  


@[simp]
lemma power_succ {a n : mat} : 
  a ^^  n.succ = (a ^^ n)  * a := 
begin
  refl, 
end   

-- Use induction on natural numbers to prove the following theorem. You may need to prove an extra lemma before that which states that the multiplication of two positive numbers  `a b : mat` is again positive (`a` is positive here means that `0 < a` which is inherited from the type class `preorder` and the fact that we gave an instance of preorder structure for type `mat`. ). 
theorem pos_of_power_of_pos (a : mat) : 
  ∀ n : mat, (0 < a) → (0 < (a^^n)) :=
begin
  intro n, -- we can prove `∀ (n : mat), 0 < a → 0 < a ^^  n` by the intro rule of ∀ 
  intro h, -- we can prove `0 < a → 0 < a ^^  n` by the intro rule of implication
  induction n with n ihn,
  {
    simp, -- we want to prove `0 < a ^^  mat.zero`, simp proves that mat.zero = 0 and replaces it
    rw mat.power, -- the def of mat.power makes the goal 0 < 1
    have h₁: 1 = (0 : mat).succ, by refl, -- we can replace 1 with 0.succ to further the goal
    rw h₁,
    have h₂, from mat.no_conf 0,-- i think that less than is not the same but basically that the two variables do NOT equal each other
    sorry,
  },
  {
    rw power_succ, -- we want to prove `0 < a ^^  n.succ`, we can use the power_succ lemma to make the goal `0 < a ^^  n * a`
    sorry,
  },

end

/- 
Homeowork 11  
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec14_inductive_naturals
import homework.hw10


open PROOFS 
open PROOFS.STR 



/-
Note that the code below is not wrapped by the namespace `mat`, so if you want to use a definition or lemma/theorem named `xyz` from lec14 you need to append `mat` to its name and use it as `mat.xyz`. 
-/



/-! ## Question 1 (20 pts) : 
Prove the following results using `cases` or `induction`. 
-/


lemma mat.zero_of_add_eq_zero (m n : mat) : 
  m + n = 0  → (m = 0) ∧ (n = 0) := 
begin
 sorry,  
end    


lemma mat.zero_of_mul_eq_zero (m n : mat) : 
  m * n = 0  → (m = 0) ∨ (n = 0) := 
begin
  sorry, 
end 



/-! ## Question 2 (20 pts) : 
Prove the following distributivity result and then use them to prove lemma `mat.two_mul` (a proof of `mat.two_mul` which does not use distributivity lemmas is also accepted). 
-/

lemma mat.mul_add_distrib (k m n : mat) : 
  k * (m + n) = k * m + k * n := 
begin
  sorry, 
end   
#check nat.left_distrib



lemma mat.add_mul_distrib (m n s : mat) : 
  (m + n) * s = m  * s + n * s := 
begin
  sorry, 
end   


lemma mat.two_mul (m : mat) : 
  2 * m = m + m := 
begin
  sorry, 
end   






/-! ## Question 3 (20 pts) : 
In this exercise you will prove that for any natural number `n`, 
`2 * (1 + ... + n) = n * (n + 1)`
which is allegedly proved by Gauss in the 18th century when he was a primary school student. https://nrich.maths.org/2478
-/

#check mat.sum_up_to --defined in the lecture 


/- To prove this statement we need to prove an additional lemma to the repository of lemmas proved about `mat` in lecture 14.  -/


theorem sum_up_to_closed_formula : 
  ∀ n : mat, 2 * (mat.sum_up_to n) = n * (n + 1) :=
begin
  sorry, 
end   








/-! ## Question 4 (20 pts)-/

variables {X Y : Type}


def has_retract (f : X → Y) : Prop := 
∃ r : Y → X, r ∘ f = id 


lemma retract_inj {f : X → Y} : 
  has_retract f → is_injective f :=
begin
  sorry, 
end 

/-
Use the lemma `has_retract` above to prove that the function `mat.succ` is injective.
-/

#check mat.succ

lemma inj_succ : 
  is_injective mat.succ :=
begin
 sorry, 
end   







/-! ## Question 5 (20 pts)
Give a different proof that `mat.succ` is injective by filling in `sorry` placeholder below. 
-/

@[simp]
def diagonal : mat → mat → Prop
| (mat.succ m) (mat.succ n) := (m = n)
| _     _     := true



lemma succ_inj (m n : mat) (h₁ : mat.succ m = mat.succ n) : 
  m = n :=
begin
  have h₂ : (mat.succ m = mat.succ n) → diagonal (mat.succ m) (mat.succ n), sorry,  
  have h₃ : diagonal (mat.succ m) (mat.succ n), sorry,  
  have h₄ : m = n, by sorry, 
  sorry, 
end 






/-! ## Question 6 (20 pts) 
Equip `mat` with the structure of a preorder by completing the following instance where the `≤` relation is defined as in below: 
-/ 

def mat.le (m n : mat) : Prop := ∃ k, m + k = n

--#check mat.le


lemma add_cancel {k m n : mat} : 
  (k + m = k + n) → m = n := 
begin 
  intro h, 
  -- want to prove m = n, 
  induction k with d ihd, 
  {
    sorry,
  },
  {
    sorry, 
  },
  
end 


/-
Prove that ≤ relation 
-/
lemma mat.le_antisymm (m n : mat) : 
  (mat.le m n) → (mat.le n m) → m = n := 
begin
  intros h₁ h₂, 
  obtain ⟨k, hk⟩ := h₁, 
  obtain ⟨l, hl⟩ := h₂,  
  sorry,  
end 




/-! ## Question 7 (20 pts) 
Equip `mat` with the structure of a preorder by completing the following instance where the `≤` relation is defined as in below: 
-/ 

instance additive_preorder_mat : preorder mat := 
{ 
  le := mat.le, 
  lt := sorry,
  le_refl := sorry,
  le_trans := sorry,
  lt_iff_le_not_le := sorry,   
}

#reduce additive_preorder_mat.le






/-! ## Question 8 (20 pts)
We define __exponentiation__ for the type `mat`. Then you should prove that all powers of a positive number are positive. 
-/


def mat.power : mat → mat → mat
| m 0        := 1
| m (n + 1)  := (mat.power m n) * m


example : 
  mat.power 4 3 = 64 := 
begin
  refl, 
end 

postfix ` ^^ `:15  := mat.power


example : 0 ^^ 31 = 0 := 
begin
  refl, 
end  


@[simp]
lemma power_succ {a n : mat} : 
  a ^^  n.succ = (a ^^ n)  * a := 
begin
  refl, 
end   
 

-- Use induction on natural numbers to prove the following theorem. You may need to prove an extra lemma before that which states that the multiplication of two positive numbers  `a b : mat` is again positive (`a` is positive here means that `0 < a` which is inherited from the type class `preorder` and the fact that we gave an instance of preorder structure for type `mat`. ). 
theorem pos_of_power_of_pos (a : mat) : 
  ∀ n : mat, (0 < a) → (0 < (a^^n)) :=
begin
  sorry, 
end




