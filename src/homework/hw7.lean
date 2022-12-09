import ..prooflab
import lectures.lec8_structure_unbundled
import lectures.lec9_structure_bundled
import data.matrix.notation
import linear_algebra.matrix.determinant




/-! # Homework 7: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.
You are allowed to use all the tactics we have learned so far. 
-/


-- set_option pp.all true

open PROOFS

open PROOFS.STR



variables {X Y Z : Type}



/-! ## Question 1 (20 pts): 
The following question has two parts. 
-/

/- **Part I** 
We define the structure `Q1` and `Q2` similar to `R1` and `R2` of the lecture. -/ 

@[ext] 
structure Q1 := 
(x : ℚ)  

@[ext] 
structure Q2 := 
(x : ℚ) 
(y : ℚ)


/-
Define the operations of addition and multiplication on `Q1` and `Q2` and prove that they are associative and commutative. 
-/

@[simp]
def Q1.add (p q : Q1) : Q1 := 
⟨p.x + q.x⟩ -- we want to add the value of p and q when they are types of Q1, which has x. In order to call upon x, we have to use the .x notation and the goal of this def is to add them together

@[simp]
def Q2.add (p q : Q2) : Q2 :=
⟨p.x + q.x, p.y + q.y⟩ -- similar to Q1, although there are two variables in the stucture of Q2, which are x and y, which we still use the .x and .y notation to add them both

@[simp]
def Q1.mul (p q : Q1) : Q1 :=
⟨p.x * q.x⟩ -- same as Q1.add but multiplcation

@[simp]
def Q2.mul (p q : Q2) : Q2 :=
⟨p.x * q.x, p.y * q.y⟩ -- same as Q2.add but multiplication


theorem Q2.add_comm (p q : Q2) : 
   p .add q = q .add p :=
begin
  simp, -- we want to simplify the goal with the definitions we established
  split, -- we want to prove `p.x + q.x = q.x + p.x ∧ p.y + q.y = q.y + p.y`, so we can use the introduction rule of conjugation to make two new goals
  repeat{rw add_comm,}, -- we want to prove `p.x + q.x = q.x + p.x` and `p.y + q.y = q.y + p.y`, so we can rw add_comm for both, which changes the goals to `q.x + p.x = q.x + p.x` and `q.y + p.y = q.y + p.y`. These are proved with refl which is embedded in rw tactic
end 

theorem Q2.mul_comm (p q : Q2) : 
   p .mul q = q .mul p :=
begin
  simp, -- basically the same as Q2.add_comm, except that to prove the split goals, we need to use mul_comm
  split,
  repeat{rw mul_comm,},
end

theorem Q2.add_assoc (p q r : Q2) : 
   (p .add q) .add r = p .add (q .add r) :=
begin
  simp, -- we want to simplify the goal with the definitions we established
  split, -- we want to prove `p.x + q.x + r.x = p.x + (q.x + r.x) ∧ p.y + q.y + r.y = p.y + (q.y + r.y)`, so we can use the introduction rule of conjugation to make two new goals
  repeat{rw add_assoc,}, -- we want to prove `p.x + q.x + r.x = p.x + (q.x + r.x)` and `p.y + q.y + r.y = p.y + (q.y + r.y)`, so we can rw add_assoc for both, which changes the goals to `p.x + (q.x + r.x) = p.x + (q.x + r.x)` and `p.y + (q.y + r.y) = p.y + (q.y + r.y)`. These are proved with refl, which is embeded in rw tactic
end 

theorem Q2.mul_assoc (p q r : Q2) : 
   (p .mul q) .mul r = p .mul (q .mul r) :=
begin
  simp, --basically the same as Q2.add_assoc, except that to prove the split goals, we need to use mul_assoc
  split,
  repeat{rw mul_assoc,},
end


/- **Part II** : Given two points `p` and `q` in `Q2`, define their midpoint (https://en.wikipedia.org/wiki/Midpoint).
-/  

@[simp]
def Q2.midpoint (p q : Q2) : Q2 :=
⟨(p.x + q.x)/2, (p.y + q.y)/2⟩ -- the same as the midpoint formula, we can divide by 2 because p.x, p.y, q.x, and q.y are ℚ






/-!
## Question 2 (20 pts) : 
We define the structure `bijection` in below. Show that every equivalence gives rise to a bijection by filling in `sorry` placeholders. 
-/

@[simp]
def is_injective {X Y : Type} (f : X → Y) :=
∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂

@[simp]
def is_surjective {X Y : Type} (f : X → Y) :=
∀ y : Y, ∃ x : X, f x = y

/- `fun_equiv` (function equivalence) is the type of functions from `X → Y` with a two-sided inverse -/ 
@[ext]
structure fun_equiv (X : Type) (Y : Type) :=
(to_fun    : X → Y)
(inv_fun   : Y → X)
(left_inv  : inv_fun ∘ to_fun = id) -- i.e. inv_fun ∘ to_fun = id_X
(right_inv : to_fun ∘ inv_fun = id) -- i.e. to_fun ∘ inv_fun = id_Y

-- infix ` ≃ `:15 := fun_equiv

@[ext]
structure bijection (X Y : Type) :=
  (to_fun : X → Y)
  (inj : is_injective to_fun)
  (surj : is_surjective to_fun)



def bijection_of_equiv (f : fun_equiv X Y) : bijection X Y := 
{
  to_fun := f.to_fun, 
  inj :=    by {
                simp, -- we want to simplify the goal, so we can use simp because we added the definition of is_injective to simp
                intros x₁ x₂, -- we want to prove `∀ ⦃x₁ x₂ : X⦄, f.to_fun x₁ = f.to_fun x₂ → x₁ = x₂`, so we can use the introduction rule of ∀
                intro h₁, -- we want to prove `f.to_fun x₁ = f.to_fun x₂ → x₁ = x₂`, so we can use the introduction rule of implication
                -- we want to prove that `x₁ = x₂` from our assumptions, but I don't know how we can impliment h₁ to prove it. I thought congr_arg would work but it only proves if `x₁ = x₂ → f x₁ = f x₂` which is the opposite here.
                have h₂, from f.left_inv, -- we can use the left_inv to to evetually get rid of the f.to_fun from h₁, so that it looks like the goal
                have h₃: f.inv_fun(f.to_fun x₁) = f.inv_fun(f.to_fun x₂), by tauto, -- this is essentially the answer, although conceptually, this is not necessarilty true. However, if the composition of inv_fun and to_fun is id_X, then it should be the goal, just needing to be simplified
                sorry,
              },
  surj :=   by {
                simp, -- we want to simplify the goal, so we can use simp because we added the definition of is_surjective to simp
                intro y₁, -- we want to prove `∀ (y : Y), ∃ (x : X), f.to_fun x = y`, so we can use the introduction rule of ∀
                have x₁, from f.inv_fun y₁, -- we can add an assumption x₁ : X, from f.inv_fun y₁, for which f is a structure that holds inv_fun (Y → X), and when y₁ : Y is applied, it will output an X type which we call x₁.
                use x₁, -- we want to prove `∃ (x : X), f.to_fun x = y`, so we can use the introduction rule of ∃ and x₁ because in order to use the introduction rule, we need a value of type X
                sorry, -- I know both values are the same because f.to_fun x when evaluated should be a number of type Y, which is the same type as y. However, how do we prove that there is such a thing?
              },
}



/- **Questions 4 and 5 in below rely on the concept of sequences**.-/


/-
A __sequence__ in a type `X` is simply a function `a : ℕ → X`. The sequence `a` assigns to every natural number `n : ℕ` an element `a(n) : X` . In informal math texts, by convention, people write "a_{n}" for `a(n)` and "(a_{n})"" for the sequence `a : ℕ → X`. The notation "(a_{n})" communicates the idea of a sequence as an _infinite list_. Note that in lists, in contrast to sets, the order of appearance of elements matter. 
Here are some examples of sequences:
- `a : ℕ → ℤ` where `a n = (-1)^(n)`; the sequence terms are `1,-1,1,-1,...`
- `b : ℕ → ℚ` in `ℚ` where `b n = n/(1+n : ℚ)`; the sequence terms are 
`0,1/2, 2/3, 3/4,...` 
-/


/-
We can add and multiply sequences in `ℝ` component-wise, i.e. the sum `a + b` of sequences 
-/


section 
variables a b : ℕ → ℝ
variable n : ℕ 
#check a n 
#check b n 
#check a n + b n
#check (a + b) n
end 

lemma sum_of_seq_component_wise {a b : ℕ → ℝ} : 
  ∀ n : ℕ, (a + b) n = a n + b n  := 
begin
  intro n, 
  refl, 
end   




/- As we saw in the lecture on unbundled structures, a structure may depend on a parameter. Here we define the structure of __upper bounds__ for sequences. Note that the structure `upper_bound` depends on a sequence `a : ℕ → ℝ`. The structure `upper_bound` consists of all sequences in `ℝ` with an explicit upper bound.
-/

structure upper_bound (a : ℕ → ℝ) :=
(ub : ℝ) -- the explicit data of upper bound 
(le_ub : ∀ (n : ℕ), a n < ub) -- th property of `ub` being an upper bound: all values of the sequence `a` are less than the bound `ub`. 

section 

variables (a : ℕ → ℝ) (M : upper_bound a)
#check upper_bound
#print upper_bound

#check upper_bound a

#check @upper_bound.ub
#check @upper_bound.ub a 
#check @upper_bound.ub a M
#check M.ub
end 


/-! ## Question 4 (20 pts):  
 Construct an upper bound for the sequence given by numbers `n/n+1` for `n : ℕ` by supplying correct expressions for `sorry` placeholders. The following lemmas might be useful. Also, the tactic `norm_cast` is useful when you want to prove something about a natural number treated as an integer, rational, or real number (or more generally when you have coercion). Here is a minial example of `norm_cast`. -/


example (n : ℕ) (h : 2 < n) : 
  2 < (n : ℝ) :=
begin 
  -- note that `exact h` does not work since `n` in the goal is a real numebr. 
  norm_cast, 
  exact h, 
end 

#check @div_le_iff
#check @div_le_div
#check @div_one
#check div_one (1 : ℝ)


def upbound_n_over_succ_n : 
  upper_bound (λ n, n/(1 + n : ℝ)) := 
{
  ub := 1, 
  le_ub := by {
                intro n, -- we want to prove `∀ (n : ℕ), ↑n / (1 + ↑n) < 1`, so we can use the introduction rule of ∀
                have h₁: 0 ≤ n, by linarith, -- I want to make assumptions using my knowledge of ℕ and the goal to use div_le_div
                have h₂: 0 < n + 1, by linarith, -- I want to make assumptions using my knowledge of ℕ and the goal to use div_le_div
                have h₃: n < n + 1, by linarith, -- I want to make assumptions using my knowledge of ℕ and the goal to use div_le_div
                sorry, -- from here, I tried to use div_le_div, but it keeps saying that h₁ cannot be used because n is unrecognized, I'm not too sure where to go from here.
              },
}


/-! ## Question 6 (40 pts)
In geometry, a simplex (plural: simplexes or simplices) is a generalization of the notion of a triangle or tetrahedron to arbitrary dimensions. 
https://en.wikipedia.org/wiki/Simplex
https://en.wikipedia.org/wiki/Simplex#/media/File:2D-simplex.svg
We define the __standard geometric one-dimensional and two-dimensional simplices__ as the following structures. 
-/

@[ext]
structure standard_one_simplex :=
(x : ℝ)
(y : ℝ)
(x_nonneg : 0 ≤ x)
(y_nonneg : 0 ≤ y)
(sum_eq   : x + y = 1)


@[ext]
structure standard_two_simplex :=
(x : ℝ)
(y : ℝ)
(z : ℝ)
(x_nonneg : 0 ≤ x)
(y_nonneg : 0 ≤ y)
(z_nonneg : 0 ≤ z)
(sum_eq   : (x + y) + z = 1)

#check standard_two_simplex


/- 
We introduce the following _notations_ for the `standard_one_simplex` and `standard_two_simplex`
 -/

notation `Δ_1` := standard_one_simplex
notation `Δ_2` := standard_two_simplex



/- **Part I** : 
Construct three distinct points (i.e. instances) of `Δ_1`  and two points (i.e. instances) of `Δ_2` with the given constraints. 
-/



def Δ_1.point1 : Δ_1 := 
{
  x := 1, -- Because this is a structure `Δ_1`, `x` input must be a number where `x + y = 1`. We are going to have to prove that `x + y = 1` in sum_eq, which is in the structure `Δ_1` Because y = 0, the most logical thing is to make `x = 1` to make it true
  y := 0, 
  x_nonneg := by {linarith,}, -- 0 ≤ 1 will always be true, we can prove this by linarith
  y_nonneg := by {linarith,}, -- 0 ≤ 0 will always be true, we can prove this by linarith
  sum_eq := by {rw add_zero,}, -- we want to prove 1 + 0 = 1, so we can use rw add_zero, which states that anything plus 0 is that thing. rw tactic includes refl which is why the goal is accomplished
}


def Δ_1.point2 : Δ_1 := 
{
  x := 0,
  y := 1, -- Because this is a structure `Δ_1`, `y` input must be a number where `x + y = 1`. We are going to have to prove that `x + y = 1` in sum_eq, which is in the structure `Δ_1` Because x = 0, the most logical thing is to make `y = 1` to make it true
  x_nonneg := by {linarith,}, -- 0 ≤ 0 will always be true and we can prove this with linarith
  y_nonneg := by {linarith}, -- 0 ≤ 1 will always be true and we can prove this with linarith
  sum_eq := by {rw zero_add,}, -- we want to prove 0 + 1 = 1, so we can use rw zero_add, which states that 0 plus anything is that thing. rw tactic includes refl which is why the goal is accomplished
}


noncomputable
def Δ_1.point3 : Δ_1 := 
{
  x := 1/(2 : ℚ),
  y := 1/2, -- Because this is a structure `Δ_1`, `y` input must be a number where `x + y = 1`. We are going to have to prove that `x + y = 1` in sum_eq, which is in the structure `Δ_1` Because x = 1/(2 : ℚ), the most logical thing is to make `y = 1/2` to make it true
  x_nonneg := by {
                  norm_cast, -- we want to treat `1/(2 : ℚ)` as an integer so we can prove it
                  linarith, -- `0 ≤ 1/2` will always be true so we can use linarith
                 }, 
  y_nonneg := by {linarith,}, -- `0 ≤ 1/2` will always be true so we can use linarith
  sum_eq := by {
                 ring_nf, -- we want to simplify in terms of something that we can use, so we can use ring
                 norm_num, -- by normalizing the goal it makes it `1/2 + 1/2 = 1`, which is true by the embedded refl
               }, 
}




def Δ_2.point1 : Δ_2 := 
{
  x := 1,
  y := 0,
  z := 0, -- Because this is a structure `Δ_2`, `z` input must be a number where `x + y + z = 1`. We are going to have to prove that `x + y + z = 1` in sum_eq, which is in the structure `Δ_2` Because x = 1 and y = 0, the most logical thing is to make `z = 0` to make sum_eq true
  x_nonneg := by {linarith,}, -- 0 ≤ 1 is always true so we can use linarith
  y_nonneg := by {linarith,}, -- 0 ≤ 0 is always true s owe can use linarith
  z_nonneg := by {linarith,}, -- 0 ≤ 0 is always true s owe can use linarith
  sum_eq := by {repeat{rw add_zero,},}, -- we want to prove 1 + 0 + 0 = 1, so we can rewrite the goal with add_zero, which states that anything plus 0 is that thing. We do it twice because there are two zeros to get rid of. The goal is accomplished because refl is embedded in rw tactic
}



noncomputable
def Δ_2.point2 : Δ_2 := 
{
  x := 1/2, -- Because this is a structure `Δ_2`, `x` input must be a number where `x + y + z = 1`. We are going to have to prove that `x + y + z = 1` in sum_eq, which is in the structure `Δ_2` Because we will make y = 0 and z is already 1 / (2 : ℚ), the most logical thing is to make `x = 1/2` to make sum_eq true
  y := 0, -- Because this is a structure `Δ_2`, `y` input must be a number where `x + y + z = 1`. We are going to have to prove that `x + y + z = 1` in sum_eq, which is in the structure `Δ_2` Because x = 1/2 and z = 1/(2: ℚ), the most logical thing is to make `y = 0` to make sum_eq true
  z:= 1/(2 : ℚ),
  x_nonneg := by {linarith,}, -- `0 ≤ 1/2` will always be true so we can use linarith
  y_nonneg := by {linarith,}, -- `0 ≤ 0` will always be true so we can use linarith
  z_nonneg := by {norm_cast, linarith,}, -- we want to prove `0 ≤ 1/(2:ℚ)`, so we can normcast first to make 2 an integer so we can prove that `0 ≤ 1/2`, which is always true
  sum_eq := by {
                  ring_nf, -- we want to simplify the goal so we can use it
                  norm_num, -- we can normalize the goal so that `1/2 + 1/2 = 1`, which is true by refl which is embedded in norm_num
               }, 
}








----------------------------------------
-- **Maps of standard n-simplices**
----------------------------------------

/-
Maps of standard simplices are induced from functions of affine plane (i.e. point3d, point2d, and point1d) with the extra constraints that they map the points in one simplex into the points of the other. The constraints become part of the data of the map between simplices. 
-/


/-
 There are two __degeneracy maps__ from the standard 2-simplex to the standard 1-simplex: try to understand the geometric idea begind these maps.
-/

/- 
**Part II** : Fill in `sorry` placeholders in below so that `dg_2d_to_1d_fst` and `dg_2d_to_1d_snd` are functions from the type `Δ_2` to `Δ_1`. 
-/

def dg_2d_to_1d_fst  (a : Δ_2) : Δ_1 
:= 
{ x := a.x, 
  y := a.y + a.z, 
  x_nonneg := by {
                    exact a.x_nonneg, -- Because `a : Δ_2`, it contains `(x : ℝ) (y : ℝ) (z : ℝ) (x_nonneg : 0 ≤ x) (y_nonneg : 0 ≤ y) (z_nonneg : 0 ≤ z) (sum_eq   : (x + y) + z = 1)`, and we want to prove `0 ≤ a.x`, so we can use `exact a.x_nonneg`, which proves a.x will always be ≥ 0 or not negative.
                  }, 
  y_nonneg := by {
                    -- we want to prove `0 ≤ a.y + a.z`, but we have to prove that both a.y and a.z are nonneg because then, ∀ cases, this will be true. So we provide a proof that y is nonneg with a.y_nonneg, z is nonneg with a.z_nonneg.
                    have h₁, from a.y_nonneg, -- Becuase `a : Δ_2`, it contains `y_nonneg` which says that `0 ≤ y`. y being inside a, we must call it using the `.` notation
                    have h₂, from a.z_nonneg, -- Becasue `a : Δ_2` it conatins `z_nonneg` which says that `0 ≤ z`. z being inside a, we must call it using the `.` notation
                    have h₃, from add_le_add h₁ h₂, -- we can use the lemma add_le_add to prove that if both h₁ and h₂ added together will be `0 + 0 ≤ a.y + a.z`, which is close to the goal
                    rw add_zero at h₃, -- we want to prove h₃ is the goal, so we rw add_zero, which states that any number plus 0 is that number
                    assumption, -- we can prove the exact assumption from the goal
                  },
  sum_eq := by {
                  have h₁, from a.sum_eq, -- Because `a : Δ_2`, it contains sum_eq, which states that `x + y + z = 1`, which is close to the goal, so we can make it an assumption by using `have`. We must use `.` notation in order to call it from a, because it is a structure
                  rw ← add_assoc, -- we can rewrite the goal in terms of the assumption by using ← add_assoc, which basically gets rid of the perenthesis and makes the goal look like the assumption h₁
                  assumption, -- we can prove the exact goal from an assumption
  }, 
}



def dg_2d_to_1d_snd  (a : Δ_2) : Δ_1
:= 
{ x := a.x + a.y, 
  y := a.z, 
  x_nonneg := by {
                    -- we want to prove `0 ≤ a.x + a.y`, but we have to prove that both a.x and a.y are nonneg because then, ∀ cases, this will be true. So we provide a proof that x is nonneg with a.x_nonneg, y is nonneg with a.y_nonneg.
                    have h₁, from a.x_nonneg, -- Becuase `a : Δ_2`, it contains `x_nonneg` which says that `0 ≤ x`. x being inside a, we must call it using the `.` notation
                    have h₂, from a.y_nonneg, -- Becasue `a : Δ_2` it conatins `y_nonneg` which says that `0 ≤ y`. y being inside a, we must call it using the `.` notation
                    have h₃, from add_le_add h₁ h₂, -- we can use the lemma add_le_add to prove that if both h₁ and h₂ added together will be `0 + 0 ≤ a.x + a.y`, which is close to the goal
                    rw add_zero at h₃, -- we want to prove h₃ is the goal, so we rw add_zero, which states that any number plus 0 is that number
                    assumption -- we can prove the exact assumption from the goal
                  }, 
  y_nonneg := by {
                    exact a.z_nonneg, -- we want to prove that 0 ≤ a.z, which is exactly what a.z_nonneg is. z_nonneg is contained in structure Δ_2, which we must call using the `.` notation.
                  }, 
  sum_eq := by {
                  exact a.sum_eq, -- we want to prove that `a.x + a.y + a.z = 1`, which is exactly what a.sum_eq is. sum_eq is contained in the structure Δ_2, which we must call using `.` notation and states that `x + y + z = 1`.
                },
}



/- **Part III**: 
Prove the following equality of points in `Δ_1`  (i.e. instance of structure `Δ_1`.) -/

example : 
  dg_2d_to_1d_fst Δ_2.point1 = Δ_1.point1 := 
begin
   ext,
   {
      refl, -- we want to prove `(dg_2d_to_1d_fst Δ_2.point1).x = Δ_1.point1.x`. Thinking about it these are exactly the same. Because the `x of dg_2d_to_1d_fst` is `a.x` and the `x of Δ_2.point1` is `1`, in simplification, the left side of the equality is equal to 1 and `Δ_1.point1` is also equal to 1, which we can prove by refl.
   },
   {
      exact add_zero Δ_2.point1.y, -- we want to prove `(dg_2d_to_1d_fst Δ_2.point1).y = Δ_1.point1.y`. Because `dg_2d_to_1d_fst.y` is equal to `a.y + a.z` and `a.y and a.z is equal to 0`, the left side of the equality is `0 + 0`. Because the right side of the equality is also equal to `0`, we can prove this by using the `add_zero` lemma to `Δ_2.point1.y`, which makes the goal `0 = 0`, which is exactly the same
   },
end 


example : 
  dg_2d_to_1d_snd Δ_2.point2 = Δ_1.point3 := 
begin
   ext,
   {
      unfold Δ_1.point3, -- We want to prove `(dg_2d_to_1d_snd Δ_2.point2).x = Δ_1.point3.x`,but I want to see the components of `Δ_1.point3`, so the unfold tactic works to do that
      unfold Δ_2.point2, -- We want to prove the new goal,`(dg_2d_to_1d_snd Δ_2.point2).x = {x := 1 / ↑2, y := 1 / 2, x_nonneg := Δ_1.point3._proof_1, y_nonneg := Δ_1.point3._proof_2, sum_eq := Δ_1.point3._proof_3}.x`,but I want to see the components of Δ_2.point2, so the unfold tactic works to do that
      norm_cast, -- we want to normalize all numbers to integers so we can use them, makes the new goal `(dg_2d_to_1d_snd Δ_2.point2).x = {x := 1 / ↑2, y := 1 / 2, x_nonneg := Δ_1.point3._proof_1, y_nonneg := Δ_1.point3._proof_2, sum_eq := Δ_1.point3._proof_3}.x`
      norm_num, -- this makes all numbers normalized so that we can use them and also make the right side of the equality equal to 1/2. The goal is now `(dg_2d_to_1d_snd {x := 1 / 2, y := 0, z := 1 / 2, x_nonneg := _, y_nonneg := _, z_nonneg := _, sum_eq := _}).x = 1 / 2`.
      exact add_zero Δ_2.point2.x, -- we want to prove `(dg_2d_to_1d_snd {x := 1 / 2, y := 0, z := 1 / 2, x_nonneg := _, y_nonneg := _, z_nonneg := _, sum_eq := _}).x = 1 / 2`. Because `x` value of `dg_2d_to_1d_snd` is `a.x + a.y` and `a.x` is `Δ_2.point2.x` which = `1/2` and `a.y` is `Δ_2.point2.y` which = `0`, the simplified left side of the equality is `1/2 + 0`. We can use the rewrite tactic with the lemma `add_zero` to get rid of the zero because it proves that anything plus 0 is that thing, which makes the new goal `1/2 = 1/2`. this is exactly the same which accomplishes the goal
   },
   {
      unfold Δ_2.point2, -- We want to prove that `(dg_2d_to_1d_snd Δ_2.point2).y = Δ_1.point3.y`, but I want to see the componenets of `Δ_2.point2`, so the unfold tactic does that, this makes the new goal `(dg_2d_to_1d_snd {x := 1 / 2, y := 0, z := 1 / ↑2, x_nonneg := Δ_2.point2._proof_1, y_nonneg := Δ_2.point2._proof_2, z_nonneg := Δ_2.point2._proof_3, sum_eq := Δ_2.point2._proof_4}).y = Δ_1.point3.y`
      norm_cast, -- we want to normalize the all the numbers in the goal so that we can use proves that we know of integers, so norm_cast does that, the new goal is now `(dg_2d_to_1d_snd {x := 1 / 2, y := 0, z := ↑(1 / 2), x_nonneg := _, y_nonneg := _, z_nonneg := _, sum_eq := _}).y = Δ_1.point3.y`
      norm_num, -- we want to normalize the goal, which makes the new goal `(dg_2d_to_1d_snd {x := 1 / 2, y := 0, z := 1 / 2, x_nonneg := _, y_nonneg := _, z_nonneg := _, sum_eq := _}).y = Δ_1.point3.y`
      refl, -- this is exactly the same because `y` component of structure `dg_2d_to_1d_snd` is `a.z` and `a.z` is `Δ_2.point.z`, which is now `1/2`. This mean the goal is `1/2 = Δ_1.point3.y`. `Δ_1.point3.y` is the y component of `Δ_1.point3`, which is also 1/2. This means that the goal is `1/2 = 1/2`, which is proven by refl
   },
end 

end





