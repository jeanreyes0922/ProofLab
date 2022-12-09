import ..prooflab
import lectures.lec7_predicate


/-! # Homework 6: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far.
 -/


namespace PROOFS


variables {X Y Z : Type}



/-! ## Question 1 (20 points):
The following question has five lemmas each worth 4 points. Refer to the lecture file for a review of concepts of __binary relation__ and __equivalence relation__.
-/

-- let X be a type, and let R be a binary relation on R.
variable {R : X → X → Prop}


namespace equivalence_alt

lemma refl_ext_left {ρ : reflexive R} (x y : X) (H : ∀ a : X,  R a x → R a y) :
  R x y :=
begin
  apply H x, -- H x is the binary relation R x x → R x y because x supplies the Type that we can apply to the goal, which rewrites the right side of the predicate to the left
  exact ρ x, -- ρ x is the reflexive R supplied with x which is X → X → Prop applied to x, R x x. This is the same as the goal R x x
end


lemma refl_ext {ρ : reflexive R} (x y : X) (H : ∀ a: X,  R x a ↔ R y a) :
  R x y :=
begin
  have h₁: R x y ↔ R y y, from H y, -- we want to make an assumption R x y ↔ R y y, which we can from H y in order to make it look somewhat like the goal
  cases h₁ with hxy hyy, -- we want to prove R x y ↔ R y y. We can use the elim rule of biimplication to make two new assumptions R x y → R y y and R y y → R x y
  apply hyy, -- we want to prove R x y, so we can use the elim rule of implication, apply, which rewrites the goal to the left side of the implication
  exact ρ y, -- ρ y is the reflexive R supplied with y which is X → X → Prop applied to y, R y y. This is the same as the goal R y y
end


lemma refl_symm_ext_left {ρ : reflexive R} {σ : symmetric R} (x y : X) (H : ∀ a : X,  R x a → R y a) :
  R x y :=
begin
  have h₁: R x x → R y x, from H x, -- we want to make an assumption R x x → R y x, which we can from H x in order to make it look somewhat like the goal
  apply σ, -- we want to make the goal R y x so we can use the assumption we just made, using the elim rule of implication, we can apply σ, which proves R a b = R b a
  apply h₁, -- we want to prove R y x, so we can use the elim rule of implication, apply, which rewrites the goal as the left side of the implication h₁, R x x
  exact ρ x, -- ρ x is the reflexive R supplied with x which is X → X → Prop applied to x, R x x. This is the same as the goal R x x
end


lemma eqv_rel_ext {eqv : equivalence R} (x y : X) (H : ∀ a : X,  R x a → R y a) : R x y :=
begin
obtain ⟨ρ, σ, τ⟩ := eqv, -- I'm not really sure what 'obtain' does, but it does include relexive, symmetric, and transitive properties of relation R
  have h₁: R x x → R y x, from H x, -- we want to make an assumption R x x → R y x, which we can from H x in order to make it look somewhat like the goal
  apply σ, -- we want to make the goal R y x so we can use the assumption we just made, using the elim rule of implication, we can apply σ, which proves R a b = R b a
  apply h₁, -- we want to prove R y x, so we can use the elim rule of implication, apply, which rewrites the goal as the left side of the implication h₁, R x x
  exact ρ x, -- ρ x is the reflexive R supplied with x which is X → X → Prop applied to x, R x x. This is the same as the goal R x x
end


lemma trans_ext {tr : transitive R} (x y : X) (H : ∃ a : X, R x a ∧ R a y) : R x y :=
begin
  cases H with H1 Hh,
  cases Hh with right left, -- we want to prove R x H1 ∧ R H1 y, so we can use the elim rule of conjugation to make two new assumptions R x H1 and R H1 y
  apply tr, -- we want to prove the goal R x y, so we can use the assumption tr, which says that the goal is transitive. We need the tactic apply, which is an elim rule of implication
  {
    assumption, -- we can prove the goal, R x m_1, with R x H1
  },
  {
    assumption, -- we can prove the goal, R m_1 y, with R H1 y(m_1 was specified in the goal before, so the goal is actually R H1 y)
  },
end

end equivalence_alt -- end of namespace


@[simp]
def is_injective {X Y : Type} (f : X → Y) :=
∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂




/-! ## Question 2 (10 points): -/

lemma injection_respect_distinction_alt {X Y : Type} {f : X → Y} (inj : is_injective f) :
  ∀ ⦃x₁ x₂⦄, (x₁ ≠ x₂)  → (f x₁ ≠ f x₂) :=
begin
  unfold is_injective at *, -- we want to make both the goal and assumptions clearer, we can `unfold` everywhere to do that
  intro x₁, -- we want to prove `∀ ⦃x₁ x₂ : X⦄, x₁ ≠ x₂ → f x₁ ≠ f x₂`, so we fix an arbitrary element `x₁`. The intro rule of ∀ is used
  intro x₂, -- we want to prove `∀ ⦃x₂ : X⦄, x₁ ≠ x₂ → f x₁ ≠ f x₂`, so we fix an arbitrary element of `x₂`. The intro rule of ∀ is used
  intro xnx, -- we want to prove `x₁ ≠ x₂ → f x₁ ≠ f x₂`, so we use the intro rule of implication, which makes the new goal `f x₁ ≠ f x₂`
  intro fxnfx, -- we want to prove `f x₁ ≠ f x₂`, which we know is the same as `f x₁ = f x₂ → false`, so we use the intro rule of implication to make the new goal `false`.
  apply xnx, -- we want to prove `false`, so we can use the elim rule of implication at `xnx (x₁ ≠ x₂)`, which is the same as `x₁ = x₂ → false`. This makes the new goal `x₁ = x₂`.
  apply inj, -- we want to prove `x₁ = x₂`, so we can use the elim rule of implication at `inj (∀ ⦃x₁ x₂ : X⦄, f x₁ = f x₂ → x₁ = x₂)`, which, because we have x₁ and x₂ in the goal, we can rewrite the goal to `f x₁ = f x₂`.
  assumption, -- we can prove the exact goal with an assumption.
end







/-! ## Question 3 (20 points):

We Define a predicate which states whether a function of the form `ℤ × ℤ → ℤ` is symmetric. Recall that a function `f : ℤ × ℤ → ℤ` is said to be __symmetric__ if swapping the coordinates does not change the value of the function, i.e `f (x , y) = f(y , x)` for all integers `x` and `y`.
-/

def is_symm_fun (f : ℤ × ℤ → ℤ) := ∀ x y : ℤ, f (x , y) = f (y , x)

#check is_symm_fun


/-
**Part I**: Consider the functions `shift_fun` and `diff_fun_zero` defined in below. The function `cross_effect` is constructed from these functions. Lemma `cross_effect_defn` in below describes the effect of fucntion `cross_effect` on each pair `(x,y) : ℤ × ℤ`.
-/

def shift_fun (x : ℤ) (f : ℤ → ℤ) :=
λ y : ℤ, f (x + y)

#check shift_fun


def diff_fun_zero (f : ℤ → ℤ) (y : ℤ) :=
f y - f 0


#check diff_fun_zero

def cross_effect (f : ℤ → ℤ) (p : ℤ × ℤ) := (diff_fun_zero (shift_fun p.1 f) p.2) - (diff_fun_zero f p.2)


#eval cross_effect (λ x, x^2) (2, 3)



lemma cross_effect_defn {x y : ℤ} {f : ℤ → ℤ} :
cross_effect f (x,y) = f (x + y) - f (x) - f (y) + f(0) :=
begin
  unfold cross_effect, -- want to make the goal without any lemmas, so we can unfold all of them
  unfold diff_fun_zero,
  unfold shift_fun,
  ring_nf, -- we can prove this by ring, because ring proves everything. 
end

/-
**Part II**: Show that for any function `f : ℤ × ℤ → ℤ`, the cross-effect of `f` is symmetric by completing the following proof. You can use the lemma `cross_effect_defn`.
-/

theorem is_symm_cross_effect :
  ∀ f : ℤ → ℤ, is_symm_fun (cross_effect f) :=
begin
  intro f, -- we want to prove `∀ f : ℤ → ℤ, is_symm_fun (cross_effect f)`, so we can use the introduction rule of ∀, which makes an assumption f, which is of type ℤ → ℤ
  intro x, -- we want to prove `is_symm_fun (cross_effect f)`, so we can use the introduction rule of ∀ in `is_symm_fun`, which makes the assumption x which is of type ℤ
  intro y, -- we want to prove `∀ (y : ℤ), cross_effect f (x, y) = cross_effect f (y, x)`, so we can use the introduction rule of ∀, which makes the assumption y which is of type ℤ 
  rw cross_effect_defn, -- we can define the left side of the equation in the goal by cross_effect_defn, which, when we rewrite it, makes the left side `f (x + y) - f x - f y + f 0`(cross_effect_defn)
  rw cross_effect_defn, -- we can define the right side of the equation in the goal by cross_effect_defn, which, when we rewrite it, makes the right side `f (x + y) - f x - f y + f 0`(cross_effect_defn)
  ring, -- using definitions and assumptions , we can prove the goal, aka ring
end






/- ## Question 4 (20 points): -/

@[simp]
def bool_of_nat (n : ℕ) := 
if n = 0 then ff else tt

#check bool_of_nat
-- This function was defined in `lec3_function` as follows:
-- def bool_of_nat (n : ℕ) := if n = 0 then ff else tt

#check is_injective

lemma not_inj_bool_of_nat :
  ¬ is_injective (bool_of_nat) :=
begin
  norm_num, --  we want to normalize the numerical expression, `¬ is_injective (bool_of_nat)`, so we use norm_num, which gives us `∃ (x x_1 : ℕ), ite (x = 0) ff tt = ite (x_1 = 0) ff tt ∧ ¬x = x_1`
  use 1, -- we want to prove `∃ (x x_1 : ℕ), ite (x = 0) ff tt = ite (x_1 = 0) ff tt ∧ ¬x = x_1`, so we can use the introduction rule of ∃ to make the new goal `∃ (x : ℕ), ite (1 = 0) ff tt = ite (x = 0) ff tt ∧ ¬1 = x`
  use 2, -- we want to prove `∃ (x : ℕ), ite (1 = 0) ff tt = ite (x = 0) ff tt ∧ ¬1 = x`, so we can use the introduction rule of ∃ to make the new goal `ite (1 = 0) ff tt = ite (2 = 0) ff tt ∧ ¬1 = 2`
  split, -- we want to prove `ite (1 = 0) ff tt = ite (2 = 0) ff tt ∧ ¬1 = 2`, so we can use the introduction rule of conjugation, which makes two new goals
  {
    refl, -- both sides of the equation are reflexive, because they give the same output no matter what
  },
  {
    intro h₁, -- we want to prove `¬1 = 2`, which is really an implication → false, so we can use the introduction rule of implication/negation to make the new goal false and a new assumption 1 = 2
    linarith, -- we know that 1 ≠ 2, so we can use linarith to prove that 1 = 2 is the goal false
  },
end







/- ## Question 5 (30 points):

**Part I**:
Prove that for every function `f : X → Y` and `g : Y → Z`, if the composition `g ∘ f : X → Z` is injective then `f` is injective.
-/

#check congr_arg

lemma inj_right_of_inj_comp_alt (f : X → Y) (g : Y → Z) (h : is_injective (g ∘ f)) :
  is_injective f :=
begin
  unfold is_injective at *, -- I want to make is_injective more clear, so we can use the unfold tactic
  dsimp at h, -- we want to make h more clear, so we can use dsimp because they're compositions
  intro x₁, -- we want to prove `∀ ⦃x₁ x₂ : X⦄, f x₁ = f x₂ → x₁ = x₂`, so we can use the introduction rule of ∀ to make x₁ an assumption
  intro x₂, -- we want to prove `∀ ⦃x₂ : X⦄, f x₁ = f x₂ → x₁ = x₂`, so we can use the introduction rule of ∀ to make x₂ an assumption
  intro fx, -- we want to prove `f x₁ = f x₂ → x₁ = x₂`, so we can use the introduction rule of implication, making the new goal `x₁ = x₂`
  apply h, -- we want to prove `x₁ = x₂`, so we can use the elimination rule of ∀. This applies h to the goal, which makes the new goal `g (f x₁) = g (f x₂)`
  apply congr_arg, -- we want to prove `g (f x₁) = g (f x₂)`, so we can use the elimination rule of ∀ in the lemma `congr_arg`
  assumption, -- we can prove the exact goal from an assumption
end



/- **Part II**-/

@[simp]
def nat_of_bool : bool → ℕ 
| ff := 0 
| tt := 1 

/-def bool_of_nat (n : ℕ) := 
if n = 0 then ff else tt-/

#check nat_of_bool
#check bool_of_nat

lemma id_of_bool_nat_comp_nat_bool :
  bool_of_nat ∘ nat_of_bool = id :=
begin
  funext j, -- function extensionality applies the variable j to both sides
  dsimp, -- the new goal is definitionally equal
  cases j, -- we want to prove `ite (nat_of_bool j = 0) ff tt = j`, so we can use cases to give the finite variables that bool posseses, which are ff and tt
  {
    refl, --we want to prove `ite (nat_of_bool ff = 0) ff tt = ff`, so we can reflexivity.
  },
  {
    refl, -- we want to prove `ite (nat_of_bool tt = 0) ff tt = tt`, so we can use reflexivity
  },
end



/- **Part III**:
Use lemma `id_of_bool_nat_comp_nat_bool` and `not_inj_bool_of_nat` to prove the following statement.
-/

#check tactic.fconstructor
#check tactic.constructor

example :
∃ X Y Z : Type, ∃ f : X → Y, ∃ g : Y → Z,  is_injective (g ∘ f) ∧  ¬ is_injective g :=
begin
  norm_num, -- we want to normalize the goal
  use bool, -- we want to prove `∃ (X Y Z : Type) (f : X → Y) (g : Y → Z), (∀ ⦃x₁ x₂ : X⦄, g (f x₁) = g (f x₂) → x₁ = x₂) ∧ ∃ (x x_1 : Y), g x = g x_1 ∧ ¬x = x_1`, so we can use the introduction rule of ∃
  use ℕ, -- we want to prove `∃ (Y Z : Type) (f : bool → Y) (g : Y → Z), (∀ ⦃x₁ x₂ : bool⦄, g (f x₁) = g (f x₂) → x₁ = x₂) ∧ ∃ (x x_1 : Y), g x = g x_1 ∧ ¬x = x_1`, so we can use the introduction rule of ∃
  use bool, -- we want to prove `∃ (Z : Type) (f : bool → ℕ) (g : ℕ → Z), (∀ ⦃x₁ x₂ : bool⦄, g (f x₁) = g (f x₂) → x₁ = x₂) ∧ ∃ (x x_1 : ℕ), g x = g x_1 ∧ ¬x = x_1`, so we can use the introduction rule of ∃
  norm_num, -- we want to normalize the goal again
  fconstructor, -- similar to the intro rule of ∀, but makes you prove the ∃
  {
    exact nat_of_bool, -- we want to prove `bool → ℕ`, which is exactly what nat_of_bool's type is.
  },
  {
    norm_num, -- we want to normalize the goal
    fconstructor, -- similar to the intro rule of ∀, but mkaes you prove the ∃ 
    {
      exact bool_of_nat, -- we want to prove `ℕ → bool`, which is exactly what bool_of_nat's type is
    },
    {
      split, -- we want to prove `((bool_of_nat 0 = bool_of_nat 1 → false) ∧ (bool_of_nat 1 = bool_of_nat 0 → false)) ∧ ∃ (x x_1 : ℕ), bool_of_nat x = bool_of_nat x_1 ∧ ¬x = x_1`, so we can use the introduction rule of conjugation.
      {
        split, -- we want to prove `(bool_of_nat 0 = bool_of_nat 1 → false) ∧ (bool_of_nat 1 = bool_of_nat 0 → false)`, so we can use the introduction rule of conjugation
        {
          intro hp, -- we want to prove `bool_of_nat 0 = bool_of_nat 1 → false`, so we can use the introduction rule of implicaiton
          dsimp at *, -- we want to simplify the goal and its assumptions
          simp at hp, -- we want to simplify hp because we know that it is false
          assumption, -- we can prove the exact goal from an assumption
        },
        {
          intro hp, -- we want to prove `bool_of_nat 1 = bool_of_nat 0 → false`, so we can use the introduction rule of implication
          dsimp at *, -- we want to simplify the goal and assumptions
          simp at hp, -- we want to simplify hp because we know that it is false
          assumption, -- we can prove the exact goal from an assumption
        },
      },
      {
        use 1, -- we want to prove `∃ (x x_1 : ℕ), bool_of_nat x = bool_of_nat x_1 ∧ ¬x = x_1`, so we can use the introduction rule of ∃
        use 2, -- we want to prove `∃ (x : ℕ), bool_of_nat 1 = bool_of_nat x ∧ ¬1 = x`, so we can use the introduction rule of ∃
        split, -- we want to prove `bool_of_nat 1 = bool_of_nat 2 ∧ ¬1 = 2`, so we can use the introduction rule of conjugation
        {
          simp, -- we can simplify and say that the goal is false
        },
        {
          intro ho, -- we wnat to prove `¬1 = 2`, so we can use the introduction rule of implication
          linarith, -- we can prove the goal using assumptions and definitions
        },
      },
    },  
  },
end

import ..prooflab
import lectures.lec7_predicate


/-! # Homework 6: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far. 
 -/


namespace PROOFS


variables {X Y Z : Type}



/-! ## Question 1 (20 points): 
The following question has five lemmas each worth 4 points. Refer to the lecture file for a review of concepts of __binary relation__ and __equivalence relation__.
-/

-- let X be a type, and let R be a binary relation on R.
variable {R : X → X → Prop}


namespace equivalence_alt

lemma refl_ext_left {ρ : reflexive R} (x y : X) (H : ∀ a : X,  R a x → R a y) : 
  R x y :=
begin
  sorry, 
end 


lemma refl_ext {ρ : reflexive R} (x y : X) (H : ∀ a: X,  R x a ↔ R y a) : 
  R x y :=
begin
  sorry, 
end 


lemma refl_symm_ext_left {ρ : reflexive R} {σ : symmetric R} (x y : X) (H : ∀ a : X,  R x a → R y a) : 
  R x y :=
begin
  sorry, 
end    


lemma eqv_rel_ext {eqv : equivalence R} (x y : X) (H : ∀ a : X,  R x a → R y a) : R x y :=
begin 
obtain ⟨ρ, σ, τ⟩ := eqv, 
  sorry, 
end 


lemma trans_ext {tr : transitive R} (x y : X) (H : ∃ a : X, R x a ∧ R a y) : R x y := 
begin 
sorry, 
end 

end equivalence_alt -- end of namespace







/-! ## Question 2 (10 points): -/

lemma injection_respect_distinction_alt {X Y : Type} {f : X → Y} (inj : is_injective f) : 
  ∀ ⦃x₁ x₂⦄, (x₁ ≠ x₂)  → (f x₁ ≠ f x₂) := 
begin
  sorry, 
end 







/-! ## Question 3 (20 points): 

We Define a predicate which states whether a function of the form `ℤ × ℤ → ℤ` is symmetric. Recall that a function `f : ℤ × ℤ → ℤ` is said to be __symmetric__ if swapping the coordinates does not change the value of the function, i.e `f (x , y) = f(y , x)` for all integers `x` and `y`. 
-/

def is_symm_fun (f : ℤ × ℤ → ℤ) := ∀ x y : ℤ, f (x , y) = f (y , x)

#check is_symm_fun


/-
**Part I**: Consider the functions `shift_fun` and `diff_fun_zero` defined in below. The function `cross_effect` is constructed from these functions. Lemma `cross_effect_defn` in below describes the effect of fucntion `cross_effect` on each pair `(x,y) : ℤ × ℤ`. 
-/

def shift_fun (x : ℤ) (f : ℤ → ℤ) := 
λ y : ℤ, f (x + y)

#check shift_fun 


def diff_fun_zero (f : ℤ → ℤ) (y : ℤ) := 
f y - f 0 


#check diff_fun_zero

def cross_effect (f : ℤ → ℤ) (p : ℤ × ℤ) := (diff_fun_zero (shift_fun p.1 f) p.2) - (diff_fun_zero f p.2)


#eval cross_effect (λ x, x^2) (2, 3)



lemma cross_effect_defn {x y : ℤ} {f : ℤ → ℤ} :
cross_effect f (x,y) = f (x + y) - f (x) - f (y) + f(0) := 
begin 
  sorry,   
end 

/-
**Part II**: Show that for any function `f : ℤ × ℤ → ℤ`, the cross-effect of `f` is symmetric by completing the following proof. You can use the lemma `cross_effect_defn`.  
-/

theorem is_symm_cross_effect : 
  ∀ f : ℤ → ℤ, is_symm_fun (cross_effect f) := 
begin
  sorry, 
end   






/- ## Question 4 (20 points): -/

#check bool_of_nat 
-- This function was defined in `lec3_function` as follows: 
-- def bool_of_nat (n : ℕ) := if n = 0 then ff else tt



lemma not_inj_bool_of_nat : 
  ¬ is_injective (bool_of_nat) := 
begin
  sorry,
end    







/- ## Question 5 (30 points): 

**Part I**:
Prove that for every function `f : X → Y` and `g : Y → Z`, if the composition `g ∘ f : X → Z` is injective then `f` is injective.  
-/

lemma inj_right_of_inj_comp_alt (f : X → Y) (g : Y → Z) (h : is_injective (g ∘ f)) :
  is_injective f := 
begin
  sorry, 
end 



/- **Part II**-/

lemma id_of_bool_nat_comp_nat_bool : 
  bool_of_nat ∘ nat_of_bool = id := 
begin
  sorry, 
end  



/- **Part III**: 
Use lemma `id_of_bool_nat_comp_nat_bool` and `not_inj_bool_of_nat` to prove the following statement. 
-/

example : 
∃ X Y Z : Type, ∃ f : X → Y, ∃ g : Y → Z,  is_injective (g ∘ f) ∧  ¬ is_injective g := 
begin
  sorry, 
end 


end PROOFS