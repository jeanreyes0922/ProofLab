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

def bool_of_nat (n : ℕ) := 
if n = 0 then ff else tt

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