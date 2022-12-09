/-
Homeowork 9
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec11_type_classes
import lectures.lec12_gaussian_integers



open PROOFS
open PROOFS.STR


variables {X Y : Type} {P : X → Prop}



/- The first question is about __unique existence__. For instance, we know not only that there exists a natural `n` such that `n` is even and prime, but such a number is unique.  -/

-- ∃! is the symbol for unique existence.

#check exists_unique


lemma uniquely_exists₁  :
  (∃! x, P x) ↔ (∃ x, P x ∧ (∀ y : X, P y → y = x)) :=
begin
  rw exists_unique,
end


/-! ## Question 1 (20 pts):
Give a proof of the following lemma.
-/

lemma uniquely_exists₂  :
  (∃! x, P x) ↔ (∃ x, P x) ∧ (∀ y z : X, P y ∧ P z → y = z) :=
begin
  split,
  {
    unfold exists_unique,
    intro h₁,
    split,
    {
      cases h₁ with x hx,
      cases hx with px hy,
      use x,
      assumption,
    },
    {
      intros y z h₂,
      cases h₁ with x hx,
      cases hx with h₃ h₄,
      cases h₂ with h₅ h₆,
      rw h₄ y h₅,
      rw h₄ z h₆,
    },
  },
  {
    intro h₁,
    unfold exists_unique,
    cases h₁ with h₂ h₃,
    cases h₂ with x hx,
    use x,
    split,
    {
      assumption,
    },
    {
      intros y hy,
      apply h₃,
      exact ⟨hy, hx⟩, 
    }
  },
end






/- Questions 2 and 3 concern the notion of quasigroup.  In below we define __quasigroup__ structures. A quasigroup structure consists of one binary operation `op` operations and left and right divisions (with respect `op` ).
-/

class quasi_group_str (Q : Type) :=
(op : Q → Q → Q) -- a binary operation `op` on `Q`
(left_div : Q → Q → Q)
(right_div : Q → Q → Q)
(l := left_div) -- temporary notation, just inside this structure declaration
(r := right_div) -- temporary notation, just inside this structure declaration
(op_of_left_div : ∀ x y : Q, op x  (l x y) = y) -- finding column
(left_div_of_op : ∀ x y : Q, l x (op x y) = y) -- unique column
(op_of_right_div : ∀ x y : Q, op (r y x)  x = y)
(right_div_of_op : ∀ x y : Q, r (op y  x) x  = y)



local infix `#` :15 := quasi_group_str.op
local infix ` \\ ` :15 := quasi_group_str.left_div -- `l x y` is `x \\ y`
local infixl ` // ` :15 := quasi_group_str.right_div -- `r x y` is `y // x`


/-! ## Question 2 (20 pts):
Show that The integers ℤ with subtraction form a quasigroup.
-/
instance : quasi_group_str ℤ :=
{
  op := λ x, λ y, x - y,
  left_div := λ y, λ x, y - x, -- we know it's `y - x` because `x - (x - y) = y`
  right_div := λ y, λ x, y + x, -- we know it's `y + x` becuase y + x - x = y and y - x + x = y
  --these make x - y a quasi group because there is an operation of the left and right divisions with respect to op
  op_of_left_div := by{intros x y, ring,}, -- have to show that `x - (x - y) = y`, we can prove `∀ (x y : ℤ), x - (x - y) = y` with introduction rule of ∀ and ring, which proves `x - (x - y) = y`, we know this is true through basic math.
  left_div_of_op := by{intros x y, ring,}, -- we want to prove `∀ (x y : ℤ), x - (x - y) = y`, we can use introduction rule of ∀ and ring, which proves `x - (x - y) = y`, we know this is true by basic math.
  op_of_right_div := by{intros x y, ring,}, -- we want to prove `∀ (x y : ℤ), y + x - x = y`, we use introduction rule of ∀ and ring, which proves `y + x - x = y`, which is true by sub_self x.
  right_div_of_op := by{intros x y, ring,}, -- we want to prove `∀ (x y : ℤ), y - x + x = y`, we can use introduction rule of ∀ and ring, which proves `y - x + x = y` by sub_self x.
}






/-! ## Question 3 (20 pts)
**(Part I)** :
 Prove the following simplification lemmas directly from the definitions above.
-/

@[simp]
lemma mul_of_left_div_def {Q : Type} [quasi_group_str Q] (a b : Q) :
  (a # (a \\ b)) = b :=
begin
  sorry,
end


@[simp]
lemma left_div_of_mul_def {Q : Type} [quasi_group_str Q] (a b : Q) :
  (a \\ (a # b)) = b :=
begin
  sorry,
end


lemma mul_of_right_div_def {Q : Type} [quasi_group_str Q] (a b : Q) :
  ((b // a) # a) = b :=
begin
  sorry,
end


lemma right_div_of_mul_def {Q : Type} [quasi_group_str Q] (a b : Q) :
  ((b # a) // a) = b :=
begin
  sorry,
end



/-
## Question 3 (Part II):
 Prove the Latin square property of quasigroups. A __Latin square__ is an array filled with different symbols, each occurring exactly once in each row and exactly once in each column.
An example of a `3×3` Latin square with symbols `A B C` is

                      A B   C
                      C A   B
                      B C   A

Hint : Q1 should help you here.
-/

theorem Latin_square_property {Q : Type} [quasi_group_str Q] :
  ∀ a b : Q, (∃! x : Q, (a # x) = b) ∧ (∃! y : Q, (y # a) = b) :=
begin
  sorry,
end







/- The notion of __monoid__ strucutre (`mult_monoid_str` and `additive_monoid_str`) was defined in lecture 12. -/

@[ext]
structure positive_nat :=
(num : ℕ)
(pos : 0 < num)

local notation ` ℕ₊ `: 15 := positive_nat

/- Fill in `sorry` placeholder in below.-/
instance : has_one ℕ₊ :=
{ one := ⟨1, by{ linarith,} ⟩ ,}

#reduce has_one


@[simp]
lemma pos_nat_one_val : (1 : ℕ₊).num = 1 :=
begin
  refl,
end


/- Fill in `sorry` placeholder in below.-/
instance : has_mul ℕ₊ := 
{ mul := λ x, λ y, ⟨x.num * y.num, by{have h₁, from x.pos, have h₂, from y.pos, simp, split,repeat{assumption}}⟩ }


@[simp]
lemma pos_nat_mul_pos_nat {x y : ℕ₊} : (x * y).num = x.num * y.num :=
begin
  refl,
end


/-! ## Question 4 (20 pts):
Show that the positive natural numbers admit a multiplicative monoid structure by filling in the `sorry` placeholders in below. You should use the instances of type classes `has_one ℕ₊` and `has_mul ℕ₊` in above. Feel free to prove your own simplification lemmas if needed.
-/

instance : mult_monoid_str ℕ₊ :=
{ 
  mul := has_mul.mul, -- we already have an instance of this embedded in the mult_monoid_str, which is mul inside has_mul
  mul_assoc := by
  {
    intros a b c, -- introduction rule of ∀
    ext, -- extenstionality that we have in the structure ℕ₊, makes the goal `(a * b * c).num = (a * (b * c)).num`
    simp, -- `pos_nat_mul_pos_nat` lemma that I made and attached simp to simplifies the goal so that each variable has extension .num. the new goal is `a.num * b.num * c.num = a.num * (b.num * c.num)`
    rw ← mul_assoc, -- because all the "variables" are now natural numbers, we can use mul_assoc for natural numbers to prove it
  },
  one := ⟨1, by{ linarith,} ⟩, -- we need to prove that there is a one inside this structure and we can prove that it's postive because we know 0 < 1 by contradiction
  mul_one := by
  {
    intro a, -- we use introduction rule of ∀ to make the goal `a * 1 = a`
    ext, -- we know that `a` and `1` is of type ℕ₊, so we have to use extenstionality so that we can use it in terms of natural numbers
    simp, -- we use `pos_nat_mul_pos_nat` to prove that `(a * 1).num = a.num` is `a.num * 1.num = a.num`, Lean knows that a natural number multiplied by `1.num : ℕ` is that number, which is why the goal is accomplished
  }, 
  one_mul := by
  {
    intro a, -- we use introduction rule of ∀ to make the goal `1 * a = a`
    ext, -- we know that `1` and `a` is of type ℕ₊, so we have to use extenstionality so that we can use it in terms of natural numbers
    simp, -- we use `pos_nat_mul_pos_nat` to prove that `(1 * a).num = a.num` is `1.num * a.num = a.num`, Lean knows that a natural number multiplied by `1.num : ℕ` is that number, which is why the goal is accomplished
  },
}






/-!  In below we define the __group__ structure. A group structure on a type `X` consists of a binary operation (e.g. multiplication, addition) and a unary operation of taking __inverse__.
-/

class additive_group_str (X : Type) extends additive_monoid_str X :=
(inv : X → X)
(left_inv : ∀ x : X,  (inv x) + x =  0)
(right_inv : ∀ x : X,  x + (inv x) = 0)



class mult_group_str (X : Type) extends mult_monoid_str X :=
(inv : X → X)
(left_inv : ∀ x : X,  (inv x) * x =  1)
(right_inv : ∀ x : X,  x * (inv x) = 1)

-- our notation for inverse of an element.
postfix `ⁱ` :std.prec.max_plus := mult_group_str.inv


section
variables (G : Type) [mult_group_str G] (x : G)
#check x
#check xⁱ
end




/-! ## Question 5 (20 pts) :
Show that the Gaussian integers with the opeation of addition form an additive group. -/


instance : additive_group_str ℤ[i] :=
sorry







/-
In below we define the notion of __monoid morphism__. A monoid morphism between monoids `M` and `N` is given by a function `f : M → N` which preserves the multiplication operation.
-/

class mult_monoid.morphism (M : Type) (N : Type) [mult_monoid_str M] [mult_monoid_str N] :=
(to_fun : M → N)
(resp_one : to_fun 1 = 1)
(resp_mul : ∀ x y : M, to_fun (x * y) = to_fun x * to_fun y)


infixr ` →ₘ* `:25 := mult_monoid.morphism



/-! ## Question 6 (20 pts):
Show that the function from ℕ₊ → ℤ[i] which maps `n` to `n + 0i` is a multiplicative monoid morphism.
-/

instance : ℕ₊ →ₘ* ℤ[i] := 
{ 
  to_fun := λ x, ⟨x.num, 0 ⟩, -- given an x : ℕ₊, we need a gaussian integer, which has ⟨re, im⟩. re needs to be an integer, which is supplied from x.num : ℕ and im needs to be zero so that x = x + i0
  resp_one := rfl, -- the re of ℤ[i], which is ⟨1, 0⟩.re = 1 is equal to 1 by reflexivity
  resp_mul := by
  {
    intros x y, -- use introduction rule of ∀ to make the new goal `{re := ↑((x * y).num), im := 0} = {re := ↑(x.num), im := 0} * {re := ↑(y.num), im := 0}`
    simp, -- simp uses the lemma `pos_nat_mul_pos_nat`, which makes the goal `{re := ↑(x.num) * ↑(y.num), im := 0} = {re := ↑(x.num), im := 0} * {re := ↑(y.num), im := 0}`
    rw gaussian_int.mul_def, -- `mul_def` is how we multiplied gaussian integers, this rewrites the right side of the equation in terms of that theorem
    simp, 
    /- 
    {re := ↑(x.num) * ↑(y.num), im := 0} = 
     {
     re := __this is the real part of the multiplication of ℤ[i]__
     {re := ↑(x.num), im := 0}.re 
     * 
     {re := ↑(y.num), im := 0}.re 
     - 
     {re := ↑(x.num), im := 0}.im 
     * 
     {re := ↑(y.num), im := 0}.im
     ,
    im := __this is the imaginary part of the multiplication of ℤ[i]__
     {re := ↑(x.num), im := 0}.re 
     *
     {re := ↑(y.num), im := 0}.im 
     + {re := ↑(x.num), im := 0}.im 
     *
     {re := ↑(y.num), im := 0}.re
     }
    -/
    -- using the lemmas we created in `lec12`, we can simplify this statment so that x.num * y.num = x.num * y.num
  },
}








/-! ## Question 7 (20 pts):
Show that for a type `X` the automorphisms of `X` admits a group strucuture where the multiplication operation is given by the composition of functions. You might like to use some stuff we proved about `auto` in Lecture on unbundled strucutres. -/

def group_of_auto : mult_group_str (auto X) :=
sorry







#check monoid_hom
#check @monoid_hom X


/-! ## Question 8 (20 pts):
Show that the endomorphisms of any type form a monoid with composition of functions as monoid multiplication.
-/ 

#check @has_zero X

instance monoid_of_endo : mult_monoid_str (endo X) :=
{ 
  mul := λ x, λ y, x ∘ y, -- an endomorphism is a function from type → type. So endo X is the same as a function from X → X. mul takes two inputs of the same type and outputs the same type. So we introduce `x : endo X` and `x : endo X`, and outputs the same type `x : endo X`
  mul_assoc := by
  {
    intros a b c, -- we use the introduction rule of ∀ to make the new goal `a * b * c = a * (b * c)`
    refl, -- because a b c : endo X, the output of the left side of the equality is endo X and the right side is the same output endo X, which is the same by reflexivity. The parenthesis do not matter because they're all of the same type
  },
  one := id, -- nomatter what input is given, it will output the same type. Given an input of 1 : ℕ, it will output 1 : ℕ. `1 : endo m_1`
  mul_one := by
  {
    intro a, -- use introduction rule of ∀ to make the new goal `a * 1 = a`
    ext, -- use function extensionality with variable x to make the new goal `(a * 1) x = a x`
    simp, -- I think simp writes the goal as a(1(x)) = a(x), and it simplifies the left side to just be a(x) = a(x), which is true by reflexivity
  },
  one_mul := by
  {
    intro a, -- we use the introduction rule of ∀, makes the goal `1 * a = a` 
    ext, -- extensionality with variable x makes the goal `(1 * a) x = a x`
    refl, -- the goal can be written as `1(a(x)) = a(x)`, which is the same by refl because one is just `id`
  },
}




/-! ## Question 9 (20 pts):
**Part I :** Prove the following lemma.
-/
lemma inv_cancel_left {G : Type} [mult_group_str G] :
  ∀ a b : G, (aⁱ) * (a * b) = b :=
begin
  sorry,
end


/-
**Part II :** Use the previous lemma to prove the following cancellation property of multiplication for groups.
-/

lemma mul_left_cancel_group {G : Type} [mult_group_str G] :
  ∀ a b c : G, (a * b = a * c) → b = c :=
begin
  sorry,
end





/-
In below we define the __action__ of a monoid on a type.
-/

class mult_monoid_left_action (M A : Type) [mult_monoid_str M] :=
(smul : M → A → A) -- the scalar multiplication of `M` on `A`.
(one_smul : ∀ (x : A), smul (1 : M) x = x)
(mul_smul : ∀ (r s : M) (x : A), smul (r * s) x = smul r (smul s x))

#check @one_smul
/- ## Question 10 (20 pts):
Given a monoid `M` and an action of `M` on a type `A` construct a monoid morphism from `M` to `endo A`.
-/


def monoid_morphism_of_monoid_action  (M A : Type) [mult_monoid_str M] [mult_monoid_left_action M A] :
M →ₘ* (endo A) :=
{ 
  to_fun := mult_monoid_left_action.smul, -- `_inst_2 : mult_monoid_action M A` and to_fun needs a function from M → endo A and endo A : A → A so to_fun actually needs M → A → A, which is exactly that of smul of _inst_2
  resp_one := by
  {
    funext x, -- we want to use function extensionality to supply variable x : A, this makes the new goal `mult_monoid_action.smul 1 x = 1 x`
    rw mult_monoid_left_action.one_smul, -- the left side of the equality of the goal is  _inst_2.one_smul, `∀ (x : A), smul (1 : M) x = x`, and rewriting that would make the new goal `x = 1 x`
    refl, -- 1(x) is the same as x because of has_one, which is why reflexivity works
  },
  resp_mul := by
  {
    intros x y, -- we use the introduction rule of ∀ to make the new goal `mult_monoid_action.smul (x * y) = mult_monoid_action.smul x * mult_monoid_action.smul y`
    ext z, -- we want to use function extensionality so that we can eventually rw with our instances
    rw mult_monoid_left_action.mul_smul,
    refl, -- we can rewrite with _inst_2.mul_smul becuase the left side of the equality is `mult_monoid_action.smul (x * y) z`, which is the same as mul_smul in instance 2, which states `∀ (r s : M) (x : A), smul (r * s) x = smul r (smul s x)`
    -- the knew goal is `mult_monoid_action.smul x (mult_monoid_action.smul y z) = (mult_monoid_action.smul x * mult_monoid_action.smul y) z`
    -- we know that `mult_monoid_action.smul y z` is `something : A` and `mult_monoid_action.smul x something` is `something_1 : A` so the left side of the equation is a variable w/ type A
    -- we know that `mult_monoid_action.smul x : A → A` and `mult_monoid_action.smul y : A → A`. based off what we know before, these are endomorphisms, and when multiplied, give you an output of an endomorphism, which in this case would be A → A. when supplied z : A, the right side of the equation is also a variable w/ type A.
    -- reflexivity of equation is true because of this
  }, 
}





