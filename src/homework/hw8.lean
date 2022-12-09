/-
Homeowork 8
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/


import ..prooflab
import lectures.lec11_type_classes


/-! # Homework 8: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far.
-/


variables {X Y : Type} {f : X → Y} {p : Y → X}{x : X}


open PROOFS
open PROOFS.STR
open PROOFS.type_classes



local notation `𝟙∘` := unit -- type as \b1\o
local notation `⋆` := unit.star

#check unit.star
#check @unit.ext

lemma unit_unique (x : 𝟙∘) :
   x = ⋆ :=
begin
  exact unit.ext,
end


/-
A map is __constant__ if it maps all points in the domain to the same point in the codomain.
-/
def is_constant (f : X → Y) := ∀ x x' : X, f x = f x'

/-
A map `f : X → Y` is __constant at a point__ `y` of `Y` if `f` maps all points in `X` to `y`.
-/
def is_constant_at (f : X → Y) (y : Y) := ∀ x : X, f x = y

#check @is_constant_at

/-! ## Question 1 (20 pts):
Show that if a function is constant at a point then it is constant.
-/
lemma constant_at_point_implies_constant {f : X → Y} :
   (∃ y : Y,  is_constant_at f y)  → is_constant f :=
begin
  intro h, -- we want to prove `(∃ (y : Y), is_constant_at f y) → is_constant f`, so we use the intro rule of implication
  unfold is_constant, -- we want to make the goal more clear, so we can unfold `is_constant`
  intros x x₁, -- we want to prove `∀ (x x' : X), f x = f x'`, so we use the intro rule of ∀ twice
  cases h with y h₁, -- we want to prove `∃ (y : Y), is_constant_at f y`, so we can use the elim rule of ∃ to make two more assumptions which we will call y and h₁
  unfold is_constant_at at h₁, -- we want to make h₁ clearer so we can unfold `is_constant_at`
  have h₂: f x = y, from h₁ x, -- we want to prove that f x = y because we can supply an x to h₁ so we can eventually rw it in the goal so we can prove that y = y
  have h₃: f x₁ = y, from h₁ x₁, -- we want to prove that f x₁ = y because we can supply an x to h₁ so we can eventually rw it in the goal so we can prove y = y
  rw h₂, -- we want to rw the goal to make it look like y = y
  rw h₃, -- we want to rw the goal to make it look like y = y and it is proven with refl embedded in rw tactic
end







/-! ## Question 2 (20 pts):
Prove that a function which factors through a type which is equivalent to the one-point type is constant.

Feel free to use the lemma `ptwise.left_inv`
-/

namespace ptwise
lemma left_inv {g : Y → X} {f : X → Y} (h : g ∘ f = id) :
  ∀ x : X, g (f x) = x :=
begin
  intro x, 
  apply congr_fun h, 
end 
end ptwise 

#check @ptwise.left_inv

--@[ext]
--structure fun_equiv (X : Type) (Y : Type) :=
--(to_fun    : X → Y)
--(inv_fun   : Y → X)
--(left_inv  : inv_fun ∘ to_fun = id) -- i.e. inv_fun ∘ to_fun = id_X
--(right_inv : to_fun ∘ inv_fun = id) -- i.e. to_fun ∘ inv_fun = id_Y


#check fun_fact
#check @unit
#check 𝟙∘
#check @unit.star
#check @fun_equiv 𝟙∘
#check @fun_equiv.inv_fun X Y
#check f (x : X)


/-
structure fun_fact {X Y : Type} (f : X → Y) :=
(node : Type) -- the node through which `f` factors
(left_fun : X → node) -- the left factor
(right_fun : node → Y) -- the right factor
-/

#print fun_fact
#check @fun_fact.node
#check @fun_fact.left_fun
#check @fun_fact.right_fun

#check @congr_arg

theorem constant_of_factor_unit  {f : X → Y} {b : fun_fact f} {p : fun_equiv b.node 𝟙∘} :
   is_constant f :=
begin
  intros x x₁,
  have pt, from p.to_fun,
  have pi, from p.inv_fun,
  have bl, from b.left_fun,
  have br, from b.right_fun,
  have hx: f = (b.right_fun ∘ ((p.inv_fun ∘ p.to_fun) ∘ b.left_fun))  , by { rw p.left_inv, simp,  rw b.fun_eq,}, -- we want to to give f in terms of b and p, which we can by saying that X → b.node to b.node → 𝟙∘ to 𝟙∘ → b.node to b.node → Y. This will allow us to to evetually give a vairable x that inside the function will always give you the same y. We proved it by rw p.left_inv, which says that p.inv_fun ∘ p.to_fun = id, simp, which makes the new goal f = b.right_fun ∘ b.left_fun, and rw b.fun_eq, which says that b.right_fun ∘ b.left_fun = f. Refl is used.
  have hxx: f x = (b.right_fun ∘ ((p.inv_fun ∘ p.to_fun) ∘ b.left_fun)) x , by {rw ← hx,}, -- we can prove f x to soon rewrite that into the goal with hx, which says that f = (b.right_fun ∘ ((p.inv_fun ∘ p.to_fun) ∘ b.left_fun))
  simp at hxx, -- we want to simplify hxx to show the input that the constant function, p.to_fun, takes, so that we can supply it later to show that no matter what x we give it, it will output ⋆
  have tf: p.to_fun (b.left_fun x) = ⋆, by ring, -- we are proving that nomatter what x : X, it will always be equal to ⋆ because p.to_fun = b.node → 𝟙∘ and 𝟙∘ = ⋆
  rw tf at hxx, -- we can rewrite tf, which says that it will always be ⋆ into hxx to show that hxx will be the same y : Y because the inside function will always be ⋆
  rw hxx, -- we can rewrite into the goal so we can then prove the other side the exact same way but with x₁ and both sides will be equal by refl
  have hxv: f x₁ = (b.right_fun ∘ ((p.inv_fun ∘ p.to_fun) ∘ b.left_fun)) x₁ , by {rw ← hx,},
  simp at hxv,
  have tg: p.to_fun (b.left_fun x₁) = ⋆, by ring, -- same process
  rw tg at hxv, -- same process
  rw hxv, -- when you rw hxv, both sides are equal by refl
end





/- For every type `X` there is a unique function
from `X` to `𝟙` which takes all points of `X` to `⋆`.
-/
@[simp]
def to_terminal (X : Type) : X → 𝟙∘  := λ x, ⋆

notation ` ! ` := to_terminal
infix ` ≅∘ `:35 := fun_equiv


@[simp]
def is_surjective {X Y : Type} (f : X → Y) :=
∀ y : Y, ∃ x : X, f x = y

/-! ## Question 3 (20 pts):
Prove that the unique function `X → 𝟙∘` is surjective iff `X` is pointed by filling the `sorry` placeholder.
-/

/-
structure pointed_type :=
(type : Type)
(point : type)
-/

#check to_terminal

def is_surj_of_pointed_type {X : pointed_type} :
  is_surjective (! X.type) :=
begin
   unfold is_surjective, -- we want to make the goal more clear, so we can unfold `is_surjective`
   intro y, -- we want to prove `∀ (y : 𝟙∘), ∃ (x : X.type), ! X.type x = y`, so we can use the intro rule of ∀ to make an assumption y : 𝟙∘ and the new goal `∃ (x : X.type), ! X.type x = y`
   have x₁, from X.point, -- in order to use the introduction rule for ∃, we need to have some `X.type` to `use`, which we can get from `X`, which is a `pointed_type` and contains a type and point. We can get the type by using dot notation, `X.point`
   use x₁, -- we want to prove `∃ (x : X.type), ! X.type x = y`, so we can use the introduction rule of ∃ and the x₁ that we made an assumption for earlier
   simp, -- we have the goal `! X.type x₁ = y`, and we know that `!` is `Π (X : Type), X → 𝟙∘`. ! takes a Type, which is supplied by `X.type`. and makes it `X.type → 𝟙∘`. This new function takes an `X.type`, which is supplied by `x₁`, and converts it to `𝟙∘`. This is equivalent to the type of `y`, which is of type `𝟙∘`. Equivalent.
end



/-
**Formalize the converse**, that is if `! X : X → 𝟙∘` is surjective then `X` is pointed (i.e. it admits the structure of a pointed type). Then **prove** the converse statement.
-/

--I'm not sure how to do this
--Uses axiom of choice
#check classical.some

noncomputable
def is_pointed_of_surj {X : Type} {h : is_surjective (! X)} : pointed_type :=
{
   type := X,
   point := let h' : (∃ x : X, true) := by {unfold is_surjective at h,
      simp at *, assumption} in classical.some h' ,
}





/-! ## Question 4 (20 pts):
Prove that the image of the unique function `X → 𝟙∘` is equivalent to to `𝟙∘` if `X` is pointed.

Feel free to use the lemma `ptwise.left_inv`
-/

--infix ` ≅∘ `:35 := fun_equiv

/-
structure fun_equiv (X : Type) (Y : Type) :=
(to_fun    : X → Y)
(inv_fun   : Y → X)
(left_inv  : inv_fun ∘ to_fun = id) -- i.e. inv_fun ∘ to_fun = id_X
(right_inv : to_fun ∘ inv_fun = id) -- i.e. to_fun ∘ inv_fun = id_Y
-/

--def fun_image (f : X → Y) : Type := { y : Y // ∃ x : X, y = f x}

/-
structure pointed_type :=
(type : Type)
(point : type)
-/


#check @fun_image

def truncation_of_pointed_type {X : pointed_type} :
  𝟙∘   ≅∘  (fun_image (! X.type)) :=
{
  to_fun := λ x, ⟨ ! X.type X.point , by { use X.point, } ⟩, -- because to_fun is a function from X: 𝟙∘ to Y: (fun_image (! X.type)), we need to introduce a value, x, that has the type 𝟙∘, which we do by λ x. We then supply ! X.type X.point because ! X.type : X.type → 𝟙∘ and supplied with X.point, which has type X.type making this 𝟙∘. We prove that ∃ (x : X.type), ! X.type X.point = ! X.type x by using the introduction rule of ∃, use X.point, which has the type X.type, and is the same by refl
  inv_fun := λ y, ⋆, -- for any input y, we get the same output ⋆ because the input is 𝟙∘, which only contains ⋆
  left_inv := by {simp,}, -- we can prove ((λ (y : fun_image (! X.type)), ⋆) ∘ λ (x : 𝟙∘), ⟨! X.type X.point, _⟩) = id with simp
  right_inv := by {
                    ext,
                  },
}

def truncation_of_pointed_type_alt {X : pointed_type} :
  𝟙∘   ≅∘  (fun_image (! X.type)) :=
{
  to_fun := λ x, fun_image.cover(! X.type) X.point,
  inv_fun := λ x, ⋆,
  left_inv := by ext,
  right_inv := by ext,
}



/-
We say a type is __inhabited__ if there is some element in it.
-/

@[simp]
def is_inhabited (X : Type) :=  ∃ x : X, true

#check @is_inhabited

/-
The __fibre at a point__ `x : X` of a function  `p : Y → X` is the preimage of `x` under `p`.
-/
@[simp]
def fibre_at (x : X) := { y : Y // p y = x}

#check @fibre_at


local notation ` p⁻¹ ` : 15 := λ x, @fibre_at X Y p x
#check p⁻¹



/-!  ## Question 5 (20 pts):
Let `p : Y → X` be a function. Prove that if all the fibres of `p` are inhabited then `p` is surjective.
-/


def surj_of_pointed_fibres {ptd_fibres : ∀ x : X, is_inhabited (p⁻¹ x) } : is_surjective p :=
begin
  unfold is_inhabited at *, -- we want to make the goal more clear, so we can unfold `is_inhabited`
  unfold is_surjective, -- we want to make the goal more clear so we can unfold `is_surjective`
  intro x₁, -- we want to prove `∀ (y : X), ∃ (x : Y), p x = y`, so we can use the introduction rule of ∀ to make a new assumption x₁ : X and the new goal `∃ (x : Y), p x = y`
  have h₁, from ptd_fibres x₁, -- we can supply a variable of type `X` to `ptd_fibres` so we can get something close to the goal that we can prove. We can have an assumption `h₁` from `ptd_fibres`, which is `∀ (x : X), ∃ (x : fibre_at x), true`, and supply it `x₁` which is of type `X`, to make `h₁ : ∃ (x : fibre_at x₁), true` and this looks very similar to the goal
  cases h₁ with h t, -- we want to split `h₁` into assumptions we can use, so we can use the elimination rule of `∃` to make `h : fibre_at x₁` and `t : true`
  unfold fibre_at at h, -- we want to make h more clear so we can unfold `fibre_at`
  cases h with y hy, -- `h` consists of pairs of `y : Y` and a proof that the `p y = x₁`, so we can split that into individual assumption using cases.
  use y, -- we now have something of type `Y` that we can use the introduction rule of `∃` to make the goal `p y = x₁`
  exact hy, -- we can prove the exact goal using the assumption we created with `cases h`, `hy`
end
/- 
Homeowork 8  
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec11_type_classes


/-! # Homework 8: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far. 
-/


variables {X Y : Type} {f : X → Y} {p : Y → X}


open PROOFS 
open PROOFS.STR 
open PROOFS.type_classes



local notation `𝟙` := unit -- type as \b1
local notation `⋆` := unit.star



lemma unit_unique (x : 𝟙) : 
   x = ⋆ := 
begin
  exact unit.ext,
end 


/- 
A map is __constant__ if it maps all points in the domain to the same point in the codomain.
-/
def is_constant (f : X → Y) := ∀ x x' : X, f x = f x' 

/- 
A map `f : X → Y` is __constant at a point__ `y` of `Y` if `f` maps all points in `X` to `y`. 
-/
def is_constant_at (f : X → Y) (y : Y) := ∀ x : X, f x = y

/-! ## Question 1 (20 pts):
Show that if a function is constant at a point then it is constant. 
-/
lemma constant_at_point_implies_constant {f : X → Y} :  
   (∃ y : Y,  is_constant_at f y)  → is_constant f := 
begin
  sorry, 
end  







/-! ## Question 2 (20 pts):
Prove that a function which factors through a type which is equivalent to the one-point type is constant. 

Feel free to use the lemma `ptwise.left_inv`
-/

#check @ptwise.left_inv

theorem constant_of_factor_unit  {f : X → Y} {Φ : fun_fact f} {α : fun_equiv Φ.node 𝟙} :  
   is_constant f :=
begin
   unfold is_constant, 
end 










/- For every type `X` there is a unique function 
from `X` to `𝟙` which takes all points of `X` to `⋆`. 
-/
@[simp]
def to_terminal (X : Type) : X → 𝟙 := λ x, ⋆

notation ` ! ` := to_terminal
infix ` ≅ `:35 := fun_equiv


/-! ## Question 3 (20 pts):
Prove that the unique function `X → 𝟙` is surjective iff `X` is pointed by filling the `sorry` placeholder. 
-/ 

def is_surj_of_pointed_type {X : pointed_type} : 
  is_surjective (! X.type) :=  
begin
   sorry, 
end 



/-
**Formalize the converse**, that is if `! X : X → 𝟙` is surjective then `X` is pointed (i.e. it admits the structure of a pointed type). Then **prove** the converse statement. 
-/




#check classical.some
noncomputable
def is_pointed_of_surj {X : Type} {h : is_surjective (! X)} : pointed_type :=
{
   type := X,
   point := let h' : (∃ x : X, true) := by {unfold is_surjective at h,
      simp at *, assumption} in classical.some h' , 
}








/-! ## Question 4 (20 pts):
Prove that the image of the unique function `X → 𝟙` is equivalent to to `𝟙` if `X` is pointed. 

Feel free to use the lemma `ptwise.left_inv`
-/

def truncation_of_pointed_type {X : pointed_type} : 
  𝟙  ≅ (fun_image (! X.type)) := 
{
  to_fun := sorry,
  inv_fun := sorry, 
  left_inv := by {sorry},
  right_inv := by {sorry},
}  





/- 
We say a type is __inhabited__ if there is some element in it. 
-/ 

@[simp]
def is_inhabited (X : Type) :=  ∃ x : X, true



/-
The __fibre at a point__ `x : X` of a function  `p : Y → X` is the preimage of `x` under `p`. 
-/
@[simp]
def fibre_at (x : X) := { y : Y // p y = x}

#check @fibre_at


local notation ` p⁻¹ ` : 15 := λ x, @fibre_at X Y p x
#check p⁻¹



/-!  ## Question 5 (20 pts): 
Let `p : Y → X` be a function. Prove that if all the fibres of `p` are inhabited then `p` is surjective.  
-/


def surj_of_pointed_fibres {ptd_fibres : ∀ x : X, is_inhabited (p⁻¹ x) } : is_surjective p := 
begin
   sorry,  
end 










