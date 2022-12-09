/-
Homeowork 10
Sina Hazratpour
Introduction to Proof
MATH 301, Johns Hopkins University, Fall 2022
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec11_type_classes
import lectures.lec12_gaussian_integers
import lectures.lec13_structures_on_gaussian_int



open PROOFS
open PROOFS.STR




variables {L M N : Type} [mult_monoid_str L] [mult_monoid_str M] [mult_monoid_str N]



/-! ## Question 1 (20 pts)
First, show that monoid morphisms are closed under composition, i.e. the composition of two monoid morphisms is again a monoid morphism.

Then, show that for any monoid `M`, the type of monoid endomorphism `M →ₘ* M` itself admits a monoid structure. Note that the latter is very different than the type of endofunctions `M → M`. we showed before that whereas there is only one constant endomorphism `ℤ →ₘ* ℤ` there are ℤ-mnay endofunctions `ℤ → ℤ`.
-/

@[simp]
def mult_monoid.morphism.comp (g : M →ₘ* N) (f : L →ₘ* M)  : L →ₘ* N :=
{ 
  to_fun := g ∘ f,
  resp_one := by
                {
                  dsimp,
                  have h: f(1) = 1, from mult_monoid.morphism.resp_one,
                  rw h,
                  have h₁: g(1) = 1, from mult_monoid.morphism.resp_one,
                  rw h₁,
                },
  resp_mul := by
                {
                  simp,
                }, 
}


infixr  ` ∘* ` : 90  := mult_monoid.morphism.comp

def mult_monoid.morphism.id : M →ₘ* M :=
{
  to_fun := id,
  resp_one := by {simp},
  resp_mul := by {simp},
}

#check M →ₘ* M



instance : mult_monoid_str (M →ₘ* M) :=
{
  mul := (∘*),
  mul_assoc := by
                {
                  intros a b c,
                  ext,
                  refl,
                },
  one := mult_monoid.morphism.id,
  mul_one := by
                {
                  intro a,
                  ext,
                  refl,
                },
  one_mul := by
                {
                  intro a,
                  ext,
                  refl,
                },
}





/-! ## Question 2 (20 pts)
Construct the cartesian products of monoids, and show that the two projection are monoid morphisms .
-/

instance mult_monoid_str.product {M N : Type} [mult_monoid_str M] [mult_monoid_str  N] :
  mult_monoid_str (M × N) :=
{
  mul := λ x, λ y, ⟨x.1 * y.1, x.2 * y.2⟩,
  mul_assoc := by
                {
                  intros a b c,
                  ext,
                  {
                    simp,
                    rw _inst_4.mul_assoc,
                  },
                  {
                    simp,
                    rw _inst_5.mul_assoc,
                  },
                },
  one := (1,1),
  mul_one := by
              {
                intro a,
                ext,
                { 
                  simp,
                  rw _inst_4.mul_one,
                },
                {
                  simp,
                  rw _inst_5.mul_one,
                },
              },
  one_mul := by
                {
                  intro a,
                  ext,
                  {
                    simp,
                    rw _inst_4.one_mul,
                  },
                  {
                    simp,
                    rw _inst_5.one_mul,
                  },
                },
}


instance mon_fst : M × N →ₘ* M :=
{ 
  to_fun := λ x, x.1,
  resp_one := rfl,
  resp_mul := by
                {
                  intros x y,
                  simp,
                }, 
}

instance snd_fst : M × N →ₘ* N :=
{ 
  to_fun := λ x, x.2,
  resp_one := rfl,
  resp_mul := by
                {
                  intros x y,
                  simp,
                }, 
}





/-! ## Question 3 (20 pts)
Construct an equivalence of types of gaussian integers ℤ[i] and the cartesian product ℤ × ℤ.
-/
infix ` &≅ `:15 := fun_equiv

def gausssian_int_cartesian_product :
  ℤ[i] &≅ ℤ × ℤ :=
{ 
  to_fun := λ z, (z.re, z.im),
  inv_fun := λ z, ⟨z.1, z.2⟩,
  left_inv := by
                {
                  ext,
                  {
                    simp,
                  },
                  {
                    simp,
                  },
                },
  right_inv := by
                {
                  ext,
                  {
                    simp,
                  },
                  {
                    simp,
                  },
                },
  }


/- Is this equivalence a monoid isomorphism? If yes, prove it in below, if no, explain why it is not. -/


def gausssian_int_cartesian_product_monoid_isomorphism : ℤ[i] ≅ₘ* ℤ × ℤ :=
sorry






/-! ## Question 4 (20 pts)
Show that the type of functions `X → M` has a monoid structure if the codomain `M` has a monoid structure. The multiplication on `X → M` is given by pointwise multiplication, i.e. the multiplication of two functions
`f g : X → M` should be a function `f * g : X → M` where
`f * g (x) = (f x) * (g x)`.
-/

@[instance]
def mult_monoid_str.function (X M : Type)  [mult_monoid_str  M] :
  mult_monoid_str (X → M) :=
{
  mul := λ f, λ g, λ x, f(x)*g(x),
  mul_assoc := by
                {
                  intros a b c,
                  ext,
                  simp,
                  rw _inst_4.mul_assoc,
                },
  one := 1 * 1,
  mul_one := by
                {
                  intro a,
                  ext,
                  simp,
                  rw _inst_4.mul_one,
                  rw _inst_4.mul_one,
                },
  one_mul := by
                {
                  intro a,
                  ext,
                  simp,
                  rw _inst_4.one_mul,
                  rw _inst_4.one_mul,
                },
}







/-! ## Question 5 (20 pts)
Show that `Prop` admit multiplicative and additive monoid structures. -/

instance : comm_mult_monoid_str Prop :=
{
  mul := (∧),
  mul_assoc := by 
  {
    intros a b c,
    ext,
    split,
    {
      intro h,
      cases h with hab hc,
      cases hab with ha hb,
      split,
      {
        assumption,
      },
      {
        split,
        {
          assumption,
        },
        {
          assumption,
        },
      },
    },
    {
      intro h,
      cases h with ha hbc,
      cases hbc with hb hc,
      split,
      {
        split,
        {
          assumption,
        },
        {
          assumption,
        },
      },
      {
        assumption,
      },
    },
  },
  one := 1 * 1 = 1,
  mul_one := by
  {
    intro a,
    ext,
    split,
    {
      intro hao,
      cases hao with ha ho,
      assumption,
    },
    { 
      intro ha,
      split,
      {
        assumption,
      },
      {
        simp, -- why?
      },
    },
  },
  one_mul := by 
  {
    intro a,
    ext,
    split,
    {
      intro hoa,
      cases hoa with ho ha,
      assumption,
    },
    {
      intro ha,
      split,
      {
        simp,
      },
      {
        assumption,
      },
    },
  },
  mul_comm := by
  {
    intros x y,
    ext,
    split,
    {
      intro hxy,
      cases hxy with hx hy,
      split,
      {
        assumption,
      },
      {
        assumption,
      },
    },
    {
      intro hyx,
      cases hyx with hy hx,
      split,
      {
        assumption,
      },
      {
        assumption,
      },
    },
  },
}


instance or_additive : comm_additive_monoid_str Prop :=
{
  add := (∨),
  add_assoc := by
  {
    intros a b c,
    ext,
    split,
    {
      intro h₁,
      cases h₁,
      {
        cases h₁,
        {
          left,
          assumption,
        },
        { 
          right,
          left,
          assumption,
        },
      },
      {
        right,
        right,
        assumption,
      },
    },
    {
      intro h₁,
      cases h₁,
      {
        left,
        left,
        assumption,
      },
      {
        cases h₁,
        {
          left,
          right,
          assumption,
        },
        {
          right,
          assumption,
        },
      },
    },
  },
  zero := 0 = 1,
  add_zero := by 
  {
    intro a,
    ext,
    split,
    {
      intro h,
      cases h,
      {
        assumption,
      },
      {
        dsimp at h,
        exfalso,
        linarith,
      },
    },
    {
      intro h,
      left,
      assumption,
    },
  },
  zero_add := by
  {
    intro a,
    ext,
    split,
    {
      intro h,
      cases h,
      {
        dsimp at h,
        exfalso,
        linarith,
      },
      {
        assumption,
      },
    },
    {
      intro h,
      right,
      assumption,
    },
  },
  add_comm := by
  {
    intros x y,
    ext,
    split,
    {
      intro h,
      cases h,
      {
        right,
        assumption,
      },
      {
        left,
        assumption,
      },
    },
    {
      intro h,
      cases h,
      {
        right,
        assumption,
      },
      {
        left,
        assumption,
      },
    },
  },
}


instance xor_additive : comm_additive_monoid_str Prop :=
{
  add := λ P Q, (P ∨ Q) ∧ ¬ (P ∧ Q),
  add_assoc := λ a, λ b, λ c, sorry,
  zero := 0 = 1,
  add_zero := by{
                  intro a,
                  ext,
                  split,
                  {
                    intro h,
                    dsimp at h,
                    cases h with h₁ h₂,
                    cases h₁,
                    {
                      assumption,
                    },
                    {
                      simp at *,
                      exfalso,
                      assumption,
                    },
                  },
                  {
                    intro h,
                    simp,
                    assumption,
                  },
                },
  zero_add := by{
                  intro a,
                  ext,
                  split,
                  {
                    intro h,
                    simp at h,
                    assumption,
                  },
                  {
                    intro h,
                    simp,
                    assumption,
                  },
                },
  add_comm := λ x, λ y, by{
                            ext,
                            split,
                            {
                              intro h,
                              simp at *,
                              cases h with h₁ h₂,
                              split,
                              {
                                cases h₁,
                                {
                                  right,
                                  assumption,
                                },
                                {
                                  left,
                                  assumption,
                                },
                              },
                              {
                                intro h₃,
                                intro h₄,
                                apply h₂,
                                {
                                  assumption,
                                },
                                {
                                  assumption,
                                },
                              },
                            },
                            {
                              intro h,
                              split,
                              {
                                cases h with h₁ h₂,
                                cases h₁,
                                {
                                  right,
                                  assumption,
                                },
                                {
                                  left,
                                  assumption,
                                },
                              },
                              {
                                intro h₁,
                                cases h with h₂ h₃,
                                apply h₃,
                                cases h₁ with x y,
                                split,
                                {
                                  assumption,
                                },
                                {
                                  assumption,
                                },
                              },
                            },
                          },
}







/-! ## Question 6 (20 pts)
For a type `X`, the type `set X` in Lean is defined as the function type `X → Prop`. Given a set `A : set X`
(i.e. a function `A : X → Prop` and a term `x : X` we write `x ∈ A` as a shorthand for the proposition `A x`.

  set X       X → Prop
----------|------------
    A     |   A : X → Prop
  x ∈ A   |   A x
-/

#check @set

/- Show that the __convolution__ multiplication defined a semigroup structure on `set M` when `M` is a monoid.  -/

instance monoid_convolution_alt {M : Type} [mult_monoid_str M] :
  mult_semigroup_str (set M) :=
{
  mul := λ A B, λ m, ∃ x y : M, (m = x * y) ∧ (A x) ∧ (B y),  -- { (x * y) | (x ∈ A) (y ∈ B) }
  mul_assoc := λ a,λ b, λ c, by{
                                ext,
                                split,
                                {
                                  intro h,
                                  split,
                                  {
                                    use x,
                                    split,
                                    {
                                      rw _inst_4.one_mul,
                                    },
                                    {
                                      split,
                                      {
                                        cases h with d h₁,
                                        cases h₁ with g h₁,
                                        cases h₁ with h₁ h₂,
                                        cases h₂ with h₂ h₃,
                                        cases h₂ with u h₃,
                                        cases h₃ with v h₃,
                                        cases h₃ with h₃ h₄,
                                        cases h₄ with h₄ h₅,
                                        sorry,
                                      },
                                      {
                                        split,
                                        {
                                          use x,
                                          split,
                                          {
                                            rw _inst_4.one_mul,
                                          },
                                          {
                                            split,
                                            {
                                              cases h with d h₁,
                                              cases h₁ with g h₁,
                                              cases h₁ with h₁ h₂,
                                              cases h₂ with h₂ h₃,
                                              cases h₂ with u h₃,
                                              cases h₃ with v h₃,
                                              cases h₃ with h₃ h₄,
                                              cases h₄ with h₄ h₅,
                                              sorry,
                                            },
                                            {
                                              cases h with d h₁,
                                              cases h₁ with g h₁,
                                              cases h₁ with h₁ h₂,
                                              rw h₁,
                                              cases h₂ with h₂ h₃,
                                              sorry,
                                              /-
                                              
                                              cases h₂ with u h₄,
                                              cases h₄ with v h₄,
                                              cases h₄ with h₄ h₅,
                                              cases h₅ with h₆ h₇,
                                              -/
                                            },
                                          },
                                        },
                                      },
                                    },
                                  },
                                },
                                {
                                  intro h,
                                  cases h with z h₁,
                                  cases h₁ with l h₁,
                                  cases h₁ with h₁ h₂,
                                  cases h₂ with h₂ h₃,
                                  split,
                                  {
                                    use z,
                                    split,
                                    {
                                      sorry,
                                    },
                                    {
                                      split,
                                      {
                                        split,
                                        {
                                          sorry,
                                        },
                                        {
                                          assumption,
                                        },  
                                      },
                                      {
                                        sorry,
                                      },
                                    },
                                  },
                                  {
                                    assumption,
                                  },
                                },
                               }

}



/- ## Question 7 (20 pts)
In this problem we define the structure of __join semilattice__ in terms of commutative idempotent monoids. You then show that every join semilattice is in fact a preorder.
-/

/-
A monoid is __idempotent__ if each of its elements is idempotent.
-/

@[simp]
def idemp (e : M) := (e * e = e)

def mon_idemp (M : Type) [mult_monoid_str M] : Prop :=
∀ e : M, idemp e


/- A __(join) semilattice__ is a commutative and idempotent additive monoid.  -/

@[class]
structure jslat_str (X : Type) extends comm_mult_monoid_str X :=
(idemp : mon_idemp X)


/-
Mathlib defines the notions of __preorder__ as a type class and it defined the structure of  __partial order__ as an extension of __preorder__ structure. Go ahead and examine this definitions by click&command in below.
-/

#check preorder



def preorder_of_jslat (X : Type) [jslat_str X] :
preorder X :=
{ 
  le := λ x, λ y, (x * y = y),
  lt := λ x, λ y, (x * y = x),
  le_refl := _inst_4.idemp,
  le_trans := λ x, λ y, λ z, λ f, λ g, sorry,
  lt_iff_le_not_le := λ a, λ b, by
                                  {
                                    split,
                                    {
                                      intro h,
                                      split,
                                      {
                                        simp at *,
                                        have h₁, from jslat_str.idemp b,
                                        have h₂, from jslat_str.idemp a,
                                        unfold idemp at h₁ h₂,
                                        sorry,
                                        
                                      },
                                      {
                                        simp at *,
                                        intro h₁,
                                        have h₂, from jslat_str.idemp b,
                                        have h₃, from jslat_str.idemp a,
                                        unfold idemp at h₂ h₃,
                                        sorry,
                                      },
                                    },
                                    {
                                      intro h,
                                      cases h with h₁ h₂,
                                      simp at *,
                                      sorry,
                                    },
                                  }, 
}






/-! ## Question 8 (20 pts)
Show that for any monoid morphism `f : M →ₘ* N` the image of the underlying function `f : M → N` inherits a monoid structure from `N`.
-/


structure mult_monoid_image_fact (f : M →ₘ* N) :=
(node : Type)
(mon_node : mult_monoid_str node)
(left_mor : M →ₘ* node)
(right_mor : node →ₘ* N)
(fun_eq : right_mor ∘* left_mor = f)


local notation `im` :15 :=  fun_image

instance mult_monoid_str.fun_image (f : M →ₘ* N) : mult_monoid_str (im f) :=
{
  mul := λ x, λ y, y,
  mul_assoc := λ a b c, by{
                            simp,
                          },
  one := sorry,
  mul_one := λ a, by{
                      simp,
                      sorry,
                    },
  one_mul := λ a, by{
                      simp,
                    },
}






/-! ## Question 9 (20 pts)
In this problem, you are asked to construct image factorization for monoids using what you already did in the previous problem. You will show that for any monoid morphism `f : M →ₘ*  N` we can factor `f` into two monoid morphisms `p` and `m` such that `f = m ∘ p`, and `p` is surjective and `m` is injective.
-/

def mon_mor_img_embedding (f : M →ₘ* N) : (im f) →ₘ* N :=
{
  to_fun := fun_image.embedding f,
  resp_one := by{
                  simp,
                  sorry,
                },
  resp_mul := λ a b,by{
                        simp,
                        sorry,
                      },
}


def mon_mor_img_cover (f : M →ₘ* N) : M →ₘ* (im f) :=
{
  to_fun := fun_image.cover f,
  resp_one := by{
    ext,
    sorry,
  },
  resp_mul := λ x y, by{
    ext,
    sorry,
  },
}



def canonical_mult_monoid_image_fact (f : M →ₘ* N) : mult_monoid_image_fact (f : M →ₘ* N)  :=
{
  node := im f,
  mon_node := mult_monoid_str.fun_image f,
  left_mor := mon_mor_img_cover f,
  right_mor := mon_mor_img_embedding f,
  fun_eq := by{
    simp,
    sorry,
  },
}
/- 
Homeowork 10  
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/


import ..prooflab
import lectures.lec10_surj_inj_fact
import lectures.lec11_type_classes
import lectures.lec12_gaussian_integers
import lectures.lec13_structures_on_gaussian_int



open PROOFS 
open PROOFS.STR 




variables {L M N : Type} [mult_monoid_str L] [mult_monoid_str M] [mult_monoid_str N]



/-! ## Question 1 (20 pts) 
First, show that monoid morphisms are closed under composition, i.e. the composition of two monoid morphisms is again a monoid morphism. 

Then, show that for any monoid `M`, the type of monoid endomorphism `M →ₘ* M` itself admits a monoid structure. Note that the latter is very different than the type of endofunctions `M → M`. we showed before that whereas there is only one constant endomorphism `ℤ →ₘ* ℤ` there are ℤ-mnay endofunctions `ℤ → ℤ`. 
-/

@[simp]
def mult_monoid.morphism.comp (g : M →ₘ* N) (f : L →ₘ* M)  : L →ₘ* N := 
{ to_fun := g ∘ f,
  resp_one := sorry,
  resp_mul := sorry, } 


infixr  ` ∘* ` : 90  := mult_monoid.morphism.comp

def mult_monoid.morphism.id : M →ₘ* M := 
{
  to_fun := id, 
  resp_one := by {simp}, 
  resp_mul := by {simp},
}

#check M →ₘ* M



instance : mult_monoid_str (M →ₘ* M) := 
{ 
  mul := (∘*),
  mul_assoc := sorry,
  one := mult_monoid.morphism.id,
  mul_one := sorry,
  one_mul := sorry, 
}





/-! ## Question 2 (20 pts) 
Construct the cartesian products of monoids, and show that the two projection are monoid morphisms .  
-/

instance mult_monoid_str.product {M N : Type} [mult_monoid_str M] [mult_monoid_str  N] :
  mult_monoid_str (M × N) :=
{ 
  mul := λ x, λ y, ⟨x.1 * y.1, x.2 * y.2⟩,
  mul_assoc := sorry,
  one := sorry,
  mul_one := sorry,
  one_mul := sorry, 
}


instance mon_fst : M × N →ₘ* M := 
sorry 


instance snd_fst : M × N →ₘ* N := 
sorry 





/-! ## Question 3 (20 pts) 
Construct an equivalence of types of gaussian integers ℤ[i] and the cartesian product ℤ × ℤ.   
-/
infix ` ≅ `:15 := fun_equiv

def gausssian_int_cartesian_product :  
  ℤ[i] ≅ ℤ × ℤ :=  
{ to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry, }  


/- Is this equivalence a monoid isomorphism? If yes, prove it in below, if no, explain why it is not. -/


def gausssian_int_cartesian_product_monoid_isomorphism : ℤ[i] ≅ₘ* ℤ × ℤ := 
sorry 






/-! ## Question 4 (20 pts) 
Show that the type of functions `X → M` has a monoid structure if the codomain `M` has a monoid structure. The multiplication on `X → M` is given by pointwise multiplication, i.e. the multiplication of two functions 
`f g : X → M` should be a function `f * g : X → M` where 
`f * g (x) = (f x) * (g x)`. 
-/

@[instance] 
def mult_monoid_str.function (X M : Type)  [mult_monoid_str  M] :
  mult_monoid_str (X → M) :=
{ 
  mul := sorry,
  mul_assoc := sorry,
  one := sorry,
  mul_one := sorry,
  one_mul := sorry,  
}







/-! ## Question 5 (20 pts) 
Show that `Prop` admit multiplicative and additive monoid structures. -/ 

instance : comm_mult_monoid_str Prop := 
{ 
  mul := (∧),
  mul_assoc := sorry,
  one := sorry,
  mul_one := by sorry,
  one_mul := by sorry, 
  mul_comm := sorry,
}


instance or_additive : comm_additive_monoid_str Prop := 
{ 
  add := (∨),
  add_assoc := sorry,
  zero := sorry,
  add_zero := by sorry,
  zero_add := by sorry, 
  add_comm := sorry,
}


instance xor_additive : comm_additive_monoid_str Prop := 
{ 
  add := λ P Q, (P ∨ Q) ∧ ¬ (P ∧ Q),
  add_assoc := by {intros P Q R, ext, split, intro h, simp, split, simp at h, cases h with h₁ h₂, cases h₁ with hpq hr,  sorry, sorry, sorry, sorry, },
  zero := false,
  add_zero := by {intro P, ext, split, intro h, cases h with h₁ h₂, simp at h₁, exact h₁, intro hp, split, left, exact hp, simp,  },
  zero_add := by {intro P, ext, split, intro h, cases h with h₁ h₂, simp at h₁, exact h₁, intro hp, split, right, exact hp, simp,  }, 
  add_comm := by {intros P Q, simp, rw or_comm P Q, congr',  ext, split, intro h, intro hq, intro hp, apply h, exact hp, exact hq, intro h, intro hp, intro hq, apply h, assumption', },
}

lemma xor_no_ident :
¬(∃ b₁ : bool, ∀ b₂ : bool, (b₁ || b₂) && switch (b₁ && b₂) = b₁) :=
begin
  intro h₁,
  cases h₁ with b₁ hb₁,
  have h₂ : ¬(tt = ff), by {
    simp,
  },
  cases b₁,
  {
    apply h₂,
    rw ← hb₁ tt,
    refl,
  },
  {
    apply h₂,
    rw ← hb₁ tt,
    refl,
  },
end


lemma xor_no_ident :
(∃ b₁ : bool, ∀ b₂ : bool, (b₁ || b₂) && switch (b₁ && b₂) = b₂) :=
begin
  use ff, 
  intro b, 
end





/-! ## Question 6 (20 pts) 
For a type `X`, the type `set X` in Lean is defined as the function type `X → Prop`. Given a set `A : set X` 
(i.e. a function `A : X → Prop` and a term `x : X` we write `x ∈ A` as a shorthand for the proposition `A x`. 

  set X       X → Prop
----------|------------
    A     |   A : X → Prop
  x ∈ A   |   A x
-/

#check set

/- Show that the __convolution__ multiplication defined a semigroup structure on `set M` when `M` is a monoid.  -/

instance monoid_convolution_alt {M : Type} [mult_monoid_str M] :
  mult_semigroup_str (set M) := 
{ 
  mul := λ A B, λ m, ∃ x y : M, (m = x * y) ∧ (A x) ∧ (B y),  -- { (x * y) | (x ∈ A) (y ∈ B) }
  mul_assoc := sorry, 
}  





/- ## Question 7 (20 pts) 
In this problem we define the structure of __join semilattice__ in terms of commutative idempotent monoids. You then show that every join semilattice is in fact a preorder. 
-/

/-
A monoid is __idempotent__ if each of its elements is idempotent. 
-/

@[simp]
def idemp (e : M) := (e * e = e)

def mon_idemp (M : Type) [mult_monoid_str M] : Prop := 
∀ e : M, idemp e 


/- A __(join) semilattice__ is a commutative and idempotent additive monoid.  -/

@[class]
structure jslat_str (X : Type) extends comm_mult_monoid_str X := 
(idemp : mon_idemp X) 


/- 
Mathlib defines the notions of __preorder__ as a type class and it defined the structure of  __partial order__ as an extension of __preorder__ structure. Go ahead and examine this definitions by click&command in below. 
-/

#check preorder



def preorder_of_jslat (X : Type) [jslat_str X] : 
preorder X := 
{ le := λ x, λ y, (x * y = y),
  lt := λ x, λ y, (x * y = y) ∧ ¬ (y * x = x),
  le_refl := by {intro x, simp, exact (jslat_str.idemp x), },
  le_trans := by {intros x y z, intros h h', simp at *, rw ← h', rw ← mult_mon_assoc, rw h,  },
  lt_iff_le_not_le := by {intros a b, split; intro h; dsimp, exact h, split, exact h.1, exact h.2,  }, }






/-! ## Question 8 (20 pts) 
Show that for any monoid morphism `f : M →ₘ* N` the image of the underlying function `f : M → N` inherits a monoid structure from `N`.  
-/


structure mult_monoid_image_fact (f : M →ₘ* N) := 
(node : Type)
(mon_node : mult_monoid_str node) 
(left_mor : M →ₘ* node)
(right_mor : node →ₘ* N) 
(fun_eq : right_mor ∘* left_mor = f)


local notation `im` :15 :=  fun_image 

instance mult_monoid_str.fun_image (f : M →ₘ* N) : mult_monoid_str (im f) := 
{ 
  mul :=  sorry,
  mul_assoc := sorry,
  one := sorry,
  mul_one := sorry,
  one_mul := sorry, 
}






/-! ## Question 9 (20 pts) 
In this problem, you are asked to construct image factorization for monoids using what you already did in the previous problem. You will show that for any monoid morphism `f : M →ₘ*  N` we can factor `f` into two monoid morphisms `p` and `m` such that `f = m ∘ p`, and `p` is surjective and `m` is injective.   
-/ 

def mon_mor_img_embedding (f : M →ₘ* N) : (im f) →ₘ* N := 
{ 
  to_fun := fun_image.embedding f, 
  resp_one := sorry,
  resp_mul := sorry,
}


def mon_mor_img_cover (f : M →ₘ* N) : M →ₘ* (im f) := 
{ 
  to_fun := fun_image.cover f,
  resp_one := sorry,
  resp_mul := sorry, 
}



def canonical_mult_monoid_image_fact (f : M →ₘ* N) : mult_monoid_image_fact (f : M →ₘ* N)  := 
{ 
  node := im f,
  mon_node := mult_monoid_str.fun_image f,
  left_mor := mon_mor_img_cover f,
  right_mor := mon_mor_img_embedding f,
  fun_eq := sorry,
}




