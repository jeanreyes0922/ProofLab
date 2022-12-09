import lectures.lec18_nat_trans

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {𝓒 : Type u₁} [category_str.{v₁} 𝓒] {𝓓 : Type u₂} [category_str.{v₂} 𝓓]


def ℍom : 𝓒 ⥤ (𝓒ᵒᵖ ⥤ Type v₁) :=
{
  -- the action of ℍom on objects of 𝓒
  obj := λ X, c𝓕 X,
  -- the action of ℍom on morphisms of 𝓒
  mor := λ X Y, λ f, {
                      cmpt := λ W, λ g, f ⊚ g,
                      naturality' :=
                      by
                      {
                        intros U V k,
                        dsimp,
                        funext x,
                        change f ⊚ (x ⊚ (hom.unop k)) = (f ⊚ x) ⊚ (hom.unop k),
                        simp only [comp_assoc],
                      },
                     },
  -- ℍom is functorial, it respects identifies and compositions in 𝓒
  resp_id' := by {intro X, ext Y, simp, refl,},
  resp_comp' := by 
                  {
                    intros X Y Z f g,
                    ext U,
                    simp,
                    refl,
                  },
}
/-
 __Q1__
 Construct the type of all groups. Show that this type admits the structure of a (large) category where morphisms are group homomorphisms.
-/


/-
__Q2__ 
Recall the definition of mult_monoid_action from HW10.

class mult_monoid_action (M A : Type) [mult_monoid_str M] :=
(smul : M → A → A) -- the scalar multiplication of `M` on `A`.
(one_smul' : ∀ (x : A), smul (1 : M) x = x)
(mul_smul' : ∀ (r s : M) (x : A),
smul (r * s)  x = smul r (smul s x))
Show that a monoid action gives rise to a functor from the delooping category of the monoid to the category of types. You can show that by filling in for the sorry placeholder in below.

def delooping_monoid_action (A : Type) [M : mult_Monoid] [mult_monoid_action M.carrier A] : (delooping_cat M).carrier ⥤  Type* :=  sorry
-/


--__Q3__
def Yoneda (X Y: 𝓒) (α : ℍom.obj X ≅ ℍom.obj Y) :
  X ≅ Y :=
{
  to_mor := α.to_mor.cmpt (op X) (𝟙 X),
  inv_mor := α.inv_mor.cmpt (op Y) (𝟙 Y),
  left_inv := sorry,
  right_inv := sorry,
}

-- __Q4__ The final question

/-! ## The Arrow Category :
Given a category 𝓒 we want to construct a new category whose objects are morphisms of 𝓒 and whose morphisms are commutative squares in 𝓒.
 -/


structure arrow_type (𝓒 : Type*) [small_category_str 𝓒] :=
(dom : 𝓒)
(cod : 𝓒)
(arrow : dom ⟶ cod)

#check arrow_type


local notation `𝔸𝕣` : 10 := arrow_type



structure arrow_type_hom {𝓒 : Type*}[small_category_str 𝓒] (α β : 𝔸𝕣 𝓒 ) :=
(top : α.dom ⟶ β.dom)
(bot : α.cod ⟶ β.cod)
(eq : β.arrow ⊚ top = bot ⊚ α.arrow)