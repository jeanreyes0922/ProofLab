/- 
Inductive Types : Part I, Natural Numbers
Sina Hazratpour
Introduction to Proof  
MATH 301, Johns Hopkins University, Fall 2022   
-/

import ..prooflab
import lectures.lec12_gaussian_integers
import lectures.lec13_structures_on_gaussian_int


/-
Overview of this code:
1. Natural Numbers
2. Predicates on Natural Numbers
3. Induction  
-/


namespace PROOFS

variables {X Y : Type}

------------------------------
--------Natural Numbers----
------------------------------

/- 
1.  Every natural number is either `zero` or `succ n`, for a previously defined natural number `n`. 
2. The type `nat` of natural numbers, which is defined in the Lean mathlib library, is the archetypal exmaple of an __inductive__ type.  
3. However, for the sole purpose of pedagogy we are going to define our own adhoc inductive type of natural numbers. It is defined in the same way as in the mathlib, but we give it a different name so that we can prove our own theorem without any previous knowledge. So far, we have taken the knowledge of natural numbers for granted, and we have relied on mathlib. Now, for the first time we will understand what statements like `∀ m n : mat, m + n = n + m` are true in virute of the construction of natural numbers. 
-/


/- mat short for  mynat -/

inductive mat : Type
| zero : mat -- pattern 1 (constructor `zero`)
| succ : mat → mat -- pattern 2 (constructor `succ`)
-- there are two cases; either a natural number is zero or is the successor of a previously defined natural number. 

/- 3 = succ 2 = succ (succ 1) = succ (succ (succ 0)) -/


/- There are two __constructors__. We start with `zero : nat`; it takes no arguments, so we have it from the start. In contrast, the constructor `succ` can only be applied to a previously constructed nat. Applying it to zero yields `succ zero : mat`. Applying it again yields `succ (succ zero) : mat`, and so on. 
-/



#check mat


#check mat.zero -- zero constructor 
#check mat.succ -- succ constructor 






namespace mat

instance : has_zero mat := ⟨mat.zero⟩ --zero here is mat.zero since we are inside in the namespace `mat`. 

@[simp]
lemma zero_def : 
  mat.zero = 0 := 
begin
  refl, 
end 


def one := succ 0 -- this works because 0 := zero in the type class has_zero 


instance : has_one mat := ⟨one⟩ 


def two := succ 1  


def three := succ two 

def four := succ three

def five := succ (succ three)



example : 
  five = succ (four) := 
begin
  refl, 
end 



example : 
  five = succ (succ (succ (two))) := 
begin
  refl, 
end 


#reduce three
#reduce four


example (m : mat) (h : succ m = two) : 
  succ(succ(m)) = three :=
begin
  rw h, 
  refl, 
end 


theorem no_conf : -- short for no_confusion
  ∀ m : mat, 0 ≠ succ (m) := 
begin 
  intro m, 
  intro h, 
  contradiction, -- the free generation of mat under the constructors `zero` and `succ` means there cannot be any non-rfl equations between terms of `mat` 
end   



/- 
What does it mean that `mat` is indutively defined? Intuitively, `mat` is the “smallest” type with these two constructors, meaning that it is __exhaustively__ and __freely__ generated by starting with `zero` and applying `succ` repeatedly. 
As a consequence to define a function, say `f`, out of `mat` all we need to do is to specify the value of `f` at `zero` and the value of `f` at `succ n` for `n : mat`. 

This is the idea behind __recursion__. 
-/


def pred : mat → mat -- predecessor function 
| 0 := 0 
| (succ n) := n 

#check pred



lemma pred_succ : 
   pred ∘ succ = id := 
begin
  funext n,
  dsimp, 
  cases n,
  {
    refl, 
  }, 
  {
    refl,
  }
end    


lemma succ_pred (k : mat) (h : ∃ m : mat, k = succ m): 
  succ (pred k) = k := 
begin 
  cases h with n hn,
  rw hn, 
  refl,  
end   



/-
Another example of recursion: For instance the constant function `mat → bool` at `ff`: 
-/

def constant_ff_of_mat : mat → bool 
| 0 := ff 
| (succ n) := constant_ff_of_mat n -- this definition is recursive since the value of `constant_ff_of_mat` at `succ n` is expressed in term of the value of  `constant_ff_of_mat` at `n` (one lower). This process halts at `zero`. 



def constant_ff_of_mat_alt : mat → bool  := λ b, ff -- what is the difference between this function and the one above


#reduce bool_of_nat 

-- define it by pattern matching  
def bool_of_mat : mat → bool 
| 0 := ff  
| (succ n) := tt 



def bad : mat → mat
| zero := zero
| (succ n) := succ (bad (succ n))



#check one + two 


-- note what just happened:
def thirty_seven_error : mat := 37 -- what is 37?


-- define it recursively 
def two_add : mat → mat 
-- define two_add to be a function which takes a natural number n and returns 2 + n
| 0 := two 
| (succ n) := succ (two_add (n))


/- `two_add 1 = two_add (succ 0)  by pattern matching 
              = succ (two_add 0) by definition of two_add; second pattern 
              = succ (two)  by definition of two_add; first pattern 
              = three by definition of three
-/


example : 
  two_add two = four := 
begin 
  refl, 
end 


def add : mat → mat → mat
-- λ m, (add m : mat → mat)
| m 0 := m
| m (succ n) := succ (add m n)



example : 
  add two two = four := 
begin 
  refl, 
end 

instance : has_add mat := ⟨add⟩


#check one + two 

def thirty_seven : mat := 37

-- another example of recursive function 
def double : mat → mat  
| 0 := 0 
| (succ n) := double n + 2 


example : 
  double 1 = 2 := 
begin 
  refl, 
end 


lemma add_zero (m : mat) : 
  m + 0 = m :=
begin
  refl, -- works because of the defn of addition 
end


lemma add_one (m : mat) : 
  m + 1 = succ (m) :=
begin
  refl,  
end 


lemma add_succ (m n : mat) : 
  m + succ n = succ (m + n) := 
begin
  refl,
end 




lemma zero_add' (m : mat) :
  0 + m = m := 
begin
  cases m, 
  {
    refl,  
  },
  {
    rw add_succ,
    -- we cannot do this because this is our original problem -- to do this we need some more tools (induction).
  }
end   


/-
__The Principle of Induction for Natural Numbers__: 
Let `P` be any property of natural numbers, i.e. P : ℕ → Prop (e.g. `P m = (0 + m =m)` ). Suppose `P` holds of zero (i.e. `P 0` holds), and whenever `P` holds of a natural number `n`, then it holds of its successor, `succ n` (i.e. we have a proof of `P n → P succ(n)` ). Then `P` holds of every natural number `n` (i.e. `∀ n : ℕ, P n` ).

`P 0 ∧ ( ∀ n, P n → P succ(n) ) →  ∀ n, P n`. 

                          ---------
                          `P n` (the induction hypothesis) 
                          .
                          .
                          .
`P 0` (the base case)     `P (succ n)`
------------------------------------
          ∀ n, P n 

Induction  works very similar to `cases`  but it gives us an extra assumption when proving the successor case, which we usually label `ih` (or something similar) for the induction hypothesis. 
-/


lemma zero_add  :
  ∀ m : mat, 0 + m = m :=  -- has the form of `∀ m : mat, P m` 
begin
  intro m, 
  induction m with n ihn, -- the important difference between tactic `induction` is that we now have an extra assumption `ihn` in the context which will be crucial
  {
    -- proving base case `P 0`
    refl,
  },
  {-- the inductive step: assuming `P n` and proving  `P succ(n)`
    rw add_succ,    
    rw ihn,
  },
end   


lemma one_add (n : mat) : 1 + n = succ n :=
begin
  induction n with d ihd, -- ihd stands for "inductive hypothesis"
  {
    refl,
  },
  {
    rw add_succ, -- changes lhs `1 + d.succ` to `(1 + d).succ`
    rw ihd,
  },
end


-- We isolate some useful facts and prove them first
lemma succ_add (a b : mat) : succ a + b = succ (a + b) :=
begin
  induction b with d ihd,
  { -- base case when b = 0
    refl,
  }, 
  { -- supposing `succ a + i = succ (a + i)` we want to prove `a.succ + i.succ = (a + i.succ).succ`. 
    rw add_succ, -- bring `i` into the addition. 
    rw ihd,
    refl,
  }
end

lemma add_comm (m n : mat) : m + n = n + m :=
begin
  induction m with d ihd,
  {
    show 0 + n = n + 0,
    rw add_zero, -- simplified `n + 0` to `n`
    rw zero_add, 
  },
  {
    rw add_succ, --changed `n + d.succ` to `(n + d).succ`
    rw ← ihd, 
    --rw ← add_succ,
    rw succ_add, 
  },
end   



lemma add_assoc (a b c : mat) : (a + b) + c = a + (b + c) :=
begin
  induction c with d ihd,
  {
    -- (a + b) + zero = a + (b + zero)
    show (a + b) + 0 = a + (b + 0), 
    repeat {rw add_zero}, 
  },
  {
    rw add_succ, 
    rw add_succ, 
    rw add_succ, 
    rw ihd, 
  },
end 



namespace STR
open PROOFS.STR

instance : comm_additive_monoid_str mat := 
{ 
  add := mat.add,
  add_assoc := mat.add_assoc,
  zero := 0,
  add_zero := mat.add_zero,
  zero_add := mat.zero_add, 
  add_comm := mat.add_comm, 
}

end STR




lemma succ_inj' : 
  is_injective succ := 
begin
  unfold is_injective,
  intros a b, -- introduced these to prove ∀   
  intro h, -- introduce `h` to prove → 
  induction a with d ihd, 
  {
    show 0 = b, 
    induction b with c ihc, 
    {
      refl,
    },
    {
      sorry, -- maybe this is a deadend approach, we have to reevaluate our strategy. 
    },
  },
  {
    sorry,
  },
end 










def mul : mat → mat → mat
-- λ m, (add m : mat → mat)
| m 0 := 0  
| m (succ n) :=  (mul m n) + m -- m * (n + 1) should return m * n + m


lemma mul_zero' (m : mat) : 
  mul m 0 =  0 := 
begin
  refl, -- definitional equality based on the first line of the defn of mul 
end   


instance : has_mul mat := ⟨mul⟩ 


lemma mul_zero (m : mat) : 
   m * 0 =  0 :=  
begin
  refl, -- definitional equality based on the first line of the defn of mul 
end   



lemma mul_succ (m n : mat) : 
   m * (succ n) =  m * n + m :=  
begin
  refl, -- definitional equality based on the second line of defn of mul 
end   



lemma mul_one (m : mat) : 
  m * 1 = m := 
begin
  suffices h : m * 1 = 0 + m, from zero_add m, 
  refl, 
end   



lemma zero_mul (m : mat) : 
   0 * m =  0 :=  
begin
  induction m with d ihd, 
  {
    refl, 
  }, 
  {
    rw mul_succ, 
    rw add_zero, 
    rw ihd, 
  }
end   

#check mat.mul_zero

lemma one_mul (m : mat) : 
  1 * m = m := 
begin
  induction m with d ihd, 
  {
    show (1 : mat) * 0 = 0, from (mat.mul_zero 1),
  },
  {
    rw mul_succ, 
    rw ihd, 
    rw add_one, 
  },
end 



/- We define recursively a function `sum_up_to : mat → mat` which assigns to `m : mat` the sum of natural numbers up to (and including) `m`, i.e. the value `sum_up n` is the sum of `1, ..., n`. -/

def sum_up_to : mat → mat
-- 
-- therefore, 
| 0 := 0
| (succ n) := sum_up_to n + succ n 

-- testing
example : 
  sum_up_to 5 = 15 := 
begin
  refl,   
end 



end mat 
end PROOFS



