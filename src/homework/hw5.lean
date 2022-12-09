import ..prooflab
import lectures.lec6_proposition


/-! # Homework 5: ...
Homework must be done individually.
Replace the placeholders (e.g., `:= sorry`) with your solutions.

You are allowed to use all the tactics we have learned so far.
 -/


namespace PROOFS

/-! ## Question 1 (20 points):
(**Part I**) Give a proof of the following propositional formula.
-/


theorem  disj_conj {P Q R : Prop} :
  (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) :=
begin
  split, -- we want to prove that (P ∨ Q → R) →  (P → R) ∧ (Q → R) and (P ∨ Q → R) ←  (P → R) ∧ (Q → R). The intro rule of biimplication is used with "split" to create two new goals
  {
    intro hqr, --we want to prove (P ∨ Q → R) → (P → R) ∧ (Q → R), so we use the intro rule of implication that makes P ∨ Q → R an assumption hqr and the rest the new goal
    split, --we want to prove (P → R) ∧ (Q → R) with the introduction rule of conjugation, which allows us to 'split' the goal to prove both sides of the conjugation
    {
      intro p, --we want to prove that P → R, the intro rule of implication makes P true and an assumption and the new goal R
      apply hqr, --we want to prove that R is P ∨ Q, so the elim rule of implication, apply, makes it so the goal, R, is the new goal, P ∨ Q
      left, --we want to prove that P ∨ Q, so one of the intro rules of disjunction, left, will be used to make the goal P from P ∨ Q
      assumption, --we can prove the exact goal from an assumption
    },
    {
      intro q, --we want to prove that Q → R, so the intro rule of implication makes Q true and an assumption and the new goal is R
      apply hqr, --we want to provae that R is P ∨ Q, so the elim rule of iimplication, apply, makes it so the goal, R, is the new goal, P ∨ Q
      right, -- we want to prove that P ∨ Q, so one of the intro rules of dijunction, right, will be used t omake the goal Q from P ∨ Q
      assumption, --we can prove the exact goal from an assumption
    },
  },
  {
    intro prqr, --we want to prove that (P → R) ∧ (Q → R) → P ∨ Q → R, so the intro rule of implication is used to make the left side of the implication an assumption and the right side of the implication the new goal
    cases prqr with pr qr, -- we want to make (P → R) and (Q → R) assumptions, so we use the elim rule of conjucation makes (P → R) ∧ (Q → R) to the two new assumptions
    intro poq, -- we want to prove P ∨ Q → R, so we use the intro rule of implication to make it so the left side of the implication is an assumption and the right side of the implication the new goal
    cases poq, -- we want to prove P ∨ Q, so we use the elim rule of disjunction to split the goal to prove that we can prove with P or with Q
    {
      apply pr, -- we want to prove R → P, so we use the elim rule of implication, apply, to make the goal P, if we apply pr (pr : P → R)
      assumption, -- we can prove the exact goal from an assumption
    },
    {
      apply qr, -- we want to prove R → Q, so we use the elim rule of iimplication, apply, to make the goal Q, if we apply qr (qr : Q → R)
      assumption, -- we can prove the exact goal from an assumption
    },
  },
end

/-
(**Part II**) In `lec6_proposition` we proved that
`P ∨ Q → ¬ P → Q`. The proof was `resolve_right`.

Use the previous theorem (`disj_conj`) to give a new proof of `P ∨ Q → ¬ P → Q`.
-/

theorem resolve_right_alt {P Q : Prop} :
 P ∨ Q → ¬ P → Q :=
begin
  intro poq, -- we want to prove that P ∨ Q → ¬ P → Q, so we use the intro rule of implication, which makes the left side of the implication an assumption and the right side of the implication the new goal
  intro np, -- we want to prove the ¬ P → Q, so we use the intor rule of implication, same exp as above
  cases poq, -- we want to prove that P ∨ Q, so we use the elim rule of disjunction, which makes it so we have to prove that we can prove the goal using either P or Q
  {
    contradiction, -- uses exfalso and apply np poq to prove that both the goal and assumptions are false
  },
  {
    assumption, -- we can prove the exact goal using an assumption
  },
end





/-! ## Question 2 (20 points):
Give a proof of the following statement.
-/
example (a b c : ℝ) (h₁ : c * a ≤ c * b) (h₂ : ¬ b ≤ a) :
  c * a ≤ c * b ∧ a ≠ b :=
begin
  split, -- we want to prove c * a ≤ c * b ∧ a ≠ b, so we use the intro rule of conjugation, split, to split the goal and prove both sides
  {
    assumption, -- proves the exact goal with an assumption
  },
  {
    linarith, -- proves the goal by using definitions and assumptions
  },
end






/-! ## Question 3 (20 points):
Give a proof of the following statements using only lemmas `neg_neg`, `neg_lt`, `neg_le`. The first one states that negation flips the strict order (<) , and the second one states that negation flips the order (≤).
-/

#check neg_neg
#check neg_lt
#check neg_le 

lemma lt_rev_of_neg {x y : ℝ} (h : x < y)
  : - y < - x :=
begin
  rw neg_lt, -- rewrite using neg_lt which makes the goal --x < y from -y < -x
  rw neg_neg, -- rewrite using neg_neg which proves that --x = x, which makes the goal x < y from --x < y
  assumption, -- we can prove the exact goal from an assumption
end



lemma le_rev_of_neg {x y : ℝ} (h : x ≤ y)
  : - y ≤ - x :=
begin
  rw neg_le, --rewrite using neg_le which makes the goal --x ≤ y from - y ≤ -x(basically the same as neg_lt)
  rw neg_neg, --rewrite using neg_neg which proves that --x = x, which makes the goal x ≤ y from --x ≤ y
  assumption, --proves the exact goal from an assumption
end






/-! ## Question 4 (20 points):
Use the two lemmas `lt_rev_of_neg` and `le_rev_of_neg` above together with some/all of the following lemmas to prove the following statement.
-/
#check lt_rev_of_neg
#check le_rev_of_neg
#check le_or_gt
#check abs_of_nonneg
#check abs_of_neg
#check neg_neg
#check lt_of_lt_of_le
#check lt_of_le_of_lt
#check le_trans
#check lt_trans
#check gt_iff_lt

example (x y : ℝ ) :
  abs x < y ↔ - y < x ∧ x < y :=
begin
  split, -- we want to give a proof of |x| < y ↔ -y < x ∧ x < y, we can use the intro rule of biimplication
  {
    intro h₁, -- we want to prove |x| < y → -y < x ∧ x < y, we can use the intro rule of implication
    split, -- we want to prove -y < x ∧ x < y, we can use the intro rule of conjugation
    {
      have h₃, from le_or_gt 0 x, -- we want to get rid of the || around x, so we need to introduce an assumption h₃, 0 ≤ x ∨ 0 > x, from le_or_gt 0 x
      cases h₃, -- we want to prove 0 ≤ x ∨ 0 > x, we can use tactic cases to introduce both sides of the dijunction(intro rule)
      {
        rw abs_of_nonneg h₃ at h₁, -- we want to prove |x| < y is x < y, which we can prove by rewriting abs_of_nonneg h₃(|x| < y) at h₁(x < y). abs_of_nonneg says that if you have a proof that 0 ≤ a, you can say that |a| = a
        linarith, --uses definitions and assumptions to prove the goal
      },
      {
        rw gt_iff_lt at h₃, -- we want to reverse the order of h₃, x < 0, so I can use the lemmas available, we can use gt_iff_lt to do this
        have h₄: |x| = -x, from abs_of_neg h₃, -- we want to get rid of the || around x, we can prove that by using abs_of_neg h₃, which makes |x| = -x
        rw h₄ at h₁, -- we can rewrite h₄ at h₁ which makes |x| < y to -x < y
        have h₅: -y < - -x, from lt_rev_of_neg h₁, -- we want to prove that -x < y is the same as the goal, so we can introduce h₅, -y < --x, from lt_rev_of_neg h₁, which says that -x < y can be written as h₅
        rw neg_neg at h₅, -- we want to rewrite h₅ so that it looks like the goal, we can use neg_neg to rewrite the double negative at h₅
        assumption, -- we can prove the exact goal from an assumption
      },
    },
    {
      have h₃, from le_or_gt 0 x, -- we want to introduce an assumption that we can use to get rid of the || around x, so we have h₃, from le_or_gt 0 x, which says we now have h₃, 0 ≤ x ∨ 0 > x, as an assumption
      cases h₃, -- we want to prove 0 ≤ x ∨ 0 > x, so we use the intro rule of disjunction
      {
        have h₄: |x| = x, from abs_of_nonneg h₃, -- we want to get rid of the || around x to make it closer to the goal, so we introduce h₄ from abs_of_nonneg h₃, which says that h₃, 0 ≤ x, proves that |x| = x
        rw h₄ at h₁, -- rewrites every |x| for x in h₁, which makes |x| < y to x < y
        assumption, -- we can prove the exact goal from an assumption
      },
      {
        rw gt_iff_lt at h₃, -- we want to reverse h₃ so we can use the lemmas
        rw abs_of_neg h₃ at h₁, -- we want to get rid of the || around x, so we can rewrite abs_of_neg h₃, which proves that |x| = -x, at h₁, which rewrites |x| < y to -x < y
        linarith, -- we can prove the goal using definitions and assumptions
      },
    },
  },
  {
    intro h₁, -- we want to prove -y < x ∧ x < y → |x| < y, we can use the intro rule of implication
    cases h₁ with h₂ h₃, -- we want to prove -y < x ∧ x < y, we can use the elim rule of conjugation
    have h₄, from le_or_gt 0 x, -- we want to introduce assumptions that we can use to get rid of || from x eventually, so we have h₄,0 ≤ x ∨ 0 > x, from le_or_gt 0 x
    cases h₄, -- we want to prove both sides of disjunction, so we use tactic 'cases' to split the assumption
    { 
      have h₅: |x| = x, from abs_of_nonneg h₄, -- we want an assumption that can get rid of the || from the goal, we can get |x| = x from abs_of_nonneg h₄, which says that because of h₄, 0 ≤ x, we can prove that x will always be positive, so we can prove |x| = x
      rw h₅, -- rewrites the goal to x < y from |x| < y by h₅, which says |x| = x
      assumption, -- we can prove the exact goal from an assumption
    },
    {
      rw gt_iff_lt at h₄, -- we want to rewrite h₄ so we can use it, gt_iff_lt flips h₄, 0 > x, to x < 0
      rw abs_of_neg h₄, -- rewrites the goal with abs_of_neg h₄, which says that h₄, x < 0, proves that |x| = -x. That rewrites any instances of |x| to -x
      have h₆: -x < - -y, from lt_rev_of_neg h₂, -- we want to rewrites h₂ to look more like the goal, so we can make it -x < --y from lemma lt_rev_of_neg h₂, which states that a < b can be rewritten as -b < -a
      rw neg_neg at h₆, -- rewrites any instances of -- as positive at h₆, which rewrites h₆ from -x < --y to -x < y
      assumption, -- we can prove the exact goal from an assumption
    },
  },
end

/-this is the first way I solved it
example (x y : ℝ ) :
  abs x < y ↔ - y < x ∧ x < y :=
begin
  split,
  {
    intro axy,
    rw abs_lt at axy,
    assumption,
  },
  {
    intro nyxxy,
    rw abs_lt,
    assumption,
  },
end
-/





/-! ## Question 5 (20 points): -/


def EM (P : Prop) :=
P ∨ ¬ P

#check EM

def DN (P : Prop) :=
(¬ P → false) → P

#check DN



theorem excluded_implies_double_negation  {P : Prop} : EM P → DN P :=
begin
 unfold EM,
 unfold DN,
 intro ponp, -- we want to prove P ∨ ¬P → (¬P → false) → P, so we use the intro rule of implication to make the left side of the first implication an assumption and the left side the new goal
 intro npf, -- we want to prove that (¬P → false) → P, so we use the intro rule of implication to make the left side of the first implication an assumption and the left side the new goal
 cases ponp, -- we want to prove P ∨ ¬P, so we use the elimination rule of disjunction which splits the goal so we can prove the goal through either P or ¬ P
 {
  assumption, -- the exact goal can be proven with an assumption
 },
 {
  contradiction, --uses exfalso in the goal and the fact that both assumption contradict each other to prove that false is false
 },
end




end PROOFS