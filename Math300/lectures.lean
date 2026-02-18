import Math300.basic
import Mathlib

--linearith : linear arithemtic
--lemma sq_nonneg : x^2 ≥ 0
example {a b : ℤ} (h1 : a - 2 * b = 1) : a = 2 * b + 1 := by
  linarith

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 := by
  calc
    x + y^2 = x + (-7) := by rw [hy]
    _= 2 + (-7) := by rw [hx]
    _= -5 := by ring

--lecture 4
/-
logic?
existence proofs

ramanujan likes the number 1729
-/
-- proofs by cases (or)
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  · calc
    x*y + x = 1*y + 1 := by rw [hx]
    _= y + 1 := by ring
  · calc
    x*y + x = x*-1 + x := by rw [hy]
    _= -1 + 1 := by ring
    _= y + 1 := by rw [hy]

--proving the right goal
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2*x + 1 - 1) / 2 := by ring
    _= (5 - 1) / 2 := by rw [hx]
    _= 2 := by norm_num
--proving left then right
/-
-/
example {x : ℝ} (hx : 2 * x + 1 = 5) : (x = 1 ∨ x = 2) ∨ x = 7 := by
  left
  right
  calc
    x = (2*x + 1 - 1) / 2 := by ring
    _= (5 - 1) / 2 := by rw [hx]
    _= 2 := by norm_num

--something cool maybe
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x^2 - 3*x + 2 := by ring
    _= 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hx1 | hx2 := h2
  · left
    /-
    calc
       x = x - 1 + 1 := by ring
       _= 0 + 1 := by rw [hx1]
       _= 1 := by ring
    -/
    linarith
  · right
    linarith

-- and
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  --obtain ⟨h1, h2⟩ := h
  linarith
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
    a = 4 + 5*b := by linarith [h1]
    _= -6 + 5*(b + 2) := by ring
    _= -6 + 5*3 := by rw [h2]
    _= 9 := by norm_num 
  · linarith [h2]

-- existance
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b^2 + 1 := hb
    _> 0 := by linarith [sq_nonneg b]

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  ring --ring is used for algebraic expressions, norm_num just arithmetics

--lecture 5 odd even 

-- prop: proposition
-- def Odd (a : ℤ) : Prop := ∃ k, a = 2 * k + 1
example : Odd (7 : ℤ) := by 
  unfold Odd
  use 3 
  norm_num

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 := by 
  have h2 : n ^ 2 - 2 * n + 3 = (n - 5) ^ 2 + 8 * n - 22 := by ring 
  have h3 : (n - 5) ^ 2 ≥ 0 := sq_nonneg (n-5)
  have h4 : 8 * n - 22 ≥ 18 := by linarith
  have h5 : (n - 5) ^ 2 + 8 * n - 22 ≥ 0 + 18 := by linarith [h3, h4]
  linarith

--by calc 
--ring -> sq_nonneg -> linarith/rel [h1] -> norm_num
example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 := by 
  have h2 : (n - 5) ^ 2 ≥ 0 := sq_nonneg (n-5)
  calc 
    n ^ 2 - 2 * n + 3 = (n - 5) ^ 2 + 8 * n - 22 := by ring
    have h3 : 8 * n - 22 ≥ 18 := by linarith
    _≥ 0 + 18 := 
    


