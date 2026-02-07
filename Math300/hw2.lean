import Math300.basic
import Mathlib

example {a b : ℚ} (h1 : a ≥ 3) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by
    linarith

example {x : ℤ} (h1 : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by
    have h2 : x - 8 ≥ 1 := by linarith
    calc
        x^3 - 8*x^2 + 2*x = x*(x*(x-8)+2) := by ring
        _≥ 9*(9*1+2) := by rel [h1, h2]
        _≥ 9*(11) := by norm_num
        _≥ 3 := by norm_num

example {n : ℤ} (h1 : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by
    calc
        n^4 - 2*n^2 = n*n^3 - 2*n^2 := by ring
        _ ≥ 10*n^3 - 2*n^2 := by rel [h1]
        _ = 3*n^3 + 7*n*n^2 - 2*n^2 := by ring
        _ ≥ 3*n^3 + 7*10*n^2 - 2*n^2 := by rel [h1]
        _ = 3*n^3 + 68*(n*n) := by ring
        _ ≥ 3*n^3 + 68*(10*10) := by rel [h1]
        _ = 3*n^3 + 6800 := by norm_num
        _ > 3*n^3 := by norm_num

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 := by
    calc
        n^2 - 2*n + 3 = n*(n-2) + 3 := by ring
        _ ≥ 5*(5-2) + 3 := by rel [h1]
        _ = 5*3 + 3 := by ring
        _ = 18 := by norm_num
        _ > 14 := by norm_num

example {a b : ℤ} : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
    have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    calc
        a^2 + b^2 = (a-b)^2 + 2*a*b := by ring
        _≥ 0 + 2*a*b := by rel [h1]
        _≥ 2*a*b := by norm_num
