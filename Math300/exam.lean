import Mathlib

example : ∃! n : ℕ, 0 < n ∧ n ^ 2 ≤ 2 := by
  use 1
  constructor
  · norm_num
  · intro y hy
    nlinarith

example : ∃ n : ℕ, 0 < n ∧ n ^ 2 ≤ 2 := by
  use 1
  constructor
  · linarith
  · nlinarith

example {n : ℤ} (h1 : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by
  have h2 : n * (7 * n ^ 2 - 20 * n) > 0 := by nlinarith [h1]
  have h3 : n ^ 2 - 2 > 0 := by nlinarith [h2]
  calc
    n ^ 4 - 2 * n ^ 2 = n^2*(n ^ 2 - 2) := by ring
    _ = n * n * (n ^ 2 - 2) := by nlinarith
    _ ≥ 10 * n * (n ^ 2 - 2) := by rel [h1, h3]
    _ = 3*n^3 + n * (7*n^2 - 20) := by nlinarith
    _ > 3*n^3 := by nlinarith --except i accidentally put norm_num on the exam
