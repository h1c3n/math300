import Mathlib

example : ∃! n : ℕ, 0 < n ∧ n ^ 2 ≤ 2 := by
  use 1
  dsimp
  constructor
  · norm_num
  · intro y hy
    nlinarith
