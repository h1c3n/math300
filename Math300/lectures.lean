import Math300.basic
import Mathlib

--linearith : linear arithemtic
example {a b : ℤ} (h1 : a - 2 * b = 1) : a = 2 * b + 1 := by
  linarith

example {x y : ℚ} (hx : x = 2) (hy : y ^ 2 = -7) : x + y ^ 2 = -5 := by
  calc
    x + y^2 = x + (-7) := by rw [hy]
    _= 2 + (-7) := by rw [hx]
    _= -5 := by ring
