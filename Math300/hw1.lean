import Math300.basic
import Mathlib

example {a b : ℤ} (h1 : a - b = 0) : a = b := by
  calc
    a = a - b + b := by ring
    _ = 0 + b := by rw [h1]
    _ = b := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by
  calc
    p = p - 2*q + 2*q := by ring
    _ = 1 + 2*q := by rw [h1]
    _ = 1 + 2*(-1) := by rw [h2]
    _ = -1 := by ring

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 := by
  calc
    x = x + 2*y - 2*y := by ring
    _ = 3 - 2*y := by rw [h2]
    _ = 3 - 2*(y + 1) + 2 := by ring
    _ = 3 - 2*3 + 2 := by rw [h1]
    _ = -1 := by ring

example {u v : ℝ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 := by
  calc
    u = (4*u + v - v) / 4 := by ring
    _ = (3 - v) / 4 := by rw [h1]
    _ = (3 - 2) / 4 := by rw [h2]
    _ = 1 / 4 := by ring

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by
  calc
    a = (3*a) / 3 := by ring
    _ = ((a + 2*b) + 2*(a - b)) / 3 := by ring
    _ = (4 + 2*1) / 3 := by rw [h1, h2]
    _ = 2 := by ring

example {u v : ℝ} (h1 : u + 1 = v) : u^2 + 3*u + 1 = v^2 + v - 1 := by
  calc
    u^2 + 3*u + 1 = (u + 1)^2 + (u + 1) - 1 := by ring
    _ = v^2 + v - 1 := by rw [h1]
