import Math300.basic
import Mathlib

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 :=
    calc
      (x + 3)*(x - 1) = x^2 + 2*x - 3 := by ring
      _= 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hx1 | hx2 := h2
  · left
    linarith
  · right
    linarith

example {a b : ℝ} (ha : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h1 : a^2 + 2*b^2 - 3*a*b = 0 := by
    linarith [ha]
  have h1 :=
    calc
      (a - b)*(a - 2*b) = a^2 + 2*b^2 - 3*a*b := by ring
      _ = 0 := by rw [h1]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h2 | ha2b := h2
  · left
    linarith
  · right
    linarith

example {r s : ℝ} (h1 : r + s ≤ 1) (h2 : r - s ≤ 5) : 2 * r ≤ 6 := by
  linarith


example {a b : ℝ} (h1 : a * b = a ∧ a = b) : (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 1) := by
  obtain ⟨h2, h3⟩ := h1
  have ha2 : a^2 = a := by
    calc
      a^2 = a*a := by ring
      _= a*b := by rw [h3]
      _= a := by linarith
  have ha : a = 0 ∨ a = 1 := by
    have h4 : a * (a - 1) = 0 := by
      calc
        a*(a - 1) = a^2 - a := by ring
        _= 0 := by linarith
    have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h4
    obtain ⟨h0, h1⟩ := h5
    · left
      linarith
    · right
      linarith
  obtain ha0 | ha1 := ha
  · left
    constructor
    · linarith
    · calc
        b = a := by linarith [h3]
        _= 0 := by rw [ha0]
  · right
    constructor
    · linarith
    · calc
        b = a := by linarith [h3]
        _= 1 := by rw [ha1]

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 > 1 := by
  use (-2 : ℝ)
  constructor
  · linarith
  · norm_num

example (x : ℚ) : ∃ y : ℚ, y^2 > x := by
  use (x + 1)
  nlinarith

example {t : ℝ} (h1 : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h1
  intro ht
  have ha1 : a*1 + 1 < a + 1 := by
    rw [ht] at ha
    linarith [ha]
  have : a + 1 < a + 1 := by
    calc
      a + 1 = a*1 + 1 := by ring
      _ < a + 1 := ha1
  linarith

example (n : ℤ) : ∃ a : ℤ, 2 * a^3 ≥ n * a + 7 := by
  obtain hn | hn := le_or_gt n 0
  · use 2
    calc
      2*2^3 = 16 := by norm_num
      _≥ n*2 + 7 := by linarith [hn]
  · use n + 7
    have h2 : 0 ≤ n^2 := by exact sq_nonneg n
    have h3 : 2*(n + 7)^3 = 2*n^3 + 42*n^2 + 294*n + 686 := by ring
    have h4 : n*(n + 7) + 7 = n^2 + 7*n + 7 := by ring
    rw [h3, h4]
    nlinarith [h2, hn]
