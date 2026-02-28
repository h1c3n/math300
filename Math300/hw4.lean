import Math300.basic
import Mathlib

example {m n : ℤ} (hm : Odd m) (hn : ∃ k, n = 2*k) : Odd (m + n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  use a + b
  calc
    m + n = (2*a + 1) + 2*b := by rw [ha, hb]
    _= 2*(a + b) + 1 := by ring

example {a b : ℤ}
  (ha : ∃ k, a = 2*k)
  (hb : Odd b) :
  ∃ t, 3*a + b - 3 = 2*t := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, hm⟩ := hb
  use 3*k + m - 1
  calc
    3*a + b - 3 = 3*(2*k) + (2*m + 1) - 3 := by rw [hk, hm]
    _= 6*k + 2*m - 2 := by ring
    _= 2*(3*k + m - 1) := by ring

example (n : ℤ) : ∃ m : ℤ, m ≥ n ∧ Odd m := by
  use (2*(n*n) + 1)
  constructor
  · nlinarith
  · use (n*n)

example {a b : ℤ} (h : a ∣ b) :
  a ∣ (2*b^3 - b^2 + 3*b) := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  use (2*(a*k)^2*k - (a*k)*k + 3*k)
  ring

example : ∃ n : ℕ, n > 0 ∧ 9 ∣ (2^n - 1) := by
  use 6
  constructor
  · norm_num
  · use 7
    norm_num

example {n : ℤ} (h7 : 7 ∣ n) (h9 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha⟩ := h7
  obtain ⟨b, hb⟩ := h9
  have h : 7*a = 9*b := by
    calc
      7*a = n := by
        rw [ha]
      _= 9*b := by
        rw [hb]
  have h9a : 9 ∣ a := by
    use (4*b - 3*a)
    calc
      a = 28*a - 27*a := by ring
      _= 4*(7*a) - 3*(9*a) := by ring
      _= 4*(9*b) - 3*(9*a) := by rw [h]
      _= 9*(4*b - 3*a) := by ring
  obtain ⟨t, ht⟩ := h9a
  use t
  calc
    n = 7*a := by rw [ha]
    _= 7*(9*t) := by rw [ht]
    _= 63*t := by ring
