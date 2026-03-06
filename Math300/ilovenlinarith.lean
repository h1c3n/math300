import Math300.basic
import Mathlib

example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4*b - b^2) : a ≥ 1 := by
  have := h 2
  nlinarith

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  · intro h
    obtain h1 | h2 := le_or_gt k 2
    · obtain h3 | h4 := le_or_gt k 1
      · obtain h5 | h6 := le_or_gt k 0
        · left
          nlinarith
        · right
          · left
            nlinarith
      · right
        · right
          nlinarith
    · nlinarith
  · intro h
    obtain h0 | h1 | h2 := h
    · nlinarith
    · nlinarith
    · nlinarith

example : ∃! n : ℕ, ∀ a : ℕ, n ≤ a := by
  use 0
  constructor
  · intro a
    linarith
  · intro y hy
    have := hy 0
    linarith

example : ¬ ∃ N : ℕ, ∀ n : ℕ, n > N → Even n := by
  intro h
  obtain ⟨N, hN⟩ := h
  have h1 : Even (2 * N + 1) := by
    apply hN
    nlinarith
  obtain ⟨k, hk⟩ := h1
  have h2 := le_or_gt k N
  obtain h3 | h4 := h2
  · nlinarith
  · nlinarith
