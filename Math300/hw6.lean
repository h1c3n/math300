import Math300.basic
import Mathlib

example (P : Prop) : P → ¬ (¬ P) := by
    intro hP hnP
    exact hnP hP

example (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬P ∧ ¬Q) := by
    constructor
    · intro h1
      constructor
      · intro hP
        apply h1
        left
        exact hP
      · intro hQ
        apply h1
        right
        exact hQ
    · intro h2 h
      obtain hP | hQ := h
      · exact h2.left hP
      · exact h2.right hQ

example (P Q : Prop) : (¬Q → ¬P) ↔ (P → Q) := by
  constructor
  · intro h1 hP
    by_cases hQ : Q
    · exact hQ
    · have : ¬ P := h1 hQ
      contradiction
  · intro h2 hQ hP
    have : Q := h2 hP
    contradiction

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  · intro h
    by_contra h1
    apply h
    intro a
    by_contra ha
    apply h1
    use a
  · intro h h1
    obtain ⟨x, hx⟩ := h
    have : P x := h1 x
    contradiction

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h1 : 0 ≤ 1 + a := by linarith
    have h2 : (1 + a) ^ k * (1 + a) ≥ (1 + (k : ℝ) * a) * (1 + a) := by
      exact mul_le_mul_of_nonneg_right ih h1
    calc
      (1 + a)^(k + 1) = (1 + a)^k*(1 + a) := by rw [pow_succ]
      _ ≥ (1 + (k : ℝ)*a)*(1 + a) := by exact h2
      _ = 1 + ((k : ℝ) + 1)*a + (k : ℝ)*a^2 := by ring
      _ ≥ 1 + ((k : ℝ) + 1)*a := by nlinarith
      _ = 1 + (((k + 1 : ℕ) : ℝ))*a := by norm_num

example {n : ℕ} : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero =>
    norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        2*(∑ i ∈ Finset.range (k + 1), i + (k + 1)) =
        2*∑ i ∈ Finset.range (k + 1), i + 2*(k + 1) := by ring
        _ = k * (k + 1) + 2 * (k + 1) := by rw [ih]
        _ = (k + 1) * (k + 2) := by ring

example {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  exact Odd.pow ha

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  rcases Nat.even_or_odd a with h | h
  · exact h
  · exfalso
    have h1 : Odd (a ^ n) := Odd.pow h
    rw [← Nat.not_even_iff_odd] at h1
    exact h1 ha

def F : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

example (n : ℕ) : Even (F (3 * n)) := by
  induction n with
  | zero =>
      use 0
      norm_num [F]
  | succ k ih =>
      have h1 : 3 * (k + 1) = 3 * k + 3 := by ring
      rw [h1]
      have h2 : F (3 * k + 3) = 2 * F (3 * k + 1) + F (3 * k) := by
        calc
          F (3 * k + 3) = F (3 * k + 2) + F (3 * k + 1) := by
            rw [show 3 * k + 3 = (3 * k + 1) + 2 by ring]
            rw [F]
          _ = (F (3 * k + 1) + F (3 * k)) + F (3 * k + 1) := by
            rw [show 3 * k + 2 = (3 * k) + 2 by ring]
            rw [F]
          _ = 2 * F (3 * k + 1) + F (3 * k) := by ring
      rw [h2]
      have h3 : Even (2 * F (3 * k + 1)) := by
        use F (3 * k + 1)
        ring
      exact Even.add h3 ih

example {n : ℕ} (hn : 12 ≤ n) : ∃ a b : ℕ, n = 4 * a + 5 * b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- Wrap the match in a recursive helper to access the induction hypothesis
  let rec helper (m : ℕ) : ∃ a b : ℕ, 12 + m = 4 * a + 5 * b := by
    match m with
    | 0 => exact ⟨3, 0, by norm_num⟩  -- 12 = 4·3 + 5·0
    | 1 => exact ⟨2, 1, by norm_num⟩  -- 13 = 4·2 + 5·1
    | 2 => exact ⟨1, 2, by norm_num⟩  -- 14 = 4·1 + 5·2
    | 3 => exact ⟨0, 3, by norm_num⟩  -- 15 = 4·0 + 5·3
    | x + 4 =>
      -- The recursive call gives us the IH for x
      obtain ⟨a, b, ih⟩ := helper x
      -- Since 12 + x = 4a + 5b, then 12 + (x + 4) = 4(a + 1) + 5b
      exact ⟨a + 1, b, by linarith⟩
  exact helper k
