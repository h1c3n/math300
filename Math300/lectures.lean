import Math300.basic
import Mathlib

-- Nat or \ N or \ nat
-- Int or \ Z or \ int
-- Real or \ R or \ real
-- Rat or \ Q or \ rat
-- \ leq
-- \ geq
-- \ and
-- \ or
-- \ .
-- \ langle or \ < -> ⟨
-- \ rangle or \ > -> ⟩
-- \ iff  ↔
-- \ not  ¬
-- Preferred way to write: 0 ≤ a^2 rather than a^2 ≥ 0

-- Tactics
-- calc        : Proof by calculation
-- ring        : Abstract algebra ring
-- rw          : Rewrite (equalities)
-- rel         : relation or relational (inequalities)
-- norm_num    : Operation with numbers
-- linarith    : Linear arithemtic
-- have        : Introduce a new hypothesis
-- apply       : Apply a Lemma or Theorem
-- exact       : Close the goal when it is exact a given result
-- constructor : Splits and goal into subtasks
-- nlinarith   : Nonlinear arithemtic
-- dsimp       : Definitional simplify
-- obtain      : Obtain hypotheses from composite hypothesis
-- left        : Get the left goal from a OR goal
-- right       : Get the right goal from a OR goal
-- intro       : Get the variable or hypothesis needed to prove goal

-- Lemmas/Theorems:
-- lemma sq_nonneg : {a : ℝ} : 0 ≤ a^2 - Square nonnegative

-- lemma ne_of_lt {a b : ℚ} (h : a < b) : a ≠ b :=
-- not equal of less than

-- lemma ne_of_gt {a b : ℝ} (h : a > b) : a ≠ b :=
-- not equal of greater than

-- lemma le_antisymm {a b : ℝ} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
-- less or equal antisymmetry

-- lemma le_or_succ_le (a b : ℕ) : a ≤ b ∨ b + 1 ≤ a :=
-- less or equal or successor less or equal

-- Prop: Proposition
-- def Odd (a : ℤ) : Prop := ∃ k, a = 2 * k + 1

-- lemma Nat.le_of_dvd {a b : ℕ} (hb : 0 < b) (hab : a ∣ b) : a ≤ b := by
-- lemma Nat.pos_of_dvd_of_pos {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by

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

--exam 1 notes
example (t : ℝ) (h : t ≥ 10) : t^2 - 3 * t + 17 ≥ 5 := by
  calc
    t^2 - 3 * t + 17 = t * t - 3 * t + 17 := by ring
    _                ≥ 10 * t - 3 * t + 17 := by rel [h]
    _                = 7 * t + 17 := by ring
    _                ≥ 7 * 10 + 17 := by rel [h]
    _                ≥ 5 := by norm_num

example {m n : ℤ} (h1 : m ^ 2 + n ≤ 2) : n ≤ 2 := by
  calc
    n ≤ m ^ 2 + n := by linarith [sq_nonneg m]
    _ ≤ 2 := by rel [h1]

example {m n : ℤ} (h1 : m ^ 2 + n ≤ 2) : n ≤ 2 := by
  have h2 : 0 ≤ m ^ 2 := sq_nonneg m
  linarith

example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 := by
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by linarith [sq_nonneg (x - y)]
    _           = 2 * (x ^ 2 + y ^ 2) := by ring
    _           ≤ 2 * 1 := by rel [h]
    _           < 3 := by norm_num

example {m n : ℤ} (h1 : m ^ 2 + n ≤ 2) : n ≤ 2 := by
  have h2 : 0 ≤ m ^ 2 := sq_nonneg m
  calc
    n ≤ m ^ 2 + n := by linarith [h2]
    _ ≤ 2 := by rel [h1]

example {m n : ℤ} (h1 : m ^ 2 + n ≤ 2) : n ≤ 2 := by
  linarith [sq_nonneg m]

-- Invoking lemmas
example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by norm_num

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  linarith

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  have h2 := by
    calc
      x = 3 * x / 3 := by ring
      _ = 2 / 3 := by rw [hx]
      _ < 1 := by norm_num
  apply ne_of_lt h2

-- Proofs by cases
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  · calc a ^ 2 = a ^ 2 + 0 := by ring
      _ ≤ a ^ 2 + b ^ 2 := by linarith [sq_nonneg b]
      _ = 0 := by rw [h1]
  · exact sq_nonneg a

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  have h2 :=
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by linarith [sq_nonneg b]
      _     = 0 := h1
  have h3 := sq_nonneg a
  exact le_antisymm h2 h3
  -- apply le_antisymm h2 h3

  -- Proofs by cases (proofs with OR hypothesis or goals)
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  · calc
      x * y + x = 1 * y + 1 := by rw [hx]
      _ = y + 1 := by ring
  · calc
      x * y + x = x * -1 + x := by rw [hy]
      _ = -1 + 1 := by ring
      _ = y + 1 := by rw [hy]

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by ring -- norm_num

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 2 ∨ x = 1 := by
  left
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by norm_num

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hx1 | hx2 := h2
  · left
    calc
      x = x - 1 + 1 := by ring
      _ = 0 + 1 := by rw [hx1]
      _ = 1 := by ring
  · right
    linarith

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain hx1 | hx2 := h2
  · left
    linarith
  · right
    linarith

-- Proofs by cases (proofs with AND hypothesis or goals)
example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring

example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  linarith

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by linarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · linarith [h2]

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by linarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by linarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · linarith
  · linarith

-- Existence proofs
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by linarith [sq_nonneg b]

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  ring

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  linarith

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  linarith

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  calc
    3 * n + 2 = 3 * (2 * k + 1) + 2 := by rw [hk]
    _ = 2 * (3 * k + 2) + 1 := by ring

example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨m, hm⟩ := hbc
  use k ^ 2 * m
  calc
    c = b ^ 2 * m := by rw [hm]
    _ = (a * k) ^ 2 * m := by rw [hk]
    _ = a ^ 2 * ( k ^ 2 * m) := by ring

example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by norm_num

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by nlinarith
    _  = x ^ 2 - 2 * x := by ring

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1
  intro x
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by linarith [sq_nonneg (x - 1)]
    _  = x ^ 2 - 2 * x := by ring

example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
         _ ≤ (7 - 1) / 3 := by rel [h]
         _ = 2 := by norm_num
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
         _         = 7 := by norm_num

example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring

example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · norm_num
  · intro y hy
    linarith

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  dsimp at ha2
  have h1 : -a = a := by
    apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _        = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
      x = a ^ 2 := by rw [ha1]
      _ = 0 ^ 2 := by rw [h2]
      _ = 0 := by ring

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have h2 := h (1/2)
  norm_num at h2

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have := h (1/2)
  linarith

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro ⟨n, hn⟩
  obtain h1 | h2 := le_or_gt n 1
  · nlinarith
  · nlinarith

example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · exact hP
  · contradiction

example {P Q : Prop} : P → (P ∨ ¬ Q) := by
  intro hP
  left
  apply hP

example {P : Prop} : (P ∨ P) ↔ P := by
  constructor
  · intro hP
    obtain h1 | h2 := hP
    · exact h1
    · exact h2
  · intro hP
    left
    exact hP

example {P Q R : Prop} : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · exact h1
      · exact h2
    · right
      constructor
      · exact h1
      · exact h2
  · intro h
    obtain ⟨h1, h2⟩ | ⟨h3, h4⟩ := h
    · constructor
      · exact h1
      · left
        exact h2
    · constructor
      · exact h3
      · right
        exact h4

-- α is the "Universe" of all possible values of x
-- P is a function from α to Prop
example {α} (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  -- Prove ->
  · intro h a ha
    have : ∃ x, P x
    · use a
    contradiction
  -- Prove <-
  · intro h h'
    obtain ⟨y, hy⟩ := h'
    have : ¬ P y := h y
    contradiction

example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

example {α : Type*} (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

example {X} (P : X → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
    intro x
    constructor
    · apply h1
    · apply h2

example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx

-- Normal form for negation
-- Push ¬ inside the expression

example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h hPQ
    obtain ⟨hP, hQ⟩ := hPQ
    rcases h with hNP | hNQ
    · exact hNP hP
    · exact hNQ hQ

-- Law of the excluded middle
example {P : Prop} (hP : ¬¬P) : P := by
  by_cases hP2 : P
  · apply hP2
  · contradiction

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  -- Proof by induction
  induction n with
  | zero => linarith -- norm_num -- nlinarith
  | succ k ih =>
    omega

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  -- Proof by induction
  induction n with
  | zero => norm_num -- simp -- nlinarith
  | succ n ih =>
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
                  _ ≥ 2 * (n + 1) := by rel [ih] -- linarith
                  _ = n + 1 + (n + 1) := by ring
                  _ ≥ n + 1 + 1 := by linarith

example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  induction n
  · -- base case
    simp
  · -- induction step
    rename_i n ih
    calc 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    _ ≥ 2 * (n + 1) := by linarith
    _ = n + 1 + (n + 1) := by ring
    _ ≥ n + 1 + 1 := by linarith

example (n : ℕ) : Even n ∨ Odd n := by
  induction n with
  | zero =>
    left
    norm_num -- decide -- simp
  | succ n ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      -- exact ⟨k, by omega⟩
      use k
      omega
    · left
      -- exact ⟨k + 1, by omega⟩
      use k + 1
      omega

example (n : ℕ) : Even n ∨ Odd n := by
  induction n with
  | zero =>
    left
    simp
  | succ n ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      exact ⟨k, by omega⟩
    · left
      exact ⟨k + 1, by omega⟩

example (n : ℕ) : Even n ∨ Odd n := by
  induction n with
  | zero =>
    left
    exact ⟨0, rfl⟩
  | succ n ih =>
    rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩
    · right
      exact ⟨k, by omega⟩
    · left
      exact ⟨k + 1, by omega⟩

example {n : ℕ} (hn : 4 ≤ n) : 2 ^ n > 3 * n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have h3 : 2 ^ n > 0 := by positivity
    linarith

def a (n : ℕ) : ℕ := 2 ^ n

-- #eval a 10

def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => (b n) ^ 2 - 2

#eval b 0

#eval b 3

example (n : ℕ) : Odd (b n) := by
  induction n with
  -- base case
  | zero =>
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by norm_num
  -- inductive step
  | succ n ih =>
    obtain ⟨x, hx⟩ := ih
    use 2 * x ^ 2 + 2 * x - 1
    calc b (n + 1) = b n ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring

-- \ sum -> ∑
-- Finset.range n = {0, 1, 2, ..., n - 1}
example (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => norm_num -- simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

-- Finset.range (n + 1) = {0, 1, 2, ..., n}
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (2 * i + 1) = (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

def sumOdd : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

-- #eval sumOdd 1

example (n : ℕ) : sumOdd n = n ^ 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp [sumOdd, ih]
    ring

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F 10 -- Outputs 89

-- Note that Nat.fib is F shifitted,
-- that is, F n = Nat.fib (n + 1)
-- Fibonacci sequence define on Lean
#eval Nat.fib 11 -- Outputs 89

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      dsimp [F]
      norm_num
  | 1 =>
      dsimp [F]
      norm_num
  | k + 2 =>
      have IH1 := F_bound k -- first inductive hypothesis
      have IH2 := F_bound (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by norm_num
        _ = 2 ^ (k + 2) := by ring

theorem F_bound_v2 (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      calc F 0 = 1 := by rw [F]
        _ ≤ 2 ^ 0 := by norm_num
  | 1 =>
      calc F 1 = 1 := by rw [F]
        _ ≤ 2 ^ 1 := by norm_num
  | k + 2 =>
      have IH1 := F_bound_v2 k -- first inductive hypothesis
      have IH2 := F_bound_v2 (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by norm_num
        _ = 2 ^ (k + 2) := by ring

def F1 : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => F (n + 1) + F n

#eval F1 20

#check @F1

-- q : ℝ → ℝ
-- q(x) = x + 3
def q (x : ℝ) : ℝ := x + 3

#check @q

def Injective {X Y} (f : X → Y) : Prop :=
                         ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2

example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  dsimp [q] at h
  linarith

example : Injective q := by
  dsimp [Injective]
  intro x1 x2 h
  calc
    x1 = (x1 + 3) - 3 := by ring
     _ = (q x1) - 3 := by rw [q]
     _ = (q x2) - 3 := by rw [h]
     _ = (x2 + 3) - 3 := by rw [q]
     _ = x2 := by ring

example : ¬ Injective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Injective]
  push_neg
  use -1, 1
  constructor
  · norm_num -- linarith -- ring
  · norm_num -- linarith

def Surjective {X Y} (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y

-- s : ℚ → ℚ
-- s(a) = 3 * a + 2
def s (a : ℚ) : ℚ := 3 * a + 2

-- 3 * x + 2 = y -> x = (y - 2) / 3
example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  dsimp [s]
  linarith

example : Surjective s := by
  dsimp [Surjective]
  intro y
  use (y - 2) / 3
  calc s ((y - 2) / 3) = 3 * ((y - 2) / 3) + 2 := by rw [s]
                     _ = y := by ring

example : ¬ Surjective (fun x : ℝ ↦ x ^ 2) := by
  dsimp [Surjective]
  push_neg
  use -1
  intro x
  apply ne_of_gt
  calc -1 < 0 := by norm_num
        _ ≤ x ^ 2 := by nlinarith

def Bijective {X Y} (f : X → Y) : Prop := Injective f ∧ Surjective f

def p (x : ℝ) : ℝ := 2 * x - 5

-- p is injective: If 2 * x1 - 5 = 2 * x2 - 5 => x1 = x2. So q is injective.
-- p is projective: Given y, ∃ x s.t. 2 * x - 5 = y. Take x = (y + 5) / 2.
--                  Then q(x) = y. So q is surjective.
example : Bijective p := by
  dsimp [Bijective]
  constructor
  · dsimp [Injective]
    intro x1 x2 hx
    dsimp [p] at hx
    calc x1 = ((2 * x1 - 5) + 5) / 2 := by ring
          _ = ((2 * x2 - 5) + 5) / 2 := by rw [hx]
          _ = x2 := by ring
  · dsimp [Surjective]
    intro y
    use (y + 5) / 2
    calc p ((y + 5) / 2) = 2 * ((y + 5) / 2) - 5 := by rfl
                       _ = y := by ring

-- def a (t : ℝ) : ℝ := t ^ 3 - t

-- example : ¬ Bijective a := by
--   dsimp [Bijective]
--   rw [not_and_or]
--   left
--   dsimp [Injective]
--   push_neg
--   use 0, 1
--   constructor
--   · calc a 0 = 0 ^ 3 - 0 := by rfl
--       _ = 1 ^ 3 - 1 := by norm_num
--       _ = a 1 := by rfl
--   · norm_num

example {X Y} {f : X → Y} : Bijective f ↔ ∀ y, ∃! x, f x = y := by
  constructor
  · -- if `f` is bijective then `∀ y, ∃! x, f x = y`
    intro h y
    obtain ⟨h_inj, h_surj⟩ := h
    obtain ⟨x, hx⟩ := h_surj y
    use x
    dsimp
    constructor
    · apply hx
    · intro x' hx'
      apply h_inj
      calc f x' = y := by rw [hx']
        _ = f x := by rw [hx]
  · -- if `∀ y, ∃! x, f x = y` then `f` is bijective
    intro h
    constructor
    · -- `f` is injective
      intro x1 x2 hx1x2
      obtain ⟨x, hx, hx'⟩ := h (f x1)
      have hxx1 : x1 = x
      · apply hx'
        rfl
      have hxx2 : x2 = x
      · apply hx'
        rw [hx1x2]
      calc x1 = x := by rw [hxx1]
        _ = x2 := by rw [hxx2]
    · -- `f` is surjective
      intro y
      obtain ⟨x, hx, hx'⟩ := h y
      use x

-- Function composition
def comp {X Y Z} (f : X → Y) (g : Y → Z) (x : X) : Z := g (f x)

def f (a : ℝ) : ℝ := a + 3
def g (b : ℝ) : ℝ := 2 * b
def h (c : ℝ) : ℝ := 2 * c + 6

-- \ o, \ circ, \ comp -> ∘
example : g ∘ f = h := by
  ext x
  calc (g ∘ f) x = g (f x) := by rfl
    _ = 2 * (x + 3) := by rfl
    _ = 2 * x + 6 := by ring
    _ = h x := by rfl

def id2 {X} (x : X) : X := x

def s2 (x : ℝ) : ℝ := 5 - x

example : s2 ∘ s2 = id2 := by
  ext x
  dsimp [s2]
  dsimp [id2]
  ring

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rfl
      _ = f x := by apply hg
      _ = f (id x) := by rfl
  · -- prove `f ∘ g = id`
    ext y
    apply hg

theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl

theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  constructor
  · apply exists_inverse_of_bijective
  · intro h
    obtain ⟨g, H⟩ := h
    apply bijective_of_inverse H
