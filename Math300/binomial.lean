import Mathlib

open Finset
open scoped BigOperators
-- project with Mitchell Glassner & Justin Bernal
-- proving the binomial theorem by induction:

-- use the induction hypothesis to replace (x+y)^n by the binomial sum
-- multiply that whole sum by (x+y).
-- distribute, so each term becomes one ... * x part and one ... * y part and split into two sums
-- reindex them so matching powers line up
-- combine matching terms using pascal’s identity
-- choose n (k+1) + choose n k = choose (n+1) (k+1)
-- put back the first and last terms to find the full binomial sum for n+1
theorem binomial_pascal_real (x y : ℝ) : ∀ n : ℕ, (x + y)^n =
  (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * x^(n - k) * y^k)
  -- base case: n = 0
  -- left side is (x + y)^0 = 1
  -- right side is a sum over range 1, so only k = 0
  -- choose 0 0 * x^0 * y^0 = 1
  | 0 => by simp
  -- inductive step: assume the formula is true for n,
  -- and prove it for n+1.
  -- rewrite (x+y)^(n+1) as (x+y)^n * (x+y),
  -- then replace (x+y)^n using the induction hypothesis
  | n + 1 => by
      rw [pow_succ, binomial_pascal_real x y n]
      -- rewrite (x+y)^(n+1) as (x+y)^n (x+y),
      -- then replace (x+y)^n using the induction hypothesis
      calc
        (∑ k ∈ range (n + 1), (Nat.choose n k : ℝ) * x^(n - k) * y^k) * (x + y)
        = ∑ k ∈ range (n + 1), ((Nat.choose n k : ℝ) * x^(n + 1 - k) * y^k
            + (Nat.choose n k : ℝ) * x^(n - k) * y^(k + 1)) := by
            -- distribute multiplication by (x+y) across the sum
            -- so sum(...) * (x+y) becomes sum(... * (x+y))
            rw [Finset.sum_mul] -- distributes multiplication over a finite sum
            apply Finset.sum_congr rfl -- "indexing set is same, so summands are equal term-by-term”
            intro k hk
            have hk' : k < n + 1 := by
              simpa using hk
            have h1 : n + 1 - k = (n - k) + 1 := by
              omega
            rw [h1, pow_succ, pow_succ]
            ring
        _ = (∑ k ∈ range (n + 1), (Nat.choose n k : ℝ) * x^(n + 1 - k) * y^k)
            + (∑ k ∈ range (n + 1), (Nat.choose n k : ℝ) * x^(n - k) * y^(k + 1)) := by
            rw [Finset.sum_add_distrib] -- turns ∑ (A_k + B_k) into (∑ A_k) + (∑ B_k)
        _ = (x^(n + 1) + ∑ k ∈ range n, (Nat.choose n (k + 1) : ℝ) * x^(n - k) * y^(k + 1))
            + ((∑ k ∈ range n, (Nat.choose n k : ℝ) * x^(n - k) * y^(k + 1))
            + y^(n + 1)) := by
            rw [Finset.sum_range_succ', Finset.sum_range_succ]
            simp [Nat.choose_zero_right, Nat.choose_self, add_assoc, add_left_comm, add_comm]
        _ = x^(n + 1) + (∑ k ∈ range n, ((Nat.choose n (k + 1) : ℝ) + (Nat.choose n k : ℝ))
            * x^(n - k) * y^(k + 1)) + y^(n + 1) := by
            -- combine the two middle sums term-by-term
            rw [← add_assoc, add_assoc (x^(n + 1))]
            congr 2 -- “the outer structure matches, now prove the relevant inner part is equal”
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            ring
        _ = x^(n + 1) + (∑ k ∈ Finset.range n, (Nat.choose (n + 1) (k + 1) : ℝ) *
            x^(n - k) * y^(k + 1)) + y^(n + 1) := by
            congr 2
            apply Finset.sum_congr rfl
            intro k hk
            have hchoose : ((Nat.choose n (k + 1) : ℝ) + (Nat.choose n k : ℝ))
              = (Nat.choose (n + 1) (k + 1) : ℝ) := by
              -- Nat.choose_succ_succ is Pascal's rule
              norm_num [Nat.choose_succ_succ, add_comm] -- Pascal's rule for binomial coef, simp
            rw [hchoose]
        _ = ∑ k ∈ range (n + 2),
            (Nat.choose (n + 1) k : ℝ) * x^((n + 1) - k) * y^k := by
            -- rebuild the full binomial sum for n+1
            -- the middle sum gives the terms 1 through n,
            -- x^(n+1) is the k=0 term,
            -- and y^(n+1) is the k=n+1 term
            rw [Finset.sum_range_succ]
            rw [Finset.sum_range_succ']
            simp [Nat.choose_zero_right, Nat.choose_self, add_left_comm, add_comm]
