import Mathlib

open scoped BigOperators

open Real

theorem lemma_d9rq9z (β : ℝ) (hβ : 0 < β ∧ β < 1)
  (m : ℕ) (hm : IsLeast {x | 0 < x ∧ x * β ≥ 1} m) :
  ∑ i ∈ Finset.Icc 1 m, ⌊(i * β)⌋ = ⌊(m * β)⌋ := by
sorry

theorem imo_2024_p1_v33 (k : ℤ) (n : ℕ) (hk : Even k) (hn : 0 < n) :
  ∃ m, ∑ i ∈ Finset.Icc 1 n, ⌊(i * k : ℚ)⌋ = m * n := by
  sorry

theorem imo_2024_p1_v111 (α : ℝ) (k : ℤ) (n : ℕ) (npos : n > 0) :
  ∑ i in Finset.Icc 1 n, ⌊i * (α + 2 * k)⌋ =
  ∑ i in Finset.Icc 1 n, ⌊i * α⌋ + k * n * (n + 1) := by
  sorry


/--
Determine all real numbers $\alpha$ such that, for every positive integer $n$, the integer
$$
\lfloor \alpha\rfloor + \lfloor2\alpha\rfloor + \cdots + \lfloor n\alpha\rfloor
$$
is a multiple of $n$.
(Note that $\lfloor z\rfloor$ denotes the greatest integer less than or equal to $z$.
For example, $\lfloor-\pi\rfloor = -4$ and $\lfloor2\rfloor = \lfloor2.9\rfloor = 2$.)

Solution: $\alpha$ is an even integer.
-/
theorem imo_2024_p1 :
    {(α : ℝ) | ∀ (n : ℕ), 0 < n → (n : ℤ) ∣ (∑ i in Finset.Icc 1 n, ⌊i * α⌋)}
    = {α : ℝ | ∃ k : ℤ, Even k ∧ α = k} := by
