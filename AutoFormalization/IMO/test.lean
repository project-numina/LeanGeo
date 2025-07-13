import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
theorem amc12b_2002_p4 (n : ℕ) (h₀ : 0 < n) (h₁ : (1 /. 2 + 1 /. 3 + 1 /. 7 + 1 /. ↑n).den = 1) : n = 42 := by
  have h2 : (1 /. 2 + 1 /. 3 + 1 /. 7 + 1 /. n) = (41 * n + 42) / (42 * n) := by
    field_simp
    ring_nf
    have : 41 /. 42 * n * 42 = n * 41 := by
      ring_nf
    rw [this]
    ring
  rw [h2] at h₁
  have h3 : (41 * n + 42) / (42 * n : ℚ) = (41 * n + 42) / (42 * n : ℚ) := by rfl
  rw [h3] at h₁
  have h4 : (42 * n : ℚ) ∣ (41 * n + 42) := by
    have h5 : (41 * n + 42 : ℚ) = (41 * n + 42) / (42 * n : ℚ) * (42 * n : ℚ) := by
      field_simp
    rw [h5]
    apply mul_dvd_mul_right
    have h6 : (41 * n + 42) / (42 * n : ℚ) ∈ (ℤ : Type) := by
      have h7 : (41 * n + 42) / (42 * n : ℚ) = (41 * n + 42) / (42 * n : ℚ) := by rfl
      rw [h7] at h₁
      simpa using h₁
    norm_cast at h6
    exact Int.cast_dvd.mpr h6
  have h7 : n = 42 := by
    have h8 : (42 * n : ℤ) ∣ (41 * n + 42 : ℤ) := by
      norm_cast at h4
    have h9 : n ≤ 42 := by
      have h10 : (42 * n : ℤ) ∣ (41 * n + 42 : ℤ) := h8
      have h11 : (41 * n + 42 : ℤ) ≠ 0 := by
        omega
      have h12 : (42 * (n : ℤ) ≤ (41 * n + 42 : ℤ)) := by
        exact Int.le_of_dvd (by omega) h10
      omega
    interval_cases n <;> norm_num at h8 <;> omega
  exact h7
