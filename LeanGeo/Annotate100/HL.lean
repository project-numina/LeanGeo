import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
theorem HL_congruent : ∀ (a b c d e f : Point) ,  rightTriangle a b c ∧ rightTriangle d e f ∧ |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| → (△a:b:c).congruent_test (△d:e:f) := by
  euclid_intros
  euclid_apply pythagorean_point a b c
  euclid_apply pythagorean_point d e f
  have h1 : |(a─b)| = |(d─e)| := by
    euclid_finish
  have h2 : |(b─c)| = |(e─f)| := by
    euclid_finish
  have h4 : |(e─f)| * |(e─f)| = |(d─e)| * |(d─e)| + |(d─f)| * |(d─f)| := by
    euclid_finish
  have h3 : |(b─c)| * |(b─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)| := by
    euclid_finish
  have h5 : |(a─c)| = |(d─f)| := by
    rw [h1, h2] at h3
    have h6 : |(a─c)| * |(a─c)| = |(d─f)| * |(d─f)| := by linarith
    have h7 : |(a─c)| > 0 := by euclid_finish
    have h8 : |(d─f)| > 0 := by euclid_finish
    sorry
  euclid_finish
