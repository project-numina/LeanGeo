import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library1 : ∀ (a b c d o: Point) (O : Circle), a.onCircle O ∧ b.onCircle O ∧ c.onCircle O ∧ d.onCircle O ∧  o.isCentre O ∧ |(a─b)| = |(c─d)| → ∠a:o:b =∠ c:o:d := by
  euclid_intros
  by_cases h : a = b
  · euclid_assert c = d
    euclid_apply coincident_angle_eq_zero b o
    euclid_apply coincident_angle_eq_zero d o
    euclid_finish
  · -- Case a ≠ b
    euclid_assert c ≠ d
    by_cases h2 : Coll a o b
    · euclid_assert between a o b
      euclid_assert |(a─b)| = |(a─o)| + |(o─b)|
      euclid_assert |(c─d)| = |(c─o)| + |(o─d)|
      euclid_apply between_if_sum c d o
      euclid_finish
    · by_cases h3: Coll c o d
      · euclid_apply between_if_sum a b o
        euclid_finish
      · euclid_apply congruentTriangles_SSS a o b c o d
        euclid_finish
