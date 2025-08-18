import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library1 : ∀ (a b c d o: Point) (O : Circle), a.onCircle O ∧ b.onCircle O ∧ c.onCircle O ∧ d.onCircle O ∧  o.isCentre O ∧ |(a─b)| = |(c─d)| → ∠a:o:b =∠ c:o:d := by
  euclid_intros
  by_cases h : a = b
  · euclid_assert c = d
    euclid_apply angle_coincide_zero b o
    euclid_apply angle_coincide_zero d o
    euclid_finish
  · -- Case a ≠ b
    euclid_assert c ≠ d
    by_cases h2 : coll a o b
    · euclid_assert between a o b
      euclid_assert |(a─b)| = |(a─o)| + |(o─b)|
      euclid_assert |(c─d)| = |(c─o)| + |(o─d)|
      euclid_apply triangle_ineqaulity_eql c d o
      euclid_finish
    · by_cases h3: coll c o d
      · euclid_apply triangle_ineqaulity_eql a b o
        euclid_finish
      · euclid_apply congruent_SSS a o b c o d
        euclid_finish
