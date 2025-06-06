import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
theorem triangle_area :∀ (a b c d: Point), (coll a b d) ∧ (triangle a b c) ∧ ((∠c:d:a = ∟) ∨ (∠c:d:b = ∟)) → (△a:b:c).area = |(c─d)| * |(a─b)| := by
  sorry

/--5. If two altitudes of a triangle are equal, then the triangle is isosceles.-/
theorem Numina_Geometry_557 :
  ∀ (a b c d e : Point),
    (triangle a b c) ∧
    coll b c d ∧
    coll a c e ∧
    ∠ a:e:b = ∟ ∧
    ∠ a:d:b = ∟ ∧ e ≠ a ∧ d ≠ b ∧
    (|(a─d)| = |(b─e)|)
    → isoTriangle c a b := by
    euclid_intros
    euclid_assert triangle c a b
    euclid_assert ∠ b:e:a = ∠ a:e:b
    euclid_apply triangle_area c a b e
    euclid_apply triangle_area c b a d
    --euclid_assert |(b─e)| * |(c─a)| = |(a─d)| * |(c─b)|
    euclid_finish
