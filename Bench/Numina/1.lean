import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

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
    sorry
