import SystemE
import LeanGeo

namespace LeanGeo

theorem diameter_rightAngle' : ∀ (a b c o: Point) (C: Circle), (diameter a b o C) ∧(o.isCentre C)∧ (c.onCircle C) ∧ (c ≠ a) ∧ (c ≠ b) → ∠ a:c:b = ∟ := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  euclid_apply line_from_points c a as CA
  euclid_assert between a o b
  euclid_apply line_from_points a b as ab
  euclid_assert isoTriangle o a c
  euclid_assert isoTriangle o b c
  euclid_apply isoTriangle_eqAngle o a c
  euclid_apply isoTriangle_eqAngle o b c
  euclid_assert triangle a b c
  euclid_apply triangle_angleSum a b c
  euclid_assert ∠o:a:c = ∠b:a:c
  euclid_assert ∠o:b:c = ∠a:b:c
  euclid_assert ∠a:c:b = ∠ a:c:o + ∠o:c:b
  euclid_finish
