import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--5. If two altitudes of a triangle are equal, then the triangle is isosceles.-/
theorem Numina_Geometry_557 :
  ∀ (A B C D E: Point) (AB BC CA : Line),
    (formTriangle A B C AB BC CA) ∧
    foot A D BC ∧ foot B E CA ∧
    (|(A─D)| = |(B─E)|)
    → isoTriangle C A B := by
  euclid_intros

  -- Calculate area using both altitudes
  -- Area(△ABC) = |(A─D)| * |(B─C)| / 2  (altitude from A to BC)
  have h_area1 : (△A:B:C).area = |(A─D)| * |(B─C)| / 2 := by
    euclid_apply triangle_area_foot A B C D BC
    euclid_finish

  -- Area(△ABC) = |(B─E)| * |(A─C)| / 2  (altitude from B to AC)
  have h_area2 : (△A:B:C).area = |(B─E)| * |(A─C)| / 2 := by
    euclid_apply triangle_area_foot B A C E CA
    euclid_finish

  -- Since the areas are equal and the altitudes are equal, the bases must be equal
  have h_equal_sides : |(B─C)| = |(A─C)| := by
    have h_eq : |(A─D)| * |(B─C)| / 2 = |(B─E)| * |(A─C)| / 2 := by
      rw [h_area1] at h_area2
      linarith

    -- Given that |(A─D)| = |(B─E)| and both are positive
    have h_altitudes_pos : |(A─D)| > 0 ∧ |(B─E)| > 0 := by
      euclid_finish

    have h_altitudes_eq : |(A─D)| = |(B─E)| := by
      euclid_finish

    -- From |(A─D)| * |(B─C)| = |(B─E)| * |(A─C)| and |(A─D)| = |(B─E)| > 0
    have h_bases_eq : |(B─C)| = |(A─C)| := by
      have h1 : |(A─D)| * |(B─C)| = |(B─E)| * |(A─C)| := by linarith
      rw [h_altitudes_eq] at h1
      have h2 : |(A─D)| > 0 := h_altitudes_pos.left
      have h3 : |(A─C)| > 0 := by euclid_finish
      have h4 : |(B─C)| > 0 := by euclid_finish
      euclid_finish

    exact h_bases_eq

  -- Now prove the triangle is isosceles using the equal side lengths
  euclid_apply eqSide_eqAngle C A B
  euclid_finish
