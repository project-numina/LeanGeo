import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle

open LeanGeo
namespace LeanGeo
theorem angleBisector_opposingsides : ∀ (A B C I : Point) (AI : Line), (distinctPointsOnLine A I AI)∧ triangle A B C ∧ ∠ I:A:B = ∠ I:A:C →  B.opposingSides C AI := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_finish

theorem opposingsides_inside_triangle :  ∀ (A B C I : Point) (AB BC CA AI BI CI : Line), (formTriangle A B C AB BC CA) ∧ (distinctPointsOnLine B I BI) ∧ (distinctPointsOnLine C I CI) ∧ A.opposingSides C BI ∧ B.opposingSides C AI → insideTriangle I A B C AB BC CA:= by
  euclid_intros
  sorry

theorem quadrilateral_line_from_side_sameside : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), formQuadrilateral A B C D AB BC CD DA ∧ distinctPointsOnLine E F EF ∧ between B E C ∧ between A F D → A.sameSide B EF := by
  sorry
theorem perp_foot: ∀ (A B C: Point) (l : Line), ¬ A.onLine l ∧ distinctPointsOnLine B C l ∧ ∠A:B:C = ∟ → foot A B l:= by
  euclid_intros
  euclid_apply angle_between_transfer
  euclid_finish

theorem eqAngle_sameSide_coll : ∀ (A B C D : Point)(AB: Line), distinctPointsOnLine A B AB ∧ ∠A:B:C = ∠A:B:D  ∧ C.sameSide D AB → coll B C D := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem eqAngle_perp_coll : ∀ (A B C D : Point), (A ≠ B) ∧ ∠A:B:D= ∟ ∧ ∠ A:B:C = ∟ → coll B C D := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  by_cases C.sameSide D AB
  · -- Case 1: C and D are on the same side of AB.
    -- Since ∠A:B:C = ∠A:B:D = 90, and C, D are on the same side of AB, the rays BC and BD must coincide.
    euclid_apply sameSide_eqAngle_coll A B C D AB
    euclid_finish
  · -- Case 2: C and D are not on the same side of AB.
    -- Since neither C nor D can be on the line AB (as the angle would be 0 or 180, not 90),
    -- they must be on opposite sides.
    by_cases C.opposingSides D AB
    · -- We construct a point C_prime that extends the line segment CB through B.
      euclid_apply line_from_points B C as BC
      euclid_apply extend_point BC C B as C_prime
      -- The angles ∠A:B:C and ∠A:B:C_prime are supplementary.
      have h_supp : ∠A:B:C + ∠A:B:C_prime = ∟ + ∟ := by
        have h_not_coll_abc : ¬ coll A B C := by
          by_contra h_coll
          euclid_finish
        euclid_apply supplementaryAngle_line A C B C_prime
        euclid_finish
      -- Since ∠A:B:C = 90°, it follows that ∠A:B:C_prime = 90°.
      have h_eq_angle : ∠A:B:C_prime = ∟ := by
        euclid_finish
      -- Now ∠A:B:D = 90° and ∠A:B:C_prime = 90°.
      -- C and D are on opposite sides of AB. By construction, C and C_prime are on opposite sides of AB.
      -- Therefore, D and C_prime must be on the same side of AB.
      have h_sameside : D.sameSide C_prime AB := by
        euclid_finish
      -- Since D and C_prime are on the same side of AB and form the same angle with the line AB at point B,
      -- the points B, D, C_prime must be collinear.
      have h_coll_BDC_prime : coll B D C_prime := by
        euclid_apply sameSide_eqAngle_coll A B D C_prime AB
        euclid_finish
      -- By construction, B, C, C_prime are collinear.
      -- Since D lies on the line defined by B and C_prime, and C also lies on it, B, C, D must be collinear.
      euclid_assert coll B C C_prime
      euclid_finish
    · -- This case is ¬(C.sameSide D AB) ∧ ¬(C.opposingSides D AB).
      -- This implies one of the points is on the line AB, which contradicts the angles being 90 degrees.
      -- Thus this case is impossible.
      euclid_finish

end LeanGeo
