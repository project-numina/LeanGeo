import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem tangent_parallel_to_chord_collinear:
  ∀ (Ω : Circle) (L_AB L_T : Line) (O A B M T: Point),
    O.isCentre Ω ∧
    A.onCircle Ω ∧ B.onCircle Ω ∧ T.onCircle Ω ∧
    A ≠ B ∧
    midpoint A M B ∧
    distinctPointsOnLine A B L_AB ∧
    tangentAtPoint T O L_T Ω ∧
    (¬ L_AB.intersectsLine L_T)
    → coll O M T := by
  euclid_intros
  
  -- Case 1: O coincides with M. The collinearity is trivial.
  by_cases h_O_eq_M : O = M
  · euclid_finish

  -- Case 2: O is distinct from M.
  -- First, show that O is not on the chord line L_AB.
  have h_O_not_on_AB : ¬(O.onLine L_AB) := by
    by_contra h_O_on_AB
    -- If O is on L_AB, since O is the center and A,B are on the circle, O is the midpoint of AB.
    have h_O_is_midpoint : midpoint A O B := by
      euclid_finish
    -- We are given that M is the midpoint of AB.
    -- The midpoint of a segment is unique, which can be proven by line_ratio_unique.
    have h_O_must_be_M : O = M := by
      have h_between_O : between A O B := by euclid_finish
      have h_between_M : between A M B := by euclid_finish
      have h_ratio_O : |(A─O)| / |(O─B)| = 1 := by euclid_finish
      have h_ratio_M : |(A─M)| / |(M─B)| = 1 := by euclid_finish
      euclid_apply line_ratio_unique A B O M
      euclid_finish
    -- This contradicts our assumption that O is distinct from M.
    euclid_finish

  -- Since M is the midpoint of the chord AB and O is the center not on the chord line, OM is perpendicular to AB.
  have h_foot_OM_AB : foot O M L_AB := by
    euclid_apply chord_midpoint_foot O A B M Ω L_AB
    euclid_finish

  -- Construct the line L_OM through O and M.
  euclid_apply line_from_points O M h_O_eq_M as L_OM

  -- The foot property implies that L_OM is perpendicular to L_AB.
  have h_perp_OM_AB : perpLine L_OM L_AB := by
    use M
    constructor
    · euclid_finish
    · euclid_finish

  -- We are given that the tangent L_T is parallel to the chord L_AB.
  -- A line perpendicular to one of two parallel lines is perpendicular to the other.
  have h_perp_OM_T : perpLine L_T L_OM := by
    euclid_apply perpLine_parallel_perpLine L_AB L_OM L_T
    euclid_finish

  -- The tangent L_T at point T is perpendicular to the radius OT.
  have h_foot_OT_LT : foot O T L_T := by
    euclid_finish

  -- To construct the line L_OT, we need O ≠ T.
  have h_O_neq_T : O ≠ T := by
    euclid_finish
  
  euclid_apply line_from_points O T h_O_neq_T as L_OT

  -- The foot property implies that L_OT is perpendicular to L_T.
  have h_perp_OT_T : perpLine L_OT L_T := by
    use T
    constructor
    · euclid_finish
    · euclid_finish
  
  -- We now have two lines, L_OM and L_OT, both passing through O and perpendicular to L_T.
  -- The theorem `perp_same_line_coll` states that if two distinct lines from a point O are perpendicular
  -- to a third line L_T, then the three points O, M, T are collinear.
  euclid_apply perp_same_line_coll O M T L_T L_OM L_OT
  euclid_finish

end LeanGeo