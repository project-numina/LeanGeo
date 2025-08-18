import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem cyclic_collinearity_from_exterior_angle :
  ∀ (A B C D E F : Point) (AB BC CD DA : Line) (Ω : Circle),
    cyclicQuadrilateral A B C D AB BC CD DA Ω ∧
    between A B E ∧
    A.sameSide F CD ∧
    ∠ E:B:C = ∠ F:D:C
  → coll A D F := by
  euclid_intros
  -- Step 1: Establish that the exterior angle of the cyclic quadrilateral at vertex B
  -- is equal to the interior opposite angle at vertex D.
  have h_exterior_eq_interior_opposite : ∠ E:B:C = ∠ A:D:C := by
    -- In a cyclic quadrilateral, the sum of opposite angles is 180 degrees.
    have h_cyclic_angles_sum_180 : ∠ A:B:C + ∠ A:D:C = ∟ + ∟ := by
      euclid_apply cyclic_property A B C D AB BC CD DA Ω
      euclid_finish

    -- Angles on the straight line ABE at point B also sum to 180 degrees.
    have h_supplementary_angles : ∠ A:B:C + ∠ E:B:C = ∟ + ∟ := by
      -- We need to ensure that C is not on the line defined by A, B, E.
      -- This is guaranteed by `formQuadrilateral`, which implies `triangle A B C`.
      have h_not_coll_ABC : ¬ coll A B C := by euclid_finish
      euclid_apply supplementaryAngle_line C A B E
      euclid_finish

    -- From the two sum-to-180 equations, we deduce the equality.
    euclid_finish

  -- Step 2: Use the premise ∠ E:B:C = ∠ F:D:C and the result from Step 1.
  have h_target_angles_eq : ∠ A:D:C = ∠ F:D:C := by
    euclid_finish

  -- Step 3: Use the property that if two angles sharing a vertex and an arm are equal,
  -- and their other endpoints are on the same side of the shared arm, then the three
  -- points defining the other arms are collinear.
  have h_commutative_angle1 : ∠ C:D:A = ∠ A:D:C := by euclid_finish
  have h_commutative_angle2 : ∠ C:D:F = ∠ F:D:C := by euclid_finish
  have h_final_angle_eq : ∠ C:D:A = ∠ C:D:F := by euclid_finish
  euclid_apply eqAngle_sameSide_coll C D A F CD
  euclid_finish