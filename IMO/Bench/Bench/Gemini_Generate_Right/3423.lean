import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem parallelogram_angle_bisector_creates_isoceles:
  ∀ (A B C D E : Point) (AB BC CD DA AE : Line),
    Parallelogram A B C D AB BC CD DA ∧
    distinctPointsOnLine A E AE ∧
    E.onLine CD ∧ between C E D ∧
    ∠D:A:E = ∠E:A:B
    → |(D─E)| = |(A─D)| := by
  euclid_intros
  -- From the Parallelogram property, line AB is parallel to line CD. Since E is on line CD, AB is parallel to DE.
  have h_parallel : ¬ AB.intersectsLine CD := by
    euclid_finish
  -- Since AE is a transversal intersecting the parallel lines AB and CD (containing E),
  -- the alternate interior angles are equal.
  have h_alt_angles_eq : ∠ E:A:B = ∠ A:E:D := by
    -- We need to prove B and D are on opposite sides of the transversal AE.
    -- This follows from the properties of a parallelogram.
    euclid_apply parallel_imp_eq_alternateAngles AB CD AE A E B D
    euclid_finish
  -- We are given that AE bisects the angle ∠DAB.
  have h_bisect : ∠ D:A:E = ∠ E:A:B := by
    euclid_finish
  -- By transitivity from the angle bisection and the alternate interior angles,
  -- we show that two angles in Triangle ADE are equal.
  have h_base_angles_eq : ∠ D:A:E = ∠ A:E:D := by
    euclid_finish
  -- To apply the converse of the Isosceles Triangle Theorem, we must first show that A, D, E form a triangle.
  have h_tri_ADE : Triangle A D E := by
    -- In a parallelogram, vertex A cannot be on the line CD of the opposite side.
    -- Since D and E are on line CD, the points A, D, E cannot be collinear.
    euclid_finish
  -- In Triangle ADE, angles ∠DAE and ∠AED are equal.
  -- Therefore, the sides opposite these angles, DE and AD, must be equal in length.
  -- We apply the theorem that equal angles in a Triangle imply an isosceles triangle.
  -- The mapping is a=D, b=A, c=E. We need to prove `triangle D A E` and `∠D:A:E = ∠D:E:A`,
  -- which follows from our previous steps.
  euclid_apply isoTriangle_if_eq_angles D A E
  euclid_finish
