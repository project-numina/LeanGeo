import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
set_option maxHeartbeats 0
/--2. Points E and $\mathrm{F}$ are the midpoints of sides BC and CD, respectively, of Rectangle $A B C D$. Prove that $A E&lt;2 E F$.-/
theorem Numina_Geometry_599 :
  ∀ (A B C D E F : Point) (AB BC CD DA : Line),
    Rectangle A B C D AB BC CD DA ∧
    MidPoint B E C ∧
    MidPoint C F D →
    |(A─E)| < |(E─F)| + |(E─F)| := by
  euclid_intros

  -- Establish that triangles ABE and ECF are right-angled triangles to use Pythagoras.
  have h_tri_ABE : RightTriangle B A E := by
    constructor
    · have h_tri : Triangle A B E := by euclid_finish
      euclid_finish
    · -- The angle ∠A:B:E is a right angle because ABCD is a Rectangle and E is on BC.
      have h_angle : ∠ A:B:C = ∟ := by euclid_finish
      have h_coll : Coll B E C := by euclid_finish
      euclid_finish
  have h_pyth_AE : |(A─E)| * |(A─E)| = |(A─B)| * |(A─B)| + |(B─E)| * |(B─E)| := by
    euclid_apply PythagoreanTheorem_point B A E
    euclid_finish

  have h_tri_ECF : RightTriangle C E F := by
    constructor
    · have h_tri : Triangle E C F := by euclid_finish
      euclid_finish
    · -- The angle ∠E:C:F is a right angle because ABCD is a rectangle, E is on BC, and F is on CD.
      have h_angle : ∠ B:C:D = ∟ := by euclid_finish
      euclid_finish
  have h_pyth_EF : |(E─F)| * |(E─F)| = |(E─C)| * |(E─C)| + |(C─F)| * |(C─F)| := by
    euclid_apply PythagoreanTheorem_point C E F
    euclid_finish

  -- Establish relations between side lengths.
  have h_AB_eq_DC : |(A─B)| = |(D─C)| := by
    -- In a rectangle, opposite sides are equal.
    have h_sides_eq : |(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)| := by
      euclid_apply rectangle_dignonals_equal A B C D AB BC CD DA
      euclid_finish
    euclid_finish

  have h_BE_eq_EC : |(B─E)| = |(E─C)| := by euclid_finish

  have h_DC_eq_2CF : |(D─C)| = 2 * |(F─C)| := by
    euclid_apply midpoint_half_len C D F
    euclid_finish

  have h_EC_gt_zero : |(E─C)| > 0 := by
    -- In a non-degenerate rectangle, B ≠ C. Since E is the midpoint, E ≠ C, so |(E-C)| > 0.
    euclid_finish

  -- The original inequality is equivalent to |(A─E)|² < 4 * |(E─F)|².
  -- By substituting the Pythagorean identities and side length relations, this becomes:
  -- |(A─B)|² + |(B─E)|² < 4 * (|(E─C)|² + |(C─F)|²)
  -- (2*|C─F|)² + |E─C|² < 4 * (|E─C|² + |C─F|²)
  -- 4*|C─F|² + |E─C|² < 4*|E─C|² + 4*|C─F|²
  -- which simplifies to |E─C|² < 4*|E─C|², or 0 < 3*|E─C|².
  -- This is true since |E─C| > 0. The SMT solver can verify this chain of reasoning.
  euclid_finish
