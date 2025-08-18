import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/-- Thales's Theorem (converse): In a Triangle $A B C$, let $M$ be the MidPoint of the side $B C$. If the length of the median $A M$ is equal to half the length of the side $B C$ (i.e., $|(A-M)| = |(B-M)|$), prove that the Triangle is a right-angled Triangle at vertex $A$.-/
theorem median_is_half_side_implies_right_triangle:
  ∀ (A B C M : Point),
    Triangle A B C ∧
    MidPoint B M C ∧
    |(A─M)| = |(B─M)|
    → ∠ B:A:C = ∟ := by
    euclid_intros
    -- From the MidPoint definition, we know |(B─M)| = |(M─C)|.
    -- Combined with the hypothesis |(A─M)| = |(B─M)|, we get |(A─M)| = |(M─C)|.
    have h_AM_eq_CM : |(A─M)| = |(M─C)| := by
      euclid_finish

    -- In Triangle AMB, the sides AM and BM are equal, so it is an isosceles triangle.
    -- By `eq_sides_imp_eq_angles`, the base angles are equal.
    -- The SMT solver can prove the side conditions `triangle A M B` and `A ≠ B` from the premises.
    have h_angle_AMB_eq : ∠M:A:B = ∠A:B:M := by
      euclid_apply eq_sides_imp_eq_angles M A B
      euclid_finish

    -- Similarly, in Triangle AMC, sides AM and CM are equal, making it isosceles.
    have h_angle_AMC_eq : ∠M:A:C = ∠A:C:M := by
      euclid_apply eq_sides_imp_eq_angles M A C
      euclid_finish

    -- The sum of the angles in the main Triangle ABC is 180 degrees (∟ + ∟).
    have h_sum_ABC : ∠A:B:C + ∠B:C:A + ∠C:A:B = ∟ + ∟ := by
      euclid_apply triangle_angles_sum A B C
      euclid_finish

    -- Since M lies on the segment BC, the angle at vertex A, ∠B:A:C, is the sum of ∠B:A:M and ∠M:A:C.
    have h_sum_BAC : ∠B:A:M + ∠M:A:C = ∠B:A:C := by
      euclid_apply line_from_points B C as BC
      euclid_apply between_imp_angles_sum A B M C
      euclid_finish

    -- Also, because M is on the line segment BC, ∠A:B:M is the same as ∠A:B:C, and ∠A:C:M is the same as ∠B:C:A.
    have h_collinear_angles : ∠A:B:M = ∠A:B:C ∧ ∠A:C:M = ∠B:C:A := by
      euclid_apply line_from_points B C as BC
      euclid_apply coll_angles_eq B M C A
      euclid_finish

    -- Using the angle equalities from the isosceles triangles and the angle sum properties,
    -- we can substitute into the main Triangle angle sum equation:
    -- ∠A:B:C + ∠B:C:A + ∠B:A:C = ∟ + ∟
    -- (becomes) ∠A:B:M + ∠A:C:M + ∠B:A:C = ∟ + ∟
    -- (becomes) ∠M:A:B + ∠M:A:C + ∠B:A:C = ∟ + ∟
    -- (becomes) ∠B:A:C + ∠B:A:C = ∟ + ∟
    -- which implies ∠B:A:C = ∟. The SMT solver handles this deduction.
    euclid_finish
