import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--
In an isosceles triangle $ABC$ with $|(A-B)| = |(A-C)|$, let $I$ be the incenter.
Prove that triangle $IBC$ is also an isosceles triangle.
--/

theorem incenter_of_isosceles_triangle_is_isosceles :
  ∀ (A B C I : Point),
    isoTriangle A B C ∧
    inCentre I A B C
    → isoTriangle I B C := by
    euclid_intros

    -- Since triangle ABC is isosceles with |(A-B)| = |(A-C)|, its base angles are equal.
    have h_base_angles_eq : ∠ A:B:C = ∠ A:C:B := by
      euclid_apply isoTriangle_eqAngle A B C
      euclid_finish
    euclid_apply line_from_points A B as AB
    euclid_apply line_from_points B C as BC
    euclid_apply line_from_points C A as CA
    euclid_apply incenter_inside A B C I AB BC CA
    -- The incenter I bisects the angles at B and C. From the definition of inCentre, we have:
    -- ∠ I:B:A = ∠ I:B:C and ∠ I:C:A = ∠ I:C:B.
    -- Also, the SMT solver can deduce that ∠ A:B:C = ∠ A:B:I + ∠ I:B:C and ∠ A:C:B = ∠ A:C:I + ∠ I:C:B,
    -- because the incenter lies inside the triangle.
    -- Therefore, ∠ A:B:C = 2 * ∠ I:B:C and ∠ A:C:B = 2 * ∠ I:C:B.
    -- Since the full angles are equal, their halves must be equal too.
    have h_half_angles_eq : ∠ I:B:C = ∠ I:C:B := by
      euclid_finish

    -- To apply properties of triangle IBC, we must first prove it is a valid, non-degenerate triangle.
    -- Since I is the incenter of a non-degenerate triangle ABC, I must lie strictly inside it
    -- and thus cannot be collinear with B and C.
    have h_tri_IBC : triangle I B C := by
      euclid_finish

    -- Now we have a triangle IBC with two equal angles (∠I:B:C = ∠I:C:B).
    -- By the converse of the isosceles triangle theorem, the sides opposite these angles are equal.
    -- This will prove |(I-B)| = |(I-C)|.
    euclid_apply eqAngle_isoTriangle I B C

    -- From `triangle I B C` and `|(I-B)| = |(I-C)|`, the definition of `isoTriangle I B C` is satisfied.
    euclid_finish
