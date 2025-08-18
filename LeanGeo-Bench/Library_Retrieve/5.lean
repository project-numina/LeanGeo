import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library5 :
  ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (InsideTriangle O A B C AB BC CA) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_apply insideTriangle_angles_sum_eq_fullAngle A B C O AB BC CA
  euclid_apply line_from_points O C as OC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O A as OA
  euclid_apply isoTriangle_imp_eq_angles O A C
  euclid_apply isoTriangle_imp_eq_angles O C B
  euclid_apply triangle_angles_sum A O C
  euclid_apply triangle_angles_sum C O B
  euclid_finish
