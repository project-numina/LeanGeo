import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library5 :
  ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (insideTriangle O A B C AB BC CA) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_apply self_fullAngle A B C O AB BC CA
  euclid_apply line_from_points O C as OC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O A as OA
  euclid_apply isoTriangle_eqAngle O A C
  euclid_apply isoTriangle_eqAngle O C B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum C O B
  euclid_finish
