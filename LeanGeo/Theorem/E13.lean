import SystemE
import LeanGeo

open SystemE
namespace LeanGeo

--Lemma 1.3 (Self-full angle). If A, B, C are distinct points, then ∠A:O:C + ∠ C:O:B + ∠ B:O:A = ∟ + ∟ +  ∟ + ∟.
theorem self_fullAngle : ∀ (A B C O : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ insideTriangle O A B C AB BC CA → ∠A:O:C + ∠ C:O:B + ∠ B:O:A = ∟ + ∟ +  ∟ + ∟ := by
  euclid_intros
  euclid_apply triangle_angleSum A O B
  euclid_apply triangle_angleSum C O B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum A B C
  euclid_finish

--Theorem 1.3 (Inscribed Angle Theorem). If ∠A C B is inscribed in a circle, then it subtends an arc with measure 2∠A C B.
--Draw in O C. Set α = ∠A C O and β = ∠B C O, and let θ = α + β. Because A O = C O we have ∠O A C = ∠O C A = α, so ∠A O C = 180° − 2α. Similarly ∠B O C = 180° − 2β. Hence ∠A O B = 360° − [(180° − 2α) + (180° − 2β)] = 2θ.
theorem inscribed_angle_theorem_1:
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

theorem inscribed_angle_theorem:
  ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (O.sameSide C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  sorry

theorem circumcenter_inscribed_angle_complementary : ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (O.sameSide C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
  → ∠ O:B:A +  ∠ A:C:B= ∟ := by
  euclid_intros
  euclid_apply inscribed_angle_theorem A B C O AB BC CA Ω
  euclid_apply isoTriangle_eqAngle O A B
  euclid_apply triangle_angleSum O A B
  euclid_finish
