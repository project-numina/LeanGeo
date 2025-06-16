import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Circle
import LeanGeo.Theorem.CirclePosition
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.Construction
namespace LeanGeo

--Theorem 1.3 (Inscribed Angle Theorem). If ∠A C B is inscribed in a circle, then it subtends an arc with measure 2∠A C B.
--Draw in O C. Set α = ∠A C O and β = ∠B C O, and let θ = α + β. Because A O = C O we have ∠O A C = ∠O C A = α, so ∠A O C = 180° − 2α. Similarly ∠B O C = 180° − 2β. Hence ∠A O B = 360° − [(180° − 2α) + (180° − 2β)] = 2θ.
theorem inscribed_angle_theorem :
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

theorem incenter_inside : ∀ (A B C I : Point) (AB BC CA : Line), (formTriangle A B C AB BC CA) ∧ (inCentre I A B C) → insideTriangle I A B C AB BC CA := by
  euclid_intros
  euclid_apply line_from_points A I as AI
  euclid_apply line_from_points B I as BI
  euclid_apply line_from_points C I as CI
  euclid_apply angleBisector_opposingsides A B C I AI
  euclid_apply angleBisector_opposingsides C A B I CI
  euclid_apply angleBisector_opposingsides B C A I BI
  euclid_apply opposingsides_inside_triangle A B C I AB BC CA AI BI CI
  euclid_finish

theorem incenter_angle : ∀ (A B C I : Point), (triangle A B C) ∧ (inCentre I A B C) → ∠B:I:C = ∟ + ∠B:A:C / 2 := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A C as CA
  euclid_apply line_from_points B C as BC
  --euclid_assert formTriangle A B C AB BC CA
  euclid_apply incenter_inside A B C I AB BC CA
  --euclid_apply self_fullAngle A B C I AB BC CA
  euclid_apply triangle_angleSum I B C
  euclid_apply triangle_angleSum A B C
  --euclid_assert ∠A:B:C = 2 * ∠I:B:C
  --euclid_assert ∠A:C:B = 2 * ∠I:C:B
  euclid_finish


theorem circumcircle_circumcenter: ∀ (A B C O: Point) (Ω: Circle),
  (circumCentre O A B C) ∧
  (circumCircle Ω A B C) →
  O.isCentre Ω := by
  sorry

theorem circumcenter_inscribed_angle_complementary : ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (O.sameSide C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
  → ∠ O:B:A +  ∠ A:C:B= ∟ := by
  sorry
  --euclid_intros
  --euclid_apply inscribed_angle_theorem A B C O AB BC CA Ω
  --euclid_apply isoTriangle_eqAngle O A B
  --euclid_apply triangle_angleSum O A B
  --euclid_finish
/--
theorem circumcenter_orthocenter_eqAngle: ∀ (A B C O H : Point) (AB BC CA : Line)(Ω: Circle),
  (formAcuteTriangle A B C AB BC CA) ∧
  (circumCentre O A B C) ∧
  (circumCircle Ω A B C) ∧
  (orthoCentre H A B C) →
  ∠B:A:H = ∠C:A:O := by
  euclid_intros
  euclid_apply circumcenter_acute_inside A B C O AB BC CA
  euclid_apply orthocenter_acute_inside A B C H AB BC CA
  euclid_apply threePoints_existCircle A B C as Ω
  euclid_apply circumcircle_circumcenter A B C O Ω
  euclid_apply circumcenter_inscribed_angle_complementary C A B O CA AB BC Ω
  euclid_apply line_from_points A H as AH
  euclid_apply intersection_lines AH BC as D
  euclid_assert ∠B:D:A = ∟
  euclid_apply triangle_angleSum B D A
  euclid_assert ∠D:B:A = ∠C:B:A
  euclid_finish
--/
theorem exCentre_inCentre_coll : ∀ (A B C I J: Point), triangle A B C ∧ inCentre I A B C ∧ exCentre J A B C → between A I J := by
  sorry

theorem circumCentre_isCentre_circumCircle : ∀ (A B C O : Point) (Ω : Circle), triangle A B C ∧ circumCircle Ω A B C ∧ circumCentre O A B C → O.isCentre Ω := by
  euclid_intros
  sorry
