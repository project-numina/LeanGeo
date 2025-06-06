import SystemE
import LeanGeo
import LeanGeo.Evan

namespace LeanGeo

theorem circumcenter_acute_inside : ∀ (A B C O: Point) (AB BC CA : Line),
  (formAcuteTriangle A B C AB BC CA) ∧
  (circumCentre O A B C) →
  insideTriangle O A B C AB BC CA := by
  sorry

theorem orthocenter_acute_inside : ∀ (A B C H: Point) (AB BC CA : Line),
  (formAcuteTriangle A B C AB BC CA) ∧
  (orthoCentre H A B C) →
  insideTriangle H A B C AB BC CA := by
  sorry
theorem circumcircle_circumcenter: ∀ (A B C O: Point) (Ω: Circle),
  (circumCentre O A B C) ∧
  (circumCircle Ω A B C) →
  O.isCentre Ω := by
  sorry

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
