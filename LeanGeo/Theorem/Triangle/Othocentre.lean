import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Perpendicular
import LeanGeo.Theorem.Triangle.Basic
import LeanGeo.Theorem.Metrics.Area

set_option maxHeartbeats 0
open Elements.Book1
namespace LeanGeo

theorem triangle_two_altitudes_intersect : ∀ (A B C D E : Point) (AB BC CA AD BE: Line), formTriangle A B C AB BC CA ∧ Foot A D BC ∧ Foot B E CA ∧ distinctPointsOnLine A D AD ∧ distinctPointsOnLine B E BE → AD.intersectsLine BE := by
  euclid_intros
  by_contra
  euclid_assert PerpLine AD BC
  euclid_apply perp_parallel_imp_perp AD BC BE
  euclid_apply perp_parallel_imp_perp BE CA AD
  euclid_assert ∠E:B:C = ∟
  by_cases E = C
  · euclid_finish
  · euclid_apply triangle_angles_sum E B C
    euclid_apply triangle_angle_positive E B C
    euclid_finish


theorem eq_feet_if_perpLine: ∀ (A B H : Point) (l : Line), (Foot A H l) ∧ (Coll A B H) ∧ (B ≠ H) → Foot B H l := by
  euclid_intros
  euclid_apply line_from_points A H as AH
  euclid_finish


theorem triangle_two_feet_eq_pow : ∀ (A B C D E : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ Foot A D BC ∧ Foot B E CA → |(C─D)| * |(C─B)| =|(C─E)| * |(C─A)|:=  by
  euclid_intros
  by_cases ∠B:C:A = ∟
  · have h1: (E = C) ∧ (D = C) := by
      euclid_apply foot_unique B C E CA
      euclid_apply foot_unique A C D BC
      euclid_finish
    euclid_finish
  · have h2: ∠ A:C:D = ∠B:C:E := by
      by_cases ∠B:C:A < ∟
      · euclid_apply acuteAngle_foot_eq_angles A C B D BC
        euclid_apply acuteAngle_foot_eq_angles B C A E CA
        euclid_finish
      · have h3: between B C D := by
          euclid_apply obtuseTriangle_foot_between A C B D BC
          euclid_finish
        have h4: between A C E := by
          euclid_apply obtuseTriangle_foot_between B C A E CA
          euclid_finish
        have h5: ∠ A:C:D + ∠A:C:B = ∟ + ∟ := by
          euclid_apply coll_angles_eq
          euclid_finish
        have h6: ∠ B:C:E + ∠B:C:A = ∟ + ∟ := by
          euclid_apply coll_angles_eq
          euclid_finish
        euclid_finish
    euclid_apply similar_AA D C A E C B
    euclid_finish

theorem exists_orthocentre: ∀ (A B C D E F: Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ Foot A D BC ∧ Foot B E CA ∧ Foot C F AB → ∃ (H : Point), Orthocentre H A B C D E F AB BC CA:= by
  euclid_intros
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points B E as BE
  euclid_apply triangle_two_altitudes_intersect A B C D E AB BC CA AD BE
  euclid_apply intersection_lines AD BE as H
  use H
  have h1: |(A─F)| * |(B─D)| * |(C─E)| = |(B─F)| * |(C─D)| * |(A─E)| := by
    have h11: |(C─D)| * |(C─B)| =|(C─E)| * |(A─C)| := by
      euclid_apply triangle_two_feet_eq_pow A B C D E AB BC CA
      euclid_finish
    have h12: |(A─E)| * |(A─C)| =|(A─F)| * |(B─A)| := by
      euclid_apply triangle_two_feet_eq_pow B C A E F BC CA AB
      euclid_finish
    have h13: |(B─F)| * |(B─A)| =|(B─D)| * |(C─B)| := by
      euclid_apply triangle_two_feet_eq_pow C A B F D CA AB BC
      euclid_finish
    have h14: |(C─D)| * |(C─B)| * (|(A─E)| * |(A─C)|) * (|(B─F)| * |(B─A)|) = |(C─E)| * |(A─C)| * |(A─F)| * |(B─A)| * |(B─D)| * |(C─B)| := by
      rw[h11,h12,h13]
      linarith
    have h15: |(A─F)| * |(B─D)| * |(C─E)| * (|(C─B)| * |(A─C)| * |(B─A)|) = |(B─F)| * |(C─D)| * |(A─E)| * (|(C─B)| * |(A─C)| * |(B─A)|):=  by
      calc
      _ = |(C─D)| * |(C─B)| * (|(A─E)| * |(A─C)|) * (|(B─F)| * |(B─A)|)  := by linarith
      _ = |(C─E)| * |(A─C)| * |(A─F)| * |(B─A)| * |(B─D)| * |(C─B)|  := by rw [h14]
      _ = _ := by linarith
    have h_nonzero: (|(C─B)| * |(A─C)| * |(B─A)|) ≠ 0 := by euclid_finish
    apply (mul_left_inj' h_nonzero).mp
    linarith
  have h2: Coll C H F := by
    euclid_apply CevaTheorem_converse B C A E F D H
    euclid_finish
  euclid_finish

theorem orthocentre_of_rightTriangle:
  ∀ (A B C H D E F : Point) (AB BC CA : Line),
    RightTriangle A B C →
    Orthocentre H A B C D E F AB BC CA →
    H = A := by
  euclid_intros
  have h1: (E = A) ∧ (F = A) := by
      euclid_apply foot_unique B A E CA
      euclid_apply foot_unique C A F AB
      euclid_finish
  euclid_finish

theorem orthocentre_of_acuteTriangle_insideTriangle:
  ∀ (A B C H D E F : Point) (AB BC CA: Line),
    (formAcuteTriangle A B C AB BC CA) ∧ (Orthocentre H A B C D E F AB BC CA)
    → InsideTriangle H A B C AB BC CA := by
  euclid_intros
  -- An acute Triangle has all angles less than a right angle.
  -- The orthocenter H is the intersection of the altitudes AD, BE, CF.
  -- To prove H is inside Triangle ABC, we must show H lies on the same side of each side as the opposite vertex.
  -- This is equivalent to showing that H lies on the interior segments of the altitudes, i.e., between A and D, B and E, and C and F.

  -- First, because the Triangle is acute, the feet of the altitudes (D, E, F) lie between the vertices on each side.
  have h_between_BDC : between B D C := by
    euclid_apply acuteTriangle_foot_between A B C D BC
    euclid_finish
  have h_between_AEC : between A E C := by
    euclid_apply acuteTriangle_foot_between B C A E CA
    euclid_finish
  have h_between_AFB : between A F B := by
    euclid_apply acuteTriangle_foot_between C A B F AB
    euclid_finish
  euclid_finish

theorem orthocentre_of_acuteTriangle_insideTriangle_transfer : ∀(A B C D E F H: Point) (AB BC CA AH BH: Line), AcuteTriangle A B C ∧  distinctPointsOnLine A H AH ∧ distinctPointsOnLine B H BH ∧ Orthocentre H A B C D E F AB BC CA → Orthocentre C A B H E D F AB BH AH:= by
  euclid_intros
  have h1 : InsideTriangle H A B C AB BC CA := by
    euclid_apply orthocentre_of_acuteTriangle_insideTriangle A B C H D E F AB BC CA
    euclid_finish
  euclid_apply eq_feet_if_perpLine C H F AB
  euclid_finish

theorem acuteTriangle_power_of_orthocenter :
  ∀ (A B C D E F H : Point) (AB BC CA : Line),
    AcuteTriangle A B C ∧
    Orthocentre H A B C D E F AB BC CA
    → |(A─H)| * |(H─D)| = |(B─H)| * |(H─E)|  := by
  euclid_intros
  have h1 : InsideTriangle H A B C AB BC CA := by
    euclid_apply orthocentre_of_acuteTriangle_insideTriangle A B C H D E F AB BC CA
    euclid_finish
  euclid_apply line_from_points B H as BH
  euclid_apply line_from_points A H as AH
  have h1: Orthocentre C A B H E D F AB BH AH := by
    euclid_apply orthocentre_of_acuteTriangle_insideTriangle_transfer A B C D E F H AB BC CA AH BH
    euclid_finish
  euclid_apply triangle_two_feet_eq_pow A B H E D AB BH AH
  euclid_finish

end LeanGeo
