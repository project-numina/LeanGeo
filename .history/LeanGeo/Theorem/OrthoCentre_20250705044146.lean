import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Circle
import LeanGeo.Theorem.CirclePosition
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Area
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.Construction
import LeanGeo.Theorem.Parallel
import LeanGeo.Theorem.Trigonometry

open LeanGeo Real
namespace LeanGeo

theorem triangle_two_foot_intersects : ∀ (A B C D E : Point) (AB BC CA AD BE: Line), formTriangle A B C AB BC CA ∧ foot A D BC ∧ foot B E CA ∧ distinctPointsOnLine A D AD ∧ distinctPointsOnLine B E BE → AD.intersectsLine BE := by
  euclid_intros
  by_contra
  euclid_assert perpLine AD BC
  euclid_apply perpLine_parallel_perpLine AD BC BE
  euclid_apply perpLine_parallel_perpLine BE CA AD
  euclid_assert ∠E:B:C = ∟
  by_cases E = C
  · euclid_finish
  · euclid_apply triangle_angleSum E B C
    euclid_apply triangle_anglePositive E B C
    euclid_finish

theorem foot_unique: ∀ (c h g: Point) (AB : Line), foot c h AB ∧ foot c g AB → h = g := by
  euclid_intros
  by_contra
  have h1: ∠c:h:g = ∟ := by
    euclid_finish
  have h2: ∠c:g:h = ∟ := by
    euclid_finish
  have h3: triangle c g h := by
    euclid_finish
  euclid_apply triangle_angleSum c g h
  euclid_apply triangle_anglePositive c g h
  euclid_finish

theorem two_foot_cyclic : ∀ (A B C D E : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ foot A D BC ∧ foot B E CA → |(C─D)| * |(C─B)| =|(C─E)| * |(C─A)|:=  by
  euclid_intros
  by_cases ∠B:C:A = ∟
  · have h1: (E = C) ∧ (D = C) := by
      euclid_apply foot_unique B C E CA
      euclid_apply foot_unique A C D BC
      euclid_finish
    euclid_finish
  · have h2: ∠ A:C:D = ∠B:C:E := by
      by_cases ∠B:C:A < ∟
      · euclid_apply acute_angle_foot_equal A C B D BC
        euclid_apply acute_angle_foot_equal B C A E CA
        euclid_finish
      · have h3: between B C D := by
          euclid_apply o
        sorry
    euclid_apply similar_AA D C A E C B
    euclid_finish

theorem exists_orthocenter: ∀ (A B C D E F: Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ foot A D BC ∧ foot B E CA ∧ foot C F AB → ∃ (H : Point), orthoCentre H A B C D E F AB BC CA:= by
  euclid_intros
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points B E as BE
  euclid_apply triangle_two_foot_intersects A B C D E AB BC CA AD BE
  euclid_apply intersection_lines AD BE as H
  use H
  have h1: |(A─F)| * |(B─D)| * |(C─E)| = |(B─F)| * |(C─D)| * |(A─E)| := by
    have h11: |(B─D)| = |(A─B)| * sin (∠A:B:C) := by
      sorry
    have h12: |(B─D)| = |(A─B)| * sin (∠A:B:C) := by
      sorry
    have h13: |(B─D)| = |(A─B)| * sin (∠A:B:C) := by
      sorry
    have h14: |(B─D)| = |(A─B)| * sin (∠A:B:C) := by
      sorry
    have h15: |(B─D)| = |(A─B)| * sin (∠A:B:C) := by
      sorry
    have h16: |(B─D)| = |(A─B)| * sin (∠A:B:C) := by
      sorry
    sorry

  have h2: coll C H F := by
    sorry
  euclid_finish
