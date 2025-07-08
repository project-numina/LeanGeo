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
import LeanGeo.Theorem.Trianglometry

open LeanGeo
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

theorem exists_orthocenter: ∀ (A B C D E F: Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ foot A D BC ∧ foot B E CA ∧ foot C F AB → ∃ (H : Point), orthoCentre H A B C D E F AB BC CA:= by
  euclid_intros
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points B E as BE
  euclid_apply triangle_two_foot_intersects A B C D E AB BC CA AD BE
  euclid_apply intersection_lines AD BE as H
  use H
  have h1: |(A─F)| * |(B─D)| * |(C─E)| = |(B─F)| * |(C─D)| * |(A─E)| := by
    have h11: |(B─D)| =
  have h2: coll C H F := by
    sorry
  euclid_finish
