import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Basic
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.PerpBisector
import LeanGeo.Theorem.Circle

open LeanGeo
namespace LeanGeo
theorem angle_lt_outsideCircle: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ ∠A:D:B < ∠A:C:B → D.outsideCircle Ω := by
  euclid_intros
  have h1 : ¬ (D.onCircle Ω) := by
    by_contra
    euclid_apply cyclic_eqAngle A B C D AB Ω
    euclid_finish
  have h2: ¬ (D.insideCircle Ω):= by
    by_contra
    euclid_apply line_from_points A D as AD
    euclid_apply intersection_circle_line_extending_points Ω AD D A as E
    have h3: ∠B:C:A = ∠ B:E:A := by
      euclid_apply cyclic_eqAngle A B C E AB Ω
      euclid_finish
    euclid_apply triangle_exteriorAngle E D B A
    have h4: ∠A:E:B = ∠D:E:B := by
      euclid_apply angle_between_transfer A D E B
      euclid_finish
    euclid_finish
  euclid_finish

theorem angle_gt_insideCircle: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ ∠A:D:B > ∠A:C:B → D.insideCircle Ω := by
  euclid_intros
  have h1 : ¬ (D.onCircle Ω) := by
    by_contra
    euclid_apply cyclic_eqAngle A B C D AB Ω
    euclid_finish
  have h2: ¬ (D.outsideCircle Ω):= by
    by_contra
    euclid_apply exists_point_between_points_on_line AB A B as F
    euclid_apply line_from_points D F as DF
    euclid_apply intersection_circle_line_between_points  Ω DF F D as E
    have h1: ∠ A:E:B = ∠A:C:B := by
      euclid_apply cyclic_eqAngle A B C E AB Ω
      euclid_finish
    euclid_apply line_from_points A D as AD
    euclid_apply line_from_points B D as BD
    euclid_apply triangle_inside_angleSum D A B E AD AB BD
    euclid_finish
  euclid_finish

theorem angle_insideCircle_gt: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ D.insideCircle Ω → ∠A:D:B > ∠A:C:B := by
  euclid_intros
  euclid_apply line_from_points A D as AD
  euclid_apply intersection_circle_line_extending_points Ω AD D A as E
  have h3: ∠A:C:B = ∠ A:E:B := by
    euclid_apply cyclic_eqAngle A B C E AB Ω
    euclid_finish
  have h4 : ∠A:D:B = ∠D:B:E + ∠D:E:B := by
    euclid_apply triangle_exteriorAngle E D B A
    euclid_finish
  have h5: ∠A:E:B = ∠D:E:B := by
    euclid_apply angle_between_transfer A D E B
    euclid_finish
  have h6: ∠ D:B:E > 0 := by
    have h_tri_DBE: triangle D B E := by
      euclid_finish
    euclid_apply triangle_anglePositive D B E
    euclid_finish
  rw[h4,h3,h5]
  euclid_finish

theorem angle_outsideCircle_lt: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ D.outsideCircle Ω → ∠A:D:B < ∠A:C:B := by
  euclid_intros
  euclid_apply exists_point_between_points_on_line AB A B as F
  euclid_apply line_from_points D F as DF
  euclid_apply intersection_circle_line_between_points  Ω DF F D as E
  have h1: ∠ A:E:B = ∠A:C:B := by
    euclid_apply cyclic_eqAngle A B C E AB Ω
    euclid_finish
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points B D as BD
  euclid_apply triangle_inside_angleSum D A B E AD AB BD
  euclid_finish

theorem eqAngle_cyclic : ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ ∠B:C:A = ∠B:D:A ∧ C.sameSide D AB → D.onCircle Ω:= by
  euclid_intros
  have h1: ¬(D.insideCircle Ω) := by
    by_contra
    euclid_apply angle_insideCircle_gt A B C D AB Ω
    euclid_finish
  have h2: ¬(D.outsideCircle Ω) := by
    by_contra
    euclid_apply angle_outsideCircle_lt A B C D AB Ω
    euclid_finish
  euclid_finish

theorem exists_point_opposing_arc : ∀ (A B C : Point) (AB : Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ C ≠ A ∧ C ≠ B ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω → ∃ (D: Point), D.onCircle Ω ∧ D.opposingSides C AB := by
  euclid_intros
  euclid_apply exists_point_between_points_on_line AB A B as D
  euclid_apply line_from_points C D as CD
  euclid_apply intersection_circle_line_extending_points Ω CD D C as E
  use E
  euclid_finish

theorem complementary_cyclic : ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ ∠B:C:A + ∠B:D:A = ∟ + ∟ ∧ C.opposingSides D AB → D.onCircle Ω:= by
  euclid_intros
  euclid_apply exists_point_opposing_arc A B C AB Ω as E
  have h1:∠A:D:B = ∠A:E:B := by
    euclid_apply cyclic_complementary A B C E AB Ω
    euclid_finish
  euclid_apply eqAngle_cyclic A B E D AB Ω
  euclid_finish
