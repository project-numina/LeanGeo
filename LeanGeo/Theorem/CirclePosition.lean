import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Basic
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.PerpBisector
import LeanGeo.Theorem.Circle

set_option maxHeartbeats 0
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

theorem opposite_angle_similar: ∀ (a b c d e: Point),¬ coll a b c ∧ (between a c e) ∧ (between b c d) ∧ |(e─c)| * |(a─c)| = |(b─c)| * |(c─d)| → similarTriangle a c b d c e := by
  euclid_intros
  euclid_apply line_from_points a c as AC
  euclid_apply line_from_points b d as BD
  euclid_assert triangle a b c
  euclid_apply opposite_angles_same a b c d e
  euclid_apply similar_SAS a c b d c e
  euclid_finish

theorem same_angle_similar: ∀ (a b c d e: Point),¬ coll a b c ∧ (between e a b) ∧ (between e c d) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → similarTriangle e a c e d b := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points c d as CD
  euclid_assert triangle e a c
  have h1: ∠a:e:c = ∠d:e:b := by
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply similar_SAS a e c d e b
  euclid_finish

theorem power_cyclic_out: ∀ (a b c d e: Point),¬ coll a b c ∧ (between e a b) ∧ (between e c d) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → cyclic a b c d := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points c d as CD
  euclid_apply threePoints_existCircle a b c as Ω
  euclid_apply line_from_points b c as BC
  euclid_assert a.opposingSides d BC
  have h1:∠ b:a:c + ∠b:d:c = ∟ + ∟ := by
    euclid_apply same_angle_similar a b c d e
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply complementary_cyclic b c a d BC Ω
  euclid_finish

theorem power_cyclic_in: ∀ (a b c d e: Point),¬ coll a b c ∧ (between a e b) ∧ (between c e d) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → cyclic a b c d := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points c d as CD
  euclid_assert triangle a b d
  euclid_apply threePoints_existCircle a b d as Ω
  euclid_apply line_from_points b d as BD
  euclid_assert a.sameSide c BD
  have h1:∠ d:a:b = ∠d:c:b := by
    euclid_apply opposite_angle_similar d a e b c
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply eqAngle_cyclic b d a c BD Ω
  euclid_finish
