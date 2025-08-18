import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Circle.Basic
import LeanGeo.Theorem.Circle.Position
import Book

open Elements.Book1
set_option maxHeartbeats 0
namespace LeanGeo

theorem cyclic_if_eq_angles : ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ ∠B:C:A = ∠B:D:A ∧ C.sameSide D AB → D.onCircle Ω:= by
  euclid_intros
  have h1: ¬(D.insideCircle Ω) := by
    by_contra
    euclid_apply point_in_circle_onlyif_to_angle A B C D AB Ω
    euclid_finish
  have h2: ¬(D.outsideCircle Ω) := by
    by_contra
    euclid_apply point_out_circle_onlyif_to_angle A B C D AB Ω
    euclid_finish
  euclid_finish

theorem cyclic_if_supp_angles : ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ ∠B:C:A + ∠B:D:A = ∟ + ∟ ∧ C.opposingSides D AB → D.onCircle Ω:= by
  euclid_intros
  euclid_apply exists_point_on_opposing_arc  A B C AB Ω as E
  have h1:∠A:D:B = ∠A:E:B := by
    euclid_apply cyclic_supp_angles A B C E AB Ω
    euclid_finish
  euclid_apply cyclic_if_eq_angles A B E D AB Ω
  euclid_finish

theorem IntersectingSecantsTheorem_converse: ∀ (a b c d e: Point),¬ Coll a b c ∧ (between e a b) ∧ (between e c d) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → Cyclic a b c d := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points c d as CD
  euclid_apply threePoints_existCircle a b c as Ω
  euclid_apply line_from_points b c as BC
  euclid_assert a.opposingSides d BC
  have h1:∠ b:a:c + ∠b:d:c = ∟ + ∟ := by
    euclid_apply similarTriangles_with_same_angle a b c d e
    euclid_apply coll_angles_eq
    euclid_finish
  euclid_apply cyclic_if_supp_angles b c a d BC Ω
  euclid_finish

theorem IntersectingChordsTheorem_converse: ∀ (a b c d e: Point),¬ Coll a b c ∧ (between a e b) ∧ (between c e d) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → Cyclic a b c d := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points c d as CD
  euclid_assert Triangle a b d
  euclid_apply threePoints_existCircle a b d as Ω
  euclid_apply line_from_points b d as BD
  euclid_assert a.sameSide c BD
  have h1:∠ d:a:b = ∠d:c:b := by
    euclid_apply similarTriangles_with_opposite_angles d a e b c
    euclid_apply coll_angles_eq
    euclid_finish
  euclid_apply cyclic_if_eq_angles b d a c BD Ω
  euclid_finish

end LeanGeo
