import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import Book
namespace LeanGeo
open Elements.Book1

theorem triangle_inequality : ∀ (a b c : Point), Triangle a b c →
|(a─b)| < |(b─c)| + |(c─a)| := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply proposition_20
  euclid_finish

theorem midpoint_half_len: ∀ (A B P : Point), MidPoint A P B → |(A─B)| * 1/2 = |(P─B)|  := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem between_if_sum : ∀ (a b c : Point), DistinctThreePoints a b c ∧ |(a─b)| = |(b─c)| + |(c─a)| → between b c a  := by
  euclid_intros
  have h_coll : Coll a b c := by
    by_contra h_not_coll
    have h_tri : Triangle a b c := by
      euclid_finish
    euclid_apply triangle_inequality a b c
    euclid_finish
  have h_not_abc : ¬ between a b c := by
    by_contra h_abc
    euclid_finish
  have h_not_cab : ¬ between c a b := by
    by_contra h_cab
    euclid_finish
  euclid_finish

theorem between_eq_ratio_eq_point : ∀ (A B C D : Point), between A C B ∧ between A D B ∧ |(A─C)|/|(C─B)| = |(A─D)|/|(D─B)| → C = D := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem foot_shortest : ∀ (A B C : Point) (L : Line), Foot A B L ∧ distinctPointsOnLine B C L → |(A─C)| > |(A─B)| := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A C as AC
  euclid_apply proposition_47 B A C AB AC L
  euclid_finish

theorem sq_diff_mono_distinctTwoPointsOnLine : ∀ (A B C D: Point) (AB : Line), distinctPointsOnLine A B AB ∧ ((LiesOnRay B A C ∧ LiesOnRay C B D) ∨ (C = B ∧ between A C D) ∨ (between A B C ∧ between A C D)) → |(C─A)| * |(C─A)| - |(C─B)| * |(C─B)| < |(D─A)| * |(D─A)| - |(D─B)| * |(D─B)| := by
  euclid_intros
  euclid_finish

theorem sq_diff_mono_distinctTwoPointsOnLine' : ∀ (A B C D: Point) (AB : Line), distinctPointsOnLine A B AB ∧ C.onLine AB ∧ D.onLine AB ∧ |(C─A)| * |(C─A)| - |(C─B)| * |(C─B)| < |(D─A)| * |(D─A)| - |(D─B)| * |(D─B)| → ((LiesOnRay B A C ∧ LiesOnRay C B D) ∨ (C = B ∧ between A C D) ∨ (between A B C ∧ between A C D)) := by
  euclid_intros
  by_contra
  by_cases C = D
  · euclid_finish
  · euclid_apply sq_diff_mono_distinctTwoPointsOnLine A B D C AB
    euclid_finish

theorem sq_diff_mono_distinctThreePointsOnLine : ∀ (A B C D E: Point) (AB : Line), distinctPointsOnLine A B AB ∧ C.onLine AB ∧ D.onLine AB ∧ E.onLine AB ∧ |(C─A)| * |(C─A)| - |(C─B)| * |(C─B)| < |(D─A)| * |(D─A)| - |(D─B)| * |(D─B)| ∧ |(D─A)| * |(D─A)| - |(D─B)| * |(D─B)| < |(E─A)| * |(E─A)| - |(E─B)| * |(E─B)| → between C D E := by
  euclid_intros
  by_contra
  euclid_apply sq_diff_mono_distinctTwoPointsOnLine' A B C D AB
  euclid_apply sq_diff_mono_distinctTwoPointsOnLine' A B D E AB
  euclid_finish

end LeanGeo
