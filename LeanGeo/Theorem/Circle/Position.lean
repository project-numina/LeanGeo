import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Circle.Basic
import Book

open Elements.Book1
set_option maxHeartbeats 0
namespace LeanGeo

theorem rad_gt_zero : ∀ (Ω : Circle), (rad Ω) > 0 := by
  euclid_intros
  euclid_apply exists_centre Ω as O
  euclid_apply exists_point_on_circle Ω as A
  euclid_finish

theorem point_in_circle_if_to_rad : ∀ (A O: Point) (Ω : Circle), O.isCentre Ω ∧ |(A─O)| < (rad Ω) → A.insideCircle Ω := by
    euclid_intros
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_in_circle_onlyif_to_rad : ∀ (A O: Point) (Ω : Circle), O.isCentre Ω ∧ A.insideCircle Ω → |(A─O)| < (rad Ω) := by
    euclid_intros
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_out_circle_if_to_rad : ∀ (A O: Point) (Ω : Circle), O.isCentre Ω ∧ |(A─O)| > (rad Ω) → A.outsideCircle Ω := by
    euclid_intros
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_out_circle_onlyif_to_rad : ∀ (A O: Point) (Ω : Circle), O.isCentre Ω ∧ A.outsideCircle Ω → |(A─O)| > (rad Ω) := by
    euclid_intros
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_on_circle_if_to_rad : ∀ (A O : Point) (Ω : Circle), O.isCentre Ω ∧ |(A─O)| = (rad Ω) → A.onCircle Ω := by
    euclid_intros
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_on_circle_onlyif_to_rad : ∀ (A O : Point) (Ω : Circle), O.isCentre Ω ∧ A.onCircle Ω → |(A─O)| = (rad Ω) := by
    euclid_intros
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_in_circle_if_to_pow : ∀ (A : Point) (Ω : Circle), Pow(A, Ω) < 0 → A.insideCircle Ω := by
    euclid_intros
    euclid_apply exists_centre Ω as O
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_in_circle_onlyif_to_pow : ∀ (A : Point) (Ω : Circle), A.insideCircle Ω → Pow(A, Ω) < 0 := by
    euclid_intros
    euclid_apply exists_centre Ω as O
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_out_circle_if_to_pow : ∀ (A : Point) (Ω : Circle), Pow(A, Ω) > 0 → A.outsideCircle Ω := by
    euclid_intros
    euclid_apply exists_centre Ω as O
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_out_circle_onlyif_to_pow : ∀ (A : Point) (Ω : Circle), A.outsideCircle Ω → Pow(A, Ω) > 0 := by
    euclid_intros
    euclid_apply exists_centre Ω as O
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_on_circle_if_to_pow : ∀ (A : Point) (Ω : Circle), Pow(A, Ω) = 0 → A.onCircle Ω := by
    euclid_intros
    euclid_apply exists_centre Ω as O
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_on_circle_onlyif_to_pow : ∀ (A : Point) (Ω : Circle), A.onCircle Ω → Pow(A, Ω) = 0 := by
    euclid_intros
    euclid_apply exists_centre Ω as O
    euclid_apply exists_point_on_circle Ω as P
    euclid_finish

theorem point_out_circle_if_to_angle: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ ∠A:D:B < ∠A:C:B → D.outsideCircle Ω := by
  euclid_intros
  have h1 : ¬ (D.onCircle Ω) := by
    by_contra
    euclid_apply cyclic_eq_angles A B C D AB Ω
    euclid_finish
  have h2: ¬ (D.insideCircle Ω):= by
    by_contra
    euclid_apply line_from_points A D as AD
    euclid_apply intersection_circle_line_extending_points Ω AD D A as E
    have h3: ∠B:C:A = ∠ B:E:A := by
      euclid_apply cyclic_eq_angles A B C E AB Ω
      euclid_finish
    euclid_apply triangle_ex_angle_eq E D B A
    have h4: ∠A:E:B = ∠D:E:B := by
      euclid_apply coll_angles_eq A D E B
      euclid_finish
    euclid_finish
  euclid_finish

theorem point_in_circle_if_to_angle: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ ∠A:D:B > ∠A:C:B → D.insideCircle Ω := by
  euclid_intros
  have h1 : ¬ (D.onCircle Ω) := by
    by_contra
    euclid_apply cyclic_eq_angles A B C D AB Ω
    euclid_finish
  have h2: ¬ (D.outsideCircle Ω):= by
    by_contra
    euclid_apply exists_point_between_points_on_line AB A B as F
    euclid_apply line_from_points D F as DF
    euclid_apply intersection_circle_line_between_points  Ω DF F D as E
    have h1: ∠ A:E:B = ∠A:C:B := by
      euclid_apply cyclic_eq_angles A B C E AB Ω
      euclid_finish
    euclid_apply line_from_points A D as AD
    euclid_apply line_from_points B D as BD
    euclid_apply insideTriangle_angles_sum D A B E AD AB BD
    euclid_finish
  euclid_finish

theorem point_in_circle_onlyif_to_angle: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ D.insideCircle Ω → ∠A:D:B > ∠A:C:B := by
  euclid_intros
  euclid_apply line_from_points A D as AD
  euclid_apply intersection_circle_line_extending_points Ω AD D A as E
  have h3: ∠A:C:B = ∠ A:E:B := by
    euclid_apply cyclic_eq_angles A B C E AB Ω
    euclid_finish
  have h4 : ∠A:D:B = ∠D:B:E + ∠D:E:B := by
    euclid_apply triangle_ex_angle_eq E D B A
    euclid_finish
  have h5: ∠A:E:B = ∠D:E:B := by
    euclid_apply coll_angles_eq A D E B
    euclid_finish
  have h6: ∠ D:B:E > 0 := by
    have h_tri_DBE: Triangle D B E := by
      euclid_finish
    euclid_apply triangle_angle_positive D B E
    euclid_finish
  rw[h4,h3,h5]
  euclid_finish

theorem point_out_circle_onlyif_to_angle: ∀ (A B C D : Point) (AB : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine A B AB ∧ C.onCircle Ω ∧ C ≠ A ∧ C ≠ B ∧ D.sameSide C AB ∧ D.outsideCircle Ω → ∠A:D:B < ∠A:C:B := by
  euclid_intros
  euclid_apply exists_point_between_points_on_line AB A B as F
  euclid_apply line_from_points D F as DF
  euclid_apply intersection_circle_line_between_points  Ω DF F D as E
  have h1: ∠ A:E:B = ∠A:C:B := by
    euclid_apply cyclic_eq_angles A B C E AB Ω
    euclid_finish
  euclid_apply line_from_points A D as AD
  euclid_apply line_from_points B D as BD
  euclid_apply insideTriangle_angles_sum D A B E AD AB BD
  euclid_finish


end LeanGeo
