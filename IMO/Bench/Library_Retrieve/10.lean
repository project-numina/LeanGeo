import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library10 : ∀ (A B C D: Point), triangle A B C ∧ ∠D:A:B = ∠D:A:C ∧ coll B D C → |(A─C)| * |(B─D)| = |(A─B)| * |(C─D)|:= by
  euclid_intros
  euclid_apply angle_bisector_between A B C D
  have h0: (△D:A:C).area * |(D─B)| = (△D:A:B).area * |(D─C)| := by
    euclid_apply area_ratio_segment_ratio A D B C
    euclid_finish
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A C as AC
  euclid_apply exists_foot D AB as E
  euclid_apply exists_foot D AC as F
  have h1: (△D:A:B).area = |(D─E)| * |(A─B)| / 2 := by
    euclid_apply triangle_area_foot D A B E AB
    euclid_finish
  have h2: (△D:A:C).area = |(D─F)| * |(A─C)| / 2 := by
    euclid_apply triangle_area_foot D A C F AC
    euclid_finish
  have h3: |(D─E)| = |(D─F)| := by
    euclid_apply line_from_points
    euclid_apply acute_angle_foot_equal D A B E AB
    euclid_apply acute_angle_foot_equal D A C F AC
    euclid_apply congruent_AAS D A E D A F
    euclid_finish
  rw [h1,h2,h3] at h0
  euclid_finish
