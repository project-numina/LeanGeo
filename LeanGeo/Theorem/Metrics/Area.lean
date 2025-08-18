import Mathlib
import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import LeanGeo.Theorem.Basic.PerpBisector
import LeanGeo.Theorem.Triangle.Basic

open Real
namespace LeanGeo

theorem coll_triangleArea_ratio_eq_seg_ratio: ∀ (a b c d: Point),  Coll b c d → (△a:b:d).area * |(b─c)| = (△a:b:c).area * |(b─d)| := by
  euclid_intros
  euclid_apply coll_def b c d as l
  by_cases ¬ a.onLine l
  · by_cases DistinctThreePoints b c d
    · euclid_apply exists_foot a l as e
      euclid_apply triangle_area_foot a b c e l
      euclid_apply triangle_area_foot a b d e l
      euclid_finish
    · euclid_finish
  · euclid_finish

theorem triangleArea_pos: ∀(A B C : Point), Triangle A B C → (△A:B:C).area >0 := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem coll_triangleArea_add: ∀(A B C D: Point), between B D C→ (△A:B:D).area +  (△A:C:D).area = (△A:B:C).area := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

--Slow but could compile
theorem coll_triangleArea_ratio_eq_seg_ratio2: ∀ (a b c d e: Point), Coll a e d ∧ Coll b c d → (△a:b:e).area * |(d─c)| = (△c:a:e).area * |(d─b)|:= by
  euclid_intros
  have h1: (△a:d:c).area * |(d─b)| = (△a:d:b).area * |(d─c)| := by
    euclid_apply coll_triangleArea_ratio_eq_seg_ratio a d b c
    euclid_finish
  have h2: (△e:d:c).area * |(d─b)| = (△e:d:b).area * |(d─c)| := by
    euclid_apply coll_triangleArea_ratio_eq_seg_ratio e d b c
    euclid_finish
  euclid_apply coll_triangleArea_add
  euclid_finish

theorem MenelausTheorem : ∀ (A B C L M N: Point) (AB BC CA l :Line), formTriangle A B C AB BC CA  ∧  L.onLine l ∧ L.onLine BC ∧ M.onLine l ∧ M.onLine CA ∧ N.onLine l ∧ N.onLine AB → |(N─A)| * |(L─B)| * |(M─C)| = |(N─B)| * |(L─C)| * |(M─A)|:= by
  euclid_intros
  have h1: (△L:N:B).area * |(N─A)| = (△L:N:A).area * |(N─B)| := by
    euclid_apply coll_triangleArea_ratio_eq_seg_ratio L N A B
    euclid_finish
  have h2: (△L:N:C).area * |(L─B)| = (△L:N:B).area * |(L─C)| := by
    euclid_apply coll_triangleArea_ratio_eq_seg_ratio N L B C
    euclid_finish
  have h3: (△L:N:A).area * |(M─C)| = (△L:N:C).area * |(M─A)| := by
    euclid_apply coll_triangleArea_ratio_eq_seg_ratio2 N A C M L
    euclid_finish
  have h4: |(N─A)| * |(L─B)| * |(M─C)| * ((△L:N:A).area * (△L:N:B).area *  (△L:N:C).area) = |(N─B)| * |(L─C)| * |(M─A)| * ((△L:N:A).area * (△L:N:B).area *  (△L:N:C).area) := by
    calc
      |(N─A)| * |(L─B)| * |(M─C)| * ((△L:N:A).area * (△L:N:B).area * (△L:N:C).area) = ((△L:N:B).area * |(N─A)|) * ((△L:N:C).area * |(L─B)|) * ((△L:N:A).area * |(M─C)|) := by ring_nf
      _ = ((△L:N:A).area * |(N─B)|) * ((△L:N:B).area * |(L─C)|) * ((△L:N:C).area * |(M─A)|) := by rw[h1,h2,h3]
      _ = _ := by ring_nf
  by_cases (△L:N:A).area > 0 ∧ (△L:N:B).area > 0 ∧ (△L:N:C).area > 0
  · have h5: (△L:N:A).area * (△L:N:B).area * (△L:N:C).area ≠ 0 := by
      euclid_finish
    apply (mul_left_inj' h5).mp
    linarith
  · euclid_finish

theorem CevaTheorem : ∀ (A B C D E F O: Point), (Triangle A B C) ∧ Coll A F B ∧ Coll A E C ∧ Coll B D C ∧ Coll A O D ∧ Coll C O F ∧ Coll B O E → |(B─D)| * |(C─E)| * |(A─F)| = |(D─C)| * |(E─A)| * |(F─B)| := by
  euclid_intros
  by_cases (△B:O:A).area > 0 ∧ (△A:O:C).area > 0 ∧ (△B:O:C).area > 0
  · have h1: |(B─D)| * (△A:O:C).area = |(D─C)| * (△B:O:A).area:= by
      euclid_apply coll_triangleArea_ratio_eq_seg_ratio2 A B C D O
      euclid_finish
    have h2: |(C─E)| * (△B:O:A).area = |(E─A)| * (△B:O:C).area:= by
      euclid_apply coll_triangleArea_ratio_eq_seg_ratio2 B C A E O
      euclid_finish
    have h3: |(A─F)| * (△B:O:C).area = |(F─B)| * (△A:O:C).area:= by
      euclid_apply coll_triangleArea_ratio_eq_seg_ratio2 C A B F O
      euclid_finish
    have h4: |(B─D)| * |(C─E)| * |(A─F)| * ((△A:O:C).area * (△B:O:A).area * (△B:O:C).area) = |(D─C)| * |(E─A)| * |(F─B)| * ((△A:O:C).area * (△B:O:A).area * (△B:O:C).area):= by
      calc
        |(B─D)| * |(C─E)| * |(A─F)| * ((△A:O:C).area * (△B:O:A).area * (△B:O:C).area) = (|(B─D)| * (△A:O:C).area) * (|(C─E)| * (△B:O:A).area) * (|(A─F)| * (△B:O:C).area) := by ring_nf
        _ = (|(D─C)| * (△B:O:A).area) * (|(E─A)| * (△B:O:C).area) * (|(F─B)| * (△A:O:C).area) := by rw[h1,h2,h3]
        _ = _ := by ring_nf
    have h5: (△A:O:C).area * (△B:O:A).area * (△B:O:C).area ≠ 0 := by
      euclid_finish
    apply (mul_left_inj' h5).mp
    linarith
  · euclid_apply line_from_points A D as AD
    euclid_apply line_from_points B E as BE
    euclid_apply line_from_points C F as CF
    euclid_apply line_from_points A C as AC
    euclid_apply line_from_points A B as AB
    euclid_apply line_from_points B C as BC
    euclid_finish

theorem CevaTheorem_converse : ∀ (A B C D E F O : Point), (Triangle A B C) ∧ Coll A F B ∧ Coll A E C ∧ Coll B D C ∧ Coll A O D ∧ |(B─D)| * |(C─E)| * |(A─F)| = |(D─C)| * |(E─A)| * |(F─B)| ∧  Coll C O F →  Coll B O E := by
  sorry

theorem AngleBisectorTheorem : ∀ (A B C D: Point), Triangle A B C ∧ ∠D:A:B = ∠D:A:C ∧ Coll B D C → |(A─C)| * |(B─D)| = |(A─B)| * |(C─D)|:= by
  euclid_intros
  euclid_apply between_if_angles_sum A B C D
  have h0: (△D:A:C).area * |(D─B)| = (△D:A:B).area * |(D─C)| := by
    euclid_apply coll_triangleArea_ratio_eq_seg_ratio A D B C
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
    euclid_apply acuteAngle_foot_eq_angles D A B E AB
    euclid_apply acuteAngle_foot_eq_angles D A C F AC
    euclid_apply congruentTriangles_AAS D A E D A F
    euclid_finish
  rw [h1,h2,h3] at h0
  euclid_finish

end LeanGeo
