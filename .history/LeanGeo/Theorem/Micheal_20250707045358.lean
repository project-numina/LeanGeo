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

theorem intersecting_circles_perpendicular_bisector :
  ∀  (O1 O2 A B : Point) (L : Line)(C1 C2 : Circle),
  (circlesIntersectsAtTwoPoints C1 C2 A B) ∧ O1.isCentre C1 ∧ O2.isCentre C2 ∧ O1 ≠ O2
  ∧ (O1.onLine L)
  ∧ (O2.onLine L)
  → perpBisector A B L :=
by
  euclid_intros
  euclid_apply perpBisector_construction A B O1 O2 L
  euclid_finish

theorem intersecting_circle_triangle: ∀ (O1 O2 A B : Point) (C1 C2: Circle), O1 ≠ O2 ∧ O1.isCentre C1 ∧ O2.isCentre C2∧ circlesIntersectsAtTwoPoints C1 C2 A B →  triangle O1 O2 A := by
  euclid_intros
  euclid_apply line_from_points O1 O2 as L
  euclid_apply intersecting_circles_perpendicular_bisector O1 O2 A B L C1 C2
  --euclid_apply line_from_points
  euclid_finish


theorem intersecting_circle_similar_between: ∀ (O1 O2 A B C K: Point) (Ω1 Ω2: Circle), O1 ≠ O2 ∧ O1.isCentre Ω1 ∧ O2.isCentre Ω2 ∧  circlesIntersectsAtTwoPoints Ω1 Ω2 A K ∧ between B A C ∧ B ≠ K ∧ C ≠ K ∧ B.onCircle Ω1 ∧ C.onCircle Ω2 → similarTriangle O1 O2 K B C K:= by
  euclid_intros
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points A B as L
  have h1: triangle O1 O2 A := by
    euclid_apply intersecting_circle_triangle O1 O2 A K Ω1 Ω2
    euclid_finish
  have h1': triangle O1 O2 K := by
    euclid_apply intersecting_circle_triangle O1 O2 K A Ω1 Ω2
    euclid_finish
  have h3: triangle B K C := by
    euclid_apply line_from_points
    euclid_finish
  have h4: ∠A:O1:O2 = ∠ K:O1:O2:= by
    euclid_apply congruent_SSS A O1 O2 K O1 O2
    euclid_finish
  euclid_apply line_from_points A K as AK
  euclid_apply line_from_points O1 O2 as O1O2
  euclid_apply intersection_lines AK O1O2 as M
  by_cases h41: between O1 M O2
  · have h42: B.sameSide O1 AK := by
      sorry
    euclid_apply inscribed_angle_theorem_sameSide A K B O1 AK Ω1
      have h5: ∠K:B:A = ∠K:O1:O2 := by
        have h6: ∠A:O1:K = ∠A:O1:M + ∠M:O1:K := by
          euclid_apply between_angleSum O1 A M K
          euclid_finish
        have h7: ∠A:O1:O2 = ∠A:O1:M := by
          euclid_apply angle_between_transfer O1 M O2 A
          euclid_finish
        have h8: ∠K:O1:O2 = ∠K:O1:M := by
          euclid_apply angle_between_transfer O1 M O2 K
          euclid_finish
        euclid_finish
      have h10: C.sameSide O2 AK := by
        euclid_finish
      have h11: ∠K:B:C = ∠K:O1:O2 := by
        euclid_apply angle_between_transfer B A C K
        euclid_finish
      have h12: ∠K:C:B = ∠K:O2:O1 := by
        euclid_apply inscribed_angle_theorem_sameSide A K C O2 AK Ω2
        have h_cong_O2 : ∠A:O2:O1 = ∠K:O2:O1 := by
            euclid_apply congruent_SSS A O2 O1 K O2 O1
            euclid_finish
        have h_sum: ∠A:O2:K = ∠A:O2:M + ∠M:O2:K := by
            euclid_apply between_angleSum O2 A M K
            euclid_finish
        have h_A_id: ∠A:O2:O1 = ∠A:O2:M := by
            euclid_apply angle_between_transfer O1 M O2 A
            euclid_finish
        have h_K_id: ∠K:O2:O1 = ∠K:O2:M := by
            euclid_apply angle_between_transfer O1 M O2 K
            euclid_finish
        have h_BC_eq: ∠K:C:B = ∠A:C:K := by
            euclid_apply angle_between_transfer B A C K
            euclid_finish
        euclid_finish
      euclid_apply similar_AA B C K O1 O2 K
      euclid_finish
