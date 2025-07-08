import SystemE
import LeanGeo
namespace LeanGeo

/--In a right-angled triangle, the altitude drawn from the vertex of the right angle to the hypotenuse divides the triangle into two smaller triangles that are similar to the original triangle. This theorem proves that one of the smaller triangles, △DBA, is similar to the original triangle, △ABC, where A is the right angle and D is the foot of the altitude from A to BC.-/

theorem altitude_hypotenuse_similar_1:
  ∀ (A B C D: Point) (BC : Line),
    rightTriangle A B C ∧
    distinctPointsOnLine B C BC ∧
    foot A D BC
    → similarTriangle D B A A B C := by
    euclid_intros
    have h_acute_angles : ∠A:B:C < ∟ ∧ ∠A:C:B < ∟ := by
      sorry
    have h_between : between B D C := by
      euclid_apply acute_triangle_foot_between A B C D BC
      euclid_finish
    have h_tri_DBA : triangle D B A := by
      euclid_finish
    have h_angle_eq1 : ∠B:D:A = ∠B:A:C := by
      have h_D_right : ∠B:D:A = ∟ := by
        euclid_assert D ≠ B
        euclid_finish
      have h_A_right : ∠B:A:C = ∟ := by
        euclid_finish
      euclid_finish
    have h_angle_eq2 : ∠D:B:A = ∠A:B:C := by
      euclid_apply angle_between_transfer B D C A
      euclid_finish
    euclid_apply similar_AA D B A A B C
    euclid_finish

theorem altitude_hypotenuse_similar_2:
  ∀ (A B C D: Point) (BC : Line),
    rightTriangle A B C ∧
    distinctPointsOnLine B C BC ∧
    foot A D BC
    → similarTriangle D B A A B C := by
    euclid_intros
    have h_acute_angles : ∠A:B:C < ∟ ∧ ∠A:C:B < ∟ := by
      euclid_apply triangle_angleSum A B C
      euclid_apply triangle_anglePositive A B C
      euclid_finish
    have h_between : between B D C := by
      sorry
    have h_tri_DBA : triangle D B A := by
      euclid_finish
    have h_angle_eq1 : ∠B:D:A = ∠B:A:C := by
      have h_D_right : ∠B:D:A = ∟ := by
        euclid_assert D ≠ B
        euclid_finish
      have h_A_right : ∠B:A:C = ∟ := by
        euclid_finish
      euclid_finish
    have h_angle_eq2 : ∠D:B:A = ∠A:B:C := by
      euclid_apply angle_between_transfer B D C A
      euclid_finish
    euclid_apply similar_AA D B A A B C
    euclid_finish

theorem obtuse_foot_between: ∀(A B C D: Point) (BC : Line), distinctPointsOnLine B C BC ∧ foot A D BC ∧ ∠A:B:C > ∟ → between D B C := by
  euclid_intros
  have h2: ¬(between B C D):= by
    sorry
  have h3: ¬(between B D C):= by
    by_contra
    euclid_apply angle_between_transfer B D C A
    euclid_apply triangle_angleSum A B D
    euclid_finish
  have h4: D ≠ C := by
    euclid_apply triangle_angleSum A B D
    euclid_finish
  euclid_finish

theorem obtuse_foot_between_2: ∀(A B C D: Point) (BC : Line), distinctPointsOnLine B C BC ∧ foot A D BC ∧ ∠A:B:C > ∟ → between D B C := by
  euclid_intros
  have h2: ¬(between B C D):= by
    by_contra
    euclid_apply angle_between_transfer B C D A
    euclid_apply triangle_angleSum A B D
    euclid_finish
  have h3: ¬(between B D C):= by
    by_contra
    euclid_apply angle_between_transfer B D C A
    euclid_apply triangle_angleSum A B D
    euclid_finish
  have h4: D ≠ C := by
    sorry
  euclid_finish

theorem secant_theorem_1:∀ (P A B C O: Point) (Ω: Circle)(L:Line), A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ between P B C ∧ distinctPointsOnLine P A L ∧ tangentAtPoint A O L Ω → |(P─A)| * |(P─A)| = |(P─B)| * |(P─C)| := by
  euclid_intros
  have h1: A ≠ B := by
    sorry
  have h2: A ≠ C := by
    sorry
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  have h1: ∠B:A:P = ∠A:C:P := by
    euclid_apply inscribedAngle_eq_tangentAngle A B C P O Ω AB BC AC L
    euclid_apply angle_between_transfer
    euclid_finish
  have h2: ∠A:P:B = ∠C:P:A := by
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply similar_AA A P B C P A
  euclid_finish

theorem secant_theorem2 :∀ (P A B C O: Point) (Ω: Circle)(L:Line), A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ between P B C ∧ distinctPointsOnLine P A L ∧ tangentAtPoint A O L Ω → |(P─A)| * |(P─A)| = |(P─B)| * |(P─C)| := by
  euclid_intros
  have h1: A ≠ B := by
    by_contra
    euclid_apply tangentLine_outsideCircle B C O Ω L
    euclid_finish
  have h2: A ≠ C := by
    by_contra
    euclid_apply tangentLine_outsideCircle C B O Ω L
    euclid_finish
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  have h1: ∠B:A:P = ∠A:C:P := by
    euclid_apply inscribedAngle_eq_tangentAngle A B C P O Ω AB BC AC L
    euclid_apply angle_between_transfer
    euclid_finish
  have h2: ∠A:P:B = ∠C:P:A := by
    sorry
  euclid_apply similar_AA A P B C P A
  euclid_finish
