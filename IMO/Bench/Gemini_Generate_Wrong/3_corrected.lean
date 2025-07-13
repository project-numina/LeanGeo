import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--
In a right-angled triangle `ABC`, with the right angle at `A`, let `D` be the foot of the altitude from `A` to the hypotenuse `BC`.
Prove that the square of the length of the altitude `AD` is equal to the product of the lengths of the segments `BD` and `DC`.
That is, prove `|AD|² = |BD| * |CD|`.
This is also known as the geometric mean theorem or right triangle altitude theorem.
-/
theorem right_triangle_altitude_theorem:
  ∀ (A B C D: Point) (BC : Line),
    rightTriangle A B C ∧
    distinctPointsOnLine B C BC ∧
    foot A D BC
    → |(A─D)| * |(A─D)| = |(B─D)| * |(D─C)| := by
  euclid_intros
  have h_D_between_BC : between B D C := by
    have h_angleB_acute : ∠A:B:C < ∟ := by
      euclid_apply triangle_angleSum A B C
      euclid_apply triangle_anglePositive A B C
      euclid_finish
    have h_angleC_acute : ∠A:C:B < ∟ := by
      euclid_apply triangle_angleSum A B C
      euclid_apply triangle_anglePositive A B C
      euclid_finish
    euclid_apply acute_triangle_foot_between A B C D BC
    euclid_finish
  have h_tri_BDA : triangle B D A := by
    euclid_finish
  have h_tri_ADC : triangle A D C := by
    euclid_finish
  have h_angles_eq : ∠D:B:A = ∠C:A:D ∧ ∠B:A:D = ∠A:C:D := by
    constructor
    · have h_sum_ABC : ∠A:B:C + ∠A:C:B = ∟ := by
        euclid_apply triangle_angleSum A B C
        euclid_finish
      have h_sum_ACD : ∠C:A:D + ∠A:C:D = ∟ := by
        euclid_apply triangle_angleSum A C D
        have h_right_ADC : ∠A:D:C = ∟ := by
          euclid_finish
        euclid_finish
      have h_angle_eq_ACD_ACB : ∠A:C:D = ∠A:C:B := by
        euclid_apply angle_between_transfer C D B A
        euclid_finish
      have h_angle_eq_DBA_CBA : ∠D:B:A = ∠C:B:A := by
        euclid_apply angle_between_transfer C D B A
        euclid_finish
      euclid_finish
    · have h_sum_ABC : ∠A:B:C + ∠A:C:B = ∟ := by
        euclid_apply triangle_angleSum A B C
        euclid_finish
      have h_sum_ABD : ∠A:B:D + ∠B:A:D = ∟ := by
        euclid_apply triangle_angleSum A B D
        have h_right_ADB : ∠A:D:B = ∟ := by
          euclid_finish
        euclid_finish
      have h_angle_eq_ABD_ABC : ∠A:B:D = ∠A:B:C := by
        euclid_apply angle_between_transfer B D C A
        euclid_finish
      have h_angle_eq_DCA_BCA : ∠D:C:A = ∠B:C:A := by
        euclid_apply angle_between_transfer B D C A
        euclid_finish
      euclid_finish
  have h_similar : similarTriangle B D A A D C := by
    euclid_apply similar_AA B D A A D C
    · euclid_finish
  euclid_finish
