import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo


theorem library3:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠A:B:C = ∠C:D:A ∧
    ∠B:C:D = ∠D:A:B →
    parallelogram A B C D AB BC CD DA := by
  euclid_intros
  have h_angle_sum : ∠D:A:B + ∠A:B:C + ∠B:C:D + ∠C:D:A = ∟ + ∟ + ∟ + ∟ := by
    euclid_apply line_from_points A C as AC
    have h_tri_ABC : triangle A B C := by
      euclid_finish
    have h_tri_ADC : triangle A D C := by
      euclid_finish
    have h_sum_ABC : ∠A:B:C + ∠B:C:A + ∠C:A:B = ∟ + ∟ := by
      euclid_apply triangle_angleSum A B C
      euclid_finish
    have h_sum_ADC : ∠C:D:A + ∠D:A:C + ∠A:C:D = ∟ + ∟ := by
      euclid_apply triangle_angleSum A D C
      euclid_finish
    have h_angle_A_add : ∠D:A:B = ∠D:A:C + ∠C:A:B := by
      euclid_finish
    have h_angle_C_add : ∠B:C:D = ∠B:C:A + ∠A:C:D := by
      euclid_finish
    euclid_finish
  constructor
  · euclid_finish
  · constructor
    · have h_supp_1 : ∠A:B:C + ∠B:C:D = ∟ + ∟ := by
        euclid_finish
      euclid_apply supplementConsecutiveAngles_parallel AB CD BC B C A D
      euclid_finish
    · have h_supp_2 : ∠B:C:D + ∠C:D:A = ∟ + ∟ := by
        euclid_finish
      euclid_apply supplementConsecutiveAngles_parallel BC DA CD C D B A
      euclid_finish
