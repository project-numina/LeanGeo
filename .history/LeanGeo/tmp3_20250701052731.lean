import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
theorem point_on_line_second_order_equation: ∀ (B C D H: Point),B ≠ C ∧  midpoint B D C ∧ coll B C H →
|(H─B)| * |(H─B)| + |(H─C)| * |(H─C)| = 2 * (|(H─D)| * |(H─D)| + |(B─D)| * |(B─D)|) := by
  euclid_intros
  euclid_apply coll_exist_line B C H as L
  have h_mid_between : between B D C := by euclid_finish
  have h_mid_eq : |(B─D)| = |(D─C)| := by euclid_finish
  have h_positions : (between H B D) ∨ (H=B) ∨ (between B H C) ∨ (H=C) ∨ (between B C H) := by euclid_finish
  rcases h_positions
  · rename_i h_HBD
    have h_len_HD : |(H─D)| = |(H─B)| + |(B─D)| := by euclid_finish
    have h_len_HC : |(H─C)| = |(H─B)| + |(B─C)| := by euclid_finish
    have h_len_BC : |(B─C)| = 2 * |(B─D)| := by
      euclid_apply midpoint_twice B C D
      euclid_finish
    euclid_finish
  · rename_i h_HB
    have h_len_BC : |(B─C)| = 2 * |(B─D)| := by
      euclid_apply midpoint_twice B C D
      euclid_finish
    euclid_finish
  · rename_i h_BHC
    by_cases h_HD : H=D
    · euclid_finish
    · have h_BHD_or_DHC : between B H D ∨ between D H C := by euclid_finish
      cases h_BHD_or_DHC
      · rename_i h_BHD
        have h_len_BD : |(B─D)| = |(B─H)| + |(H─D)| := by euclid_finish
        have h_len_HC : |(H─C)| = |(H─D)| + |(D─C)| := by euclid_finish
        euclid_finish
      · rename_i h_DHC
        have h_len_BH : |(B─H)| = |(B─D)| + |(D─H)| := by euclid_finish
        have h_len_DC : |(D─C)| = |(D─H)| + |(H─C)| := by euclid_finish
        euclid_finish
  · rename_i h_HC
    have h_len_BC : |(B─C)| = 2 * |(D─C)| := by
      euclid_apply midpoint_twice B C D
      euclid_finish
    euclid_finish
  · rename_i h_BCH
    have h_len_BH : |(B─H)| = |(B─C)| + |(C─H)| := by euclid_finish
    have h_len_DH : |(D─H)| = |(D─C)| + |(C─H)| := by euclid_finish
    have h_len_BC : |(B─C)| = 2 * |(D─C)| := by
      euclid_apply midpoint_twice B C D
      euclid_finish
    euclid_finish
