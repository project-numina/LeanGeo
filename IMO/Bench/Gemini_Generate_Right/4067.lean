import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem power_of_midpoint_on_median:
  ∀ (A B C M D O : Point) (Ω : Circle),
    (triangle A B C) ∧
    (midpoint B M C) ∧
    (circumCircle Ω A B C) ∧
    (O.isCentre Ω) ∧
    (D.onCircle Ω) ∧
    (D ≠ A) ∧
    (between A M D)
    → |(A─M)| * |(M─D)| = |(B─M)| * |(B─M)| := by
    euclid_intros
    have h_B_neq_C: B ≠ C := by
      euclid_finish
    euclid_apply line_from_points B C h_B_neq_C as BC
    have h_A_neq_M: A ≠ M := by
      euclid_finish
    euclid_apply line_from_points A M h_A_neq_M as AM
    have h_power_AD : |(A─M)| * |(M─D)| + |(M─O)| * |(M─O)| = |(O─A)| * |(O─A)| := by
      euclid_apply inside_power M O A D Ω
      euclid_finish
    have h_power_BC : |(B─M)| * |(C─M)| + |(M─O)| * |(M─O)| = |(O─B)| * |(O─B)| := by
      euclid_apply inside_power M O B C Ω
      euclid_finish
    euclid_finish