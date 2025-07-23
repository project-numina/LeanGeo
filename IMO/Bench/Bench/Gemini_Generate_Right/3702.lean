import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem iso_triangle_median_property:
  ∀ (A B C M P : Point),
    IsoTriangle A B C ∧ MidPoint B M C ∧ Coll A M P
    → |(P─B)| = |(P─C)| := by
  euclid_intros
  by_cases h_P_eq_M : P = M
  ·
    euclid_finish
  ·
    have h_A_neq_M : A ≠ M := by
      by_contra h_contra
      euclid_finish
    euclid_apply line_from_points A M h_A_neq_M as AM
    euclid_apply line_from_points B C as BC
    have h_tri_PMB : Triangle P M B := by
      by_contra h_coll_PMB
      euclid_finish
    have h_tri_PMC : Triangle P M C := by
      by_contra h_coll_PMC
      euclid_finish
    have h_angles_at_M_eq : ∠ P:M:B = ∠ P:M:C := by
      have h_AM_perp : ∠ A:M:B = ∟ ∧ ∠ A:M:C = ∟ := by
        euclid_apply isoTriangle_three_lines_concidence_midpoint A B C M
        euclid_finish
      euclid_finish
    euclid_apply congruentTriangles_SAS P M B P M C
    euclid_finish
