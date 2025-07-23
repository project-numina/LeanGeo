import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--# Task 10.4

In Triangle $A B C$, the altitude $B H$ and medians $A M$ and $C K$ are drawn. Prove that triangles $K H M$ and $A B C$ are similar.

Number of points 7-/
theorem Numina_Geometry_1110 :
  ∀ (A B C H M K : Point) (AC: Line),
    (Triangle A B C) ∧
    (between A H C) ∧
    (Foot B H AC) ∧
    (distinctPointsOnLine A C AC) ∧
    (MidPoint B M C) ∧
    (MidPoint A K B)
    →
    (∠ K:H:M = ∠ A:B:C) ∧
    (∠ K:M:H = ∠ A:C:B) ∧
    (∠ H:K:M = ∠ B:A:C) := by
  euclid_intros
  have h_KM_len: |(A─C)| = |(K─M)| * 2 := by
    have h_tri_BAC: Triangle B A C := by euclid_finish
    have h_mid_BKA: MidPoint B K A := by euclid_finish
    euclid_apply triangleMidsegment_half_len B A C K M
    euclid_finish
  have h_KH_len: |(A─B)| = |(K─H)| * 2 := by
    have h_BHA_right: ∠ B:H:A = ∟ := by euclid_finish
    have h_tri_HAB: Triangle H A B := by euclid_finish
    have h_rtri_HAB: RightTriangle H A B := by euclid_finish
    have h_HK_eq_AK: |(H─K)| = |(A─K)| := by
      euclid_apply rightTriangle_midLine_eq_half_hypotenuse H A B K
      euclid_finish
    euclid_finish
  have h_MH_len: |(B─C)| = |(M─H)| * 2 := by
    have h_BHC_right: ∠ B:H:C = ∟ := by euclid_finish
    have h_tri_HBC: Triangle H B C := by euclid_finish
    have h_rtri_HBC: RightTriangle H B C := by euclid_finish
    have h_HM_eq_BM: |(H─M)| = |(B─M)| := by
      euclid_apply rightTriangle_midLine_eq_half_hypotenuse H B C M
      euclid_finish
    euclid_finish
  have h_tri_KHM: Triangle K H M := by
    euclid_apply line_from_points K M as KM
    have h_para_KMAC : ¬ KM.intersectsLine AC := by
      euclid_apply line_from_points A B as AB
      euclid_apply line_from_points B C as BC
      euclid_apply triangleMidsegment_parallel_base B A C K M AB AC BC KM
      euclid_finish
    by_contra
    euclid_finish
  have h_sim: SimilarTriangles A B C K H M := by
    euclid_apply similar_SSS A B C K H M
    euclid_finish
  split_ands
  · have h_angle_eq : ∠A:B:C = ∠K:H:M := by euclid_finish
    euclid_finish
  · have h_angle_eq : ∠A:C:B = ∠K:M:H := by euclid_finish
    euclid_finish
  · have h_angle_eq : ∠B:A:C = ∠H:K:M := by euclid_finish
    euclid_finish

end LeanGeo
