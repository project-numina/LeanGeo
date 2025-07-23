import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/-- In a right-angled Triangle ABC, with the right angle at A, let M be the MidPoint of the hypotenuse BC. Let D be the Foot of the perpendicular from M to the leg AB. Prove that D is the MidPoint of AB.
-/
theorem right_triangle_median_perpendicular_midpoint:
  ∀ (A B C M D : Point) (AB BC : Line),
    RightTriangle A B C ∧
    distinctPointsOnLine A B AB ∧
    distinctPointsOnLine B C BC ∧
    MidPoint B M C ∧
    Foot M D AB
    → MidPoint A D B := by
    euclid_intros
    have h_equidistant_AM_BM : |(A─M)| = |(B─M)| := by
      euclid_apply rightTriangle_midLine_eq_half_hypotenuse A B C M
      euclid_finish
    have h_tri_MAB : Triangle M A B := by
      have h1: M ≠ A := by
        by_contra h_contra
        euclid_finish
      have h2: M ≠ B := by
        by_contra h_contra
        euclid_assert MidPoint B B C
        euclid_assert B = C
        euclid_finish
      have h3: A ≠ B := by
        euclid_finish
      euclid_finish
    have h_iso_MAB : IsoTriangle M A B := by
      euclid_assert |(M─A)| = |(M─B)|
      euclid_finish
    euclid_apply isoTriangle_three_lines_concidence_foot M A B D AB
    euclid_finish
