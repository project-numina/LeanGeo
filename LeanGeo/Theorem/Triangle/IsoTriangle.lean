import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Triangle.Basic

set_option maxHeartbeats 0
open Elements.Book1
namespace LeanGeo

theorem isoTriangle_imp_eq_angles : ∀ (A B C : Point), IsoTriangle A B C → ∠ A:B:C = ∠A:C:B := by
  euclid_intros
  euclid_apply exists_midpoint B C as D
  euclid_apply line_from_points B C as BC
  euclid_apply coll_angles_eq
  euclid_apply congruentTriangles_SSS D B A D C A
  euclid_apply coll_angles_eq
  euclid_finish

theorem eq_sides_imp_eq_angles :∀ (O A B : Point), |(O─A)|=|(O─B)| ∧ (A ≠ B) → ∠O:A:B = ∠O:B:A := by
  euclid_intros
  by_cases Triangle O A B
  · euclid_assert IsoTriangle O A B
    euclid_apply isoTriangle_imp_eq_angles O A B
    euclid_finish
  · euclid_assert between A O B
    euclid_apply coll_zeroAngle A O B
    euclid_apply coll_zeroAngle B O A
    euclid_finish

theorem isoTriangle_if_eq_angles : ∀ (a b c : Point),
  (Triangle a b c) ∧ (∠ a:b:c = ∠ a:c:b)
  → |(a─b)| = |(a─c)| := by
  euclid_intros
  euclid_apply line_from_points b c as BC
  euclid_apply not_coll_not_onLine a b c BC
  euclid_apply exists_foot a BC as d
  have h1: ∠a:b:c < ∟ := by
    euclid_apply triangle_angle_positive
    euclid_apply triangle_angles_sum
    euclid_finish
  have h2: ∠a:c:b < ∟ := by
    euclid_apply triangle_angle_positive
    euclid_apply triangle_angles_sum
    euclid_finish
  euclid_apply acuteTriangle_foot_between a b c d BC
  euclid_apply coll_angles_eq b d c a
  euclid_apply congruentTriangles_AAS a d b a d c
  euclid_finish

theorem isoTriangle_three_lines_concidence_midpoint : ∀ (a b c d: Point),
  IsoTriangle a b c ∧ MidPoint b d c →
  ( ∠a:d:b = ∟ ∧  ∠a:d:c = ∟ ∧  ∠d:a:b = ∠ d:a:c)
:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply congruentTriangles_SSS a b d a c d
  euclid_finish

theorem isoTriangle_three_lines_concidence_foot : ∀ (a b c d: Point)(BC : Line),
  IsoTriangle a b c ∧ distinctPointsOnLine b c BC ∧ Foot a d BC →
  MidPoint b d c ∧  ∠a:d:b = ∟ ∧  ∠a:d:c = ∟ ∧  ∠d:a:b = ∠ d:a:c
:= by
  euclid_intros
  euclid_apply isoTriangle_imp_eq_angles a b c
  have h1 : ∠a:b:c < ∟ ∧ ∠a:c:b < ∟ := by
    euclid_apply triangle_angles_sum a b c
    euclid_apply triangle_angle_positive a b c
    euclid_finish
  euclid_apply acuteTriangle_foot_between a b c d BC
  have h2: ∠a:d:b = ∟ := by
    euclid_finish
  have h3: ∠a:d:c = ∟ := by
    euclid_finish
  euclid_apply congruentTriangles_HL d a b d a c
  euclid_finish

theorem isoTriangle_three_lines_concidence_angleBisector : ∀ (a b c d: Point),
  IsoTriangle a b c ∧ ∠d:a:b = ∠ d:a:c ∧ Coll b c d→
  (MidPoint b d c ∧  ∠a:d:b = ∟ ∧  ∠a:d:c = ∟)
:= by
  euclid_intros
  euclid_apply between_if_angles_sum a b c d
  euclid_apply line_from_points
  euclid_apply congruentTriangles_SAS b a d c a d
  euclid_finish

theorem perpBisector_imp_isoTriangle : ∀ (A B C D: Point), MidPoint B D C ∧ ∠A:D:B = ∟ ∧ Triangle A B C → IsoTriangle A B C:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_assert ∠A:D:C = ∟
  euclid_apply congruentTriangles_SAS A D B A D C
  euclid_finish

theorem ApolloniusTheorem_to_isoTriangle :
  ∀ (A B C D : Point) (BC : Line),
    IsoTriangle A B C ∧
    distinctPointsOnLine B C BC ∧
    Coll B D C ∧
    between B D C
    → |(A─B)| * |(A─B)| - |(A─D)| * |(A─D)| = |(B─D)| * |(C─D)| := by
  euclid_intros
  have h_A_not_on_line : ¬(A.onLine BC) := by
    euclid_apply not_coll_not_onLine A B C BC
    euclid_finish
  euclid_apply exists_foot A BC h_A_not_on_line as H
  have h_midpoint_H : MidPoint B H C := by
    euclid_apply isoTriangle_three_lines_concidence_foot A B C H BC
    euclid_finish
  by_cases h_D_eq_H : D = H
  · have h_tri_AHB : Triangle H A B := by
      have h_H_neq_B: H ≠ B := by
        by_contra h_eq
        have h_midpointBHC := h_midpoint_H
        euclid_assert MidPoint B B C
        euclid_finish
      euclid_finish
    have h_pyth_AB : |(A─B)| * |(A─B)| = |(A─H)| * |(A─H)| + |(B─H)| * |(B─H)| := by
      euclid_apply PythagoreanTheorem_point H A B
      euclid_finish
    euclid_finish
  · have h_tri_AHB : Triangle H A B := by
      have h_H_neq_B: H ≠ B := by
        by_contra h_eq
        have h_midpointBHC := h_midpoint_H
        euclid_assert MidPoint B B C
        euclid_finish
      euclid_finish
    have h_tri_AHD : Triangle H A D := by
      euclid_finish
    have h_pyth_AB : |(A─B)| * |(A─B)| = |(A─H)| * |(A─H)| + |(B─H)| * |(B─H)| := by
      euclid_apply PythagoreanTheorem_point H A B
      euclid_finish
    have h_pyth_AD : |(A─D)| * |(A─D)| = |(A─H)| * |(A─H)| + |(D─H)| * |(D─H)| := by
      euclid_apply PythagoreanTheorem_point H A D
      euclid_finish
    have h_lhs_is_diff_of_squares : |(A─B)| * |(A─B)| - |(A─D)| * |(A─D)| = |(B─H)| * |(B─H)| - |(D─H)| * |(D─H)| := by
      euclid_finish
    have h_rhs_is_diff_of_squares : |(B─D)| * |(C─D)| = |(B─H)| * |(B─H)| - |(D─H)| * |(D─H)| := by
      euclid_finish
    euclid_finish

end LeanGeo
