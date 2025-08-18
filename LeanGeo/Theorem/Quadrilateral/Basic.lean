import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Parallel
import LeanGeo.Theorem.Triangle.Basic
import Book
set_option maxHeartbeats 0
namespace LeanGeo

theorem trapezoid_imp_similarTriangles_interior : ∀ (A B C D E : Point) (AB CD : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ ¬ AB.intersectsLine CD ∧ between A E C ∧ Coll B E D ∧ AB ≠ CD → SimilarTriangles A B E C D E := by
  euclid_intros
  euclid_apply line_from_points B D as BD
  euclid_apply line_from_points A C as AC
  euclid_assert B.opposingSides D AC
  have h1: ∠B:A:E = ∠D:C:E := by
    have h2: ∠B:A:C = ∠A:C:D := by
      euclid_apply parallel_imp_eq_alternateAngles AB CD AC A C B D
      euclid_finish
    euclid_finish
  have h3: ∠A:B:E = ∠C:D:E := by
    have h4: ∠A:B:D = ∠C:D:B := by
      euclid_apply parallel_imp_eq_alternateAngles AB CD BD B D A C
      euclid_finish
    euclid_finish
  euclid_apply similar_AA A B E C D E
  euclid_finish

theorem trapezoid_imp_similarTriangles_exterior: ∀ (A B C D E : Point) (AB CD : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ ¬ AB.intersectsLine CD ∧ between E A C ∧ Coll B E D ∧ AB ≠ CD → SimilarTriangles E A B E C D := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B D as BD
  have h1: ∠E:A:B = ∠E:C:D := by
    euclid_apply parallel_imp_eq_alternateExteriorAngles
    euclid_finish
  have h2: ∠E:B:A = ∠E:D:C := by
    euclid_apply parallel_imp_eq_alternateExteriorAngles
    euclid_finish
  euclid_apply similar_AA E A B E C D
  euclid_finish

theorem parallelogram_imp_supp_adjacent_angles :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    Parallelogram A B C D AB BC CD DA
    → ∠ D:A:B + ∠ A:B:C = ∟ + ∟ := by
  euclid_intros
  have h_para_DA_BC : ¬ DA.intersectsLine BC := by
    euclid_finish
  have h_not_coll_ABC : ¬ Coll A B C := by
    euclid_finish
  euclid_apply extend_point BC C B as F
  have h_alt_angles_eq : ∠ D:A:B = ∠ A:B:F := by
    euclid_apply parallel_imp_eq_alternateAngles DA BC AB A B D F
    euclid_finish
  have h_supp_angles : ∠ A:B:C + ∠ A:B:F = ∟ + ∟ := by
    euclid_apply coll_supp_angles A C B F
    euclid_finish
  euclid_finish

theorem parallelogram_imp_eq_opposite_sides :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    Parallelogram A B C D AB BC CD DA
    → |(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)| := by
  euclid_intros
  have h_tri_ABC : Triangle A B C := by
    euclid_finish
  have h_tri_CDA : Triangle C D A := by
    euclid_finish
  have h_A_neq_C : A ≠ C := by
    euclid_finish
  euclid_apply line_from_points A C h_A_neq_C as AC
  have h_angle_CAB_eq_ACD : ∠C:A:B = ∠A:C:D := by
    euclid_apply parallel_imp_eq_alternateAngles AB CD AC A C B D
    euclid_finish
  have h_angle_BCA_eq_DAC : ∠B:C:A = ∠D:A:C := by
    euclid_apply parallel_imp_eq_alternateAngles BC DA AC C A B D
    euclid_finish
  have h_sum_ABC : ∠C:B:A + ∠B:C:A + ∠C:A:B = ∟ + ∟ := by
    euclid_apply triangle_angles_sum A B C
    euclid_finish
  have h_sum_CDA : ∠A:D:C + ∠D:A:C + ∠A:C:D = ∟ + ∟ := by
    euclid_apply triangle_angles_sum C D A
    euclid_finish
  have h_angle_CBA_eq_ADC : ∠C:B:A = ∠A:D:C := by
    euclid_finish
  euclid_apply congruentTriangles_AAS C A B A C D
  euclid_finish

theorem parallelogram_imp_eq_opposite_angles:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    Parallelogram A B C D AB BC CD DA →
    ∠D:A:B = ∠B:C:D ∧ ∠A:B:C = ∠C:D:A := by
  euclid_intros
  constructor
  ·
    euclid_apply line_from_points B D as BD
    have h1: ∠A:B:D = ∠C:D:B := by
      euclid_apply parallel_imp_eq_alternateAngles AB CD BD B D A C
      euclid_finish
    have h2: ∠A:D:B = ∠C:B:D := by
      euclid_apply parallel_imp_eq_alternateAngles DA BC BD D B A C
      euclid_finish
    euclid_apply congruentTriangles_ASA B D A D B C
    euclid_finish
  ·
    euclid_apply line_from_points A C as AC
    have h3: ∠B:A:C = ∠D:C:A := by
      euclid_apply parallel_imp_eq_alternateAngles AB CD AC A C B D
      euclid_finish
    have h4: ∠B:C:A = ∠D:A:C := by
      euclid_apply parallel_imp_eq_alternateAngles BC DA AC C A B D
      euclid_finish
    euclid_apply congruentTriangles_ASA A C B C A D
    euclid_finish


theorem parallelogram_imp_diagonals_bisect:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    Parallelogram A B C D AB BC CD DA →
    ∃ M, MidPoint A M C ∧ MidPoint B M D := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B D as BD
  have h_intersect : AC.intersectsLine BD := by
    euclid_finish
  euclid_apply intersection_lines AC BD as M
  use M
  have h_tri_ACB : Triangle A C B := by
    euclid_finish
  have h_tri_CAD : Triangle C A D := by
    euclid_finish
  have h_B_opp_D_AC : B.opposingSides D AC := by
    euclid_finish
  have h_angle_ACB_CAD : ∠ A:C:B = ∠ C:A:D := by
    euclid_apply parallel_imp_eq_alternateAngles BC DA AC C A B D
    euclid_finish
  have h_angle_CAB_ACD : ∠ C:A:B = ∠ A:C:D := by
    euclid_apply parallel_imp_eq_alternateAngles AB CD AC A C B D
    euclid_finish
  have h_congr_ACB_CAD : CongruentTriangles A C B C A D := by
    euclid_apply congruentTriangles_ASA A C B C A D
    euclid_finish
  have h_AB_eq_CD : |(A─B)| = |(C─D)| := by
    euclid_finish
  have h_between_AMC : between A M C := by
    euclid_finish
  have h_coll_BMD : Coll B M D := by
    euclid_finish
  have h_AB_neq_CD : AB ≠ CD := by
    euclid_finish
  have h_sim_ABM_CDM : SimilarTriangles A B M C D M := by
    euclid_apply trapezoid_imp_similarTriangles_interior A B C D M AB CD
    euclid_finish
  have h_AM_eq_CM : |(A─M)| = |(M─C)| := by
    euclid_finish
  have h_BM_eq_DM : |(B─M)| = |(M─D)| := by
    euclid_finish
  have h_between_BMD : between B M D := by
    euclid_finish
  constructor
  · constructor
    · exact h_between_AMC
    · exact h_AM_eq_CM
  · constructor
    · exact h_between_BMD
    · exact h_BM_eq_DM

theorem parallelogram_if_eq_opposite_angles:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠ D:A:B = ∠ B:C:D ∧
    ∠ A:B:C = ∠ C:D:A
    → Parallelogram A B C D AB BC CD DA := by
  euclid_intros
  have h_quad_angle_sum : ∠ D:A:B + ∠ A:B:C + ∠ B:C:D + ∠ C:D:A = ∟ + ∟ + ∟ + ∟ := by
    have h_tri_ABC : Triangle A B C := by euclid_finish
    have h_tri_ADC : Triangle A D C := by euclid_finish
    have h_sum_ABC : ∠A:B:C + ∠B:C:A + ∠C:A:B = ∟ + ∟ := by
      euclid_apply triangle_angles_sum A B C
      euclid_finish
    have h_sum_CDA : ∠C:D:A + ∠D:A:C + ∠A:C:D = ∟ + ∟ := by
      euclid_apply triangle_angles_sum C D A
      euclid_finish
    euclid_finish
  have h_supp_consecutive_1 : ∠ D:A:B + ∠ A:B:C = ∟ + ∟ := by
    euclid_finish
  have h_BC_parallel_DA : ¬ BC.intersectsLine DA := by
    euclid_apply parallel_if_supp_consecutiveAngles DA BC AB A B D C
    euclid_finish
  have h_supp_consecutive_2 : ∠ A:B:C + ∠ B:C:D = ∟ + ∟ := by
    euclid_finish
  have h_AB_parallel_CD : ¬ AB.intersectsLine CD := by
    euclid_apply parallel_if_supp_consecutiveAngles AB CD BC B C A D
    euclid_finish
  constructor
  · euclid_finish
  · constructor
    · exact h_AB_parallel_CD
    · exact h_BC_parallel_DA

theorem rhombus_imp_diagonal_bisects_angle :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  Rhombus A B C D AB BC CD DA →
     (∠B:A:C = ∠C:A:D
     ∧ ∠B:C:A = ∠A:C:D
     ∧ ∠A:B:D = ∠D:B:C
     ∧ ∠C:D:B = ∠B:D:A) := by
  euclid_intros
  have h_cong_AC : CongruentTriangles A B C A D C := by
    euclid_apply congruentTriangles_SSS A B C A D C
    euclid_finish
  have h_cong_BD : CongruentTriangles B A D B C D := by
    euclid_apply congruentTriangles_SSS B A D B C D
    euclid_finish
  split_ands
  · euclid_finish
  · euclid_finish
  · euclid_finish
  · euclid_finish

--rectangle
theorem rectangle_if_parallelogram_with_rightAngle:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    Parallelogram A B C D AB BC CD DA ∧ ∠ A:B:C = ∟
    → Rectangle A B C D AB BC CD DA := by
  euclid_intros
  have h_DAB : ∠ D:A:B = ∟ := by
    have h_supplementary : ∠ A:B:C + ∠ D:A:B = ∟ + ∟ := by
      euclid_apply parallel_imp_supp_consecutiveAngles BC DA AB B A C D
      euclid_finish
    euclid_finish
  have h_BCD : ∠ B:C:D = ∟ := by
    have h_supplementary : ∠ A:B:C + ∠ B:C:D = ∟ + ∟ := by
      euclid_apply parallel_imp_supp_consecutiveAngles AB CD BC B C A D
      euclid_finish
    euclid_finish
  have h_CDA : ∠ C:D:A = ∟ := by
    have h_supplementary : ∠ D:A:B + ∠ C:D:A = ∟ + ∟ := by
      euclid_apply parallel_imp_supp_consecutiveAngles AB CD DA A D B C
      euclid_finish
    euclid_finish
  euclid_finish

theorem rectangle_imp_eq_opposite_sides:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    Rectangle A B C D AB BC CD DA →
    |(A─B)| = |(C─D)| ∧ |(B─C)| = |(A─D)| := by
  euclid_intros
  have h_par_AB_CD : ¬ AB.intersectsLine CD := by
    euclid_apply line_from_points B C as BC_line
    euclid_apply parallel_if_supp_consecutiveAngles AB CD BC_line B C A D
    euclid_finish
  have h_par_BC_DA : ¬ BC.intersectsLine DA := by
    euclid_apply line_from_points C D as CD_line
    euclid_apply parallel_if_supp_consecutiveAngles BC DA CD_line C D B A
    euclid_finish
  euclid_apply line_from_points A C as AC_line
  have h_ang1 : ∠ B:A:C = ∠ D:C:A := by
    euclid_apply parallel_imp_eq_alternateAngles AB CD AC_line A C B D
    euclid_finish
  have h_ang2 : ∠ B:C:A = ∠ D:A:C := by
    euclid_apply parallel_imp_eq_alternateAngles BC DA AC_line C A B D
    euclid_finish
  have h_tri_BCA : Triangle B C A := by
    euclid_finish
  have h_tri_DAC : Triangle D A C := by
    euclid_finish
  euclid_apply congruentTriangles_ASA C A B A C D
  euclid_finish

theorem rectangle_if_quadrilateral_with_four_rightAngles:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠ D:A:B = ∟ ∧
    ∠ A:B:C = ∟ ∧
    ∠ B:C:D = ∟ ∧
    ∠ C:D:A = ∟
    → Rectangle A B C D AB BC CD DA := by
  euclid_intros
  have h_para_DA_BC : ¬ DA.intersectsLine BC := by
    euclid_apply parallel_if_supp_consecutiveAngles DA BC AB A B D C
    euclid_finish
  have h_para_AB_CD : ¬ AB.intersectsLine CD := by
    euclid_apply parallel_if_supp_consecutiveAngles AB CD BC B C A D
    euclid_finish
  euclid_finish


theorem rectangle_if_parallelogram_with_eq_diagonals:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    Parallelogram A B C D AB BC CD DA ∧
    |(A─C)| = |(B─D)|
    → Rectangle A B C D AB BC CD DA := by
  euclid_intros
  have h_tri_BDA: Triangle B D A := by euclid_finish
  have h_tri_DBC: Triangle D B C := by euclid_finish
  euclid_apply line_from_points B D as BD
  have h_angle_ADB_eq_CBD: ∠ A:D:B = ∠ C:B:D := by
    euclid_apply parallel_imp_eq_alternateAngles DA BC BD D B A C
    euclid_finish
  have h_angle_ABD_eq_CDB: ∠ A:B:D = ∠ C:D:B := by
    euclid_apply parallel_imp_eq_alternateAngles AB CD BD B D A C
    euclid_finish
  have h_cong_opposite_triangles: CongruentTriangles B D A D B C := by
    euclid_apply congruentTriangles_ASA B D A D B C
    euclid_finish
  have h_AB_eq_CD : |(A─B)| = |(D─C)| := by euclid_finish
  have h_AD_eq_BC : |(A─D)| = |(B─C)| := by euclid_finish
  have h_tri_ABC: Triangle A B C := by euclid_finish
  have h_tri_DCB: Triangle D C B := by euclid_finish
  have h_BC_common: |(B─C)| = |(C─B)| := by euclid_finish
  have h_cong_adjacent_triangles: CongruentTriangles A B C D C B := by
    euclid_apply congruentTriangles_SSS A B C D C B
    euclid_finish
  have h_ABC_eq_DCB: ∠ A:B:C = ∠ D:C:B := by euclid_finish
  euclid_apply line_from_points B C as BC_line
  have h_angles_supplementary: ∠ A:B:C + ∠ B:C:D = ∟ + ∟ := by
    euclid_apply parallel_imp_supp_consecutiveAngles AB CD BC_line B C A D
    euclid_finish
  have h_angle_commutes : ∠ D:C:B = ∠ B:C:D := by euclid_finish
  have h_ABC_is_right: ∠ A:B:C = ∟ := by euclid_finish
  have h_BCD_is_right: ∠ B:C:D = ∟ := by euclid_finish
  euclid_apply line_from_points A B as AB_line
  have h_supp_DAB_ABC: ∠ D:A:B + ∠ A:B:C = ∟ + ∟ := by
    euclid_apply parallel_imp_supp_consecutiveAngles DA BC AB_line A B D C
    euclid_finish
  have h_DAB_is_right: ∠ D:A:B = ∟ := by euclid_finish
  euclid_apply line_from_points D A as DA_line
  have h_supp_CDA_DAB: ∠ C:D:A + ∠ D:A:B = ∟ + ∟ := by
    euclid_apply parallel_imp_supp_consecutiveAngles CD AB DA_line D A C B
    euclid_finish
  have h_CDA_is_right: ∠ C:D:A = ∟ := by euclid_finish
  euclid_finish

theorem trapezoid_midsegment_parallel_base : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ distinctPointsOnLine E F EF ∧ MidPoint B E C ∧ MidPoint A F D →  (¬ EF.intersectsLine CD) := by
  euclid_intros
  euclid_apply line_from_points A E as AE
  euclid_apply intersection_lines CD AE as G
  have h1: |(A─E)| = |(E─G)| := by
    euclid_apply trapezoid_imp_similarTriangles_interior B A C G E AB CD
    euclid_apply  similar_AA B A E C G E
    euclid_assert |(B─E)| = |(C─E)|
    euclid_apply congruentTriangles_ASA B E A C E G
    euclid_finish
  have h2: ¬ EF.intersectsLine CD := by
    euclid_apply triangleMidsegment_parallel_base A D G F E DA CD AE
    euclid_finish
  euclid_finish

end LeanGeo
