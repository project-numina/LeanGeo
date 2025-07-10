import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Angle
set_option maxHeartbeats 0
open LeanGeo
namespace LeanGeo
--parallelogram
theorem parallelogram_adjacent_angles_supplementary :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    parallelogram A B C D AB BC CD DA
    → ∠ D:A:B + ∠ A:B:C = ∟ + ∟ := by
  euclid_intros
  have h_para_DA_BC : ¬ DA.intersectsLine BC := by
    euclid_finish
  have h_not_coll_ABC : ¬ coll A B C := by
    euclid_finish
  euclid_apply extend_point BC C B as F
  have h_alt_angles_eq : ∠ D:A:B = ∠ A:B:F := by
    euclid_apply parallel_eqAlternateAngles DA BC AB A B D F
    euclid_finish
  have h_supp_angles : ∠ A:B:C + ∠ A:B:F = ∟ + ∟ := by
    euclid_apply supplementaryAngle_line A C B F
    euclid_finish
  euclid_finish

theorem parallelogram_opposite_sides_equal :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    parallelogram A B C D AB BC CD DA
    → |(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)| := by
  euclid_intros
  have h_tri_ABC : triangle A B C := by
    euclid_finish
  have h_tri_CDA : triangle C D A := by
    euclid_finish
  have h_A_neq_C : A ≠ C := by
    euclid_finish
  euclid_apply line_from_points A C h_A_neq_C as AC
  have h_angle_CAB_eq_ACD : ∠C:A:B = ∠A:C:D := by
    euclid_apply parallel_eqAlternateAngles AB CD AC A C B D
    euclid_finish
  have h_angle_BCA_eq_DAC : ∠B:C:A = ∠D:A:C := by
    euclid_apply parallel_eqAlternateAngles BC DA AC C A B D
    euclid_finish
  have h_sum_ABC : ∠C:B:A + ∠B:C:A + ∠C:A:B = ∟ + ∟ := by
    euclid_apply triangle_angleSum A B C
    euclid_finish
  have h_sum_CDA : ∠A:D:C + ∠D:A:C + ∠A:C:D = ∟ + ∟ := by
    euclid_apply triangle_angleSum C D A
    euclid_finish
  have h_angle_CBA_eq_ADC : ∠C:B:A = ∠A:D:C := by
    euclid_finish
  euclid_apply congruent_AAS C A B A C D
  euclid_finish

theorem parallelogram_opposite_angles_equal:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    parallelogram A B C D AB BC CD DA →
    ∠D:A:B = ∠B:C:D ∧ ∠A:B:C = ∠C:D:A := by
  euclid_intros
  constructor
  ·
    euclid_apply line_from_points B D as BD
    have h1: ∠A:B:D = ∠C:D:B := by
      euclid_apply parallel_eqAlternateAngles AB CD BD B D A C
      euclid_finish
    have h2: ∠A:D:B = ∠C:B:D := by
      euclid_apply parallel_eqAlternateAngles DA BC BD D B A C
      euclid_finish
    euclid_apply congruent_ASA B D A D B C
    euclid_finish
  ·
    euclid_apply line_from_points A C as AC
    have h3: ∠B:A:C = ∠D:C:A := by
      euclid_apply parallel_eqAlternateAngles AB CD AC A C B D
      euclid_finish
    have h4: ∠B:C:A = ∠D:A:C := by
      euclid_apply parallel_eqAlternateAngles BC DA AC C A B D
      euclid_finish
    euclid_apply congruent_ASA A C B C A D
    euclid_finish


theorem parallelogram_diagonals_bisect_each_other:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    parallelogram A B C D AB BC CD DA →
    ∃ M, midpoint A M C ∧ midpoint B M D := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B D as BD
  have h_intersect : AC.intersectsLine BD := by
    euclid_finish
  euclid_apply intersection_lines AC BD as M
  use M
  have h_tri_ACB : triangle A C B := by
    euclid_finish
  have h_tri_CAD : triangle C A D := by
    euclid_finish
  have h_B_opp_D_AC : B.opposingSides D AC := by
    euclid_finish
  have h_angle_ACB_CAD : ∠ A:C:B = ∠ C:A:D := by
    euclid_apply parallel_eqAlternateAngles BC DA AC C A B D
    euclid_finish
  have h_angle_CAB_ACD : ∠ C:A:B = ∠ A:C:D := by
    euclid_apply parallel_eqAlternateAngles AB CD AC A C B D
    euclid_finish
  have h_congr_ACB_CAD : congruentTriangle A C B C A D := by
    euclid_apply congruent_ASA A C B C A D
    euclid_finish
  have h_AB_eq_CD : |(A─B)| = |(C─D)| := by
    euclid_finish
  have h_between_AMC : between A M C := by
    euclid_finish
  have h_coll_BMD : coll B M D := by
    euclid_finish
  have h_AB_neq_CD : AB ≠ CD := by
    euclid_finish
  have h_sim_ABM_CDM : similarTriangle A B M C D M := by
    euclid_apply para_similar_in A B C D M AB CD
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

theorem opposite_angles_equal_parallelogram:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠ D:A:B = ∠ B:C:D ∧
    ∠ A:B:C = ∠ C:D:A
    → parallelogram A B C D AB BC CD DA := by
  euclid_intros
  have h_quad_angle_sum : ∠ D:A:B + ∠ A:B:C + ∠ B:C:D + ∠ C:D:A = ∟ + ∟ + ∟ + ∟ := by
    have h_tri_ABC : triangle A B C := by euclid_finish
    have h_tri_ADC : triangle A D C := by euclid_finish
    have h_sum_ABC : ∠A:B:C + ∠B:C:A + ∠C:A:B = ∟ + ∟ := by
      euclid_apply triangle_angleSum A B C
      euclid_finish
    have h_sum_CDA : ∠C:D:A + ∠D:A:C + ∠A:C:D = ∟ + ∟ := by
      euclid_apply triangle_angleSum C D A
      euclid_finish
    euclid_finish
  have h_supp_consecutive_1 : ∠ D:A:B + ∠ A:B:C = ∟ + ∟ := by
    euclid_finish
  have h_BC_parallel_DA : ¬ BC.intersectsLine DA := by
    euclid_apply supplementConsecutiveAngles_parallel DA BC AB A B D C
    euclid_finish
  have h_supp_consecutive_2 : ∠ A:B:C + ∠ B:C:D = ∟ + ∟ := by
    euclid_finish
  have h_AB_parallel_CD : ¬ AB.intersectsLine CD := by
    euclid_apply supplementConsecutiveAngles_parallel AB CD BC B C A D
    euclid_finish
  constructor
  · euclid_finish
  · constructor
    · exact h_AB_parallel_CD
    · exact h_BC_parallel_DA

theorem parallelogram_eqSide : ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA ∧
   ¬(AB.intersectsLine CD) ∧
   ¬(BC.intersectsLine DA))
  → (|(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)|) := by
sorry

theorem parallelogram_eqAngle :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (¬ AB.intersectsLine CD)
  ∧ (¬ DA.intersectsLine BC)
  → ∠D:A:B = ∠B:C:D ∧ ∠A:B:C = ∠C:D:A
:= by
sorry

theorem parallelogram_diagonals_bisect :
∀ (A B C D E : Point) (AB BC CD DA AC BD : Line),
  (parallelogram A B C D AB BC CD DA)
  ∧ distinctPointsOnLine A C AC
  ∧ distinctPointsOnLine B D BD
  ∧ (twoLinesIntersectAtPoint AC BD E)
  → (midpoint A E C ∧ midpoint B E D) := by
sorry

theorem rhombus_angleBisects :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  rhombus A B C D AB BC CD DA →
     (∠B:A:C = ∠C:A:D
     ∧ ∠B:C:A = ∠A:C:D
     ∧ ∠A:B:D = ∠D:B:C
     ∧ ∠C:D:B = ∠B:D:A) := by
  euclid_intros
  -- By SSS, triangle ABC is congruent to triangle ADC.
  -- This is because all sides of a rhombus are equal, so |(A─B)| = |(A─D)| and |(B─C)| = |(D─C)|,
  -- and side AC is common to both triangles.
  have h_cong_AC : congruentTriangle A B C A D C := by
    euclid_apply congruent_SSS A B C A D C
    euclid_finish
  -- Similarly, by SSS, triangle BAD is congruent to triangle BCD.
  -- This is because |(B─A)| = |(B─C)| and |(A─D)| = |(C─D)| from the rhombus definition,
  -- and side BD is common to both triangles.
  have h_cong_BD : congruentTriangle B A D B C D := by
    euclid_apply congruent_SSS B A D B C D
    euclid_finish
  -- The four angle bisection properties follow directly from the corresponding angles
  -- in these two pairs of congruent triangles.
  split_ands
  · -- Goal: ∠B:A:C = ∠C:A:D. This follows from ΔABC ≅ ΔADC.
    euclid_finish
  · -- Goal: ∠B:C:A = ∠A:C:D. This also follows from ΔABC ≅ ΔADC.
    euclid_finish
  · -- Goal: ∠A:B:D = ∠D:B:C. This follows from ΔBAD ≅ ΔBCD.
    euclid_finish
  · -- Goal: ∠C:D:B = ∠B:D:A. This also follows from ΔBAD ≅ ΔBCD.
    euclid_finish

theorem rhombus_angleBisects_perpendicular :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  rhombus A B C D AB BC CD DA ∧ distinctPointsOnLine A C AC ∧ distinctPointsOnLine B D BD →
    perpLine AC BD := by
sorry

--rectangle
theorem parallelogram_with_right_angle_is_rectangle:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    parallelogram A B C D AB BC CD DA ∧ ∠ A:B:C = ∟
    → rectangle A B C D AB BC CD DA := by
  euclid_intros
  have h_DAB : ∠ D:A:B = ∟ := by
    have h_supplementary : ∠ A:B:C + ∠ D:A:B = ∟ + ∟ := by
      euclid_apply parallel_supplementConsecutiveAngle BC DA AB B A C D
      euclid_finish
    euclid_finish
  have h_BCD : ∠ B:C:D = ∟ := by
    have h_supplementary : ∠ A:B:C + ∠ B:C:D = ∟ + ∟ := by
      euclid_apply parallel_supplementConsecutiveAngle AB CD BC B C A D
      euclid_finish
    euclid_finish
  have h_CDA : ∠ C:D:A = ∟ := by
    have h_supplementary : ∠ D:A:B + ∠ C:D:A = ∟ + ∟ := by
      euclid_apply parallel_supplementConsecutiveAngle AB CD DA A D B C
      euclid_finish
    euclid_finish
  euclid_finish

theorem rectangle_dignonals_equal:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    rectangle A B C D AB BC CD DA →
    |(A─B)| = |(C─D)| ∧ |(B─C)| = |(A─D)| := by
  euclid_intros
  have h_par_AB_CD : ¬ AB.intersectsLine CD := by
    euclid_apply line_from_points B C as BC_line
    euclid_apply supplementConsecutiveAngles_parallel AB CD BC_line B C A D
    euclid_finish
  have h_par_BC_DA : ¬ BC.intersectsLine DA := by
    euclid_apply line_from_points C D as CD_line
    euclid_apply supplementConsecutiveAngles_parallel BC DA CD_line C D B A
    euclid_finish
  euclid_apply line_from_points A C as AC_line
  have h_ang1 : ∠ B:A:C = ∠ D:C:A := by
    euclid_apply parallel_eqAlternateAngles AB CD AC_line A C B D
    euclid_finish
  have h_ang2 : ∠ B:C:A = ∠ D:A:C := by
    euclid_apply parallel_eqAlternateAngles BC DA AC_line C A B D
    euclid_finish
  have h_tri_BCA : triangle B C A := by
    euclid_finish
  have h_tri_DAC : triangle D A C := by
    euclid_finish
  euclid_apply congruent_ASA C A B A C D
  euclid_finish


theorem quadrilateral_with_four_right_angles_is_rectangle:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠ D:A:B = ∟ ∧
    ∠ A:B:C = ∟ ∧
    ∠ B:C:D = ∟ ∧
    ∠ C:D:A = ∟
    → rectangle A B C D AB BC CD DA := by
  euclid_intros
  have h_para_DA_BC : ¬ DA.intersectsLine BC := by
    euclid_apply supplementConsecutiveAngles_parallel DA BC AB A B D C
    euclid_finish
  have h_para_AB_CD : ¬ AB.intersectsLine CD := by
    euclid_apply supplementConsecutiveAngles_parallel AB CD BC B C A D
    euclid_finish
  euclid_finish


theorem parallelogram_diagonals_equal_is_rectangle:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    parallelogram A B C D AB BC CD DA ∧
    |(A─C)| = |(B─D)|
    → rectangle A B C D AB BC CD DA := by
  euclid_intros
  have h_tri_BDA: triangle B D A := by euclid_finish
  have h_tri_DBC: triangle D B C := by euclid_finish
  euclid_apply line_from_points B D as BD
  have h_angle_ADB_eq_CBD: ∠ A:D:B = ∠ C:B:D := by
    euclid_apply parallel_eqAlternateAngles DA BC BD D B A C
    euclid_finish
  have h_angle_ABD_eq_CDB: ∠ A:B:D = ∠ C:D:B := by
    euclid_apply parallel_eqAlternateAngles AB CD BD B D A C
    euclid_finish
  have h_cong_opposite_triangles: congruentTriangle B D A D B C := by
    euclid_apply congruent_ASA B D A D B C
    euclid_finish
  have h_AB_eq_CD : |(A─B)| = |(D─C)| := by euclid_finish
  have h_AD_eq_BC : |(A─D)| = |(B─C)| := by euclid_finish
  have h_tri_ABC: triangle A B C := by euclid_finish
  have h_tri_DCB: triangle D C B := by euclid_finish
  have h_BC_common: |(B─C)| = |(C─B)| := by euclid_finish
  have h_cong_adjacent_triangles: congruentTriangle A B C D C B := by
    euclid_apply congruent_SSS A B C D C B
    euclid_finish
  have h_ABC_eq_DCB: ∠ A:B:C = ∠ D:C:B := by euclid_finish
  euclid_apply line_from_points B C as BC_line
  have h_angles_supplementary: ∠ A:B:C + ∠ B:C:D = ∟ + ∟ := by
    euclid_apply parallel_supplementConsecutiveAngle AB CD BC_line B C A D
    euclid_finish
  have h_angle_commutes : ∠ D:C:B = ∠ B:C:D := by euclid_finish
  have h_ABC_is_right: ∠ A:B:C = ∟ := by euclid_finish
  have h_BCD_is_right: ∠ B:C:D = ∟ := by euclid_finish
  euclid_apply line_from_points A B as AB_line
  have h_supp_DAB_ABC: ∠ D:A:B + ∠ A:B:C = ∟ + ∟ := by
    euclid_apply parallel_supplementConsecutiveAngle DA BC AB_line A B D C
    euclid_finish
  have h_DAB_is_right: ∠ D:A:B = ∟ := by euclid_finish
  euclid_apply line_from_points D A as DA_line
  have h_supp_CDA_DAB: ∠ C:D:A + ∠ D:A:B = ∟ + ∟ := by
    euclid_apply parallel_supplementConsecutiveAngle CD AB DA_line D A C B
    euclid_finish
  have h_CDA_is_right: ∠ C:D:A = ∟ := by euclid_finish
  euclid_finish
--

theorem parallelogram_median_mid_mid_para : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), parallelogram A B C D AB BC CD DA ∧ distinctPointsOnLine E F EF ∧ midpoint B E C ∧ midpoint A F D →  (¬ EF.intersectsLine CD) := by
  euclid_intros
  euclid_apply parallelogram_eqSide A B C D AB BC CD DA
  have h0: parallelogram E F D C EF DA CD BC := by
    have h1: A.sameSide B EF := by
      euclid_apply quadrilateral_line_from_side_sameside A B C D E F AB BC CD DA EF
      euclid_finish
    euclid_assert formQuadrilateral E F D C EF DA CD BC
    euclid_apply parallelogram_tests E F D C EF DA CD BC
    euclid_finish
  euclid_finish

theorem trapezoid_median_mid_mid_para : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ distinctPointsOnLine E F EF ∧ midpoint B E C ∧ midpoint A F D →  (¬ EF.intersectsLine CD) := by
  euclid_intros
  euclid_apply line_from_points A E as AE
  euclid_apply intersection_lines CD AE as G
  have h1: |(A─E)| = |(E─G)| := by
    euclid_apply para_similar_in B A C G E AB CD
    euclid_apply  similar_AA B A E C G E
    euclid_assert |(B─E)| = |(C─E)|
    euclid_apply congruent_ASA B E A C E G
    euclid_finish
  have h2: ¬ EF.intersectsLine CD := by
    euclid_apply triangle_median_line_parallel A D G F E DA CD AE
    euclid_finish
  euclid_finish
end LeanGeo
