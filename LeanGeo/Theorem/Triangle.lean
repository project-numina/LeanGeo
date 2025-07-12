import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Parallel
import LeanGeo.Theorem.Construction
import LeanGeo.Theorem.Position

set_option maxHeartbeats 0
open LeanGeo Elements.Book1
namespace LeanGeo

theorem triangle_anglePositive : ∀(A B C : Point) , triangle A B C → ∠A:B:C > 0 ∧ ∠A:C:B >0 ∧ ∠C:A:B >0 := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem pythagorean : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
  euclid_intros
  euclid_apply proposition_47
  euclid_finish

theorem pythagorean_point : ∀ (a b c: Point), (triangle a b c) ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  euclid_apply line_from_points c a as CA
  have h_form_tri : formTriangle a b c AB BC CA := by
    euclid_finish
  euclid_apply pythagorean a b c AB BC CA
  euclid_finish

theorem triangle_angleSum : ∀(A B C : Point) , triangle A B C → ∠A:B:C +∠B:C:A + ∠C:A:B = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points C A as CA
  euclid_apply extend_point BC B C as D
  euclid_apply Book_triangle_angleSum A B C D AB BC CA
  euclid_finish

theorem triangle_exteriorAngle : ∀ (a b c d: Point), (triangle a b c) ∧ (between a b d) → ∠d:b:c = ∠b:c:a + ∠c:a:b := by
  euclid_intros
  euclid_apply triangle_angleSum a b c
  --euclid_assert ∠c:b:d +∠c:b:a = ∟ + ∟
  euclid_apply supplementaryAngle_line c a b d
  euclid_finish

theorem acute_triangle_foot_between : ∀(A B C D: Point) (BC: Line), distinctPointsOnLine B C BC ∧ foot A D BC ∧ ∠A:B:C < ∟ ∧ ∠ A:C:B < ∟ → between B D C := by
  euclid_intros
  have h2: ¬(between D B C):= by
    by_contra
    euclid_apply triangle_exteriorAngle D B A C
    euclid_finish
  have h3: ¬(between B C D):= by
    by_contra
    euclid_apply triangle_exteriorAngle D C A B
    euclid_finish
  euclid_finish

theorem congruent_SSS : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧ |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)| → congruentTriangle A B C D E F := by
  sorry

theorem congruent_SAS : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧ |(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)| → congruentTriangle A B C D E F := by
  sorry

theorem congruent_ASA : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧ |(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ ∠ B:A:C = ∠ E:D:F → congruentTriangle A B C D E F := by
  sorry

theorem congruent_AAS : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧ |(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ ∠ A:C:B = ∠ D:F:E → congruentTriangle A B C D E F := by
  sorry

theorem similar_AA : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧  ∠ A:B:C = ∠ D:E:F ∧ ∠ B:A:C = ∠ E:D:F → similarTriangle A B C D E F := by
  sorry

 theorem similar_SAS : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧  ∠ A:B:C = ∠ D:E:F ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| → similarTriangle A B C D E F := by
  sorry

theorem similar_SSS : ∀ (A B C D E F : Point), triangle A B C ∧ triangle D E F ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ |(B─C)| * |(F─D)| = |(C─A)| * |(E─F)| → similarTriangle A B C D E F := by
  sorry

--nlinarith makes it very slow in this proof.
theorem HL_congruent : ∀ (a b c d e f : Point) ,  rightTriangle a b c ∧ rightTriangle d e f ∧ |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| → congruentTriangle a b c d e f := by
  euclid_intros
  euclid_apply pythagorean_point a b c
  euclid_apply pythagorean_point d e f
  have h1 : |(a─b)| = |(d─e)| := by
    euclid_finish
  have h2 : |(b─c)| = |(e─f)| := by
    euclid_finish
  have h4 : |(e─f)| * |(e─f)| = |(d─e)| * |(d─e)| + |(d─f)| * |(d─f)| := by
    euclid_finish
  have h3 : |(b─c)| * |(b─c)| = |(a─b)| * |(a─b)| + |(a─c)| * |(a─c)| := by
    euclid_finish
  have h5 : |(a─c)| = |(d─f)| := by
    rw [h1, h2] at h3
    have h6 : |(a─c)| * |(a─c)| = |(d─f)| * |(d─f)| := by linarith
    have h7 : |(a─c)| > 0 := by euclid_finish
    have h8 : |(d─f)| > 0 := by euclid_finish
    euclid_finish
  euclid_apply congruent_SSS a b c d e f
  euclid_finish

theorem isoTriangle_eqAngle : ∀ (A B C : Point), isoTriangle A B C → ∠ A:B:C = ∠A:C:B := by
  euclid_intros
  euclid_apply exists_midpoint B C as D
  euclid_apply line_from_points B C as BC
  euclid_apply angle_between_transfer
  euclid_apply congruent_SSS D B A D C A
  euclid_apply angle_between_transfer
  euclid_finish

theorem eqSide_eqAngle :∀ (O A B : Point), |(O─A)|=|(O─B)| ∧ (A ≠ B) → ∠O:A:B = ∠O:B:A := by
  euclid_intros
  by_cases triangle O A B
  · euclid_assert isoTriangle O A B
    euclid_apply isoTriangle_eqAngle O A B
    euclid_finish
  · euclid_assert between A O B
    euclid_apply between_zeroAngle A O B
    euclid_apply between_zeroAngle B O A
    euclid_finish

theorem eqAngle_isoTriangle : ∀ (a b c : Point),
  (triangle a b c) ∧ (∠ a:b:c = ∠ a:c:b)
  → |(a─b)| = |(a─c)| := by
  euclid_intros
  euclid_apply line_from_points b c as BC
  euclid_apply point_not_onLine a b c BC
  euclid_apply exists_foot a BC as d
  have h1: ∠a:b:c < ∟ := by
    euclid_apply triangle_anglePositive
    euclid_apply triangle_angleSum
    euclid_finish
  have h2: ∠a:c:b < ∟ := by
    euclid_apply triangle_anglePositive
    euclid_apply triangle_angleSum
    euclid_finish
  euclid_apply acute_triangle_foot_between a b c d BC
  euclid_apply angle_between_transfer b d c a
  euclid_apply congruent_AAS a d b a d c
  euclid_finish

theorem isoTriangle_threeLine_concidence_midpoint : ∀ (a b c d: Point),
  isoTriangle a b c ∧ midpoint b d c →
  ( ∠a:d:b = ∟ ∧  ∠a:d:c = ∟ ∧  ∠d:a:b = ∠ d:a:c)
:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply congruent_SSS a b d a c d
  euclid_finish

theorem isoTriangle_threeLine_concidence_foot : ∀ (a b c d: Point)(BC : Line),
  isoTriangle a b c ∧ distinctPointsOnLine b c BC ∧ foot a d BC →
  midpoint b d c ∧  ∠a:d:b = ∟ ∧  ∠a:d:c = ∟ ∧  ∠d:a:b = ∠ d:a:c
:= by
  euclid_intros
  euclid_apply isoTriangle_eqAngle a b c
  have h1 : ∠a:b:c < ∟ ∧ ∠a:c:b < ∟ := by
    euclid_apply triangle_angleSum a b c
    euclid_apply triangle_anglePositive a b c
    euclid_finish
  euclid_apply acute_triangle_foot_between a b c d BC
  have h2: ∠a:d:b = ∟ := by
    euclid_finish
  have h3: ∠a:d:c = ∟ := by
    euclid_finish
  euclid_apply HL_congruent d a b d a c
  euclid_finish

theorem isoTriangle_threeLine_concidence_bisector : ∀ (a b c d: Point),
  isoTriangle a b c ∧ ∠d:a:b = ∠ d:a:c ∧ coll b c d→
  (midpoint b d c ∧  ∠a:d:b = ∟ ∧  ∠a:d:c = ∟)
:= by
  euclid_intros
  euclid_apply angle_bisector_between a b c d
  euclid_apply line_from_points
  euclid_apply congruent_SAS b a d c a d
  euclid_finish

theorem perp_bisector_eqSide : ∀ (A B C D: Point), midpoint B D C ∧ ∠A:D:B = ∟ ∧ triangle A B C → isoTriangle A B C:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_assert ∠A:D:C = ∟
  euclid_apply congruent_SAS A D B A D C
  euclid_finish

theorem triangle_median_line_parallel : ∀ (a b c d e : Point) (AB BC CA DE: Line), formTriangle a b c AB BC CA ∧ distinctPointsOnLine d e DE ∧ midpoint a d b ∧ midpoint a e c →  ¬ BC.intersectsLine DE:= by
  euclid_intros
  euclid_apply similar_SAS d a e b a c
  euclid_apply eqAlternateExteriorAngle_parallel
  euclid_finish

theorem triangle_median_line_half : ∀ (a b c d e : Point), triangle a b c ∧ midpoint a d b ∧ midpoint a e c → |(b─c)| = |(d─e)| * 2:= by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply similar_SAS d a e b a c
  have h1: |(b─a)| = |(d─a)| * 2 := by
    euclid_apply midpoint_twice
    euclid_finish
  euclid_finish

theorem self_fullAngle : ∀ (A B C O : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ insideTriangle O A B C AB BC CA → ∠A:O:C + ∠ C:O:B + ∠ B:O:A = ∟ + ∟ +  ∟ + ∟ := by
  euclid_intros
  euclid_apply triangle_angleSum A O B
  euclid_apply triangle_angleSum C O B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum A B C
  euclid_finish

theorem triangle_inside_angleSum: ∀ (A B C O : Point) (AB BC CA: Line), formTriangle A B C AB BC CA ∧ insideTriangle O A B C AB BC CA → ∠B:O:C = ∠O:B:A + ∠B:A:C + ∠A:C:O := by
  euclid_intros
  euclid_apply triangle_angleSum A O B
  euclid_apply triangle_angleSum C O B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum A B C
  euclid_finish

theorem para_similar_in : ∀ (A B C D E : Point) (AB CD : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ ¬ AB.intersectsLine CD ∧ between A E C ∧ coll B E D ∧ AB ≠ CD → similarTriangle A B E C D E := by
  euclid_intros
  euclid_apply line_from_points B D as BD
  euclid_apply line_from_points A C as AC
  euclid_assert B.opposingSides D AC
  have h1: ∠B:A:E = ∠D:C:E := by
    have h2: ∠B:A:C = ∠A:C:D := by
      euclid_apply parallel_eqAlternateAngles AB CD AC A C B D
      euclid_finish
    euclid_finish
  have h3: ∠A:B:E = ∠C:D:E := by
    have h4: ∠A:B:D = ∠C:D:B := by
      euclid_apply parallel_eqAlternateAngles AB CD BD B D A C
      euclid_finish
    euclid_finish
  euclid_apply similar_AA A B E C D E
  euclid_finish

theorem para_similar_out: ∀ (A B C D E : Point) (AB CD : Line), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ ¬ AB.intersectsLine CD ∧ between E A C ∧ coll B E D ∧ AB ≠ CD → similarTriangle E A B E C D := by
  euclid_intros
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B D as BD
  have h1: ∠E:A:B = ∠E:C:D := by
    euclid_apply parallel_eqAlternateExteriorAngle
    euclid_finish
  have h2: ∠E:B:A = ∠E:D:C := by
    euclid_apply parallel_eqAlternateExteriorAngle
    euclid_finish
  euclid_apply similar_AA E A B E C D
  euclid_finish

theorem obtuse_triangle_foot_between: ∀(A B C D: Point) (BC : Line), distinctPointsOnLine B C BC ∧ foot A D BC ∧ ∠A:B:C > ∟ → between D B C := by
  euclid_intros
  have h2: ¬(between B C D):= by
    by_contra
    euclid_apply angle_between_transfer B C D A
    euclid_apply triangle_angleSum A B D
    euclid_finish
  have h3: ¬(between B D C):= by
    by_contra
    euclid_apply angle_between_transfer B D C A
    euclid_apply triangle_angleSum A B D
    euclid_finish
  have h4: D ≠ C := by
    euclid_apply triangle_angleSum A B D
    euclid_finish
  euclid_finish

theorem rightTriangle_midLine_half: ∀ (A B C D: Point), rightTriangle A B C ∧ midpoint B D C → |(A─D)| = |(B─D)| := by
  euclid_intros
  euclid_apply exists_midpoint A C as E
  euclid_apply line_from_points A C as CA
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points D E as DE
  have h1: ∠C:E:D = ∟ := by
    euclid_apply triangle_median_line_parallel C A B E D  CA AB BC DE
    euclid_apply parallel_eqAlternateExteriorAngle  D E B A C DE AB CA
    euclid_finish
  euclid_apply perp_bisector_eqSide D A C E
  euclid_finish

theorem acute_angle_foot_equal : ∀ (A B C D : Point) (BC: Line), distinctPointsOnLine B C BC ∧ ¬ (A.onLine BC) ∧ foot A D BC ∧ ∠A:B:C < ∟ → ∠A:B:C = ∠A:B:D := by
  euclid_intros
  euclid_apply line_from_points
  euclid_apply triangle_angleSum
  euclid_finish

theorem rightTriangle_hypotenuse_longest : ∀(A B C : Point), rightTriangle A B C → |(B─C)| > |(A─B)| ∧  |(B─C)| > |(A─C)| := by
  euclid_intros
  euclid_apply pythagorean_point A B C
  euclid_finish

theorem foot_shortest : ∀ (A B C : Point) (L : Line), foot A B L ∧ distinctPointsOnLine B C L → |(A─C)| > |(A─B)| := by
  euclid_intros
  euclid_apply rightTriangle_hypotenuse_longest B A C
  euclid_finish

theorem foot_square_difference: ∀ (A B C H: Point) (BC : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ (foot A H BC) → |(A─B)| * |(A─B)| - |(H─B)| * |(H─B)| = |(A─C)| * |(A─C)| - |(C─H)| * |(C─H)| := by
  euclid_intros
  euclid_apply pythagorean_point
  euclid_finish

theorem triangle_para_similar : ∀ (A B C D E: Point) (BC DE : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine D E DE ∧ ¬ BC.intersectsLine DE ∧ coll A B D ∧ coll A C E → similarTriangle A B C A D E := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points A C as AC
  have h1: between A D B ∨ between A B D ∨ between B A D ∨ D = B := by
    euclid_finish
  rcases h1 with h2|h3|h4|h5
  · euclid_apply parallel_eqAlternateExteriorAngle E D C B A DE BC AB
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_apply parallel_eqAlternateExteriorAngle C B E D A BC DE AB
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_apply parallel_eqAlternateAngles BC DE AB B D C E
    have h6: ∠ E:A:D = ∠B:A:C := by
      euclid_apply opposite_angles_same D E A C B
      euclid_finish
    euclid_apply similar_AA A D E A B C
    euclid_finish
  · euclid_finish

theorem greater_side_greater_angle : ∀ (a b c : Point) ,
  triangle a b c ∧ (|(a─c)| > |(a─b)|) →
  (∠ a:b:c > ∠ b:c:a) :=
by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  euclid_apply line_from_points c a as CA
  euclid_apply Book_greater_side_greater_angle a b c AB BC CA
  euclid_finish

theorem apollonius_on_isoceles :
  ∀ (A B C D : Point) (BC : Line),
    isoTriangle A B C ∧
    distinctPointsOnLine B C BC ∧
    coll B D C ∧
    between B D C
    → |(A─B)| * |(A─B)| - |(A─D)| * |(A─D)| = |(B─D)| * |(C─D)| := by
  euclid_intros
  have h_A_not_on_line : ¬(A.onLine BC) := by
    euclid_apply point_not_onLine A B C BC
    euclid_finish
  euclid_apply exists_foot A BC h_A_not_on_line as H
  have h_midpoint_H : midpoint B H C := by
    euclid_apply isoTriangle_threeLine_concidence_foot A B C H BC
    euclid_finish
  by_cases h_D_eq_H : D = H
  · have h_tri_AHB : triangle H A B := by
      have h_H_neq_B: H ≠ B := by
        by_contra h_eq
        have h_midpointBHC := h_midpoint_H
        euclid_assert midpoint B B C
        euclid_finish
      euclid_finish
    have h_pyth_AB : |(A─B)| * |(A─B)| = |(A─H)| * |(A─H)| + |(B─H)| * |(B─H)| := by
      euclid_apply pythagorean_point H A B
      euclid_finish
    euclid_finish
  · have h_tri_AHB : triangle H A B := by
      have h_H_neq_B: H ≠ B := by
        by_contra h_eq
        have h_midpointBHC := h_midpoint_H
        euclid_assert midpoint B B C
        euclid_finish
      euclid_finish
    have h_tri_AHD : triangle H A D := by
      euclid_finish
    have h_pyth_AB : |(A─B)| * |(A─B)| = |(A─H)| * |(A─H)| + |(B─H)| * |(B─H)| := by
      euclid_apply pythagorean_point H A B
      euclid_finish
    have h_pyth_AD : |(A─D)| * |(A─D)| = |(A─H)| * |(A─H)| + |(D─H)| * |(D─H)| := by
      euclid_apply pythagorean_point H A D
      euclid_finish
    have h_lhs_is_diff_of_squares : |(A─B)| * |(A─B)| - |(A─D)| * |(A─D)| = |(B─H)| * |(B─H)| - |(D─H)| * |(D─H)| := by
      euclid_finish
    have h_rhs_is_diff_of_squares : |(B─D)| * |(C─D)| = |(B─H)| * |(B─H)| - |(D─H)| * |(D─H)| := by
      euclid_finish
    euclid_finish

theorem triangle_para_sameRatio: ∀ (A B C D E F G: Point) (BC DE : Line), triangle A B C ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine D E DE ∧ ¬ BC.intersectsLine DE ∧ coll A B D ∧ coll A C E ∧ F.onLine BC ∧ G.onLine DE ∧ coll A G F ∧ F ≠ B ∧ F ≠ C ∧ G ≠ D ∧ G ≠ E → |(D─G)| * |(B─C)|  =|(D─E)| *|(B─F)| := by
  euclid_intros
  euclid_apply triangle_para_similar A B C D E BC DE
  euclid_apply triangle_para_similar A B F D G BC DE
  have h1: |(D─G)| * |(A─B)| = |(B─F)| * |(A─D)| := by
    euclid_finish
  have h2: |(D─E)| * |(A─B)| = |(B─C)| * |(A─D)| := by
    euclid_finish
  have h3: |(A─B)| * |(A─D)| > 0 := by
    euclid_finish
  have h5: |(D─G)| * |(B─C)| * (|(A─B)| * |(A─D)|) =|(D─E)| * |(B─F)| * (|(A─B)| * |(A─D)|) := by
    calc
      _ = (|(D─G)| * |(A─B)|) * (|(B─C)| * |(A─D)|) := by linarith
      _ = (|(B─F)| * |(A─D)|) * (|(D─E)| * |(A─B)|) := by rw[h1,h2]
      _ = _ := by linarith
  euclid_finish
end LeanGeo
