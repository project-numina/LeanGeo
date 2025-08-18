import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Distance
import LeanGeo.Theorem.Basic.PerpBisector
import LeanGeo.Theorem.Triangle.Basic
import LeanGeo.Theorem.Triangle.IsoTriangle

set_option maxHeartbeats 0
namespace LeanGeo

theorem eq_centralAngles_if_eq_chords : ∀ (a b c d o: Point) (O : Circle), a.onCircle O ∧ b.onCircle O ∧ c.onCircle O ∧ d.onCircle O ∧  o.isCentre O ∧ |(a─b)| = |(c─d)| → ∠a:o:b =∠ c:o:d := by
  euclid_intros
  by_cases h : a = b
  · euclid_assert c = d
    euclid_apply coincident_angle_eq_zero b o
    euclid_apply coincident_angle_eq_zero d o
    euclid_finish
  · -- Case a ≠ b
    euclid_assert c ≠ d
    by_cases h2 : Coll a o b
    · euclid_assert between a o b
      euclid_assert |(a─b)| = |(a─o)| + |(o─b)|
      euclid_assert |(c─d)| = |(c─o)| + |(o─d)|
      euclid_apply between_if_sum c d o
      euclid_finish
    · by_cases h3: Coll c o d
      · euclid_apply between_if_sum a b o
        euclid_finish
      · euclid_apply congruentTriangles_SSS a o b c o d
        euclid_finish

theorem chord_perpBisector : ∀ (O A B: Point) (C: Circle) (AB L: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ PerpLine AB L
  → O.onLine L →  PerpBisector A B L := by
  euclid_intros
  euclid_apply intersection_lines AB L as F
  have h1 : |(A─F)| = |(F─B)| := by
    by_cases Triangle A B O
    . euclid_assert Foot O F AB
      euclid_apply isoTriangle_three_lines_concidence_foot O A B F AB
      euclid_finish
    · euclid_assert between A O B
      euclid_assert O = F
      euclid_finish
  euclid_apply (perpBisector_iff A B L).mpr
  euclid_finish

theorem chord_midpoint_if_foot : ∀ (O A B D: Point) (C: Circle) (AB: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ ¬ (O.onLine AB) ∧ Foot O D AB → |(A─D)| = |(D─B)|:= by
  euclid_intros
  euclid_apply isoTriangle_three_lines_concidence_foot O A B D AB
  euclid_finish

theorem chord_midpoint_imp_foot : ∀ (O A B D: Point) (C: Circle) (AB: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ MidPoint A D B ∧ (¬O.onLine AB) → Foot O D AB:= by
  euclid_intros
  euclid_apply isoTriangle_three_lines_concidence_midpoint O A B D
  euclid_finish


theorem ThalesTheorem : ∀ (a b c o : Point) (C: Circle), o.isCentre C ∧  (Diameter a b o C) ∧ (c.onCircle C) ∧ (c ≠ a) ∧ (c ≠ b) → ∠ a:c:b = ∟ := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  euclid_apply line_from_points c a as CA
  euclid_assert between a o b
  euclid_apply line_from_points a b as ab
  euclid_assert IsoTriangle o a c
  euclid_assert IsoTriangle o b c
  euclid_apply isoTriangle_imp_eq_angles o a c
  euclid_apply isoTriangle_imp_eq_angles o b c
  euclid_assert Triangle a b c
  euclid_apply triangle_angles_sum a b c
  euclid_assert ∠o:a:c = ∠b:a:c
  euclid_assert ∠o:b:c = ∠a:b:c
  euclid_assert ∠a:c:b = ∠ a:c:o + ∠o:c:b
  euclid_finish

theorem rightAngle_imp_diameter : ∀(A B C O:Point) (Ω : Circle), O.isCentre Ω ∧ Circumcircle Ω A B C ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ ∠B:A:C = ∟ → Diameter B C O Ω := by
  euclid_intros
  euclid_apply line_from_points B O as BO
  euclid_apply intersection_circle_line_extending_points Ω BO O B as X
  have h0: X ≠ A := by
    by_contra
    euclid_apply ThalesTheorem B X C O Ω
    euclid_apply triangle_angles_sum A B C
    euclid_apply triangle_angle_positive A B C
    euclid_finish
  have h1:C = X := by
    have h2: ∠ B:A:X = ∟ := by
      euclid_apply ThalesTheorem B X A O Ω
      euclid_finish
    have h3: Coll A X C := by
      euclid_apply common_perpLine_imp_coll B A X C
      euclid_finish
    euclid_finish
  euclid_finish

theorem rightAngle_imp_diameter_onCircle : ∀ (A B C O: Point) (Ω: Circle), Diameter A B O Ω ∧ ∠A:C:B = ∟ → C.onCircle Ω := by
  euclid_intros
  by_cases C = A ∨ C = B ∨ A = B
  · euclid_finish
  · have h1: ¬ Coll A B C := by
      euclid_apply line_from_points
      euclid_finish
    euclid_apply rightTriangle_midLine_eq_half_hypotenuse C A B O
    euclid_finish

theorem diameter_longest : ∀(a b c d o: Point) (C: Circle), (Diameter a b o C) ∧ (c.onCircle C) ∧ (d.onCircle C) → |(a─b)| ≥ |(c─d)| := by
  euclid_intros
  by_cases Triangle o c d
  · euclid_apply triangle_inequality c d o
    euclid_finish
  · euclid_finish

theorem InscribedAngleTheorem_insideTriangle :
  ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (InsideTriangle O A B C AB BC CA) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_apply insideTriangle_angles_sum_eq_fullAngle A B C O AB BC CA
  euclid_apply line_from_points O C as OC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O A as OA
  euclid_apply isoTriangle_imp_eq_angles O A C
  euclid_apply isoTriangle_imp_eq_angles O C B
  euclid_apply triangle_angles_sum A O C
  euclid_apply triangle_angles_sum C O B
  euclid_finish

theorem InscribedAngleTheorem_outsideTriangle :
  ∀ (A B C O : Point) (OA OC: Line) (Ω : Circle), Triangle A B C ∧ (B.sameSide A OC ∧ B.sameSide C OA) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω) ∧ distinctPointsOnLine O A OA ∧ distinctPointsOnLine O C OC
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_assert ∠A:O:B + ∠B:O:C = ∠ A:O:C
  euclid_apply isoTriangle_imp_eq_angles O A C
  euclid_apply isoTriangle_imp_eq_angles O C B
  euclid_apply triangle_angles_sum A O C
  euclid_apply triangle_angles_sum C O B
  euclid_apply triangle_angles_sum B O A
  euclid_apply line_from_points
  euclid_finish


theorem InscribedAngleTheorem_sameSide :
  ∀ (A B C O : Point) (AB: Line) (Ω : Circle), Triangle A B C ∧  distinctPointsOnLine A B AB ∧ (O.sameSide C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_apply line_from_points O A as OA
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O C as OC
  by_cases B.sameSide C OA
  · have h1:∠B:A:O = ∠ B:A:C +∠C:A:O := by
      euclid_finish
    have h2:B.sameSide A OC := by
      by_contra
      euclid_apply intersection_lines AB OC as D
      euclid_finish
    euclid_apply InscribedAngleTheorem_outsideTriangle A B C O OA OC Ω
    euclid_finish
  · by_cases A.sameSide C OB
    · have h3:A.sameSide B OC := by
        by_contra
        euclid_apply intersection_lines AB OC as D
        euclid_finish
      euclid_apply InscribedAngleTheorem_outsideTriangle B A C O OB OC Ω
      euclid_finish
    · by_cases C.onLine OB
      · euclid_apply isoTriangle_imp_eq_angles O A C
        euclid_apply triangle_ex_angle_eq C O A B
        euclid_finish
      · by_cases C.onLine OA
        · euclid_apply isoTriangle_imp_eq_angles O B C
          euclid_apply triangle_ex_angle_eq C O B A
          euclid_finish
        · euclid_assert InsideTriangle O A B C AB BC AC
          euclid_apply InscribedAngleTheorem_insideTriangle A B C O AB BC AC Ω
          euclid_finish

theorem InscribedAngleTheorem_opposingSides:
∀ (A B C O : Point) (AB: Line) (Ω : Circle), Triangle A B C ∧  distinctPointsOnLine A B AB ∧ (O.opposingSides C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B + ∠ A:C:B + ∠ A:C:B = ∟ + ∟ + ∟ + ∟:= by
  euclid_intros
  euclid_apply line_from_points O A as OA
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O C as OC
  euclid_apply intersection_lines OC AB as D
  euclid_apply triangle_angles_sum
  euclid_apply isoTriangle_imp_eq_angles
  euclid_finish

theorem cyclic_eq_angles: ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ C≠ A ∧ D ≠ A ∧ C ≠ B ∧ D ≠ B ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ D.onCircle Ω ∧ C.sameSide D AB → ∠B:C:A = ∠B:D:A := by
  euclid_intros
  euclid_apply exists_centre Ω as O
  by_cases O.sameSide C AB
  · euclid_assert O.sameSide D AB
    euclid_apply InscribedAngleTheorem_sameSide A B C O AB Ω
    euclid_apply InscribedAngleTheorem_sameSide A B D O AB Ω
    euclid_finish
  · by_cases O.onLine AB
    · euclid_apply ThalesTheorem A B C O Ω
      euclid_apply ThalesTheorem A B D O Ω
      euclid_finish
    · euclid_apply InscribedAngleTheorem_opposingSides A B C O AB Ω
      euclid_apply InscribedAngleTheorem_opposingSides A B D O AB Ω
      euclid_finish

theorem cyclic_supp_angles : ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ DistinctFourPoints A B C D ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ D.onCircle Ω ∧ C.opposingSides D AB → ∠B:C:A + ∠B:D:A = ∟ + ∟ := by
  euclid_intros
  euclid_apply exists_centre Ω as O
  by_cases O.sameSide C AB
  · euclid_assert O.opposingSides D AB
    euclid_apply InscribedAngleTheorem_sameSide A B C O AB Ω
    euclid_apply InscribedAngleTheorem_opposingSides A B D O AB Ω
    euclid_finish
  · by_cases O.onLine AB
    · euclid_apply ThalesTheorem A B C O Ω
      euclid_apply ThalesTheorem A B D O Ω
      euclid_finish
    · euclid_apply InscribedAngleTheorem_sameSide A B D O AB Ω
      euclid_apply InscribedAngleTheorem_opposingSides A B C O AB Ω
      euclid_finish

theorem cyclic_sameside_symm : ∀ (A B C D : Point) (AB CD : Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧ C.sameSide D AB → A.sameSide B CD := by
  euclid_intros
  by_contra
  euclid_apply intersection_lines AB CD as E
  euclid_finish

theorem cyclic_opposingSides_symm : ∀ (A B C D : Point) (AB CD : Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ distinctPointsOnLine C D CD ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧ C.opposingSides D AB → A.opposingSides B CD := by
  euclid_intros
  by_contra
  euclid_apply intersection_lines AB CD as E
  euclid_finish

theorem cyclic_opposingSides_imp_sameSide : ∀ (A B C D : Point) (CD AC : Line) (Ω : Circle), A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧ distinctPointsOnLine A C AC ∧ distinctPointsOnLine C D CD ∧ B.opposingSides D AC → A.sameSide B CD := by
  euclid_intros
  by_contra
  euclid_apply line_from_points A B as AB
  euclid_apply intersection_lines AB CD as E
  euclid_finish

theorem cyclic_eq_angles' : ∀ (A B C D: Point) (AB : Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ C.sameSide D AB ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω → ∠C:A:D = ∠C:B:D := by
  euclid_intros
  by_cases C = D
  · euclid_apply coincident_angle_eq_zero
    euclid_finish
  · euclid_apply line_from_points C D as CD
    euclid_apply cyclic_sameside_symm A B C D AB CD Ω
    euclid_apply cyclic_eq_angles C D A B CD Ω
    euclid_finish

theorem cyclic_supp_angles' : ∀ (A B C D: Point) (AB : Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ C.opposingSides D AB ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω → ∠C:A:D + ∠C:B:D = ∟ + ∟ := by
  euclid_intros
  euclid_apply line_from_points C D as CD
  euclid_apply cyclic_opposingSides_symm A B C D AB CD Ω
  euclid_apply cyclic_supp_angles C D A B CD Ω
  euclid_finish

theorem IntersectingChordsTheorem : ∀ (A B C D E : Point) (Ω: Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
  DistinctFourPoints A B C D ∧
  between A E B ∧ between C E D → |(A─E)| * |(E─B)| = |(C─E)| * |(E─D)|:= by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points C D as CD
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B D as BD
  have h1: ∠C:B:E = ∠A:D:E := by
    euclid_apply cyclic_eq_angles A C B D AC Ω
    euclid_apply coll_angles_eq
    euclid_finish
  have h2: ∠B:C:E = ∠D:A:E := by
    euclid_apply cyclic_eq_angles B D A C BD Ω
    euclid_apply coll_angles_eq
    euclid_finish
  euclid_apply similar_AA C B E A D E
  euclid_finish

theorem IntersectingSecantsTheorem :∀ (A B C D E : Point) (Ω: Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
  DistinctFourPoints A B C D ∧
  between A B E ∧ between D C E → |(A─E)| * |(E─B)| = |(C─E)| * |(E─D)|:= by
  euclid_intros
  euclid_apply line_from_points A C as AC
  have h1: ∠C:B:E = ∠E:D:A := by
    euclid_apply cyclic_supp_angles A C B D AC Ω
    euclid_apply coll_angles_eq
    euclid_finish
  euclid_apply line_from_points B D as BD
  have h2: ∠B:C:E = ∠E:A:D := by
    euclid_apply cyclic_supp_angles B D A C BD Ω
    euclid_apply coll_angles_eq
    euclid_finish
  euclid_apply similar_AA B C E D A E
  euclid_finish

theorem tangentLine_not_in_circle: ∀ (A B O : Point) (Ω: Circle) (L: Line), TangentLineCircleAtPoint A O L Ω ∧ distinctPointsOnLine A B L → B.outsideCircle Ω := by
  euclid_intros
  euclid_apply foot_shortest
  euclid_finish

theorem tangentLine_sameSide_if_onCircle: ∀ (A B C O : Point) (Ω: Circle) (L: Line), TangentLineCircleAtPoint A O L Ω ∧ DistinctThreePoints A B C ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω → B.sameSide C L := by
  euclid_intros
  by_contra
  euclid_apply line_from_points B C as BC
  euclid_apply intersection_lines BC L as D
  have h: D.outsideCircle Ω := by
    euclid_apply tangentLine_not_in_circle A D O Ω L
    euclid_finish
  euclid_finish

theorem AlternateSegmentTheorem_to_diameter : ∀ (A B D X O: Point) (C: Circle) (L AX: Line), Diameter A X O C ∧ B.onCircle C ∧ B ≠ X ∧ distinctPointsOnLine A D L ∧ TangentLineCircleAtPoint A O L C ∧ distinctPointsOnLine A X AX ∧ B.sameSide D AX → ∠D:A:B = ∠A:X:B := by
  euclid_intros
  euclid_apply tangentLine_sameSide_if_onCircle A B X O C L
  have h1: ∠X:A:B + ∠D:A:B = ∟ := by
    euclid_finish
  have h2: ∠X:A:B + ∠A:X:B = ∟ := by
    euclid_apply ThalesTheorem A X B O
    euclid_apply triangle_angles_sum A X B
    euclid_finish
  euclid_finish

theorem AlternateSegmentTheorem : ∀ (A B C D O: Point) (Ω : Circle) (AB BC CA L : Line),
  (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ formTriangle A B C AB BC CA ∧ O.isCentre Ω ∧
  distinctPointsOnLine A D L ∧ TangentLineCircleAtPoint A O L Ω ∧ B.sameSide D CA
  → ∠ B:A:D = ∠ B:C:A := by
  euclid_intros
  euclid_apply line_from_points O A as OA
  euclid_apply intersection_circle_line_extending_points Ω OA O A as X
  by_cases C = X
  · euclid_apply AlternateSegmentTheorem_to_diameter A B D X O Ω L OA
    euclid_finish
  · by_cases B.sameSide D OA
    · euclid_apply AlternateSegmentTheorem_to_diameter A B D X O Ω L OA
      euclid_apply tangentLine_sameSide_if_onCircle A B X O Ω L
      euclid_apply tangentLine_sameSide_if_onCircle A C X O Ω L
      euclid_assert C.sameSide X AB
      euclid_apply cyclic_eq_angles A B C X AB Ω
      euclid_finish
    · euclid_apply extend_point L D A as E
      by_cases B ≠ X
      · euclid_assert E.sameSide B OA
        euclid_apply tangentLine_sameSide_if_onCircle A B X O Ω L
        euclid_apply tangentLine_sameSide_if_onCircle A C X O Ω L
        euclid_apply AlternateSegmentTheorem_to_diameter A B E X O Ω L OA
        euclid_apply line_from_points A B as AB
        euclid_assert X.opposingSides C AB
        euclid_apply cyclic_supp_angles A B C X AB Ω
        euclid_finish
      · euclid_apply ThalesTheorem A B C O
        euclid_finish

theorem TangentSecantTheorem_subcase:∀ (P A B C O: Point) (Ω: Circle)(L:Line), A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ between P B C ∧ distinctPointsOnLine P A L ∧ TangentLineCircleAtPoint A O L Ω → |(P─A)| * |(P─A)| = |(P─B)| * |(P─C)| := by
  euclid_intros
  have h1: A ≠ B := by
    by_contra
    euclid_apply tangentLine_not_in_circle B C O Ω L
    euclid_finish
  have h2: A ≠ C := by
    by_contra
    euclid_apply tangentLine_not_in_circle C B O Ω L
    euclid_finish
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  have h1: ∠B:A:P = ∠A:C:P := by
    euclid_apply AlternateSegmentTheorem A B C P O Ω AB BC AC L
    euclid_apply coll_angles_eq
    euclid_finish
  have h2: ∠A:P:B = ∠C:P:A := by
    euclid_apply coll_angles_eq
    euclid_finish
  euclid_apply similar_AA A P B C P A
  euclid_finish

theorem TangentSecantTheorem:∀ (P A B C O: Point) (Ω: Circle)(L:Line), A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ B ≠ C ∧ Coll P B C ∧ distinctPointsOnLine P A L ∧ TangentLineCircleAtPoint A O L Ω → |(P─A)| * |(P─A)| = |(P─B)| * |(P─C)| := by
  euclid_intros
  have h1: P.outsideCircle Ω := by
    euclid_apply tangentLine_not_in_circle A P O Ω L
    euclid_finish
  have h2: between P B C ∨ between P C B := by
    euclid_finish
  rcases h2 with h3|h4
  · euclid_apply TangentSecantTheorem_subcase P A B C O Ω L
    euclid_finish
  · euclid_apply TangentSecantTheorem_subcase P A C B O Ω L
    euclid_finish

theorem eq_len_of_tangents : ∀ (P A B O: Point) (Ω: Circle) (L1 L2: Line), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine P A L1 ∧ distinctPointsOnLine P B L2 ∧ TangentLineCircleAtPoint A O L1 Ω ∧ TangentLineCircleAtPoint B O L2 Ω → |(P─A)| = |(P─B)| := by
  euclid_intros
  have h1: |(P─A)| * |(P─A)| = |(P─B)| * |(P─B)| := by
    euclid_apply exists_point_inside_circle Ω as Q
    have h2: P.outsideCircle Ω := by
      euclid_apply tangentLine_not_in_circle A P O Ω L1
      euclid_finish
    euclid_apply line_from_points P Q as PQ
    euclid_apply intersection_circle_line_between_points Ω PQ Q P as D
    euclid_apply intersection_circle_line_extending_points Ω PQ Q D as E
    euclid_apply TangentSecantTheorem P A D E O Ω L1
    euclid_apply TangentSecantTheorem P B D E O Ω L2
    euclid_finish
  have h3: |(P─A)| > 0 := by
    euclid_finish
  have h4: |(P─B)| > 0 := by
    euclid_finish
  nlinarith

theorem distinctThreePoints_onCircle_formTriangle : ∀ (A B C O : Point) (Γ : Circle),
  A.onCircle Γ ∧ B.onCircle Γ ∧ C.onCircle Γ ∧ O.isCentre Γ ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A
  → Triangle A B C := by
  euclid_intros
  euclid_finish

theorem cyclic_def : ∀ (A B C D : Point), Cyclic A B C D → ∃ (O: Circle), A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O:= by
  euclid_intros
  euclid_finish

theorem IntersectingSecantsAndChordsTheorem: ∀ (a b c d e: Point),DistinctFourPoints a b c d ∧ Cyclic a b c d ∧ (Coll a b e) ∧ (Coll c d e) → |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| := by
  euclid_intros
  euclid_apply cyclic_def a b c d as C
  by_cases between a e b
  · euclid_assert between c e d
    euclid_apply IntersectingChordsTheorem a b c d e C
    euclid_finish
  · euclid_apply IntersectingSecantsTheorem
    euclid_finish

theorem pow_of_point_in_circle_on_diameter: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ between A P B ∧ Coll A O B→ |(P─A)| * |(P─B)| + |(P─O)| * |(P─O)| = |(O─A)| * |(O─A)| := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem pow_of_point_out_circle_on_diameter: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧  between P A B ∧ Coll A O B→ |(P─A)| * |(P─B)| + |(O─A)| * |(O─A)|= |(P─O)| * |(P─O)|  := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem pow_of_point_in_circle: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ between A P B → |(P─A)| * |(P─B)| + |(P─O)| * |(P─O)|= |(O─A)| * |(O─A)|  := by
  euclid_intros
  by_cases h: Coll A O B
  · euclid_apply pow_of_point_in_circle_on_diameter P O A B C
    euclid_finish
  · euclid_apply line_from_points O P as l
    euclid_apply intersections_circle_line C l as (S,T)
    have h1 : |(P─A)| * |(P─B)| = |(P─S)| * |(P─T)| := by
      euclid_apply IntersectingSecantsAndChordsTheorem S T A B P
      euclid_finish
    rw[h1]
    euclid_finish

theorem pow_of_point_out_circle: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧  between P A B → |(P─A)| * |(P─B)| + |(O─A)| * |(O─A)|= |(P─O)| * |(P─O)|  := by
  euclid_intros
  by_cases h: Coll A O B
  · euclid_apply pow_of_point_out_circle_on_diameter P O A B C
    euclid_finish
  · euclid_apply line_from_points O P as l
    euclid_apply intersections_circle_line C l as (S,T)
    have h1 : |(P─A)| * |(P─B)| = |(P─S)| * |(P─T)| := by
      euclid_apply IntersectingSecantsAndChordsTheorem S T A B P
      euclid_finish
    rw[h1]
    euclid_finish

theorem pow_of_point_in_circle' : ∀ (A B C : Point) (L : Line) (Ω : Circle), A.insideCircle Ω ∧ A.onLine L ∧ LineIntersectsCircleAtTwoPoints B C L Ω → Pow(A, Ω) + |(A─B)| * |(A─C)| = 0:= by
    euclid_intros
    euclid_apply exists_centre Ω as O
    euclid_apply pow_of_point_in_circle A O B C Ω
    euclid_finish

theorem pow_of_point_out_circle' : ∀ (A B C : Point) (L : Line) (Ω : Circle), A.outsideCircle Ω ∧ A.onLine L ∧ LineIntersectsCircleAtTwoPoints B C L Ω → Pow(A, Ω) = |(A─B)| * |(A─C)| := by
    euclid_intros
    euclid_apply exists_centre Ω as O
    by_cases between A B C
    · euclid_apply pow_of_point_out_circle A O B C Ω
      euclid_finish
    · euclid_apply pow_of_point_out_circle A O C B Ω
      euclid_finish

theorem eq_chords_eq_or_supp_inscribedAngles: ∀
(A B C A' B' C' : Point) (Ω : Circle), DistinctThreePoints A B C ∧ DistinctThreePoints A' B' C' ∧
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω
  ∧ A'.onCircle Ω ∧ B'.onCircle Ω ∧ C'.onCircle Ω
  ∧ (|(A─C)| = |(A'─C')|)
  → ∠ A:B:C = ∠ A':B':C' ∨ ∠ A:B:C + ∠ A':B':C' = ∟ + ∟
:= by
  euclid_intros
  euclid_apply exists_centre Ω as O
  have h_central_angles_eq : ∠ A:O:C = ∠ A':O:C' := by
    euclid_apply eq_centralAngles_if_eq_chords A C A' C' O Ω
    euclid_finish
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A' C' as A'C'
  by_cases hO_on_AC : O.onLine AC
  · have h_diam_AC : Diameter A C O Ω := by
      euclid_finish
    have h_angle_ABC : ∠ A:B:C = ∟ := by
      euclid_apply ThalesTheorem A C B O Ω
      euclid_finish
    have h_diam_A'C' : Diameter A' C' O Ω := by
      euclid_finish
    have h_angle_A'B'C' : ∠ A':B':C' = ∟ := by
      euclid_apply ThalesTheorem A' C' B' O Ω
      euclid_finish
    right
    euclid_finish
  · have hO_not_on_A'C' : ¬(O.onLine A'C') := by
      by_contra h_contra
      have h_O_on_AC_implied : O.onLine AC := by
        euclid_finish
      exact hO_on_AC h_O_on_AC_implied
    have h_tri_ACB : Triangle A C B := by
      euclid_finish
    have h_tri_A'C'B' : Triangle A' C' B' := by
      euclid_finish
    by_cases hB_side : B.sameSide O AC
    · have h_angle_ABC : ∠ A:O:C = ∠ A:B:C + ∠ A:B:C := by
        euclid_apply InscribedAngleTheorem_sameSide A C B O AC Ω
        euclid_finish
      by_cases hB'_side : B'.sameSide O A'C'
      · have h_angle_A'B'C' : ∠ A':O:C' = ∠ A':B':C' + ∠ A':B':C' := by
          euclid_apply InscribedAngleTheorem_sameSide A' C' B' O A'C' Ω
          euclid_finish
        left
        euclid_finish
      · have hB'_opp : B'.opposingSides O A'C' := by
          euclid_finish
        have h_angle_A'B'C' : ∠ A':O:C' + (∠ A':B':C' + ∠ A':B':C') = ∟ + ∟ + ∟ + ∟ := by
          euclid_apply InscribedAngleTheorem_opposingSides A' C' B' O A'C' Ω
          euclid_finish
        right
        euclid_finish
    · have hB_opp : B.opposingSides O AC := by
        euclid_finish
      have h_angle_ABC : ∠ A:O:C + (∠ A:B:C + ∠ A:B:C) = ∟ + ∟ + ∟ + ∟ := by
        euclid_apply InscribedAngleTheorem_opposingSides A C B O AC Ω
        euclid_finish
      by_cases hB'_side : B'.sameSide O A'C'
      · have h_angle_A'B'C' : ∠ A':O:C' = ∠ A':B':C' + ∠ A':B':C' := by
          euclid_apply InscribedAngleTheorem_sameSide A' C' B' O A'C' Ω
          euclid_finish
        right
        euclid_finish
      · have hB'_opp : B'.opposingSides O A'C' := by
          euclid_finish
        have h_angle_A'B'C' : ∠ A':O:C' + (∠ A':B':C' + ∠ A':B':C') = ∟ + ∟ + ∟ + ∟ := by
          euclid_apply InscribedAngleTheorem_opposingSides A' C' B' O A'C' Ω
          euclid_finish
        left
        euclid_finish

theorem exists_point_on_opposing_arc  : ∀ (A B C : Point) (AB : Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ C ≠ A ∧ C ≠ B ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω → ∃ (D: Point), D.onCircle Ω ∧ D.opposingSides C AB := by
  euclid_intros
  euclid_apply exists_point_between_points_on_line AB A B as D
  euclid_apply line_from_points C D as CD
  euclid_apply intersection_circle_line_extending_points Ω CD D C as E
  use E
  euclid_finish

end LeanGeo
