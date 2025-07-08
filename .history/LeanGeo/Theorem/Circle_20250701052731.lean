import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Basic
import LeanGeo.Theorem.Triangle
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.PerpBisector
namespace LeanGeo
theorem eqChord_eqCentralAngle : ∀ (a b c d o: Point) (O : Circle), a.onCircle O ∧ b.onCircle O ∧ c.onCircle O ∧ d.onCircle O ∧  o.isCentre O ∧ |(a─b)| = |(c─d)| → ∠a:o:b =∠ c:o:d := by
  euclid_intros
  by_cases h : a = b
  · euclid_assert c = d
    euclid_apply angle_coincide_zero b o
    euclid_apply angle_coincide_zero d o
    euclid_finish
  · -- Case a ≠ b
    euclid_assert c ≠ d
    by_cases h2 : coll a o b
    · euclid_assert between a o b
      euclid_assert |(a─b)| = |(a─o)| + |(o─b)|
      euclid_assert |(c─d)| = |(c─o)| + |(o─d)|
      euclid_apply triangle_ineqaulity_eql c d o
      euclid_finish
    · by_cases h3: coll c o d
      · euclid_apply triangle_ineqaulity_eql a b o
        euclid_finish
      · euclid_apply congruent_SSS a o b c o d
        euclid_finish

theorem threePoints_existCircle : ∀ (A B C : Point),
  triangle A B C →
  ∃ (Ω : Circle),
    (A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω) :=
by
  euclid_intros
  euclid_apply construct_perpBisector A B as L1
  euclid_apply construct_perpBisector B C as L2
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  euclid_apply (perpBisector_equiv A B L1).mp as (P,L3)
  sorry
  --euclid_assert L1.intersectsLine L2

theorem chord_bisector_line : ∀ (O A B: Point) (C: Circle) (AB L: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ perpLine AB L
  → O.onLine L →  perpBisector A B L := by
  euclid_intros
  euclid_apply intersection_lines AB L as F
  have h1 : |(A─F)| = |(F─B)| := by
    by_cases triangle A B O
    . euclid_assert foot O F AB
      euclid_apply isoTriangle_threeLine_concidence_foot O A B F AB
      euclid_finish
    · euclid_assert between A O B
      euclid_assert O = F
      euclid_finish
  euclid_apply (perpBisector_equiv A B L).mpr
  euclid_finish

theorem chord_foot_midpoint : ∀ (O A B D: Point) (C: Circle) (AB: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ ¬ (O.onLine AB) ∧ foot O D AB → |(A─D)| = |(D─B)|:= by
  euclid_intros
  euclid_apply isoTriangle_threeLine_concidence_foot O A B D AB
  euclid_finish

theorem chord_midpoint_foot : ∀ (O A B D: Point) (C: Circle) (AB: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ midpoint A D B ∧ (¬O.onLine AB) → foot O D AB:= by
  euclid_intros
  euclid_apply isoTriangle_threeLine_concidence_midpoint O A B D
  euclid_finish


theorem diameter_rightAngle : ∀ (a b c o : Point) (C: Circle), o.isCentre C ∧  (diameter a b o C) ∧ (c.onCircle C) ∧ (c ≠ a) ∧ (c ≠ b) → ∠ a:c:b = ∟ := by
  euclid_intros
  euclid_apply line_from_points a b as AB
  euclid_apply line_from_points b c as BC
  euclid_apply line_from_points c a as CA
  euclid_assert between a o b
  euclid_apply line_from_points a b as ab
  euclid_assert isoTriangle o a c
  euclid_assert isoTriangle o b c
  euclid_apply isoTriangle_eqAngle o a c
  euclid_apply isoTriangle_eqAngle o b c
  euclid_assert triangle a b c
  euclid_apply triangle_angleSum a b c
  euclid_assert ∠o:a:c = ∠b:a:c
  euclid_assert ∠o:b:c = ∠a:b:c
  euclid_assert ∠a:c:b = ∠ a:c:o + ∠o:c:b
  euclid_finish

theorem rightAngle_diameter : ∀(A B C O:Point) (Ω : Circle), O.isCentre Ω ∧ circumCircle Ω A B C ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ ∠B:A:C = ∟ → diameter B C O Ω := by
  euclid_intros
  euclid_apply line_from_points B O as BO
  euclid_apply intersection_circle_line_extending_points Ω BO O B as X
  have h0: X ≠ A := by
    by_contra
    euclid_apply diameter_rightAngle B X C O Ω
    euclid_apply triangle_angleSum A B C
    euclid_apply triangle_anglePositive A B C
    euclid_finish
  have h1:C = X := by
    have h2: ∠ B:A:X = ∟ := by
      euclid_apply diameter_rightAngle B X A O Ω
      euclid_finish
    have h3: coll A X C := by
      euclid_apply eqAngle_perp_coll B A X C
      euclid_finish
    euclid_finish
  euclid_finish

theorem rightAngle_diameter_onCircle : ∀ (A B C O: Point) (Ω: Circle), diameter A B O Ω ∧ ∠A:C:B = ∟ → C.onCircle Ω := by
  euclid_intros
  by_cases C = A ∨ C = B ∨ A = B
  · euclid_finish
  · have h1: ¬ coll A B C := by
      euclid_apply line_from_points
      euclid_finish
    euclid_apply rightTriangle_midLine_half C A B O
    euclid_finish

theorem diameter_longest : ∀(a b c d o: Point) (C: Circle), (diameter a b o C) ∧ (c.onCircle C) ∧ (d.onCircle C) → |(a─b)| ≥ |(c─d)| := by
  euclid_intros
  by_cases triangle o c d
  · euclid_apply triangle_inequality c d o
    euclid_finish
  · euclid_finish

--See proof in Exervise/1-6

theorem inscribed_angle_theorem_inside :
  ∀ (A B C O : Point) (AB BC CA: Line) (Ω : Circle), (formTriangle A B C AB BC CA) ∧ (insideTriangle O A B C AB BC CA) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_apply self_fullAngle A B C O AB BC CA
  euclid_apply line_from_points O C as OC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O A as OA
  euclid_apply isoTriangle_eqAngle O A C
  euclid_apply isoTriangle_eqAngle O C B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum C O B
  euclid_finish

theorem inscribed_angle_theorem_outside :
  ∀ (A B C O : Point) (OA OC: Line) (Ω : Circle), triangle A B C ∧ (B.sameSide A OC ∧ B.sameSide C OA) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω) ∧ distinctPointsOnLine O A OA ∧ distinctPointsOnLine O C OC
    → ∠ A:O:B = ∠ A:C:B + ∠ A:C:B := by
  euclid_intros
  euclid_assert ∠A:O:B + ∠B:O:C = ∠ A:O:C
  euclid_apply isoTriangle_eqAngle O A C
  euclid_apply isoTriangle_eqAngle O C B
  euclid_apply triangle_angleSum A O C
  euclid_apply triangle_angleSum C O B
  euclid_apply triangle_angleSum B O A
  euclid_apply line_from_points
  euclid_finish


theorem inscribed_angle_theorem_sameSide :
  ∀ (A B C O : Point) (AB: Line) (Ω : Circle), triangle A B C ∧  distinctPointsOnLine A B AB ∧ (O.sameSide C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
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
    euclid_apply inscribed_angle_theorem_outside A B C O OA OC Ω
    euclid_finish
  · by_cases A.sameSide C OB
    · have h3:A.sameSide B OC := by
        by_contra
        euclid_apply intersection_lines AB OC as D
        euclid_finish
      euclid_apply inscribed_angle_theorem_outside B A C O OB OC Ω
      euclid_finish
    · by_cases C.onLine OB
      · euclid_apply isoTriangle_eqAngle O A C
        euclid_apply triangle_exteriorAngle C O A B
        euclid_finish
      · by_cases C.onLine OA
        · euclid_apply isoTriangle_eqAngle O B C
          euclid_apply triangle_exteriorAngle C O B A
          euclid_finish
        · euclid_assert insideTriangle O A B C AB BC AC
          euclid_apply inscribed_angle_theorem_inside A B C O AB BC AC Ω
          euclid_finish

theorem inscribed_angle_theorem_opposingSide:
∀ (A B C O : Point) (AB: Line) (Ω : Circle), triangle A B C ∧  distinctPointsOnLine A B AB ∧ (O.opposingSides C AB) ∧ (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (O.isCentre Ω)
    → ∠ A:O:B + ∠ A:C:B + ∠ A:C:B = ∟ + ∟ + ∟ + ∟:= by
  euclid_intros
  euclid_apply line_from_points O A as OA
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B C as BC
  euclid_apply line_from_points O B as OB
  euclid_apply line_from_points O C as OC
  euclid_apply intersection_lines OC AB as D
  euclid_apply triangle_AngleSum
  euclid_apply isoTriangle_eqAngle
  euclid_finish

theorem cyclic_eqAngle: ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ C≠ A ∧ D ≠ A ∧ C ≠ B ∧ D ≠ B ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ D.onCircle Ω ∧ C.sameSide D AB → ∠B:C:A = ∠B:D:A := by
  euclid_intros
  euclid_apply exists_centre Ω as O
  by_cases O.sameSide C AB
  · euclid_assert O.sameSide D AB
    euclid_apply inscribed_angle_theorem_sameSide A B C O AB Ω
    euclid_apply inscribed_angle_theorem_sameSide A B D O AB Ω
    euclid_finish
  · by_cases O.onLine AB
    · euclid_apply diameter_rightAngle A B C O Ω
      euclid_apply diameter_rightAngle A B D O Ω
      euclid_finish
    · euclid_apply inscribed_angle_theorem_opposingSide A B C O AB Ω
      euclid_apply inscribed_angle_theorem_opposingSide A B D O AB Ω
      euclid_finish

theorem cyclic_complementary : ∀ (A B C D: Point) (AB:Line) (Ω : Circle), distinctPointsOnLine A B AB ∧ distinctFourPoints A B C D ∧ A.onCircle Ω ∧ B.onCircle Ω ∧  C.onCircle Ω ∧ D.onCircle Ω ∧ C.opposingSides D AB → ∠B:C:A + ∠B:D:A = ∟ + ∟ := by
  euclid_intros
  euclid_apply exists_centre Ω as O
  by_cases O.sameSide C AB
  · euclid_assert O.opposingSides D AB
    euclid_apply inscribed_angle_theorem_sameSide A B C O AB Ω
    euclid_apply inscribed_angle_theorem_opposingSide A B D O AB Ω
    euclid_finish
  · by_cases O.onLine AB
    · euclid_apply diameter_rightAngle A B C O Ω
      euclid_apply diameter_rightAngle A B D O Ω
      euclid_finish
    · euclid_apply inscribed_angle_theorem_sameSide A B D O AB Ω
      euclid_apply inscribed_angle_theorem_opposingSide A B C O AB Ω
      euclid_finish

theorem intersecting_chord : ∀ (A B C D E : Point) (Ω: Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
  distinctFourPoints A B C D ∧
  between A E B ∧ between C E D → |(A─E)| * |(E─B)| = |(C─E)| * |(E─D)|:= by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points C D as CD
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points B D as BD
  have h1: ∠C:B:E = ∠A:D:E := by
    euclid_apply cyclic_eqAngle A C B D AC Ω
    euclid_apply angle_between_transfer
    euclid_finish
  have h2: ∠B:C:E = ∠D:A:E := by
    euclid_apply cyclic_eqAngle B D A C BD Ω
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply similar_AA C B E A D E
  euclid_finish

theorem secant_theorem :∀ (A B C D E : Point) (Ω: Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧
  distinctFourPoints A B C D ∧
  between A B E ∧ between D C E → |(A─E)| * |(E─B)| = |(C─E)| * |(E─D)|:= by
  euclid_intros
  euclid_apply line_from_points A C as AC
  have h1: ∠C:B:E = ∠E:D:A := by
    euclid_apply cyclic_complementary A C B D AC Ω
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply line_from_points B D as BD
  have h2: ∠B:C:E = ∠E:A:D := by
    euclid_apply cyclic_complementary B D A C BD Ω
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply similar_AA B C E D A E
  euclid_finish


--tangent
theorem tangentLine_outsideCircle: ∀ (A B O : Point) (Ω: Circle) (L: Line), tangentAtPoint A O L Ω ∧ distinctPointsOnLine A B L → B.outsideCircle Ω := by
  euclid_intros
  euclid_apply foot_shortest
  euclid_finish

theorem tangentLine_sameSide_onCircle: ∀ (A B C O : Point) (Ω: Circle) (L: Line), tangentAtPoint A O L Ω ∧ distinctThreePoints A B C ∧ A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω → B.sameSide C L := by
  euclid_intros
  by_contra
  euclid_apply line_from_points B C as BC
  euclid_apply intersection_lines BC L as D
  have h: D.outsideCircle Ω := by
    euclid_apply tangentLine_outsideCircle A D O Ω L
    euclid_finish
  euclid_finish

theorem inscribedAngle_eq_tangentAngle_diameter : ∀ (A B D X O: Point) (C: Circle) (L AX: Line), diameter A X O C ∧ B.onCircle C ∧ B ≠ X ∧ distinctPointsOnLine A D L ∧ tangentAtPoint A O L C ∧ distinctPointsOnLine A X AX ∧ B.sameSide D AX → ∠D:A:B = ∠A:X:B := by
  euclid_intros
  euclid_apply tangentLine_sameSide_onCircle A B X O C L
  have h1: ∠X:A:B + ∠D:A:B = ∟ := by
    euclid_finish
  have h2: ∠X:A:B + ∠A:X:B = ∟ := by
    euclid_apply diameter_rightAngle A X B O
    euclid_apply triangle_angleSum A X B
    euclid_finish
  euclid_finish


theorem inscribedAngle_eq_tangentAngle : ∀ (A B C D O: Point) (Ω : Circle) (AB BC CA L : Line),
  (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ formTriangle A B C AB BC CA ∧ O.isCentre Ω ∧
  distinctPointsOnLine A D L ∧ tangentAtPoint A O L Ω ∧ B.sameSide D CA
  → ∠ B:A:D = ∠ B:C:A := by
  euclid_intros
  euclid_apply line_from_points O A as OA
  euclid_apply intersection_circle_line_extending_points Ω OA O A as X
  by_cases C = X
  · euclid_apply inscribedAngle_eq_tangentAngle_diameter A B D X O Ω L OA
    euclid_finish
  · by_cases B.sameSide D OA
    · euclid_apply inscribedAngle_eq_tangentAngle_diameter A B D X O Ω L OA
      euclid_apply tangentLine_sameSide_onCircle A B X O Ω L
      euclid_apply tangentLine_sameSide_onCircle A C X O Ω L
      euclid_assert C.sameSide X AB
      euclid_apply cyclic_eqAngle A B C X AB Ω
      euclid_finish
    · euclid_apply extend_point L D A as E
      by_cases B ≠ X
      · euclid_assert E.sameSide B OA
        euclid_apply tangentLine_sameSide_onCircle A B X O Ω L
        euclid_apply tangentLine_sameSide_onCircle A C X O Ω L
        euclid_apply inscribedAngle_eq_tangentAngle_diameter A B E X O Ω L OA
        euclid_apply line_from_points A B as AB
        euclid_assert X.opposingSides C AB
        euclid_apply cyclic_complementary A B C X AB Ω
        euclid_finish
      · euclid_apply diameter_rightAngle A B C O
        euclid_finish

theorem secant_tangent_theorem:∀ (P A B C O: Point) (Ω: Circle)(L:Line), A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ between P B C ∧ distinctPointsOnLine P A L ∧ tangentAtPoint A O L Ω → |(P─A)| * |(P─A)| = |(P─B)| * |(P─C)| := by
  euclid_intros
  have h1: A ≠ B := by
    by_contra
    euclid_apply tangentLine_outsideCircle B C O Ω L
    euclid_finish
  have h2: A ≠ C := by
    by_contra
    euclid_apply tangentLine_outsideCircle C B O Ω L
    euclid_finish
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points B C as BC
  have h1: ∠B:A:P = ∠A:C:P := by
    euclid_apply inscribedAngle_eq_tangentAngle A B C P O Ω AB BC AC L
    euclid_apply angle_between_transfer
    euclid_finish
  have h2: ∠A:P:B = ∠C:P:A := by
    euclid_apply angle_between_transfer
    euclid_finish
  euclid_apply similar_AA A P B C P A
  euclid_finish

theorem length_of_tangent : ∀ (P A B O: Point) (Ω: Circle) (L1 L2: Line), A.onCircle Ω ∧ B.onCircle Ω ∧ distinctPointsOnLine P A L1 ∧ distinctPointsOnLine P B L2 ∧ tangentAtPoint A O L1 Ω ∧ tangentAtPoint B O L2 Ω → |(P─A)| = |(P─B)| := by
  euclid_intros
  have h1: |(P─A)| * |(P─A)| = |(P─B)| * |(P─B)| := by
    euclid_apply exists_point_inside_circle Ω as Q
    have h2: P.outsideCircle Ω := by
      euclid_apply tangentLine_outsideCircle A P O Ω L1
      euclid_finish
    euclid_apply line_from_points P Q as PQ
    euclid_apply intersection_circle_line_between_points Ω PQ Q P as D
    euclid_apply intersection_circle_line_extending_points Ω PQ Q D as E
    euclid_apply secant_tangent_theorem P A D E O Ω L1
    euclid_apply secant_tangent_theorem P B D E O Ω L2
    euclid_finish
  have h3: |(P─A)| > 0 := by
    euclid_finish
  have h4: |(P─B)| > 0 := by
    euclid_finish
  nlinarith

theorem inscribed_formtriangle : ∀ (A B C O : Point) (Γ : Circle),
  A.onCircle Γ ∧ B.onCircle Γ ∧ C.onCircle Γ ∧ O.isCentre Γ ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A
  → triangle A B C := by
  euclid_intros
  euclid_finish


theorem tangent_circles_line_of_centers
  : ∀ (C1 C2 : Circle) (O1 O2 T : Point),
    O1.isCentre C1 ∧
    O2.isCentre C2 ∧
    T.onCircle C1 ∧
    T.onCircle C2 ∧
    (∀ X : Point, X.onCircle C1 ∧ X.onCircle C2 → X = T)
    → coll O1 O2 T
  := by
sorry

theorem power_cyclic_out: ∀ (a b c d e: Point),distinctFourPoints a b c d ∧ (between a b e) ∧ (between c d e) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → cyclic a b c d := by
  sorry

theorem power_cyclic_in: ∀ (a b c d e: Point),distinctFourPoints a b c d ∧ (between a e b) ∧ (between c e d) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → cyclic a b c d := by
  sorry

theorem cyclic_exists_circle : ∀ (A B C D : Point), cyclic A B C D → ∃ (O: Circle), A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O:= by
  euclid_intros
  euclid_finish

theorem cyclic_power: ∀ (a b c d e: Point),distinctFourPoints a b c d ∧ cyclic a b c d ∧ (coll a b e) ∧ (coll c d e) → |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| := by
  euclid_intros
  euclid_apply cyclic_exists_circle a b c d as C
  by_cases between a e b
  · euclid_assert between c e d
    euclid_apply intersecting_chord a b c d e C
    euclid_finish
  · euclid_apply secant_theorem
    euclid_finish


theorem inside_power_sameline: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ between A P B ∧ coll A O B→ |(P─A)| * |(P─B)| + |(P─O)| * |(P─O)| = |(O─A)| * |(O─A)| := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem outside_power_sameline: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧  between P A B ∧ coll A O B→ |(P─A)| * |(P─B)| + |(O─A)| * |(O─A)|= |(P─O)| * |(P─O)|  := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem inside_power: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ between A P B → |(P─A)| * |(P─B)| + |(P─O)| * |(P─O)|= |(O─A)| * |(O─A)|  := by
  euclid_intros
  by_cases h: coll A O B
  · euclid_apply inside_power_sameline P O A B C
    euclid_finish
  · euclid_apply line_from_points O P as l
    euclid_apply intersections_circle_line C l as (S,T)
    have h1 : |(P─A)| * |(P─B)| = |(P─S)| * |(P─T)| := by
      euclid_apply cyclic_power S T A B P
      euclid_finish
    rw[h1]
    euclid_finish

theorem outside_power: ∀ (P O A B: Point) (C: Circle),O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧  between P A B ∧ coll A O B→ |(P─A)| * |(P─B)| + |(O─A)| * |(O─A)|= |(P─O)| * |(P─O)|  := by
  euclid_intros
  by_cases h: coll A O B
  · euclid_apply outside_power_sameline P O A B C
    euclid_finish
  · euclid_apply line_from_points O P as l
    euclid_apply intersections_circle_line C l as (S,T)
    have h1 : |(P─A)| * |(P─B)| = |(P─S)| * |(P─T)| := by
      euclid_apply cyclic_power S T A B P
      euclid_finish
    rw[h1]
    euclid_finish


theorem eqChord_eqInsctribedAngle: ∀
(A B C A' B' C' : Point) (Ω : Circle), distinctThreePoints A B C ∧ distinctThreePoints A' B' C' ∧
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω
  ∧ A'.onCircle Ω ∧ B'.onCircle Ω ∧ C'.onCircle Ω
  ∧ (|(A─C)| = |(A'─C')|)
  → ∠ A:B:C = ∠ A':B':C' ∨ ∠ A:B:C + ∠ A':B':C' = ∟ + ∟
:= by
  euclid_intros
  euclid_apply exists_centre Ω as O
  have h_central_angles_eq : ∠ A:O:C = ∠ A':O:C' := by
    euclid_apply eqChord_eqCentralAngle A C A' C' O Ω
    euclid_finish
  euclid_apply line_from_points A C as AC
  euclid_apply line_from_points A' C' as A'C'
  by_cases hO_on_AC : O.onLine AC
  · have h_diam_AC : diameter A C O Ω := by
      euclid_finish
    have h_angle_ABC : ∠ A:B:C = ∟ := by
      euclid_apply diameter_rightAngle A C B O Ω
      euclid_finish
    have h_diam_A'C' : diameter A' C' O Ω := by
      euclid_finish
    have h_angle_A'B'C' : ∠ A':B':C' = ∟ := by
      euclid_apply diameter_rightAngle A' C' B' O Ω
      euclid_finish
    right
    euclid_finish
  · have hO_not_on_A'C' : ¬(O.onLine A'C') := by
      by_contra h_contra
      have h_O_on_AC_implied : O.onLine AC := by
        euclid_finish
      exact hO_on_AC h_O_on_AC_implied
    have h_tri_ACB : triangle A C B := by
      euclid_finish
    have h_tri_A'C'B' : triangle A' C' B' := by
      euclid_finish
    by_cases hB_side : B.sameSide O AC
    · have h_angle_ABC : ∠ A:O:C = ∠ A:B:C + ∠ A:B:C := by
        euclid_apply inscribed_angle_theorem_sameSide A C B O AC Ω
        euclid_finish
      by_cases hB'_side : B'.sameSide O A'C'
      · have h_angle_A'B'C' : ∠ A':O:C' = ∠ A':B':C' + ∠ A':B':C' := by
          euclid_apply inscribed_angle_theorem_sameSide A' C' B' O A'C' Ω
          euclid_finish
        left
        euclid_finish
      · have hB'_opp : B'.opposingSides O A'C' := by
          euclid_finish
        have h_angle_A'B'C' : ∠ A':O:C' + (∠ A':B':C' + ∠ A':B':C') = ∟ + ∟ + ∟ + ∟ := by
          euclid_apply inscribed_angle_theorem_opposingSide A' C' B' O A'C' Ω
          euclid_finish
        right
        euclid_finish
    · have hB_opp : B.opposingSides O AC := by
        euclid_finish
      have h_angle_ABC : ∠ A:O:C + (∠ A:B:C + ∠ A:B:C) = ∟ + ∟ + ∟ + ∟ := by
        euclid_apply inscribed_angle_theorem_opposingSide A C B O AC Ω
        euclid_finish
      by_cases hB'_side : B'.sameSide O A'C'
      · have h_angle_A'B'C' : ∠ A':O:C' = ∠ A':B':C' + ∠ A':B':C' := by
          euclid_apply inscribed_angle_theorem_sameSide A' C' B' O A'C' Ω
          euclid_finish
        right
        euclid_finish
      · have hB'_opp : B'.opposingSides O A'C' := by
          euclid_finish
        have h_angle_A'B'C' : ∠ A':O:C' + (∠ A':B':C' + ∠ A':B':C') = ∟ + ∟ + ∟ + ∟ := by
          euclid_apply inscribed_angle_theorem_opposingSide A' C' B' O A'C' Ω
          euclid_finish
        left
        euclid_finish



end LeanGeo
