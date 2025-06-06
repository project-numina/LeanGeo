import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Basic
import LeanGeo.Theorem.Triangle
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
    · euclid_assert (△ a:o:b).congruent_test (△ c:o:d)
      euclid_apply Triangle.congruent_property (△ a:o:b) (△ c:o:d)
      euclid_finish

theorem threePoints_existCircle : ∀ (A B C : Point),
  triangle A B C →
  ∃ (Ω : Circle),
    (A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω) :=
by sorry

theorem eqChord_eqInsctribedAngle : ∀
(A B C A' B' C' : Point) (Ω : Circle), distinctThreePoints A B C ∧ distinctThreePoints A' B' C' ∧
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω
  ∧ A'.onCircle Ω ∧ B'.onCircle Ω ∧ C'.onCircle Ω
  ∧ (|(A─C)| = |(A'─C')|)
  → ∠ A:B:C = ∠ A':B':C' ∨ ∠ A:B:C + ∠ A':B':C' = ∟ + ∟
:= by
sorry

theorem eqInscribedAngle_eqChord : ∀
(A B C A' B' C' : Point) (Ω : Circle), distinctThreePoints A B C ∧ distinctThreePoints A' B' C' ∧
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω
  ∧ A'.onCircle Ω ∧ B'.onCircle Ω ∧ C'.onCircle Ω
  ∧ ∠A:B:C = ∠ A':B':C' ∨ ∠ A:B:C + ∠ A':B':C' = ∟ + ∟
  → |(A─C)| = |(A'─C')|
:= by
sorry

theorem intersecting_chord : ∀ (A B C D E : Point) (O: Circle),
  A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O ∧
  distinctFourPoints A B C D ∧
  between A E B ∧ between C E D → |(A─E)| * |(E─B)| = |(C─E)| * |(E─D)|:= by
  sorry

--Proved in Everyday/0415.lean
theorem chord_bisector_line : ∀ (O A B: Point) (C: Circle) (AB L: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ perpLine AB L
  → O.onLine L →  perpBisector A B L := by
  sorry

theorem chord_foot_midpoint : ∀ (O A B D: Point) (C: Circle) (AB: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ foot O D AB → |(A─D)| = |(D─B)|:= by
  sorry

theorem foot_chord_midpoint : ∀ (O A B D: Point) (C: Circle) (AB: Line), O.isCentre C ∧ A.onCircle C ∧ B.onCircle C ∧ distinctPointsOnLine A B AB ∧ midpoint A D B ∧ (¬O.onLine AB) → foot O D AB:= by
  sorry

theorem inscribedAngle_eq_tangentAngle : ∀ (A B C D : Point) (Ω : Circle) (AB BC CA L : Line),
  (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D L ∧ tangentAtPoint L Ω A ∧ B.sameSide D AC
  → ∠ B:A:D = ∠ B:C:A :=
by sorry

theorem intersecting_circles_perpendicular_bisector :
  ∀ (C1 C2 : Circle) (O1 O2 A B : Point) (L : Line),
  (circlesIntersectsAtTwoPoints C1 C2 A B) ∧ O1.isCentre C1 ∧ O2.isCentre C2
  ∧ (O1.onLine L)
  ∧ (O2.onLine L)
  → perpBisector A B L :=
by sorry

theorem rightAngle_diameter : ∀(A B C O:Point) (Ω : Circle), O.isCentre Ω ∧ circumCircle Ω A B C ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ ∠B:A:C = ∟ → diameter B C O Ω := by
  sorry
theorem rightAngle_diameter_onCircle : ∀ (A B C O: Point) (Ω: Circle), diameter A B O Ω ∧ ∠A:C:B = ∟ → C.onCircle Ω := by
  sorry
theorem diameter_longest : ∀(a b c d o: Point) (C: Circle), (diameter a b o C) ∧ (c.onCircle C) ∧ (d.onCircle C) → |(a─b)| ≥ |(c─d)| := by
  euclid_intros
  sorry

--See proof in Exervise/1-6
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

theorem perpendicular_radius_tangent : ∀
  (a b : Point) (AB L : Line) (C : Circle),
  distinctPointsOnLine a b AB ∧
  b.isCentre C ∧
  a.onCircle C ∧
  twoLinesIntersectAtPoint AB L a ∧
  perpLine AB L
  → tangentLine L C := by
sorry

theorem inscribed_formtriangle : ∀ (A B C O : Point) (Γ : Circle),
  A.onCircle Γ ∧ B.onCircle Γ ∧ C.onCircle Γ ∧ O.isCentre Γ ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A
  → triangle A B C := by
sorry


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

theorem power_cyclic: ∀ (a b c d e: Point),distinctFourPoints a b c d ∧ (coll a b e) ∧ (coll c d e) ∧ |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| → cyclic a b c d := by
  sorry

theorem cyclic_power: ∀ (a b c d e: Point),distinctFourPoints a b c d ∧ cyclic a b c d ∧ (coll a b e) ∧ (coll c d e) → |(e─a)| * |(e─b)| = |(e─c)| * |(e─d)| := by
  sorry

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
end LeanGeo
