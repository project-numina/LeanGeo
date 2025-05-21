import SystemE
import LeanGeo.Abbre
namespace LeanGeo
theorem construct_perpBisector (a b : Point) : ¬ (a ≠ b) →  ∃ L, perpBisector a b L := by
  sorry

theorem exists_centre : ∀ (O: Circle), ∃ (C : Point), C.isCentre O := by
  sorry

theorem exists_midpoint : ∀ (A B : Point), ∃(P : Point), midpoint A P B := by
  sorry

--theorem exists_foot : ∀ (A : Point) (l : Line), ∃(P : Point), P.onLine l ∧
--(∀ Q:Point, Q.onLine l → ∠A:P:Q = ∟) := by
--  sorry
theorem midpoint_twice: ∀ (A B P : Point), midpoint A P B → |(A─B)| * 1/2 = |(P─B)|  := by
  euclid_intros
  euclid_finish

theorem exists_foot : ∀ (c a b : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) :=
by
  sorry

theorem exists_angleBisection : ∀ (A B C : Point),
(A ≠ B) ∧ (A ≠ C) ∧ ¬(coll A B C)
→ ∃ (L : Line), ∀ (P: Point), P.onLine L ↔ ∠ A:B:P = ∠ P:B:C
:= by
sorry

theorem supplementaryAngle_line : ∀ (d a b c: Point), (between a b c) ∧ (¬ coll a b d) → ∠d:b:a + ∠d:b:c = ∟ + ∟ := by
  sorry



theorem coll_exist_line : ∀ (A B C : Point), coll A B C ↔ ∃(l:Line),
A.onLine l ∧ B.onLine l ∧ C.onLine l := by
  sorry


theorem point_not_onLine : ∀(A B C : Point) (l :Line), ¬ coll A B C ∧ distinctPointsOnLine B C l → ¬ A.onLine l := by
  rintro A B C l ⟨h1,h2⟩ h3
  have h: coll A B C := by
    rw [coll_exist_line]
    use l
    euclid_finish
  exact h1 h

theorem unique_perpLine : ∀ (A : Point) (L : Line),
  ¬(A.onLine L)
  → ∃! (M : Line),
    A.onLine M
    ∧ perpLine L M
    :=
by
  sorry

--Angle
theorem angle_coincide_zero : ∀ (a o : Point), (a ≠ o) → ∠a:o:a = 0:= by
  sorry
theorem angle_positive_neq : ∀ (a o b : Point), (∠a:o:b>0) → (a ≠ b) ∧ (a ≠ o) ∧ (b ≠ o) := by
  sorry
theorem angle_between_transfer : ∀ (a b c d : Point),between a b c ∧ ¬ coll a b d → ∠d:c:b = ∠d:c:a ∧ ∠d:b:c + ∠d:b:a = ∟ + ∟ := by
  sorry

theorem rightAngle_eq_pi_div_two : ∟ = Real.pi / 2 := by
  sorry

theorem sin_rightAngle : Real.sin ∟ = 1 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.sin_pi_div_two]

theorem cos_rightAngle : Real.cos ∟ = 0 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.cos_pi_div_two]


--perpBisector
theorem perpBisector_property : ∀ (A B : Point) (L : Line),
  perpBisector A B L →
  (∀ (X : Point), X.onLine L → |(X─A)| = |(X─B)|) ∧
  (∀ (X : Point), |(X─A)| = |(X─B)| → X.onLine L)
:= by
sorry

theorem perpBisector_construction :
∀ (a b p q : Point) (L : Line),
(|(a─p)| = |(b─p)|) ∧ (|(a─q)| = |(b─q)|) ∧ distinctPointsOnLine p q L
→ perpBisector a b L := by
sorry

theorem perpBisector_equiv : ∀ (A B : Point) (L: Line),
perpBisector A B L ↔ ∃ (P :Point) (AB : Line), P.onLine L ∧ midpoint A P B ∧ perpLine AB L ∧ distinctPointsOnLine A B AB := by
  sorry
theorem between_fourpoint: ∀(A B C D: Point), between A B C ∧ between B C D ∧ between C D E → between A C E := by
  euclid_intros
  euclid_finish

theorem between_zeroAngle : ∀ (A B C : Point), between A B C → ∠B:A:C = 0 := by
  sorry

theorem between_straightAngle : ∀ (A B C : Point), between A B C → ∠A:B:C = ∟  + ∟ := by
  sorry

--Triangle
theorem triangle_anglePositive : ∀(A B C : Point) , triangle A B C → ∠A:B:C > 0 ∧ ∠A:C:B >0 ∧ ∠C:A:B >0 := by
  sorry

theorem triangle_angleSum : ∀(A B C : Point) , triangle A B C → ∠A:B:C +∠B:C:A + ∠C:A:B = ∟ + ∟ := by
  euclid_intros
  euclid_assert ¬ (between A B C)
  euclid_assert A ≠ B
  euclid_apply line_from_points A B as AB
  sorry

theorem triangle_exteriorAngle : ∀ (a b c d: Point), (triangle a b c) ∧ (between a b d) → ∠d:b:c = ∠b:c:a + ∠c:a:b := by
  euclid_intros
  euclid_apply triangle_angleSum a b c
  --euclid_assert ∠c:b:d +∠c:b:a = ∟ + ∟
  euclid_apply supplementaryAngle_line c a b d
  euclid_finish

theorem isoTriangle_eqAngle : ∀ (A B C : Point), isoTriangle A B C → ∠ A:B:C = ∠A:C:B := by
  euclid_intros
  euclid_apply exists_midpoint B C as D
  euclid_apply line_from_points B C as BC
  euclid_assert A ≠ D
  euclid_assert triangle D A B
  euclid_assert triangle D A C
  euclid_assert Triangle.congruent_test (△ D:A:B) (△ D:A:C)
  euclid_apply Triangle.congruent_property (△ D:A:B) (△ D:A:C)
  euclid_assert ∠D:B:A = ∠D:C:A
  sorry

theorem eqside_eqAngle :∀ (O A B : Point), |(O─A)|=|(O─B)| ∧ (A ≠ B) → ∠O:A:B = ∠O:B:A := by
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
  (triangle a b c) ∧ (∠ b:a:c = ∠ a:b:c)
  → |(b─c)| = |(a─c)| := by
  euclid_intros
  euclid_apply line_from_points b c as BC
  euclid_apply point_not_onLine a b c BC
  euclid_apply exists_foot a b c BC as d
  euclid_assert a ≠ d
  sorry

theorem isoTriangle_threeLine_concidence : ∀ (a b c d: Point),
  isoTriangle a b c ∧ coll c b d →
  (midpoint b d c ∨ ∠a:d:b = ∟ ∨ ∠a:d:c = ∟ ∨ ∠d:a:b = ∠ d:a:c) →
  (midpoint b d c ∧  ∠a:d:b = ∟ ∧  ∠a:d:c = ∟ ∧  ∠d:a:b = ∠ d:a:c)
:= by
  sorry

theorem pythagorean : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| :=
by
  sorry

theorem pythagorean_point : ∀ (a b c: Point), (triangle a b c) ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  sorry

theorem triangle_side_angle_inequality : ∀ (a b c: Point),
  (triangle a b c) ∧ (|(b─c)| > |(a─c)|)
  → ∠ b:a:c > ∠ a:b:c := by
sorry


axiom triangle_inequality : ∀ (a b c : Point), triangle a b c →
|(a─b)| < |(b─c)| + |(c─a)|

axiom triangle_inequality_le : ∀ (a b c : Point),
|(a─b)| ≤  |(b─c)| + |(c─a)|

theorem triangle_ineqaulity_eql : ∀ (a b c : Point), distinctThreePoints a b c ∧ |(a─b)| = |(b─c)| + |(c─a)| → between b c a  := by
  sorry


--Parallel
theorem parallel_eqAlternateAngles :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧ A ≠ C ∧ D ≠ B ∧
  C.opposingSides D T
  → ∠ C:A:B = ∠ A:B:D
:= by
sorry

theorem parallel_SupplementConsecutiveAngles :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T
  → ∠ C:A:B + ∠ A:B:D = ∟ + ∟
:= by
sorry
theorem perpLine_perpLine_parallel : ∀ (L1 L2 M : Line),
  (perpLine L1 M) ∧ (perpLine L2 M) ∧ L1 ≠ L2 →
  ¬(L1.intersectsLine L2) :=
by sorry

theorem perpLine_parallel_perpLine:
  ∀ (M N L : Line),
    (perpLine M N ∧ ¬L.intersectsLine M) →
    perpLine L N :=
by
  sorry



--Circle
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


theorem inscribedAngle_eq_tangentAngle : ∀ (A B C D : Point) (Ω : Circle) (AB BC CAL : Line),
  (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ formTriangle A B C AB BC CA ∧
  distinctPointsOnLine A D L ∧ tangentAtPoint L Ω A ∧ B.sameSide D AC
  → ∠ B:A:D = ∠ B:C:A :=
by sorry

theorem intersecting_circles_perpendicular_bisector :
  ∀ (C1 C2 : Circle) (O1 O2 A B : Point) (L : Line),
  (circlesIntersectsAtTwoPoints C1 C2 O1 O2)
  ∧ (O1.onLine L)
  ∧ (O2.onLine L)
  → perpBisector A B L :=
by sorry


theorem diameter_longest : ∀(a b c d: Point) (C: Circle), (diameter a b C) ∧ (c.onCircle C) ∧ (d.onCircle C) → |(a─b)| ≥ |(c─d)| := by
  euclid_intros
  sorry

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


--Quadrilateral
theorem parallelogram_tests : ∀
  (A B C D : Point)
  (AB BC CD DA AC BD : Line),
  (formQuadrilateral A B C D AB BC CD DA) ∧
  (
    (|(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)|)
    ∨
    (|(A─B)| = |(C─D)| ∧ ¬ AB.intersectsLine CD)
    ∨
    (∃ O : Point, twoLinesIntersectAtPoint AC BD O ∧ midpoint A O C ∧ midpoint B O D)
  )
  →
  (parallelogram A B C D AB BC CD DA)
:= by
sorry

theorem parallelogram_eqside : ∀ (A B C D : Point) (AB BC CD DA : Line),
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
sorry

theorem rhombus_angleBisects_perpendicular :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  rhombus A B C D AB BC CD DA ∧ distinctPointsOnLine A C AC ∧ distinctPointsOnLine B D BD →
    perpLine AC BD := by
sorry

theorem circumscribed_quadrilateral_eqsumside :
  ∀ (A B C D : Point) (AB BC CD DA : Line) (Ω : Circle),
    (formQuadrilateral A B C D AB BC CD DA)
    ∧ (tangentLine AB Ω)
    ∧ (tangentLine BC Ω)
    ∧ (tangentLine CD Ω)
    ∧ (tangentLine DA Ω)
    → (|(A─B)| + |(C─D)| = |(B─C)| + |(D─A)|) :=
by
  sorry

theorem cyclic_test (A B C D: Point) (AB BC CD DA :Line) : (formQuadrilateral A B C D AB BC CD DA) ∧ (
  (∠ A:B:D = ∠ A:C:D) ∨
  (∠ D:A:C = ∠ D:B:C) ∨
  (∠ A:D:B = ∠ A:C:B) ∨
  (∠ B:D:C = ∠ B:A:C) ∨
  (∠ A:D:C + ∠A:B:C = ∟ + ∟) ∨
  (∠ D:A:B + ∠D:C:B = ∟ + ∟)) → ∃ (O: Circle), cyclicQuadrilateral A B C D AB BC CD DA O := by
  sorry

theorem cyclic_property (A B C D: Point) (AB BC CD DA :Line) (O: Circle): cyclicQuadrilateral A B C D AB BC CD DA O →
  (∠ A:B:D = ∠ A:C:D) ∧
  (∠ D:A:C = ∠ D:B:C) ∧
  (∠ A:D:B = ∠ A:C:B) ∧
  (∠ B:D:C = ∠ B:A:C) ∧
  (∠ A:D:C + ∠A:B:C = ∟ + ∟) ∧
  (∠ D:A:B + ∠D:A:C = ∟ + ∟)
  :=by
  sorry

theorem isoTrapezoid_eqAngle:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  trapezoid A B C D AB BC CD DA ∧
  (|(B─C)| = |(D─A)|)
  → (∠A:B:C = ∠D:C:B) ∧ (∠B:A:D = ∠C:D:A) := by
sorry

--Algebra
theorem ratio_transfer : ∀ (a b c d : ℝ), a / b = c / d  → a / c = b / d := by
  sorry
