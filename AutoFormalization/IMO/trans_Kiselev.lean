import SystemE
import UniGeo.Relations
import UniGeo.Abbre
import UniGeo.Theorem
theorem triangle_inequality_theorem : ∀ (A B C : Point),
  (triangle A B C)
  → (|(A─B)| + |(B─C)| > |(A─C)|)
    ∧ (|(B─C)| + |(A─C)| > |(A─B)|)
    ∧ (|(A─B)| + |(A─C)| > |(B─C)|) := by
sorry

theorem isosceles_triangle_base_angles : ∀ (A B C : Point), isoTriangle A B C → ∠ A:B:C = ∠ A:C:B := by
  euclid_intros
  euclid_apply exists_midpoint B C as D
  euclid_apply line_from_points B C as BC
  euclid_assert A ≠ D
  euclid_assert triangle D A B
  euclid_assert triangle D A C
  euclid_assert Triangle.congruent_judge (△ D:A:B) (△ D:A:C)
  euclid_apply Triangle.congruent_property (△ D:A:B) (△ D:A:C)
  euclid_assert ∠D:B:A = ∠D:C:A
  euclid_finish

theorem perpendicular_to_radius_tangent_line :
  ∀ (O A : Point) (C : Circle) (L M : Line),
    O.isCentre C ∧
    A.onCircle C ∧
    distinctPointsOnLine O A M ∧
    A.onLine L ∧
    A.onLine M ∧
    perpLine L M
    → tangentLine L C := by
sorry

theorem triangle_angle_sum_theorem : ∀ (a b c: Point), (triangle a b c) → ∠b:a:c + ∠a:b:c + ∠a:c:b = ∟ + ∟ := by
sorry

theorem triangle_side_inequality : ∀ (A B C : Point),
  (triangle A B C)
  → (|(A─B)| + |(B─C)| > |(A─C)| ∧ |(A─B)| + |(A─C)| > |(B─C)| ∧ |(B─C)| + |(A─C)| > |(A─B)|)
:= by
sorry

theorem triangle_exteriorAngle : ∀ (a b c d: Point), (triangle a b c) ∧ (between a b d) → ∠d:b:c = ∠b:c:a + ∠c:a:b := by
sorry

theorem exterior_angle_triangle : ∀ (a b c d: Point),
  (triangle a b c) ∧ (between a b d)
  → ∠d:b:c = ∠b:c:a + ∠c:a:b
:= by
sorry

theorem isosceles_triangle_base_angles : ∀ (A B C : Point),
  (triangle A B C) ∧ (|(A─B)| = |(A─C)|)
  → ∠ B:A:C = ∠ C:A:B
:= by
sorry

theorem isosceles_triangle_sides : ∀ (a b c : Point),
  (triangle a b c) ∧ (∠ b:a:c = ∠ a:b:c)
  → |(b─c)| = |(a─c)| := by
sorry

theorem isosceles_triangle_base_angle_theorem : ∀ (A B C : Point), (isoTriangle A B C) → ∠ B:A:C = ∠ C:A:B := by
sorry

theorem angle_sum_triangle : ∀ (A B C : Point), (triangle A B C) → ∠B:A:C + ∠A:C:B + ∠C:B:A = ∟ + ∟ := by
sorry

theorem exterior_angle_theorem : ∀ (a b c d: Point),
  (triangle a b c) ∧ (between a b d) →
  ∠ d:b:c = ∠ b:c:a + ∠ c:a:b :=
by
  sorry

theorem triangle_angle_sum : ∀ (a b c: Point), (triangle a b c) → ∠b:a:c + ∠a:b:c + ∠a:c:b = ∟ + ∟ := by
sorry

theorem inscribed_angle_and_semicircle_right_angle : ∀ (a b c: Point) (O: Circle),
  (diameter a b O) ∧ (c.onCircle O) ∧ (c ≠ a) ∧ (c ≠ b) →
  ∠ a:c:b = ∟
:= by
sorry

theorem perpendicular_to_radius_tangent : ∀
  (a b : Point) (AB L : Line) (C : Circle),
  distinctPointsOnLine a b AB ∧
  b.isCentre C ∧
  a.onCircle C ∧
  twoLinesIntersectAtPoint AB L a ∧
  perpLine AB L
  → tangentLine L C := by
sorry

theorem inscribed_angle_and_circumscribed_polygon :
  ∀ (A B C D : Point) (AB BC CD DA : Line) (Ω : Circle),
    (formQuadrilateral A B C D AB BC CD DA)
    ∧ (tangentLine AB Ω)
    ∧ (tangentLine BC Ω)
    ∧ (tangentLine CD Ω)
    ∧ (tangentLine DA Ω)
    → (|(A─B)| + |(C─D)| = |(B─C)| + |(D─A)|) :=
by
  sorry

theorem isosceles_triangle_base_angles : ∀ (A B C : Point), isoTriangle A B C → ∠ A:B:C = ∠ A:C:B := by
sorry

theorem circumscribed_polygon_property :
  ∀ (A B C D : Point) (AB BC CD DA : Line) (O : Circle),
    formQuadrilateral A B C D AB BC CD DA ∧
    tangentLine AB O ∧
    tangentLine BC O ∧
    tangentLine CD O ∧
    tangentLine DA O
    → |(A─B)| + |(C─D)| = |(B─C)| + |(D─A)| := by
sorry

theorem inscribed_angle_and_semicircle : ∀ (A B C : Point) (Ω : Circle),
  (diameter A B Ω) ∧ (C.onCircle Ω) ∧ (C ≠ A) ∧ (C ≠ B) →
  ∠ A:C:B = ∟
:= by
sorry

theorem triangle_inequality : ∀ (a b c : Point),
  (triangle a b c)
  → (|(a─b)| + |(b─c)| > |(a─c)|)
    ∧ (|(b─c)| + |(a─c)| > |(a─b)|)
    ∧ (|(a─c)| + |(a─b)| > |(b─c)|) := by
sorry

theorem perpendiculars_to_parallel_lines : ∀ (L1 L2 M : Line),
  (perpLine L1 M) ∧ (perpLine L2 M) →
  ¬(∃ (X : Point), twoLinesIntersectAtPoint L1 L2 X) :=
by sorry

theorem inscribed_angles_intercepting_same_arc :
  ∀ (A B P Q : Point) (Ω : Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ P.onCircle Ω ∧ Q.onCircle Ω
  ∧ A ≠ B ∧ A ≠ P ∧ B ≠ P ∧ A ≠ Q ∧ B ≠ Q ∧ P ≠ Q →
  ∠A:P:B = ∠A:Q:B
:= by
sorry

theorem perpendiculars_to_same_line_parallel : ∀ (L1 L2 M : Line),
  perpLine L1 M ∧ perpLine L2 M →
  ¬ ∃ (b : Point), twoLinesIntersectAtPoint L1 L2 b
:= by
sorry

theorem angle_congruence_construction_theorem :
  ∀ (A B C : Point),
    (B ≠ A) ∧ (B ≠ C) →
    ∃ (D E F : Point), (D ≠ E) ∧ (E ≠ F) ∧ (∠D:E:F = ∠A:B:C) := by
sorry


theorem intersecting_circles_perpendicular_bisector :
  ∀ (C1 C2 : Circle) (O1 O2 A B : Point) (L : Line),
  (C1.intersectsCircle C2)
  ∧ (O1.isCentre C1)
  ∧ (O2.isCentre C2)
  ∧ (A.onCircle C1)
  ∧ (A.onCircle C2)
  ∧ (B.onCircle C1)
  ∧ (B.onCircle C2)
  ∧ (A ≠ B)
  ∧ (O1.onLine L)
  ∧ (O2.onLine L)
  → perpBisector A B L :=
by sorry

theorem drop_perpendicular : ∀ (A : Point) (L : Line), ¬(A.onLine L) → ∃ (M : Line), A.onLine M ∧ perpLine M L := by
sorry


theorem inscribed_angle_measure : ∀ (A B C O : Point) (Γ : Circle),
  A.onCircle Γ ∧ B.onCircle Γ ∧ C.onCircle Γ ∧ O.isCentre Γ ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A
  → ∠ A:B:C + ∠ A:B:C = ∠ A:O:C := by
sorry

theorem tangent_perpendicular_to_radius :
  ∀ (O P : Point) (L L1 : Line) (Ω : Circle),
  (O.isCentre Ω) ∧ (tangentAtPoint L Ω P) ∧ (distinctPointsOnLine O P L1)
  → perpLine L L1 := by
sorry

theorem parallelogram_opposite_sides : ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA ∧
   ¬(∃ X : Point, twoLinesIntersectAtPoint AB DC X) ∧
   ¬(∃ X : Point, twoLinesIntersectAtPoint BC DA X))
  → (|(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)|) := by
sorry

theorem tangent_line_perpendicular_to_radius : ∀
  (O P : Point) (C : Circle) (L : Line),
  (O.isCentre C) ∧ (tangentAtPoint L C P)
  → ∃ (M : Line), distinctPointsOnLine O P M ∧ perpLine M L
:= by
sorry


theorem inscribed_polygon_angle_sum : ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA) ∧ (cyclic A B C D)
  → (∠D:A:B + ∠B:C:D = ∟ + ∟) ∧ (∠A:B:C + ∠C:D:A = ∟ + ∟) := by
sorry

theorem parallelogram_opposite_angles :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (∀ P : Point, ¬(twoLinesIntersectAtPoint AB CD P))
  ∧ (∀ Q : Point, ¬(twoLinesIntersectAtPoint BC DA Q))
  → ∠D:A:B = ∠B:C:D ∧ ∠A:B:C = ∠C:D:A
:= by
sorry

theorem perpendicular_and_slant : ∀ (A Q X : Point) (L M : Line),
¬(A.onLine L) ∧ A.onLine M ∧ Q.onLine L ∧ Q.onLine M ∧ perpLine L M ∧ X.onLine L ∧ (X ≠ Q)
→ (|(A─Q)| < |(A─X)|) := by
sorry

theorem inscribed_angle_in_semicircle : ∀ (a b c : Point) (C : Circle), (diameter a c C) ∧ (b.onCircle C) ∧ (b ≠ a) ∧ (b ≠ c) → ∠ a:b:c = ∟ := by
sorry



theorem parallel_lines_perpendiculars :
  ∀ (L M N : Line),
    (perpLine L M ∧ ¬(∃ (X : Point), twoLinesIntersectAtPoint M N X)) →
    perpLine L N :=
by
  sorry



theorem parallel_lines_and_transversal_alternate_interior_angles :
∀ (L1 L2 T : Line) (A B X Y : Point),
  (A.onLine L1 ∧ A.onLine T)
  ∧ (B.onLine L2 ∧ B.onLine T)
  ∧ (X.onLine L1 ∧ X ≠ A)
  ∧ (Y.onLine L2 ∧ Y ≠ B)
  ∧ (∠ X:A:B = ∠ A:B:Y)
  → ¬(∃ P : Point, P.onLine L1 ∧ P.onLine L2)
:= by
sorry

theorem parallelogram_diagonals_bisect :
∀ (A B C D E : Point) (AB BC CD DA AC BD : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (¬ (∃ P : Point, twoLinesIntersectAtPoint AB CD P))
  ∧ (¬ (∃ Q : Point, twoLinesIntersectAtPoint BC DA Q))
  ∧ (twoLinesIntersectAtPoint AC BD E)
  → (midpoint A E C ∧ midpoint B E D) := by
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

theorem unique_perpendicular_theorem : ∀ (A : Point) (L : Line),
  ¬(A.onLine L)
  → ∃ (M : Line),
    A.onLine M
    ∧ perpLine L M
    ∧ (∀ (N : Line), A.onLine N ∧ perpLine L N → N = M) :=
by
  sorry

theorem perpendicular_and_slant_theorem :
  ∀ (p q r : Point) (L M : Line),
    ¬(p.onLine L) ∧
    p.onLine M ∧
    twoLinesIntersectAtPoint L M q ∧
    perpLine L M ∧
    r.onLine L ∧
    r ≠ q
  → (|(p─q)| < |(p─r)|) :=
by sorry

theorem triangle_side_angle_inequality : ∀ (a b c: Point),
  (triangle a b c) ∧ (|(b─c)| > |(a─c)|)
  → ∠ b:a:c > ∠ a:b:c := by
sorry




theorem inscribed_angle_and_congruent_arcs : ∀
(A B C A' B' C' : Point) (Ω : Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω
  ∧ A'.onCircle Ω ∧ B'.onCircle Ω ∧ C'.onCircle Ω
  ∧ (|(A─C)| = |(A'─C')|)
  → ∠ A:B:C = ∠ A':B':C'
:= by
sorry


theorem common_point_tangent_circles : ∀
  (C1 C2 : Circle) (O1 O2 p : Point) (L : Line),
  O1.isCentre C1 ∧
  O2.isCentre C2 ∧
  O1.onLine L ∧
  O2.onLine L ∧
  p.onLine L ∧
  p.onCircle C1 ∧
  p.onCircle C2
  → (∀ (q : Point), q.onCircle C1 ∧ q.onCircle C2 → q = p)
:= by
sorry

theorem intersecting_circles_perpendicular_bisector :
  ∀ (C1 C2 : Circle) (O1 O2 x y : Point) (L : Line),
    (O1.isCentre C1) ∧
    (O2.isCentre C2) ∧
    (intersectsCircle C1 C2) ∧
    (x.onCircle C1) ∧
    (x.onCircle C2) ∧
    (y.onCircle C1) ∧
    (y.onCircle C2) ∧
    (x ≠ y) ∧
    (distinctPointsOnLine O1 O2 L)
    → perpBisector x y L
:= by
sorry

theorem parallel_lines_and_transversal_consecutive_interior_angles :
  ∀ (L1 L2 L3 : Line) (A B U V : Point),
  (A.onLine L1 ∧ A.onLine L3) ∧
  (B.onLine L2 ∧ B.onLine L3) ∧
  (A ≠ B) ∧
  (U.onLine L1 ∧ U ≠ A) ∧
  (V.onLine L2 ∧ V ≠ B) ∧
  (∠ U:A:B + ∠ V:B:A = ∟ + ∟)
  → ¬(∃ X : Point, X.onLine L1 ∧ X.onLine L2)
:= by
sorry

theorem polygon_angle_sum : ∀ (A B C D : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA →
  ∠B:A:C + ∠C:B:D + ∠D:C:A + ∠A:D:B = 2 * (∟ + ∟) :=
by
  sorry

theorem central_angles_congruent_arcs : ∀ (O a b c d : Point) (Ω : Circle),
  O.isCentre Ω ∧ a.onCircle Ω ∧ b.onCircle Ω ∧ c.onCircle Ω ∧ d.onCircle Ω ∧ (∠ a:O:b = ∠ c:O:d)
  → |(a─b)| = |(c─d)| := by
sorry

theorem inscribed_angle_and_inscribed_polygon :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA ∧ cyclic A B C D)
  → ( (∠B:A:D + ∠B:C:D = ∟ + ∟) ∧ (∠A:B:C + ∠C:D:A = ∟ + ∟) ) := by
sorry

theorem rhombus_properties :
  ∀ (A B C D : Point) (AB BC CD DA AC BD : Line),
  (formQuadrilateral A B C D AB BC CD DA
   ∧ ¬(AB.intersectsLine CD)
   ∧ ¬(BC.intersectsLine DA)
   ∧ |(A─B)| = |(B─C)|
   ∧ |(B─C)| = |(C─D)|
   ∧ |(C─D)| = |(D─A)|)
  → (perpLine AC BD
     ∧ ∠B:A:C = ∠C:A:D
     ∧ ∠B:C:A = ∠A:C:D
     ∧ ∠A:B:D = ∠D:B:C
     ∧ ∠C:D:B = ∠B:D:A) := by
sorry

theorem angle_congruence_construction : ∀
  (A B C P Q R : Point),
  (A ≠ B) ∧ (B ≠ C) ∧ (P ≠ Q) ∧ (Q ≠ R)
  → ∠ A:B:C = ∠ P:Q:R
:= by
sorry

theorem perpendicular_smaller_than_slant :
∀ (P Q : Point) (L M : Line),
(¬(P.onLine L) ∧ Q.onLine L ∧ P.onLine M ∧ Q.onLine M ∧ perpLine L M)
→ ∀ (X : Point), (X.onLine L ∧ X ≠ Q) → |(P─Q)| < |(P─X)| := by
sorry

theorem inscribed_angle_and_tangent : ∀ (A B C : Point) (Ω : Circle) (L : Line),
  (A.onCircle Ω) ∧ (B.onCircle Ω) ∧ (C.onCircle Ω) ∧ (A ≠ B) ∧ (B ≠ C) ∧ (C ≠ A) ∧
  L.tangentLine Ω ∧ A.onLine L
  → ∠ B:A:L = ∠ B:C:A :=
by sorry

theorem parallelogram_tests : ∀
  (A B C D : Point)
  (AB BC CD DA AC BD : Line),
  (formQuadrilateral A B C D AB BC CD DA) ∧
  (
    (|(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)|)
    ∨
    (|(A─B)| = |(C─D)| ∧ ¬(∃ X : Point, twoLinesIntersectAtPoint AB CD X))
    ∨
    (∃ O : Point, twoLinesIntersectAtPoint AC BD O ∧ midpoint A O C ∧ midpoint B O D)
  )
  →
  (¬(∃ X : Point, twoLinesIntersectAtPoint AB DC X) ∧ ¬(∃ Y : Point, twoLinesIntersectAtPoint BC DA Y))
:= by
sorry



theorem parallel_lines_alternate_exterior_angles_converse :
∀ (L M T : Line) (A B C D : Point),
  (¬ ∃ X : Point, twoLinesIntersectAtPoint L M X) ∧
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  (A ≠ C) ∧
  (B ≠ D)
  → ∠ C:A:B = ∠ A:B:D
:= by
sorry

theorem angle_bisection_construction :
  ∀ (A B C P Q R : Point) (AB BC : Line) (Ω1 Ω2 Ω3 : Circle),
    distinctPointsOnLine A B AB ∧
    distinctPointsOnLine B C BC ∧
    B.isCentre Ω1 ∧
    P.onCircle Ω1 ∧
    P.onLine AB ∧
    Q.onCircle Ω1 ∧
    Q.onLine BC ∧
    P ≠ B ∧
    Q ≠ B ∧
    P.isCentre Ω2 ∧
    Q.onCircle Ω2 ∧
    Q.isCentre Ω3 ∧
    P.onCircle Ω3 ∧
    R.onCircle Ω2 ∧
    R.onCircle Ω3
  → ∠A:B:R = ∠R:B:C :=
by
  sorry

theorem perpendicular_bisector_properties : ∀ (A B : Point) (L : Line),
  perpBisector A B L →
  (∀ (X : Point), X.onLine L → |(X─A)| = |(X─B)|) ∧
  (∀ (X : Point), |(X─A)| = |(X─B)| → X.onLine L)
:= by
sorry

theorem perpendicular_bisector_construction_theorem :
∀ (a b p q : Point) (L : Line),
(|(a─p)| = |(b─p)|) ∧ (|(a─q)| = |(b─q)|) ∧ distinctPointsOnLine p q L
→ perpBisector a b L := by
sorry

theorem triangle_congruence_tests_theorem :
∀ (A B C D E F : Point),
  (triangle A B C) ∧
  (triangle D E F) ∧
  (
    (|(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ ∠ B:A:C = ∠ E:D:F)
    ∨
    (∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)| ∧ ∠ B:C:A = ∠ E:F:D)
    ∨
    (|(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)|)
  )
  → (|(A─B)| = |(D─E)|) ∧ (|(B─C)| = |(E─F)|) ∧ (|(C─A)| = |(F─D)|)
    ∧ (∠ B:A:C = ∠ E:D:F) ∧ (∠ C:B:A = ∠ F:E:D) ∧ (∠ A:C:B = ∠ D:F:E) :=
by sorry

theorem circle_three_points : ∀ (A B C : Point),
  triangle A B C →
  ∃! (Ω : Circle),
    (A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω) :=
by sorry

theorem perpendicular_dropping_construction :
∀ (A : Point) (L : Line),
¬(A.onLine L) →
∃ (M : Line), A.onLine M ∧ perpLine L M
:= by sorry

theorem isosceles_triangle_bisector_median_altitude :
  ∀ (A B C M : Point) (AM BC : Line),
  (isoTriangle A B C) ∧
  (distinctPointsOnLine B C BC) ∧
  (distinctPointsOnLine A M AM) ∧
  (B.onLine BC) ∧
  (C.onLine BC) ∧
  (A.onLine AM) ∧
  (M.onLine BC) ∧
  (M.onLine AM) ∧
  (∠B:A:M = ∠M:A:C)
  → (midpoint B M C) ∧ (perpLine AM BC)
:= by
sorry

theorem triangle_side_angle_inequality_theorem : ∀ (A B C : Point),
  (triangle A B C) ∧ (|(A─B)| > |(A─C)|) →
  ∠ B:A:C > ∠ C:A:B := by
sorry

theorem parallel_lines_consecutive_exterior_angles_converse :
∀ (A B C D E F : Point) (L M T : Line),
(¬(∃ X : Point, twoLinesIntersectAtPoint L M X))
∧ twoLinesIntersectAtPoint L T A
∧ twoLinesIntersectAtPoint M T B
∧ A.onLine L
∧ A.onLine T
∧ B.onLine M
∧ B.onLine T
∧ C.onLine L
∧ D.onLine T
∧ E.onLine M
∧ F.onLine T
→ ∠C:A:D + ∠E:B:F = ∟ + ∟ :=
by
sorry

theorem isosceles_trapezoid_properties :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ¬ (∃ X : Point, twoLinesIntersectAtPoint AB CD X) ∧
  (|(B─C)| = |(D─A)|)
  → (∠A:B:C = ∠D:C:B) ∧ (∠B:A:D = ∠C:D:A) := by
sorry

theorem basic_construction_problems : ∀ (A B C : Point) (Ω₁ Ω₂ : Circle),
  A.isCentre Ω₁ ∧ B.isCentre Ω₂ ∧ C.onCircle Ω₁ ∧ C.onCircle Ω₂ ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C ∧ ¬ coll(A B C)
  → triangle A B C := by
sorry

theorem angle_bisection_construction_theorem : ∀ (A B C : Point),
(A ≠ B) ∧ (A ≠ C) ∧ ¬(coll A B C)
→ ∃ (D : Point), ∠ B:A:D = ∠ D:A:C
:= by
sorry


theorem rectangle_properties :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    (¬(∃ P : Point, twoLinesIntersectAtPoint AB CD P)) ∧
    (¬(∃ Q : Point, twoLinesIntersectAtPoint BC DA Q)) ∧
    (∠A:B:C = ∟) ∧
    (∠B:C:D = ∟) ∧
    (∠C:D:A = ∟) ∧
    (∠D:A:B = ∟)
    → (|(A─C)| = |(B─D)|)
:= by
sorry

theorem parallel_lines_definition : ∀ (L M : Line),
  (L ≠ M) ∧ (¬ (∃ p : Point, twoLinesIntersectAtPoint L M p))
  → ∀ p : Point, ¬ twoLinesIntersectAtPoint L M p
:= by
sorry

theorem common_point_tangent_circles :
  ∀ (C1 C2 : Circle) (O1 O2 T : Point) (L : Line),
    (O1.isCentre C1) ∧
    (O2.isCentre C2) ∧
    distinctPointsOnLine O1 O2 L ∧
    T.onCircle C1 ∧
    T.onCircle C2 ∧
    T.onLine L
    → (C1.intersectsCircle C2) ∧
      (∀ (Q : Point), Q.onCircle C1 ∧ Q.onCircle C2 → Q = T)
:= by sorry

theorem triangle_congruence_tests : ∀
(A B C D E F : Point),
(triangle A B C ∧ triangle D E F) ∧
(
  ( |(A─B)| = |(D─E)| ∧ ∠B:A:C = ∠E:D:F ∧ |(A─C)| = |(D─F)| )
  ∨
  ( ∠A:B:C = ∠D:E:F ∧ |(B─C)| = |(E─F)| ∧ ∠B:C:A = ∠E:F:D )
  ∨
  ( |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)| )
)
→
( |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)| ∧ ∠A:B:C = ∠D:E:F ∧ ∠B:C:A = ∠E:F:D ∧ ∠C:A:B = ∠F:D:E )
:= by
sorry

theorem parallel_lines_and_transversal_corresponding_angles :
  ∀ (L1 L2 T : Line) (P Q U V X Y : Point),
    (P.onLine L1 ∧ P.onLine T)
  ∧ (Q.onLine L2 ∧ Q.onLine T)
  ∧ (U.onLine L1 ∧ U ≠ P)
  ∧ (V.onLine T ∧ V ≠ P)
  ∧ (X.onLine L2 ∧ X ≠ Q)
  ∧ (Y.onLine T ∧ Y ≠ Q)
  ∧ (∠ U:P:V = ∠ X:Q:Y)
  → ∀ (M : Point), ¬ twoLinesIntersectAtPoint L1 L2 M
:= by
  sorry

theorem exterior_angle_sum_of_polygon : ∀
  (A B C D E F : Point)
  (AB BC CA : Line),
  (formTriangle A B C AB BC CA) ∧ (between B A D) ∧ (between C B E) ∧ (between A C F)
  → ∠ d:a:b + ∠ e:b:c + ∠ f:c:a = (∟ + ∟) + (∟ + ∟)
:= by
sorry

theorem angle_with_vertex_inside_circle :
  ∀ (O A B C D P : Point) (Ω : Circle) (AB DC : Line),
    O.isCentre Ω ∧
    A.onCircle Ω ∧
    B.onCircle Ω ∧
    C.onCircle Ω ∧
    D.onCircle Ω ∧
    P.insideCircle Ω ∧
    distinctPointsOnLine A B AB ∧
    distinctPointsOnLine C D DC ∧
    twoLinesIntersectAtPoint AB DC P
    → (∠ A:P:B + ∠ A:P:B) = (∠ A:O:B + ∠ C:O:D) :=
by
sorry

theorem parallel_lines_and_transversal_alternate_exterior_angles :
∀ (L1 L2 L3 : Line) (A B C D E F : Point),
  (twoLinesIntersectAtPoint L1 L3 A)
∧ (twoLinesIntersectAtPoint L2 L3 B)
∧ (threePointsOnLine A C L1)
∧ (threePointsOnLine A D L3)
∧ (threePointsOnLine B E L2)
∧ (threePointsOnLine B F L3)
∧ (∠C:A:D = ∠E:B:F)
→ ¬(∃ (Q : Point), twoLinesIntersectAtPoint L1 L2 Q) := by
sorry

theorem angle_sum_of_polygon : ∀ (n : Nat), (n ≥ 3) → ((n - 2) * (∟ + ∟) = (sum_of_interior_angles_of_convex_n_gon n)) := by
sorry

theorem inscribed_angle_and_vertex_inside_circle :
  ∀ (A B C D E : Point) (Ω : Circle),
    A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ D.onCircle Ω ∧ E.insideCircle Ω ∧
    twoLinesIntersectAtPoint A C B D E
    → ∠ A:E:B = ∠ C:E:D
:= by
sorry

theorem perpendicular_bisector_construction :
  ∀ (A B P Q : Point) (C1 C2 : Circle) (L : Line),
    (A ≠ B)
    ∧ (A.isCentre C1)
    ∧ (B.isCentre C2)
    ∧ (intersectsCircle C1 C2)
    ∧ (P.onCircle C1)
    ∧ (P.onCircle C2)
    ∧ (Q.onCircle C1)
    ∧ (Q.onCircle C2)
    ∧ (P ≠ Q)
    ∧ (distinctPointsOnLine P Q L)
  → perpBisector A B L
:= by
sorry

theorem parallel_lines_alternate_interior_angles_converse :
  ∀ (l₁ l₂ t : Line) (A B C D : Point),
  ¬(l₁.intersectsLine l₂) ∧
  twoLinesIntersectAtPoint l₁ t A ∧
  twoLinesIntersectAtPoint l₂ t B ∧
  C.onLine l₁ ∧ C ≠ A ∧
  D.onLine l₂ ∧ D ≠ B
  → ∠ C:A:B = ∠ A:B:D
:= by
sorry

theorem bisect_angle : ∀ (A B C : Point),
  (A ≠ B) ∧ (B ≠ C) ∧ ¬(coll A B C)
  → ∃ (X : Point), ∠ A:B:X = ∠ X:B:C
:= by
sorry

theorem triangle_angle_side_inequality : ∀ (A B C : Point),
  (triangle A B C) ∧ (∠ B:A:C > ∠ A:B:C) →
  (|(B─C)| > |(A─C)|) := by
sorry

theorem triangle_side_angle_inequality : ∀ (a b c : Point),
  (triangle a b c) ∧ (|(a─b)| > |(b─c)|)
  → ∠ a:c:b > ∠ b:a:c := by
sorry

theorem parallelogram_consecutive_angles :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (¬(∃ X : Point, twoLinesIntersectAtPoint AB CD X))
  ∧ (¬(∃ Y : Point, twoLinesIntersectAtPoint BC DA Y))
  → ( (∠A:B:C + ∠B:C:D) = ∟ + ∟ )
    ∧ ( (∠B:C:D + ∠C:D:A) = ∟ + ∟ )
    ∧ ( (∠C:D:A + ∠D:A:B) = ∟ + ∟ )
    ∧ ( (∠D:A:B + ∠A:B:C) = ∟ + ∟ )
:= by
sorry

theorem isosceles_triangle_symmetry :
  ∀ (A B C : Point) (AB BC CA : Line),
    isoTriangle A B C ∧ formTriangle A B C AB BC CA →
    ∃ (L : Line), perpBisector B C L ∧ A.onLine L
:= by
sorry

theorem isosceles_triangle_symmetry_theorem : ∀ (A B C : Point),
  isoTriangle A B C
  → ∃ (L : Line), A.onLine L ∧ perpBisector B C L
:= by
  sorry

theorem isosceles_triangle_vertex_angle_theorem :
  ∀ (A B C D : Point) (L M : Line),
  isoTriangle A B C ∧ distinctPointsOnLine B C L ∧ distinctPointsOnLine A D M ∧ D.onLine L ∧ (∠ B:A:D = ∠ D:A:C)
  → midpoint B D C ∧ perpLine M L := by
sorry

theorem tangent_circles_common_tangent :
  ∀ (C₁ C₂ : Circle) (O₁ O₂ T : Point) (L M : Line),
    (O₁.isCentre C₁ ∧ O₂.isCentre C₂)
    ∧ (∀ X : Point, (X.onCircle C₁ ∧ X.onCircle C₂) → X = T)
    ∧ (tangentAtPoint L C₁ T)
    ∧ (tangentAtPoint L C₂ T)
    ∧ (distinctPointsOnLine O₁ O₂ M)
  → perpLine M L := by
  sorry

theorem angle_bisector_properties :
∀ (A B C P : Point) (AB BC : Line),
  (threePointsOnLine B A AB) ∧
  (threePointsOnLine B C BC) ∧
  (A ≠ B) ∧
  (B ≠ C)
  → ( (∠ A:B:P = ∠ P:B:C)
      ↔ (/* P is equidistant from lines AB, BC; no built-in predicate available */) )
:= by
sorry

theorem inscribed_angle_and_polygon_angle_sum : ∀
  (A B C D : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA
  → ∠D:A:B + ∠A:B:C + ∠B:C:D + ∠C:D:A = 2 * (∟ + ∟)
:= by
sorry

theorem tangent_circles_common_tangent :
  ∀ (C1 C2 : Circle) (A M1 M2 : Point) (L M : Line),
    (M1.isCentre C1)
  ∧ (M2.isCentre C2)
  ∧ (M1 ≠ M2)
  ∧ (A ≠ M1)
  ∧ (A ≠ M2)
  ∧ (C1.intersectsCircle C2)
  ∧ (∀ X : Point, (X.onCircle C1 ∧ X.onCircle C2) → X = A)
  ∧ (A.onCircle C1)
  ∧ (A.onCircle C2)
  ∧ (tangentAtPoint L C1 A)
  ∧ (tangentAtPoint L C2 A)
  ∧ (distinctPointsOnLine M1 M2 M)
  → perpLine L M
:= by
sorry

theorem diameter_bisects_chord : ∀
  (a b c d : Point) (O : Circle) (L M : Line),
  (diameter a b O)
  ∧ (c.onCircle O)
  ∧ (d.onCircle O)
  ∧ distinctPointsOnLine a b L
  ∧ distinctPointsOnLine c d M
  ∧ perpLine L M
  → (∃ p, twoLinesIntersectAtPoint L M p ∧ midpoint c p d)
    ∧ (∠ c:a:d = ∠ c:b:d)
:= by
sorry

theorem perpendicular_erection_construction : ∀
  (A B C : Point) (AB AC : Line) (O : Circle),
  distinctPointsOnLine A B AB ∧
  distinctPointsOnLine A C AC ∧
  diameter A B O ∧
  C.onCircle O ∧
  C ≠ A ∧
  C ≠ B
  → perpLine AB AC := by
sorry

theorem trapezoid_midline : ∀
(A B C D M N : Point)
(AB BC CD DA MN : Line),
  formQuadrilateral A B C D AB BC CD DA
  ∧ (¬ ∃ X : Point, twoLinesIntersectAtPoint AB CD X)
  ∧ midpoint A M D
  ∧ midpoint B N C
  → (¬ ∃ Y : Point, twoLinesIntersectAtPoint MN AB Y)
    ∧ (¬ ∃ Z : Point, twoLinesIntersectAtPoint MN CD Z)
    ∧ (|(M─N)| = (|(A─B)| + |(C─D)|) / 2)
:= by
sorry

theorem construct_angle_congruent : ∀ (A B C : Point), (¬ coll A B C) → ∃ (D E F : Point), (¬ coll D E F ∧ (∠ D:E:F = ∠ A:B:C)) := by
sorry

theorem perpendicular_dropping_construction_theorem :
  ∀ (A : Point) (L : Line),
    ¬(A.onLine L)
    → ∃ (M : Line), A.onLine M ∧ perpLine M L
:= by
sorry

theorem isosceles_triangle_vertex_angle : ∀ (A B C D: Point),
  (isoTriangle A B C ∧ between B D C ∧ ∠B:A:D = ∠D:A:C)
  → (midpoint B D C ∧ ∠A:D:B = ∟) := by
sorry

theorem triangle_angle_side_inequality : ∀ (A B C : Point),
  (triangle A B C)
  →
  (
    (∠B:A:C > ∠A:B:C → |(B─C)| > |(A─C)|) ∧
    (∠B:A:C > ∠A:C:B → |(B─C)| > |(A─B)|) ∧
    (∠A:B:C > ∠B:A:C → |(A─C)| > |(B─C)|) ∧
    (∠A:B:C > ∠A:C:B → |(A─C)| > |(A─B)|) ∧
    (∠A:C:B > ∠B:A:C → |(A─B)| > |(B─C)|) ∧
    (∠A:C:B > ∠A:B:C → |(A─B)| > |(A─C)|)
  )
:= by
sorry

theorem inscribed_angle_definition :
  ∀ (O : Circle) (A B C : Point),
  A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ A ≠ B ∧ B ≠ C ∧ A ≠ C
  → ∃ (L1 L2 : Line),
    threePointsOnLine A B L1 ∧ threePointsOnLine A C L2
:= by
sorry

theorem right_triangle_leg_geometric_mean :
∀ (A B C D : Point) (AB BC CA AD : Line),
  (formTriangle A B C AB BC CA) ∧ (rightTriangle A B C) ∧
  (A.onLine AD) ∧ (D.onLine AD) ∧
  (B.onLine BC) ∧ (C.onLine BC) ∧ (between B D C) ∧ (perpLine BC AD)
  → (|(A─B)| * |(A─B)| = |(B─C)| * |(B─D)|) ∧ (|(A─C)| * |(A─C)| = |(B─C)| * |(C─D)|) :=
by sorry

theorem triangle_angle_side_inequality_theorem :
  ∀ (A B C : Point),
  (triangle A B C) ∧ (∠B:A:C > ∠A:B:C) → |(B─C)| > |(A─C)|
:= by
sorry

theorem unique_perpendicular : ∀ (P : Point) (L : Line),
¬ P.onLine L →
∃ (M : Line), P.onLine M ∧ perpLine L M ∧ ∀ (N : Line), P.onLine N ∧ perpLine L N → N = M :=
by sorry

theorem parallel_lines_consecutive_interior_angles_converse
  : ∀ (L₁ L₂ T : Line) (A B C D : Point),
    (¬(∃ P : Point, twoLinesIntersectAtPoint L₁ L₂ P)
    ∧ twoLinesIntersectAtPoint L₁ T A
    ∧ twoLinesIntersectAtPoint L₂ T B
    ∧ distinctPointsOnLine A C L₁
    ∧ distinctPointsOnLine B D L₂)
    → (∠ C:A:B + ∠ A:B:D = ∟ + ∟)
  := by
sorry

theorem parallel_lines_and_transversal_consecutive_exterior_angles :
  ∀ (L M T : Line) (A B C1 C2 D1 D2 : Point),
  (twoLinesIntersectAtPoint L T A) ∧
  (twoLinesIntersectAtPoint M T B) ∧
  (∠ C1:A:C2 + ∠ D1:B:D2 = ∟ + ∟)
  → ¬(∃ (X : Point), X.onLine L ∧ X.onLine M) :=
by
  sorry

theorem polygon_exterior_angle_sum :
  ∀ (A B C D E F G H : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D (AB BC CD DA)
   ∧ between B A E
   ∧ between C B F
   ∧ between D C G
   ∧ between A D H)
  → ∠ E:A:B + ∠ F:B:C + ∠ G:C:D + ∠ H:D:A = (∟ + ∟ + ∟ + ∟)
:= by
sorry

theorem common_point_tangent_circles :
  ∀ (C1 C2 : Circle) (O1 O2 P : Point) (L : Line),
  (O1.isCentre C1)
  ∧ (O2.isCentre C2)
  ∧ distinctPointsOnLine O1 O2 L
  ∧ P.onCircle C1
  ∧ P.onCircle C2
  ∧ P.onLine L
  → (∀ Q, (Q.onCircle C1 ∧ Q.onCircle C2) → Q = P)
:= by
sorry

theorem erect_perpendicular : ∀ (a b c: Point) (O: Circle),
  (diameter a b O) ∧ (c.onCircle O) ∧ (c ≠ a) ∧ (c ≠ b)
  → ∠ a:c:b = ∟ := by
sorry

theorem angle_bisector_construction :
  ∀ (A B C P Q X : Point) (C₁ C₂ C₃ : Circle),
    (triangle A B C)
    ∧ (B.isCentre C₁)
    ∧ (A.onCircle C₁)
    ∧ (C.onCircle C₁)
    ∧ (P.onCircle C₁)
    ∧ (Q.onCircle C₁)
    ∧ (P.isCentre C₂)
    ∧ (Q.isCentre C₃)
    ∧ (X.onCircle C₂)
    ∧ (X.onCircle C₃)
  → ∠ A:B:X = ∠ X:B:C
:= by sorry

theorem parallel_lines_corresponding_angles_converse :
  ∀ (L M T : Line) (A B P Q R S : Point),
    (∀ X : Point, ¬ twoLinesIntersectAtPoint L M X)
    ∧ twoLinesIntersectAtPoint L T A
    ∧ twoLinesIntersectAtPoint M T B
    ∧ P.onLine L
    ∧ P ≠ A
    ∧ Q.onLine T
    ∧ Q ≠ A
    ∧ R.onLine M
    ∧ R ≠ B
    ∧ S.onLine T
    ∧ S ≠ B
    → ∠ P:A:Q = ∠ R:B:S
:= by
sorry

theorem isosceles_trapezoid_tests : ∀
  (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ ((¬(AB.intersectsLine CD)) ∨ (¬(BC.intersectsLine DA)))
  ∧ ((|(B─C)| = |(A─D)|) ∨ (∠B:A:D = ∠C:D:A))
  → ((|(B─C)| = |(A─D)|) ∨ (∠B:A:D = ∠C:D:A)) :=
by
sorry

theorem trapezoid_tests : ∀ (A B C D : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  ( (¬(AB.intersectsLine CD) ∧ BC.intersectsLine DA) ∨ (AB.intersectsLine CD ∧ ¬(BC.intersectsLine DA)) )
  →
  -- We introduce “trapezoid” as: a quadrilateral with exactly one pair of parallel sides.
  (formQuadrilateral A B C D AB BC CD DA ∧
    ( (¬(AB.intersectsLine CD) ∧ BC.intersectsLine DA)
      ∨ (AB.intersectsLine CD ∧ ¬(BC.intersectsLine DA)) ))
:= by
sorry

theorem square_properties :
∀ (A B C D : Point) (AB BC CD DA AC BD : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (threePointsOnLine A C AC)
  ∧ (threePointsOnLine B D BD)
  ∧ (¬(AB.intersectsLine CD))
  ∧ (¬(BC.intersectsLine DA))
  ∧ (|(A─B)| = |(B─C)|)
  ∧ (|(B─C)| = |(C─D)|)
  ∧ (|(C─D)| = |(D─A)|)
  ∧ (∠B:A:D = ∟)
  ∧ (∠A:B:C = ∟)
  ∧ (∠B:C:D = ∟)
  ∧ (∠C:D:A = ∟)
  →
  (|(A─C)| = |(B─D)|)
  ∧ perpLine AC BD
  ∧ (∠B:A:C = ∠C:A:D)
  ∧ (∠B:C:A = ∠A:C:D)
  ∧ (∠A:B:D = ∠D:B:C)
  ∧ (∠C:D:B = ∠B:D:A)
:= by
sorry

theorem inscribed_angle_and_polygon_exterior_angle_sum :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  formQuadrilateral A B C D AB BC CD DA
  → ( ∠ A:B:C + ∠ B:C:D + ∠ C:D:A + ∠ D:A:B = 4∟ )
:= by
sorry

theorem right_triangle_altitude_geometric_mean :
∀ (A B C P : Point),
  rightTriangle A B C ∧ between B P C ∧ perpLine (Line A P) (Line B C)
  → (|(A─P)| * |(A─P)| = |(B─P)| * |(P─C)|) :=
by sorry

theorem segment_bisection_construction :
  ∀ (A B P : Point) (C D : Circle),
  (A ≠ B)
  ∧ A.isCentre C
  ∧ B.onCircle C
  ∧ B.isCentre D
  ∧ A.onCircle D
  ∧ intersectsCircle C D
  ∧ P.onCircle C
  ∧ P.onCircle D
  → isoTriangle P A B
:= by
sorry
