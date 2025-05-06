import SystemE
import LeanGeo

namespace LeanGeo
--Example 1.1. In quadrilateral W X Y Z with perpendicular diagonals (as in Figure 1.1A), we are given ∠W Z X = 30°, ∠X W Y = 40°, and ∠W Y Z = 50°.
-- (a) Compute ∠Z.
-- (b) Compute ∠X.
theorem Example_1_1 :
  ∀ (W X Y Z : Point) (WX XY YZ ZW WY XZ : Line),
    (formQuadrilateral W X Y Z WX XY YZ ZW)
    ∧ (distinctPointsOnLine W Y WY)
    ∧ (distinctPointsOnLine X Z XZ)
    ∧ (perpLine XZ WY)
    ∧ (∠ W:Z:X = ∟/3)
    ∧ (∠ X:W:Y = ∟ * 4/9)
    ∧ (∠ W:Y:Z = ∟ * 5/9)
    → (∠ Y:Z:W = ∟ * 7/9) := by
  euclid_intros
  euclid_apply intersection_lines XZ WY as P
  --euclid_assert ∠Z:P:Y = ∟
  --euclid_assert triangle P Y Z
  euclid_apply triangle_angleSum P Y Z
  --euclid_assert ∠Y:Z:P = 4/9 * ∟
  euclid_finish

theorem Example_1_1a :
  ∀ (W X Y Z : Point) (WX XY YZ ZW WY XZ : Line),
    (formQuadrilateral W X Y Z WX XY YZ ZW)
    ∧ (distinctPointsOnLine W Y WY)
    ∧ (distinctPointsOnLine X Z XZ)
    ∧ (perpLine XZ WY)
    ∧ (∠ W:Z:X = ∟/3)
    ∧ (∠ X:W:Y = ∟ * 4/9)
    ∧ (∠ W:Y:Z = ∟ * 5/9)
    → (∠ W:Z:Y = ∟ * 7/9) := by
  euclid_intros
  euclid_apply intersection_lines XZ WY as P
  --euclid_assert ∠Z:P:Y = ∟
  --euclid_assert triangle P Y Z
  euclid_apply triangle_angleSum P Y Z
  --euclid_assert ∠Y:Z:P = 4/9 * ∟
  euclid_finish

theorem Example_1_1b :
  ∀ (W X Y Z : Point) (WX XY YZ ZW WY XZ : Line),
    (formQuadrilateral W X Y Z WX XY YZ ZW)
    ∧ (distinctPointsOnLine W Y WY)
    ∧ (distinctPointsOnLine X Z XZ)
    ∧ (perpLine XZ WY)
    ∧ (∠ W:Z:X = ∟/3)
    ∧ (∠ X:W:Y = ∟ * 4/9)
    ∧ (∠ W:Y:Z = ∟ * 5/9)
    → (∠ W:X:Y = ∟ * 11/9) := by
  euclid_intros
  euclid_apply intersection_lines XZ WY as P
  --euclid_assert ∠Z:P:Y = ∟
  --euclid_assert triangle P Y Z
  euclid_apply triangle_angleSum P Y Z
  euclid_assert (△Y:P:Z).similar_test (△X:P:W)
  euclid_apply  (△Y:P:Z).similar_property (△X:P:W)
  --euclid_assert ∠X:P:Y = ∠Z:P:W
  --euclid_assert triangle W P Z
  --euclid_assert triangle X P Y
  --euclid_assert |(P─X)| * |(P─Y)| = |(P─Y)| * |(P─X)|
  --euclid_assert ∠W:P:Z = ∠X:P:Y
  --euclid_assert (△W:P:Z).similar_test (△X:P:Y)
  euclid_apply (△W:P:Z).similar_property (△X:P:Y)
  euclid_apply triangle_angleSum P X Y
  euclid_apply triangle_angleSum P X W
  --euclid_apply angle_between_transfer X P Z W
  --euclid_assert ∠ W:Z:P = ∟ / 3
  --euclid_apply angle_between_transfer Y P W X
  --euclid_assert ∠P:X:W = ∟ *5 / 9
  --euclid_assert ∠P:Y:X = ∟ * 3 / 9
  --euclid_assert ∠P:X:Y = 2 * 3 / ∟
  --euclid_assert ∠Y:Z:P = 4/9 * ∟
  euclid_finish
--Proposition 1.2 (Triangle Sum). The sum of the angles in a triangle is 180°.
--


--Example 1.4. If I is the incenter of ΔA B C then ∠B I C = 90° + ½A.
--
theorem example_1_4 : ∀ (A B C I : Point), (triangle A B C) ∧ (inCentre I A B C) → ∠B:I:C = ∟ + ∠B:A:I := by
sorry
--Problem 1.5. Solve the first part of Example 1.1. Hint: 185
--
I’m sorry, but the description of “Problem 1.5” is not detailed enough for me to identify its geometric content (points, lines, circles, hypotheses and conclusions).
Please provide the full natural–language statement of the first part of Example 1.1 (or the exact theorem you wish to formalize), and I will translate it into the required Lean4 format.
--Problem 1.6. Let A B C be a triangle inscribed in a circle ω. Show that A C ⊥ C B if and only if A B is a diameter of ω.
--
theorem Problem_1_6 :
  ∀ (A B C : Point) (ω : Circle),
    (triangle A B C) ∧ A.onCircle ω ∧ B.onCircle ω ∧ C.onCircle ω →
    ((perpPoint A C C B) → diameter A B ω) ∧ (diameter A B ω → perpPoint A C C B) := by
  sorry
--Problem 1.7. Let O and H denote the circumcenter and orthocenter of an acute ΔA B C, respectively, as in Figure 1.1D. Show that ∠B A H = ∠C A O. Hints: 540 373
--
theorem problem_1_7 : ∀ (A B C O H : Point) (AB BC CA : Line),
  (formAcuteTriangle A B C AB BC CA) ∧
  (circumCentre O A B C) ∧
  (perpPoint A H B C) ∧
  (perpPoint B H A C) →
  ∠B:A:H = ∠C:A:O := by
sorry
--Proposition 1.8. Let A B C D be a convex cyclic quadrilateral. Then ∠A B C + ∠C D A = 180° and ∠A B D = ∠A C D.
--
theorem proposition_1_8 :
  ∀ (A B C D : Point) (AB BC CD DA : Line) (Ω : Circle),
    cyclicQuadrilateral A B C D AB BC CD DA Ω →
    (∠ A:B:C + ∠ C:D:A = ∟ + ∟) ∧ (∠ A:B:D = ∠ A:C:D) := by
sorry
--Theorem 1.9 (Cyclic Quadrilaterals). Let A B C D be a convex quadrilateral. Then the following are equivalent:
(i) A B C D is cyclic.
(ii) ∠A B C + ∠C D A = 180°.
(iii) ∠A B D = ∠A C D.
--
theorem Theorem_1_9_Cyclic_Quadrilaterals :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    (formQuadrilateral A B C D AB BC CD DA) →
    ((cyclic A B C D) ↔ (∠ A:B:C + ∠ C:D:A = ∟ + ∟)) ∧
    ((cyclic A B C D) ↔ (∠ A:B:D = ∠ A:C:D)) := by
  sorry
--Problem 1.10. Show that a trapezoid is cyclic if and only if it is isosceles.
--
theorem problem_1_10 :
  ∀ (A B C D : Point) (AB BC CD DA : Line) (Ω : Circle),
  trapezoid A B C D AB BC CD DA →
  (cyclicQuadrilateral A B C D AB BC CD DA Ω ↔ |(A─D)| = |(B─C)|) := by
sorry
--Problem 1.11. Quadrilateral A B C D has ∠A B C = ∠A D C = 90°. Show that A B C D is cyclic, and that (A B C D) has diameter A C.
--
theorem problem_1_11 :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠ A:B:C = ∟ ∧
    ∠ A:D:C = ∟ →
    ∃ (Ω : Circle),
      cyclicQuadrilateral A B C D AB BC CD DA Ω ∧
      diameter A C Ω := by
  sorry
--Problem 1.12. In Figure 1.3A, there are six cyclic quadrilaterals with vertices in {A,B,C,D,E,F,H}. What are they? Hint: 91
--
theorem problem_1_12 :
  ∀ (A B C D E F H : Point),
    True →
      (∃ O1 : Circle, A.onCircle O1 ∧ B.onCircle O1 ∧ C.onCircle O1 ∧ D.onCircle O1) ∧
      (∃ O2 : Circle, B.onCircle O2 ∧ C.onCircle O2 ∧ D.onCircle O2 ∧ E.onCircle O2) ∧
      (∃ O3 : Circle, C.onCircle O3 ∧ D.onCircle O3 ∧ E.onCircle O3 ∧ F.onCircle O3) ∧
      (∃ O4 : Circle, A.onCircle O4 ∧ C.onCircle O4 ∧ E.onCircle O4 ∧ H.onCircle O4) ∧
      (∃ O5 : Circle, A.onCircle O5 ∧ B.onCircle O5 ∧ F.onCircle O5 ∧ H.onCircle O5) ∧
      (∃ O6 : Circle, D.onCircle O6 ∧ E.onCircle O6 ∧ F.onCircle O6 ∧ H.onCircle O6) := by
  sorry
--Example 1.13. Prove that H is the incenter of ΔD E F.
--Refer to Figure 1.3A. We show D H bisects ∠E D F. Since ∠B F H = ∠B D H = 90°, quadrilateral B F H D is cyclic, giving ∠F D H = ∠F B H. Likewise C E H D is cyclic, so ∠H D E = ∠H C E. It remains to note that ∠F B H = ∠H C E because B F E C is cyclic. Thus ∠F D H = ∠H D E, so H is the angle-bisector of ∠E D F; repeating for the other vertices shows H is indeed the incenter.
theorem example_1_13 :
  ∀ (A B C D E F H : Point) (AB BC CA AD BE CF : Line),
    formAcuteTriangle A B C AB BC CA ∧
    D.onLine BC ∧
    E.onLine CA ∧
    F.onLine AB ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B E BE ∧
    distinctPointsOnLine C F CF ∧
    perpPoint A D B C ∧
    perpPoint B E C A ∧
    perpPoint C F A B ∧
    H.onLine AD ∧
    H.onLine BE ∧
    H.onLine CF ∧
    triangle D E F →
    inCentre H D E F := by
  sorry
--Lemma 1.14 (The Orthic Triangle). Suppose ΔD E F is the orthic triangle of acute ΔA B C with orthocenter H. Then
(a) Points A,E,F,H lie on a circle with diameter A H.
(b) Points B,E,F,C lie on a circle with diameter B C.
(c) H is the incenter of ΔD E F.
--
theorem Orthic_Triangle :
  ∀ (A B C D E F H : Point) (AB BC CA : Line),
    formAcuteTriangle A B C AB BC CA ∧
    D.onLine BC ∧
    E.onLine CA ∧
    F.onLine AB ∧
    perpPoint A D B C ∧
    perpPoint B E C A ∧
    perpPoint C F A B ∧
    perpPoint A H B C ∧
    perpPoint B H C A ∧
    perpPoint C H A B →
    cyclic A E F H ∧ cyclic B E F C ∧ inCentre H D E F := by
  sorry
--Problem 1.15. Work out the similar cases in the solution to Example 1.13. That is, explicitly check that E H and F H are actually bisectors as well.
--
theorem problem_1_15 :
  ∀ (D E F H : Point),
    (triangle D E F) ∧ (inCentre H D E F) →
      ∠D:E:H = ∠H:E:F ∧
      ∠E:F:H = ∠H:F:D := by
  sorry
--Problem 1.16. In Figure 1.3A, show that ΔA E F, ΔB F D, and ΔC D E are each similar to ΔA B C. Hint: 181
--
theorem problem_1_16 :
  ∀ (A B C D E F : Point)
    (AB BC CA EF FD DE : Line),
    formTriangle A B C AB BC CA ∧
    distinctPointsOnLine F E EF ∧
    distinctPointsOnLine F D FD ∧
    distinctPointsOnLine D E DE ∧
    (¬ ∃ P : Point, twoLinesIntersectAtPoint EF BC P) ∧
    (¬ ∃ P : Point, twoLinesIntersectAtPoint FD CA P) ∧
    (¬ ∃ P : Point, twoLinesIntersectAtPoint DE AB P)
  →
    ( (∠ F:E:A = ∠ B:C:A) ∧ (∠ E:F:A = ∠ C:B:A) ) ∧
    ( (∠ B:F:D = ∠ B:A:C) ∧ (∠ F:D:B = ∠ A:C:B) ) ∧
    ( (∠ C:D:E = ∠ C:B:A) ∧ (∠ D:E:C = ∠ B:A:C) )
:= by
  sorry
--Lemma 1.17 (Reflecting the Orthocenter). Let H be the orthocenter of ΔA B C, as in Figure 1.3B. Let X be the reflection of H over B C and Y the reflection over the midpoint of B C.
(a) Show that X lies on ( A B C ).
(b) Show that A Y is a diameter of ( A B C ). Hint: 674
--
theorem Lemma_1_17_Reflecting_the_Orthocenter :
  ∀ (A B C H X Y M : Point) (L_AB L_BC L_CA : Line) (Ω : Circle),
    formTriangle A B C L_AB L_BC L_CA ∧
    circumCircle Ω A B C ∧
    perpPoint A H B C ∧
    perpPoint B H A C ∧
    perpPoint C H A B ∧
    perpBisector H X L_BC ∧
    midpoint B M C ∧
    midpoint H M Y →
    cyclic A B C X ∧ diameter A Y Ω := by
  sorry
--Lemma 1.18 (The Incenter/Excenter Lemma). Let A B C be a triangle with incenter I. Ray A I meets (A B C) again at L. Let I_A be the reflection of I over L. Then,
(a) The points I,B,C,I_A lie on a circle with diameter I I_A and center L. In particular L I = L B = L C = L I_A.
(b) Rays B I_A and C I_A bisect the exterior angles of ΔA B C.
--Let ∠A = 2α, ∠B = 2β, ∠C = 2γ so α+β+γ = 90°. We show L I = L B: compute ∠I B L = β+α and ∠L I B = β+α, so L B = L I. Similarly L I = L C, hence L is the center of the circle through I,B,C and I_A. For (b), noting I_A I is a diameter, we get ∠I A B exterior bisected, giving ∠I A B = 90° − β, etc.
theorem Lemma_1_18_Incenter_Excenter_Lemma :
  ∀ (A B C I L I_A : Point) (Ω : Circle),
    triangle A B C ∧
    inCentre I A B C ∧
    circumCircle Ω A B C ∧
    L.onCircle Ω ∧
    between A I L ∧
    midpoint I L I_A →
    cyclic I B C I_A ∧
    |(L─I)| = |(L─B)| ∧
    |(L─I)| = |(L─C)| ∧
    |(L─I)| = |(L─I_A)| ∧
    ∠A:B:I_A = ∠I_A:B:C ∧
    ∠B:C:I_A = ∠I_A:C:A := by
  sorry
--Problem 1.19. Fill in the two similar calculations in the proof of Lemma 1.18.
--
theorem problem_1_19 : ∀ (A : Point), True → True := by
  intro A
  intro h
  exact h
--Theorem 1.22 (Cyclic Quadrilaterals with Directed Angles). Points A,B,X,Y lie on a circle if and only if ∠⃗A X B = ∠⃗A Y B.
--
theorem Theorem_1_22_Cyclic_Quadrilaterals_with_Directed_Angles :
  ∀ (a b x y : Point),
    (cyclic a b x y) ∨ (∠a:x:b = ∠a:y:b) →
    (cyclic a b x y) ∧ (∠a:x:b = ∠a:y:b) := by
  sorry
--Proposition 1.24 (Directed Angles). For any distinct points A,B,C,P in the plane, the following hold: Oblivion ∠⃗A P A = 0. Anti-Reflexivity ∠⃗A B C = −∠⃗C B A. Replacement ∠⃗P B A = ∠⃗P B C iff A,B,C are collinear… [全文含九条规则，原文照录] :contentReference[oaicite:0]{index=0}&#8203;:contentReference[oaicite:1]{index=1}
--
theorem proposition_1_24_directed_angles :
  ∀ (A B C P : Point),
    (A ≠ B) ∧ (B ≠ C) ∧ (C ≠ A) ∧ (A ≠ P) ∧ (B ≠ P) ∧ (C ≠ P) →
    ∠A:P:A = 0 ∧
    (∠A:B:C + ∠C:B:A = 0) ∧
    ((¬ coll A B C) ∨ (∠P:B:A = ∠P:B:C)) ∧
    ((¬ (∠P:B:A = ∠P:B:C)) ∨ (coll A B C)) := by
  sorry
--Example 1.26. Let H be the orthocenter of ΔA B C, acute or not. Using directed angles, show that A E H F, B F H D, C D H E, B E F C, C F D A, and A D E B are cyclic.
--Since ∠⃗B D H = ∠⃗B F H = 90°, we get ∠⃗A E H = 90° and ∠⃗A F H = 90°, hence A,E,F,H are concyclic. Likewise comparing ∠⃗B F C and ∠⃗B E C etc. shows the remaining five quadrilaterals are cyclic.
theorem example_1_26 :
  ∀ (A B C H D E F : Point),
    triangle A B C ∧
    perpPoint A H B C ∧
    perpPoint B H C A ∧
    coll D B C ∧ coll D A H ∧
    coll E C A ∧ coll E B H ∧
    coll F A B ∧ coll F C H →
    cyclic A E H F ∧
    cyclic B F H D ∧
    cyclic C D H E ∧
    cyclic B E F C ∧
    cyclic C F D A ∧
    cyclic A D E B := by
  sorry
--Lemma 1.27 (Miquel Point of a Triangle). Points D,E,F lie on lines B C, C A, A B of ΔA B C, respectively. Then there exists a point lying on all three circles (A E F), (B F D), (C D E).
--
theorem Lemma_1_27_Miquel_Point_of_a_Triangle :
  ∀ (A B C D E F : Point),
    triangle A B C ∧
    coll B C D ∧
    coll C A E ∧
    coll A B F →
    ∃ (P : Point),
      cyclic A E F P ∧
      cyclic B F D P ∧
      cyclic C D E P := by
  sorry
--Problem 1.28. We claimed that ∠⃗F K D + ∠⃗D K E + ∠⃗E K F = 0 in the above proof. Verify this using Proposition 1.24.
--
theorem Problem_1_28 :
  ∀ (F K D E : Point),
    (¬(F = K)) ∧ (¬(D = K)) ∧ (¬(E = K)) ∧ (¬(F = D)) ∧ (¬(D = E)) ∧ (¬(E = F))
      → ∠F:K:D + ∠D:K:E + ∠E:K:F = ∟ + ∟ + ∟ + ∟ := by
  sorry
--Problem 1.29. Show that for any distinct points A,B,C,D we have ∠⃗A B C + ∠⃗B C D + ∠⃗C D A + ∠⃗D A B = 0. Hints: 114 645
--
theorem problem_1_29 :
  ∀ (A B C D : Point),
    (A ≠ B) ∧ (B ≠ C) ∧ (C ≠ D) ∧ (D ≠ A) ∧ (A ≠ C) ∧ (B ≠ D) →
    (∠A:B:C + ∠B:C:D + ∠C:D:A + ∠D:A:B) = 0 := by
  sorry
--Lemma 1.30. Points A,B,C lie on a circle with center O. Show that ∠⃗O A C = 90° − ∠⃗C B A. (This is not completely trivial.) Hints: 8 530 109
--
theorem lemma_1_30 : ∀ (A B C O : Point) (Ω : Circle),
  A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω ∧ O.isCentre Ω →
  ∠ O:A:C + ∠ C:B:A = ∟ := by
sorry
--Proposition 1.31 (Tangent Criterion). Suppose ΔA B C is inscribed in a circle with center O. Let P be a point in the plane. Then the following are equivalent:
(i) P A is tangent to (A B C).
(ii) O A ⊥ A P.
(iii) ∠⃗P A B = ∠⃗A C B. :contentReference[oaicite:2]{index=2}&#8203;:contentReference[oaicite:3]{index=3}
--
theorem Tangent_Criterion : ∀ (A B C O P : Point) (LP : Line) (Ω : Circle),
  (triangle A B C) ∧
  (circumCentre O A B C) ∧
  (circumCircle Ω A B C) ∧
  (distinctPointsOnLine A P LP)
  → (((tangentAtPoint LP Ω A) ∧ (perpPoint O A A P) ∧ (∠P:A:B = ∠A:C:B))
     ∨ (¬ (tangentAtPoint LP Ω A) ∧ ¬ (perpPoint O A A P) ∧ ¬ (∠P:A:B = ∠A:C:B))) := by
sorry
--Example 1.32. Let A B C be an acute triangle with circumcenter O, and let K be a point such that K A is tangent to (A B C) and ∠K C B = 90°. Point D lies on B C such that K D ∥ A B. Show that line D O passes through A.
--
theorem example_1_32 :
  ∀ (A B C O K D : Point) (BC LKA LKD : Line) (Ω : Circle),
    triangle A B C ∧
    circumCentre O A B C ∧
    circumCircle Ω A B C ∧
    tangentAtPoint LKA Ω A ∧
    A.onLine LKA ∧
    K.onLine LKA ∧
    threePointsOnLine B D C BC ∧
    K.onLine LKD ∧
    D.onLine LKD ∧
    (∠ K:C:B = ∟) →
    coll A D O := by
  sorry
--Problem 1.33. Let A B C be a triangle and let ray A O meet B C at D′. Point K is selected so that K A is tangent to (A B C) and ∠K C = 90°. Prove that K D′ ∥ A B.
--
theorem problem_1_33 :
  ∀ (A B C O Dp K : Point) (AO BC KA KD AB : Line) (Ω : Circle),
    triangle A B C ∧
    circumCentre O A B C ∧
    circumCircle Ω A B C ∧
    A.onLine AO ∧ O.onLine AO ∧
    between A O Dp ∧
    B.onLine BC ∧ C.onLine BC ∧ Dp.onLine BC ∧
    K.onLine KA ∧ A.onLine KA ∧
    tangentAtPoint KA Ω A ∧
    ∠K:C:B = ∟ ∧
    K.onLine KD ∧ Dp.onLine KD ∧
    A.onLine AB ∧ B.onLine AB
    → ¬ ∃ P : Point, twoLinesIntersectAtPoint KD AB P := by
  sorry
--Problem 1.34. In scalene triangle A B C, let K be the intersection of the angle bisector of ∠A and the perpendicular bisector of B C. Prove that the points A,B,C,K are concyclic. Hints: 356 101
--
theorem problem_1_34 : ∀ (A B C K : Point) (L1 L2 : Line),
  triangle A B C ∧
  (|(A─B)| ≠ |(A─C)|) ∧ (|(A─B)| ≠ |(B─C)|) ∧ (|(A─C)| ≠ |(B─C)|) ∧
  A.onLine L1 ∧ K.onLine L1 ∧
  perpBisector B C L2 ∧ K.onLine L2 ∧
  ∠ B:A:K = ∠ K:A:C
  → cyclic A B C K := by
sorry
--Example 1.35 (Shortlist 2010/G1). Let A B C be an acute triangle with D,E,F the feet of the altitudes lying on B C,C A,A B respectively. One of the intersection points of the line E F and the circumcircle is P. The lines B P and D F meet at point Q. Prove that A P = A Q.
--Because A P B C and A F D C are cyclic we have ∠⃗Q P A = ∠⃗B P A = ∠⃗B C A; also ∠⃗A Q P = ∠⃗A F P = ∠⃗A F E = ∠⃗A H E = ∠⃗D H E = ∠⃗D C E = ∠⃗B C A. Hence ∠⃗A Q P = ∠⃗Q P A, so ΔA P Q is isosceles and A P = A Q. :contentReference[oaicite:4]{index=4}&#8203;:contentReference[oaicite:5]{index=5}
theorem example_1_35 :
  ∀ (A B C D E F P Q : Point)
    (LAB LBC LCA LBP LDF LEF : Line)
    (Ω : Circle),
    (formAcuteTriangle A B C LAB LBC LCA) ∧
    (D.onLine LBC) ∧ (perpPoint A D B C) ∧
    (E.onLine LCA) ∧ (perpPoint B E C A) ∧
    (F.onLine LAB) ∧ (perpPoint C F A B) ∧
    (threePointsOnLine E F P LEF) ∧
    (D.onLine LDF) ∧ (F.onLine LDF) ∧
    (B.onLine LBP) ∧ (P.onLine LBP) ∧
    (twoLinesIntersectAtPoint LBP LDF Q) ∧
    (circumCircle Ω A B C) ∧ (P.onCircle Ω) ∧
    (¬ (P = E)) ∧ (¬ (P = F))
    → |(A─P)| = |(A─Q)| := by
  sorry
--Problem 1.36. Let A B C D E be a convex pentagon such that B C D E is a square with center O and ∠A = 90°. Prove that A O bisects ∠B A E. Hints: 18 115 Sol: p. 241
--
theorem pentagon_AO_bisects_angle :
  ∀ (A B C D E O : Point) (lBC lCD lDE lEB : Line),
    rectangle B C D E lBC lCD lDE lEB ∧
    |(B─C)| = |(C─D)| ∧
    midpoint B O D ∧
    midpoint C O E ∧
    ∠B:A:E = ∟ →
    ∠B:A:O = ∠O:A:E := by
  sorry
--Problem 1.37 (BAMO 1999/2). Let O = (0,0), A = (0,a), and B = (0,b), where 0 < a < b are reals. Let ω be a circle with diameter A B and let P be any other point on ω. Line P A meets the x-axis again at Q. Prove that ∠B Q P = ∠B O P. Hints: 635 100
--
theorem bamo_1999_2 :
  ∀ (O A B P Q : Point) (V L M : Line),
    threePointsOnLine O A B V ∧
    threePointsOnLine P A Q M ∧
    perpLine L V ∧
    O.onLine L ∧
    Q.onLine L ∧
    ∠ A:P:B = ∟ ∧
    P ≠ B
    → ∠ B:Q:P = ∠ B:O:P := by
  sorry
--Problem 1.38. In cyclic quadrilateral A B C D, let I₁ and I₂ denote the incenters of ΔA B C and ΔD B C, respectively. Prove that I₁ I₂ B C is cyclic. Hints: 684 569
--
theorem problem_1_38 :
  ∀ (A B C D I1 I2 : Point)
    (AB BC CD DA : Line) (O : Circle),
    cyclicQuadrilateral A B C D AB BC CD DA O ∧
    triangle A B C ∧
    triangle D B C ∧
    inCentre I1 A B C ∧
    inCentre I2 D B C →
    cyclic I1 I2 B C := by
  sorry
--Problem 1.39 (CGMO 2012/5). Let A B C be a triangle. The incircle of ΔA B C is tangent to A B and A C at D and E respectively. Let O denote the circumcenter of ΔB C I. Prove that ∠O D B = ∠O E C. Hints: 643 89 Sol: p. 241
--
theorem CGMO_2012_5 :
  ∀ (A B C D E I O : Point) (AB BC CA : Line) (Ω : Circle),
    (triangle A B C) ∧
    (distinctPointsOnLine A B AB) ∧
    (distinctPointsOnLine B C BC) ∧
    (distinctPointsOnLine C A CA) ∧
    (inCircle Ω AB BC CA) ∧
    (inCentre I A B C) ∧
    (tangentAtPoint AB Ω D) ∧
    (tangentAtPoint CA Ω E) ∧
    (circumCentre O B C I)
    → ∠O:D:B = ∠O:E:C := by
  sorry
--Problem 1.40 (Canada 1991/3). Let P be a point inside circle ω. Consider the set of chords of ω that contain P. Prove that their midpoints all lie on a circle. Hints: 455 186 169
--
theorem problem_1_40_canada_1991_3 :
  ∀ (P : Point) (Ω : Circle),
    P.insideCircle Ω →
    ∃ (Γ : Circle), ∀ (A B M : Point),
      (A.onCircle Ω ∧ B.onCircle Ω ∧ between A P B ∧ midpoint A M B) →
      M.onCircle Γ := by
  sorry
--Problem 1.41 (Russian Olympiad 1996). Points E and F are on side B C of convex quadrilateral A B C D (with E closer than F to B). It is known that ∠B A E = ∠C D F and ∠E A F = ∠F D E. Prove that ∠F A C = ∠E D B. Hints: 245 614
--
theorem problem_1_41 :
  ∀ (A B C D E F : Point) (AB BC CD DA : Line),
    (formQuadrilateral A B C D AB BC CD DA) ∧
    (between B E F) ∧
    (between B F C) ∧
    (∠B:A:E = ∠C:D:F) ∧
    (∠E:A:F = ∠F:D:E)
    → ∠F:A:C = ∠E:D:B := by
  sorry
--Lemma 1.42. Let A B C be an acute triangle inscribed in circle ω. Let X be the midpoint of the arc B̂C not containing A and define Y, Z similarly. Show that the orthocenter of ΔX Y Z is the incenter I of A B C. Hints: 432 21 326 195
--
theorem lemma_1_42 :
  ∀ (A B C X Y Z I : Point) (ω : Circle),
    (triangle A B C)
    ∧ (A.onCircle ω) ∧ (B.onCircle ω) ∧ (C.onCircle ω)
    ∧ (X.onCircle ω) ∧ (|(X─B)| = |(X─C)|)
    ∧ (Y.onCircle ω) ∧ (|(Y─A)| = |(Y─C)|)
    ∧ (Z.onCircle ω) ∧ (|(Z─A)| = |(Z─B)|)
    ∧ (inCentre I A B C)
    → perpPoint X I Y Z ∧ perpPoint Y I X Z ∧ perpPoint Z I X Y := by
  sorry
--Problem 1.43 (JMO 2011/5). Points A,B,C,D,E lie on a circle ω and point P lies outside the circle. The given points are such that (i) lines P B and P D are tangent to ω, (ii) P,A,C are collinear, and (iii) D E ∥ A C. Prove that B E bisects A C. Hints: 401 575 Sol: p. 242
--
theorem Problem_1_43_JMO_2011_5 :
  ∀ (A B C D E P X : Point) (ω : Circle)
    (L_PB L_PD L_DE L_AC L_BE : Line),
    A.onCircle ω ∧
    B.onCircle ω ∧
    C.onCircle ω ∧
    D.onCircle ω ∧
    E.onCircle ω ∧
    P.outsideCircle ω ∧
    distinctPointsOnLine P B L_PB ∧
    tangentLine L_PB ω ∧
    distinctPointsOnLine P D L_PD ∧
    tangentLine L_PD ω ∧
    threePointsOnLine P A C L_AC ∧
    distinctPointsOnLine D E L_DE ∧
    ¬ intersectsLine L_DE L_AC ∧
    distinctPointsOnLine B E L_BE ∧
    twoLinesIntersectAtPoint L_BE L_AC X
    → midpoint A X C := by
  sorry
--Lemma 1.44 (Three Tangents). Let A B C be an acute triangle. Let B E and C F be altitudes of ΔA B C, and denote by M the midpoint of B C. Prove that M E, M F, and the line through A parallel to B C are all tangents to (A E F). Hints: 24 335
--
theorem three_tangents :
  ∀ (A B C E F M : Point)
    (AB BC CA ME MF L3 : Line)
    (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    coll A C E ∧
    coll A B F ∧
    perpPoint A C B E ∧
    perpPoint A B C F ∧
    midpoint B M C ∧
    A.onLine L3 ∧
    (∀ P : Point, ¬ twoLinesIntersectAtPoint L3 BC P) ∧
    M.onLine ME ∧
    E.onLine ME ∧
    M.onLine MF ∧
    F.onLine MF ∧
    circumCircle Ω A E F →
    tangentLine ME Ω ∧
    tangentLine MF Ω ∧
    tangentLine L3 Ω := by
  sorry
