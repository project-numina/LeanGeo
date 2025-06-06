import SystemE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
namespace LeanGeo
@[simp]
abbrev cyclic (A B C D: Point) : Prop :=
 ∃ (O: Circle), A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O

--abbrev collinear (P A B : Point) : Prop :=
 --- ∃ l : Line, (P.on_Line l) ∧ (A.on_Line l) ∧ (B.on_Line l)

@[simp]
abbrev midpoint (A P B : Point) : Prop :=
  between A P B ∧ |(A─P)| = |(P─B)|

@[simp]
abbrev perpLineatPoint (L M : Line) (X : Point): Prop :=
  ∀ (A B: Point) , (A ≠ X) →  (B ≠ X) → (A.onLine L) →  (B.onLine M) → (∠ A : X : B = ∟)

@[simp]
abbrev perpLine (L M : Line) : Prop :=
  ∃(X : Point), twoLinesIntersectAtPoint L M X ∧ perpLineatPoint L M X

@[simp]
abbrev foot (A B : Point) (l : Line) :=
  ¬A.onLine l ∧ B.onLine l ∧ (∀ (C : Point), C.onLine l ∧ B ≠ C → ∠ C:B:A = ∟)
@[simp]
abbrev perpBisector (a b : Point) (L : Line) : Prop :=
  ¬(a = b) ∧ ∀ (x : Point), x.onLine L → |(x─a)| = |(x─b)|

@[simp]
abbrev concurrent (l1 l2 l3 : Line) : Prop :=
  ∃ (P : Point), P.onLine l1 ∧ P.onLine l2 ∧ P.onLine l3

@[simp]
abbrev formAcuteTriangle (a b c : Point) (AB BC CA : Line) : Prop :=
formTriangle a b c AB BC CA ∧ (∠ a : c : b < ∟) ∧ (∠ a : b : c < ∟) ∧ (∠ c : a : b < ∟)

@[simp]
abbrev circumCentre (O A B C : Point) : Prop :=
|(O─A)| = |(O─B)| ∧ |(O─C)| = |(O─B)|

@[simp]
abbrev circumCircle (Ω : Circle) (A B C : Point) : Prop :=
A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω

@[simp]
abbrev inCentre (I A B C : Point) : Prop :=
∠ I:A:B = ∠ I:A:C ∧ ∠ I:C:A = ∠ I:C:B ∧ ∠I:B:A = ∠I:B:C

@[simp]
abbrev exCentre (J A B C : Point) : Prop :=
∠ J:B:A + ∠J:B:C = ∟ + ∟ ∧ ∠ J:C:A + ∠ J:C:B = ∟ + ∟

@[simp]
abbrev tangentLine (L : Line) (O : Circle) : Prop :=
∃! (P : Point), (P.onLine L) ∧ (P.onCircle O)

@[simp]
abbrev inCircle (Ω : Circle) (AB BC CA : Line) : Prop :=
tangentLine AB Ω ∧ tangentLine BC Ω ∧ tangentLine CA Ω

@[simp]
abbrev tangentAtPoint (L : Line) (O :Circle) (P : Point) : Prop :=
(P.onLine L) ∧ (P.onCircle O) ∧ ∃! (X : Point), (X.onLine L) ∧ (X.onCircle O)

@[simp]
abbrev formPentagon (A B C D E : Point) (AB BC CD DE EA : Line): Prop :=
(distinctPointsOnLine A B AB) ∧ (distinctPointsOnLine B C BC) ∧
(distinctPointsOnLine C D CD) ∧ (distinctPointsOnLine D E DE) ∧
(distinctPointsOnLine E A EA) ∧ (∠ A:B:C + ∠ B:C:D  + ∠ C:D:E + ∠ D:E:A + ∠ E:A:D = ∟ + ∟ + ∟ + ∟)

@[simp]
abbrev threePointsOnLine (A B C : Point) (L : Line) : Prop :=
(A.onLine L) ∧ (B.onLine L) ∧ (C.onLine L) ∧ (A ≠ B) ∧ (B ≠ C) ∧ (C ≠ A)

@[simp]
abbrev insideTriangle (X A B C : Point) (AB BC CA: Line) : Prop :=
X.sameSide A BC ∧ X.sameSide B CA ∧ X.sameSide C AB

@[simp]
abbrev insideQuadrilateral (X A B C D: Point) (AB BC CD DA: Line) : Prop :=
X.sameSide A BC ∧ X.sameSide B CD ∧ X.sameSide C DA ∧ X.sameSide D AB

@[simp]
abbrev coll (A B C : Point) : Prop :=
between A B C ∨ between B C A ∨ between C A B ∨ A = B ∨ A = C ∨ B = C

@[simp]
abbrev perpPoint (A B C D : Point) : Prop :=
∃ (P : Point), (coll P A B) ∧ (coll P C D) ∧ (∠ A:P:C = ∟)

@[simp]
abbrev orthoCentre (X A B C : Point) : Prop :=
perpPoint X A B C ∧ perpPoint X B A C ∧ perpPoint X C A B


@[simp]
abbrev triangle (A B C : Point) : Prop :=
¬ (coll A B C)

@[simp]
abbrev acuteTriangle (A B C : Point) : Prop :=
triangle A B C ∧ ∠A:B:C < ∟ ∧ ∠B:C:A < ∟ ∧ ∠C:A:B < ∟


@[simp]
abbrev isoTriangle (A B C : Point) : Prop :=
triangle A B C ∧ |(A─B)| = |(A─C)|

@[simp]
abbrev rightTriangle (A B C : Point) : Prop :=
triangle A B C ∧ ∠B:A:C = ∟

@[simp]
abbrev diameter (A B O: Point) (C: Circle): Prop :=
midpoint A O B ∧ O.isCentre C ∧ A.onCircle C ∧ B.onCircle C

@[simp]
abbrev circlesIntersectsAtTwoPoints (C1 C2 : Circle) (A B : Point): Prop :=
(C1.intersectsCircle C2) ∧ (A.onCircle C1) ∧ (A.onCircle C2) ∧ (B.onCircle C1) ∧ (B.onCircle C2) ∧ (A ≠ B)

@[simp]
abbrev trapezoid (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ (BC.intersectsLine DA)

@[simp]
abbrev rhombus (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ (¬ BC.intersectsLine DA) ∧
|(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─D)| ∧ |(C─D)| = |(D─A)|

@[simp]
abbrev rectangle (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA  ∧
(∠ A:B:C = ∟) ∧ (∠ B:C:D = ∟) ∧ (∠ C:D:A = ∟) ∧ (∠ D:A:B = ∟)

@[simp]
abbrev square (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA  ∧
(∠ A:B:C = ∟) ∧ (∠ B:C:D = ∟) ∧ (∠ C:D:A = ∟) ∧ (∠ D:A:B = ∟) ∧
|(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─D)| ∧ |(C─D)| = |(D─A)|

@[simp]
abbrev parallelogram (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ (¬ BC.intersectsLine DA)

@[simp]
abbrev cyclicQuadrilateral (A B C D : Point) (AB BC CD DA : Line) (O: Circle): Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (A.onCircle O) ∧ (B.onCircle O) ∧ (C.onCircle O) ∧ (D.onCircle O)

@[simp]
abbrev distinctFourPoints (A B C D : Point): Prop :=
A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D

@[simp]
abbrev distinctThreePoints (A B C: Point): Prop :=
A ≠ B ∧ B ≠ C ∧ A ≠ C

@[simp]
abbrev congruentTriangle (A B C D E F: Point) : Prop :=
triangle A B C ∧ triangle D E F ∧ |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(A─C)| = |(D─F)| ∧ ∠A:B:C = ∠D:E:F ∧ ∠B:A:C = ∠E:D:F ∧ ∠A:C:B = ∠D:F:E

@[simp]
abbrev similarTriangle (A B C D E F: Point) : Prop :=
triangle A B C ∧ triangle D E F ∧ ∠A:B:C = ∠D:E:F ∧ ∠B:A:C = ∠E:D:F ∧ ∠A:C:B = ∠D:F:E ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ |(B─C)| * |(F─D)| = |(C─A)| * |(E─F)| ∧ |(C─A)| * |(D─E)| = |(A─B)| * |(F─D)|
end LeanGeo
namespace Triangle

@[simp]
abbrev congruent_test : Triangle → Triangle →  Prop
| (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
  -- SSS
  ((|(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(C─A)| = |(F─D)|) ∨
  -- SAS
  (|(A─B)| = |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)|) ∨
  (|(B─C)| = |(E─F)| ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
  (|(C─A)| = |(F─D)| ∧ ∠ C:A:B = ∠ F:D:E ∧ |(A─B)| = |(D─E)|) ∨
--  ASA or AAS
  (∠ A:B:C = ∠ D:E:F ∧ |(A─B)| = |(D─E)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
  (∠ B:C:A = ∠ E:F:D ∧ |(B─C)| = |(E─F)| ∧ ∠ C:A:B = ∠ F:D:E) ∨
  (∠ C:A:B = ∠ F:D:E ∧ |(C─A)| = |(F─D)| ∧ ∠ A:B:C = ∠ D:E:F) ∨
  (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(B─C)| = |(E─F)|) ∨
  (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E ∧ |(C─A)| = |(F─D)|) ∨
  (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F ∧ |(A─B)| = |(D─E)|) ∨
  (∠ C:A:B = ∠ F:D:E ∧ ∠ B:C:A = ∠ E:F:D ∧ |(A─B)| = |(D─E)|) ∨
  (∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D ∧ |(C─A)| = |(F─D)|) ∨
  (∠ A:B:C = ∠ D:E:F ∧ |(B─C)| = |(E─F)| ∧ ∠ C:A:B = ∠ F:D:E))
  ∧ ((¬ LeanGeo.coll A B C) ∨ (¬ LeanGeo.coll D E F))

@[simp]
axiom congruent_property (T1 T2: Triangle): congruent T1 T2 →
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(A─C)| = |(D─F)| ∧ ∠ A:B:C = ∠ D:E:F ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F
@[simp]
abbrev similar_test (T1 T2: Triangle): Prop :=
  match T1, T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
  ((∠ A:B:C = ∠ D:E:F ∧ ∠ B:C:A = ∠ E:F:D) ∨
  (∠ B:C:A = ∠ E:F:D ∧ ∠ C:A:B = ∠ F:D:E) ∨
  (∠ C:A:B = ∠ F:D:E ∧ ∠ A:B:C = ∠ D:E:F) ∨
-- SAS criterion (with side ratios)
  (|(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ ∠ A:B:C = ∠ D:E:F) ∨
  (|(B─C)| * |(F─D)| = |(C─A)| * |(E─F)| ∧ ∠ B:C:A = ∠ E:F:D) ∨
  (|(C─A)| * |(D─E)| = |(A─B)| * |(F─D)| ∧ ∠ C:A:B = ∠ F:D:E) ∨
-- SSS criterion (with side ratios)
  (|(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ |(B─C)| * |(F─D)| = |(C─A)| * |(E─F)|)
  ∧ (¬ LeanGeo.coll A B C))

notation:50 a:51 "~" b:51 => similar a b

@[simp]
axiom similar_property (T1 T2: Triangle):  T1.similar_test T2 →
  match T1,T2 with
  | (Triangle.ofPoints A B C) ,(Triangle.ofPoints D E F) =>
    |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ |(B─C)| * |(F─D)| = |(C─A)| * |(E─F)|
   ∧ |(C─A)| * |(D─E)| = |(A─B)| * |(F─D)| ∧ ∠ A:B:C = ∠ D:E:F
   ∧ ∠ A:C:B = ∠ D:F:E ∧ ∠ B:A:C = ∠ E:D:F

end Triangle
