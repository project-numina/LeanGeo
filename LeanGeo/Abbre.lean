import SystemE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open LeanGeo
namespace LeanGeo

/-Relations-/
@[simp]
abbrev Coll (A B C : Point) : Prop :=
between A B C ∨ between B C A ∨ between C A B ∨ A = B ∨ A = C ∨ B = C

@[simp]
abbrev Cyclic (A B C D: Point) : Prop :=
 ∃ (O: Circle), A.onCircle O ∧ B.onCircle O ∧ C.onCircle O ∧ D.onCircle O

@[simp]
abbrev DistinctThreePoints (A B C: Point): Prop :=
A ≠ B ∧ B ≠ C ∧ A ≠ C

@[simp]
abbrev DistinctFourPoints (A B C D : Point): Prop :=
A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D

@[simp]
abbrev TwoLinesIntersectAtPoint (AB BC : Line) (b: Point) : Prop :=
  AB.intersectsLine BC ∧ b.onLine AB ∧ b.onLine BC ∧ AB ≠ BC

@[simp]
abbrev distinctThreePointsOnLine (A B C : Point) (L : Line) : Prop :=
(A.onLine L) ∧ (B.onLine L) ∧ (C.onLine L) ∧ DistinctThreePoints A B C

@[simp]
abbrev Concurrent (l1 l2 l3 : Line) : Prop :=
  ∃ (P : Point), P.onLine l1 ∧ P.onLine l2 ∧ P.onLine l3

@[simp]
abbrev LiesOnRay (A B C : Point) : Prop :=
between A C B ∨ between A B C ∨ C = B

@[simp]
abbrev MidPoint (A P B : Point) : Prop :=
  between A P B ∧ |(A─P)| = |(P─B)|

/-Perpendicular-/
@[simp]
abbrev PerpLineAtPoint (L M : Line) (X : Point): Prop :=
  ∀ (A B: Point), (A ≠ X) ∧ (B ≠ X) ∧ (A.onLine L) ∧ (B.onLine M) → (∠A:X:B = ∟)

@[simp]
abbrev PerpLine (L M : Line) : Prop :=
  ∃(X : Point), TwoLinesIntersectAtPoint L M X ∧ PerpLineAtPoint L M X

@[simp]
abbrev Foot (A B : Point) (l : Line) :=
  ¬A.onLine l ∧ B.onLine l ∧ (∀ (C : Point), C.onLine l ∧ B ≠ C → ∠ C:B:A = ∟)

@[simp]
abbrev PerpBisector (a b : Point) (L : Line) : Prop :=
  ¬(a = b) ∧ ∀ (x : Point), x.onLine L → |(x─a)| = |(x─b)|

@[simp]
abbrev PerpFourPoints (A B C D : Point) : Prop :=
∃ (P : Point), (Coll P A B) ∧ (Coll P C D) ∧ (∠ A:P:C = ∟)

/-Circles-/
@[simp]
abbrev Diameter (A B O: Point) (C: Circle): Prop :=
MidPoint A O B ∧ O.isCentre C ∧ A.onCircle C ∧ B.onCircle C

@[simp]
abbrev Circumcentre (O A B C : Point) : Prop :=
|(O─A)| = |(O─B)| ∧ |(O─C)| = |(O─B)|

@[simp]
abbrev Circumcircle (Ω : Circle) (A B C : Point) : Prop :=
A.onCircle Ω ∧ B.onCircle Ω ∧ C.onCircle Ω

@[simp]
abbrev TangentLineCircle (L : Line) (O : Circle) : Prop :=
∃! (P : Point), (P.onLine L) ∧ (P.onCircle O)

@[simp]
abbrev TangentLineCircleAtPoint (P O: Point) (L: Line) (C :Circle) : Prop :=
(O.isCentre C) ∧ (P.onCircle C) ∧ Foot O P L

/-Triangle-/
@[simp]
abbrev Triangle (A B C : Point) : Prop :=
¬ (Coll A B C)

@[simp]
abbrev AcuteTriangle (A B C : Point) : Prop :=
Triangle A B C ∧ ∠A:B:C < ∟ ∧ ∠B:C:A < ∟ ∧ ∠C:A:B < ∟

@[simp]
abbrev formAcuteTriangle (a b c : Point) (AB BC CA : Line) : Prop :=
formTriangle a b c AB BC CA ∧ (∠ a : c : b < ∟) ∧ (∠ a : b : c < ∟) ∧ (∠ c : a : b < ∟)

@[simp]
abbrev IsoTriangle (A B C : Point) : Prop :=
Triangle A B C ∧ |(A─B)| = |(A─C)|

@[simp]
abbrev RightTriangle (A B C : Point) : Prop :=
Triangle A B C ∧ ∠B:A:C = ∟

@[simp]
abbrev InsideTriangle (X A B C : Point) (AB BC CA: Line) : Prop :=
X.sameSide A BC ∧ X.sameSide B CA ∧ X.sameSide C AB

@[simp]
abbrev CongruentTriangles (A B C D E F: Point) : Prop :=
Triangle A B C ∧ Triangle D E F ∧ |(A─B)| = |(D─E)| ∧ |(B─C)| = |(E─F)| ∧ |(A─C)| = |(D─F)| ∧ ∠A:B:C = ∠D:E:F ∧ ∠B:A:C = ∠E:D:F ∧ ∠A:C:B = ∠D:F:E

@[simp]
abbrev SimilarTriangles (A B C D E F: Point) : Prop :=
Triangle A B C ∧ Triangle D E F ∧ ∠A:B:C = ∠D:E:F ∧ ∠B:A:C = ∠E:D:F ∧ ∠A:C:B = ∠D:F:E ∧ |(A─B)| * |(E─F)| = |(B─C)| * |(D─E)| ∧ |(B─C)| * |(F─D)| = |(C─A)| * |(E─F)| ∧ |(C─A)| * |(D─E)| = |(A─B)| * |(F─D)|

@[simp]
abbrev Incentre (I A B C : Point) : Prop :=
∠ I:A:B = ∠ I:A:C ∧ ∠ I:C:A = ∠ I:C:B ∧ ∠I:B:A = ∠I:B:C

@[simp]
abbrev Excentre (J A B C : Point) : Prop :=
∠ J:B:A + ∠J:B:C = ∟ + ∟ ∧ ∠ J:C:A + ∠ J:C:B = ∟ + ∟

@[simp]
abbrev Incircle (Ω : Circle) (A B C: Point) (AB BC CA : Line) : Prop :=
TangentLineCircle AB Ω ∧ TangentLineCircle BC Ω ∧ TangentLineCircle CA Ω ∧ ∃(I: Point), Incentre I A B C ∧ I.isCentre Ω

@[simp]
abbrev Excircle (Ω : Circle) (A B C: Point) (AB BC CA : Line) : Prop :=
TangentLineCircle AB Ω ∧ TangentLineCircle BC Ω ∧ TangentLineCircle CA Ω ∧ ∃(I: Point), Excentre I A B C ∧ I.isCentre Ω

@[simp]
abbrev Orthocentre (X A B C D E F: Point) (AB BC CA : Line): Prop :=
formTriangle A B C AB BC CA ∧ Foot A D BC ∧ Foot B E CA ∧ Foot C F AB ∧ Coll A X D ∧ Coll B X E ∧ Coll C X F

/-Quadrilateral-/
@[simp]
abbrev InsideQuadrilateral (X A B C D: Point) (AB BC CD DA: Line) : Prop :=
X.sameSide A BC ∧ X.sameSide B CD ∧ X.sameSide C DA ∧ X.sameSide D AB

@[simp]
abbrev formQuadrilateral (a b c d : Point) (AB BC CD DA : Line) : Prop :=
    distinctPointsOnLine a b AB ∧
    distinctPointsOnLine c d CD ∧
    distinctPointsOnLine b c BC ∧
    distinctPointsOnLine a d DA ∧ a.sameSide b CD ∧ b.sameSide c DA ∧ c.sameSide d AB ∧ d.sameSide a BC ∧ (b ≠ d) ∧ (a ≠ c)

@[simp]
abbrev CyclicQuadrilateral (A B C D : Point) (AB BC CD DA : Line) (O: Circle): Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (A.onCircle O) ∧ (B.onCircle O) ∧ (C.onCircle O) ∧ (D.onCircle O)

@[simp]
abbrev CompleteQuadrilateral (A B C D E F : Point) (ABC CDF BDE AEF : Line) : Prop :=
formQuadrilateral A B D F ABC BDE CDF AEF ∧ C.onLine ABC ∧ C.onLine CDF ∧ E.onLine BDE ∧ E.onLine AEF ∧ between A B C ∧ between A F E

/-Other Shapes-/
@[simp]
abbrev formPentagon (A B C D E : Point) (AB BC CD DE EA : Line): Prop :=
(distinctPointsOnLine A B AB) ∧ (distinctPointsOnLine B C BC) ∧
(distinctPointsOnLine C D CD) ∧ (distinctPointsOnLine D E DE) ∧
(distinctPointsOnLine E A EA) ∧ (∠ A:B:C + ∠ B:C:D  + ∠ C:D:E + ∠ D:E:A + ∠ E:A:D = ∟ + ∟ + ∟ + ∟)

@[simp]
abbrev Trapezoid (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ (BC.intersectsLine DA)

@[simp]
abbrev Rhombus (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ (¬ BC.intersectsLine DA) ∧
|(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─D)| ∧ |(C─D)| = |(D─A)|

@[simp]
abbrev Rectangle (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA  ∧
(∠ A:B:C = ∟) ∧ (∠ B:C:D = ∟) ∧ (∠ C:D:A = ∟) ∧ (∠ D:A:B = ∟)

@[simp]
abbrev Square (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA  ∧
(∠ A:B:C = ∟) ∧ (∠ B:C:D = ∟) ∧ (∠ C:D:A = ∟) ∧ (∠ D:A:B = ∟) ∧
|(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─D)| ∧ |(C─D)| = |(D─A)|

@[simp]
abbrev Parallelogram (A B C D : Point) (AB BC CD DA : Line) : Prop :=
formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ (¬ BC.intersectsLine DA)

/-Position of Circles-/
@[simp]
abbrev LineIntersectsCircleAtTwoPoints (A B : Point) (L : Line) (Ω: Circle) : Prop :=
L.intersectsCircle Ω ∧ A ≠ B ∧ A.onCircle Ω ∧ A.onLine L ∧ B.onCircle Ω ∧ B.onLine L

@[simp]
abbrev CirclesIntersectAtTwoPoints (C1 C2 : Circle) (A B : Point): Prop :=
(C1.intersectsCircle C2) ∧ (A.onCircle C1) ∧ (A.onCircle C2) ∧ (B.onCircle C1) ∧ (B.onCircle C2) ∧ (A ≠ B)

@[simp]
abbrev TangentCircles (Ω₁ Ω₂ : Circle) : Prop :=
∃ (A : Point), A.onCircle Ω₁ ∧ A.onCircle Ω₂ ∧ (∀ (B : Point), B ≠ A ∧ B.onCircle Ω₁ ∧ B.onCircle Ω₂ → False)

@[simp]
abbrev TangentCirclesInterior (Ω₁ Ω₂ : Circle) : Prop :=
∃ (A : Point), A.onCircle Ω₁ ∧ A.onCircle Ω₂ ∧ (∀ (B : Point), B ≠ A ∧ B.onCircle Ω₁ ∧ B.onCircle Ω₂ → False) ∧ (∀ (C : Point), C.insideCircle Ω₁ → C.insideCircle Ω₂)

@[simp]
abbrev TangentCirclesExterior (Ω₁ Ω₂ : Circle) : Prop :=
∃ (A : Point), A.onCircle Ω₁ ∧ A.onCircle Ω₂ ∧ (∀ (B : Point), B ≠ A ∧ B.onCircle Ω₁ ∧ B.onCircle Ω₂ → False) ∧ (∀ (C : Point), C.insideCircle Ω₁ ∧ C.insideCircle Ω₂ → False)

@[simp]
abbrev SeperateCircles (Ω₁ Ω₂ : Circle) : Prop :=
∀ (P : Point), (P.insideCircle Ω₁ ∨ P.onCircle Ω₁) ∧ (P.insideCircle Ω₂ ∨ P.onCircle Ω₂) → False

@[simp]
abbrev InsideCircle (Ω₁ Ω₂ : Circle) : Prop :=
∀ (P : Point), P.insideCircle Ω₁ ∨ P.onCircle Ω₁ → P.insideCircle Ω₂

@[simp]
abbrev RadicalAxis (Ω₁ Ω₂ : Circle) (L : Line) : Prop :=
∀ (A : Point), A.onLine L → Pow(A, Ω₁) = Pow(A, Ω₂)

end LeanGeo
