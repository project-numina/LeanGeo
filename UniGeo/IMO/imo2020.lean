import SystemE
import UniGeo.Relations
import UniGeo.Abbre

open SystemE

theorem imo_2020_1:
  ∀ (A B C D P Q R Z X : Point) (AB BC CD DA DQ l CR: Line),
  (formQuadrilateral A B C D AB BC CD DA) ∧
  (P.sameSide C AB) ∧ (P.sameSide A CD) ∧ (P.sameSide D BC) ∧
  (P.sameSide B DA) ∧ (B ≠ P) ∧ (A ≠ P) ∧ (C ≠ P) ∧ (D ≠ P) ∧
  (2 * (∠P : A : D : ℝ) = (∠P : B : A : ℝ)) ∧
  (3 * (∠P : A : D : ℝ) = (∠D : P : A : ℝ)) ∧
  (2 * (∠C : B : P : ℝ) = (∠C : A : P : ℝ)) ∧
  (3 * (∠C : B : P : ℝ) = (∠B : P : C : ℝ)) ∧
  (∠Q : D : A : ℝ) = (∠Q : D : P : ℝ) ∧
  (∠R : C : B : ℝ) = (∠R : C : B : ℝ) ∧
  (perpBisector A B l) ∧
  (distinctPointsOnLine D Q DQ) ∧
  (distinctPointsOnLine C R CR) →
  concurrent DQ CR l := by
  euclid_intros
  euclid_apply (construct_perpBisector B P) as l1
  euclid_apply (construct_perpBisector A P) as l2
  sorry

theorem imo_2021_3: ∀ (A B C D E F X O₁ O₂: Point) (AB BC CA: Line), formAcuteTriangle A B C AB BC CA ∧
D.sameSide A BC ∧
D.sameSide C AB ∧
D.sameSide B CA ∧
|(A─B)| > |(A─C)| ∧
E.onLine AC ∧ ∠A:D:E = ∠B:C:D ∧
F.onLine AB ∧ ∠F:D:A = ∠D:B:C ∧
X.onLine AC ∧ |(C─X)| = |(B─X)| ∧
circumCentre O₁ A D C ∧ circumCentre O₂ E X D → concurrent BC EF O₁O₂ := by
  sorry

theorem imo_2021_4 : ∀ (A B C D Y T Z X : Point) (AB BC CD DA: Line) (Γ Ω: Circle), formQuadrilateral A B C D AB BC CD DA ∧
tangentLine AB Γ ∧ tangentLine BC Γ ∧ tangentLine CD Γ ∧ tangentLine DA Γ ∧
circumCircle Ω A I C ∧
X.onLine AB ∧ X.onCircle Ω ∧
Z.onLine BC ∧ Z.onCircle Ω ∧
Y.onLine DA ∧ Y.onCircle Ω ∧
T.onLine CD ∧ T.onCircle Ω → |(A─D)| + |(D─T)| + |(T─X)| + |(X─A)| = |(C─D)| + |(D─Y)| + |(Y─Z)| + |(Z─C)|:= by
  sorry

theorem imo_2022_4 : ∀ (A B C D T Y T R S: Point) (AB BC CD DE EA EA CT: Line), (formPentagon A B C D E AB BC CD DE EA) ∧
|(T─B)|=|(T─D)| ∧ |(T─C)|=|(T─E)| ∧ |(T─B)|=|(T─D)| ∧ ∠A:B:T = ∠T:E:A ∧
twoLinesIntersectAtPoint AB CD P ∧ distinctPointsOnLine C T CT ∧ twoLinesIntersectAtPoint AB CT Q ∧
between P B A ∧ between B A Q ∧
distinctPointsOnLine D T DT ∧
twoLinesIntersectAtPoint CD EA R
∧ twoLinesIntersectAtPoint DT EA S
∧ between R E A ∧ between E A S
→ cyclic P S Q R := by
sorry

theorem imo_2023_2 : ∀ (A B C D E S L P X: Point) (AB BC CA ADE BE DL l BS: Line) (Ω ω: Circle), formAcuteTriangle A B C AB BC CA ∧
|(A─B)| < |(A─C)| ∧ circumCircle Ω A B C ∧
S.onCircle Ω ∧ |(S─C)| = |(S─B)| ∧ S.sameSide A BC
∧ threePointsOnLine A D E ADE ∧ perpLine ADE BC ∧
D.onLine BS ∧ E.onCircle Ω ∧ threePointsOnLine B E L BE ∧
distinctPointsOnLine D L DL ∧ ¬(BE.intersectsLine DL) ∧
circumCircle ω B D L ∧
P.onCircle Ω ∧ P.onCircle ω ∧ P ≠ B ∧
distinctPointsOnLine B S BS ∧
tangentAtPoint l ω P ∧ twoLinesIntersectAtPoint l BS X
 → ∠ X:A:B = ∠X:A:C := by
sorry

theorem isl_2023_g2 : ∀ (A B C P S D Q E O : Point)
  (AB BC CA SP BP CQ DQ AE BE : Line)
  (Ω : Circle),
  formTriangle A B C AB BC CA ∧
  |(A─C)| > |(B─C)| ∧
  circumCircle Ω A B C ∧
  circumCentre O A B C ∧
  O.isCentre Ω ∧
  P.onLine CA ∧
  |(B─C)| = |(C─P)| ∧
  S.onLine AB ∧
  distinctPointsOnLine S P SP ∧
  perpLine SP AB ∧
  distinctPointsOnLine B P BP ∧
  D.onLine BP ∧
  D.onCircle Ω ∧
  Q.onLine SP ∧
  |(P─Q)| = |(O─A)| ∧
  between S P Q ∧
  distinctPointsOnLine C Q CQ ∧
  distinctPointsOnLine D Q DQ ∧
  perpLine AE CQ ∧
  perpLine BE DQ
  → E.onCircle Ω := by
  sorry
