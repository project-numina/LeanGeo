import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $AH_1, BH_2, CH_3$ be the altitudes of an acute angled triangle $ABC$. Its incircle touches the sides $BC, AC$ and $AB$ at $T_1, T_2$ and $T_3$ respectively. Consider the symmetric images of the lines $H_1H_2, H_2H_3$ and $H_3H_1$ with respect to the lines $T_1T_2, T_2T_3$ and $T_3T_1$. Prove that these images form a triangle whose vertices lie on the incircle of $ABC$.
theorem IMO_2000_P6 :
  ∀ (A B C H1 H2 H3 T1 T2 T3 X Y Z : Point)
    (AB BC CA T12 T23 T31 L12 L23 L31 : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    foot A H1 BC ∧
    foot B H2 CA ∧
    foot C H3 AB ∧
    inCentre I A B C ∧
    tangentAtPoint T1 I BC Ω ∧
    tangentAtPoint T2 I CA Ω ∧
    tangentAtPoint T3 I AB Ω ∧
    distinctPointsOnLine T1 T2 T12 ∧
    distinctPointsOnLine T2 T3 T23 ∧
    distinctPointsOnLine T3 T1 T31 ∧
    distinctPointsOnLine H1 H2 H12 ∧
    distinctPointsOnLine H2 H3 H23 ∧
    distinctPointsOnLine H3 H1 H31 ∧
    twoLinesIntersectAtPoint T12 H12 P1 ∧
    twoLinesIntersectAtPoint T23 H23 P2 ∧
    twoLinesIntersectAtPoint T31 H31 P3 ∧
    P1.onLine L1 ∧ P2.onLine L2 ∧ P3.onLine L3 ∧
    (∀ (P: Point), P.onLine L1 ∧ P ≠ P1 → ∠P:P1:T1 = ∠ T1:P1:H1 ∨ ∠P:P1:T1 + ∠ T1:P1:H1 = ∟ + ∟) ∧
    (∀ (P: Point), P.onLine L2 ∧ P ≠ P2 → ∠P:P2:T2 = ∠ T1:P2:H2 ∨ ∠P:P2:T2 + ∠ T3:P3:H3 = ∟ + ∟) ∧
    (∀ (P: Point), P.onLine L3 ∧ P ≠ P3 → ∠P:P3:T3 = ∠ T1:P3:H3 ∨ ∠P:P3:T3 + ∠ T3:P3:H3 = ∟ + ∟)
     ∧
    twoLinesIntersectAtPoint L12 L23 X ∧
    twoLinesIntersectAtPoint L23 L31 Y ∧
    twoLinesIntersectAtPoint L31 L12 Z → X.onCircle Ω ∧ Y.onCircle Ω ∧ Z.onCircle Ω:= by
  sorry
