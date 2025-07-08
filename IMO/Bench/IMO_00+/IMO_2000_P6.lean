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
    T1.onLine BC ∧ T1.onCircle Ω ∧
    T2.onLine CA ∧ T2.onCircle Ω ∧
    T3.onLine AB ∧ T3.onCircle Ω ∧
    distinctPointsOnLine T1 T2 T12 ∧
    distinctPointsOnLine T2 T3 T23 ∧
    distinctPointsOnLine T3 T1 T31 ∧
    symmetricLine H1H2 T12 L12 ∧
    symmetricLine H2H3 T23 L23 ∧
    symmetricLine H3H1 T31 L31 →
    twoLinesIntersectAtPoint L12 L23 X ∧ X.onCircle Ω ∧
    twoLinesIntersectAtPoint L23 L31 Y ∧ Y.onCircle Ω ∧
    twoLinesIntersectAtPoint L31 L12 Z ∧ Z.onCircle Ω := by
  sorry