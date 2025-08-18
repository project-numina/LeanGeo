import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Given triangle $ABC$ the point $J$ is the centre of the excircle opposite the vertex $A$. This excircle is tangent to the side $BC$ at $M$, and to the lines $AB$ and $AC$ at $K$ and $L$, respectively. The lines $LM$ and $BJ$ meet at $F$, and the lines $KM$ and $CJ$ meet at $G$. Let $S$ be the point of intersection of the lines $AF$ and $BC$, and let $T$ be the point of intersection of the lines $AG$ and $BC$. Prove that $M$ is the midpoint of $ST$. (The excircle of $ABC$ opposite the vertex $A$ is the circle that is tangent to the line segment $BC$, to the ray $AB$ beyond $B$, and to the ray $AC$ beyond $C$.)
theorem IMO_2012_P1 :
  ∀ (A B C J K L M F G S T : Point)
    (AB BC CA LM BJ KM CJ AF AG : Line)
    (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    exCentre J A B C ∧
    J.isCentre Ω ∧
    tangentAtPoint M J BC Ω ∧
    tangentAtPoint K J AB Ω ∧
    tangentAtPoint L J AC Ω ∧
    distinctPointsOnLine L M LM ∧
    distinctPointsOnLine B J BJ ∧
    F.onLine LM ∧
    F.onLine BJ ∧
    distinctPointsOnLine K M KM ∧
    distinctPointsOnLine C J CJ ∧
    G.onLine KM ∧
    G.onLine CJ ∧
    distinctPointsOnLine A F AF ∧
    S.onLine AF ∧
    S.onLine BC ∧
    distinctPointsOnLine A G AG ∧
    T.onLine AG ∧
    T.onLine BC
    → midpoint S M T := by
  sorry