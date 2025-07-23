import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $P$ be a point interior to Triangle $ABC$ (with $CA ≠ CB$). The lines $AP$, $BP$ and $CP$ meet again its circumcircle $\Gamma$ at $K$, $L$, respectively $M$. The tangent line at $C$ to $\Gamma$ meets the line $AB$ at $S$. Show that from $SC = SP$ follows $MK = ML$.
theorem IMO_2010_P4 :
  ∀ (A B C P K L M S O : Point) (t : Line) (Γ : Circle) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    |(C─A)| ≠ |(C─B)| ∧
    InsideTriangle P A B C AB BC CA ∧
    O.isCentre Γ ∧
    Circumcircle Γ A B C ∧
    between A P K ∧
    between B P L ∧
    between C P M ∧
    K.onCircle Γ ∧
    L.onCircle Γ ∧
    M.onCircle Γ ∧
    TangentLineCircleAtPoint C O t Γ ∧
    S.onLine AB ∧
    S.onLine t ∧
    |(S─C)| = |(S─P)| →
    |(M─K)| = |(M─L)| := by
  sorry
