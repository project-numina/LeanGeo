import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Convex quadrilateral $ABCD$ has $\angle ABC = \angle CDA = 90^{\circ}$. Point $H$ is the foot of the perpendicular from $A$ to $BD$. Points $S$ and $T$ lie on sides $AB$ and $AD$, respectively, such that $H$ lies inside triangle $SCT$ and\[\angle CHS - \angle CSB = 90^{\circ}, \quad \angle THC - \angle DTC = 90^{\circ}. \]Prove that line $BD$ is tangent to the circumcircle of triangle $TSH$.
theorem IMO_2014_P3 :
  ∀ (A B C D H S T O: Point)
    (AB BC CD DA BD SC CT ST: Line)
    (Ω: Circle),
    formQuadrilateral A B C D AB BC CD DA ∧
    ∠ A:B:C = ∟ ∧
    ∠ C:D:A = ∟ ∧
    foot A H BD ∧
    between A S B ∧
    between A T D ∧
    formTriangle S C T SC CT ST ∧
    insideTriangle H S C T SC CT ST ∧
    ∠ C:H:S = ∠ C:S:B + ∟ ∧
    ∠ T:H:C = ∠ D:T:C + ∟ ∧
    circumCircle Ω T S H ∧ circumCentre O T S H
    → (∃(P: Point), P.onLine BD ∧ tangentAtPoint H O BD Ω) := by
  sorry
