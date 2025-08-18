import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--The circle $S$ has centre $O$, and $BC$ is a diameter of $S$. Let $A$ be a point of $S$ such that $\angle AOB<120{{}^\circ}$. Let $D$ be the midpoint of the arc $AB$ which does not contain $C$. The line through $O$ parallel to $DA$ meets the line $AC$ at $I$. The perpendicular bisector of $OA$ meets $S$ at $E$ and at $F$. Prove that $I$ is the incentre of the triangle $CEF$.
theorem IMO_2002_P2 :
  ∀ (A B C D E F I O : Point) (S : Circle) (DA AC L1 L2 : Line),
    O.isCentre S ∧
    B.onCircle S ∧ C.onCircle S ∧ A.onCircle S ∧
    diameter B C O S ∧
    ∠ A:O:B < 4 / 3 * ∟ ∧
    D.onCircle S ∧
    ∠ A:O:D = ∠ D:O:B ∧
    distinctPointsOnLine D A DA ∧
    distinctPointsOnLine A C AC ∧
    O.onLine L1 ∧ ¬ L1.intersectsLine DA ∧ twoLinesIntersectAtPoint L1 AC I ∧
    perpBisector O A L2 ∧
    E.onLine L2 ∧ E.onCircle S ∧
    F.onLine L2 ∧ F.onCircle S →
  inCentre I C E F := by
  sorry
