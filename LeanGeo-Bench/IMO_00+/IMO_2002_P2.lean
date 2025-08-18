import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--The circle $S$ has centre $O$, and $BC$ is a Diameter of $S$. Let $A$ be a point of $S$ such that $\angle AOB<120{{}^\circ}$. Let $D$ be the MidPoint of the arc $AB$ which does not contain $C$. The line through $O$ parallel to $DA$ meets the line $AC$ at $I$. The perpendicular bisector of $OA$ meets $S$ at $E$ and at $F$. Prove that $I$ is the incentre of the Triangle $CEF$.
theorem IMO_2002_P2 :
  ∀ (A B C D E F I O : Point) (S : Circle) (AB DA AC L1 L2 : Line),
    O.isCentre S ∧
    B.onCircle S ∧ C.onCircle S ∧ A.onCircle S ∧
    Diameter B C O S ∧
    ∠ A:O:B < 4 / 3 * ∟ ∧
    D.onCircle S ∧
    ∠ A:O:D = ∠ D:O:B ∧
    distinctPointsOnLine A B AB ∧
    D.opposingSides C AB ∧
    distinctPointsOnLine D A DA ∧
    distinctPointsOnLine A C AC ∧
    O.onLine L1 ∧ ¬ L1.intersectsLine DA ∧ TwoLinesIntersectAtPoint L1 AC I ∧
    PerpBisector O A L2 ∧
    E.onLine L2 ∧ E.onCircle S ∧
    F.onLine L2 ∧ F.onCircle S →
  Incentre I C E F := by
  sorry
