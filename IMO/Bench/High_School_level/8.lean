import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--9.1. On the diagonal $B D$ of parallelogram $A B C D$, a point $K$ is taken. Line $A K$ intersects lines $C D$ and $B C$ at points $L$ and $M$ respectively. Prove that $A K^{2}=K L \cdot K M$.-/
theorem Numina_Geometry_1339 :
  ∀ (A B C D K L M : Point)
    (AB BC CD DA BD AK : Line),
    parallelogram A B C D AB BC CD DA ∧
    distinctPointsOnLine B D BD ∧
    distinctPointsOnLine A K AK ∧
    between B K D ∧
    twoLinesIntersectAtPoint AK CD L ∧
    twoLinesIntersectAtPoint AK BC M
  → |(A─K)| * |(A─K)| = |(K─L)| * |(K─M)| := by
  sorry
