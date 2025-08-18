import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo


--In quadrilateral $ABCD$, $AE \perp BD$ at point $E$, $CF \perp BD$ at point $F$, and point $P$ is the MidPoint of $AC$. Prove that $PE = PF$.
theorem problem_MP19 :
∀ (A B C D E F P : Point)
  (AB BC CD DA BD AE CF AC : Line),
  formQuadrilateral A B C D AB BC CD DA ∧
  distinctPointsOnLine B D BD ∧
  distinctPointsOnLine A E AE ∧
  Foot A E BD ∧
  Foot C F BD ∧
  distinctPointsOnLine A C AC ∧
  MidPoint A P C
→ |(P─E)| = |(P─F)| :=
by
  sorry
