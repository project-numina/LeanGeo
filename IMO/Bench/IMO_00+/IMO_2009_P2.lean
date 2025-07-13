import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be a triangle with circumcentre $O$. The points $P$ and $Q$ are interior points of the sides $CA$ and $AB$ respectively. Let $K,L$ and $M$ be the midpoints of the segments $BP,CQ$ and $PQ$. respectively, and let $\Gamma$ be the circle passing through $K,L$ and $M$. Suppose that the line $PQ$ is tangent to the circle $\Gamma$. Prove that $OP = OQ$.
theorem IMO_2009_P2 :
  ∀ (A B C O P Q K L M OΓ : Point) (AB BC CA PQ : Line) (Γ : Circle),
    formTriangle A B C AB BC CA ∧
    circumCentre O A B C ∧
    P.onLine CA ∧ between C P A ∧
    Q.onLine AB ∧ between A Q B ∧
    midpoint B K P ∧
    midpoint C L Q ∧
    midpoint P M Q ∧
    circumCircle Γ K L M ∧
    tangentAtPoint M OΓ PQ Γ →
    |(O─P)| = |(O─Q)| := by
  sorry