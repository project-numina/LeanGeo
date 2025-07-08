import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $A, B, C, D$ be four distinct points on a line, in that order. The circles with diameters $\overline{A C}$ and $\overline{B D}$ intersect at $X$ and $Y$. The line $X Y$ meets $\overline{B C}$ at $Z$. Let $P$ be a point on the line $X Y$ other than $Z$. The line $C P$ intersects the circle with diameter $A C$ at $C$ and $M$, and the line $B P$ intersects the circle with diameter $B D$ at $B$ and $N$. Prove that the lines $A M, D N, X Y$ are concurrent.
theorem IMO_1995_1 :
  ∀ (A B C D X Y Z P M N O₁ O₂ : Point) (L LXY L_AM L_DN : Line) (C₁ C₂ : Circle),
    distinctPointsOnLine A B L ∧ C.onLine L ∧ D.onLine L ∧ between A B C ∧ between B C D ∧
    midpoint A O₁ C ∧ O₁.isCentre C₁ ∧ A.onCircle C₁ ∧ C.onCircle C₁ ∧
    midpoint B O₂ D ∧ O₂.isCentre C₂ ∧ B.onCircle C₂ ∧ D.onCircle C₂ ∧
    circlesIntersectsAtTwoPoints C₁ C₂ X Y ∧ distinctPointsOnLine X Y LXY ∧
    Z.onLine LXY ∧ between B Z C ∧ P.onLine LXY ∧ P ≠ Z ∧
    coll C P M ∧ M.onCircle C₁ ∧ M ≠ C ∧
    coll B P N ∧ N.onCircle C₂ ∧ N ≠ B ∧
    distinctPointsOnLine A M L_AM ∧ distinctPointsOnLine D N L_DN →
    concurrent L_AM L_DN LXY := by
  sorry
