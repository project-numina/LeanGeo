import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $P$ and $Q$ be on segment $BC$ of an acute triangle $ABC$ such that $\angle PAB=\angle BCA$ and $\angle CAQ=\angle ABC$. Let $M$ and $N$ be the points on $AP$ and $AQ$, respectively, such that $P$ is the midpoint of $AM$ and $Q$ is the midpoint of $AN$. Prove that the intersection of $BM$ and $CN$ is on the circumference of triangle $ABC$.
theorem IMO_2014_P4 :
  ∀ (A B C P Q M N X : Point) (AB BC CA BM CN : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    between B P C ∧ between B Q C ∧
    ∠ P:A:B = ∠ B:C:A ∧ ∠ C:A:Q = ∠ A:B:C ∧
    midpoint A P M ∧ midpoint A Q N ∧
    distinctPointsOnLine B M BM ∧ distinctPointsOnLine C N CN ∧
    twoLinesIntersectAtPoint BM CN X ∧
    circumCircle Ω A B C
    → X.onCircle Ω := by
  sorry