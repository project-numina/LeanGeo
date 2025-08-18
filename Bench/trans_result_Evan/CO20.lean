import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--As shown in the figure, in an isosceles triangle $ABC$ with $AB = BC$, $I$ is the incenter, $M$ is the midpoint of $BI$, $P$ is a point on side $AC$ such that $AP = 3PC$, and $PI$ is extended to a point $H$ such that $MH \perp PH$. $Q$ is the midpoint of $AB$ on the circumcircle of $\triangle ABC$. Prove: $BH \perp QH$.-\/
theorem problem_CO20 :
∀ (A B C I M P H Q : Point) (AB BC CA PH MH BH QH: Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(B─C)| ∧
  inCentre I A B C ∧
  midpoint B M I ∧
  between A P C  ∧
  (|(A─P)| = 3 * |(P─C)|) ∧
  between P I H ∧
  distinctPointsOnLine P H PH ∧
  distinctPointsOnLine M H MH ∧
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine Q H QH ∧
  perpLine PH MH ∧
  cyclic Q B C A ∧
  |(A─Q)| = |(B─Q)|
  → perpLine BH QH :=
by
  sorry
