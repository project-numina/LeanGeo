import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--As shown in the figure, in an isosceles Triangle $ABC$ with $AB = BC$, $I$ is the incenter, $M$ is the MidPoint of $BI$, $P$ is a point on side $AC$ such that $AP = 3PC$, and $PI$ is extended to a point $H$ such that $MH \perp PH$. $Q$ is the MidPoint of $AB$ on the circumcircle of $\triangle ABC$. Prove: $BH \perp QH$.-\/
theorem problem_CO20 :
∀ (A B C I M P H Q : Point) (AB BC CA PH MH BH QH: Line),
  formTriangle A B C AB BC CA ∧
  |(A─B)| = |(B─C)| ∧
  Incentre I A B C ∧
  MidPoint B M I ∧
  between A P C  ∧
  (|(A─P)| = 3 * |(P─C)|) ∧
  between P I H ∧
  distinctPointsOnLine P H PH ∧
  distinctPointsOnLine M H MH ∧
  distinctPointsOnLine B H BH ∧
  distinctPointsOnLine Q H QH ∧
  PerpLine PH MH ∧
  Cyclic Q B C A ∧
  |(A─Q)| = |(B─Q)| ∧
  Q.opposingSides C AB
  → PerpLine BH QH :=
by
  sorry
