import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--Given that in $\triangle ABC$, $O$ is the circumcenter, and $I$ is the incenter. Line $OI$ is perpendicular to line $AI$. Prove that $AB + AC = 2BC$.-/
theorem problem_HP97 :
  ∀ (A B C O I : Point) (AB BC CA OI AI : Line),
  formTriangle A B C AB BC CA ∧
  circumCentre O A B C ∧
  inCentre I A B C ∧
  distinctPointsOnLine O I OI ∧
  distinctPointsOnLine A I AI ∧
  perpLine OI AI
  → (|(A─B)| + |(A─C)|) = (|(B─C)| + |(B─C)|) := by
  sorry
