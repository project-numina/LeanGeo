import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
/--6. (30 points) $S M$ is the angle bisector in triangle $S Q T$. Point $O$ on side $S T$ is such that angle $O Q T$ is equal to the sum of angles $Q T S$ and $Q S T$. Prove that $O M$ is the angle bisector of angle $Q O T$.

![](https://cdn.mathpix.com/cropped/2024_05_06_e07f284b5d5a13e50986g-4.jpg?height=579&amp;width=674&amp;top_left_y=453&amp;top_left_x=682)-/
theorem Numina_Geometry_705 :
  ∀ (S M Q T O : Point),
    triangle S Q T ∧
    coll Q T M ∧
    (∠ Q:S:M = ∠ M:S:T) ∧
    between S O T ∧
    (∠ O:Q:T = ∠ Q:T:S + ∠ Q:S:T)
    → ∠ Q:O:M = ∠ M:O:T := by
  sorry
