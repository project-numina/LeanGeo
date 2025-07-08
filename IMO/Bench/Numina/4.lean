import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--9.4. In triangle $ABC$, $\angle ABC = 2 \angle ACB$, $K$ is the midpoint of side $BC$, and $AE$ is the altitude. Prove that $AB = 2EK$.-/
theorem Numina_Geometry_1200 :
  ∀ (A B C K E : Point),
  formTriangle A B C AB BC CA ∧
  midpoint B K C ∧
  foot A E BC ∧
  ∠ A:B:C = ∠ A:C:B + ∠ A:C:B
    → |(A─B)| = |(E─K)| + |(E─K)| := by
  sorry
