import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--9.4. In Triangle $ABC$, $\angle ABC = 2 \angle ACB$, $K$ is the MidPoint of side $BC$, and $AE$ is the altitude. Prove that $AB = 2EK$.-/
theorem Numina_Geometry_1200 :
  ∀ (A B C K E : Point),
  formTriangle A B C AB BC CA ∧
  MidPoint B K C ∧
  Foot A E BC ∧
  ∠ A:B:C = ∠ A:C:B + ∠ A:C:B
    → |(A─B)| = |(E─K)| + |(E─K)| := by
  sorry
