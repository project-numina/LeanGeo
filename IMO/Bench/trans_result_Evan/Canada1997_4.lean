import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--The point O is situated inside the parallelogram ABCD such that ∠AOB + ∠COD = 180◦. Prove that ∠OBC = ∠ODC
theorem Canada1997_4 :
  ∀ (A B C D O : Point) (AB BC CD DA : Line),
    parallelogram A B C D AB BC CD DA ∧
    insideQuadrilateral O A B C D AB BC CD DA ∧
    ∠ A:O:B + ∠ C:O:D = ∟ + ∟ →
    ∠ O:B:C = ∠ O:D:C := by
  sorry