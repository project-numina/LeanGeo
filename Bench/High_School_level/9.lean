import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--II OM - I - Task 3

In a circle, two equal chords $ AB $ and $ AC $ and an arbitrary chord $ AD $ are drawn; the line $ AD $ intersects the line $ BC $ at point $ E $. Prove that the product $ AE \cdot AD $ does not depend on the position of point $ D $ on the circle, i.e., that $ AE \cdot AD = AC^2 $.-/
theorem Numina_Geometry_145 :
  ∀ (A B C D E : Point) (O : Circle) (AD BC : Line),
    (A.onCircle O) ∧
    (B.onCircle O) ∧
    (C.onCircle O) ∧
    (D.onCircle O) ∧
    (distinctPointsOnLine A D AD) ∧
    (distinctPointsOnLine B C BC) ∧
    (A ≠ B) ∧ (A ≠ C) ∧
    (twoLinesIntersectAtPoint AD BC E) ∧
    (|(A─B)| = |(A─C)|)
    → |(A─E)| * |(A─D)| = |(A─C)| * |(A─C)| := by
  sorry
