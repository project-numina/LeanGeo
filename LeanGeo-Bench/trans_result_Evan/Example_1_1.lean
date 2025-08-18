import Mathlib
import SystemE
import LeanGeo

namespace LeanGeo
--Example 1.1. In quadrilateral W X Y Z with perpendicular diagonals (as in Figure 1.1A), we are given ∠W Z X = 30°, ∠X W Y = 40°, and ∠W Y Z = 50°.
-- (a) Compute ∠Z.
-- (b) Compute ∠X.

theorem Example_1_1b :
  ∀ (W X Y Z : Point) (WX XY YZ ZW WY XZ : Line),
    (formQuadrilateral W X Y Z WX XY YZ ZW)
    ∧ (distinctPointsOnLine W Y WY)
    ∧ (distinctPointsOnLine X Z XZ)
    ∧ (PerpLine XZ WY)
    ∧ (∠ W:Z:X = ∟/3)
    ∧ (∠ X:W:Y = ∟ * 4/9)
    ∧ (∠ W:Y:Z = ∟ * 5/9)
    → (∠ W:X:Y = ∟ * 11/9) := by
  sorry
