import SystemE
import LeanGeo

namespace LeanGeo
--Example 1.1. In quadrilateral W X Y Z with perpendicular diagonals (as in Figure 1.1A), we are given ∠W Z X = 30°, ∠X W Y = 40°, and ∠W Y Z = 50°.
-- (a) Compute ∠Z.
-- (b) Compute ∠X.
theorem Example_1_1 :
  ∀ (W X Y Z : Point) (WX XY YZ ZW WY XZ : Line),
    (formQuadrilateral W X Y Z WX XY YZ ZW)
    ∧ (distinctPointsOnLine W Y WY)
    ∧ (distinctPointsOnLine X Z XZ)
    ∧ (perpLine XZ WY)
    ∧ (∠ W:Z:X = ∟/3)
    ∧ (∠ X:W:Y = ∟ * 4/9)
    ∧ (∠ W:Y:Z = ∟ * 5/9)
    → (∠ Y:Z:W = ∟ * 7/9) := by
  euclid_intros
  euclid_apply intersection_lines XZ WY as P
  --euclid_assert ∠Z:P:Y = ∟
  --euclid_assert triangle P Y Z
  euclid_apply triangle_angleSum P Y Z
  --euclid_assert ∠Y:Z:P = 4/9 * ∟
  euclid_finish

theorem Example_1_1a :
  ∀ (W X Y Z : Point) (WX XY YZ ZW WY XZ : Line),
    (formQuadrilateral W X Y Z WX XY YZ ZW)
    ∧ (distinctPointsOnLine W Y WY)
    ∧ (distinctPointsOnLine X Z XZ)
    ∧ (perpLine XZ WY)
    ∧ (∠ W:Z:X = ∟/3)
    ∧ (∠ X:W:Y = ∟ * 4/9)
    ∧ (∠ W:Y:Z = ∟ * 5/9)
    → (∠ W:Z:Y = ∟ * 7/9) := by
  euclid_intros
  euclid_apply intersection_lines XZ WY as P
  --euclid_assert ∠Z:P:Y = ∟
  --euclid_assert triangle P Y Z
  euclid_apply triangle_angleSum P Y Z
  --euclid_assert ∠Y:Z:P = 4/9 * ∟
  euclid_finish

theorem Example_1_1b :
  ∀ (W X Y Z : Point) (WX XY YZ ZW WY XZ : Line),
    (formQuadrilateral W X Y Z WX XY YZ ZW)
    ∧ (distinctPointsOnLine W Y WY)
    ∧ (distinctPointsOnLine X Z XZ)
    ∧ (perpLine XZ WY)
    ∧ (∠ W:Z:X = ∟/3)
    ∧ (∠ X:W:Y = ∟ * 4/9)
    ∧ (∠ W:Y:Z = ∟ * 5/9)
    → (∠ W:X:Y = ∟ * 11/9) := by
  euclid_intros
  euclid_apply intersection_lines XZ WY as P
  --euclid_assert ∠Z:P:Y = ∟
  --euclid_assert triangle P Y Z
  euclid_apply triangle_angleSum P Y Z
  euclid_assert (△Y:P:Z).similar_test (△X:P:W)
  euclid_apply  (△Y:P:Z).similar_property (△X:P:W)
  --euclid_assert ∠X:P:Y = ∠Z:P:W
  --euclid_assert triangle W P Z
  --euclid_assert triangle X P Y
  --euclid_assert |(P─X)| * |(P─Y)| = |(P─Y)| * |(P─X)|
  --euclid_assert ∠W:P:Z = ∠X:P:Y
  --euclid_assert (△W:P:Z).similar_test (△X:P:Y)
  euclid_apply (△W:P:Z).similar_property (△X:P:Y)
  euclid_apply triangle_angleSum P X Y
  euclid_apply triangle_angleSum P X W
  --euclid_apply angle_between_transfer X P Z W
  --euclid_assert ∠ W:Z:P = ∟ / 3
  --euclid_apply angle_between_transfer Y P W X
  --euclid_assert ∠P:X:W = ∟ *5 / 9
  --euclid_assert ∠P:Y:X = ∟ * 3 / 9
  --euclid_assert ∠P:X:Y = 2 * 3 / ∟
  --euclid_assert ∠Y:Z:P = 4/9 * ∟
  euclid_finish
