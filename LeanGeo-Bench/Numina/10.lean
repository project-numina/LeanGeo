import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--7.2. In Triangle $ABC$, the point of intersection of the medians is equidistant from all three vertices. Prove that Triangle $ABC$ is equilateral.-/
theorem Numina_Geometry_1652 :
  ∀ (A B C D E G : Point) (AD BE : Line),
    Triangle A B C ∧
    MidPoint B D C ∧
    MidPoint A E C ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B E BE ∧
    TwoLinesIntersectAtPoint AD BE G ∧
    |(A─G)| = |(B─G)| ∧
    |(B─G)| = |(C─G)|
    → |(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─A)| := by
  sorry
