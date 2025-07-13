import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--7.2. In triangle $ABC$, the point of intersection of the medians is equidistant from all three vertices. Prove that triangle $ABC$ is equilateral.-/
theorem Numina_Geometry_1652 :
  ∀ (A B C D E G : Point) (AD BE : Line),
    triangle A B C ∧
    midpoint B D C ∧
    midpoint A E C ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B E BE ∧
    twoLinesIntersectAtPoint AD BE G ∧
    |(A─G)| = |(B─G)| ∧
    |(B─G)| = |(C─G)|
    → |(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─A)| := by
  sorry
