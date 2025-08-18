import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--3. In rhombus $A B C D$, points $E$ and $F$ are the midpoints of sides $A B$ and $B C$ respectively. Point $P$ is such that $P A=P F, P E=P C$. Prove that point $P$ lies on line $B D$.-/
theorem Numina_Geometry_856 :
  ∀ (A B C D E F P : Point) (AB BC CD DA : Line),
    (parallelogram A B C D AB BC CD DA) ∧
    |(A─B)| = |(B─C)| ∧
    |(B─C)| = |(C─D)| ∧
    |(C─D)| = |(D─A)| ∧
    midpoint A E B ∧
    midpoint B F C ∧
    |(P─A)| = |(P─F)| ∧
    |(P─E)| = |(P─C)|
    → coll B D P := by
  sorry
