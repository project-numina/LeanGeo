import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--3. In Rhombus $A B C D$, points $E$ and $F$ are the midpoints of sides $A B$ and $B C$ respectively. Point $P$ is such that $P A=P F, P E=P C$. Prove that point $P$ lies on line $B D$.-/
theorem Numina_Geometry_856 :
  ∀ (A B C D E F P : Point) (AB BC CD DA : Line),
    Rhombus A B C D AB BC CD DA ∧
    MidPoint A E B ∧
    MidPoint B F C ∧
    |(P─A)| = |(P─F)| ∧
    |(P─E)| = |(P─C)|
    → Coll B D P := by
  sorry
