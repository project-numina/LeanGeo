import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Triangle $A B C$ has perimeter 4. Points $X$ and $Y$ lie on rays $A B$ and $A C$, respectively, such that $A X=A Y=1$. Segments $B C$ and $X Y$ intersect at point $M$. Prove that the perimeter of either $\triangle A B M$ or $	riangle A C M$ is 2.
theorem Russian_Olympiad_2010 :
  ∀ (A B C X Y M : Point) (AB BC CA XY : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| + |(B─C)| + |(C─A)| = 4 ∧
    X.onLine AB ∧ Y.onLine AC ∧ |(A─X)| = 1 ∧ |(A─Y)| = 1 ∧
    distinctPointsOnLine X Y XY ∧
    M.onLine BC ∧ M.onLine XY
    → (|(A─B)| + |(B─M)| + |(M─A)| = 2) ∨ (|(A─C)| + |(C─M)| + |(M─A)| = 2) := by
  sorry
