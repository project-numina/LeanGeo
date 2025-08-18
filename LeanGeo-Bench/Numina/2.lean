import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--9.3. Given $\triangle A B C$. Points $M$ and $N$ are taken on sides $A B$ and $B C$ respectively. It is known that $M N \| A C$ and $B N=1, M N=2, A M=3$. Prove that $A C&gt;4$.-/
theorem Numina_Geometry_1633 :
  ∀ (A B C M N : Point),
    Triangle A B C ∧
    between A M B ∧
    between B N C ∧
    distinctPointsOnLine M N MN ∧
    distinctPointsOnLine A C AC ∧
    ¬ MN.intersectsLine AC ∧
    |(B─N)| = 1 ∧
    |(M─N)| = 2 ∧
    |(A─M)| = 3 →
    |(A─C)| > 4 := by
  sorry
