import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be a triangle with $\angle BCA=90^{\circ}$, and let $D$ be the foot of the altitude from $C$. Let $X$ be a point in the interior of the segment $CD$. Let $K$ be the point on the segment $AX$ such that $BK=BC$. Similarly, let $L$ be the point on the segment $BX$ such that $AL=AC$. Let $M$ be the point of intersection of $AL$ and $BK$. Show that $MK=ML$.
theorem IMO_2012_P5 :
  ∀ (A B C D X K L M : Point) (AB BC CA AL BK : Line),
    formTriangle A B C AB BC CA ∧ ∠ B:C:A = ∟ ∧ foot C D AB ∧
    between C X D ∧ between A K X ∧ |(B─K)| = |(B─C)| ∧
    between B L X ∧ |(A─L)| = |(A─C)| ∧
    distinctPointsOnLine A L AL ∧ distinctPointsOnLine B K BK ∧
    M.onLine AL ∧ M.onLine BK →
    |(M─K)| = |(M─L)| := by
  sorry