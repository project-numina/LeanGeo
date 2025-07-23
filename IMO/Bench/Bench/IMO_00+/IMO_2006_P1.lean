import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be Triangle with incenter $I$. A point $P$ in the interior of the Triangle satisfies\[\angle PBA+\angle PCA = \angle PBC+\angle PCB.\]Show that $AP \geq AI$, and that equality holds if and only if $P=I$.
theorem IMO_2006_P1 :
  ∀ (A B C I P : Point) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    Incentre I A B C ∧
    InsideTriangle P A B C AB BC CA ∧
    ∠ P:B:A + ∠ P:C:A = ∠ P:B:C + ∠ P:C:B →
    |(A─P)| ≥ |(A─I)| ∧ (|(A─P)| = |(A─I)| ↔ P = I) := by
  sorry
