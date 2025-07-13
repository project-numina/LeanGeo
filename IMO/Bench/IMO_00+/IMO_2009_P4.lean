import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be a triangle with $AB = AC$. The angle bisectors of $\angle CAB$ and $\angle ABC$ meet the sides $BC$ and $CA$ at $D$ and $E$, respectively. Let $K$ be the incentre of triangle $ADC$. Suppose that $\angle BEK = 45^\circ$. Find all possible values of $\angle CAB$.
theorem IMO_2009_P4 :
  ∀ (A B C D E K : Point) (AB BC CA AD DC : Line),
    formTriangle A B C AB BC CA ∧ |(A─B)| = |(A─C)| ∧
    between B D C ∧ ∠ C:A:D = ∠ D:A:B ∧
    between C E A ∧ ∠ A:B:E = ∠ E:B:C ∧
    formTriangle A D C AD DC CA ∧ inCentre K A D C ∧
    ∠ B:E:K = ∟/2 →
    (∠ C:A:B = ∟) ∨ (∠ C:A:B = 2/3 * ∟) := by
  sorry