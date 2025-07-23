import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be a Triangle with $\angle BAC = 60^{\circ}$. Let $AP$ bisect $\angle BAC$ and let $BQ$ bisect $\angle ABC$, with $P$ on $BC$ and $Q$ on $AC$. If $AB + BP = AQ + QB$, what are the angles of the triangle?
theorem IMO_2001_P5 :
  ∀ (A B C P Q : Point) (AB BC CA AP BQ : Line),
    formTriangle A B C AB BC CA ∧
    ∠ B:A:C = 2/3 * ∟ ∧
    distinctPointsOnLine A P AP ∧ P.onLine BC ∧ ∠ B:A:P = ∠ P:A:C ∧
    distinctPointsOnLine B Q BQ ∧ Q.onLine CA ∧ ∠ A:B:Q = ∠ Q:B:C ∧
    |(A─B)| + |(B─P)| = |(A─Q)| + |(Q─B)| →
    ∠ A:B:C = 8/9 * ∟ ∧ ∠ B:C:A = 4/9 * ∟ := by
  sorry
