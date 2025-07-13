import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Consider the convex quadrilateral $ABCD$. The point $P$ is in the interior of $ABCD$. The following ratio equalities hold: \[\angle PAD:\angle PBA:\angle DPA=1:2:3=\angle CBP:\angle BAP:\angle BPC\]Prove that the following three lines meet in a point: the internal bisectors of angles $\angle ADP$ and $\angle PCB$ and the perpendicular bisector of segment $AB$.
theorem IMO_2020_P1 :
  ∀ (A B C D P : Point) (AB BC CD DA l1 l2 l3 : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    insideQuadrilateral P A B C D AB BC CD DA ∧
    ∠ P:B:A = 2 * ∠ P:A:D ∧
    ∠ D:P:A = 3 * ∠ P:A:D ∧
    ∠ B:A:P = 2 * ∠ C:B:P ∧
    ∠ B:P:C = 3 * ∠ C:B:P ∧
    D.onLine l1 ∧
    (∀ (X : Point), X.onLine l1 → ∠ A:D:X = ∠ P:D:X) ∧
    A.opposingSides P l1 ∧
    C.onLine l2 ∧
    (∀ (X : Point), X.onLine l2 → ∠ P:C:X = ∠ B:C:X) ∧
    P.opposingSides B l2 ∧
    perpBisector A B l3 →
  concurrent l1 l2 l3 := by
  sorry