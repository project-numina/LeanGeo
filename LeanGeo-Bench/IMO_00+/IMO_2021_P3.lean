import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $D$ be an interior point of the acute Triangle $ABC$ with $AB > AC$ so that $\angle DAB = \angle CAD.$ The point $E$ on the segment $AC$ satisfies $\angle ADE =\angle BCD,$ the point $F$ on the segment $AB$ satisfies $\angle FDA =\angle DBC,$ and the point $X$ on the line $AC$ satisfies $CX = BX.$ Let $O_1$ and $O_2$ be the circumcenters of the triangles $ADC$ and $EXD,$ respectively. Prove that the lines $BC, EF,$ and $O_1O_2$ are concurrent.
theorem IMO_2021_P3 :
  ∀ (A B C D E F X O1 O2 : Point) (AB BC CA EF L12 : Line),
    formAcuteTriangle A B C AB BC CA ∧
    InsideTriangle D A B C AB BC CA ∧
    |(A─B)| > |(A─C)| ∧
    ∠ D:A:B = ∠ C:A:D ∧
    between A E C ∧
    ∠ A:D:E = ∠ B:C:D ∧
    between A F B ∧
    ∠ F:D:A = ∠ D:B:C ∧
    X.onLine CA ∧
    |(C─X)| = |(B─X)| ∧
    Circumcentre O1 A D C ∧
    Circumcentre O2 E X D ∧
    distinctPointsOnLine E F EF ∧
    distinctPointsOnLine O1 O2 L12 →
    Concurrent BC EF L12 := by sorry
