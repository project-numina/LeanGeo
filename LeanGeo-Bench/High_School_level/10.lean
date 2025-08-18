import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--XLIII OM - III - Problem 1

Segments $ AC $ and $ BD $ intersect at point $ P $, such that $ |PA|=|PD| $, $ |PB|=|PC| $. Let $ O $ be the center of the circumcircle of Triangle $ PAB $. Prove that the lines $ OP $ and $ CD $ are perpendicular.-/
theorem Numina_Geometry_478 : ∀ (A B C D P O : Point),
Triangle P A B ∧
between A P C ∧
between B P D ∧
|(P─A)| = |(P─D)| ∧
|(P─B)| = |(P─C)| ∧
Circumcentre O P A B →
PerpFourPoints O P C D := by
  sorry
