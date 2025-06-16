import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem day158: (A B C M T E F : Point) (Ω : Circle) triangle A B C ∧ midpoint B M C ∧ between B T C ∧ ∠T:A:B = ∠T:A:C  ∧ T.onCircle Ω ∧ M.onCircle Ω ∧
