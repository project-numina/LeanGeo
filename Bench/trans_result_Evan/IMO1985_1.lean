import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

-- A circle has center on the side AB of the cyclic quadrilateral ABCD. The other three sides are tangent to the circle. Prove that AD + BC = AB.
theorem IMO1985_1 :
  ∀ (A B C D K : Point) (Ω ω : Circle) (AB BC CD DA : Line),
    cyclicQuadrilateral A B C D AB BC CD DA Ω ∧
    K.onLine AB ∧
    K.isCentre ω ∧
    tangentLine BC ω ∧
    tangentLine CD ω ∧
    tangentLine DA ω →
    |(A─D)| + |(B─C)| = |(A─B)| := by
  sorry