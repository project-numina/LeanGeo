import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

-- A circle has center on the side AB of the Cyclic quadrilateral ABCD. The other three sides are tangent to the circle. Prove that AD + BC = AB.
theorem IMO1985_1 :
  ∀ (A B C D K : Point) (Ω ω : Circle) (AB BC CD DA : Line),
    CyclicQuadrilateral A B C D AB BC CD DA Ω ∧
    K.onLine AB ∧
    K.isCentre ω ∧
    TangentLineCircle BC ω ∧
    TangentLineCircle CD ω ∧
    TangentLineCircle DA ω →
    |(A─D)| + |(B─C)| = |(A─B)| := by
  sorry
