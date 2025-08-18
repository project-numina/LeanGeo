import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--
In an isosceles Triangle $ABC$ with $|(A-B)| = |(A-C)|$, let $I$ be the incenter.
Prove that Triangle $IBC$ is also an isosceles triangle.
--/

theorem incenter_of_isosceles_triangle_is_isosceles :
  ∀ (A B C I : Point),
    IsoTriangle A B C ∧
    Incentre I A B C
    → IsoTriangle I B C := by
    sorry
