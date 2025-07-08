import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--A convex quadrilateral $ABCD$ satisfies $AB\cdot CD = BC\cdot DA$. Point $X$ lies inside $ABCD$ so that\[\angle{XAB} = \angle{XCD}\quad\,\,	ext{and}\quad\,\,\angle{XBC} = \angle{XDA}.\]Prove that $\angle{BXA} + \angle{DXC} = 180^\circ$
theorem IMO_2018_P6 :
  ∀ (A B C D X : Point) (AB BC CD DA : Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(A─B)| * |(C─D)| = |(B─C)| * |(D─A)| ∧
    insideQuadrilateral X A B C D AB BC CD DA ∧
    ∠ X:A:B = ∠ X:C:D ∧
    ∠ X:B:C = ∠ X:D:A →
    ∠ B:X:A + ∠ D:X:C = ∟ + ∟ := by
  sorry