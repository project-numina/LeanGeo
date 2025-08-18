import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABCD$ be a convex quadrilateral with $BA≠ BC$. Denote the incircles of triangles $ABC$ and $ADC$ by $\omega_{1}$ and $\omega_{2}$ respectively. Suppose that there exists a circle $\omega$ tangent to ray $BA$ beyond $A$ and to the ray $BC$ beyond $C$, which is also tangent to the lines $AD$ and $CD$. Prove that the common external tangents to $\omega_{1}$ and $\omega_{2}$ intersect on $\omega$.
theorem IMO_2008_P6 :
  ∀ (A B C D X: Point) (AB BC CD DA CA l₁ l₂: Line) (ω₁ ω₂ ω : Circle),
    formQuadrilateral A B C D AB BC CD DA ∧ ¬ (|(A─B)| = |(B─C)|) ∧
    Incircle ω₁ A B C AB BC CA ∧ Incircle ω₂ C D A CD DA CA ∧
    TangentLineCircle AB ω ∧ TangentLineCircle BC ω ∧ TangentLineCircle DA ω ∧ TangentLineCircle CD ω ∧
    TangentLineCircle l₁ ω₁ ∧ TangentLineCircle l₁ ω₂ ∧ TangentLineCircle l₂ ω₁ ∧ TangentLineCircle l₂ ω₂ ∧
    TwoLinesIntersectAtPoint l₁ l₂ X →  X.onCircle ω := by
  sorry
