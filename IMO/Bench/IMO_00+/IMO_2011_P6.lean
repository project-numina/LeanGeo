import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute triangle with circumcircle $\Gamma$. Let $\ell$ be a tangent line to $\Gamma$, and let $\ell_a, \ell_b$ and $\ell_c$ be the lines obtained by reflecting $\ell$ in the lines $BC$, $CA$ and $AB$, respectively. Show that the circumcircle of the triangle determined by the lines $\ell_a, \ell_b$ and $\ell_c$ is tangent to the circle $\Gamma$.
theorem IMO_2011_P6 :
  ∀ (A B C A' B' C' P O : Point) (ℓ ℓ_a ℓ_b ℓ_c : Line) (Γ Δ : Circle),
    acuteTriangle A B C ∧
    circumCircle Γ A B C ∧
    O.isCentre Γ ∧
    tangentAtPoint P O ℓ Γ ∧
    reflectLine ℓ BC ℓ_a ∧
    reflectLine ℓ CA ℓ_b ∧
    reflectLine ℓ AB ℓ_c ∧
    twoLinesIntersectAtPoint ℓ_b ℓ_c A' ∧
    twoLinesIntersectAtPoint ℓ_c ℓ_a B' ∧
    twoLinesIntersectAtPoint ℓ_a ℓ_b C' ∧
    circumCircle Δ A' B' C' →
    tangentCircles Γ Δ := by
  sorry
