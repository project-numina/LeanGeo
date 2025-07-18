import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute triangle with circumcircle $\Gamma$. Let $\ell$ be a tangent line to $\Gamma$, and let $\ell_a, \ell_b$ and $\ell_c$ be the lines obtained by reflecting $\ell$ in the lines $BC$, $CA$ and $AB$, respectively. Show that the circumcircle of the triangle determined by the lines $\ell_a, \ell_b$ and $\ell_c$ is tangent to the circle $\Gamma$.
theorem IMO_2011_P6 :
  ∀ (A B C A' B' C' P O : Point) (l la lb lc AB BC CA: Line) (Γ Δ : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    circumCircle Γ A B C ∧
    O.isCentre Γ ∧
    tangentAtPoint P O l Γ ∧
    twoLinesIntersectAtPoint l AB X ∧
    twoLinesIntersectAtPoint l BC Y ∧
    twoLinesIntersectAtPoint l CA Z ∧
    (∀ (M: Point), M.onLine lc ∧ M ≠ X → (∠M:X:B = ∠ B:X:P ∨ ∠M:X:B + ∠B:X:P = ∟ + ∟)) ∧
    (∀ (M: Point), M.onLine la ∧ M ≠ Y → (∠M:Y:C = ∠ C:Y:P ∨ ∠M:Y:C + ∠C:Y:P = ∟ + ∟)) ∧
    (∀ (M: Point), M.onLine lb ∧ M ≠ Z → (∠M:Z:A = ∠ A:Z:P ∨ ∠M:Z:A + ∠A:Z:P = ∟ + ∟)) ∧
    twoLinesIntersectAtPoint lb lc A' ∧
    twoLinesIntersectAtPoint lc la B' ∧
    twoLinesIntersectAtPoint la lb C' ∧
    circumCircle Δ A' B' C' →
    ∃!(P: Point), P.onCircle Δ ∧ P.onCircle Γ := by
  sorry
