import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute Triangle with circumcircle $\Gamma$. Let $\ell$ be a tangent line to $\Gamma$, and let $\ell_a, \ell_b$ and $\ell_c$ be the lines obtained by reflecting $\ell$ in the lines $BC$, $CA$ and $AB$, respectively. Show that the circumcircle of the Triangle determined by the lines $\ell_a, \ell_b$ and $\ell_c$ is tangent to the circle $\Gamma$.
theorem IMO_2011_P6 :
  ∀ (A B C A' B' C' P O : Point) (l la lb lc AB BC CA: Line) (Γ Δ : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    Circumcircle Γ A B C ∧
    O.isCentre Γ ∧
    TangentLineCircleAtPoint P O l Γ ∧
    TwoLinesIntersectAtPoint l AB X ∧
    TwoLinesIntersectAtPoint l BC Y ∧
    TwoLinesIntersectAtPoint l CA Z ∧
    (∀ (M: Point), M.onLine lc ∧ M ≠ X → (∠M:X:B = ∠ B:X:P ∨ ∠M:X:B + ∠B:X:P = ∟ + ∟)) ∧
    (∀ (M: Point), M.onLine la ∧ M ≠ Y → (∠M:Y:C = ∠ C:Y:P ∨ ∠M:Y:C + ∠C:Y:P = ∟ + ∟)) ∧
    (∀ (M: Point), M.onLine lb ∧ M ≠ Z → (∠M:Z:A = ∠ A:Z:P ∨ ∠M:Z:A + ∠A:Z:P = ∟ + ∟)) ∧
    TwoLinesIntersectAtPoint lb lc A' ∧
    TwoLinesIntersectAtPoint lc la B' ∧
    TwoLinesIntersectAtPoint la lb C' ∧
    Circumcircle Δ A' B' C' →
    ∃!(P: Point), P.onCircle Δ ∧ P.onCircle Γ := by
  sorry
