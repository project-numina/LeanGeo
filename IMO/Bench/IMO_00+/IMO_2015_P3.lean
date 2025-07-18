import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute triangle with $AB > AC$. Let $\Gamma $ be its circumcircle, $H$ its orthocenter, and $F$ the foot of the altitude from $A$. Let $M$ be the midpoint of $BC$. Let $Q$ be the point on $\Gamma$ such that $\angle HQA = 90^{\circ}$ and let $K$ be the point on $\Gamma$ such that $\angle HKQ = 90^{\circ}$. Assume that the points $A$, $B$, $C$, $K$ and $Q$ are all different and lie on $\Gamma$ in this order. Prove that the circumcircles of triangles $KQH$ and $FKM$ are tangent to each other.
theorem IMO_2015_P3 :
  ∀ (A B C H F M K Q D E O₁ O₂ : Point) (AB BC CA l AK KQ QA: Line) (Γ Δ Θ : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| > |(A─C)| ∧
    circumCircle Γ A B C ∧
    orthoCentre H A B C D E F AB BC CA ∧
    midpoint B M C ∧
    Q.onCircle Γ ∧ ∠ H:Q:A = ∟ ∧
    K.onCircle Γ ∧ ∠ H:K:Q = ∟ ∧
    formQuadrilateral A C K Q CA CK KQ QA ∧
    circumCircle Δ K Q H ∧
    circumCircle Θ F K M → (∃!(P: Point), P.onCircle Δ ∧ P.onCircle θ) := by
  sorry
