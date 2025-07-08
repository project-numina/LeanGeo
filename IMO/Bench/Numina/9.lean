import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--Problem 3. In an acute-angled triangle $A B C$, the altitude $A H$ is drawn. Let $P$ and $Q$ be the feet of the perpendiculars dropped from point $H$ to sides $A B$ and $A C$ respectively. Prove that $\angle B Q H=\angle C P H$.-/
theorem Numina_Geometry_542 : ∀ (A B C H P Q : Point) (AB BC CA : Line),
    (formAcuteTriangle A B C AB BC CA) ∧
    foot A H BC ∧
    foot H P AB ∧
    foot H Q AC
    → ∠B:Q:H = ∠C:P:H := by
  sorry
