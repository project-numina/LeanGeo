import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Consider an acute-angled triangle $ABC$. Let $P$ be the foot of the altitude of triangle $ABC$ issuing from the vertex $A$, and let $O$ be the circumcenter of triangle $ABC$. Assume that $\angle C \geq \angle B+30^{\circ}$. Prove that $\angle A+\angle COP < 90^{\circ}$.
theorem IMO_2001_P1 :
  ∀ (A B C P O : Point) (AB BC CA : Line),
    formAcuteTriangle A B C AB BC CA ∧
    foot A P BC ∧
    circumCentre O A B C ∧
    ∠ A:C:B ≥ ∠ C:B:A + ∟/3 →
    ∠ B:A:C + ∠ C:O:P < ∟ := by
  sorry
