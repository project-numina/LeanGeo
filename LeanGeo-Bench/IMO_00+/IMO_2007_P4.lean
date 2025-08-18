import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--In Triangle $ABC$ the bisector of angle $BCA$ intersects the circumcircle again at $R$, the perpendicular bisector of $BC$ at $P$, and the perpendicular bisector of $AC$ at $Q$. The MidPoint of $BC$ is $K$ and the MidPoint of $AC$ is $L$. Prove that the triangles $RPK$ and $RQL$ have the same area.
theorem IMO_2007_P4 :
  ∀ (A B C R P Q K L : Point) (AB BC CA L1 L2 : Line) (Ω : Circle),
    formTriangle A B C AB BC CA ∧
    Circumcircle Ω A B C ∧
    R.onCircle Ω ∧
    R ≠ C ∧
    ∠ B:C:R = ∠ R:C:A ∧
    PerpBisector B C L1 ∧ P.onLine L1 ∧ ∠ B:C:P = ∠ P:C:A ∧
    PerpBisector A C L2 ∧ Q.onLine L2 ∧ ∠ B:C:Q = ∠ Q:C:A ∧
    MidPoint B K C ∧ MidPoint A L C
    → (△ R:P:K).area = (△ R:Q:L).area := by
  sorry
