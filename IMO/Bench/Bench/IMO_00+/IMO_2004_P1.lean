import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute-angled Triangle with $AB≠AC$. The circle with Diameter $BC$ intersects the sides $AB$ and $AC$ at $M$ and $N$ respectively. Denote by $O$ the MidPoint of the side $BC$. The bisectors of the angles $\angle BAC$ and $\angle MON$ intersect at $R$. Prove that the circumcircles of the triangles $BMR$ and $CNR$ have a common point lying on the side $BC$.
theorem IMO_2004_P1 :
  ∀ (A B C M N O R X : Point) (AB BC CA : Line) (Ω : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| ≠ |(A─C)| ∧
    Diameter B C O Ω ∧
    M.onCircle Ω ∧
    N.onCircle Ω ∧
    between A M B ∧
    between A N C ∧
    MidPoint B O C ∧
    ∠ B:A:R = ∠ R:A:C ∧
    ∠ M:O:R = ∠ R:O:N →
  ∃ (X : Point), X.onLine BC ∧ Cyclic B M R X ∧ Cyclic C N R X := by
  sorry
