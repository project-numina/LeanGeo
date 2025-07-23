import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $H$ be the orthocenter of an acute-angled Triangle $ABC$. The circle $\Gamma_{A}$ centered at the MidPoint of $BC$ and passing through $H$ intersects the sideline $BC$ at points $A_{1}$ and $A_{2}$. Similarly, define the points $B_{1}$, $B_{2}$, $C_{1}$ and $C_{2}$. Prove that the six points $A_{1}$, $A_{2}$, $B_{1}$, $B_{2}$, $C_{1}$ and $C_{2}$ are concyclic.
theorem IMO_2008_P1 :
  ∀ (A B C H D E F A1 A2 B1 B2 C1 C2 MBC MCA MAB : Point) (AB BC CA : Line) (ΓA ΓB ΓC : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    Orthocentre H A B C D E F AB BC CA ∧
    MidPoint B MBC C ∧
    MBC.isCentre ΓA ∧
    H.onCircle ΓA ∧
    distinctPointsOnLine A1 A2 BC ∧
    A1.onCircle ΓA ∧
    A2.onCircle ΓA ∧
    MidPoint C MCA A ∧
    MCA.isCentre ΓB ∧
    H.onCircle ΓB ∧
    distinctPointsOnLine B1 B2 CA ∧
    B1.onCircle ΓB ∧
    B2.onCircle ΓB ∧
    MidPoint A MAB B ∧
    MAB.isCentre ΓC ∧
    H.onCircle ΓC ∧
    distinctPointsOnLine C1 C2 AB ∧
    C1.onCircle ΓC ∧
    C2.onCircle ΓC
  → ∃ (Ω : Circle), A1.onCircle Ω ∧ A2.onCircle Ω ∧ B1.onCircle Ω ∧ B2.onCircle Ω ∧ C1.onCircle Ω ∧ C2.onCircle Ω := by
  sorry
