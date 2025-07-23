import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute-angled Triangle with $AB < AC$. Let $\Omega$ be the circumcircle of $ABC$. Let $S$ be the MidPoint of the arc $CB$ of $\Omega$ containing $A$. The perpendicular from $A$ to $BC$ meets $BS$ at $D$ and meets $\Omega$ again at $E ¬eq A$. The line through $D$ parallel to $BC$ meets line $BE$ at $L$. Denote the circumcircle of Triangle $BDL$ by $\omega$. Let $\omega$ meet $\Omega$ again at $P ¬eq B$. Prove that the line tangent to $\omega$ at $P$ meets line $BS$ on the internal angle bisector of $\angle BAC$.
theorem IMO_2023_P2 :
  ∀ (A B C S D E L P M Oω : Point) (Ω ω : Circle)
    (AB BC CA BS BE DL TL : Line),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| < |(A─C)| ∧
    Circumcircle Ω A B C ∧
    S.onCircle Ω ∧
    |(C─S)| = |(B─S)| ∧
    S.sameSide A BC ∧
    Foot A D BC ∧
    distinctPointsOnLine B S BS ∧
    D.onLine BS ∧
    distinctPointsOnLine B E BE ∧
    E.onCircle Ω ∧
    Coll A D E ∧
    E ≠ A ∧
    distinctPointsOnLine D L DL ∧
    ¬ DL.intersectsLine BC ∧
    L.onLine BE ∧
    Circumcircle ω B D L ∧
    P.onCircle Ω ∧
    P.onCircle ω ∧
    P ≠ B ∧
    Oω.isCentre ω ∧
    TangentLineCircleAtPoint P Oω TL ω ∧
    M.onLine TL ∧
    M.onLine BS →
    ∠ B:A:M = ∠ M:A:C := by
  sorry
