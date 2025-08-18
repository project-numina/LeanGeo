import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABC$ be an acute-angled triangle with $AB < AC$. Let $\Omega$ be the circumcircle of $ABC$. Let $S$ be the midpoint of the arc $CB$ of $\Omega$ containing $A$. The perpendicular from $A$ to $BC$ meets $BS$ at $D$ and meets $\Omega$ again at $E ¬eq A$. The line through $D$ parallel to $BC$ meets line $BE$ at $L$. Denote the circumcircle of triangle $BDL$ by $\omega$. Let $\omega$ meet $\Omega$ again at $P ¬eq B$. Prove that the line tangent to $\omega$ at $P$ meets line $BS$ on the internal angle bisector of $\angle BAC$.
theorem IMO_2023_P2 :
  ∀ (A B C S D E L P M Oω : Point) (Ω ω : Circle)
    (AB BC CA BS BE DL TL : Line),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| < |(A─C)| ∧
    circumCircle Ω A B C ∧
    S.onCircle Ω ∧
    |(C─S)| = |(B─S)| ∧
    S.sameSide A BC ∧
    foot A D BC ∧
    distinctPointsOnLine B S BS ∧
    D.onLine BS ∧
    distinctPointsOnLine B E BE ∧
    E.onCircle Ω ∧
    coll A D E ∧
    E ≠ A ∧
    distinctPointsOnLine D L DL ∧
    ¬ DL.intersectsLine BC ∧
    L.onLine BE ∧
    L.onLine DL ∧
    circumCircle ω B D L ∧
    P.onCircle Ω ∧
    P.onCircle ω ∧
    P ≠ B ∧
    Oω.isCentre ω →
    tangentAtPoint P Oω TL ω ∧
    M.onLine TL ∧
    M.onLine BS ∧
    ∠ B:A:M = ∠ M:A:C := by
  sorry
