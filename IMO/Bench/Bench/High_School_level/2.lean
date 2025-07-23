import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

/--Given that in $\triangle ABC$, lines $AD$, $BE$, and $CF$ are the altitudes of $\triangle ABC$. Point $H$ is the orthocenter of $\triangle ABC$, and point $O$ is the circumcenter of $\triangle ABC$. Line $ED$ intersects line $AB$ at point $M$, and line $FD$ intersects line $AC$ at point $N$. Prove that $OH \perp MN$.-/
theorem problem_HP71 :
  ∀ (A B C D E F H O M N : Point)
    (AB BC CA AD BE CF ED FD MN OH: Line),
    formTriangle A B C AB BC CA ∧
    distinctPointsOnLine A D AD ∧
    distinctPointsOnLine B E BE ∧
    distinctPointsOnLine C F CF ∧
    Orthocentre H A B C D E F AB BC CA ∧
    Circumcentre O A B C ∧
    distinctPointsOnLine D E ED ∧
    distinctPointsOnLine F D FD ∧
    TwoLinesIntersectAtPoint ED AB M ∧
    TwoLinesIntersectAtPoint FD AC N ∧
    distinctPointsOnLine O H OH ∧
    distinctPointsOnLine M N MN
  → PerpLine OH MN
:= by
  sorry
