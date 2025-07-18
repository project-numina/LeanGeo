import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $\Gamma$ be the circumcircle of acute triangle $ABC$. Points $D$ and $E$ are on segments $AB$ and $AC$ respectively such that $AD = AE$. The perpendicular bisectors of $BD$ and $CE$ intersect minor arcs $AB$ and $AC$ of $\Gamma$ at points $F$ and $G$ respectively. Prove that lines $DE$ and $FG$ are either parallel or they are the same line.
theorem IMO_2018_P1 :
  ∀ (A B C D E F G : Point)
    (AB BC CA L1 L2 DE FG : Line)
    (Γ : Circle),
    formAcuteTriangle A B C AB BC CA ∧
    circumCircle Γ A B C ∧
    between A D B ∧
    between A E C ∧
    |(A─D)| = |(A─E)| ∧
    perpBisector B D L1 ∧
    F.onCircle Γ ∧
    F.onLine L1 ∧
    F.opposingSides C AB ∧
    perpBisector C E L2 ∧
    G.onCircle Γ ∧
    G.onLine L2 ∧
    G.opposingSides B AC ∧
    distinctPointsOnLine D E DE ∧
    distinctPointsOnLine F G FG →
    ¬(DE.intersectsLine FG) := by
  sorry
