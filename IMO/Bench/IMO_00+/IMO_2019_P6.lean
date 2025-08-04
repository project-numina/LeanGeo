import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $I$ be the incentre of acute triangle $ABC$ with $AB
eq AC$. The incircle $\omega$ of $ABC$ is tangent to sides $BC, CA$, and $AB$ at $D, E,$ and $F$, respectively. The line through $D$ perpendicular to $EF$ meets $\omega$ at $R$. Line $AR$ meets $\omega$ again at $P$. The circumcircles of triangle $PCE$ and $PBF$ meet again at $Q$. Prove that lines $DI$ and $PQ$ meet on the line through $A$ perpendicular to $AI$.
theorem IMO_2019_P6 :
  ∀ (A B C I D E F R P Q X : Point)
    (ω : Circle)
    (BC CA AB EF Ld ARline AIline DIline PQline Lperp : Line),
    formAcuteTriangle A B C AB BC CA ∧
    |(A─B)| ≠ |(A─C)| ∧
    inCircle ω AB BC CA ∧
    inCentre I A B C ∧
    tangentAtPoint D I BC ω ∧
    tangentAtPoint E I CA ω ∧
    tangentAtPoint F I AB ω ∧
    distinctPointsOnLine E F EF ∧
    distinctPointsOnLine D R Ld ∧
    perpLineatPoint Ld EF D ∧
    R.onCircle ω ∧
    distinctPointsOnLine A R ARline ∧
    P.onLine ARline ∧
    P.onCircle ω ∧
    P ≠ R ∧
    cyclic P C E Q ∧
    cyclic P B F Q ∧
    Q ≠ P ∧
    distinctPointsOnLine A I AIline ∧
    distinctPointsOnLine D I DIline ∧
    distinctPointsOnLine P Q PQline ∧
    twoLinesIntersectAtPoint DIline PQline X ∧
    perpLineatPoint Lperp AIline A
    → X.onLine Lperp :=
  by
  sorry
