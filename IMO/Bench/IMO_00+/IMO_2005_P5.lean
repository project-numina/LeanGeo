import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABCD$ be a fixed convex quadrilateral with $BC=DA$ and $BC$ not parallel with $DA$. Let two variable points $E$ and $F$ lie of the sides $BC$ and $DA$, respectively and satisfy $BE=DF$. The lines $AC$ and $BD$ meet at $P$, the lines $BD$ and $EF$ meet at $Q$, the lines $EF$ and $AC$ meet at $R$. Prove that the circumcircles of the triangles $PQR$, as $E$ and $F$ vary, have a common point other than $P$.
theorem IMO_2005_P5 :
  ∀ (A B C D P: Point)
    (AB BC CD DA AC BD: Line),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(B─C)| = |(D─A)| ∧
    BC.intersectsLine DA ∧
    distinctPointsOnLine A C AC ∧
    distinctPointsOnLine B D BD ∧
    twoLinesIntersectAtPoint AC BD P
    → (∃(X:Point), X ≠ P ∧  ∀ ( E F P Q R: Point) (EF : Line),
    between B E C ∧
    between A F D ∧
    |(B─E)| = |(D─F)| ∧
    distinctPointsOnLine E F EF ∧
    twoLinesIntersectAtPoint BD EF Q ∧
    twoLinesIntersectAtPoint EF AC R
    → cyclic P Q R X) := by
  sorry
