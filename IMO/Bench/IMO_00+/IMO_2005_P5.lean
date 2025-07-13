import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $ABCD$ be a fixed convex quadrilateral with $BC=DA$ and $BC$ not parallel with $DA$. Let two variable points $E$ and $F$ lie of the sides $BC$ and $DA$, respectively and satisfy $BE=DF$. The lines $AC$ and $BD$ meet at $P$, the lines $BD$ and $EF$ meet at $Q$, the lines $EF$ and $AC$ meet at $R$. Prove that the circumcircles of the triangles $PQR$, as $E$ and $F$ vary, have a common point other than $P$.
theorem IMO_2005_P5 :
  ∀ (A B C D E F P Q R X : Point)
    (AB BC CD DA AC BD EF : Line)
    (Ω1 Ω2 : Circle),
    formQuadrilateral A B C D AB BC CD DA ∧
    |(B─C)| = |(D─A)| ∧
    BC.intersectsLine DA ∧
    E.onLine BC ∧
    F.onLine DA ∧
    |(B─E)| = |(D─F)| ∧
    twoLinesIntersectAtPoint AC BD P ∧
    twoLinesIntersectAtPoint BD EF Q ∧
    twoLinesIntersectAtPoint EF AC R ∧
    circumCircle Ω1 P B C ∧
    circumCircle Ω2 P D A ∧
    circlesIntersectsAtTwoPoints Ω1 Ω2 P X →
    cyclic P Q R X := by
  sorry