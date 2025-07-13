import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Each pair of opposite sides of a convex hexagon has the following property: the distance between their midpoints is equal to $\dfrac{\sqrt{3}}{2}$ times the sum of their lengths. Prove that all the angles of the hexagon are equal.
theorem IMO_2003_P3 :
  ∀ (A B C D E F M1 M2 M3 M4 M5 M6 : Point)
    (AB BC CD DE EF FA : Line),
    distinctPointsOnLine A B AB ∧ distinctPointsOnLine B C BC ∧ distinctPointsOnLine C D CD ∧
    distinctPointsOnLine D E DE ∧ distinctPointsOnLine E F EF ∧ distinctPointsOnLine F A FA ∧
    A.sameSide C DE ∧ B.sameSide D EF ∧ C.sameSide E FA ∧
    D.sameSide F AB ∧ E.sameSide A BC ∧ F.sameSide B CD ∧
    midpoint A M1 B ∧ midpoint D M2 E ∧ |(M1─M2)| = (√3/2) * (|(A─B)| + |(D─E)|) ∧
    midpoint B M3 C ∧ midpoint E M4 F ∧ |(M3─M4)| = (√3/2) * (|(B─C)| + |(E─F)|) ∧
    midpoint C M5 D ∧ midpoint F M6 A ∧ |(M5─M6)| = (√3/2) * (|(C─D)| + |(F─A)|) →
    ∠ F:A:B = ∠ A:B:C ∧
    ∠ A:B:C = ∠ B:C:D ∧
    ∠ B:C:D = ∠ C:D:E ∧
    ∠ C:D:E = ∠ D:E:F ∧
    ∠ D:E:F = ∠ E:F:A := by
  sorry