import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Six points are chosen on the sides of an equilateral triangle $ABC$: $A_1$, $A_2$ on $BC$, $B_1$, $B_2$ on $CA$ and $C_1$, $C_2$ on $AB$, such that they are the vertices of a convex hexagon $A_1A_2B_1B_2C_1C_2$ with equal side lengths. Prove that the lines $A_1B_2$, $B_1C_2$ and $C_1A_2$ are concurrent.
theorem IMO_2005_P1 :
  ∀ (A B C A1 A2 B1 B2 C1 C2 : Point)
    (AB BC CA A1B2 B1C2 C1A2 : Line),
    formTriangle A B C AB BC CA ∧
    |(A─B)| = |(B─C)| ∧ |(B─C)| = |(C─A)| ∧
    between B A1 A2 ∧ between A1 A2 C ∧
    between C B1 B2 ∧ between B1 B2 A ∧
    between A C1 C2 ∧ between C1 C2 B ∧
    distinctPointsOnLine A1 B2 A1B2 ∧
    distinctPointsOnLine B1 C2 B1C2 ∧
    distinctPointsOnLine C1 A2 C1A2 ∧
    |(A1─A2)| = |(B1─B2)| ∧
    |(B1─B2)| = |(C1─C2)| →
    concurrent A1B2 B1C2 C1A2 := by
  sorry
