import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let $A B C$ be a triangle. Take points $D, E, F$ on the perpendicular bisectors of $\overline{B C}, \overline{C A}, \overline{A B}$ respectively. Show that the lines through $A, B, C$ perpendicular to $\overline{E F}, \overline{F D}, \overline{D E}$ respectively are concurrent.
theorem Problem_2_30_USAMO_1997_2 :
  ∀ (A B C D E F : Point)
    (AB BC CA l1 l2 l3 EF FD DE lA lB lC : Line),
    formTriangle A B C AB BC CA ∧
    perpBisector B C l1 ∧ D.onLine l1 ∧
    perpBisector C A l2 ∧ E.onLine l2 ∧
    perpBisector A B l3 ∧ F.onLine l3 ∧
    distinctPointsOnLine E F EF ∧
    distinctPointsOnLine F D FD ∧
    distinctPointsOnLine D E DE ∧
    A.onLine lA ∧ perpLine lA EF ∧
    B.onLine lB ∧ perpLine lB FD ∧
    C.onLine lC ∧ perpLine lC DE →
    concurrent lA lB lC := by
  sorry