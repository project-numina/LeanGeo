import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let the excircle of triangle $ABC$ opposite the vertex $A$ be tangent to the side $BC$ at the point $A_1$. Define the points $B_1$ on $CA$ and $C_1$ on $AB$ analogously, using the excircles opposite $B$ and $C$, respectively. Suppose that the circumcentre of triangle $A_1B_1C_1$ lies on the circumcircle of triangle $ABC$. Prove that triangle $ABC$ is right-angled.
theorem imo2013_p3 :
  ∀ (A B C Ia Ib Ic A1 B1 C1 O1 : Point)
    (exA exB exC Ω : Circle)
    (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    exCentre Ia A B C ∧ exCentre Ib B C A ∧ exCentre Ic C A B ∧
    Ia.isCentre exA ∧ tangentAtPoint A1 Ia BC exA ∧ between B A1 C ∧
    Ib.isCentre exB ∧ tangentAtPoint B1 Ib CA exB ∧ between C B1 A ∧
    Ic.isCentre exC ∧ tangentAtPoint C1 Ic AB exC ∧ between A C1 B ∧
    circumCentre O1 A1 B1 C1 ∧ circumCircle Ω A B C ∧
    O1.onCircle Ω
    → rightTriangle A B C := by
  sorry