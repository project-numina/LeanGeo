import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo
--Not verified
--Let the excircle of Triangle $ABC$ opposite the vertex $A$ be tangent to the side $BC$ at the point $A_1$. Define the points $B_1$ on $CA$ and $C_1$ on $AB$ analogously, using the excircles opposite $B$ and $C$, respectively. Suppose that the circumcentre of Triangle $A_1B_1C_1$ lies on the circumcircle of Triangle $ABC$. Prove that Triangle $ABC$ is right-angled.
theorem imo2013_p3 :
  ∀ (A B C Ia Ib Ic A1 B1 C1 O1 : Point)
    (exA exB exC Ω : Circle)
    (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧ Excircle exA A B C AB BC CA ∧
    Excircle exB B C A BC CA AB ∧ Excircle exC C A B CA AB BC ∧
    Excentre Ia A B C ∧ Excentre Ib B C A ∧ Excentre Ic C A B ∧
    TangentLineCircleAtPoint A1 Ia BC exA ∧ between B A1 C ∧
    TangentLineCircleAtPoint B1 Ib CA exB ∧ between C B1 A ∧
    TangentLineCircleAtPoint C1 Ic AB exC ∧ between A C1 B ∧
    Circumcentre O1 A1 B1 C1 ∧ Circumcircle Ω A B C ∧
    O1.onCircle Ω
    → RightTriangle A B C := by
  sorry
