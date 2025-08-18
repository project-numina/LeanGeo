import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let ABC be a Triangle and P be any point on the circumcircle of Triangle ABC. Let X, Y, Z be the feet of the perpendiculars from P onto lines BC, CA, and AB. Prove that points X, Y , Z are collinear.
theorem Simson_Line :
  ∀ (A B C P X Y Z : Point) (Ω : Circle) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    Circumcircle Ω A B C ∧
    P.onCircle Ω ∧
    Foot P X BC ∧
    Foot P Y CA ∧
    Foot P Z AB →
    Coll X Y Z := by
  sorry
