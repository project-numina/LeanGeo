import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

--Let ABC be a triangle and P be any point on the circumcircle of triangle ABC. Let X, Y, Z be the feet of the perpendiculars from P onto lines BC, CA, and AB. Prove that points X, Y , Z are collinear.
theorem Simson_Line :
  ∀ (A B C P X Y Z : Point) (Ω : Circle) (AB BC CA : Line),
    formTriangle A B C AB BC CA ∧
    circumCircle Ω A B C ∧
    P.onCircle Ω ∧
    foot P X BC ∧
    foot P Y CA ∧
    foot P Z AB →
    coll X Y Z := by
  sorry