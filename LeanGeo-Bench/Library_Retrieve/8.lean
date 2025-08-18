import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library8 : ∀(A B C : Point), RightTriangle A B C → |(B─C)| > |(A─B)| ∧  |(B─C)| > |(A─C)| := by
  euclid_intros
  euclid_apply PythagoreanTheorem_point A B C
  euclid_finish
