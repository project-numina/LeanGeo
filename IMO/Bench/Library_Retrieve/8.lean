import Mathlib
import SystemE
import LeanGeo
namespace LeanGeo

theorem library8 : ∀(A B C : Point), rightTriangle A B C → |(B─C)| > |(A─B)| ∧  |(B─C)| > |(A─C)| := by
  euclid_intros
  euclid_apply pythagorean_point A B C
  euclid_finish
