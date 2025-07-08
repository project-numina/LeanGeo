import Mathlib
import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Construction

open LeanGeo
namespace LeanGeo
open Real
axiom rightAngle_eq_pi_div_two : ∟ = Real.pi / 2

theorem sin_rightAngle : sin ∟ = 1 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.sin_pi_div_two]

theorem cos_rightAngle : cos ∟ = 0 := by
  rw [rightAngle_eq_pi_div_two]
  rw [Real.cos_pi_div_two]

axiom rightTriangle_sin : ∀ (A B C : Point), rightTriangle A B C → sin (∠A:B:C) = |(A─C)| / |(B─C)|
axiom rightTriangle_cos : ∀ (A B C : Point), rightTriangle A B C → cos (∠B:C:A) = |(A─B)| / |(B─C)|

theorem law_of_sin : ∀ (A B C : Point), triangle A B C → |(B─C)| * sin (∠B:C:A)= |(A─B)| / sin (∠B:A:C)  := by
  euclid_intros
  euclid_apply line_from_points B C as BC
  euclid_apply exists_foot A BC as H
  by_cases (H ≠ C) ∧ (H ≠ B)
  · euclid_apply rightTriangle_sin H C A
    euclid_apply rightTriangle_sin H B A
