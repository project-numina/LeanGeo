import Mathlib
import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Construction

namespace LeanGeo
open Real


axiom rightTriangle_sin : ∀ (A B C : Point), rightTriangle A B C → sin (∠A:B:C) = |(A─C)| / |(B─C)|
axiom rightTriangle_cos : ∀ (A B C : Point), rightTriangle A B C → cos (∠B:C:A) = |(A─B)| / |(B─C)|

theorem law_of_sin : ∀ (A B C : Point), triangle A B C → |(B─C)| * sin (∠B:C:A)= |(A─B)| / sin (∠B:A:C)  := by
  euclid_intros
  euclid_apply line_from_points B C as BC
  euclid_apply exists_foot A BC as H
  by_cases (H ≠ C) ∧ (H ≠ B)
  · euclid_apply rightTriangle_sin H C A
    euclid_apply rightTriangle_sin H B A
