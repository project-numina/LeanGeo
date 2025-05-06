import Mathlib
import SystemE


theorem parallelogram_opposite_sides_angles :
  ∀ (A B C D: Point), (A = B ) →   ∠ A:B:C = ∠ C:D:A   :=
by
  euclid_intros
  euclid_apply parallelogram_opposite_sides_angles
  euclid_finish
