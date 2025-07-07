import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.BookTheorem

open LeanGeo
namespace LeanGeo
theorem perpBisector_property : ∀ (A B : Point) (L : Line),
  perpBisector A B L →
  (∀ (X : Point), X.onLine L → |(X─A)| = |(X─B)|) ∧
  (∀ (X : Point), |(X─A)| = |(X─B)| → X.onLine L)
:= by
  euclid_intros
  constructor
  · euclid_finish
  · euclid_intros

    sorry

theorem perpBisector_construction :
∀ (a b p q : Point) (L : Line),
(a ≠ b) ∧ (|(a─p)| = |(b─p)|) ∧ (|(a─q)| = |(b─q)|) ∧ distinctPointsOnLine p q L
→ perpBisector a b L := by
sorry

theorem perpBisector_equiv : ∀ (A B : Point) (L: Line),
perpBisector A B L ↔ ∃ (P :Point) (AB : Line), P.onLine L ∧ midpoint A P B ∧ perpLine AB L ∧ distinctPointsOnLine A B AB := by
  sorry


theorem between_zeroAngle : ∀ (A B C : Point), between A B C → ∠B:A:C = 0 := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  euclid_finish

end LeanGeo
