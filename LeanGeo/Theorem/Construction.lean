import SystemE
import LeanGeo.Abbre

namespace LeanGeo
theorem construct_perpBisector (a b : Point) : ¬ (a ≠ b) →  ∃ L, perpBisector a b L := by
  euclid_intros
  euclid_apply line_from_points
  sorry

theorem exists_centre : ∀ (O: Circle), ∃ (C : Point), C.isCentre O := by
  sorry

theorem exists_midpoint : ∀ (A B : Point), ∃(P : Point), midpoint A P B := by
  sorry

--theorem exists_foot : ∀ (A : Point) (l : Line), ∃(P : Point), P.onLine l ∧
--(∀ Q:Point, Q.onLine l → ∠A:P:Q = ∟) := by
--  sorry
theorem midpoint_twice: ∀ (A B P : Point), midpoint A P B → |(A─B)| * 1/2 = |(P─B)|  := by
  euclid_intros
  euclid_apply line_from_points
  euclid_finish

theorem exists_foot : ∀ (c: Point) (AB : Line),
   ¬(c.onLine AB) →
  exists h : Point, foot c h AB :=
by
  sorry

theorem exists_angleBisection : ∀ (A B C : Point),
(A ≠ B) ∧ (A ≠ C) ∧ ¬(coll A B C)
→ ∃ (L : Line), ∀ (P: Point), P.onLine L ↔ ∠ A:B:P = ∠ P:B:C
:= by
    sorry


theorem unique_perpLine : ∀ (A : Point) (L : Line),
  ¬(A.onLine L)
  → ∃! (M : Line),
    A.onLine M
    ∧ perpLine L M
    :=
by
  sorry

theorem exists_inCentre : ∀ (A B C: Point), triangle A B C → ∃ (I : Point), inCentre I A B C := by
  sorry
end LeanGeo
