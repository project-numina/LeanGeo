import SystemE
import LeanGeo.Abbre

namespace LeanGeo
theorem parallel_eqAlternateAngles :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧ A ≠ C ∧ D ≠ B ∧
  C.opposingSides D T
  → ∠ C:A:B = ∠ A:B:D
:= by
sorry
theorem eqAlternateExteriorAngle_parallel : ∀ (a b c d e : Point) (AB CD BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine b d BD ∧
  (between e b d) ∧ (a.sameSide c BD) ∧
  (∠ e:b:a = ∠ e:d:c) →
  ¬(AB.intersectsLine CD) :=
by
  sorry

theorem parallel_eqAlternateExteriorAngle : ∀ (a b c d e : Point) (AB CD BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine b d BD ∧
  (between e b d) ∧ (a.sameSide c BD) ∧
  ¬(AB.intersectsLine CD)  → (∠ e:b:a = ∠ e:d:c)
   :=
by
  sorry
theorem parallel_supplementConsecutiveAngle :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T
  → ∠ C:A:B + ∠ A:B:D = ∟ + ∟
:= by
sorry

theorem supplementConsecutiveAngles_parallel :
∀ (L M T : Line) (A B C D : Point),
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T
  ∧ ∠ C:A:B + ∠ A:B:D = ∟ + ∟ → (¬ L.intersectsLine M)
:= by
sorry

theorem perpLine_perpLine_parallel : ∀ (L1 L2 M : Line),
  (perpLine L1 M) ∧ (perpLine L2 M) ∧ L1 ≠ L2 →
  ¬(L1.intersectsLine L2) :=
by sorry

theorem perpLine_parallel_perpLine:
  ∀ (M N L : Line),
    (perpLine M N ∧ ¬L.intersectsLine M) →
    perpLine L N :=
by
  sorry

theorem perp_same_line_coll : ∀ (A B C: Point) (l AB AC : Line), (perpLine l AB ∧ perpLine l AC) ∧ (distinctPointsOnLine A B AB) ∧ (distinctPointsOnLine A C AC) → coll A B C := by
  euclid_intros
  euclid_apply intersection_lines AB l as P
  euclid_apply exists_distincts_points_on_line l P as Q
  sorry

end LeanGeo
