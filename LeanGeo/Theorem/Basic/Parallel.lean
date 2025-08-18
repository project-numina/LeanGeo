import SystemE
import LeanGeo.Abbre
import LeanGeo.Axiom
import LeanGeo.Theorem.Basic.Angle
import LeanGeo.Theorem.Basic.Construction
import Book

set_option maxHeartbeats 0

open Elements.Book1
namespace LeanGeo

theorem parallel_imp_eq_alternateAngles :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  TwoLinesIntersectAtPoint L T A ∧
  TwoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧ A ≠ C ∧ D ≠ B ∧ A ≠ B ∧
  C.opposingSides D T
  → ∠ C:A:B = ∠ D:B:A
:= by
  euclid_intros
  obtain ⟨C', hC'1, hC'2⟩ := extend_point L C A (by euclid_finish)
  have : A ≠ B := by tauto
  obtain ⟨A', hA'⟩ := extend_point T B A (by euclid_finish)
  obtain ⟨D', hD'⟩ := extend_point M D B (by euclid_finish)
  obtain ⟨B', hB'⟩ := extend_point T A B (by euclid_finish)
  have := proposition_29 C C' D' D A' B' A B  L M T (by euclid_finish)
  euclid_finish

theorem parallel_if_eq_alternateAngles :
∀ (L M T : Line) (A B C D : Point),
  TwoLinesIntersectAtPoint L T A ∧
  TwoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.opposingSides D T ∧ A ≠ B
  ∧ ∠ C:A:B = ∠ A:B:D  → (¬ L.intersectsLine M) := by
  euclid_intros
  obtain ⟨c', hc'⟩ := extend_point L C A (by euclid_finish)
  obtain ⟨d', hd'⟩ := extend_point M D B (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point T B A (by euclid_finish)
  obtain ⟨b', hb'⟩ := extend_point T A B (by euclid_finish)
  have h1: ∠a':A :c' = ∠C:A:B := by
    euclid_apply eq_opposite_angles C B A a' c'
    euclid_finish
  have := proposition_28 C c' d' D a' b' A B L M T (by euclid_finish)
  euclid_finish

theorem parallel_if_eq_alternateExteriorAngles : ∀ (a b c d e : Point) (AB CD BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine b d BD ∧
  (between e b d) ∧ (a.sameSide c BD) ∧
  (∠ e:b:a = ∠ e:d:c) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  obtain ⟨d', hd'⟩ := extend_point BD b d (by euclid_finish)
  obtain ⟨c', hc'⟩ := extend_point CD c d (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point AB a b (by euclid_finish)
  have := proposition_28 a' a c' c e d' b d AB CD BD (by euclid_finish)
  euclid_finish

theorem parallel_imp_eq_alternateExteriorAngles : ∀ (a b c d e : Point) (AB CD BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine b d BD ∧
  (between e b d) ∧ (a.sameSide c BD) ∧
  ¬(AB.intersectsLine CD)  → (∠ e:b:a = ∠ e:d:c)
   := by
  euclid_intros
  obtain ⟨d', hd'⟩ := extend_point BD b d (by euclid_finish)
  obtain ⟨c', hc'⟩ := extend_point CD c d (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point AB a b (by euclid_finish)
  have := proposition_29 a' a c' c e d' b d AB CD BD (by euclid_finish)
  euclid_finish

theorem parallel_imp_supp_consecutiveAngles :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  TwoLinesIntersectAtPoint L T A ∧
  TwoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T ∧ A ≠ B
  → ∠ C:A:B + ∠ A:B:D = ∟ + ∟
:= by
  euclid_intros
  obtain ⟨c', hc'⟩ := extend_point L C A (by euclid_finish)
  obtain ⟨d', hd'⟩ := extend_point M D B (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point T B A (by euclid_finish)
  obtain ⟨b', hb'⟩ := extend_point T A B (by euclid_finish)
  have := proposition_29 c' C d' D a' b' A B L M T (by euclid_finish)
  euclid_finish

theorem parallel_if_supp_consecutiveAngles :
∀ (L M T : Line) (A B C D : Point),
  TwoLinesIntersectAtPoint L T A ∧
  TwoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T ∧ A ≠ B
  ∧ ∠ C:A:B + ∠ A:B:D = ∟ + ∟ → (¬ L.intersectsLine M) := by
  euclid_intros
  obtain ⟨c', hc'⟩ := extend_point L C A (by euclid_finish)
  obtain ⟨d', hd'⟩ := extend_point M D B (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point T B A (by euclid_finish)
  obtain ⟨b', hb'⟩ := extend_point T A B (by euclid_finish)
  have := proposition_28 c' C d' D a' b' A B L M T (by euclid_finish)
  euclid_finish

theorem common_perpLine_imp_coll : ∀ (A B C D: Point), A ≠ B ∧ C ≠ B  ∧ B ≠ D ∧  ∠A:B:C = ∟ ∧ ∠A:B:D = ∟ → Coll B C D := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  by_cases C.sameSide D AB
  · euclid_apply coll_if_eq_angles A B C D AB
    euclid_finish
  · euclid_assert ¬ C.onLine AB
    euclid_apply coll_if_supp_angles A B C D AB
    euclid_finish

theorem perpLine_imp_rightAngleLine_parallel : ∀ (L1 L2 M : Line),
  (PerpLine L1 M) ∧ (PerpLine L2 M) ∧ L1 ≠ L2 →
  ¬(L1.intersectsLine L2) := by
    euclid_intros
    euclid_apply intersection_lines L1 M as P
    euclid_apply intersection_lines L2 M as Q
    have h1: P ≠ Q := by
      by_contra
      euclid_apply exists_distincts_points_on_line L1 P as R
      euclid_apply exists_distincts_points_on_line L2 P as S
      euclid_apply exists_distincts_points_on_line M P as T
      euclid_assert ∠R:P:T = ∟
      euclid_assert ∠S:P:T = ∟
      have h1: Coll T P S := by
        euclid_apply common_perpLine_imp_coll T P R S
        euclid_finish
      euclid_finish
    simp_all
    euclid_apply exists_distincts_points_on_line L1 P as R
    euclid_apply exists_distincts_points_on_line L2 Q as T
    euclid_assert ∠ R:P:Q = ∟
    by_cases R.sameSide T M
    · euclid_apply parallel_if_supp_consecutiveAngles
      euclid_finish
    · euclid_apply parallel_if_eq_alternateAngles
      euclid_finish

theorem perp_parallel_imp_perp:
  ∀ (M N L : Line),
    (PerpLine M N ∧ ¬L.intersectsLine M) →
    PerpLine L N :=
by
  euclid_intros
  euclid_apply intersection_lines N M as T
  euclid_apply exists_distincts_points_on_line M T as R
  euclid_apply intersection_lines N L as P
  by_cases P = T
  · euclid_finish
  · use P
    constructor
    · euclid_finish
    · intro A B hAP
      euclid_assert ∠P:T:R = ∟
      have h1: ∠T:P:A = ∟ := by
        by_cases A.sameSide R N
        · euclid_apply parallel_imp_supp_consecutiveAngles
          euclid_finish
        · euclid_apply parallel_imp_eq_alternateAngles
          euclid_finish
      euclid_finish

end LeanGeo
