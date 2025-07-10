import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
import LeanGeo.Theorem.Construction
import Book

set_option maxHeartbeats 0

open Elements.Book1

open LeanGeo
namespace LeanGeo

-- proposition_31 used to construct a parallel line passing though a point
-- that is given point P and line L, construct L' parrallel to L passing through P

theorem transferline_angles : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧ ¬(AB.intersectsLine CD)
  → ∠ a:g:h = ∠ g:h:d ∧ ∠ e:g:b = ∠ g:h:d ∧ ∠ b:g:h + ∠ g:h:d = ∟ + ∟ := proposition_29

theorem parallel_eqAlternateAngles :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
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
  have := transferline_angles C C' D' D A' B' A B  L M T (by euclid_finish)
  euclid_finish

theorem parallel_if : ∀ (a b c d e f g h : Point) (AB CD EF : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine e f EF ∧
  (between a g b) ∧ (between c h d) ∧ (between e g h) ∧ (between g h f) ∧ (b.sameSide d EF) ∧
  (∠ e:g:b = ∠ g:h:d ∨ ∠ b:g:h + ∠ g:h:d = ∟ + ∟) →
  ¬(AB.intersectsLine CD) := proposition_28

theorem eqAlternateAngles_parallel :
∀ (L M T : Line) (A B C D : Point),
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
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
    euclid_apply opposite_angles_same C B A a' c'
    euclid_finish
  have := parallel_if C c' d' D a' b' A B L M T (by euclid_finish)
  euclid_finish

theorem eqAlternateExteriorAngle_parallel : ∀ (a b c d e : Point) (AB CD BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine b d BD ∧
  (between e b d) ∧ (a.sameSide c BD) ∧
  (∠ e:b:a = ∠ e:d:c) →
  ¬(AB.intersectsLine CD) :=
by
  euclid_intros
  obtain ⟨d', hd'⟩ := extend_point BD b d (by euclid_finish)
  obtain ⟨c', hc'⟩ := extend_point CD c d (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point AB a b (by euclid_finish)
  have := parallel_if a' a c' c e d' b d AB CD BD (by euclid_finish)
  euclid_finish

theorem parallel_eqAlternateExteriorAngle : ∀ (a b c d e : Point) (AB CD BD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ distinctPointsOnLine b d BD ∧
  (between e b d) ∧ (a.sameSide c BD) ∧
  ¬(AB.intersectsLine CD)  → (∠ e:b:a = ∠ e:d:c)
   := by
  euclid_intros
  obtain ⟨d', hd'⟩ := extend_point BD b d (by euclid_finish)
  obtain ⟨c', hc'⟩ := extend_point CD c d (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point AB a b (by euclid_finish)
  have := transferline_angles a' a c' c e d' b d AB CD BD (by euclid_finish)
  euclid_finish

theorem parallel_supplementConsecutiveAngle :
∀ (L M T : Line) (A B C D : Point),
  (¬ L.intersectsLine M) ∧
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
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
  have := transferline_angles c' C d' D a' b' A B L M T (by euclid_finish)
  euclid_finish

theorem supplementConsecutiveAngles_parallel :
∀ (L M T : Line) (A B C D : Point),
  twoLinesIntersectAtPoint L T A ∧
  twoLinesIntersectAtPoint M T B ∧
  C.onLine L ∧
  D.onLine M ∧
  C.sameSide D T ∧ A ≠ B
  ∧ ∠ C:A:B + ∠ A:B:D = ∟ + ∟ → (¬ L.intersectsLine M) := by
  euclid_intros
  obtain ⟨c', hc'⟩ := extend_point L C A (by euclid_finish)
  obtain ⟨d', hd'⟩ := extend_point M D B (by euclid_finish)
  obtain ⟨a', ha'⟩ := extend_point T B A (by euclid_finish)
  obtain ⟨b', hb'⟩ := extend_point T A B (by euclid_finish)
  have := parallel_if c' C d' D a' b' A B L M T (by euclid_finish)
  euclid_finish
theorem perpLine_perp : ∀ (P Q R: Point) (L1 L2 : Line), perpLine L1 L2 ∧ twoLinesIntersectAtPoint L1 L2 P ∧ Q.onLine L1 ∧ R.onLine L2 ∧ Q ≠ P ∧ R ≠ P → ∠Q:P:R = ∟ := by
  euclid_intros
  euclid_finish

theorem perp_perp_coll : ∀ (A B C D: Point), A ≠ B ∧ C ≠ B  ∧ B ≠ D ∧  ∠A:B:C = ∟ ∧ ∠A:B:D = ∟ → coll B C D := by
  euclid_intros
  euclid_apply line_from_points A B as AB
  by_cases C.sameSide D AB
  · euclid_apply sameSide_eqAngle_coll A B C D AB
    euclid_finish
  · euclid_assert ¬ C.onLine AB
    euclid_apply opposingSides_complement_coll A B C D AB
    euclid_finish

theorem perpLine_perpLine_parallel : ∀ (L1 L2 M : Line),
  (perpLine L1 M) ∧ (perpLine L2 M) ∧ L1 ≠ L2 →
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
      have h1: coll T P S := by
        euclid_apply perp_perp_coll T P R S
        euclid_finish
      euclid_finish
    simp_all
    euclid_apply exists_distincts_points_on_line L1 P as R
    euclid_apply exists_distincts_points_on_line L2 Q as T
    euclid_assert ∠ R:P:Q = ∟
    by_cases R.sameSide T M
    · euclid_apply supplementConsecutiveAngles_parallel
      euclid_finish
    · euclid_apply eqAlternateAngles_parallel
      euclid_finish

theorem perpLine_parallel_perpLine:
  ∀ (M N L : Line),
    (perpLine M N ∧ ¬L.intersectsLine M) →
    perpLine L N :=
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
    · intro A B hAP hBP hAL hBL
      euclid_assert ∠P:T:R = ∟
      have h1: ∠T:P:A = ∟ := by
        by_cases A.sameSide R N
        · euclid_apply parallel_supplementConsecutiveAngle
          euclid_finish
        · euclid_apply parallel_eqAlternateAngles
          euclid_finish
      euclid_finish


end LeanGeo
