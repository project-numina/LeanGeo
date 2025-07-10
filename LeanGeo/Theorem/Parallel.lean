import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Angle
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

theorem coll_of_rayAngleEq (A B C C' : Point) (hAB : A ≠ B) (hC : ¬ coll A B C) (hC' : ¬ coll A B C') : ∠ A:B:C = ∠ A:B:C' → coll B C C' := sorry
theorem perpLine_perpLine_parallel : ∀ (L1 L2 M : Line),
  (perpLine L1 M) ∧ (perpLine L2 M) ∧ L1 ≠ L2 →
  ¬(L1.intersectsLine L2) :=
by
  euclid_intros
  obtain ⟨X, hX⟩ := left
  obtain ⟨Y, hY⟩ := left_1
  obtain ⟨E1, hE1⟩ := intersection_lines L1 M hX.1.1
  obtain ⟨E2, hE2⟩ := intersection_lines L2 M hY.1.1
  have : E1 ≠ E2 := by
    intro h
    rw [← h] at hE2
    obtain ⟨E1', hE1'⟩ := exists_distincts_points_on_line M E1
    obtain ⟨E1'', hE1''⟩ := exists_distincts_points_on_line L1 E1
    obtain ⟨E1''', hE1'''⟩ := exists_distincts_points_on_line L2 E1
    have := hX.2 E1'' E1' (by euclid_finish) (by euclid_finish) (by euclid_finish) (by euclid_finish)
    have : E1 = X := by euclid_finish
    have : E1 = Y := by euclid_finish
    have : twoLinesIntersectAtPoint L2 L1 Y := by euclid_finish
    have := hY.2 E1''' E1' (by euclid_finish) (by euclid_finish) (by euclid_finish) (by euclid_finish)
    have : coll E1 E1'' E1''' := by
      have := coll_of_rayAngleEq
      euclid_finish
    euclid_finish
  obtain ⟨E1', hE1'⟩ := exists_distincts_points_on_line L1 E1
  obtain ⟨M', hM'⟩ := proposition_31 E1' E1 E2 M (by euclid_finish)
  have : M'.intersectsLine L2 := by euclid_finish
  obtain ⟨E2', hE2'⟩ := intersection_lines M' L2 this
  have := supplementConsecutiveAngles_parallel L1 L2 M E1 E2 E1' E2' (by euclid_finish)
  euclid_finish

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
