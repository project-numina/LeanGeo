import SystemE
import LeanGeo.Abbre
import LeanGeo.Theorem.Position
import LeanGeo.Theorem.Triangle

open SystemE
namespace LeanGeo
theorem parallelogram_tests : ∀
  (A B C D : Point)
  (AB BC CD DA: Line),
  (formQuadrilateral A B C D AB BC CD DA) ∧
    ((|(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)|)
    ∨
    (|(A─B)| = |(C─D)| ∧ ¬ AB.intersectsLine CD)
    ∨ (|(B─C)| = |(D─A)| ∧ ¬ BC.intersectsLine DA))
  →
  (parallelogram A B C D AB BC CD DA)
:= by
sorry

theorem parallelogram_eqSide : ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA ∧
   ¬(AB.intersectsLine CD) ∧
   ¬(BC.intersectsLine DA))
  → (|(A─B)| = |(C─D)| ∧ |(B─C)| = |(D─A)|) := by
sorry

theorem parallelogram_eqAngle :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  (formQuadrilateral A B C D AB BC CD DA)
  ∧ (¬ AB.intersectsLine CD)
  ∧ (¬ DA.intersectsLine BC)
  → ∠D:A:B = ∠B:C:D ∧ ∠A:B:C = ∠C:D:A
:= by
sorry

theorem parallelogram_diagonals_bisect :
∀ (A B C D E : Point) (AB BC CD DA AC BD : Line),
  (parallelogram A B C D AB BC CD DA)
  ∧ distinctPointsOnLine A C AC
  ∧ distinctPointsOnLine B D BD
  ∧ (twoLinesIntersectAtPoint AC BD E)
  → (midpoint A E C ∧ midpoint B E D) := by
sorry

theorem rhombus_angleBisects :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  rhombus A B C D AB BC CD DA →
     (∠B:A:C = ∠C:A:D
     ∧ ∠B:C:A = ∠A:C:D
     ∧ ∠A:B:D = ∠D:B:C
     ∧ ∠C:D:B = ∠B:D:A) := by
sorry

theorem rhombus_angleBisects_perpendicular :
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  rhombus A B C D AB BC CD DA ∧ distinctPointsOnLine A C AC ∧ distinctPointsOnLine B D BD →
    perpLine AC BD := by
sorry

theorem circumscribed_quadrilateral_eqsumside :
  ∀ (A B C D : Point) (AB BC CD DA : Line) (Ω : Circle),
    (formQuadrilateral A B C D AB BC CD DA)
    ∧ (tangentLine AB Ω)
    ∧ (tangentLine BC Ω)
    ∧ (tangentLine CD Ω)
    ∧ (tangentLine DA Ω)
    → (|(A─B)| + |(C─D)| = |(B─C)| + |(D─A)|) :=
by
  sorry

theorem cyclic_test (A B C D: Point) (AB BC CD DA :Line) : (formQuadrilateral A B C D AB BC CD DA) ∧ (
  (∠ A:B:D = ∠ A:C:D) ∨
  (∠ D:A:C = ∠ D:B:C) ∨
  (∠ A:D:B = ∠ A:C:B) ∨
  (∠ B:D:C = ∠ B:A:C) ∨
  (∠ A:D:C + ∠A:B:C = ∟ + ∟) ∨
  (∠ D:A:B + ∠D:C:B = ∟ + ∟)) → ∃ (O: Circle), cyclicQuadrilateral A B C D AB BC CD DA O := by
  sorry

theorem cyclic_property (A B C D: Point) (AB BC CD DA :Line) (O: Circle): cyclicQuadrilateral A B C D AB BC CD DA O →
  (∠ A:B:D = ∠ A:C:D) ∧
  (∠ D:A:C = ∠ D:B:C) ∧
  (∠ A:D:B = ∠ A:C:B) ∧
  (∠ B:D:C = ∠ B:A:C) ∧
  (∠ A:D:C + ∠A:B:C = ∟ + ∟) ∧
  (∠ D:A:B + ∠D:C:B = ∟ + ∟)
  :=by
  sorry

theorem isoTrapezoid_eqAngle:
  ∀ (A B C D : Point) (AB BC CD DA : Line),
  trapezoid A B C D AB BC CD DA ∧
  (|(B─C)| = |(D─A)|)
  → (∠A:B:C = ∠D:C:B) ∧ (∠B:A:D = ∠C:D:A) := by
sorry
theorem parallelogram_median_mid_mid_para : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), parallelogram A B C D AB BC CD DA ∧ distinctPointsOnLine E F EF ∧ midpoint B E C ∧ midpoint A F D →  (¬ EF.intersectsLine CD) := by
  euclid_intros
  euclid_apply parallelogram_eqSide A B C D AB BC CD DA
  have h0: parallelogram E F D C EF DA CD BC := by
    have h1: A.sameSide B EF := by
      euclid_apply quadrilateral_line_from_side_sameside A B C D E F AB BC CD DA EF
      euclid_finish
    euclid_assert formQuadrilateral E F D C EF DA CD BC
    euclid_apply parallelogram_tests E F D C EF DA CD BC
    euclid_finish
  euclid_finish

theorem trapezoid_median_mid_mid_para1 : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ distinctPointsOnLine E F EF ∧ midpoint B E C ∧ midpoint A F D →  (¬ EF.intersectsLine CD) := by
  euclid_intros
  by_cases h: BC.intersectsLine DA
  · euclid_apply intersection_lines BC DA as G
    by_cases between G B E
    · sorry
    · sorry
  · euclid_apply parallelogram_median_mid_mid_para A B C D E F AB BC CD DA EF
    euclid_finish

theorem trapezoid_median_mid_mid_para : ∀ (A B C D E F: Point) (AB BC CD DA EF: Line), formQuadrilateral A B C D AB BC CD DA ∧ (¬ AB.intersectsLine CD) ∧ distinctPointsOnLine E F EF ∧ midpoint B E C ∧ midpoint A F D →  (¬ EF.intersectsLine CD) := by
  euclid_intros
  euclid_apply line_from_points A E as AE
  euclid_apply intersection_lines CD AE as G
  have h1: |(A─E)| = |(E─G)| := by
    euclid_apply para_similar_in B A C G E AB CD
    euclid_apply  similar_AA B A E C G E
    euclid_assert |(B─E)| = |(C─E)|
    euclid_apply congruent_ASA B E A C E G
    euclid_finish
  have h2: ¬ EF.intersectsLine CD := by
    euclid_apply triangle_median_line_parallel A D G F E DA CD AE
    euclid_finish
  euclid_finish
end LeanGeo
