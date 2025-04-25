import SystemE
import UniGeo.Abbre
import UniGeo.Theorem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
theorem eqChord_eqChord : ∀ (A D B C : Point)(AD DB BC CA : Line) (P : Circle), cyclicQuadrilateral A D B C AD DB BC CA P ∧ |(A─D)| = |(C─B)|→ |(A─B)| = |(C─D)| := by
  euclid_intros
  euclid_apply cyclic_property A D B C AD DB BC CA P
  euclid_assert ∠D:A:B = ∠D:C:B
  euclid_assert ∠A:D:C = ∠A:B:C
  euclid_apply line_from_points A B as AB
  euclid_apply line_from_points C D as CD
  euclid_apply intersection_lines AB CD as E
  euclid_assert ∠B:C:E = ∠D:A:E
  euclid_assert ∠A:D:E = ∠C:B:E
  euclid_assert Triangle.congruent_test (△A:D:E) (△C:B:E)
  euclid_apply Triangle.congruent_property (△A:D:E) (△C:B:E)
  euclid_finish

theorem day140 : ∀ (A B O: Point) (P : Circle), O.isCentre P ∧ A.onCircle P ∧ B.onCircle P ∧ P.radius (2/3:ℝ)  ∧ ∠A:O:B = ∟ → |(A─B)| = 2 * √3  := by
  euclid_intros
  simp at *
  --euclid_apply angle_positive_neq A O B h1
  euclid_assert |(O─A)| = 2/3
  euclid_assert |(O─B)| = 2/3
  simp at *
  euclid_assert ¬ (between A O B)
  euclid_assert triangle O A B

  sorry
