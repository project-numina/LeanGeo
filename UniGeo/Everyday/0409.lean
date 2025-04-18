import SystemE
import UniGeo.Theorem
theorem day137: ∀ (A B C D O : Point) (P : Circle),
midpoint A O B ∧ O.isCentre P ∧ A.onCircle P ∧ B.onCircle P ∧ C.onCircle P ∧ C ≠ B ∧ C ≠ A ∧ D.onCircle P ∧ D ≠ A ∧ D ≠ B ∧ D ≠ C ∧ |(A─D)| =|(A─C)| →
∠C:A:B=∠D:A:B := by
  euclid_intros
  euclid_apply diameter_rightAngle A B C P
  euclid_apply diameter_rightAngle A B D P
  euclid_apply eqChord_eqInsctribedAngle A B C A B D P
  euclid_apply triangle_angleSum A B D
  euclid_apply triangle_anglePositive A B D
  euclid_assert ∠A:B:D < ∟
  euclid_apply triangle_angleSum A B C
  euclid_apply triangle_anglePositive A B C
  euclid_assert ∠A:B:C < ∟
  euclid_assert ∠A:B:D = ∠A:B:C
  euclid_assert ∠A:D:B = ∠A:C:B
  euclid_assert Triangle.congruent_test (△A:B:C) (△ A:B:D)
  euclid_apply Triangle.congruent_property (△A:B:C) (△ A:B:D)
  simp at *
  euclid_finish

theorem inscribed_trapezoid_isosceles: ∀ (A B C D: Point) (P : Circle) (AB BC CD DA : Line),
(cyclicQuadrilateral A B C D AB BC CD DA P) ∧ (¬ AB.intersectsLine CD)
→ |(B─C)| = |(A─D)| := by
  euclid_intros
  euclid_apply cyclic_property A B C D AB BC CD DA P
  euclid_apply line_from_points B D as BD
  euclid_assert C.opposingSides A BD
  euclid_apply parallel_eqAlternateAngles CD AB BD D B C A
  simp at *
  euclid_apply eqInscribedAngle_eqChord C D B A B D P
  euclid_finish

theorem day1382: ∀ (A B C D: Point) (P : Circle) (L AB CD : Line),
(cyclicQuadrilateral A B C D AB BC CD DA P) ∧ (¬ AB.intersectsLine CD) ∧
perpBisector A B L → perpBisector C D L := by
  euclid_intros
  euclid_apply (perpBisector_equiv A B L).1 as (Q, L2)
  euclid_assert perpLine AB L
  euclid_apply perpLine_parallel_perpLine AB L CD
  euclid_apply exists_centre P as O
  euclid_apply (chord_bisector O A B P AB L)
  euclid_assert O.onLine L
  euclid_apply chord_bisector O C D P CD L
  euclid_finish
